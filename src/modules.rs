//! Multi-file module loading.
//!
//! Lexes and parses the entry file plus every transitively imported sibling
//! file into a single shared `AstWorld` and `Bump` arena, building a graph
//! that the semantic pass and codegen consume.
//!
//! Modules are first-class. A `use a::b::c::d;` is resolved by walking the
//! path through the graph: any prefix that exists as a file is a real
//! `Module`; intermediate path segments without a backing file act as pure
//! namespaces, derived from `by_path` keys. The trailing segment binds locally
//! to either a `Module` (if its full path is loaded) or a `Func` (if the
//! penultimate path is loaded and the trailing name is a public item).
//!
//! The loader has one job: given a `use` path, load the longest prefix that
//! has a backing file. Whether the trailing segments are items or further
//! submodules is decided later, by the semantic pass.

use std::collections::{HashMap, HashSet};
use std::fmt;
use std::path::{Path, PathBuf};

use bumpalo::Bump;

use crate::ast::{AstWorld, NodeId, NodeKind};
use crate::lexer::Lexer;
use crate::parser::Parser;
use crate::span::Span;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ModuleId(pub u32);

/// What a name in a module's scope refers to. Mirrors Rust's `Res::Mod` /
/// `Res::Def(Fn, ...)` distinction. Populated by the semantic pass from
/// `use` declarations.
#[derive(Clone, Copy, Debug)]
pub enum Binding {
    Module(ModuleId),
    Func { node: NodeId, owner: ModuleId },
}

pub struct Module {
    pub id: ModuleId,
    pub file_path: PathBuf,
    /// Dotted module path, e.g. ["math", "geometry"]. The entry module is `vec![]`.
    pub mod_path: Vec<String>,
    pub root: NodeId,
    /// Names brought into local scope by `use` declarations. The trailing
    /// segment of each use path is the key; the value records whether that
    /// name refers to a module or a function.
    pub bindings: HashMap<String, Binding>,
}

pub struct ModuleGraph {
    pub modules: Vec<Module>,
    /// Map from the joined path key (`""` for the entry module, `"math"`,
    /// `"math::geometry"`, …) to the owning module.
    pub by_path: HashMap<String, ModuleId>,
    /// Every joined prefix that names a loaded module *or* an intermediate
    /// namespace above one. Lets `is_namespace` answer in O(1).
    pub namespaces: HashSet<String>,
    pub entry: ModuleId,
    /// Directory the entry file lives in. Used by the loader to resolve
    /// sibling and nested module files; not consulted by the semantic pass.
    pub entry_dir: PathBuf,
}

#[derive(Debug)]
pub struct ModuleError {
    pub message: String,
    pub span: Option<Span>,
}

impl fmt::Display for ModuleError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.span {
            Some(s) => write!(f, "{} at bytes {}..{}", self.message, s.start, s.end),
            None => write!(f, "{}", self.message),
        }
    }
}

impl std::error::Error for ModuleError {}

impl ModuleError {
    fn new(msg: impl Into<String>, span: Option<Span>) -> Self {
        Self {
            message: msg.into(),
            span,
        }
    }
}

impl ModuleGraph {
    /// Load the entry file plus every transitively imported file into a
    /// shared world and arena. Performs only lexing and parsing — semantic
    /// validation of `use` paths runs in the semantic pass.
    pub fn load<'arena>(
        entry_path: &Path,
        arena: &'arena Bump,
        world: &mut AstWorld<'arena>,
    ) -> Result<Self, ModuleError> {
        let entry_dir = entry_path
            .parent()
            .map(|p| p.to_path_buf())
            .unwrap_or_else(|| PathBuf::from("."));

        let mut graph = ModuleGraph {
            modules: Vec::new(),
            by_path: HashMap::new(),
            namespaces: HashSet::new(),
            entry: ModuleId(0),
            entry_dir,
        };

        let entry_id = graph.add_module(world, arena, entry_path.to_path_buf(), Vec::new())?;
        graph.entry = entry_id;

        // DFS through transitive `use` declarations, loading whichever file
        // is the longest existing prefix of each use path.
        struct Frame {
            mod_id: ModuleId,
            imports: Vec<Vec<String>>,
            idx: usize,
        }

        let mut on_stack: HashSet<ModuleId> = HashSet::new();
        on_stack.insert(entry_id);

        let mut frames: Vec<Frame> = vec![Frame {
            mod_id: entry_id,
            imports: graph.module_paths_to_load(world, entry_id),
            idx: 0,
        }];

        while let Some(frame) = frames.last_mut() {
            if frame.idx >= frame.imports.len() {
                on_stack.remove(&frame.mod_id);
                frames.pop();
                continue;
            }

            let mod_path = frame.imports[frame.idx].clone();
            frame.idx += 1;

            let key = join_path(&mod_path);
            if let Some(&child_id) = graph.by_path.get(&key) {
                if on_stack.contains(&child_id) {
                    let mut chain: Vec<String> = frames
                        .iter()
                        .map(|f| graph.modules[f.mod_id.0 as usize].mod_path_label())
                        .collect();
                    chain.push(graph.modules[child_id.0 as usize].mod_path_label());
                    return Err(ModuleError::new(
                        format!("import cycle: {}", chain.join(" -> ")),
                        None,
                    ));
                }
                continue;
            }

            let file_path = resolve_module_file(&graph.entry_dir, &mod_path);
            if !file_path.exists() {
                return Err(ModuleError::new(
                    format!(
                        "module `{}` not found (looked for {})",
                        mod_path.join("::"),
                        file_path.display()
                    ),
                    None,
                ));
            }

            let child_id = graph.add_module(world, arena, file_path, mod_path.clone())?;
            on_stack.insert(child_id);

            let child_imports = graph.module_paths_to_load(world, child_id);
            frames.push(Frame {
                mod_id: child_id,
                imports: child_imports,
                idx: 0,
            });
        }

        Ok(graph)
    }

    /// Look up a module by its dotted path segments.
    pub fn lookup(&self, segments: &[impl AsRef<str>]) -> Option<ModuleId> {
        self.by_path.get(&join_path(segments)).copied()
    }

    /// Returns true if `prefix` is the path of a loaded module, or a strict
    /// prefix of one (i.e. acts as a namespace even without its own file).
    pub fn is_namespace(&self, prefix: &[impl AsRef<str>]) -> bool {
        self.namespaces.contains(&join_path(prefix))
    }

    fn add_module<'arena>(
        &mut self,
        world: &mut AstWorld<'arena>,
        arena: &'arena Bump,
        file_path: PathBuf,
        mod_path: Vec<String>,
    ) -> Result<ModuleId, ModuleError> {
        let src = std::fs::read_to_string(&file_path).map_err(|e| {
            ModuleError::new(
                format!("error reading {}: {e}", file_path.display()),
                None,
            )
        })?;
        let tokens = Lexer::new(&src).tokenize();
        let mut parser = Parser::new(&tokens, arena, world);
        let root = parser.parse_file();

        let id = ModuleId(self.modules.len() as u32);
        let key = join_path(&mod_path);
        // Register the path itself plus every proper prefix as a namespace so
        // `is_namespace` is O(1).
        for n in 0..=mod_path.len() {
            self.namespaces.insert(join_path(&mod_path[..n]));
        }
        self.modules.push(Module {
            id,
            file_path,
            mod_path,
            root,
            bindings: HashMap::new(),
        });
        self.by_path.insert(key, id);
        Ok(id)
    }

    /// For each top-level `use` declaration in `mod_id`, return the module
    /// path the loader should attempt to load: the longest prefix of the use
    /// path that has a backing `.ecs` file. Globs and empty paths are skipped
    /// — they're rejected by the semantic pass with a precise error.
    fn module_paths_to_load(&self, world: &AstWorld<'_>, mod_id: ModuleId) -> Vec<Vec<String>> {
        let module = &self.modules[mod_id.0 as usize];
        let mut out = Vec::new();

        let items = match *world.kind(module.root) {
            NodeKind::Program(items) => items,
            _ => return out,
        };

        for &item in items {
            if let NodeKind::UseDecl { path } = *world.kind(item) {
                if path.contains(&"*") || path.is_empty() {
                    continue;
                }
                if let Some(segs) = longest_existing_prefix(&self.entry_dir, path) {
                    out.push(segs);
                }
            }
        }

        out
    }
}

impl Module {
    fn mod_path_label(&self) -> String {
        if self.mod_path.is_empty() {
            "<entry>".to_string()
        } else {
            self.mod_path.join("::")
        }
    }
}

/// Walk `path` from longest to shortest prefix and return the first one whose
/// `.ecs` file exists relative to `entry_dir`. `None` means no prefix is a
/// real file — the semantic pass will report the most informative error.
fn longest_existing_prefix(entry_dir: &Path, path: &[&str]) -> Option<Vec<String>> {
    for k in (1..=path.len()).rev() {
        let prefix: Vec<String> = path[..k].iter().map(|s| s.to_string()).collect();
        if resolve_module_file(entry_dir, &prefix).exists() {
            return Some(prefix);
        }
    }
    None
}

/// Join dotted path segments with `::`. Accepts `&[String]` or `&[&str]`.
pub fn join_path<S: AsRef<str>>(segments: &[S]) -> String {
    let mut out = String::new();
    for (i, seg) in segments.iter().enumerate() {
        if i > 0 {
            out.push_str("::");
        }
        out.push_str(seg.as_ref());
    }
    out
}

fn resolve_module_file(entry_dir: &Path, mod_path: &[String]) -> PathBuf {
    // ["math"] → entry_dir/math.ecs
    // ["math", "geometry"] → entry_dir/math/geometry.ecs
    let mut path = entry_dir.to_path_buf();
    for seg in &mod_path[..mod_path.len() - 1] {
        path.push(seg);
    }
    path.push(format!("{}.ecs", mod_path.last().unwrap()));
    path
}
