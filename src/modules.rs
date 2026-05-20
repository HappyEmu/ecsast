//! Multi-file module loading.
//!
//! Lexes and parses the entry file plus every transitively imported sibling
//! file into a single shared `AstWorld` and `Bump` arena, building a graph
//! that the semantic pass and codegen consume.

use std::collections::HashMap;
use std::fmt;
use std::path::{Path, PathBuf};

use bumpalo::Bump;

use crate::ast::{AstWorld, NodeId, NodeKind};
use crate::lexer::Lexer;
use crate::parser::Parser;
use crate::span::Span;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ModuleId(pub u32);

pub struct Module {
    pub id: ModuleId,
    pub file_path: PathBuf,
    /// Dotted module path, e.g. ["math", "geometry"]. The entry module is `vec![]`.
    pub mod_path: Vec<String>,
    pub root: NodeId,
    /// Item-imports: `use a::b::c;` → `c` → (module of `a::b`, decl node of `c`).
    /// Populated by the semantic pass.
    pub imports: HashMap<String, (ModuleId, NodeId)>,
    /// Module-aliases: `use math;` → `math` → ModuleId of `math`.
    /// Populated by the semantic pass.
    pub module_aliases: HashMap<String, ModuleId>,
}

pub struct ModuleGraph {
    pub modules: Vec<Module>,
    pub by_path: HashMap<Vec<String>, ModuleId>,
    pub entry: ModuleId,
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
            entry: ModuleId(0),
        };

        let entry_id = graph.add_module(world, arena, entry_path.to_path_buf(), Vec::new())?;
        graph.entry = entry_id;

        // Worklist: process each module's UseDecls and load missing modules.
        // In-progress set tracks the current DFS path for cycle detection.
        let mut visited: Vec<bool> = vec![false; graph.modules.len()];
        let mut on_stack: Vec<bool> = vec![false; graph.modules.len()];

        // Iterative DFS using explicit stack of (module_id, child_index_to_visit_next).
        struct Frame {
            mod_id: ModuleId,
            imports: Vec<Vec<String>>, // module paths to load
            idx: usize,
        }

        let mut frames: Vec<Frame> = Vec::new();
        frames.push(Frame {
            mod_id: entry_id,
            imports: graph.module_paths_to_load(world, entry_id),
            idx: 0,
        });
        on_stack[entry_id.0 as usize] = true;

        while let Some(frame) = frames.last_mut() {
            if frame.idx >= frame.imports.len() {
                on_stack[frame.mod_id.0 as usize] = true; // already true, but clarity
                let mod_id = frame.mod_id;
                on_stack[mod_id.0 as usize] = false;
                visited[mod_id.0 as usize] = true;
                frames.pop();
                continue;
            }

            let mod_path = frame.imports[frame.idx].clone();
            frame.idx += 1;

            // Already loaded?
            if let Some(&child_id) = graph.by_path.get(&mod_path) {
                if on_stack[child_id.0 as usize] {
                    // Cycle: walk current frames to build chain.
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
                if !visited[child_id.0 as usize] {
                    // Already on stack (shouldn't happen since checked above) or DAG re-import.
                    // For DAG: skip; already loading.
                }
                continue;
            }

            // Resolve file path.
            let file_path = resolve_module_file(&entry_dir, &mod_path);
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
            while visited.len() < graph.modules.len() {
                visited.push(false);
            }
            while on_stack.len() < graph.modules.len() {
                on_stack.push(false);
            }
            on_stack[child_id.0 as usize] = true;

            let child_imports = graph.module_paths_to_load(world, child_id);
            frames.push(Frame {
                mod_id: child_id,
                imports: child_imports,
                idx: 0,
            });
        }

        Ok(graph)
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
        self.modules.push(Module {
            id,
            file_path,
            mod_path: mod_path.clone(),
            root,
            imports: HashMap::new(),
            module_aliases: HashMap::new(),
        });
        self.by_path.insert(mod_path, id);
        Ok(id)
    }

    /// Inspect a module's top-level `UseDecl` nodes and return the list of
    /// module paths it imports (i.e. with the last segment dropped when the
    /// import names an item rather than a module).
    fn module_paths_to_load(&self, world: &AstWorld<'_>, mod_id: ModuleId) -> Vec<Vec<String>> {
        let module = &self.modules[mod_id.0 as usize];
        let mut out = Vec::new();

        let items = match *world.kind(module.root) {
            NodeKind::Program(items) => items,
            _ => return out,
        };

        for &item in items {
            if let NodeKind::UseDecl { path } = *world.kind(item) {
                // Skip globs — they're a semantic error, not a load target.
                if path.contains(&"*") {
                    continue;
                }
                // `use a;` → load module `a`. `use a::b::c;` → load module `a::b`.
                let segs: Vec<String> = if path.len() == 1 {
                    path.iter().map(|s| s.to_string()).collect()
                } else {
                    path[..path.len() - 1].iter().map(|s| s.to_string()).collect()
                };
                if !segs.is_empty() {
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
