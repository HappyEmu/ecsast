# Updating the Zed syntax-highlighting extension

The Zed extension lives in `zed-ecsast/`, with the tree-sitter grammar as a
git submodule at `zed-ecsast/tree-sitter-ecsast` (pointing at
[`HappyEmu/tree-sitter-ecsast`](https://github.com/HappyEmu/tree-sitter-ecsast)).
Zed clones the grammar from GitHub at the commit pinned in
`zed-ecsast/extension.toml`, so any grammar change must be pushed to GitHub
and the pinned commit bumped.

## First-time clone

After cloning this repo, populate the submodule:

```bash
git submodule update --init
```

(Or pass `--recursive` to `git clone` in the first place.)

## Editing the grammar

```bash
cd zed-ecsast/tree-sitter-ecsast

# 1. Edit grammar.js (and/or query files in ../languages/ecsast/*.scm)

# 2. Regenerate the parser
tree-sitter generate

# 3. Sanity check that examples still parse
for f in ../../examples/*.ecs; do tree-sitter parse "$f" --quiet || echo "FAIL: $f"; done

# 4. Commit and push the grammar
git add -A
git commit -m "..."
git push
NEW_SHA=$(git rev-parse HEAD)
echo "$NEW_SHA"
```

## Bumping the pinned commit

Back in the outer repo, update `extension.toml` to point at the new commit
and bump the submodule gitlink:

```bash
cd ../..   # back to repo root

# Replace the `commit = "..."` line in zed-ecsast/extension.toml with $NEW_SHA
# (manual edit, or: sed -i '' "s/^commit = .*/commit = \"$NEW_SHA\"/" zed-ecsast/extension.toml)

git add zed-ecsast/extension.toml zed-ecsast/tree-sitter-ecsast
git commit -m "Bump tree-sitter-ecsast grammar"
```

## Reloading in Zed

In Zed: command palette → **`zed: install dev extension`** → pick
`zed-ecsast/`. Zed re-clones the grammar from GitHub at the new commit and
rebuilds the parser.

## Editing only the queries

Query files (`highlights.scm`, `brackets.scm`, `indents.scm`) live in
`zed-ecsast/languages/ecsast/` — *not* in the submodule. Edits to those don't
require a grammar commit bump; just reinstall the dev extension to pick them
up.

Before reinstalling, validate them locally to avoid Zed rejecting the
language outright (any one invalid query blocks the whole language from
loading):

```bash
cd zed-ecsast/tree-sitter-ecsast
for q in ../languages/ecsast/*.scm; do
  tree-sitter query "$q" ../../examples/fizzbuzz.ecs >/dev/null 2>&1 \
    && echo "OK   $(basename $q)" \
    || echo "FAIL $(basename $q)"
done
```
