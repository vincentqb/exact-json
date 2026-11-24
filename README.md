# ExactJSON

Canonical, strictly typed JSON for Lean, organized as a
[Lean Software Challenge](https://github.com/vincentqb/lean-software-challenge): what the library
promises is stated in Lean, as the headlines of [`Challenge.lean`](Challenge.lean), and proved
in `ExactJSON/`.

```sh
lake build        # the library, the CLI, and the statement's checks
lake lint         # which headlines are proved, and what is assumed
lake test         # the tests
lake comparator   # the kernel replays the proofs against Challenge.lean
```

Use it from another package with

```toml
[[require]]
name = "exactjson"
git = "<this repository>"
```
