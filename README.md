# ExactJSON

Canonical, strictly typed JSON for Lean, organized as a
[Lean Software Challenge](https://github.com/vincentqb/lean-software-challenge): what the library
promises is stated in Lean, as the headlines of [`Challenge.lean`](Challenge.lean), and proved
in `ExactJSON/`.

```sh
lake build                       # the library and the CLI
lake -R -Kchallenge=on build     # once: also the statement, its checks and the tests
lake lint                        # which headlines are proved, and what is assumed
lake test                        # the tests
lake comparator                  # the kernel replays the proofs against Challenge.lean
```

The library requires nothing. Only the challenge needs Lean Software Challenge, at a pinned commit,
and Lake adds it only when the package is configured with `-Kchallenge=on`; the setting holds until
the next `-R`. Use the library from another package with

```toml
[[require]]
name = "exactjson"
git = "<this repository>"
```
