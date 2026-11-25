import Lake
open Lean Lake DSL

package «exactjson» where
  leanOptions := #[⟨`autoImplicit, false⟩]
  testDriver := "tests"
  lintDriver := if (get_config? challenge).isSome then "software_challenge/lint" else ""

meta if (get_config? challenge).isSome then do
  require software_challenge from git "https://github.com/vincentqb/lean-software-challenge" @
    "3d5035043af16034bac2a92a7ccbcb2cee68ffa9"

  lean_lib «Challenge» where
    leanOptions := #[⟨`warn.sorry, false⟩]

  lean_exe «tests» where
    root := `ExactJSON.Tests

  @[default_target]
  target statement pkg : Unit := do
    return (← pkg.fetchFacetJob `softwareChallengeStatement).map (fun _ => ())

@[default_target]
lean_lib «ExactJSON» where
  roots := #[`ExactJSON.Solution, `ExactJSON]

@[default_target]
lean_exe «exactjson» where
  root := `ExactJSON.Main
