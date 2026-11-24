import Lake
open Lean Lake DSL

package «exactjson» where
  lintDriver := "software_challenge/lint"
  testDriver := "tests"
  leanOptions := #[⟨`autoImplicit, false⟩]

require software_challenge from git "https://github.com/vincentqb/lean-software-challenge" @ "main"

@[default_target]
lean_lib «ExactJSON» where
  roots := #[`ExactJSON.Solution, `ExactJSON]
  globs := #[.andSubmodules `ExactJSON]

lean_lib «Challenge» where
  leanOptions := #[⟨`warn.sorry, false⟩]

@[default_target]
lean_exe «exactjson» where
  root := `ExactJSON.Main

lean_exe «tests» where
  root := `ExactJSON.Tests

@[default_target]
target statement pkg : Unit := do
  return (← pkg.fetchFacetJob `softwareChallengeStatement).map (fun _ => ())
