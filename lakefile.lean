import Lake
open Lean Lake DSL

package «tomljson» where
  lintDriver := "software_challenge/lint"
  testDriver := "tests"
  leanOptions := #[⟨`autoImplicit, false⟩]

require software_challenge from git "https://github.com/vincentqb/lean-software-challenge" @ "main"

@[default_target]
lean_lib «TomlJson» where
  roots := #[`TomlJson.Solution, `TomlJson]
  globs := #[.andSubmodules `TomlJson]

lean_lib «Challenge» where
  leanOptions := #[⟨`warn.sorry, false⟩]

@[default_target]
lean_exe «tomljson» where
  root := `TomlJson.Main

lean_exe «tests» where
  root := `TomlJson.Tests

@[default_target]
target statement pkg : Unit := do
  return (← pkg.fetchFacetJob `softwareChallengeStatement).map (fun _ => ())
