module

import TomlJson.Tests.Examples
import TomlJson.Tests.Properties
import TomlJson.Tests.DeriveErrors
import SoftwareChallenge.Tests
meta import SoftwareChallenge

/-! The test runner `lake test` builds and runs. Its imports are this package's own tests, which
run as they build (`#guard` and `#eval`); `SoftwareChallenge.testsMain` runs the tests of world
claims, of which this challenge has none. -/

public section

/-- Run the tests of world claims. -/
def main := SoftwareChallenge.testsMain
