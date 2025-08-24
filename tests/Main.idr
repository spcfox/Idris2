module Main

import System
import System.Directory
import System.File

import Test.Golden

%default covering


typeddTests : IO TestPool
typeddTests = testsInDir "typedd-book" "Type Driven Development"

chezTests : IO TestPool
chezTests = testsInDir "chez" "Chez backend" {codegen = Just Chez}

refcTests : IO TestPool
refcTests = testsInDir "refc" "Reference counting C backend" {codegen = Just C}

racketTests : IO TestPool
racketTests = testsInDir "racket" "Racket backend" {codegen = Just Racket}
  { pred = not . (`elem` ["conditions006", "conditions007"]) }

nodeTests : IO TestPool
nodeTests = testsInDir "node" "Node backend" {codegen = Just Node}

vmcodeInterpTests : IO TestPool
vmcodeInterpTests = testsInDir "vmcode" "VMCode interpreter"

ideModeTests : IO TestPool
ideModeTests = testsInDir "ideMode" "IDE mode"

preludeTests : IO TestPool
preludeTests = testsInDir "prelude" "Prelude library"

templateTests : IO TestPool
templateTests = testsInDir "templates" "Test templates"

-- base library tests are run against
-- each codegen supported and to keep
-- things simple it's all one test group
-- that only runs if all backends are
-- available.
baseLibraryTests : IO TestPool
baseLibraryTests = testsInDir "base" "Base library" {requirements = [Chez, Node]}

-- same behavior as `baseLibraryTests`
contribLibraryTests : IO TestPool
contribLibraryTests = testsInDir "contrib" "Contrib library" {requirements = [Chez, Node]}

-- same behavior as `baseLibraryTests`
linearLibraryTests : IO TestPool
linearLibraryTests = testsInDir "linear" "Linear library" {requirements = [Chez, Node]}

codegenTests : IO TestPool
codegenTests = testsInDir "codegen" "Code generation"

commandLineTests : IO TestPool
commandLineTests = testsInDir "cli" "Command-line interface"

idrisTestsAllSchemes : Requirement -> IO TestPool
idrisTestsAllSchemes cg = testsInDir "allschemes"
      ("Test across all scheme backends: " ++ show cg ++ " instance")
      {codegen = Just cg}

idrisTestsAllBackends : Requirement -> TestPool
idrisTestsAllBackends cg = MkTestPool
      ("Test across all backends: " ++ show cg ++ " instance")
      [] (Just cg)
       -- RefC implements IEEE standard and distinguishes between 0.0 and -0.0
       -- unlike other backends. So turn this test for now.
      $ ([ "issue2362" ] <* guard (cg /= C))
      ++ ([ "popen2" ] <* guard (cg /= Node))
      ++ [ -- Evaluator
       "evaluator004",
       -- Unfortunately the behaviour of Double is platform dependent so the
       -- following test is turned off.
       -- "evaluator005",
       "basic048",
       "perf006"]

main : IO ()
main = runner $
  [  !typeddTests
  , !ideModeTests
  , !preludeTests
  , !baseLibraryTests
  , !linearLibraryTests
  , !contribLibraryTests
  , !chezTests
  , !refcTests
  , !racketTests
  , !nodeTests
  , !vmcodeInterpTests
  , !templateTests
  , !codegenTests
  , !commandLineTests
  ]
  ++ !(traverse idrisTestsAllSchemes [Chez, Racket])
  ++ map (testPaths "allbackends" . idrisTestsAllBackends) [Chez, Node, Racket, C]


    where

    testPaths : String -> TestPool -> TestPool
    testPaths dir = { testCases $= map ((dir ++ "/") ++) }
