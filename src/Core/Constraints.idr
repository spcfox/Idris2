
module Core.Constraints

import Core.Context.Log

import Data.String
import Libraries.Data.List.Extra

export
checkUniverseConstraints : Ref Ctxt Defs => Core (List Error)
checkUniverseConstraints = do
  cs <- getUConstraints
  let cs = sortedNub cs
  logC "universe" 5 $
    do pure $ "Constraints:\n" ++ unlines !(for cs $ map show . toFullNames)
  -- TODO: check that constraints are satisfiable
  pure []
