
module Core.Constraints

import Core.Context.Log

import Data.List
import Data.List1
import Data.SortedMap as Map
import Data.SortedSet as Set
import Data.String
import Libraries.Data.Graph
import Libraries.Data.List.Extra

0 Graph : (cuid : Type) -> Ord cuid => Type
Graph cuid = SortedMap cuid (SortedSet cuid)

0 Edge : Type -> Type
Edge cuid = (cuid, cuid, Bool)

constraintsToEdges : List UConstraint -> List (Edge Name)
constraintsToEdges = map $ \case
  ULE x y => (x, y, False)
  ULT x y => (x, y, True)

buildNonStrictGraph : Ord cuid => List (Edge cuid) -> Graph cuid
buildNonStrictGraph edges =
    -- TODO: maybe enumerate vertices for faster comparaisons?
    fromListWith Set.union
      [ (from, Set.singleton to) | (from, to, strict) <- edges, not strict ]

buildSuperGraph : Ord cuid => List (List cuid) -> List (Edge cuid) -> Graph (List cuid)
buildSuperGraph sccs edges = do
    -- TODO: enumerate vertices for faster comparaisons
    let vertexToSCC = Map.fromList [ (v, scc) | scc <- sccs, v <- scc ]
    let superEdges = catMaybes $ edges <&> \(from, to, _) =>
          do fromSCC <- lookup from vertexToSCC
             toSCC <- lookup to vertexToSCC
             Just (fromSCC, toSCC)
    fromListWith Set.union [ (from, Set.singleton to) | (from, to) <- superEdges ]

-- Algorithm:
-- 1. Built graph of non-strict edges
-- 2. Find strongly connected components
-- 3. Build supergraph of strongly connected components
-- 4. Find strongly connected components of supergraph
--    (enough to find any cycle)
-- 5. If any SCC has more than one element, then there is a cycle
findStrictCycles : Show cuid => Ord cuid => List (Edge cuid) -> List (List1 (List cuid))
findStrictCycles edges = do
    let nonStrictGraph = buildNonStrictGraph edges
    let sccs = tarjan nonStrictGraph
    let superGraph = buildSuperGraph (map forget sccs) edges
    let superSCCs = tarjan superGraph
    filter (\scc => length scc > 1) superSCCs

export
checkUniverseConstraints : Ref Ctxt Defs => Core (List Error)
checkUniverseConstraints = do
  cs <- getUConstraints
  let cs = sortedNub cs
  logC "universe" 5 $
    do pure $ "Constraints:\n" ++ unlines !(for cs $ map show . toFullNames)
  let cycles = findStrictCycles $ constraintsToEdges cs
  cycles <- traverse (traverseList1 $ Core.traverse toFullNames) cycles
  pure $ cycles <&> \cycle =>
      GenericMsg emptyFC $ "Universe constraints contain a strict cycle: \{show cycle}"
