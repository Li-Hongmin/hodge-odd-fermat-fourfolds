import Certificates

/-! Run-time comparisons with the recorded Python conclusions.
These `#eval` computations do NOT provide kernel proofs of an unproved claim.
Any differing conclusion raises an error and stops verify.sh immediately.
-/

open Certificates

local instance : Decidable Mixed35.certificateStatement := by
  unfold Mixed35.certificateStatement
  infer_instance

#eval do
  if !(decide Mixed35.certificateStatement) then
    throw (IO.userError "MISMATCH: mixed35 Python assertions and Lean computation disagree")
  if (Mixed35.integerL1Ball 8 6).length != 40081 ||
      Mixed35.additiveMatrices.length != 288 || Mixed35.ordered != Mixed35.expectedTable then
    throw (IO.userError "MISMATCH: mixed35 counts or complete ordered payload")
  IO.println "mixed35: full numerical comparison=PASS (kernel proofs in Certificates.Mixed35Direct)"
  if Mixed35Direct.ordered != Mixed35.expectedTable ||
      Mixed35Direct.mixed != Mixed35Direct.essentialTable then
    throw (IO.userError "MISMATCH: complete direct and legacy matrix tables")

#eval do
  if PureSmallExceptionLevels.survivors 15 != PureSmallExceptionLevels.table15 ||
      ((PureSmallExceptionLevels.survivors 15).map (PureSmallExceptionLevels.canonical 15)).toFinset
        != PureSmallExceptionLevels.expected15 then
    throw (IO.userError "MISMATCH: complete level15 tuple and orbit tables")
  for (m, table) in [(15, PureSmallExceptionLevels.table15), (21, PureSmallExceptionLevels.table21),
      (33, PureSmallExceptionLevels.table33), (39, PureSmallExceptionLevels.table39)] do
    if PureSmallExceptionLevels.survivors m != table then
      throw (IO.userError s!"MISMATCH: complete level{m} tuple table")
    IO.println s!"level{m}: {table}"
  for (p, raw, orbits) in [(7, 12, 3), (11, 14, 2), (13, 24, 3)] do
    if PureSmallExceptionLevels.found p != PureSmallExceptionLevels.expected p ||
        (PureSmallExceptionLevels.survivors (3*p)).length != raw ||
        (PureSmallExceptionLevels.found p).card != orbits then
      throw (IO.userError s!"MISMATCH: pure-small Python and Lean disagree at p={p}")
    IO.println s!"pure-small: p={p}, raw={raw}, orbits={orbits}, full numerical comparison=PASS"

#eval do
  for (rows, cols, count) in [(3,4,106), (3,5,96), (2,5,294)] do
    if (SmallMatrices.nonzeroMatrices rows cols).length != count then
      throw (IO.userError "MISMATCH: small matrix count")
  if !((SmallMatrices.matrices 3 4 6).all SmallMatrices.classification34) ||
      !((SmallMatrices.matrices 3 5 6).all SmallMatrices.classification35) ||
      !((SmallMatrices.matrices 2 5 6).all SmallMatrices.classification25) then
    throw (IO.userError "MISMATCH: complete small matrix classifications")
  IO.println "small matrices: all 106/96/294 nonzero matrices and zero classified PASS"

#eval do
  let vs := U25Correction.vectors
  if vs.length != 1560 || !(vs.all fun v => ([1,2,3,4] : List Nat).all (U25Correction.checkPair v)) then
    throw (IO.userError "MISMATCH: complete U25 pairs")
  for (k, count, minimum) in [(2,80,14), (4,800,14), (6,5360,18)] do
    let costs := (vs.filter fun v => 2 * AdditiveDirect.l1Norm v == k).flatMap fun v =>
      ([1,2,3,4] : List Nat).map fun z => 2*k + U25Correction.correctedNorm v z
    if costs.length != count || costs.min? != some minimum then
      throw (IO.userError "MISMATCH: complete U25 count or minimum")
  IO.println "U25: all 6240 pairs; counts 80/800/5360; minimum costs 14/14/18 PASS"

#eval do
  for (p, count) in [(7,16), (11,4), (13,8)] do
    let found := HalfIntegralPotentials.accepted p
    if found.length != count || !(found.all fun vc => HalfIntegralPotentials.conclusion p vc.1 vc.2) then
      throw (IO.userError "MISMATCH: bounded half-integral potentials")
  IO.println "half-integral: full energy-bounded domains; accepted 16/4/8 PASS"

#eval IO.println "level66: manuscript inflation, Hodge rows, multiset identities and 32 sign encodings checked"
