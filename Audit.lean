import FourierJacobi
import Lean.Util.CollectAxioms

/-!
Exhaustive audit of the delivered core-evaluation publication: 30 inherited v2
modules and 39 new modules. The inventory must agree with the imported project
modules. Every declaration originating in a project module is checked, including
private helpers whose names do not start with `FourierJacobi`.

The complete types and transitive axioms of all new declarations are printed.
The main interfaces are printed again together, so that their actual hypotheses
can be reviewed separately from the axiom lists. Unsafe and partial declarations
are rejected, as are all axioms except `propext`, `Classical.choice`, and
`Quot.sound`. This audits implemented mathematics; it does not certify a missing
bridge to the paper's independently defined spherical coefficient. Source hashes
and the matching full build are recorded separately in the verification record.
-/

set_option format.width 160
set_option pp.deepTerms true
set_option pp.maxSteps 1000000

run_cmd do
  let allowed : Array Lean.Name := #[`propext, `Classical.choice, `Quot.sound]
  let baselineModules : Array Lean.Name := #[
    `FourierJacobi.Algebra.EulerFactors,
    `FourierJacobi.Algebra.FiniteCalculation,
    `FourierJacobi.Algebra.Intertwiner,
    `FourierJacobi.Algebra.Matrices,
    `FourierJacobi.Algebra.RegionSum,
    `FourierJacobi.Algebra.UnitaryFinite,
    `FourierJacobi.Algebra.UnitaryParameters,
    `FourierJacobi.Algebra.WeylCoefficient0,
    `FourierJacobi.Algebra.WeylCoefficient1,
    `FourierJacobi.Algebra.WeylCoefficient10,
    `FourierJacobi.Algebra.WeylCoefficient2,
    `FourierJacobi.Algebra.WeylCoefficient3,
    `FourierJacobi.Algebra.WeylCoefficient4,
    `FourierJacobi.Algebra.WeylCoefficient5,
    `FourierJacobi.Algebra.WeylCoefficient6,
    `FourierJacobi.Algebra.WeylCoefficient7,
    `FourierJacobi.Algebra.WeylCoefficient8,
    `FourierJacobi.Algebra.WeylCoefficient9,
    `FourierJacobi.Algebra.WeylData,
    `FourierJacobi.Algebra.WeylEvaluation,
    `FourierJacobi.Algebra.WeylSum,
    `FourierJacobi.Analysis.Damping,
    `FourierJacobi.Analysis.IntertwinerDerivative,
    `FourierJacobi.Analysis.ValuationSeries,
    `FourierJacobi.Measure.LocalHaar,
    `FourierJacobi.Measure.NullSets,
    `FourierJacobi.Valuations.Cartan,
    `FourierJacobi.Valuations.LocalField,
    `FourierJacobi.Valuations.LocalMatrix,
    `FourierJacobi.Valuations.MatrixBridge]
  let newModules : Array Lean.Name := #[
    `FourierJacobi.Analysis.CentralWeylSeries,
    `FourierJacobi.Analysis.CoreParameters,
    `FourierJacobi.Analysis.ExplicitKernel,
    `FourierJacobi.Analysis.FiberIntegration,
    `FourierJacobi.Analysis.HaarCellMass,
    `FourierJacobi.Analysis.HaarCellMaster,
    `FourierJacobi.Analysis.HaarCellValue,
    `FourierJacobi.Analysis.HaarCoreAssembly,
    `FourierJacobi.Analysis.HaarKernel,
    `FourierJacobi.Analysis.HaarLatticePartition,
    `FourierJacobi.Analysis.HaarLimits,
    `FourierJacobi.Analysis.I0Complete,
    `FourierJacobi.Analysis.I0Master,
    `FourierJacobi.Analysis.I1Assembly,
    `FourierJacobi.Analysis.I1Complete,
    `FourierJacobi.Analysis.I1Partition,
    `FourierJacobi.Analysis.I1SourceRows,
    `FourierJacobi.Analysis.I2Ambient,
    `FourierJacobi.Analysis.I2Assembly,
    `FourierJacobi.Analysis.I2Complete,
    `FourierJacobi.Analysis.I2Convergence,
    `FourierJacobi.Analysis.I2Domains,
    `FourierJacobi.Analysis.I2Master,
    `FourierJacobi.Analysis.I2Partition,
    `FourierJacobi.Analysis.I2Predicates,
    `FourierJacobi.Analysis.LatticeCore,
    `FourierJacobi.Analysis.LatticeLimits,
    `FourierJacobi.Analysis.MasterDamping,
    `FourierJacobi.Analysis.MasterSeries,
    `FourierJacobi.Analysis.PaperDomain,
    `FourierJacobi.Analysis.RationalLimits,
    `FourierJacobi.Measure.IntegerShells,
    `FourierJacobi.Measure.JointCollision,
    `FourierJacobi.Measure.MultiplicativeHaar,
    `FourierJacobi.Measure.PaperMultiplicativeHaar,
    `FourierJacobi.Measure.ShellCollision,
    `FourierJacobi.Measure.UnitScaling,
    `FourierJacobi.Valuations.KernelIndices,
    `FourierJacobi.Valuations.KernelShells]
  let finalModules : Array Lean.Name := #[
    `FourierJacobi.Analysis.LatticeLimits,
    `FourierJacobi.Analysis.HaarCoreAssembly,
    `FourierJacobi.Analysis.HaarLimits]
  let mainDeclarations : Array Lean.Name := #[
    `FourierJacobi.Algebra.finiteCore_eq_closedCore,
    `FourierJacobi.Analysis.summable_norm_i0_full,
    `FourierJacobi.Analysis.hasSum_i0_full,
    `FourierJacobi.Analysis.summable_norm_i1_master,
    `FourierJacobi.Analysis.hasSum_i1_master_of_geometricRange,
    `FourierJacobi.Analysis.summable_norm_i2_master,
    `FourierJacobi.Analysis.hasSum_i2_master,
    `FourierJacobi.Analysis.paperE_eq_closedCore,
    `FourierJacobi.Analysis.paper_denominator_interior_ne_zero,
    `FourierJacobi.Analysis.paper_denominator_special_ne_zero,
    `FourierJacobi.Analysis.summable_norm_weightedLatticeTerm,
    `FourierJacobi.Analysis.hasSum_weightedLatticeTerm,
    `FourierJacobi.Analysis.latticeCore_eq_dampedRational,
    `FourierJacobi.Analysis.centralLatticeCore_sum,
    `FourierJacobi.Analysis.hasSum_centralWeightedTerm,
    `FourierJacobi.Measure.additiveHaar_integerShell,
    `FourierJacobi.Measure.canonicalValuation_measurable,
    `FourierJacobi.Measure.paperMultiplicativeHaar_unitValuationShell,
    `FourierJacobi.Measure.additiveHaar_real_prod_sourceJointCollisionDepth,
    `FourierJacobi.Valuations.kernel_indices_nonnegative,
    `FourierJacobi.Analysis.explicitWeylKernel_formula,
    `FourierJacobi.Analysis.explicitWeylKernel_q_norm_le,
    `FourierJacobi.Analysis.explicitCoreIntegrand_measurable,
    `FourierJacobi.Analysis.haarLatticeCell_exhaustive_ae,
    `FourierJacobi.Analysis.haarLatticeCell_kernelCoordinates,
    `FourierJacobi.Analysis.haarLatticeCell_measure_ne_top,
    `FourierJacobi.Analysis.haarLatticeCell_real_mass,
    `FourierJacobi.Analysis.haarLatticeCell_prefactor_value,
    `FourierJacobi.Analysis.integrable_hasSum_of_countable_fibers]
  let expectedModules := baselineModules ++ newModules
  let env ← Lean.getEnv
  Lean.logInfo m!"ALLOWED FOUNDATIONAL AXIOMS {allowed}"
  Lean.logInfo "RULE: every project declaration, including private helpers, must be safe and nonpartial; its transitive axioms must be a subset of the allowed list."
  for moduleName in expectedModules do
    unless env.header.moduleNames.contains moduleName do
      throwError "Required project module was not imported: {moduleName}"
  for moduleName in env.header.moduleNames do
    if (`FourierJacobi).isPrefixOf moduleName && moduleName != `FourierJacobi then
      unless expectedModules.contains moduleName do
        throwError "Imported project module is missing from the audit inventory: {moduleName}"
  for name in mainDeclarations do
    unless (env.find? name).isSome do
      throwError "Required main declaration is missing: {name}"
  let entries := env.constants.toList.toArray.qsort fun a b => Lean.Name.quickLt a.1 b.1
  let mut checked : Nat := 0
  let mut newChecked : Nat := 0
  let mut newCounts := Array.replicate newModules.size (0 : Nat)
  for (name, info) in entries do
    let origin := match env.getModuleIdxFor? name with
      | some moduleIdx => env.header.moduleNames[moduleIdx]!
      | none => Lean.Name.anonymous
    let isNew := newModules.contains origin
    if (`FourierJacobi).isPrefixOf name || expectedModules.contains origin then
      if info.isUnsafe || info.isPartial then
        throwError "Unsafe or partial project declaration: {name} (module {origin})"
      let axioms ← Lean.collectAxioms name
      let unexpected := axioms.filter fun ax => !allowed.contains ax
      unless unexpected.isEmpty do
        throwError "Unexpected axioms in {name} (module {origin}): {unexpected}"
      checked := checked + 1
      if isNew then
        newChecked := newChecked + 1
        for i in [:newModules.size] do
          if newModules[i]! == origin then
            newCounts := newCounts.set! i (newCounts[i]! + 1)
        Lean.logInfo m!"NEW MODULE {origin}\nDECLARATION {name}\nTYPE {info.type}\nAXIOMS {axioms}"
  if checked == 0 then
    throwError "No project declarations were audited"
  for i in [:newModules.size] do
    if newCounts[i]! == 0 then
      throwError "No declarations found in new module {newModules[i]!}"
    Lean.logInfo m!"MODULE COUNT {newModules[i]!}: {newCounts[i]!} declarations"
  Lean.logInfo "MAIN INTERFACES: complete types below expose hypotheses; an allowed axiom list alone is not a scope claim."
  for (name, info) in entries do
    let origin := match env.getModuleIdxFor? name with
      | some moduleIdx => env.header.moduleNames[moduleIdx]!
      | none => Lean.Name.anonymous
    if mainDeclarations.contains name ||
        (finalModules.contains origin && (`FourierJacobi).isPrefixOf name) then
      let axioms ← Lean.collectAxioms name
      Lean.logInfo m!"MAIN {name}\nMODULE {origin}\nTYPE {info.type}\nAXIOMS {axioms}"
  Lean.logInfo m!"Axiom and safety audit passed for {checked} project declarations across {expectedModules.size} modules."
  Lean.logInfo m!"Of these, {newChecked} declarations belong to the {newModules.size} new core-evaluation modules; {baselineModules.size} modules are inherited from v2."
