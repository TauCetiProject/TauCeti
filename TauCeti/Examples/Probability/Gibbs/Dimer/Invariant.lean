/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Examples.Probability.Gibbs.Dimer.Basic
import TauCeti.Dynamics.Ergodic.Action.TimeMap

/-!
# Checks for invariant and ergodic dimer Gibbs measures on the line

On the nearest-neighbour graph of `ℤ` with `2ℤ` acting by translations (`ofAdd n` translating by
`2n`), the subshift `𝔛(ℤ) = dimerSubshiftInt` has the two points `evenPt`, `oddPt` of the even
and the odd edges, and `2ℤ` fixes both (`smul_eq_self_dimerSubshiftInt`).

* Every measure on `𝔛(ℤ)` is invariant, and Gibbs for the dimer specification (on the line every
  completion set is a singleton), so `𝒢_inv` is the set of all probability measures, and
  `δ_even`, `δ_odd` and their midpoint lie in `𝒢_inv` (`dirac_evenPt_mem_gibbsInvariant`,
  `dirac_oddPt_mem_gibbsInvariant`, `diracMidpoint_mem_gibbsInvariant`).
* `δ_even` and `δ_odd` are ergodic (`TauCeti.ergodicSMul_dirac`, which applies since every
  measure on `𝔛(ℤ)` is invariant), while the midpoint is not
  (`not_ergodicSMul_diracMidpoint`): the event "the edge `{0, 1}` is present", the point `evenPt`,
  is `2ℤ`-invariant of measure `1/2`.
-/

public section

noncomputable section

open SimpleGraph MeasureTheory Set Function TauCeti
open scoped ENNReal

namespace TauCeti.Examples.DimerGibbsInvariant

open TauCeti.Examples.DimerConfiguration TauCeti.Examples.DimerGibbs

/-- Every measure on `𝔛(ℤ)` is invariant under `2ℤ`. -/
instance smulInvariantMeasure_dimerSubshiftInt (μ : Measure dimerSubshiftInt) :
    SMulInvariantMeasure (Multiplicative ℤ) dimerSubshiftInt μ :=
  ⟨fun g s _ => by simp only [smul_eq_self_dimerSubshiftInt, preimage_id']⟩

/-- On `𝔛(ℤ)`, a probability measure is an invariant Gibbs measure of the dimer specification. -/
theorem mem_gibbsInvariant_of_isProbabilityMeasure {w : (nnGraph ℤ).edgeSet → ℝ}
    (hw : ∀ e, 0 < w e) (μ : Measure dimerSubshiftInt) [IsProbabilityMeasure μ] :
    μ ∈ ((nnGraph ℤ).dimerSpecification (Multiplicative ℤ)
      (Iso.exists_compHom_smul_eq_mapEdgeSet (zpowersHom _ shiftTwo)) hw).gibbsInvariant :=
  Specification.mem_gibbsInvariant_iff.2
    ⟨TauCeti.MeasureTheory.mem_invariantMeasuresOfMeasureUnivEq_iff.2
      ⟨inferInstance, measure_univ⟩, isGibbs_dimerSpecification_int hw μ⟩

/-- `δ_even` is an invariant Gibbs measure. -/
theorem dirac_evenPt_mem_gibbsInvariant {w : (nnGraph ℤ).edgeSet → ℝ} (hw : ∀ e, 0 < w e) :
    Measure.dirac evenPt ∈ ((nnGraph ℤ).dimerSpecification (Multiplicative ℤ)
      (Iso.exists_compHom_smul_eq_mapEdgeSet (zpowersHom _ shiftTwo)) hw).gibbsInvariant :=
  mem_gibbsInvariant_of_isProbabilityMeasure hw _

/-- `δ_odd` is an invariant Gibbs measure. -/
theorem dirac_oddPt_mem_gibbsInvariant {w : (nnGraph ℤ).edgeSet → ℝ} (hw : ∀ e, 0 < w e) :
    Measure.dirac oddPt ∈ ((nnGraph ℤ).dimerSpecification (Multiplicative ℤ)
      (Iso.exists_compHom_smul_eq_mapEdgeSet (zpowersHom _ shiftTwo)) hw).gibbsInvariant :=
  mem_gibbsInvariant_of_isProbabilityMeasure hw _

/-- The midpoint `(δ_even + δ_odd)/2` of the two point masses. -/
def diracMidpoint : Measure dimerSubshiftInt :=
  (2 : ℝ≥0∞)⁻¹ • Measure.dirac evenPt + (2 : ℝ≥0∞)⁻¹ • Measure.dirac oddPt

/-- The invariant event `{evenPt}` has measure `1/2` under the midpoint. -/
theorem diracMidpoint_singleton_evenPt : diracMidpoint {evenPt} = 2⁻¹ := by
  simp [diracMidpoint, Measure.dirac_apply' _ (measurableSet_singleton _), evenPt_ne_oddPt.symm]

/-- The complement of `{evenPt}` has measure `1/2` under the midpoint. -/
theorem diracMidpoint_compl_singleton_evenPt : diracMidpoint {evenPt}ᶜ = 2⁻¹ := by
  simp [diracMidpoint, Measure.dirac_apply' _ (measurableSet_singleton _).compl,
    evenPt_ne_oddPt.symm]

instance : IsProbabilityMeasure diracMidpoint :=
  ⟨by simp [diracMidpoint, ENNReal.inv_two_add_inv_two]⟩

/-- The midpoint `(δ_even + δ_odd)/2` is an invariant Gibbs measure. -/
theorem diracMidpoint_mem_gibbsInvariant {w : (nnGraph ℤ).edgeSet → ℝ} (hw : ∀ e, 0 < w e) :
    diracMidpoint ∈ ((nnGraph ℤ).dimerSpecification (Multiplicative ℤ)
      (Iso.exists_compHom_smul_eq_mapEdgeSet (zpowersHom _ shiftTwo)) hw).gibbsInvariant :=
  mem_gibbsInvariant_of_isProbabilityMeasure hw _

/-- **The midpoint is not ergodic**: the point `evenPt` (the event "the edge `{0, 1}` is
present") is `2ℤ`-invariant and has measure `1/2`. -/
theorem not_ergodicSMul_diracMidpoint :
    ¬ ErgodicSMul (Multiplicative ℤ) dimerSubshiftInt diracMidpoint :=
  not_ergodicSMul_of_forall_smul_eq smul_eq_self_dimerSubshiftInt
    (measurableSet_singleton evenPt).nullMeasurableSet
    (by simp [diracMidpoint_singleton_evenPt]) (by simp [diracMidpoint_compl_singleton_evenPt])

end TauCeti.Examples.DimerGibbsInvariant
