/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Examples.Probability.Gibbs.Dimer

/-!
# Checks for invariant and ergodic dimer Gibbs measures on the line

On the nearest-neighbour graph of `ℤ` with `2ℤ` acting by translations (`ofAdd n` translating by
`2n`), the subshift `𝔛(ℤ)` has the two points `δ_even`, `δ_odd` of the even and the odd edges.

* Translations by even numbers preserve parity, so `2ℤ` fixes both points
  (`smul_eq_self_lineSubshift`) and every probability measure on `𝔛(ℤ)` is invariant.
* Every measure on `𝔛(ℤ)` is Gibbs for the dimer specification (on the line every completion set
  is a singleton), so `𝒢_inv` is the set of all probability measures, and `δ_even`, `δ_odd` and
  their midpoint lie in `𝒢_inv` (`dirac_even_mem_gibbsInvariant`, `dirac_odd_mem_gibbsInvariant`,
  `halfDirac_mem_gibbsInvariant`).
* `δ_even` and `δ_odd` are ergodic (`ergodicSMul_dirac`), while the midpoint is not
  (`not_ergodicSMul_halfDirac`): the event "the edge `{0, 1}` is present", the point `even`, is
  `2ℤ`-invariant of measure `1/2`.
-/

public section

noncomputable section

open SimpleGraph MeasureTheory Set Function TauCeti
open scoped ENNReal

namespace TauCeti.Examples.DimerGibbsInvariant

open TauCeti.Examples.DimerConfiguration TauCeti.Examples.DimerGibbs

/-- The subshift `𝔛(ℤ)` of dimer configurations of the line, for `2ℤ` acting by translations. -/
abbrev lineSubshift : Subshift (Multiplicative ℤ) (nnGraph ℤ).edgeSet Bool :=
  (nnGraph ℤ).dimerSubshift (Multiplicative ℤ)
    (Iso.exists_compHom_smul_eq_mapEdgeSet (zpowersHom _ shiftTwo))

/-- The even edges as a point of `𝔛(ℤ)`. -/
def evenPt : lineSubshift := ⟨evenConfig, mem_dimerSubshift.2 isDimerConfiguration_evenConfig⟩

/-- The odd edges as a point of `𝔛(ℤ)`. -/
def oddPt : lineSubshift := ⟨oddConfig, mem_dimerSubshift.2 isDimerConfiguration_oddConfig⟩

theorem evenPt_ne_oddPt : evenPt ≠ oddPt := fun h =>
  evenConfig_ne_oddConfig (congrArg Subtype.val h)

/-- The powers of the translation by `2` are the translations by even numbers. -/
theorem zpow_shiftTwo_apply (n a : ℤ) : (shiftTwo ^ n) a = a + 2 * n := by
  have hs (x : ℤ) : shiftTwo x = x + 2 := shiftTwo_apply x
  induction n using Int.induction_on generalizing a with
  | zero => simp
  | succ n ih =>
    rw [zpow_add_one, RelIso.mul_apply, ih, hs]
    ring
  | pred n ih =>
    rw [zpow_sub_one, RelIso.mul_apply, ih]
    have h := RelIso.apply_inv_self shiftTwo a
    rw [hs] at h
    linarith

/-- `ofAdd n` moves the edge `{a, a + 1}` to `{a + 2n, a + 2n + 1}`. -/
theorem smul_edge (n a : ℤ) :
    (Multiplicative.ofAdd n : Multiplicative ℤ) • DimerConfiguration.edge a =
      DimerConfiguration.edge (a + 2 * n) := by
  apply Subtype.ext
  change Sym2.map (shiftTwo ^ n) (DimerConfiguration.edge a : Sym2 ℤ) = _
  rw [coe_edge, coe_edge, Sym2.map_mk, zpow_shiftTwo_apply, zpow_shiftTwo_apply,
    show a + 1 + 2 * n = a + 2 * n + 1 by ring]

/-- **`2ℤ` fixes both points of `𝔛(ℤ)`**: translations by even numbers preserve parity. -/
theorem smul_eq_self_lineSubshift (g : Multiplicative ℤ) (ω : lineSubshift) : g • ω = ω := by
  have hω : ω.val = evenConfig ∨ ω.val = oddConfig := by
    have := ω.property
    rw [mem_dimerSubshift, ← mem_ofPred_eq (p := (nnGraph ℤ).IsDimerConfiguration),
      setOf_isDimerConfiguration_int] at this
    simpa using this
  apply Subtype.ext
  funext e
  obtain ⟨a, rfl⟩ := exists_edge_eq e
  rw [Subshift.smul_apply, ← ofAdd_toAdd g⁻¹, smul_edge]
  rcases hω with h | h <;> rw [h] <;> simp [Int.even_add, Int.odd_add, parity_simps]

/-- Every measure on `𝔛(ℤ)` is invariant under `2ℤ`. -/
theorem smulInvariantMeasure_lineSubshift (μ : Measure lineSubshift) :
    SMulInvariantMeasure (Multiplicative ℤ) lineSubshift μ :=
  ⟨fun g s _ => by
    rw [show (fun x : lineSubshift => g • x) ⁻¹' s = s from by
      ext ω
      simp [smul_eq_self_lineSubshift]]⟩

/-- On `𝔛(ℤ)`, a probability measure is an invariant Gibbs measure of the dimer specification. -/
theorem mem_gibbsInvariant_of_isProbabilityMeasure {w : (nnGraph ℤ).edgeSet → ℝ}
    (hw : ∀ e, 0 < w e) (μ : Measure lineSubshift) [IsProbabilityMeasure μ] :
    μ ∈ ((nnGraph ℤ).dimerSpecification (Multiplicative ℤ)
      (Iso.exists_compHom_smul_eq_mapEdgeSet (zpowersHom _ shiftTwo)) hw).gibbsInvariant :=
  Specification.mem_gibbsInvariant_iff.2
    ⟨TauCeti.MeasureTheory.mem_invariantMeasuresOfMeasureUnivEq_iff.2
      ⟨smulInvariantMeasure_lineSubshift μ, measure_univ⟩, isGibbs_dimerSpecification_int hw μ⟩

/-- `δ_even` is an invariant Gibbs measure. -/
theorem dirac_even_mem_gibbsInvariant {w : (nnGraph ℤ).edgeSet → ℝ} (hw : ∀ e, 0 < w e) :
    Measure.dirac evenPt ∈ ((nnGraph ℤ).dimerSpecification (Multiplicative ℤ)
      (Iso.exists_compHom_smul_eq_mapEdgeSet (zpowersHom _ shiftTwo)) hw).gibbsInvariant :=
  mem_gibbsInvariant_of_isProbabilityMeasure hw _

/-- `δ_odd` is an invariant Gibbs measure. -/
theorem dirac_odd_mem_gibbsInvariant {w : (nnGraph ℤ).edgeSet → ℝ} (hw : ∀ e, 0 < w e) :
    Measure.dirac oddPt ∈ ((nnGraph ℤ).dimerSpecification (Multiplicative ℤ)
      (Iso.exists_compHom_smul_eq_mapEdgeSet (zpowersHom _ shiftTwo)) hw).gibbsInvariant :=
  mem_gibbsInvariant_of_isProbabilityMeasure hw _

/-- The midpoint `(δ_even + δ_odd)/2` of the two point masses. -/
def halfDirac : Measure lineSubshift :=
  (2 : ℝ≥0∞)⁻¹ • Measure.dirac evenPt + (2 : ℝ≥0∞)⁻¹ • Measure.dirac oddPt

theorem halfDirac_apply_even : halfDirac {evenPt} = 2⁻¹ := by
  simp [halfDirac, Measure.dirac_apply' _ (measurableSet_singleton _), evenPt_ne_oddPt.symm]

theorem halfDirac_apply_compl_even : halfDirac {evenPt}ᶜ = 2⁻¹ := by
  simp [halfDirac, Measure.dirac_apply' _ (measurableSet_singleton _).compl, evenPt_ne_oddPt.symm]

instance : IsProbabilityMeasure halfDirac :=
  ⟨by simp [halfDirac, ENNReal.inv_two_add_inv_two]⟩

/-- The midpoint `(δ_even + δ_odd)/2` is an invariant Gibbs measure. -/
theorem halfDirac_mem_gibbsInvariant {w : (nnGraph ℤ).edgeSet → ℝ} (hw : ∀ e, 0 < w e) :
    halfDirac ∈ ((nnGraph ℤ).dimerSpecification (Multiplicative ℤ)
      (Iso.exists_compHom_smul_eq_mapEdgeSet (zpowersHom _ shiftTwo)) hw).gibbsInvariant :=
  mem_gibbsInvariant_of_isProbabilityMeasure hw _

/-- The point masses of `𝔛(ℤ)` are ergodic. -/
theorem ergodicSMul_dirac (ω : lineSubshift) :
    ErgodicSMul (Multiplicative ℤ) lineSubshift (Measure.dirac ω) where
  toSMulInvariantMeasure := smulInvariantMeasure_lineSubshift _
  aeconst_of_forall_preimage_smul_ae_eq _ _ := by
    rw [ae_dirac_eq, Filter.eventuallyEmptyOrUniv_iff, Filter.eventually_pure,
      Filter.eventually_pure]
    exact em _

/-- **The midpoint is not ergodic**: the point `even` (the event "the edge `{0, 1}` is present")
is `2ℤ`-invariant and has measure `1/2`. -/
theorem not_ergodicSMul_halfDirac : ¬ ErgodicSMul (Multiplicative ℤ) lineSubshift halfDirac := by
  intro h
  have hconst := h.aeconst_of_forall_preimage_smul_ae_eq (measurableSet_singleton evenPt)
    fun g => by
      rw [show (fun x : lineSubshift => g • x) ⁻¹' {evenPt} = {evenPt} from by
        ext ω
        simp [smul_eq_self_lineSubshift]]
  rcases Filter.eventuallyEmptyOrUniv_iff.1 hconst with h₁ | h₁
  · have h₂ : halfDirac {evenPt}ᶜ = 0 := measure_eq_zero_iff_ae_notMem.2 (by simpa using h₁)
    rw [halfDirac_apply_compl_even] at h₂
    simp at h₂
  · have h₂ : halfDirac {evenPt} = 0 := measure_eq_zero_iff_ae_notMem.2 h₁
    rw [halfDirac_apply_even] at h₂
    simp at h₂

end TauCeti.Examples.DimerGibbsInvariant
