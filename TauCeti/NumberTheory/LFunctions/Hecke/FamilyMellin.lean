/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Finsupp.SymmetrizeInv
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.FiniteSum
public import TauCeti.NumberTheory.LFunctions.Hecke.RieszMellin
import TauCeti.Analysis.Contour.Residue.Germ

/-!
# Pole data for the Riesz Mellin expression of a Hecke family

A weighted family uses inverse-paired Mellin expressions, as appropriate for the real
parts of the Riesz remainders. At a point where the individual L-functions have no poles,
nonnegative weights prevent cancellation: the residues are nonnegative multiples of the
same complex factor. At real points strictly between zero and one this factor is positive.

The inverse-paired normalization and its use in Landau's theorem follow L. Alpöge's
`Deduction.Gm` and `Deduction.poleData` for Dirichlet characters.
-/

public section

open Complex Finset Set
open scoped ComplexConjugate

namespace TauCeti.LFunctions

variable {K : Type*} [Field K] [NumberField K]

/-- The real-linear combination of the normalized first Riesz Mellin expressions for
primitive ray class characters, averaging each character with its inverse. -/
noncomputable def heckeFamilyRieszRemainderMellin :
    (PrimitiveRayClassCharacter K →₀ ℝ) →ₗ[ℝ] (ℂ → ℂ) :=
  Finsupp.linearCombination ℝ fun ψ ↦ (2 : ℝ)⁻¹ •
    (rieszRemainderMellin (heckeLFunctionC ψ.character) +
      rieszRemainderMellin (heckeLFunctionC ψ⁻¹.character))

/-- Pointwise formula for the weighted, inverse-paired Riesz Mellin expression. -/
theorem heckeFamilyRieszRemainderMellin_apply (w : PrimitiveRayClassCharacter K →₀ ℝ) (z : ℂ) :
    heckeFamilyRieszRemainderMellin w z = w.sum (fun ψ c ↦ (c : ℂ) *
      ((rieszRemainderMellin (heckeLFunctionC ψ.character) z +
        rieszRemainderMellin (heckeLFunctionC ψ⁻¹.character) z) / 2)) := by
  simp only [heckeFamilyRieszRemainderMellin, Finsupp.linearCombination_apply, Finsupp.sum,
    Finset.sum_apply, Pi.smul_apply, Pi.add_apply, Complex.real_smul, Complex.ofReal_inv,
    Complex.ofReal_ofNat, div_eq_mul_inv, mul_comm _ (2 : ℂ)⁻¹]

/-- A singleton family contributes its weight times one inverse-paired average. -/
@[simp] theorem heckeFamilyRieszRemainderMellin_single
    (ψ : PrimitiveRayClassCharacter K) (c : ℝ) :
    heckeFamilyRieszRemainderMellin (Finsupp.single ψ c) = c • ((2 : ℝ)⁻¹ •
      (rieszRemainderMellin (heckeLFunctionC ψ.character) +
        rieszRemainderMellin (heckeLFunctionC ψ⁻¹.character))) := by
  simp only [heckeFamilyRieszRemainderMellin, Finsupp.linearCombination_single]

/-- An inverse-paired sum can instead be computed with symmetrized weights and no pairing. -/
theorem heckeFamilyRieszRemainderMellin_eq_sum_symmetrizeInv
    (w : PrimitiveRayClassCharacter K →₀ ℝ) :
    heckeFamilyRieszRemainderMellin w = ∑ ψ ∈ w.symmetrizeInv.support,
      w.symmetrizeInv ψ • rieszRemainderMellin (heckeLFunctionC ψ.character) := by
  exact ((w.sum_symmetrizeInv_smul (fun ψ ↦
    rieszRemainderMellin (heckeLFunctionC ψ.character))).trans
      (Finsupp.linearCombination_apply _ _).symm).symm

/-- The family expression is meromorphic on the plane. -/
theorem meromorphic_heckeFamilyRieszRemainderMellin (w : PrimitiveRayClassCharacter K →₀ ℝ) :
    Meromorphic (heckeFamilyRieszRemainderMellin w) := by
  rw [heckeFamilyRieszRemainderMellin_eq_sum_symmetrizeInv]
  exact Meromorphic.sum fun ψ _ ↦
    (meromorphicOn_univ.mp (meromorphicNFOn_rieszRemainderMellin _).meromorphicOn).const_smul _

/-- The Mellin normalization removes the singularity at one before summing. -/
theorem analyticAt_heckeFamilyRieszRemainderMellin_one (w : PrimitiveRayClassCharacter K →₀ ℝ) :
    AnalyticAt ℂ (heckeFamilyRieszRemainderMellin w) 1 := by
  rw [heckeFamilyRieszRemainderMellin_eq_sum_symmetrizeInv]
  apply Finset.analyticAt_sum
  intro ψ _
  have hL := meromorphicOn_univ.mp (meromorphicNFOn_heckeLFunctionC ψ.character).meromorphicOn
  exact hL.analyticAt_rieszRemainderMellin_one.const_smul

/-- Inverse pairing makes the family Mellin expression invariant under conjugate reflection. -/
@[simp] theorem heckeFamilyRieszRemainderMellin_apply_conj
    (w : PrimitiveRayClassCharacter K →₀ ℝ) (z : ℂ) :
    heckeFamilyRieszRemainderMellin w (conj z) = conj (heckeFamilyRieszRemainderMellin w z) := by
  rw [← Complex.conj_conj (heckeFamilyRieszRemainderMellin w (conj z)),
    heckeFamilyRieszRemainderMellin_apply, conj_finsupp_sum_rieszRemainderMellin_heckeLFunctionC,
    ← heckeFamilyRieszRemainderMellin_apply]

/-- Every pole of the family expression away from zero is at most simple, even for signed
weights. -/
theorem neg_one_le_meromorphicOrderAt_heckeFamilyRieszRemainderMellin
    (w : PrimitiveRayClassCharacter K →₀ ℝ) {z : ℂ} (hz : z ≠ 0) :
    -1 ≤ meromorphicOrderAt (heckeFamilyRieszRemainderMellin w) z := by
  rw [heckeFamilyRieszRemainderMellin_eq_sum_symmetrizeInv]
  exact neg_one_le_meromorphicOrderAt_sum_rieszRemainderMellin _
    (fun ψ _ ↦ meromorphicOn_univ.mp (meromorphicNFOn_heckeLFunctionC ψ.character).meromorphicOn)
    hz

/-- The residue of the family expression is the weighted sum of the individual orders, using
the symmetrized weights, divided by `z * (1 - z)`. An infinite order contributes zero. -/
theorem residue_heckeFamilyRieszRemainderMellin
    (w : PrimitiveRayClassCharacter K →₀ ℝ) {z : ℂ} (hz : z ≠ 0) :
    Contour.residue (heckeFamilyRieszRemainderMellin w) z =
      (↑(w.symmetrizeInv.sum fun ψ c ↦
        c * (meromorphicOrderAt (heckeLFunctionC ψ.character) z).untop₀) : ℂ) / (z * (1 - z)) := by
  rw [heckeFamilyRieszRemainderMellin_eq_sum_symmetrizeInv, Finsupp.sum]
  exact residue_sum_rieszRemainderMellin _
    (fun ψ _ ↦ meromorphicOn_univ.mp (meromorphicNFOn_heckeLFunctionC ψ.character).meromorphicOn)
    hz

private theorem sum_orders_nonneg {w : PrimitiveRayClassCharacter K →₀ ℝ} (hw : 0 ≤ w) {z : ℂ}
    (h₀ : ∀ ψ ∈ w.symmetrizeInv.support, 0 ≤ meromorphicOrderAt (heckeLFunctionC ψ.character) z) :
    0 ≤ ∑ ψ ∈ w.symmetrizeInv.support,
      w.symmetrizeInv ψ * ((meromorphicOrderAt (heckeLFunctionC ψ.character) z).untop₀ : ℝ) :=
  Finset.sum_nonneg fun ψ hψ ↦ mul_nonneg (Finsupp.le_def.mp (Finsupp.symmetrizeInv_nonneg hw) ψ)
    (by exact_mod_cast WithTop.untop₀_nonneg.mpr (h₀ ψ hψ))

private theorem sum_orders_pos_iff {w : PrimitiveRayClassCharacter K →₀ ℝ} (hw : 0 ≤ w) {z : ℂ}
    (h₀ : ∀ ψ ∈ w.symmetrizeInv.support, 0 ≤ meromorphicOrderAt (heckeLFunctionC ψ.character) z) :
    (0 < ∑ ψ ∈ w.symmetrizeInv.support,
      w.symmetrizeInv ψ * ((meromorphicOrderAt (heckeLFunctionC ψ.character) z).untop₀ : ℝ)) ↔
      ∃ ψ ∈ w.symmetrizeInv.support,
        0 < (meromorphicOrderAt (heckeLFunctionC ψ.character) z).untop₀ := by
  have hw' : ∀ ψ, 0 ≤ w.symmetrizeInv ψ :=
    fun ψ ↦ Finsupp.le_def.mp (Finsupp.symmetrizeInv_nonneg hw) ψ
  rw [Finset.sum_pos_iff_of_nonneg]
  · apply exists_congr
    intro ψ
    apply and_congr_right
    intro hψ
    have hc := (hw' ψ).lt_of_ne (Finsupp.mem_support_iff.mp hψ).symm
    rw [mul_pos_iff_of_pos_left hc, Int.cast_pos]
  · intro ψ hψ
    exact mul_nonneg (hw' ψ) (by exact_mod_cast WithTop.untop₀_nonneg.mpr (h₀ ψ hψ))

/-- Away from zero and one, if the supported L-functions and their inverses have no pole,
the family expression has a pole exactly when a supported L-function has a finite positive
order at the point or its conjugate. Identically zero germs contribute no residue. -/
theorem meromorphicOrderAt_heckeFamilyRieszRemainderMellin_neg_iff
    {w : PrimitiveRayClassCharacter K →₀ ℝ} (hw : 0 ≤ w) {z : ℂ} (hz : z ≠ 0) (h₁ : z ≠ 1)
    (h₀ : ∀ ψ ∈ w.symmetrizeInv.support, 0 ≤ meromorphicOrderAt (heckeLFunctionC ψ.character) z) :
    meromorphicOrderAt (heckeFamilyRieszRemainderMellin w) z < 0 ↔
      ∃ ψ ∈ w.support, 0 < (meromorphicOrderAt (heckeLFunctionC ψ.character) z).untop₀ ∨
        0 < (meromorphicOrderAt (heckeLFunctionC ψ.character) (conj z)).untop₀ := by
  rw [heckeFamilyRieszRemainderMellin_eq_sum_symmetrizeInv,
    meromorphicOrderAt_sum_rieszRemainderMellin_neg_iff _
      (fun ψ _ ↦ meromorphicOn_univ.mp (meromorphicNFOn_heckeLFunctionC ψ.character).meromorphicOn)
      hz h₁]
  rw [← (sum_orders_nonneg hw h₀).lt_iff_ne', sum_orders_pos_iff hw h₀]
  have hinv (ψ : PrimitiveRayClassCharacter K) :
      meromorphicOrderAt (heckeLFunctionC ψ⁻¹.character) z =
        meromorphicOrderAt (heckeLFunctionC ψ.character) (conj z) := by
    simpa only [PrimitiveRayClassCharacter.character_inv, Complex.conj_conj] using
      meromorphicOrderAt_heckeLFunctionC_inv_conj ψ.character (conj z)
  constructor
  · rintro ⟨ψ, hψ, ho⟩
    rcases (Finsupp.mem_support_symmetrizeInv hw ψ).mp hψ with hm | hm
    · exact ⟨ψ, hm, Or.inl ho⟩
    · refine ⟨ψ⁻¹, hm, Or.inr ?_⟩
      rw [← hinv ψ⁻¹, inv_inv]
      exact ho
  · rintro ⟨ψ, hm, ho | ho⟩
    · exact ⟨ψ, (Finsupp.mem_support_symmetrizeInv hw ψ).mpr (Or.inl hm), ho⟩
    · exact ⟨ψ⁻¹, (Finsupp.mem_support_symmetrizeInv hw ψ⁻¹).mpr (by simp [hm]), hinv ψ ▸ ho⟩

/-- At a real pole strictly between zero and one, if no L-function in the symmetrized
support has a pole there, the residue of a nonnegatively weighted family is positive real. -/
theorem residue_heckeFamilyRieszRemainderMellin_pos
    {w : PrimitiveRayClassCharacter K →₀ ℝ} (hw : 0 ≤ w) {r : ℝ} (hr : 0 < r) (hr₁ : r < 1)
    (h₀ : ∀ ψ ∈ w.symmetrizeInv.support,
      0 ≤ meromorphicOrderAt (heckeLFunctionC ψ.character) (r : ℂ))
    (hp : meromorphicOrderAt (heckeFamilyRieszRemainderMellin w) (r : ℂ) < 0) :
    ∃ a : ℝ, 0 < a ∧ Contour.residue (heckeFamilyRieszRemainderMellin w) (r : ℂ) = a := by
  have hr₀ := Complex.ofReal_ne_zero.mpr hr.ne'
  have hne := (Contour.meromorphicOrderAt_lt_zero_iff_residue_ne_zero
    (meromorphic_heckeFamilyRieszRemainderMellin w _)
    (neg_one_le_meromorphicOrderAt_heckeFamilyRieszRemainderMellin w hr₀)).mp hp
  let a : ℝ := (∑ ψ ∈ w.symmetrizeInv.support,
    w.symmetrizeInv ψ * ((meromorphicOrderAt (heckeLFunctionC ψ.character) (r : ℂ)).untop₀ : ℝ)) /
      (r * (1 - r))
  have heq : Contour.residue (heckeFamilyRieszRemainderMellin w) (r : ℂ) = (a : ℂ) := by
    simpa only [a, Finsupp.sum, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_sub,
      Complex.ofReal_one] using residue_heckeFamilyRieszRemainderMellin w hr₀
  have ha : 0 ≤ a := div_nonneg (sum_orders_nonneg hw h₀) (mul_nonneg hr.le (sub_nonneg.mpr hr₁.le))
  exact ⟨a, ha.lt_of_ne (Complex.ofReal_ne_zero.mp (heq ▸ hne)).symm, heq⟩

end TauCeti.LFunctions
