/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Finsupp.SymmetrizeInv
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.FiniteSum
public import TauCeti.NumberTheory.LFunctions.Hecke.RieszMellin

/-!
# Pole data for the Riesz Mellin expression of a Hecke family

A weighted family uses inverse-paired Mellin expressions, as appropriate for the real
parts of the Riesz remainders. At a point where the individual L-functions have no poles,
nonnegative weights prevent cancellation: the residues are nonnegative multiples of the
same complex factor. At real points strictly between zero and one this factor is positive.

The inverse-paired normalization and its use in Landau's theorem follow L. Alpöge's
`Deduction.Gm` (`DedekindLFunctions/CharFamily.lean`) and `Deduction.poleData`
(`DedekindLFunctions/LandauTheorems/poleData.lean`) for Dirichlet characters, in
`src/Development/AutomorphicArithmetic/` of his
[Lean formalization](https://github.com/leanprover-community/riemann-hypothesis).
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
  exact meromorphic_sum_rieszRemainderMellin _

/-- The Mellin normalization removes the singularity at one before summing. -/
theorem analyticAt_heckeFamilyRieszRemainderMellin_one (w : PrimitiveRayClassCharacter K →₀ ℝ) :
    AnalyticAt ℂ (heckeFamilyRieszRemainderMellin w) 1 := by
  rw [heckeFamilyRieszRemainderMellin_eq_sum_symmetrizeInv]
  apply Finset.analyticAt_sum
  intro ψ _
  exact (meromorphic_heckeLFunctionC ψ.character).analyticAt_rieszRemainderMellin_one.const_smul

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
    (fun ψ _ ↦ meromorphic_heckeLFunctionC ψ.character) hz

/-- The residue of the family expression is the weighted sum of the individual orders, using
the symmetrized weights, divided by `z * (1 - z)`. An infinite order contributes zero. -/
theorem residue_heckeFamilyRieszRemainderMellin
    (w : PrimitiveRayClassCharacter K →₀ ℝ) {z : ℂ} (hz : z ≠ 0) :
    Contour.residue (heckeFamilyRieszRemainderMellin w) z =
      (↑(w.symmetrizeInv.sum fun ψ c ↦
        c * (meromorphicOrderAt (heckeLFunctionC ψ.character) z).untop₀) : ℂ) / (z * (1 - z)) := by
  rw [heckeFamilyRieszRemainderMellin_eq_sum_symmetrizeInv, Finsupp.sum]
  simp only [← Complex.coe_smul, ofReal_sum, ofReal_mul, ofReal_intCast]
  exact residue_sum_rieszRemainderMellin _
    (fun (ψ : PrimitiveRayClassCharacter K) _ ↦ meromorphic_heckeLFunctionC ψ.character) hz

/-- Away from zero and one, for nonnegative weights, if the L-functions in the symmetrized
support have no pole, the family expression has a pole exactly when a supported L-function
has a finite positive order at the point or its conjugate. Nonnegativity rules out
cancellation between residues; identically zero germs contribute no residue. -/
theorem meromorphicOrderAt_heckeFamilyRieszRemainderMellin_neg_iff
    {w : PrimitiveRayClassCharacter K →₀ ℝ} (hw : 0 ≤ w) {z : ℂ} (hz : z ≠ 0) (h₁ : z ≠ 1)
    (h₀ : ∀ ψ ∈ w.symmetrizeInv.support, 0 ≤ meromorphicOrderAt (heckeLFunctionC ψ.character) z) :
    meromorphicOrderAt (heckeFamilyRieszRemainderMellin w) z < 0 ↔
      ∃ ψ ∈ w.support, 0 < (meromorphicOrderAt (heckeLFunctionC ψ.character) z).untop₀ ∨
        0 < (meromorphicOrderAt (heckeLFunctionC ψ.character) (conj z)).untop₀ := by
  rw [heckeFamilyRieszRemainderMellin_eq_sum_symmetrizeInv,
    meromorphicOrderAt_sum_rieszRemainderMellin_neg_iff_of_nonneg
      (fun ψ _ ↦ Finsupp.le_def.mp (Finsupp.symmetrizeInv_nonneg hw) ψ)
      (fun ψ _ ↦ meromorphic_heckeLFunctionC ψ.character) h₀ hz h₁]
  have hinv (ψ : PrimitiveRayClassCharacter K) :
      meromorphicOrderAt (heckeLFunctionC ψ⁻¹.character) z =
        meromorphicOrderAt (heckeLFunctionC ψ.character) (conj z) := by
    simpa only [PrimitiveRayClassCharacter.character_inv, Complex.conj_conj] using
      meromorphicOrderAt_heckeLFunctionC_inv_conj ψ.character (conj z)
  constructor
  · rintro ⟨ψ, hψ, -, ho⟩
    rcases (Finsupp.mem_support_symmetrizeInv hw ψ).mp hψ with hm | hm
    · exact ⟨ψ, hm, Or.inl ho⟩
    · refine ⟨ψ⁻¹, hm, Or.inr ?_⟩
      rw [← hinv ψ⁻¹, inv_inv]
      exact ho
  · rintro ⟨ψ, hm, ho | ho⟩
    · have hψ := (Finsupp.mem_support_symmetrizeInv hw ψ).mpr (Or.inl hm)
      exact ⟨ψ, hψ, Finsupp.mem_support_iff.mp hψ, ho⟩
    · have hψ := (Finsupp.mem_support_symmetrizeInv hw ψ⁻¹).mpr (by simp [hm])
      exact ⟨ψ⁻¹, hψ, Finsupp.mem_support_iff.mp hψ, hinv ψ ▸ ho⟩

/-- At a real pole strictly between zero and one, if no L-function in the symmetrized
support has a pole there, the residue of a nonnegatively weighted family is positive real. -/
theorem exists_pos_residue_heckeFamilyRieszRemainderMellin_of_nonneg
    {w : PrimitiveRayClassCharacter K →₀ ℝ} (hw : 0 ≤ w) {r : ℝ} (hr : 0 < r) (hr₁ : r < 1)
    (h₀ : ∀ ψ ∈ w.symmetrizeInv.support,
      0 ≤ meromorphicOrderAt (heckeLFunctionC ψ.character) (r : ℂ))
    (hp : meromorphicOrderAt (heckeFamilyRieszRemainderMellin w) (r : ℂ) < 0) :
    ∃ a : ℝ, 0 < a ∧ Contour.residue (heckeFamilyRieszRemainderMellin w) (r : ℂ) = a := by
  rw [heckeFamilyRieszRemainderMellin_eq_sum_symmetrizeInv] at hp ⊢
  exact exists_pos_residue_sum_rieszRemainderMellin_of_nonneg
    (fun ψ _ ↦ Finsupp.le_def.mp (Finsupp.symmetrizeInv_nonneg hw) ψ)
    (fun ψ _ ↦ meromorphic_heckeLFunctionC ψ.character) hr hr₁ h₀ hp

end TauCeti.LFunctions
