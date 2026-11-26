/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.Order
public import TauCeti.NumberTheory.DirichletCharacter.LFunction.Riesz.Mellin
public import TauCeti.NumberTheory.DirichletCharacter.Primitive.Bundle
import TauCeti.Analysis.Contour.Residue.Germ
import TauCeti.Analysis.Contour.Residue.Noncancellation
import TauCeti.Analysis.Meromorphic.Order
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Conjugate

/-!
# Poles of weighted Dirichlet Riesz remainder Mellin expressions

Take the weighted sum of the Mellin expressions for primitive Dirichlet characters, pairing
each character with its inverse to match the real part of its Riesz remainder. For nonnegative
weights, the residues away from `0` do not cancel: they share a common Riesz factor.
Thus at a point other than `0` there is a pole exactly when a positively weighted member's
`L`-function vanishes there or at the conjugate point, and poles on the positive real axis
have positive real residues. These are the pole data used in L. Alpöge's
`Deduction.poleData` (<https://github.com/leanprover-community/riemann-hypothesis>).
-/

public section

open Complex Finset
open scoped ComplexConjugate

namespace TauCeti

/-- The weighted sum of the Mellin expressions for the real parts of the Riesz remainders
of a finite family of primitive Dirichlet characters. Each term averages the expressions
for the character and its inverse. The weights need not be nonnegative to form the sum. -/
noncomputable def dirichletFamilyRieszRemainderMellin
    (w : PrimitiveDirichletCharacter →₀ ℝ) : ℂ → ℂ :=
  w.sum fun χ c ↦ ((c : ℂ) / 2) • (rieszRemainderMellin χ.character.LFunction +
    rieszRemainderMellin χ⁻¹.character.LFunction)

/-- Pointwise formula for the weighted, inverse-averaged Mellin expression. -/
theorem dirichletFamilyRieszRemainderMellin_apply (w : PrimitiveDirichletCharacter →₀ ℝ) (s : ℂ) :
    dirichletFamilyRieszRemainderMellin w s = w.sum (fun χ c ↦
      (c : ℂ) / 2 * (rieszRemainderMellin χ.character.LFunction s +
        rieszRemainderMellin χ⁻¹.character.LFunction s)) := by
  simp [dirichletFamilyRieszRemainderMellin, Finsupp.sum, Finset.sum_apply, smul_eq_mul, mul_add]

/-- The empty family's Mellin expression is zero. -/
@[simp] theorem dirichletFamilyRieszRemainderMellin_zero :
    dirichletFamilyRieszRemainderMellin 0 = 0 := by
  simp [dirichletFamilyRieszRemainderMellin]

/-- The Mellin expression of a single weighted character is its weight times the average
of the expressions for it and its inverse. -/
@[simp] theorem dirichletFamilyRieszRemainderMellin_single
    (χ : PrimitiveDirichletCharacter) (c : ℝ) :
    dirichletFamilyRieszRemainderMellin (Finsupp.single χ c) =
      ((c : ℂ) / 2) • (rieszRemainderMellin χ.character.LFunction +
        rieszRemainderMellin χ⁻¹.character.LFunction) := by
  unfold dirichletFamilyRieszRemainderMellin
  exact Finsupp.sum_single_index (by simp)

/-- Adding two weight families adds their Mellin expressions. -/
@[simp] theorem dirichletFamilyRieszRemainderMellin_add (w v : PrimitiveDirichletCharacter →₀ ℝ) :
    dirichletFamilyRieszRemainderMellin (w + v) =
      dirichletFamilyRieszRemainderMellin w + dirichletFamilyRieszRemainderMellin v := by
  unfold dirichletFamilyRieszRemainderMellin
  exact Finsupp.sum_add_index' (by simp) fun _ _ _ ↦ by rw [ofReal_add, add_div, add_smul]

/-- Scaling a weight family by a real number scales its Mellin expression. -/
@[simp] theorem dirichletFamilyRieszRemainderMellin_smul
    (a : ℝ) (w : PrimitiveDirichletCharacter →₀ ℝ) :
    dirichletFamilyRieszRemainderMellin (a • w) = a • dirichletFamilyRieszRemainderMellin w := by
  funext s
  rw [Pi.smul_apply, Complex.real_smul, dirichletFamilyRieszRemainderMellin_apply,
    dirichletFamilyRieszRemainderMellin_apply, Finsupp.sum_smul_index (by simp), Finsupp.mul_sum]
  exact Finset.sum_congr rfl fun χ _ ↦ by simp only [ofReal_mul, mul_div_assoc, mul_assoc]

private theorem meromorphic_rieszPair (χ : PrimitiveDirichletCharacter) :
    Meromorphic (rieszRemainderMellin χ.character.LFunction +
      rieszRemainderMellin χ⁻¹.character.LFunction) :=
  (meromorphicOn_univ.mp (meromorphicNFOn_rieszRemainderMellin _).meromorphicOn).add
    (meromorphicOn_univ.mp (meromorphicNFOn_rieszRemainderMellin _).meromorphicOn)

/-- Every weighted family Mellin expression is meromorphic on the plane. -/
theorem meromorphic_dirichletFamilyRieszRemainderMellin (w : PrimitiveDirichletCharacter →₀ ℝ) :
    Meromorphic (dirichletFamilyRieszRemainderMellin w) := by
  apply Meromorphic.sum
  intro χ _
  exact (meromorphic_rieszPair χ).const_smul _

/-- The family expression is analytic at every point with `1 ≤ Re s`, including `s = 1` where
normalization removes the singularity of the defining quotient. -/
theorem analyticAt_dirichletFamilyRieszRemainderMellin_of_one_le_re
    (w : PrimitiveDirichletCharacter →₀ ℝ) {s : ℂ} (hs : 1 ≤ s.re) :
    AnalyticAt ℂ (dirichletFamilyRieszRemainderMellin w) s := by
  apply Finset.analyticAt_sum
  intro χ _
  exact ((χ.character.analyticAt_rieszRemainderMellin_LFunction_of_one_le_re hs).add
    (χ⁻¹.character.analyticAt_rieszRemainderMellin_LFunction_of_one_le_re hs)).const_smul

private theorem neg_one_le_meromorphicOrderAt_rieszPair (χ : PrimitiveDirichletCharacter)
    {ρ : ℂ} (h₀ : ρ ≠ 0) :
    -1 ≤ meromorphicOrderAt (rieszRemainderMellin χ.character.LFunction +
      rieszRemainderMellin χ⁻¹.character.LFunction) ρ :=
  le_trans (le_min
    (χ.character.meromorphic_LFunction.neg_one_le_meromorphicOrderAt_rieszRemainderMellin h₀)
    (χ⁻¹.character.meromorphic_LFunction.neg_one_le_meromorphicOrderAt_rieszRemainderMellin
      h₀))
    (meromorphicOrderAt_add
      (meromorphicNFOn_rieszRemainderMellin _ (Set.mem_univ ρ)).meromorphicAt
      (meromorphicNFOn_rieszRemainderMellin _ (Set.mem_univ ρ)).meromorphicAt)

/-- Away from `0`, every pole of the weighted expression is at most simple, even for
signed weights. -/
theorem neg_one_le_meromorphicOrderAt_dirichletFamilyRieszRemainderMellin
    (w : PrimitiveDirichletCharacter →₀ ℝ) {ρ : ℂ} (h₀ : ρ ≠ 0) :
    -1 ≤ meromorphicOrderAt (dirichletFamilyRieszRemainderMellin w) ρ := by
  apply le_meromorphicOrderAt_sum
  · intro χ _
    exact (meromorphic_rieszPair χ ρ).const_smul _
  · intro χ hχ
    have hc : (w χ : ℂ) / 2 ≠ 0 :=
      div_ne_zero (ofReal_ne_zero.mpr (Finsupp.mem_support_iff.mp hχ)) (by norm_num)
    rw [meromorphicOrderAt_const_smul_eq_meromorphicOrderAt hc]
    exact neg_one_le_meromorphicOrderAt_rieszPair χ h₀

/-- The weighted sum over characters `χ` of the mean of the zero multiplicities of the
`L`-functions of `χ` and `χ⁻¹` at `ρ`. Away from `0`, it is the residue of
`dirichletFamilyRieszRemainderMellin w` at `ρ` times `ρ * (1 - ρ)`. -/
noncomputable def dirichletFamilyZeroMultiplicity (w : PrimitiveDirichletCharacter →₀ ℝ)
    (ρ : ℂ) : ℝ :=
  w.sum fun χ c ↦ c / 2 * ((analyticOrderNatAt χ.character.LFunction ρ : ℝ) +
    analyticOrderNatAt χ⁻¹.character.LFunction ρ)

/-- Formula for the weighted zero multiplicity as a finitely supported sum. -/
theorem dirichletFamilyZeroMultiplicity_def (w : PrimitiveDirichletCharacter →₀ ℝ) (ρ : ℂ) :
    dirichletFamilyZeroMultiplicity w ρ = w.sum (fun χ c ↦
      c / 2 * ((analyticOrderNatAt χ.character.LFunction ρ : ℝ) +
        analyticOrderNatAt χ⁻¹.character.LFunction ρ)) := (rfl)

/-- The empty family has zero weighted multiplicity. -/
@[simp] theorem dirichletFamilyZeroMultiplicity_zero (ρ : ℂ) :
    dirichletFamilyZeroMultiplicity 0 ρ = 0 := by
  rw [dirichletFamilyZeroMultiplicity_def, Finsupp.sum_zero_index]

/-- A single weighted character contributes its weight times the mean of the two
zero multiplicities for the character and its inverse. -/
@[simp] theorem dirichletFamilyZeroMultiplicity_single
    (χ : PrimitiveDirichletCharacter) (c : ℝ) (ρ : ℂ) :
    dirichletFamilyZeroMultiplicity (Finsupp.single χ c) ρ =
      c / 2 * ((analyticOrderNatAt χ.character.LFunction ρ : ℝ) +
        analyticOrderNatAt χ⁻¹.character.LFunction ρ) := by
  rw [dirichletFamilyZeroMultiplicity_def, Finsupp.sum_single_index (by simp)]

/-- Adding two weight families adds their weighted zero multiplicities. -/
@[simp] theorem dirichletFamilyZeroMultiplicity_add
    (w v : PrimitiveDirichletCharacter →₀ ℝ) (ρ : ℂ) :
    dirichletFamilyZeroMultiplicity (w + v) ρ =
      dirichletFamilyZeroMultiplicity w ρ + dirichletFamilyZeroMultiplicity v ρ := by
  simp only [dirichletFamilyZeroMultiplicity_def]
  exact Finsupp.sum_add_index' (by simp) (by simp [add_div, add_mul])

/-- Scaling a weight family by a real number scales its weighted zero multiplicity. -/
@[simp] theorem dirichletFamilyZeroMultiplicity_smul
    (a : ℝ) (w : PrimitiveDirichletCharacter →₀ ℝ) (ρ : ℂ) :
    dirichletFamilyZeroMultiplicity (a • w) ρ = a * dirichletFamilyZeroMultiplicity w ρ := by
  rw [dirichletFamilyZeroMultiplicity_def, dirichletFamilyZeroMultiplicity_def,
    Finsupp.sum_smul_index (by simp), Finsupp.mul_sum]
  exact Finset.sum_congr rfl fun χ _ ↦ by simp only [mul_div_assoc, mul_assoc]

/-- The weighted zero multiplicity is nonnegative for nonnegative weights. -/
theorem dirichletFamilyZeroMultiplicity_nonneg {w : PrimitiveDirichletCharacter →₀ ℝ}
    (hw : 0 ≤ w) (ρ : ℂ) : 0 ≤ dirichletFamilyZeroMultiplicity w ρ :=
  Finset.sum_nonneg fun χ _ ↦ by
    have : 0 ≤ w χ := by simpa using Finsupp.le_def.mp hw χ
    positivity

-- The averaged pair for one character, with its residue as a nonnegative real multiple of the
-- common Riesz denominator `(ρ * (1 - ρ))⁻¹`.
private theorem residue_rieszPair (χ : PrimitiveDirichletCharacter) {ρ : ℂ} (h₀ : ρ ≠ 0) :
    Contour.residue ((2⁻¹ : ℂ) • (rieszRemainderMellin χ.character.LFunction +
      rieszRemainderMellin χ⁻¹.character.LFunction)) ρ =
      (((analyticOrderNatAt χ.character.LFunction ρ : ℝ) +
        analyticOrderNatAt χ⁻¹.character.LFunction ρ) / 2) • (ρ * (1 - ρ))⁻¹ := by
  rw [Contour.residue_const_smul, Contour.residue_add
      (meromorphicNFOn_rieszRemainderMellin _ (Set.mem_univ ρ)).meromorphicAt
      (meromorphicNFOn_rieszRemainderMellin _ (Set.mem_univ ρ)).meromorphicAt,
    χ.character.residue_rieszRemainderMellin_LFunction h₀,
    χ⁻¹.character.residue_rieszRemainderMellin_LFunction h₀, Complex.real_smul, smul_eq_mul]
  push_cast
  ring

private theorem dirichletFamilyRieszRemainderMellin_eq_sum (w : PrimitiveDirichletCharacter →₀ ℝ) :
    dirichletFamilyRieszRemainderMellin w = ∑ χ ∈ w.support, (w χ : ℂ) •
      ((2⁻¹ : ℂ) • (rieszRemainderMellin χ.character.LFunction +
        rieszRemainderMellin χ⁻¹.character.LFunction)) := by
  simp only [dirichletFamilyRieszRemainderMellin, Finsupp.sum, smul_smul, div_eq_mul_inv]

/-- Away from `0`, the residue is the weighted zero multiplicity
`dirichletFamilyZeroMultiplicity w ρ` divided by the common Riesz denominator `ρ * (1 - ρ)`. -/
theorem residue_dirichletFamilyRieszRemainderMellin (w : PrimitiveDirichletCharacter →₀ ℝ)
    {ρ : ℂ} (h₀ : ρ ≠ 0) :
    Contour.residue (dirichletFamilyRieszRemainderMellin w) ρ =
      (dirichletFamilyZeroMultiplicity w ρ : ℂ) / (ρ * (1 - ρ)) := by
  rw [dirichletFamilyRieszRemainderMellin_eq_sum, Contour.residue_sum _
      fun χ _ ↦ ((meromorphic_rieszPair χ ρ).const_smul _).const_smul _,
    dirichletFamilyZeroMultiplicity, Finsupp.sum, ofReal_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun χ _ ↦ ?_
  rw [Contour.residue_const_smul, residue_rieszPair χ h₀, Complex.real_smul, smul_eq_mul]
  push_cast
  ring

-- A single averaged pair has a pole away from `0` exactly when `L(χ, ·)` vanishes at `ρ` or at
-- `conj ρ`; the two residues lie on a common ray, so they cannot cancel.
private theorem meromorphicOrderAt_rieszPair_neg_iff (χ : PrimitiveDirichletCharacter) {ρ : ℂ}
    (h₀ : ρ ≠ 0) :
    meromorphicOrderAt (rieszRemainderMellin χ.character.LFunction +
      rieszRemainderMellin χ⁻¹.character.LFunction) ρ < 0 ↔
    0 < meromorphicOrderAt χ.character.LFunction ρ ∨
      0 < meromorphicOrderAt χ.character.LFunction (conj ρ) := by
  let ψ : Fin 2 → PrimitiveDirichletCharacter := ![χ, χ⁻¹]
  have hsum : rieszRemainderMellin χ.character.LFunction +
      rieszRemainderMellin χ⁻¹.character.LFunction =
      ∑ i, rieszRemainderMellin (ψ i).character.LFunction := by
    simp [ψ, Fin.sum_univ_two]
  have hinv : meromorphicOrderAt χ⁻¹.character.LFunction ρ =
      meromorphicOrderAt χ.character.LFunction (conj ρ) := by
    simpa only [PrimitiveDirichletCharacter.character_inv, conj_conj] using
      χ.character.meromorphicOrderAt_LFunction_inv_conj (conj ρ)
  rw [hsum, Contour.meromorphicOrderAt_sum_lt_zero_iff_of_pairwise_sameRay
    (fun i _ ↦ (meromorphicNFOn_rieszRemainderMellin _ (Set.mem_univ ρ)).meromorphicAt)
    (fun i _ ↦
      (ψ i).character.meromorphic_LFunction.neg_one_le_meromorphicOrderAt_rieszRemainderMellin h₀)]
  · simp only [Finset.mem_univ, true_and, Fin.exists_fin_two, ψ, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    rw [χ.character.meromorphicOrderAt_rieszRemainderMellin_LFunction_neg_iff h₀,
      χ⁻¹.character.meromorphicOrderAt_rieszRemainderMellin_LFunction_neg_iff h₀, hinv]
  · intro i _ j _ _
    simp only [Function.onFun, DirichletCharacter.residue_rieszRemainderMellin_LFunction _ h₀,
      div_eq_mul_inv, ← ofReal_natCast, ← Complex.real_smul]
    exact ((SameRay.refl _).nonneg_smul_left (Nat.cast_nonneg _)).nonneg_smul_right
      (Nat.cast_nonneg _)

/-- For nonnegative weights, the family expression has a pole away from `0` exactly when
some positively weighted member vanishes there or at the conjugate point. -/
theorem meromorphicOrderAt_dirichletFamilyRieszRemainderMellin_neg_iff
    {w : PrimitiveDirichletCharacter →₀ ℝ} (hw : 0 ≤ w) {ρ : ℂ} (h₀ : ρ ≠ 0) :
    meromorphicOrderAt (dirichletFamilyRieszRemainderMellin w) ρ < 0 ↔
    ∃ χ ∈ w.support, 0 < meromorphicOrderAt χ.character.LFunction ρ ∨
      0 < meromorphicOrderAt χ.character.LFunction (conj ρ) := by
  have hnonneg (χ : PrimitiveDirichletCharacter) : 0 ≤ w χ := by
    simpa using Finsupp.le_def.mp hw χ
  have h2 : (2⁻¹ : ℂ) ≠ 0 := by norm_num
  rw [dirichletFamilyRieszRemainderMellin_eq_sum,
    Contour.meromorphicOrderAt_sum_smul_lt_zero_iff_of_pairwise_sameRay
      (fun χ _ ↦ (meromorphic_rieszPair χ ρ).const_smul _)
      (fun χ _ ↦ by
        rw [meromorphicOrderAt_const_smul_eq_meromorphicOrderAt h2]
        exact neg_one_le_meromorphicOrderAt_rieszPair χ h₀)
      (fun χ _ ↦ hnonneg χ)
      (fun χ _ ψ _ _ ↦ by
        simp only [Function.onFun, residue_rieszPair _ h₀]
        exact ((SameRay.refl _).nonneg_smul_left (by positivity)).nonneg_smul_right
          (by positivity))]
  refine exists_congr fun χ ↦ and_congr_right fun hχ ↦ ?_
  rw [and_iff_right ((hnonneg χ).lt_of_ne (Finsupp.mem_support_iff.mp hχ).symm),
    meromorphicOrderAt_const_smul_eq_meromorphicOrderAt h2,
    meromorphicOrderAt_rieszPair_neg_iff χ h₀]

/-- A pole of the weighted family expression away from `0` is simple, even for signed weights. -/
theorem dirichletFamilyRieszRemainderMellin_simplePole
    {w : PrimitiveDirichletCharacter →₀ ℝ} {ρ : ℂ} (h₀ : ρ ≠ 0)
    (hp : meromorphicOrderAt (dirichletFamilyRieszRemainderMellin w) ρ < 0) :
    meromorphicOrderAt (dirichletFamilyRieszRemainderMellin w) ρ = -1 := by
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hp.ne_top
  have hlo := neg_one_le_meromorphicOrderAt_dirichletFamilyRieszRemainderMellin w h₀
  rw [← hm] at hp hlo ⊢
  have hm_lt : m < 0 := by exact_mod_cast hp
  have hm_le : m ≤ -1 := by omega
  exact le_antisymm (WithTop.coe_le_coe.mpr hm_le) hlo

/-- Every pole of the family expression lies strictly left of `Re s = 1`. -/
theorem re_lt_one_of_dirichletFamilyRieszRemainderMellin_pole
    {w : PrimitiveDirichletCharacter →₀ ℝ} {ρ : ℂ}
    (hp : meromorphicOrderAt (dirichletFamilyRieszRemainderMellin w) ρ < 0) : ρ.re < 1 :=
  not_le.mp fun h ↦ hp.not_ge
    (analyticAt_dirichletFamilyRieszRemainderMellin_of_one_le_re w h).meromorphicOrderAt_nonneg

/-- For nonnegative weights, at any positive real pole the family expression has a strictly
positive real residue, which equals the leading Laurent coefficient because the pole is simple. -/
theorem exists_pos_meromorphicTrailingCoeffAt_dirichletFamilyRieszRemainderMellin
    {w : PrimitiveDirichletCharacter →₀ ℝ} (hw : 0 ≤ w) {β : ℝ} (hβ : 0 < β)
    (hp : meromorphicOrderAt (dirichletFamilyRieszRemainderMellin w) (β : ℂ) < 0) :
    ∃ c : ℝ, 0 < c ∧ meromorphicTrailingCoeffAt
      (dirichletFamilyRieszRemainderMellin w) (β : ℂ) = (c : ℂ) := by
  have h₀ := ofReal_ne_zero.mpr hβ.ne'
  have hord := dirichletFamilyRieszRemainderMellin_simplePole h₀ hp
  have hβ₁ : β < 1 := by simpa using re_lt_one_of_dirichletFamilyRieszRemainderMellin_pole hp
  have hres := (Contour.meromorphicOrderAt_lt_zero_iff_residue_ne_zero
    (meromorphic_dirichletFamilyRieszRemainderMellin w β)
    (neg_one_le_meromorphicOrderAt_dirichletFamilyRieszRemainderMellin w h₀)).mp hp
  rw [residue_dirichletFamilyRieszRemainderMellin w h₀, div_ne_zero_iff, ofReal_ne_zero] at hres
  have hpos := (dirichletFamilyZeroMultiplicity_nonneg hw β).lt_of_ne hres.1.symm
  refine ⟨_ / (β * (1 - β)), div_pos hpos (mul_pos hβ (sub_pos.mpr hβ₁)), ?_⟩
  rw [← Contour.residue_eq_meromorphicTrailingCoeffAt_of_order_eq_neg_one hord,
    residue_dirichletFamilyRieszRemainderMellin w h₀, ofReal_div, ofReal_mul, ofReal_sub,
    ofReal_one]

end TauCeti
