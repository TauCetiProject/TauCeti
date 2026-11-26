/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.Order
public import TauCeti.NumberTheory.DirichletCharacter.LFunction.RieszMellin
public import TauCeti.NumberTheory.DirichletCharacter.Primitive.Bundle
import TauCeti.Analysis.Contour.Residue.Germ
import TauCeti.Analysis.Meromorphic.Order
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Conjugate

/-!
# Poles of weighted Dirichlet Riesz remainder Mellin expressions

Take the weighted sum of the Mellin expressions for primitive Dirichlet characters, pairing
each character with its inverse to match the real part of its Riesz remainder. For nonnegative
weights, the residues do not cancel: the sole complex factor is the common Riesz denominator.
The poles thus detect every positively weighted zero and its conjugate, and real poles have
positive residues. These are the pole data used in L. Alpöge's `Deduction.poleData`
(<https://github.com/leanprover-community/riemann-hypothesis>).
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
    exact (le_min (χ.character.neg_one_le_meromorphicOrderAt_rieszRemainderMellin_LFunction h₀)
      (χ⁻¹.character.neg_one_le_meromorphicOrderAt_rieszRemainderMellin_LFunction h₀)).trans
      (meromorphicOrderAt_add
        (meromorphicNFOn_rieszRemainderMellin _ (Set.mem_univ ρ)).meromorphicAt
        (meromorphicNFOn_rieszRemainderMellin _ (Set.mem_univ ρ)).meromorphicAt)

/-- Away from `0`, the residue is the weighted mean of the two zero multiplicities per
character, divided by the common Riesz denominator. -/
theorem residue_dirichletFamilyRieszRemainderMellin (w : PrimitiveDirichletCharacter →₀ ℝ)
    {ρ : ℂ} (h₀ : ρ ≠ 0) :
    Contour.residue (dirichletFamilyRieszRemainderMellin w) ρ =
      (w.sum (fun χ c ↦ c / 2 * ((analyticOrderNatAt χ.character.LFunction ρ : ℝ) +
        analyticOrderNatAt χ⁻¹.character.LFunction ρ)) : ℝ) / (ρ * (1 - ρ)) := by
  rw [dirichletFamilyRieszRemainderMellin, Finsupp.sum, Contour.residue_sum]
  · simp only [Finsupp.sum, ofReal_sum, div_eq_mul_inv, Finset.sum_mul]
    refine Finset.sum_congr rfl fun χ _ ↦ ?_
    rw [Contour.residue_const_smul, Contour.residue_add
      (meromorphicNFOn_rieszRemainderMellin _ (Set.mem_univ ρ)).meromorphicAt
      (meromorphicNFOn_rieszRemainderMellin _ (Set.mem_univ ρ)).meromorphicAt,
      χ.character.residue_rieszRemainderMellin_LFunction h₀,
      χ⁻¹.character.residue_rieszRemainderMellin_LFunction h₀]
    push_cast
    simp only [smul_eq_mul, div_eq_mul_inv, ← add_mul, mul_assoc]
  · intro χ _
    exact (meromorphic_rieszPair χ ρ).const_smul _

private theorem familyMultiplicity_pos_iff (w : PrimitiveDirichletCharacter →₀ ℝ)
    (hw : 0 ≤ w) (ρ : ℂ) :
    0 < w.sum (fun χ c ↦ c / 2 * ((analyticOrderNatAt χ.character.LFunction ρ : ℝ) +
      analyticOrderNatAt χ⁻¹.character.LFunction ρ)) ↔
    ∃ χ ∈ w.support, 0 < meromorphicOrderAt χ.character.LFunction ρ ∨
      0 < meromorphicOrderAt χ.character.LFunction (conj ρ) := by
  have hnonneg (χ : PrimitiveDirichletCharacter) : 0 ≤ w χ := by
    simpa using (Finsupp.le_def.mp hw χ)
  rw [Finsupp.sum, Finset.sum_pos_iff_of_nonneg (fun χ _ ↦ by
    have := hnonneg χ
    positivity)]
  refine exists_congr fun χ ↦ and_congr_right fun hχ ↦ ?_
  have hc := (hnonneg χ).lt_of_ne (Finsupp.mem_support_iff.mp hχ).symm
  have hpos (ψ : PrimitiveDirichletCharacter) :
      0 < (analyticOrderNatAt ψ.character.LFunction ρ : ℝ) ↔
        0 < meromorphicOrderAt ψ.character.LFunction ρ := by
    rw [Nat.cast_pos]
    exact ψ.character.one_le_analyticOrderNatAt_LFunction_iff.trans
      ψ.character.meromorphicOrderAt_LFunction_pos_iff.symm
  have hinv : meromorphicOrderAt χ⁻¹.character.LFunction ρ =
      meromorphicOrderAt χ.character.LFunction (conj ρ) := by
    simpa only [PrimitiveDirichletCharacter.character_inv, conj_conj] using
      χ.character.meromorphicOrderAt_LFunction_inv_conj (conj ρ)
  rw [mul_pos_iff_of_pos_left (half_pos hc), ← Nat.cast_add, Nat.cast_pos,
    Nat.add_pos_iff_pos_or_pos]
  simpa only [Nat.cast_pos, hinv] using (hpos χ).or (hpos χ⁻¹)

/-- For nonnegative weights, the family expression has a pole away from `0` exactly when
some positively weighted member vanishes there or at the conjugate point. -/
theorem meromorphicOrderAt_dirichletFamilyRieszRemainderMellin_neg_iff
    {w : PrimitiveDirichletCharacter →₀ ℝ} (hw : 0 ≤ w) {ρ : ℂ} (h₀ : ρ ≠ 0) :
    meromorphicOrderAt (dirichletFamilyRieszRemainderMellin w) ρ < 0 ↔
    ∃ χ ∈ w.support, 0 < meromorphicOrderAt χ.character.LFunction ρ ∨
      0 < meromorphicOrderAt χ.character.LFunction (conj ρ) := by
  by_cases h₁ : ρ = 1
  · subst ρ
    apply iff_of_false (not_lt.mpr
      (analyticAt_dirichletFamilyRieszRemainderMellin_of_one_le_re w
        (s := 1) (by simp)).meromorphicOrderAt_nonneg)
    rintro ⟨χ, -, hz⟩
    have hz' : 0 < meromorphicOrderAt χ.character.LFunction 1 := by simpa using hz
    obtain ⟨hz₀, hreg⟩ := χ.character.meromorphicOrderAt_LFunction_pos_iff.mp hz'
    simpa using χ.character.re_lt_one_of_LFunction_eq_zero hreg hz₀
  rw [Contour.meromorphicOrderAt_lt_zero_iff_residue_ne_zero
    (meromorphic_dirichletFamilyRieszRemainderMellin w ρ)
    (neg_one_le_meromorphicOrderAt_dirichletFamilyRieszRemainderMellin w h₀),
    residue_dirichletFamilyRieszRemainderMellin w h₀,
    div_ne_zero_iff, and_iff_left (mul_ne_zero h₀ (sub_ne_zero.mpr (Ne.symm h₁)))]
  have hnonneg (χ : PrimitiveDirichletCharacter) : 0 ≤ w χ := by
    simpa using (Finsupp.le_def.mp hw χ)
  rw [ofReal_ne_zero, ← familyMultiplicity_pos_iff w hw ρ]
  have hsum : 0 ≤ w.sum (fun χ c ↦ c / 2 * ((analyticOrderNatAt χ.character.LFunction ρ : ℝ) +
      analyticOrderNatAt χ⁻¹.character.LFunction ρ)) :=
    Finset.sum_nonneg fun χ _ ↦ by
      have := hnonneg χ
      positivity
  exact ⟨fun h ↦ hsum.lt_of_ne h.symm, ne_of_gt⟩

/-- A pole of the weighted family expression away from `0` is simple, even for signed weights. -/
theorem dirichletFamilyRieszRemainderMellin_simplePole
    {w : PrimitiveDirichletCharacter →₀ ℝ} {ρ : ℂ} (h₀ : ρ ≠ 0)
    (hp : meromorphicOrderAt (dirichletFamilyRieszRemainderMellin w) ρ < 0) :
    meromorphicOrderAt (dirichletFamilyRieszRemainderMellin w) ρ = -1 := by
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hp.ne_top
  have hlo := neg_one_le_meromorphicOrderAt_dirichletFamilyRieszRemainderMellin w h₀
  rw [← hm] at hp hlo ⊢
  have hm₀ : m < 0 := WithTop.coe_lt_coe.mp hp
  have hm₁ : (-1 : ℤ) ≤ m := WithTop.coe_le_coe.mp hlo
  have hm' : m = -1 := by omega
  exact congrArg ((↑) : ℤ → WithTop ℤ) hm'

/-- Every pole of the family expression lies strictly left of `Re s = 1`. -/
theorem re_lt_one_of_dirichletFamilyRieszRemainderMellin_pole
    {w : PrimitiveDirichletCharacter →₀ ℝ} {ρ : ℂ}
    (hp : meromorphicOrderAt (dirichletFamilyRieszRemainderMellin w) ρ < 0) : ρ.re < 1 :=
  not_le.mp fun h ↦ hp.not_ge
    (analyticAt_dirichletFamilyRieszRemainderMellin_of_one_le_re w h).meromorphicOrderAt_nonneg

/-- At any positive real pole the family expression has a strictly positive real residue,
which equals the leading Laurent coefficient because the pole is simple. -/
theorem exists_pos_meromorphicTrailingCoeffAt_dirichletFamilyRieszRemainderMellin
    {w : PrimitiveDirichletCharacter →₀ ℝ} (hw : 0 ≤ w) {β : ℝ} (hβ : 0 < β)
    (hp : meromorphicOrderAt (dirichletFamilyRieszRemainderMellin w) (β : ℂ) < 0) :
    ∃ c : ℝ, 0 < c ∧ meromorphicTrailingCoeffAt
      (dirichletFamilyRieszRemainderMellin w) (β : ℂ) = (c : ℂ) := by
  have h₀ := ofReal_ne_zero.mpr hβ.ne'
  have hord := dirichletFamilyRieszRemainderMellin_simplePole h₀ hp
  have hβ₁ : β < 1 := by simpa using re_lt_one_of_dirichletFamilyRieszRemainderMellin_pole hp
  have hpos := (familyMultiplicity_pos_iff w hw (β : ℂ)).mpr
    ((meromorphicOrderAt_dirichletFamilyRieszRemainderMellin_neg_iff hw h₀).mp hp)
  refine ⟨_ / (β * (1 - β)), div_pos hpos (mul_pos hβ (sub_pos.mpr hβ₁)), ?_⟩
  rw [← Contour.residue_eq_meromorphicTrailingCoeffAt_of_order_eq_neg_one hord,
    residue_dirichletFamilyRieszRemainderMellin w h₀]
  push_cast
  rfl

end TauCeti
