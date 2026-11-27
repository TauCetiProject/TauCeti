/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.RemainderMellin
import Mathlib.Algebra.BigOperators.Field
import TauCeti.Analysis.Contour.Residue.Germ
import TauCeti.Analysis.Meromorphic.Order

/-!
# Poles of finite sums of Riesz Mellin expressions

A finite linear combination of first Riesz Mellin expressions has at most simple poles
away from zero. Their residues share the factor `1 / (z * (1 - z))`, so cancellation is
exactly cancellation in the weighted sum of the orders of the underlying functions. With
nonnegative real weights and pole-free summands there is no cancellation, and at real
points strictly between zero and one the residue is positive.
-/

public section

open Complex Finset Set

namespace TauCeti

variable {ι : Type*} {t : Finset ι} {L : ι → ℂ → ℂ} {z : ℂ}

/-- Away from zero a finite complex-weighted sum of Riesz Mellin expressions has at most
simple poles. No condition on the weights is needed. -/
theorem neg_one_le_meromorphicOrderAt_sum_rieszRemainderMellin (c : ι → ℂ)
    (hL : ∀ i ∈ t, Meromorphic (L i)) (hz : z ≠ 0) :
    -1 ≤ meromorphicOrderAt (∑ i ∈ t, c i • rieszRemainderMellin (L i)) z := by
  apply le_meromorphicOrderAt_sum
  · intro i _
    exact (meromorphicNFOn_rieszRemainderMellin _ (mem_univ z)).meromorphicAt.const_smul _
  · intro i hi
    by_cases hc : c i = 0
    · simp [hc]
    · rw [meromorphicOrderAt_const_smul_eq_meromorphicOrderAt hc]
      exact (hL i hi).neg_one_le_meromorphicOrderAt_rieszRemainderMellin hz

/-- The residue of a finite complex-weighted sum of Riesz Mellin expressions is the
weighted sum of orders divided by the common Riesz denominator. Infinite orders contribute
zero; at `z = 1` both sides are zero, by normalization and division by zero respectively. -/
theorem residue_sum_rieszRemainderMellin (c : ι → ℂ)
    (hL : ∀ i ∈ t, Meromorphic (L i)) (hz : z ≠ 0) :
    Contour.residue (∑ i ∈ t, c i • rieszRemainderMellin (L i)) z =
      (∑ i ∈ t, c i * ((meromorphicOrderAt (L i) z).untop₀ : ℂ)) / (z * (1 - z)) := by
  rw [Finset.sum_div, Contour.residue_sum t (fun i _ ↦
    (meromorphicNFOn_rieszRemainderMellin _ (mem_univ z)).meromorphicAt.const_smul _)]
  exact sum_congr rfl fun i hi ↦ by
    rw [Contour.residue_const_smul, (hL i hi).residue_rieszRemainderMellin hz,
      smul_eq_mul, mul_div_assoc]

/-- Off zero and one, the finite weighted Riesz Mellin sum has a pole exactly when its
weighted sum of orders (ignoring infinite orders) does not vanish. -/
theorem meromorphicOrderAt_sum_rieszRemainderMellin_neg_iff (c : ι → ℂ)
    (hL : ∀ i ∈ t, Meromorphic (L i)) (hz : z ≠ 0) (hz₁ : z ≠ 1) :
    meromorphicOrderAt (∑ i ∈ t, c i • rieszRemainderMellin (L i)) z < 0 ↔
      ∑ i ∈ t, c i * ((meromorphicOrderAt (L i) z).untop₀ : ℂ) ≠ 0 := by
  have hm : MeromorphicAt (∑ i ∈ t, c i • rieszRemainderMellin (L i)) z :=
    MeromorphicAt.sum fun i _ ↦
      (meromorphicNFOn_rieszRemainderMellin _ (mem_univ z)).meromorphicAt.const_smul _
  rw [Contour.meromorphicOrderAt_lt_zero_iff_residue_ne_zero hm
    (neg_one_le_meromorphicOrderAt_sum_rieszRemainderMellin c hL hz),
    residue_sum_rieszRemainderMellin c hL hz, div_ne_zero_iff]
  simp [hz, sub_ne_zero.mpr hz₁.symm]

private theorem sum_mul_untop₀_nonneg {c : ι → ℝ} (hc : ∀ i ∈ t, 0 ≤ c i)
    (h₀ : ∀ i ∈ t, 0 ≤ meromorphicOrderAt (L i) z) :
    0 ≤ ∑ i ∈ t, c i * ((meromorphicOrderAt (L i) z).untop₀ : ℝ) :=
  Finset.sum_nonneg fun i hi ↦
    mul_nonneg (hc i hi) (by exact_mod_cast WithTop.untop₀_nonneg.mpr (h₀ i hi))

private theorem residue_sum_rieszRemainderMellin_real (c : ι → ℝ)
    (hL : ∀ i ∈ t, Meromorphic (L i)) (hz : z ≠ 0) :
    Contour.residue (∑ i ∈ t, c i • rieszRemainderMellin (L i)) z =
      (↑(∑ i ∈ t, c i * ((meromorphicOrderAt (L i) z).untop₀ : ℝ)) : ℂ) / (z * (1 - z)) := by
  simp only [← Complex.coe_smul, residue_sum_rieszRemainderMellin _ hL hz, ofReal_sum,
    ofReal_mul, ofReal_intCast]

/-- Off zero and one, if the weights are nonnegative and no summand `L i` has a pole, the
real-weighted Riesz Mellin sum has a pole exactly when some summand with nonzero weight has
a finite positive order there. Nonnegativity rules out cancellation between residues. -/
theorem meromorphicOrderAt_sum_rieszRemainderMellin_neg_iff_of_nonneg {c : ι → ℝ}
    (hc : ∀ i ∈ t, 0 ≤ c i) (hL : ∀ i ∈ t, Meromorphic (L i))
    (h₀ : ∀ i ∈ t, 0 ≤ meromorphicOrderAt (L i) z) (hz : z ≠ 0) (hz₁ : z ≠ 1) :
    meromorphicOrderAt (∑ i ∈ t, c i • rieszRemainderMellin (L i)) z < 0 ↔
      ∃ i ∈ t, c i ≠ 0 ∧ 0 < (meromorphicOrderAt (L i) z).untop₀ := by
  have hm : MeromorphicAt (∑ i ∈ t, c i • rieszRemainderMellin (L i)) z :=
    MeromorphicAt.sum fun i _ ↦
      (meromorphicNFOn_rieszRemainderMellin _ (mem_univ z)).meromorphicAt.const_smul _
  rw [Contour.meromorphicOrderAt_lt_zero_iff_residue_ne_zero hm
    (by simpa only [← Complex.coe_smul] using
      neg_one_le_meromorphicOrderAt_sum_rieszRemainderMellin (fun i ↦ (c i : ℂ)) hL hz),
    residue_sum_rieszRemainderMellin_real c hL hz, div_ne_zero_iff, Complex.ofReal_ne_zero,
    ← (sum_mul_untop₀_nonneg hc h₀).lt_iff_ne', Finset.sum_pos_iff_of_nonneg fun i hi ↦
      mul_nonneg (hc i hi) (by exact_mod_cast WithTop.untop₀_nonneg.mpr (h₀ i hi))]
  simp only [hz, sub_ne_zero.mpr hz₁.symm, ne_eq, mul_eq_zero, or_self, not_false_eq_true,
    and_true]
  refine exists_congr fun i ↦ and_congr_right fun hi ↦ ?_
  rcases (hc i hi).eq_or_lt with h | h
  · simp [← h]
  · rw [mul_pos_iff_of_pos_left h, Int.cast_pos]
    exact ⟨fun h' ↦ ⟨h.ne', h'⟩, And.right⟩

/-- At a real pole strictly between zero and one, if the weights are nonnegative and no
summand `L i` has a pole there, the residue of the real-weighted Riesz Mellin sum is a
positive real number. -/
theorem exists_pos_residue_sum_rieszRemainderMellin_of_nonneg {c : ι → ℝ}
    (hc : ∀ i ∈ t, 0 ≤ c i) (hL : ∀ i ∈ t, Meromorphic (L i)) {r : ℝ} (hr : 0 < r)
    (hr₁ : r < 1) (h₀ : ∀ i ∈ t, 0 ≤ meromorphicOrderAt (L i) (r : ℂ))
    (hp : meromorphicOrderAt (∑ i ∈ t, c i • rieszRemainderMellin (L i)) (r : ℂ) < 0) :
    ∃ a : ℝ, 0 < a ∧ Contour.residue (∑ i ∈ t, c i • rieszRemainderMellin (L i)) (r : ℂ) = a := by
  have hr₀ := Complex.ofReal_ne_zero.mpr hr.ne'
  have hm : MeromorphicAt (∑ i ∈ t, c i • rieszRemainderMellin (L i)) (r : ℂ) :=
    MeromorphicAt.sum fun i _ ↦
      (meromorphicNFOn_rieszRemainderMellin _ (mem_univ _)).meromorphicAt.const_smul _
  have hne := (Contour.meromorphicOrderAt_lt_zero_iff_residue_ne_zero hm
    (by simpa only [← Complex.coe_smul] using
      neg_one_le_meromorphicOrderAt_sum_rieszRemainderMellin (fun i ↦ (c i : ℂ)) hL hr₀)).mp hp
  let a : ℝ := (∑ i ∈ t, c i * ((meromorphicOrderAt (L i) (r : ℂ)).untop₀ : ℝ)) / (r * (1 - r))
  have heq : Contour.residue (∑ i ∈ t, c i • rieszRemainderMellin (L i)) (r : ℂ) = (a : ℂ) := by
    simpa only [a, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_sub,
      Complex.ofReal_one] using residue_sum_rieszRemainderMellin_real c hL hr₀
  have ha : 0 ≤ a :=
    div_nonneg (sum_mul_untop₀_nonneg hc h₀) (mul_nonneg hr.le (sub_nonneg.mpr hr₁.le))
  exact ⟨a, ha.lt_of_ne (Complex.ofReal_ne_zero.mp (heq ▸ hne)).symm, heq⟩

end TauCeti
