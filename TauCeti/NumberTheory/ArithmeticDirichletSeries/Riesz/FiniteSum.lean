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
exactly cancellation in the weighted sum of the orders of the underlying functions.
-/

public section

open Complex Finset Set

namespace TauCeti

variable {ι : Type*} {t : Finset ι} {L : ι → ℂ → ℂ} {z : ℂ}

/-- Away from zero a finite real-weighted sum of Riesz Mellin expressions has at most
simple poles. No sign condition on the weights is needed. -/
theorem neg_one_le_meromorphicOrderAt_sum_rieszRemainderMellin (c : ι → ℝ)
    (hL : ∀ i ∈ t, Meromorphic (L i)) (hz : z ≠ 0) :
    -1 ≤ meromorphicOrderAt (∑ i ∈ t, c i • rieszRemainderMellin (L i)) z := by
  simp only [← Complex.coe_smul]
  apply le_meromorphicOrderAt_sum
  · intro i _
    exact (meromorphicNFOn_rieszRemainderMellin _ (mem_univ z)).meromorphicAt.const_smul _
  · intro i hi
    by_cases hc : (c i : ℂ) = 0
    · simp [hc]
    · rw [meromorphicOrderAt_const_smul_eq_meromorphicOrderAt hc]
      exact (hL i hi).neg_one_le_meromorphicOrderAt_rieszRemainderMellin hz

/-- The residue of a finite real-weighted sum of Riesz Mellin expressions is the weighted
sum of orders divided by the common Riesz denominator. Infinite orders contribute zero;
at `z = 1` both sides are zero, by normalization and division by zero respectively. -/
theorem residue_sum_rieszRemainderMellin (c : ι → ℝ)
    (hL : ∀ i ∈ t, Meromorphic (L i)) (hz : z ≠ 0) :
    Contour.residue (∑ i ∈ t, c i • rieszRemainderMellin (L i)) z =
      (↑(∑ i ∈ t, c i * (meromorphicOrderAt (L i) z).untop₀) : ℂ) / (z * (1 - z)) := by
  simp only [← Complex.coe_smul, ofReal_sum, ofReal_mul, ofReal_intCast, Finset.sum_div]
  rw [Contour.residue_sum t (fun i _ ↦
    (meromorphicNFOn_rieszRemainderMellin _ (mem_univ z)).meromorphicAt.const_smul _)]
  exact sum_congr rfl fun i hi ↦ by
    rw [Contour.residue_const_smul, (hL i hi).residue_rieszRemainderMellin hz,
      smul_eq_mul, mul_div_assoc]

/-- Off zero and one, the finite weighted Riesz Mellin sum has a pole exactly when its
weighted sum of orders (ignoring infinite orders) does not vanish. -/
theorem meromorphicOrderAt_sum_rieszRemainderMellin_neg_iff (c : ι → ℝ)
    (hL : ∀ i ∈ t, Meromorphic (L i)) (hz : z ≠ 0) (hz₁ : z ≠ 1) :
    meromorphicOrderAt (∑ i ∈ t, c i • rieszRemainderMellin (L i)) z < 0 ↔
      ∑ i ∈ t, c i * (meromorphicOrderAt (L i) z).untop₀ ≠ 0 := by
  have hm : MeromorphicAt (∑ i ∈ t, c i • rieszRemainderMellin (L i)) z := by
    simp only [← Complex.coe_smul]
    exact MeromorphicAt.sum fun i _ ↦
      (meromorphicNFOn_rieszRemainderMellin _ (mem_univ z)).meromorphicAt.const_smul _
  rw [Contour.meromorphicOrderAt_lt_zero_iff_residue_ne_zero hm
    (neg_one_le_meromorphicOrderAt_sum_rieszRemainderMellin c hL hz),
    residue_sum_rieszRemainderMellin c hL hz]
  rw [div_ne_zero_iff, Complex.ofReal_ne_zero]
  simp [hz, sub_ne_zero.mpr hz₁.symm]

end TauCeti
