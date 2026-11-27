/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Quaternion.QuotientDeriv
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
import TauCeti.Analysis.Quaternion.Rigidity
import TauCeti.MeasureTheory.Integral.CurveIntegral.Basic
import TauCeti.MeasureTheory.Integral.CurveIntegral.Segment

/-!
# Ordered loop integrals of quaternionic `1`-forms

For `f : ℍ → ℍ`, the quaternion-valued `1`-forms `f dq` and `dq f` are the fields
`q ↦ (h ↦ f q * h)` and `q ↦ (h ↦ h * f q)`, that is `ContinuousLinearMap.mul ℝ ℍ (f q)` and
`(ContinuousLinearMap.mul ℝ ℍ).flip (f q)`. Their integrals around a closed polygon with vertices
`p 0, …, p (n - 1)` are the sums of the curve integrals along the edges from `p k` to
`p (finRotate n k)`.

Unlike holomorphic functions of one complex variable, quaternionic functions with a one-sided
quotient derivative satisfy no loop theorem for `dq`. On a connected open set such a function is
affine by quotient rigidity, and its loop integrals are given by commutators of consecutive
vertices (`TauCeti.LeftQuotientDifferentiableOn.sum_curveIntegral_segment_mul_flip`,
`TauCeti.RightQuotientDifferentiableOn.sum_curveIntegral_segment_mul`). Around the positively
oriented square `0 → i → i + j → j → 0` the identity, which has both slopes `1`, gives
`∮ q dq = 2k` and `∮ dq q = -2k` (`TauCeti.sum_curveIntegral_segment_square_mul`,
`TauCeti.sum_curveIntegral_segment_square_mul_flip`). Consequently every closed polygon in the
set has vanishing integral of `dq f` for a left quotient differentiable `f`, or of `f dq` for a
right quotient differentiable `f`, only when `f` is constant on the set
(`TauCeti.LeftQuotientDifferentiableOn.forall_sum_curveIntegral_segment_mul_flip_eq_zero_iff`,
`TauCeti.RightQuotientDifferentiableOn.forall_sum_curveIntegral_segment_mul_eq_zero_iff`).

## References

* A. Sudbery, *Quaternionic analysis*, Math. Proc. Cambridge Philos. Soc. 85 (1979),
  199–225, Theorem 1, for the classification of one-sided quaternionic differentiation.
* I. Frenkel and M. Libine, *Quaternionic analysis, representation theory and physics*,
  Adv. Math. 218 (2008), arXiv:0711.2699v5, §2.2, for the ordered quaternionic `1`-form `dq`.
-/

public section

open Set Quaternion

namespace TauCeti

variable {f : ℍ → ℍ} {s : Set ℍ} {n : ℕ}

/-- The commutators of consecutive vertices of the square with corner `q₀` and side `δ` in the
`(x, y)`-directions, oriented from `i` to `j`, sum to `4 δ² k`. -/
private theorem sum_mul_sub_mul_square (q₀ : ℍ) (δ : ℝ) :
    let p : Fin 4 → ℍ := ![q₀, q₀ + ⟨0, δ, 0, 0⟩, q₀ + ⟨0, δ, δ, 0⟩, q₀ + ⟨0, 0, δ, 0⟩]
    ∑ k, (p k * p (finRotate 4 k) - p (finRotate 4 k) * p k) = ⟨0, 0, 0, 4 * δ ^ 2⟩ := by
  intro p
  simp only [Fin.sum_univ_four, p, Fin.isValue, Matrix.cons_val_zero, finRotate_apply, zero_add,
    Matrix.cons_val_one, Fin.reduceAdd, Matrix.cons_val]
  ext <;> simp <;> ring

/-- The commutators of consecutive vertices of the square with corner `q₀` and side `δ`, taken in
the reverse order, sum to `-4 δ² k`. -/
private theorem sum_mul_sub_mul_square_rev (q₀ : ℍ) (δ : ℝ) :
    let p : Fin 4 → ℍ := ![q₀, q₀ + ⟨0, δ, 0, 0⟩, q₀ + ⟨0, δ, δ, 0⟩, q₀ + ⟨0, 0, δ, 0⟩]
    ∑ k, (p (finRotate 4 k) * p k - p k * p (finRotate 4 k)) = ⟨0, 0, 0, -4 * δ ^ 2⟩ := by
  intro p
  rw [← neg_inj, ← Finset.sum_neg_distrib]
  simp only [neg_sub]
  rw [sum_mul_sub_mul_square]
  ext <;> simp

/-- The integral of `q dq` around the positively oriented square with corner `q₀` and side `δ`
in the `(x, y)`-directions is `2 δ² k`. For `q₀ = 0` and `δ = 1` this is `∮ q dq = 2k` around
`0 → i → i + j → j → 0`. -/
theorem sum_curveIntegral_segment_square_mul (q₀ : ℍ) (δ : ℝ) :
    let p : Fin 4 → ℍ := ![q₀, q₀ + ⟨0, δ, 0, 0⟩, q₀ + ⟨0, δ, δ, 0⟩, q₀ + ⟨0, 0, δ, 0⟩]
    ∑ k, ∫ᶜ q in .segment (p k) (p (finRotate 4 k)), ContinuousLinearMap.mul ℝ ℍ q =
      ⟨0, 0, 0, 2 * δ ^ 2⟩ := by
  intro p
  have h := sum_curveIntegral_segment_mul_const_add_mul p 0 1
  simp only [zero_add, one_mul] at h
  rw [h, sum_mul_sub_mul_square]
  ext <;> simp
  ring

/-- The integral of `dq q` around the positively oriented square with corner `q₀` and side `δ`
in the `(x, y)`-directions is `-2 δ² k`. For `q₀ = 0` and `δ = 1` this is `∮ dq q = -2k` around
`0 → i → i + j → j → 0`. -/
theorem sum_curveIntegral_segment_square_mul_flip (q₀ : ℍ) (δ : ℝ) :
    let p : Fin 4 → ℍ := ![q₀, q₀ + ⟨0, δ, 0, 0⟩, q₀ + ⟨0, δ, δ, 0⟩, q₀ + ⟨0, 0, δ, 0⟩]
    ∑ k, ∫ᶜ q in .segment (p k) (p (finRotate 4 k)), (ContinuousLinearMap.mul ℝ ℍ).flip q =
      ⟨0, 0, 0, -2 * δ ^ 2⟩ := by
  intro p
  have h := sum_curveIntegral_segment_mul_flip_add_mul_const p 0 1
  simp only [zero_add, mul_one] at h
  rw [h, sum_mul_sub_mul_square_rev]
  ext <;> simp
  ring

/-- Around a closed polygon whose edges lie in `s`, the integral of `dq f` for `f` agreeing on `s`
with `q ↦ a + q * b` is the commutator sum of the vertices times `b / 2`. -/
private theorem sum_curveIntegral_segment_mul_flip_of_eqOn {a b : ℍ}
    (hab : ∀ q ∈ s, f q = a + q * b) (p : Fin n → ℍ)
    (hp : ∀ k, segment ℝ (p k) (p (finRotate n k)) ⊆ s) :
    ∑ k, ∫ᶜ q in .segment (p k) (p (finRotate n k)), (ContinuousLinearMap.mul ℝ ℍ).flip (f q) =
      (2 : ℝ)⁻¹ • ((∑ k, (p (finRotate n k) * p k - p k * p (finRotate n k))) * b) := by
  rw [← sum_curveIntegral_segment_mul_flip_add_mul_const p a b]
  refine Finset.sum_congr rfl fun k _ ↦ curveIntegral_congr ?_
  rw [Path.range_segment]
  intro q hq
  simp only [hab q (hp k hq)]

/-- Around a closed polygon whose edges lie in `s`, the integral of `f dq` for `f` agreeing on `s`
with `q ↦ a + b * q` is `b / 2` times the commutator sum of the vertices. -/
private theorem sum_curveIntegral_segment_mul_of_eqOn {a b : ℍ}
    (hab : ∀ q ∈ s, f q = a + b * q) (p : Fin n → ℍ)
    (hp : ∀ k, segment ℝ (p k) (p (finRotate n k)) ⊆ s) :
    ∑ k, ∫ᶜ q in .segment (p k) (p (finRotate n k)), ContinuousLinearMap.mul ℝ ℍ (f q) =
      (2 : ℝ)⁻¹ • (b * ∑ k, (p k * p (finRotate n k) - p (finRotate n k) * p k)) := by
  rw [← sum_curveIntegral_segment_mul_const_add_mul p a b]
  refine Finset.sum_congr rfl fun k _ ↦ curveIntegral_congr ?_
  rw [Path.range_segment]
  intro q hq
  simp only [hab q (hp k hq)]

/-- **Loop integrals of left quotient differentiable functions.** Let `f` have a left quotient
derivative at every point of a connected open set `s`, with left slope `b` at some point of `s`.
Around every closed polygon whose edges lie in `s`, the integral of `dq f` is half the sum of the
commutators `p (k + 1) * p k - p k * p (k + 1)` of consecutive vertices, times `b`. -/
theorem LeftQuotientDifferentiableOn.sum_curveIntegral_segment_mul_flip
    (hf : LeftQuotientDifferentiableOn f s) (hs : IsOpen s) (hc : IsPreconnected s) {q₀ b : ℍ}
    (hq₀ : q₀ ∈ s) (hb : HasLeftQuotientFDerivAt f q₀ b) (p : Fin n → ℍ)
    (hp : ∀ k, segment ℝ (p k) (p (finRotate n k)) ⊆ s) :
    ∑ k, ∫ᶜ q in .segment (p k) (p (finRotate n k)), (ContinuousLinearMap.mul ℝ ℍ).flip (f q) =
      (2 : ℝ)⁻¹ • ((∑ k, (p (finRotate n k) * p k - p k * p (finRotate n k))) * b) := by
  obtain ⟨a, c, hac⟩ := (leftQuotient_rigidity hs hc).mp hf
  have hcb : c = b := (((hasLeftQuotientFDerivAt_mul_const c q₀).const_add a).congr_of_eventuallyEq
    (Filter.eventually_of_mem (hs.mem_nhds hq₀) hac)).unique hb
  exact hcb ▸ sum_curveIntegral_segment_mul_flip_of_eqOn hac p hp

/-- **Loop integrals of right quotient differentiable functions.** Let `f` have a right quotient
derivative at every point of a connected open set `s`, with right slope `b` at some point of `s`.
Around every closed polygon whose edges lie in `s`, the integral of `f dq` is `b / 2` times the
sum of the commutators `p k * p (k + 1) - p (k + 1) * p k` of consecutive vertices. -/
theorem RightQuotientDifferentiableOn.sum_curveIntegral_segment_mul
    (hf : RightQuotientDifferentiableOn f s) (hs : IsOpen s) (hc : IsPreconnected s) {q₀ b : ℍ}
    (hq₀ : q₀ ∈ s) (hb : HasRightQuotientFDerivAt f q₀ b) (p : Fin n → ℍ)
    (hp : ∀ k, segment ℝ (p k) (p (finRotate n k)) ⊆ s) :
    ∑ k, ∫ᶜ q in .segment (p k) (p (finRotate n k)), ContinuousLinearMap.mul ℝ ℍ (f q) =
      (2 : ℝ)⁻¹ • (b * ∑ k, (p k * p (finRotate n k) - p (finRotate n k) * p k)) := by
  obtain ⟨a, c, hac⟩ := (rightQuotient_rigidity hs hc).mp hf
  have hcb : c = b := (((hasRightQuotientFDerivAt_const_mul c q₀).const_add a).congr_of_eventuallyEq
    (Filter.eventually_of_mem (hs.mem_nhds hq₀) hac)).unique hb
  exact hcb ▸ sum_curveIntegral_segment_mul_of_eqOn hac p hp

/-- Every neighbourhood of `q₀` contains a square with corner `q₀` and positive side in the
`(x, y)`-directions, edges included. -/
private theorem exists_square_segment_subset {q₀ : ℍ} (hs : s ∈ nhds q₀) :
    ∃ δ : ℝ, δ ≠ 0 ∧
      let p : Fin 4 → ℍ := ![q₀, q₀ + ⟨0, δ, 0, 0⟩, q₀ + ⟨0, δ, δ, 0⟩, q₀ + ⟨0, 0, δ, 0⟩]
      ∀ k, segment ℝ (p k) (p (finRotate 4 k)) ⊆ s := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hs
  refine ⟨ε / 2, by positivity, fun k ↦ ?_⟩
  have hmem : ∀ k, (![q₀, q₀ + ⟨0, ε / 2, 0, 0⟩, q₀ + ⟨0, ε / 2, ε / 2, 0⟩,
      q₀ + ⟨0, 0, ε / 2, 0⟩] : Fin 4 → ℍ) k ∈ Metric.ball q₀ ε := by
    intro k
    rw [mem_ball_iff_norm, ← pow_lt_pow_iff_left₀ (norm_nonneg _) hε.le two_ne_zero, sq,
      ← normSq_eq_norm_mul_self, normSq_def']
    fin_cases k <;> simp <;> nlinarith
  exact ((convex_ball q₀ ε).segment_subset (hmem _) (hmem _)).trans hball

/-- **No loop theorem for left quotient differentiable functions.** Let `f` have a left quotient
derivative at every point of a connected open set `s`. Then the integral of `dq f` vanishes
around every closed polygon whose edges lie in `s` exactly when `f` is constant on `s`. -/
theorem LeftQuotientDifferentiableOn.forall_sum_curveIntegral_segment_mul_flip_eq_zero_iff
    (hf : LeftQuotientDifferentiableOn f s) (hs : IsOpen s) (hc : IsPreconnected s) :
    (∀ (n : ℕ) (p : Fin n → ℍ), (∀ k, segment ℝ (p k) (p (finRotate n k)) ⊆ s) →
      ∑ k, ∫ᶜ q in .segment (p k) (p (finRotate n k)),
        (ContinuousLinearMap.mul ℝ ℍ).flip (f q) = 0) ↔
      ∃ c, ∀ q ∈ s, f q = c := by
  constructor
  · intro h
    obtain ⟨a, b, hab⟩ := (leftQuotient_rigidity hs hc).mp hf
    rcases s.eq_empty_or_nonempty with rfl | ⟨q₀, hq₀⟩
    · exact ⟨0, by simp⟩
    obtain ⟨δ, hδ, hp⟩ := exists_square_segment_subset (hs.mem_nhds hq₀)
    have hsq := sum_curveIntegral_segment_mul_flip_of_eqOn hab _ hp
    rw [h 4 _ hp, sum_mul_sub_mul_square_rev] at hsq
    have hb : b = 0 := by
      refine (by simpa using hsq.symm : _ ∨ b = 0).resolve_left fun h0 ↦ hδ ?_
      simpa using congrArg QuaternionAlgebra.imK h0
    exact ⟨a, fun q hq ↦ by rw [hab q hq, hb, mul_zero, add_zero]⟩
  · rintro ⟨c, hfc⟩ n p hp
    have hc' : ∀ q ∈ s, f q = c + q * 0 := fun q hq ↦ by rw [hfc q hq, mul_zero, add_zero]
    simp [sum_curveIntegral_segment_mul_flip_of_eqOn hc' p hp]

/-- **No loop theorem for right quotient differentiable functions.** Let `f` have a right quotient
derivative at every point of a connected open set `s`. Then the integral of `f dq` vanishes
around every closed polygon whose edges lie in `s` exactly when `f` is constant on `s`. -/
theorem RightQuotientDifferentiableOn.forall_sum_curveIntegral_segment_mul_eq_zero_iff
    (hf : RightQuotientDifferentiableOn f s) (hs : IsOpen s) (hc : IsPreconnected s) :
    (∀ (n : ℕ) (p : Fin n → ℍ), (∀ k, segment ℝ (p k) (p (finRotate n k)) ⊆ s) →
      ∑ k, ∫ᶜ q in .segment (p k) (p (finRotate n k)),
        ContinuousLinearMap.mul ℝ ℍ (f q) = 0) ↔
      ∃ c, ∀ q ∈ s, f q = c := by
  constructor
  · intro h
    obtain ⟨a, b, hab⟩ := (rightQuotient_rigidity hs hc).mp hf
    rcases s.eq_empty_or_nonempty with rfl | ⟨q₀, hq₀⟩
    · exact ⟨0, by simp⟩
    obtain ⟨δ, hδ, hp⟩ := exists_square_segment_subset (hs.mem_nhds hq₀)
    have hsq := sum_curveIntegral_segment_mul_of_eqOn hab _ hp
    rw [h 4 _ hp, sum_mul_sub_mul_square] at hsq
    have hb : b = 0 := by
      refine (by simpa using hsq.symm : b = 0 ∨ _).resolve_right fun h0 ↦ hδ ?_
      simpa using congrArg QuaternionAlgebra.imK h0
    exact ⟨a, fun q hq ↦ by rw [hab q hq, hb, zero_mul, add_zero]⟩
  · rintro ⟨c, hfc⟩ n p hp
    have hc' : ∀ q ∈ s, f q = c + 0 * q := fun q hq ↦ by rw [hfc q hq, zero_mul, add_zero]
    simp [sum_curveIntegral_segment_mul_of_eqOn hc' p hp]

end TauCeti
