/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Kernel
public import TauCeti.MeasureTheory.Function.Lp.Operator.Integral
public import TauCeti.MeasureTheory.Integral.DecayMajorant

/-!
# `Lᵖ` boundedness of quantizations with integrable kernels

A symbol `a` of order `m < -n` has an integrable frequency slice, so its quantization is the
integral operator `Op(a) u (x) = ∫ K_a(x, y) u(y) dy` with the continuous kernel
`K_a = TauCeti.quantizationKernel a`. The decay of `K_a` off the diagonal
(`TauCeti.Symbol.one_add_norm_div_pow_mul_norm_quantizationKernel_le`), with `n + 1` frequency
derivatives, makes its row integral at `x` finite. When the symbol estimates are moreover uniform
in the position (`TauCeti.Symbol.IsUniform`), the row and column integrals are bounded uniformly,
and Schur's test (`TauCeti.integralOperatorLp`) then bounds `Op(a)` on every `Lᵖ`, `1 ≤ p ≤ ∞`.

The bounds are stated in a scale-invariant form. If at every position
`∫ ‖a(x, ξ)‖ dξ ≤ A` and `∫ ‖∂_{ξ_j}^{n+1} a(x, ξ)‖ dξ ≤ A Rⁿ⁺¹` for every coordinate `j`, then
the row and column integrals of `‖K_a‖`, and hence the `Lᵖ` operator norm, are at most `C_n A Rⁿ`
with a constant `C_n` depending only on `n`. A uniform symbol of order `0` multiplied by a smooth
dyadic cutoff to frequencies of size `2^k` satisfies these hypotheses at every position with `A`
of size `2^{kn}` and `R = 2^{-k}`, so these dyadic pieces have `Lᵖ` norms bounded independently
of `k`; these are the diagonal estimates of the almost-orthogonality argument
(`TauCeti.norm_sum_le_of_almost_orthogonal`) for the `L²` boundedness of uniform operators of
order `0`.

## Main results

* `TauCeti.Symbol.lintegral_enorm_quantizationKernel_right_le` and
  `TauCeti.Symbol.lintegral_enorm_quantizationKernel_left_le`: the bounds
  `∫ ‖K_a(x, y)‖ dy ≤ C_n A Rⁿ` and `∫ ‖K_a(x, y)‖ dx ≤ C_n A Rⁿ`.
* `TauCeti.Symbol.quantizeLp`: for a symbol of order `m < -n` with estimates uniform in the
  position, the quantization as a bounded operator `Lᵖ(ℝⁿ; V) → Lᵖ(ℝⁿ; W)`.
* `TauCeti.Symbol.coeFn_quantizeLp_toLp`: on Schwartz functions it is `Op(a)`.
* `TauCeti.Symbol.norm_quantizeLp_le`: its norm is at most `C_n A Rⁿ`.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §3.
* G. B. Folland, *Real Analysis: Modern Techniques and Their Applications*, 2nd ed.,
  Theorem 6.18 (Schur's test).
-/

public section

open scoped SchwartzMap ENNReal NNReal
open MeasureTheory Real Module

noncomputable section

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m : ℝ}
  {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- **Schur bound in the second variable.** If at the position `x` the frequency slice of a
symbol of order `m < -n` has `∫ ‖a(x, ξ)‖ dξ ≤ A` and its `(n + 1)`-st frequency derivatives have
`∫ ‖∂_{ξ_j}^{n+1} a(x, ξ)‖ dξ ≤ A Rⁿ⁺¹`, then `∫ ‖K_a(x, y)‖ dy ≤ C_n A Rⁿ`, with a constant
`C_n` depending only on `n`. -/
theorem lintegral_enorm_quantizationKernel_right_le (a : Symbol n V W m) (hm : m < -n)
    {x : CoordinateSpace n} {A R : ℝ} (hR : 0 < R) (h₀ : ∫ ξ, ‖a.coefficient (x, ξ)‖ ≤ A)
    (h₁ : ∀ j, ∫ ξ, ‖mixedDeriv [] (List.replicate (n + 1) j) a.coefficient x ξ‖ ≤
      A * R ^ (n + 1)) :
    ∫⁻ y, ‖quantizationKernel a.coefficient x y‖ₑ ≤
      ENNReal.ofReal (2 ^ (n + 1) * (1 + √n ^ (n + 1)) * ((2 * π) ^ n)⁻¹ * A *
        (∫ w : CoordinateSpace n, ((1 + ‖w‖) ^ (n + 1))⁻¹) * R ^ n) := by
  have hA : 0 ≤ A := (integral_nonneg fun _ ↦ norm_nonneg _).trans h₀
  have h := lintegral_le_of_le_inv_one_add_norm_div_pow (μ := volume)
    (D := 2 ^ (n + 1) * (1 + √n ^ (n + 1)) * ((2 * π) ^ n)⁻¹ * A) hR (by positivity) x
    (f := fun y ↦ ‖quantizationKernel a.coefficient x y‖ₑ) fun y ↦ ?_
  · simpa only [finrank_euclideanSpace_fin] using h
  rw [← ofReal_norm, finrank_euclideanSpace_fin]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), mul_comm]
  exact a.one_add_norm_div_pow_mul_norm_quantizationKernel_le hm hR (n + 1) h₀ h₁ y

/-- **Schur bound in the first variable.** Under the bounds of
`TauCeti.Symbol.lintegral_enorm_quantizationKernel_right_le` at every position,
`∫ ‖K_a(x, y)‖ dx ≤ C_n A Rⁿ` for every `y`. -/
theorem lintegral_enorm_quantizationKernel_left_le (a : Symbol n V W m) (hm : m < -n)
    {A R : ℝ} (hR : 0 < R) (h₀ : ∀ x, ∫ ξ, ‖a.coefficient (x, ξ)‖ ≤ A)
    (h₁ : ∀ x j, ∫ ξ, ‖mixedDeriv [] (List.replicate (n + 1) j) a.coefficient x ξ‖ ≤
      A * R ^ (n + 1)) (y : CoordinateSpace n) :
    ∫⁻ x, ‖quantizationKernel a.coefficient x y‖ₑ ≤
      ENNReal.ofReal (2 ^ (n + 1) * (1 + √n ^ (n + 1)) * ((2 * π) ^ n)⁻¹ * A *
        (∫ w : CoordinateSpace n, ((1 + ‖w‖) ^ (n + 1))⁻¹) * R ^ n) := by
  have hA : 0 ≤ A := (integral_nonneg fun _ ↦ norm_nonneg _).trans (h₀ y)
  have h := lintegral_le_of_le_inv_one_add_norm_div_pow (μ := volume)
    (D := 2 ^ (n + 1) * (1 + √n ^ (n + 1)) * ((2 * π) ^ n)⁻¹ * A) hR (by positivity) y
    (f := fun x ↦ ‖quantizationKernel a.coefficient x y‖ₑ) fun x ↦ ?_
  · simpa only [finrank_euclideanSpace_fin] using h
  rw [← ofReal_norm, norm_sub_rev, finrank_euclideanSpace_fin]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), mul_comm]
  exact a.one_add_norm_div_pow_mul_norm_quantizationKernel_le hm hR (n + 1) (h₀ x) (h₁ x) y

/-- A uniform symbol of order `m < -n` satisfies the hypotheses of the Schur bounds with `R = 1`. -/
private theorem IsUniform.exists_integral_norm_le {a : Symbol n V W m} (ha : a.IsUniform)
    (hm : m < -n) :
    ∃ A, (∀ x, ∫ ξ, ‖a.coefficient (x, ξ)‖ ≤ A) ∧
      ∀ x j, ∫ ξ, ‖mixedDeriv [] (List.replicate (n + 1) j) a.coefficient x ξ‖ ≤ A := by
  have hweight := integrable_rpow_neg_one_add_norm_sq
    (μ := (volume : Measure (CoordinateSpace n))) (r := -m)
    (by simp only [finrank_euclideanSpace_fin]; linarith)
  simp only [neg_neg] at hweight
  obtain ⟨C₀, hC₀, h₀⟩ := isUniform_iff.1 ha [] []
  choose C hC h₁ using fun j : Fin n ↦ isUniform_iff.1 ha [] (List.replicate (n + 1) j)
  set I := ∫ ξ : CoordinateSpace n, (1 + ‖ξ‖ ^ 2) ^ (m / 2)
  refine ⟨(C₀ + ∑ j, C j) * I, fun x ↦ ?_, fun x j ↦ ?_⟩
  · refine (integral_mono_of_nonneg (ae_of_all _ fun _ ↦ norm_nonneg _) (hweight.const_mul C₀)
      (ae_of_all _ fun ξ ↦ by simpa using h₀ x ξ)).trans ?_
    rw [integral_const_mul]
    gcongr
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun j _ ↦ hC j)
  · refine (integral_mono_of_nonneg (ae_of_all _ fun _ ↦ norm_nonneg _) (hweight.const_mul (C j))
      (ae_of_all _ fun ξ ↦ (h₁ j x ξ).trans ?_)).trans ?_
    · refine mul_le_mul_of_nonneg_left (rpow_weight_le_rpow_weight ξ ?_) (hC j)
      rw [List.length_replicate]
      push_cast
      linarith
    rw [integral_const_mul]
    gcongr
    exact (Finset.single_le_sum (fun i _ ↦ hC i) (Finset.mem_univ j)).trans
      (le_add_of_nonneg_left hC₀)

/-- A uniform symbol of order `m < -n` has a kernel with uniformly bounded row and column
integrals. -/
private theorem IsUniform.exists_lintegral_enorm_quantizationKernel_le {a : Symbol n V W m}
    (ha : a.IsUniform) (hm : m < -n) :
    ∃ B : ℝ≥0, (∀ x, ∫⁻ y, ‖quantizationKernel a.coefficient x y‖ₑ ≤ B) ∧
      ∀ y, ∫⁻ x, ‖quantizationKernel a.coefficient x y‖ₑ ≤ B := by
  obtain ⟨A, h₀, h₁⟩ := ha.exists_integral_norm_le hm
  have h₁' (x j) : ∫ ξ, ‖mixedDeriv [] (List.replicate (n + 1) j) a.coefficient x ξ‖ ≤
      A * 1 ^ (n + 1) := by
    rw [one_pow, mul_one]
    exact h₁ x j
  refine ⟨Real.toNNReal (2 ^ (n + 1) * (1 + √n ^ (n + 1)) * ((2 * π) ^ n)⁻¹ * A *
    (∫ w : CoordinateSpace n, ((1 + ‖w‖) ^ (n + 1))⁻¹) * 1 ^ n),
    fun x ↦ ?_, fun y ↦ ?_⟩
  · rw [ENNReal.ofNNReal_toNNReal]
    exact a.lintegral_enorm_quantizationKernel_right_le hm one_pos (h₀ x) (h₁' x)
  · rw [ENNReal.ofNNReal_toNNReal]
    exact a.lintegral_enorm_quantizationKernel_left_le hm one_pos h₀ h₁' y

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

variable (p) in
/-- The quantization of a uniform symbol of order `m < -n` as a bounded operator
`Lᵖ(ℝⁿ; V) → Lᵖ(ℝⁿ; W)`, for `1 ≤ p ≤ ∞`: the integral operator with kernel `K_a`, whose row and
column integrals are bounded. On Schwartz functions it is the quantization
`TauCeti.quantizeSchwartzValue` (`TauCeti.Symbol.coeFn_quantizeLp_toLp`). -/
def quantizeLp (a : Symbol n V W m) (hm : m < -n) (ha : a.IsUniform) :
    Lp V p (volume : Measure (CoordinateSpace n)) →L[ℂ]
      Lp W p (volume : Measure (CoordinateSpace n)) :=
  integralOperatorLp (quantizationKernel a.coefficient) p
    (a.continuous_quantizationKernel hm).aestronglyMeasurable
    (ae_of_all _ (ha.exists_lintegral_enorm_quantizationKernel_le hm).choose_spec.1)
    (ae_of_all _ (ha.exists_lintegral_enorm_quantizationKernel_le hm).choose_spec.2)

variable {a : Symbol n V W m} {hm : m < -n} {ha : a.IsUniform}

/-- The operator `TauCeti.Symbol.quantizeLp` acts by `u ↦ (x ↦ ∫ K_a(x, y) u(y) dy)`. -/
theorem coeFn_quantizeLp (u : Lp V p (volume : Measure (CoordinateSpace n))) :
    a.quantizeLp p hm ha u =ᵐ[volume] fun x ↦ ∫ y, quantizationKernel a.coefficient x y (u y) :=
  coeFn_integralOperatorLp u

/-- On Schwartz functions, `TauCeti.Symbol.quantizeLp` is the quantization `Op(a)`. -/
theorem coeFn_quantizeLp_toLp [CompleteSpace V] [CompleteSpace W]
    (u : 𝓢(CoordinateSpace n, V)) :
    a.quantizeLp p hm ha (u.toLp p) =ᵐ[volume] quantizeSchwartzValue a.coefficient u := by
  filter_upwards [coeFn_quantizeLp (a := a) (hm := hm) (ha := ha) (u.toLp p)] with x hx
  rw [hx, quantizeSchwartzValue_eq_integral_quantizationKernel (a.integrable_coefficient hm x)]
  refine integral_congr_ae ?_
  filter_upwards [u.coeFn_toLp p] with y hy
  rw [hy]

/-- **Scale-invariant `Lᵖ` bound.** If `∫ ‖a(x, ξ)‖ dξ ≤ A` and
`∫ ‖∂_{ξ_j}^{n+1} a(x, ξ)‖ dξ ≤ A Rⁿ⁺¹` at every position and in every coordinate direction, then
`‖Op(a)‖_{Lᵖ → Lᵖ} ≤ C_n A Rⁿ`. -/
theorem norm_quantizeLp_le {A R : ℝ} (hR : 0 < R) (h₀ : ∀ x, ∫ ξ, ‖a.coefficient (x, ξ)‖ ≤ A)
    (h₁ : ∀ x j, ∫ ξ, ‖mixedDeriv [] (List.replicate (n + 1) j) a.coefficient x ξ‖ ≤
      A * R ^ (n + 1)) :
    ‖a.quantizeLp p hm ha‖ ≤ 2 ^ (n + 1) * (1 + √n ^ (n + 1)) * ((2 * π) ^ n)⁻¹ * A *
        (∫ w : CoordinateSpace n, ((1 + ‖w‖) ^ (n + 1))⁻¹) * R ^ n := by
  set B := 2 ^ (n + 1) * (1 + √n ^ (n + 1)) * ((2 * π) ^ n)⁻¹ * A *
    (∫ w : CoordinateSpace n, ((1 + ‖w‖) ^ (n + 1))⁻¹) * R ^ n
  have hrow (x) : ∫⁻ y, ‖quantizationKernel a.coefficient x y‖ₑ ≤ B.toNNReal := by
    rw [ENNReal.ofNNReal_toNNReal]
    exact a.lintegral_enorm_quantizationKernel_right_le hm hR (h₀ x) (h₁ x)
  have hcol (y) : ∫⁻ x, ‖quantizationKernel a.coefficient x y‖ₑ ≤ B.toNNReal := by
    rw [ENNReal.ofNNReal_toNNReal]
    exact a.lintegral_enorm_quantizationKernel_left_le hm hR h₀ h₁ y
  -- `quantizeLp` is the integral operator with these bounds.
  have h : a.quantizeLp p hm ha = integralOperatorLp (quantizationKernel a.coefficient) p
      (a.continuous_quantizationKernel hm).aestronglyMeasurable (ae_of_all _ hrow)
      (ae_of_all _ hcol) :=
    ContinuousLinearMap.ext fun u ↦ (integralOperatorLp_eq_iff.2 (coeFn_quantizeLp u).symm).symm
  rw [h]
  refine norm_integralOperatorLp_le_max.trans ?_
  have hA : 0 ≤ A := (integral_nonneg fun _ ↦ norm_nonneg _).trans (h₀ 0)
  rw [max_self, Real.coe_toNNReal _ (by positivity)]

end Symbol

end TauCeti
