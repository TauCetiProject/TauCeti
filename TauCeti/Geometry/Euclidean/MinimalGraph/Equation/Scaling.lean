/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Euclidean.MinimalGraph.Equation.Operator
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import TauCeti.Analysis.Calculus.Gradient
public import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
public import TauCeti.Analysis.Calculus.IteratedFDeriv.CompContinuousLinearEquiv
public import TauCeti.Analysis.Calculus.MeanValue
public import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic

/-!
# Scaling and normalization of Euclidean minimal graphs

Simultaneously dilating the horizontal and vertical coordinates leaves the gradient unchanged
at the corresponding point and multiplies the native minimal graph operator by the reciprocal
scale. Centering at a point and dividing the height by the radius gives the inverse normalization:
the gradient is unchanged and the native operator is multiplied by the radius.

All finite derivative and native operator identities hold without regularity assumptions,
including at scale zero. Gradient identities require nonzero scales. Height centering disappears
only at positive derivative orders. Nonnegative scales give exact derivative norm identities.
Positive scales transport differentiability between the corresponding balls. A gradient bound
on the original ball controls the normalized height by the mean value inequality.

## Main declarations

* `TauCeti.MinimalGraph.iteratedFDeriv_dilatedHeight`: the exact finite-order dilation factor.
* `TauCeti.MinimalGraph.iteratedFDeriv_normalizedHeight`: positive-order normalization factors.
* `TauCeti.MinimalGraph.nondivergenceOperator_normalizedHeight`: native graph equation scaling.
* `TauCeti.MinimalGraph.contDiffOn_normalizedHeight_ball`: regularity on a fixed normalized ball.
* `TauCeti.MinimalGraph.abs_normalizedHeight_le`: a height bound from the gradient bound.
-/

public noncomputable section

open InnerProductSpace Metric Set
open scoped ContDiff Gradient Laplacian

namespace TauCeti.MinimalGraph

section Jets

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem iteratedFDeriv_const_mul_nonzero (u : E → ℝ) {a : ℝ} (ha : a ≠ 0)
    (x : E) (k : ℕ) :
    iteratedFDeriv ℝ k (fun y ↦ a * u y) x = a • iteratedFDeriv ℝ k u x := by
  have h := (ContinuousLinearEquiv.smulLeft (Units.mk0 a ha) : ℝ ≃L[ℝ] ℝ)
    |>.iteratedFDeriv_comp_left (f := u) (x := x) (i := k)
  ext v
  simpa [Function.comp_def] using congrArg (fun L ↦ L v) h

/-- Dilating a graph scales its iterated derivatives by the corresponding degree. -/
theorem iteratedFDeriv_dilatedHeight (u : E → ℝ) (r : ℝ)
    (x : E) (k : ℕ) :
    iteratedFDeriv ℝ k (fun y ↦ r * u (r⁻¹ • y)) x =
      (r * (r⁻¹) ^ k) • iteratedFDeriv ℝ k u (r⁻¹ • x) := by
  by_cases hr : r = 0
  · subst r
    simp
  rw [iteratedFDeriv_const_mul_nonzero _ hr,
    TauCeti.iteratedFDeriv_comp_const_smul_apply, smul_smul]

/-- Normalizing a graph scales its positive-order iterated derivatives by its radius. -/
theorem iteratedFDeriv_normalizedHeight (u : E → ℝ) (p : E) (R : ℝ)
    (x : E) (k : ℕ) (hk : 1 ≤ k) :
    iteratedFDeriv ℝ k (fun y ↦ R⁻¹ * (u (p + R • y) - u p)) x =
      (R⁻¹ * R ^ k) • iteratedFDeriv ℝ k u (p + R • x) := by
  by_cases hR : R = 0
  · subst R
    simp
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [iteratedFDeriv_const_mul_nonzero _ (inv_ne_zero hR)]
  simp_rw [sub_eq_add_neg]
  rw [Nat.add_comm 1, TauCeti.iteratedFDeriv_succ_add_const]
  rw [TauCeti.iteratedFDeriv_comp_const_smul_apply (fun z ↦ u (p + z)) R x (j + 1),
    iteratedFDeriv_comp_add_left, smul_smul]

/-- Nonnegative graph dilations scale derivative norms by the corresponding factor. -/
theorem norm_iteratedFDeriv_dilatedHeight (u : E → ℝ) {r : ℝ} (hr : 0 ≤ r)
    (x : E) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun y ↦ r * u (r⁻¹ • y)) x‖ =
      (r * (r⁻¹) ^ k) * ‖iteratedFDeriv ℝ k u (r⁻¹ • x)‖ := by
  rw [iteratedFDeriv_dilatedHeight u r, norm_smul,
    Real.norm_of_nonneg (mul_nonneg hr (pow_nonneg (inv_nonneg.mpr hr) k))]

/-- Nonnegative graph normalizations scale positive-order derivative norms by the radius factor. -/
theorem norm_iteratedFDeriv_normalizedHeight (u : E → ℝ) (p : E) {R : ℝ} (hR : 0 ≤ R)
    (x : E) (k : ℕ) (hk : 1 ≤ k) :
    ‖iteratedFDeriv ℝ k (fun y ↦ R⁻¹ * (u (p + R • y) - u p)) x‖ =
      (R⁻¹ * R ^ k) * ‖iteratedFDeriv ℝ k u (p + R • x)‖ := by
  rw [iteratedFDeriv_normalizedHeight u p R x k hk, norm_smul,
    Real.norm_of_nonneg (mul_nonneg (inv_nonneg.mpr hR) (pow_nonneg hR k))]

end Jets

section Generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Dilation transports local differentiability through the actual rescaling map. -/
theorem contDiffOn_dilatedHeight {u : E → ℝ} {S T : Set E} {k : ℕ∞ω} {r : ℝ}
    (hu : ContDiffOn ℝ k u S) (hmap : MapsTo (fun x ↦ r⁻¹ • x) T S) :
    ContDiffOn ℝ k (fun x ↦ r * u (r⁻¹ • x)) T := by
  exact (hu.comp (contDiffOn_const.smul contDiffOn_id) hmap).const_smul r

/-- Centering and rescaling the height transports local differentiability. -/
theorem contDiffOn_normalizedHeight {u : E → ℝ} (p : E) (R : ℝ) {S T : Set E} {k : ℕ∞ω}
    (hu : ContDiffOn ℝ k u S) (hmap : MapsTo (fun x ↦ p + R • x) T S) :
    ContDiffOn ℝ k (fun x ↦ R⁻¹ * (u (p + R • x) - u p)) T := by
  exact ((hu.comp (contDiffOn_const.add (contDiffOn_const.smul contDiffOn_id)) hmap).sub
    contDiffOn_const).const_smul R⁻¹

private theorem mem_ball_normalizedHeight {p z : E} {R a : ℝ} (hR : 0 < R)
    (hz : z ∈ ball (0 : E) a) : p + R • z ∈ ball p (R * a) := by
  rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hR]
  exact mul_lt_mul_of_pos_left (by simpa only [mem_ball, dist_zero_right] using hz) hR

/-- A positive height normalization takes differentiability on a scaled ball to a fixed ball. -/
theorem contDiffOn_normalizedHeight_ball {u : E → ℝ} {p : E} {R a : ℝ} {k : ℕ∞ω}
    (hR : 0 < R) (hu : ContDiffOn ℝ k u (ball p (R * a))) :
    ContDiffOn ℝ k (fun x ↦ R⁻¹ * (u (p + R • x) - u p)) (ball (0 : E) a) := by
  exact contDiffOn_normalizedHeight p R hu (fun _ hx ↦ mem_ball_normalizedHeight hR hx)

end Generic

section Gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- The gradient is unchanged by simultaneous dilation of the horizontal and vertical axes. -/
theorem gradient_dilatedHeight (u : E → ℝ) {r : ℝ} (hr : r ≠ 0) (x : E) :
    ∇ (fun y ↦ r * u (r⁻¹ • y)) x = ∇ u (r⁻¹ • x) := by
  apply (toDual ℝ E).injective
  rw [toDual_gradient, toDual_gradient]
  ext e
  have h := congrArg (fun A : E [×1]→L[ℝ] ℝ ↦ A (fun _ ↦ e))
    (iteratedFDeriv_dilatedHeight u r x 1)
  simpa only [iteratedFDeriv_one_apply, smul_apply, pow_one,
    mul_inv_cancel₀ hr, one_smul] using h

/-- Centering and normalizing the height leaves the gradient at the corresponding point. -/
theorem gradient_normalizedHeight (u : E → ℝ) (p : E) {R : ℝ} (hR : R ≠ 0) (x : E) :
    ∇ (fun y ↦ R⁻¹ * (u (p + R • y) - u p)) x = ∇ u (p + R • x) := by
  apply (toDual ℝ E).injective
  rw [toDual_gradient, toDual_gradient]
  ext e
  have h := congrArg (fun A : E [×1]→L[ℝ] ℝ ↦ A (fun _ ↦ e))
    (iteratedFDeriv_normalizedHeight u p R x 1 le_rfl)
  simpa only [iteratedFDeriv_one_apply, smul_apply, pow_one,
    inv_mul_cancel₀ hR, one_smul] using h

end Gradient

section Operator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

private theorem nondivergenceOperator_eq_mul_of_gradient_of_iteratedFDeriv_two
    {u v : E → ℝ} {x y : E} {a : ℝ} (hgrad : ∇ v x = ∇ u y)
    (hsecond : iteratedFDeriv ℝ 2 v x = a • iteratedFDeriv ℝ 2 u y) :
    nondivergenceOperator v x = a * nondivergenceOperator u y := by
  have hlap : Δ v x = a * Δ u y := by
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis v
      (stdOrthonormalBasis ℝ E),
      InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis u
        (stdOrthonormalBasis ℝ E)]
    simp_rw [hsecond, smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
  have hH := congrArg (fun A : E [×2]→L[ℝ] ℝ ↦ A ![∇ u y, ∇ u y]) hsecond
  simp only [smul_apply, smul_eq_mul, iteratedFDeriv_two_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one] at hH
  rw [nondivergenceOperator_eq, nondivergenceOperator_eq, hgrad, hlap, hH]
  ring

/-- The native minimal graph operator scales inversely under simultaneous graph dilation. -/
theorem nondivergenceOperator_dilatedHeight (u : E → ℝ) (r : ℝ) (x : E) :
    nondivergenceOperator (fun y ↦ r * u (r⁻¹ • y)) x =
      r⁻¹ * nondivergenceOperator u (r⁻¹ • x) := by
  by_cases hr : r = 0
  · subst r
    simp [nondivergenceOperator_eq]
  apply nondivergenceOperator_eq_mul_of_gradient_of_iteratedFDeriv_two
    (gradient_dilatedHeight u hr x)
  convert iteratedFDeriv_dilatedHeight u r x 2 using 1
  congr 1
  field_simp

/-- The native minimal graph operator scales by the radius under height normalization. -/
theorem nondivergenceOperator_normalizedHeight (u : E → ℝ) (p : E) (R : ℝ) (x : E) :
    nondivergenceOperator (fun y ↦ R⁻¹ * (u (p + R • y) - u p)) x =
      R * nondivergenceOperator u (p + R • x) := by
  by_cases hR : R = 0
  · subst R
    simp [nondivergenceOperator_eq]
  apply nondivergenceOperator_eq_mul_of_gradient_of_iteratedFDeriv_two
    (gradient_normalizedHeight u p hR x)
  convert iteratedFDeriv_normalizedHeight u p R x 2 (by norm_num) using 1
  congr 1
  field_simp

end Operator

section Height

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- A gradient bound controls the centered normalized height by distance from the origin. -/
theorem abs_normalizedHeight_le_mul_norm {u : E → ℝ} {p z : E} {R a M : ℝ}
    (hR : 0 < R) (hu : DifferentiableOn ℝ u (ball p (R * a)))
    (hgrad : ∀ x ∈ ball p (R * a), ‖∇ u x‖ ≤ M) (hz : z ∈ ball (0 : E) a) :
    |R⁻¹ * (u (p + R • z) - u p)| ≤ M * ‖z‖ := by
  have ha : 0 < a := dist_nonneg.trans_lt (mem_ball.mp hz)
  have hp : p ∈ ball p (R * a) := mem_ball_self (mul_pos hR ha)
  have hbound := (convex_ball p (R * a)).norm_image_sub_le_of_norm_fderiv_le
    (fun x hx ↦ (hu x hx).differentiableAt (isOpen_ball.mem_nhds hx))
    (fun x hx ↦ by simpa only [← norm_gradient_eq_norm_fderiv] using hgrad x hx)
    hp (mem_ball_normalizedHeight hR hz)
  calc
    _ = R⁻¹ * ‖u (p + R • z) - u p‖ := by
      rw [abs_mul, abs_inv, abs_of_pos hR, Real.norm_eq_abs]
    _ ≤ R⁻¹ * (M * ‖p + R • z - p‖) :=
      mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hR.le)
    _ = _ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hR]
      field_simp

/-- On a fixed normalized ball, a gradient bound gives a uniform height bound. -/
theorem abs_normalizedHeight_le {u : E → ℝ} {p z : E} {R a M : ℝ}
    (hR : 0 < R) (hu : DifferentiableOn ℝ u (ball p (R * a)))
    (hgrad : ∀ x ∈ ball p (R * a), ‖∇ u x‖ ≤ M) (hz : z ∈ ball (0 : E) a) :
    |R⁻¹ * (u (p + R • z) - u p)| ≤ M * a := by
  have ha : 0 < a := dist_nonneg.trans_lt (mem_ball.mp hz)
  have hM : 0 ≤ M := (norm_nonneg _).trans (hgrad p (mem_ball_self (mul_pos hR ha)))
  exact (abs_normalizedHeight_le_mul_norm hR hu hgrad hz).trans
    (mul_le_mul_of_nonneg_left
      (by simpa only [dist_zero_right] using (mem_ball.mp hz).le) hM)

end Height

end TauCeti.MinimalGraph
