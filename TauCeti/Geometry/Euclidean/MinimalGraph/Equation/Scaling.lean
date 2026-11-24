/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Otis Chodosh, The Tau Ceti contributors
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
public import Mathlib.Analysis.Calculus.MeanValue
import TauCeti.Analysis.Normed.Module.Ball

/-!
# Scaling and normalization of Euclidean minimal graphs

Simultaneously dilating the horizontal and vertical coordinates leaves the gradient unchanged
at the corresponding point and multiplies the nondivergence minimal graph operator by the reciprocal
scale. Centering at a point and dividing the height by the radius gives the inverse normalization:
the gradient is unchanged and the nondivergence operator is multiplied by the radius.

All finite derivative and nondivergence operator identities hold without regularity assumptions,
including at scale zero. Gradient identities require nonzero scales. Height centering disappears
only at positive derivative orders. Nonnegative scales give exact derivative norm identities.
Positive scales transport differentiability between the corresponding balls. A gradient bound
on the original ball controls the normalized height by the mean value inequality.

Adapted from Otis Chodosh's formalization in
`ForTauCeti/Geometry/Euclidean/MinimalGraph/Equation/Scaling.lean` in
[ColdingMinicozziTheory](https://github.com/riccardobrasca/ColdingMinicozziTheory/blob/2490d830cfd5db58e1477b549840931baef25a88/ForTauCeti/Geometry/Euclidean/MinimalGraph/Equation/Scaling.lean)
(commit `2490d830cfd5db58e1477b549840931baef25a88`).

## Main declarations

* `TauCeti.MinimalGraph.iteratedFDeriv_dilatedHeight`: the exact finite-order dilation factor.
* `TauCeti.MinimalGraph.iteratedFDeriv_normalizedHeight`: positive-order normalization factors.
* `TauCeti.MinimalGraph.nondivergenceOperator_normalizedHeight`: equation scaling.
* `TauCeti.MinimalGraph.contDiffOn_normalizedHeight_ball`: regularity on a fixed normalized ball.
* `TauCeti.MinimalGraph.abs_normalizedHeight_le`: a height bound from the gradient bound.
-/

public noncomputable section

open InnerProductSpace Metric Set
open scoped ContDiff Gradient Laplacian

namespace TauCeti.MinimalGraph

section Heights

variable {E : Type*} [SMul ℝ E]

/-- The height of a graph after dilating both horizontal and vertical coordinates by `r`. -/
def dilatedHeight (u : E → ℝ) (r : ℝ) : E → ℝ :=
  fun y ↦ r * u (r⁻¹ • y)

/-- Evaluate the height of a simultaneously dilated graph. -/
@[simp]
theorem dilatedHeight_apply (u : E → ℝ) (r : ℝ) (y : E) :
    dilatedHeight u r y = r * u (r⁻¹ • y) := (rfl)

end Heights

section CenteredHeight

variable {E : Type*} [Add E] [SMul ℝ E]

/-- The height centered at `p` and normalized by the spatial and vertical scale `R`. -/
def normalizedHeight (u : E → ℝ) (p : E) (R : ℝ) : E → ℝ :=
  fun y ↦ R⁻¹ * (u (p + R • y) - u p)

/-- Evaluate the centered and normalized height. -/
@[simp]
theorem normalizedHeight_apply (u : E → ℝ) (p : E) (R : ℝ) (y : E) :
    normalizedHeight u p R y = R⁻¹ * (u (p + R • y) - u p) := (rfl)

end CenteredHeight

section Jets

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Dilating a graph by `r` multiplies its `k`-th iterated derivative by `r * (r⁻¹) ^ k`,
evaluated at the corresponding point. -/
theorem iteratedFDeriv_dilatedHeight (u : E → ℝ) (r : ℝ)
    (x : E) (k : ℕ) :
    iteratedFDeriv ℝ k (dilatedHeight u r) x =
      (r * (r⁻¹) ^ k) • iteratedFDeriv ℝ k u (r⁻¹ • x) := by
  conv_lhs => simp only [funext (dilatedHeight_apply u r), ← smul_eq_mul]
  rw [TauCeti.iteratedFDeriv_fun_const_smul_apply,
    TauCeti.iteratedFDeriv_comp_const_smul_apply, smul_smul]

/-- Normalizing a graph multiplies its `k`-th iterated derivative by `R⁻¹ * R ^ k` for `1 ≤ k`,
evaluated at the corresponding point. -/
theorem iteratedFDeriv_normalizedHeight (u : E → ℝ) (p : E) (R : ℝ)
    (x : E) (k : ℕ) (hk : 1 ≤ k) :
    iteratedFDeriv ℝ k (normalizedHeight u p R) x =
      (R⁻¹ * R ^ k) • iteratedFDeriv ℝ k u (p + R • x) := by
  conv_lhs => simp only [funext (normalizedHeight_apply u p R), ← smul_eq_mul]
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [TauCeti.iteratedFDeriv_fun_const_smul_apply]
  simp_rw [sub_eq_add_neg]
  rw [Nat.add_comm 1, TauCeti.iteratedFDeriv_succ_add_const]
  rw [TauCeti.iteratedFDeriv_comp_const_smul_apply (fun z ↦ u (p + z)) R x (j + 1),
    iteratedFDeriv_comp_add_left, smul_smul]

/-- Nonnegative graph dilations scale derivative norms by the corresponding factor. -/
theorem norm_iteratedFDeriv_dilatedHeight (u : E → ℝ) {r : ℝ} (hr : 0 ≤ r)
    (x : E) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (dilatedHeight u r) x‖ =
      (r * (r⁻¹) ^ k) * ‖iteratedFDeriv ℝ k u (r⁻¹ • x)‖ := by
  rw [iteratedFDeriv_dilatedHeight u r, norm_smul,
    Real.norm_of_nonneg (mul_nonneg hr (pow_nonneg (inv_nonneg.mpr hr) k))]

/-- Nonnegative graph normalizations scale positive-order derivative norms by the radius factor. -/
theorem norm_iteratedFDeriv_normalizedHeight (u : E → ℝ) (p : E) {R : ℝ} (hR : 0 ≤ R)
    (x : E) (k : ℕ) (hk : 1 ≤ k) :
    ‖iteratedFDeriv ℝ k (normalizedHeight u p R) x‖ =
      (R⁻¹ * R ^ k) * ‖iteratedFDeriv ℝ k u (p + R • x)‖ := by
  rw [iteratedFDeriv_normalizedHeight u p R x k hk, norm_smul,
    Real.norm_of_nonneg (mul_nonneg (inv_nonneg.mpr hR) (pow_nonneg hR k))]

end Jets

section Generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Dilation transports local differentiability through the actual rescaling map. -/
theorem contDiffOn_dilatedHeight {u : E → ℝ} {S T : Set E} {k : ℕ∞ω} {r : ℝ}
    (hu : ContDiffOn ℝ k u S) (hmap : MapsTo (fun x ↦ r⁻¹ • x) T S) :
    ContDiffOn ℝ k (dilatedHeight u r) T := by
  exact (hu.comp (contDiffOn_const.smul contDiffOn_id) hmap).const_smul r

/-- Centering and rescaling the height transports local differentiability. -/
theorem contDiffOn_normalizedHeight {u : E → ℝ} (p : E) (R : ℝ) {S T : Set E} {k : ℕ∞ω}
    (hu : ContDiffOn ℝ k u S) (hmap : MapsTo (fun x ↦ p + R • x) T S) :
    ContDiffOn ℝ k (normalizedHeight u p R) T := by
  exact ((hu.comp (contDiffOn_const.add (contDiffOn_const.smul contDiffOn_id)) hmap).sub
    contDiffOn_const).const_smul R⁻¹

/-- A positive height normalization takes differentiability on a scaled ball to a fixed ball. -/
theorem contDiffOn_normalizedHeight_ball {u : E → ℝ} {p : E} {R a : ℝ} {k : ℕ∞ω}
    (hR : 0 < R) (hu : ContDiffOn ℝ k u (ball p (R * a))) :
    ContDiffOn ℝ k (normalizedHeight u p R) (ball (0 : E) a) := by
  apply contDiffOn_normalizedHeight p R hu
  intro z hz
  simpa only [mem_preimage, vadd_eq_add, Real.norm_of_nonneg hR.le, add_comm] using
    (preimage_smul_vadd_ball_norm p (c := R) (norm_pos_iff.mpr hR.ne') a).symm.subset hz

end Generic

section Gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- For `r ≠ 0`, the gradient is unchanged by simultaneous dilation of both axes. -/
theorem gradient_dilatedHeight (u : E → ℝ) {r : ℝ} (hr : r ≠ 0) (x : E) :
    ∇ (dilatedHeight u r) x = ∇ u (r⁻¹ • x) := by
  apply gradient_eq_of_iteratedFDeriv_one
  simpa only [pow_one, mul_inv_cancel₀ hr, one_smul] using
    iteratedFDeriv_dilatedHeight u r x 1

/-- For `R ≠ 0`, centering and normalizing the height leaves the gradient unchanged at the
corresponding point. -/
theorem gradient_normalizedHeight (u : E → ℝ) (p : E) {R : ℝ} (hR : R ≠ 0) (x : E) :
    ∇ (normalizedHeight u p R) x = ∇ u (p + R • x) := by
  apply gradient_eq_of_iteratedFDeriv_one
  simpa only [pow_one, inv_mul_cancel₀ hR, one_smul] using
    iteratedFDeriv_normalizedHeight u p R x 1 le_rfl

end Gradient

section Operator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The nondivergence minimal graph operator scales inversely under simultaneous graph dilation. -/
theorem nondivergenceOperator_dilatedHeight (u : E → ℝ) (r : ℝ) (x : E) :
    nondivergenceOperator (dilatedHeight u r) x =
      r⁻¹ * nondivergenceOperator u (r⁻¹ • x) := by
  by_cases hr : r = 0
  · subst r
    unfold dilatedHeight
    simp [nondivergenceOperator_eq]
  apply nondivergenceOperator_eq_mul_of_gradient_of_iteratedFDeriv_two
    (gradient_dilatedHeight u hr x)
  convert iteratedFDeriv_dilatedHeight u r x 2 using 1
  congr 1
  field_simp

/-- The nondivergence minimal graph operator scales by the radius under height normalization. -/
theorem nondivergenceOperator_normalizedHeight (u : E → ℝ) (p : E) (R : ℝ) (x : E) :
    nondivergenceOperator (normalizedHeight u p R) x =
      R * nondivergenceOperator u (p + R • x) := by
  by_cases hR : R = 0
  · subst R
    unfold normalizedHeight
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
    |normalizedHeight u p R z| ≤ M * ‖z‖ := by
  have ha : 0 < a := dist_nonneg.trans_lt (mem_ball.mp hz)
  have hp : p ∈ ball p (R * a) := mem_ball_self (mul_pos hR ha)
  have hbound := (convex_ball p (R * a)).norm_image_sub_le_of_norm_fderiv_le
    (fun x hx ↦ (hu x hx).differentiableAt (isOpen_ball.mem_nhds hx))
    (fun x hx ↦ by simpa only [← norm_gradient_eq_norm_fderiv] using hgrad x hx)
    hp (by
      simpa only [mem_preimage, vadd_eq_add, Real.norm_of_nonneg hR.le, add_comm] using
        (preimage_smul_vadd_ball_norm p (c := R) (norm_pos_iff.mpr hR.ne') a).symm.subset hz)
  calc
    _ = R⁻¹ * ‖u (p + R • z) - u p‖ := by
      rw [normalizedHeight_apply, abs_mul, abs_inv, abs_of_pos hR, Real.norm_eq_abs]
    _ ≤ R⁻¹ * (M * ‖p + R • z - p‖) :=
      mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hR.le)
    _ = _ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hR]
      field_simp

/-- On a fixed normalized ball, a gradient bound gives a uniform height bound. -/
theorem abs_normalizedHeight_le {u : E → ℝ} {p z : E} {R a M : ℝ}
    (hR : 0 < R) (hu : DifferentiableOn ℝ u (ball p (R * a)))
    (hgrad : ∀ x ∈ ball p (R * a), ‖∇ u x‖ ≤ M) (hz : z ∈ ball (0 : E) a) :
    |normalizedHeight u p R z| ≤ M * a := by
  have ha : 0 < a := dist_nonneg.trans_lt (mem_ball.mp hz)
  have hM : 0 ≤ M := (norm_nonneg _).trans (hgrad p (mem_ball_self (mul_pos hR ha)))
  exact (abs_normalizedHeight_le_mul_norm hR hu hgrad hz).trans
    (mul_le_mul_of_nonneg_left
      (by simpa only [dist_zero_right] using (mem_ball.mp hz).le) hM)

end Height

end TauCeti.MinimalGraph
