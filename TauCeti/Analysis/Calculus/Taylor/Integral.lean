/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.TaylorIntegral

/-!
# Second derivatives along a line and multivariate Taylor remainders

Mathlib's `DifferentiableAt.deriv_comp_add_smul` computes the derivative of the restriction
`s ↦ f (x + s • y)` of a function to a line, and `map_add_eq_sum_add_integral_iteratedFDeriv`
expresses the multivariate Taylor remainder in integral form when the target space is complete.
This file records the second derivative along a line together with continuity of the degree-`m`
Taylor sum in its center point and the integral remainder reparametrized from the evaluation point
towards the center.

## Main results

* `DifferentiableAt.hasDerivAt_deriv_comp_add_smul`: if `f` is differentiable near `x + t • y`
  and `fderiv 𝕜 f` is differentiable at `x + t • y`, then the derivative of
  `s ↦ f (x + s • y)` has derivative `fderiv 𝕜 (fderiv 𝕜 f) (x + t • y) y y` at `t`.
* `ContDiffAt.deriv_deriv_comp_add_smul`: the second derivative of `s ↦ f (x + s • y)` at `t` is
  `fderiv 𝕜 (fderiv 𝕜 f) (x + t • y) y y`, for `f` of class `C²` at `x + t • y`.
* `TauCeti.continuousOn_sum_iteratedFDeriv`: continuity of the degree-`m` Taylor sum in the center
  point on an open set.
* `TauCeti.sub_sum_iteratedFDeriv_eq_setIntegral_iteratedFDeriv`: Taylor's integral remainder
  parametrized from `x` towards `y` over `s ∈ (0, 1)`.
-/

public section

open Topology

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {f : E → F} {x y : E} {t : 𝕜}

/-- If `f` is differentiable near `x + t • y` and `fderiv 𝕜 f` is differentiable at
`x + t • y`, then the derivative of the restriction `s ↦ f (x + s • y)` of `f` to a line has
derivative the diagonal Hessian entry `fderiv 𝕜 (fderiv 𝕜 f) (x + t • y) y y` at `t`. -/
theorem DifferentiableAt.hasDerivAt_deriv_comp_add_smul
    (hf' : DifferentiableAt 𝕜 (fderiv 𝕜 f) (x + t • y))
    (hf : ∀ᶠ z in 𝓝 (x + t • y), DifferentiableAt 𝕜 f z) :
    HasDerivAt (deriv fun s : 𝕜 => f (x + s • y)) (fderiv 𝕜 (fderiv 𝕜 f) (x + t • y) y y) t := by
  have hline : HasDerivAt (fun s : 𝕜 => x + s • y) y t := by
    simpa using ((hasDerivAt_id t).smul_const y).const_add x
  have hev : (fun s => fderiv 𝕜 f (x + s • y) y) =ᶠ[𝓝 t] deriv fun s : 𝕜 => f (x + s • y) := by
    filter_upwards [hline.continuousAt.tendsto.eventually hf] with s hs
    exact hs.deriv_comp_add_smul.symm
  simpa using ((hf'.hasFDerivAt.comp_hasDerivAt t hline).clm_apply
    (hasDerivAt_const t y)).congr_of_eventuallyEq hev.symm

/-- The second derivative of the restriction `s ↦ f (x + s • y)` of a `C²` function to a line is
the diagonal Hessian entry `fderiv 𝕜 (fderiv 𝕜 f) (x + t • y) y y`. -/
theorem ContDiffAt.deriv_deriv_comp_add_smul (hf : ContDiffAt 𝕜 2 f (x + t • y)) :
    deriv (deriv fun s : 𝕜 => f (x + s • y)) t = fderiv 𝕜 (fderiv 𝕜 f) (x + t • y) y y :=
  ((hf.fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero).hasDerivAt_deriv_comp_add_smul
    (hf.eventually (by simp) |>.mono fun _ hz => hz.differentiableAt two_ne_zero) |>.deriv

namespace TauCeti

open MeasureTheory Set
open scoped Nat

section SegmentRemainder

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- For a `C^m` map `f : E → F` on an open set `Ω` and a fixed point `x : E`, the degree-`m` Taylor
sum `y ↦ ∑ j ∈ range (m + 1), (j !)⁻¹ • D^j f(y)(x - y, …, x - y)` is continuous on `Ω`. -/
theorem continuousOn_sum_iteratedFDeriv {Ω : Set E} (hΩ : IsOpen Ω) {f : E → F} {m : ℕ}
    (hf : ContDiffOn ℝ m f Ω) (x : E) :
    ContinuousOn (fun y ↦ ∑ j ∈ Finset.range (m + 1),
      (j ! : ℝ)⁻¹ • iteratedFDeriv ℝ j f y (fun _ ↦ x - y)) Ω := by
  induction m with
  | zero =>
    simp_rw [zero_add, Finset.sum_range_one, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul,
      iteratedFDeriv_zero_apply]
    exact hf.continuousOn
  | succ m ih =>
    simp_rw [Finset.sum_range_succ _ (m + 1)]
    refine (ih (hf.of_le (by simp))).add (continuousOn_const.smul ?_)
    exact continuous_eval.comp_continuousOn
      ((ContinuousOn.continuousOn_iteratedFDeriv (k := m + 1) hf hΩ (by simp)).prodMk
        (continuous_pi fun _ ↦ continuous_const.sub continuous_id).continuousOn)

/-- **Taylor's integral remainder parametrized from the evaluation point.** If `f` is `C^{m+1}` at
every point of the segment `s ↦ x + s • (y - x)` (`s ∈ [0, 1]`), then the remainder of `f x` modulo
its degree-`m` Taylor sum at `y` equals `(m !)⁻¹` times the integral over `s ∈ (0, 1)` of
`s ^ m • D^{m+1} f (x + s • (y - x)) (x - y, …, x - y)`. -/
theorem sub_sum_iteratedFDeriv_eq_setIntegral_iteratedFDeriv (f : E → F) (m : ℕ) (x y : E)
    (hf : ∀ s ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ (m + 1) f (x + s • (y - x))) :
    f x - ∑ j ∈ Finset.range (m + 1),
        (j ! : ℝ)⁻¹ • iteratedFDeriv ℝ j f y (fun _ ↦ x - y) =
      (m ! : ℝ)⁻¹ • ∫ s in Ioo (0 : ℝ) 1,
        s ^ m • iteratedFDeriv ℝ (m + 1) f (x + s • (y - x)) (fun _ ↦ x - y) := by
  have hseg : ∀ t : ℝ, y + t • (x - y) = x + (1 - t) • (y - x) := fun t ↦ by
    rw [sub_smul, one_smul]
    abel_nf
    module
  have hft : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ (m + 1) f (y + t • (x - y)) := fun t ht ↦ by
    rw [hseg t]
    exact hf (1 - t) ⟨sub_nonneg.2 ht.2, sub_le_self _ ht.1⟩
  have htaylor := map_add_eq_sum_add_integral_iteratedFDeriv (n := m) hft
  rw [add_sub_cancel, ← sub_eq_iff_eq_add'] at htaylor
  rw [htaylor]
  congr 1
  set g : ℝ → F := fun s ↦ s ^ m • iteratedFDeriv ℝ (m + 1) f (x + s • (y - x)) (fun _ ↦ x - y)
  have hflip : (∫ t in (0 : ℝ)..1,
      (1 - t) ^ m • iteratedFDeriv ℝ (m + 1) f (y + t • (x - y)) (fun _ ↦ x - y)) =
        ∫ t in (0 : ℝ)..1, g (1 - t) :=
    intervalIntegral.integral_congr fun t _ ↦ by simp only [g, hseg t]
  rw [hflip, intervalIntegral.integral_comp_sub_left g 1, sub_self, sub_zero,
    intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]

end SegmentRemainder

end TauCeti
