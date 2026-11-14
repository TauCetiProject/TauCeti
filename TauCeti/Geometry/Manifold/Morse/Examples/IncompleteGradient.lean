/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.RateRescale
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.NormedSpace
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-!
# A proper function bounded below whose negative gradient flow is incomplete

The function `f(x) = x² + x⁴` on `ℝ` is proper and bounded below, and the standard metric on `ℝ`
is complete. Nevertheless the trajectories of `-grad f = -(2x + 4x³)`
(`TauCeti.mgradient_sq_add_pow_four`) escape to infinity in finite backward time: the backward
equation `x' = 2x + 4x³` grows like `x' = 4x³`, whose solutions blow up. Quantitatively, along a
trajectory `γ` with `γ 0 = x₀ ≠ 0`, the value of `f` grows backward in time, so `γ` never meets `0`,
and `u = γ⁻²` satisfies `u' = 4u + 8 ≥ 8`. So `u (-(8 x₀²)⁻¹) ≤ u 0 - 1 / x₀² = 0`, which is
impossible: the trajectory cannot be defined on `[-(8 x₀²)⁻¹, 0]`
(`TauCeti.not_isMIntegralCurveOn_Icc_neg_mgradient_sq_add_pow_four`). In particular `-grad f` is
not complete (`TauCeti.not_isCompleteVectorField_neg_mgradient_sq_add_pow_four`).

So properness, a lower bound and a complete metric do not make a negative gradient flow complete.
Rescaling the field to bounded rate along `f` does: `TauCeti.rateRescale` turns `-grad f` into the
complete field `-(2x + 4x³) / (1 + (2x + 4x³)⁴)` with the same zeros and the same trajectories up to
a change of time (`TauCeti.isCompleteVectorField_rateRescale_neg_mgradient_sq_add_pow_four`).

## Main results

* `TauCeti.mgradient_sq_add_pow_four`: for the standard metric, `grad f = 2x + 4x³`.
* `TauCeti.isProperMap_sq_add_pow_four`: `f` is proper.
* `TauCeti.not_isMIntegralCurveOn_Icc_neg_mgradient_sq_add_pow_four`: no trajectory of
  `-grad f` through `x₀ ≠ 0` at time `0` is defined on `[-(8 x₀²)⁻¹, 0]`.
* `TauCeti.not_isCompleteVectorField_neg_mgradient_sq_add_pow_four`: `-grad f` is not complete.
* `TauCeti.isCompleteVectorField_rateRescale_neg_mgradient_sq_add_pow_four`: its rescaling to
  bounded rate along `f` is complete.
-/

public section

open Filter Set TauCeti.Manifold
open scoped Manifold Topology

namespace TauCeti

/-- For the standard metric on `ℝ`, the gradient of `f(x) = x² + x⁴` is `2x + 4x³`. -/
@[simp]
theorem mgradient_sq_add_pow_four (x : ℝ) :
    mgradient 𝓘(ℝ, ℝ) (fun x : ℝ ↦ x ^ 2 + x ^ 4) x = (2 * x + 4 * x ^ 3 : ℝ) := by
  rw [mgradient_eq_gradient_of_eq rfl, gradient_eq_deriv']
  exact ((hasDerivAt_pow 2 x).add (hasDerivAt_pow 4 x)).deriv.trans (by ring)

/-- The function `f(x) = x² + x⁴` on `ℝ` is proper. -/
theorem isProperMap_sq_add_pow_four : IsProperMap fun x : ℝ ↦ x ^ 2 + x ^ 4 := by
  refine isProperMap_iff_tendsto_cocompact.2 ⟨by fun_prop, ?_⟩
  have hsq : Tendsto (fun x : ℝ ↦ ‖x‖ * ‖x‖) (cocompact ℝ) atTop :=
    tendsto_norm_cocompact_atTop.atTop_mul_atTop₀ tendsto_norm_cocompact_atTop
  refine (tendsto_atTop_mono (fun x ↦ ?_) hsq).mono_right
    (cocompact_eq_atBot_atTop (α := ℝ) ▸ le_sup_right)
  rw [Real.norm_eq_abs, ← sq, sq_abs]
  exact le_add_of_nonneg_right (by positivity)

/-- The negative gradient of `f(x) = x² + x⁴` for the standard metric, read in `ℝ`. -/
private theorem neg_mgradient_sq_add_pow_four_apply (x : ℝ) :
    (-mgradient 𝓘(ℝ, ℝ) (fun x : ℝ ↦ x ^ 2 + x ^ 4)) x = (-(2 * x + 4 * x ^ 3) : ℝ) := by
  rw [Pi.neg_apply, mgradient_sq_add_pow_four]
  -- Both sides are the same real number, read in `ℝ` and in its tangent space.
  rfl

/-- **Backward escape in finite time.** For the standard metric, a trajectory of `-grad f`,
`f(x) = x² + x⁴`, through `x₀ ≠ 0` at time `0` is not defined on `[-(8 x₀²)⁻¹, 0]`. -/
theorem not_isMIntegralCurveOn_Icc_neg_mgradient_sq_add_pow_four {x₀ : ℝ} (hx₀ : x₀ ≠ 0)
    {γ : ℝ → ℝ} (hγ0 : γ 0 = x₀) :
    ¬ IsMIntegralCurveOn γ (-mgradient 𝓘(ℝ, ℝ) (fun x : ℝ ↦ x ^ 2 + x ^ 4))
      (Icc (-(8 * x₀ ^ 2)⁻¹) 0) := by
  intro hγ
  set a := (8 * x₀ ^ 2)⁻¹
  have ha : 0 < a := by positivity
  rw [isMIntegralCurveOn_iff_isIntegralCurveOn] at hγ
  have hd (t : ℝ) (ht : t ∈ Icc (-a) 0) :
      HasDerivWithinAt γ (-(2 * γ t + 4 * γ t ^ 3)) (Icc (-a) 0) t :=
    (hγ t ht).congr_deriv (neg_mgradient_sq_add_pow_four_apply _)
  have hcont : ContinuousOn γ (Icc (-a) 0) := fun t ht ↦ (hd t ht).continuousWithinAt
  have hint : interior (Icc (-a) 0) = Ioo (-a) 0 := interior_Icc
  -- `f` does not decrease backward in time, since `f ∘ γ` has derivative `-(2γ + 4γ³)² ≤ 0`.
  have hanti : AntitoneOn (fun t ↦ γ t ^ 2 + γ t ^ 4) (Icc (-a) 0) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _) (by fun_prop)
      (f' := fun t ↦ -(2 * γ t + 4 * γ t ^ 3) ^ 2) (fun t ht ↦ ?_) fun t _ ↦ by
        simp only [Left.neg_nonpos_iff]; positivity
    rw [hint] at ht ⊢
    have hγt := ((hd t (Ioo_subset_Icc_self ht)).mono Ioo_subset_Icc_self)
    exact ((hγt.pow 2).add (hγt.pow 4)).congr_deriv (by push_cast; ring)
  -- So `γ` never meets `0` there, as `f (γ t) ≥ f x₀ > 0 = f 0`.
  have hne (t : ℝ) (ht : t ∈ Icc (-a) 0) : γ t ≠ 0 := by
    intro h0
    have := hanti ht ⟨neg_nonpos.2 ha.le, le_rfl⟩ ht.2
    simp only [h0, hγ0] at this
    have : 0 < x₀ ^ 2 + x₀ ^ 4 := by positivity
    norm_num at *
    linarith
  -- And `u = γ⁻²` satisfies `u' = 4u + 8 ≥ 8`, so `u - 8t` is monotone.
  have hmono : MonotoneOn (fun t ↦ (γ t ^ 2)⁻¹ - 8 * t) (Icc (-a) 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      ((hcont.pow 2).inv₀ (fun t ht ↦ pow_ne_zero 2 (hne t ht)) |>.sub (by fun_prop))
      (f' := fun t ↦ 4 * (γ t ^ 2)⁻¹) (fun t ht ↦ ?_) fun t _ ↦ by positivity
    rw [hint] at ht ⊢
    have hγt := ((hd t (Ioo_subset_Icc_self ht)).mono Ioo_subset_Icc_self)
    have hγne := hne t (Ioo_subset_Icc_self ht)
    refine (((hγt.pow 2).inv (pow_ne_zero 2 hγne)).sub
      ((hasDerivWithinAt_id t _).const_mul 8)).congr_deriv ?_
    simp only [Pi.pow_apply]
    field_simp
    ring
  have h := hmono ⟨le_rfl, neg_nonpos.2 ha.le⟩ ⟨neg_nonpos.2 ha.le, le_rfl⟩
    (neg_nonpos.2 ha.le)
  have hpos : 0 < (γ (-a) ^ 2)⁻¹ := by
    have := hne _ ⟨le_rfl, neg_nonpos.2 ha.le⟩
    positivity
  simp only [hγ0, mul_zero, sub_zero, a] at h
  have : 8 * (8 * x₀ ^ 2)⁻¹ = (x₀ ^ 2)⁻¹ := by field_simp
  linarith

/-- **The negative gradient of `x² + x⁴` is not complete** for the standard metric on `ℝ`, although
the function is proper and bounded below and the metric is complete. -/
theorem not_isCompleteVectorField_neg_mgradient_sq_add_pow_four :
    ¬ IsCompleteVectorField (-mgradient 𝓘(ℝ, ℝ) (fun x : ℝ ↦ x ^ 2 + x ^ 4)) := by
  intro hc
  have hv : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ).tangent 1 fun x : ℝ ↦
      (⟨x, (-mgradient 𝓘(ℝ, ℝ) (fun x : ℝ ↦ x ^ 2 + x ^ 4)) x⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ) := by
    simp_rw [neg_mgradient_sq_add_pow_four_apply]
    exact contMDiff_vectorSpace_iff_contDiff.2 (by fun_prop)
  obtain ⟨γ, hγ0, hγ⟩ := hc.exists_isMIntegralCurve hv 1
  exact not_isMIntegralCurveOn_Icc_neg_mgradient_sq_add_pow_four one_ne_zero hγ0
    (hγ.isMIntegralCurveOn _)

/-- **Rescaling to bounded rate makes the negative gradient of `x² + x⁴` complete.** The field
`TauCeti.rateRescale 𝓘(ℝ, ℝ) f (-grad f)` has the zeros and, up to a change of time, the
trajectories of `-grad f`, and it is complete because `f` is proper. -/
theorem isCompleteVectorField_rateRescale_neg_mgradient_sq_add_pow_four :
    IsCompleteVectorField (rateRescale 𝓘(ℝ, ℝ) (fun x : ℝ ↦ x ^ 2 + x ^ 4)
      (-mgradient 𝓘(ℝ, ℝ) (fun x : ℝ ↦ x ^ 2 + x ^ 4))) := by
  refine isCompleteVectorField_rateRescale isProperMap_sq_add_pow_four
    (contMDiff_iff_contDiff.2 (by fun_prop)) ?_
  simp_rw [neg_mgradient_sq_add_pow_four_apply]
  exact contMDiff_vectorSpace_iff_contDiff.2 (by fun_prop)

end TauCeti
