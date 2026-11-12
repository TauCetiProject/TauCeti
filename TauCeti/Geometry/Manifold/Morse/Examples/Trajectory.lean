/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Trajectory
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.NormedSpace
import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# Convergence of gradient trajectories: two negative controls

A forward trajectory of `-grad f`, for a Morse function `f` and a `C¹` Riemannian metric, which
stays in a compact set converges to a critical point in that set
(`TauCeti.IsMorse.exists_tendsto_of_isMIntegralCurveOn_neg_mgradient`), and the limit of any
convergent forward trajectory is a critical point
(`IsMIntegralCurveOn.mem_criticalPoints_of_tendsto_neg_mgradient`). This file shows on the
function `f(x) = x` on `ℝ`, which has no critical points, that neither the compact trap nor the
regularity of the metric can be dropped from these statements.

* **The compact trap cannot be dropped.** The function `f(x) = x` is a Morse function
  (`TauCeti.isMorse_id_real`), vacuously, since it has no critical points
  (`TauCeti.criticalPoints_id_real`). For the standard metric, `grad f = 1`
  (`TauCeti.mgradient_id_real`), so `t ↦ x₀ - t` is a trajectory of `-grad f`
  (`TauCeti.isMIntegralCurve_sub_neg_mgradient_id`), and every forward trajectory has this form.
  No forward trajectory stays in a compact set
  (`TauCeti.not_mapsTo_of_isMIntegralCurveOn_neg_mgradient_id`), and none converges
  (`TauCeti.not_tendsto_of_isMIntegralCurveOn_neg_mgradient_id`).
* **The regularity of the metric cannot be dropped.** Give the tangent spaces of `ℝ` the inner
  products `λ(x) v w`, where `λ(x) = x⁻²` for `x ≠ 0` and `λ(0) = 1`
  (`TauCeti.singularLineMetric`). Each tangent space carries an inner product, but `λ` is
  discontinuous at `0`, so this metric is not even continuous
  (`TauCeti.not_isContMDiffRiemannianBundle_singularLineMetric`). For this metric
  `grad f = λ⁻¹`, which is `x²` off `0` and `1` at `0`
  (`TauCeti.mgradient_id_singularLineMetric`). The trajectory of `-grad f` from `x₀ > 0` is
  `t ↦ x₀ / (1 + x₀ t)` (`TauCeti.isMIntegralCurveOn_neg_mgradient_id_singularLineMetric`). For
  `x₀ = 1` it stays in the compact interval `[0, 1]` and converges to `0`, which is not a critical
  point of `f` (`TauCeti.exists_isMIntegralCurveOn_neg_mgradient_id_singularLineMetric`).

Neither example uses compactness of the manifold `ℝ`: the theorems recalled above replace it by
the compact set containing the trajectory.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Proposition 2.1.6 and Chapter 2.
-/

public section

open Bundle Filter Set Topology TauCeti.Manifold
open scoped ContDiff Manifold

namespace TauCeti

/-! ### The function `f(x) = x` and the standard metric -/

section Untrapped

/-- **The function `f(x) = x` on `ℝ` has no critical points.** -/
theorem criticalPoints_id_real : criticalPoints 𝓘(ℝ, ℝ) (id : ℝ → ℝ) = ∅ := by
  ext x
  simp only [mem_criticalPoints_iff_fderiv_eq_zero, fderiv_id, mem_empty_iff_false, iff_false]
  intro h
  simpa using congrArg (fun L : ℝ →L[ℝ] ℝ ↦ L 1) h

/-- **The function `f(x) = x` on `ℝ` is a Morse function**, vacuously: it has no critical
points. -/
theorem isMorse_id_real : IsMorse 𝓘(ℝ, ℝ) (id : ℝ → ℝ) :=
  isMorseOn_univ.1 (isMorseOn_iff_criticalPoints.2
    ⟨contMDiff_id.contMDiffOn, fun x _ hx ↦ by simp [criticalPoints_id_real] at hx⟩)

/-- For the standard metric on `ℝ`, the gradient of `f(x) = x` is `1`. -/
@[simp]
theorem mgradient_id_real (x : ℝ) : mgradient 𝓘(ℝ, ℝ) (id : ℝ → ℝ) x = (1 : ℝ) := by
  rw [mgradient_eq_gradient_of_eq rfl, gradient_eq_deriv', deriv_id]

/-- For the standard metric on `ℝ`, the negative gradient of `f(x) = x` is `-1`. -/
private theorem neg_mgradient_id_real_apply (x : ℝ) :
    (-mgradient 𝓘(ℝ, ℝ) (id : ℝ → ℝ)) x = (-1 : ℝ) := by
  rw [Pi.neg_apply, mgradient_id_real]
  -- Both sides are the real number `-1`, read in `ℝ` and in its tangent space.
  rfl

/-- For the standard metric on `ℝ`, the curve `t ↦ x₀ - t` is a trajectory of `-grad f`, for
`f(x) = x`. -/
theorem isMIntegralCurve_sub_neg_mgradient_id (x₀ : ℝ) :
    IsMIntegralCurve (fun t : ℝ ↦ x₀ - t) (-mgradient 𝓘(ℝ, ℝ) (id : ℝ → ℝ)) := by
  rw [isMIntegralCurve_iff_isMIntegralCurveOn, isMIntegralCurveOn_iff_isIntegralCurveOn]
  intro t _
  exact ((hasDerivAt_id t).const_sub x₀).hasDerivWithinAt.congr_deriv
    (neg_mgradient_id_real_apply _).symm

variable {γ : ℝ → ℝ}

/-- A forward trajectory of `-grad f`, for `f(x) = x` and the standard metric, moves at unit
speed to the left. -/
private theorem eqOn_sub_of_isMIntegralCurveOn_neg_mgradient_id
    (hγ : IsMIntegralCurveOn γ (-mgradient 𝓘(ℝ, ℝ) (id : ℝ → ℝ)) (Ici 0)) :
    EqOn γ (fun t ↦ γ 0 - t) (Ici 0) := by
  rw [isMIntegralCurveOn_iff_isIntegralCurveOn] at hγ
  intro t ht
  refine eq_of_has_deriv_right_eq (a := 0) (b := t) (f' := fun _ ↦ -1)
    (fun s hs ↦ ((hγ s hs.1).mono (Ici_subset_Ici.2 hs.1)).congr_deriv
      (neg_mgradient_id_real_apply _))
    (fun s _ ↦ ((hasDerivAt_id s).const_sub (γ 0)).hasDerivWithinAt)
    (fun s hs ↦ (hγ s hs.1).continuousWithinAt.mono (Icc_subset_Ici_self))
    (by fun_prop) (by simp) t ⟨ht, le_rfl⟩

/-- **No forward trajectory of `-grad f` stays in a compact set**, for `f(x) = x` on `ℝ` with the
standard metric. -/
theorem not_mapsTo_of_isMIntegralCurveOn_neg_mgradient_id
    (hγ : IsMIntegralCurveOn γ (-mgradient 𝓘(ℝ, ℝ) (id : ℝ → ℝ)) (Ici 0)) {K : Set ℝ}
    (hK : IsCompact K) : ¬ MapsTo γ (Ici 0) K := by
  intro hmaps
  obtain ⟨m, hm⟩ := hK.bddBelow
  have ht : (0 : ℝ) ≤ max 0 (γ 0 - m + 1) := le_max_left _ _
  have hle := hm (hmaps ht)
  rw [eqOn_sub_of_isMIntegralCurveOn_neg_mgradient_id hγ ht] at hle
  linarith [le_max_right 0 (γ 0 - m + 1)]

/-- **No forward trajectory of `-grad f` converges**, for `f(x) = x` on `ℝ` with the standard
metric. -/
theorem not_tendsto_of_isMIntegralCurveOn_neg_mgradient_id
    (hγ : IsMIntegralCurveOn γ (-mgradient 𝓘(ℝ, ℝ) (id : ℝ → ℝ)) (Ici 0)) (p : ℝ) :
    ¬ Tendsto γ atTop (𝓝 p) := by
  have hbot : Tendsto γ atTop atBot := by
    refine (tendsto_atBot_add_const_left atTop (γ 0) tendsto_neg_atTop_atBot).congr' ?_
    filter_upwards [eventually_ge_atTop 0] with t ht
    simp [eqOn_sub_of_isMIntegralCurveOn_neg_mgradient_id hγ ht, sub_eq_add_neg]
  exact not_tendsto_nhds_of_tendsto_atBot hbot p

end Untrapped

/-! ### The function `f(x) = x` and a discontinuous metric -/

section Singular

/-- The weight `λ` of `singularLineMetric`: `λ(x) = x⁻²` for `x ≠ 0` and `λ(0) = 1`. -/
noncomputable def singularLineWeight (x : ℝ) : ℝ :=
  if x = 0 then 1 else (x ^ 2)⁻¹

/-- The weight `λ` of `singularLineMetric` is positive. -/
theorem singularLineWeight_pos (x : ℝ) : 0 < singularLineWeight x := by
  rw [singularLineWeight]
  split_ifs <;> positivity

/-- **A discontinuous Riemannian metric on the line.** The inner product on the tangent space of
`ℝ` at `x` is `λ(x) v w`, where `λ(x) = x⁻²` for `x ≠ 0` and `λ(0) = 1`. Each tangent space
carries an inner product, but `λ` is discontinuous at `0`. -/
noncomputable def singularLineMetric :
    RiemannianMetric (fun x : ℝ ↦ TangentSpace 𝓘(ℝ, ℝ) x) where
  inner x := singularLineWeight x • ContinuousLinearMap.mul ℝ ℝ
  -- The tangent space `TangentSpace 𝓘(ℝ, ℝ) x` is `ℝ` by definition, so each field is restated
  -- with `change` as a statement about real numbers.
  symm x := by
    change ∀ v w : ℝ, singularLineWeight x * (v * w) = singularLineWeight x * (w * v)
    intro v w
    ring
  pos x := by
    change ∀ v : ℝ, v ≠ 0 → 0 < singularLineWeight x * (v * v)
    intro v hv
    exact mul_pos (singularLineWeight_pos x) (mul_self_pos.2 hv)
  continuousAt x := by
    change ContinuousAt (fun v : ℝ ↦ singularLineWeight x * (v * v)) 0
    fun_prop
  isVonNBounded x :=
    (singularLineWeight x • ContinuousLinearMap.mul ℝ ℝ).isVonNBounded_setOf_lt_one_of_pos
      fun v hv ↦ mul_pos (singularLineWeight_pos x) (mul_self_pos.2 hv)

/-- The inner products of `singularLineMetric`: `⟪v, w⟫ₓ = λ(x) v w`. -/
@[simp]
theorem singularLineMetric_inner (x v w : ℝ) :
    singularLineMetric.inner x v w = singularLineWeight x * (v * w) := by
  rw [singularLineMetric]
  -- The bilinear form `λ(x) • mul ℝ ℝ` on `TangentSpace 𝓘(ℝ, ℝ) x = ℝ` evaluates by definition;
  -- the tangent-space typing of `v` and `w` blocks the `ContinuousLinearMap` simp lemmas.
  rfl

/-- **The metric `singularLineMetric` is not continuous**, so in particular it is not `C¹`: the
inner product of the constant unit vector field with itself is `λ`, which is discontinuous at
`0`. -/
theorem not_isContMDiffRiemannianBundle_singularLineMetric (n : WithTop ℕ∞) :
    let _ : RiemannianBundle (fun x : ℝ ↦ TangentSpace 𝓘(ℝ, ℝ) x) := ⟨singularLineMetric⟩
    ¬ IsContMDiffRiemannianBundle 𝓘(ℝ, ℝ) n ℝ (fun x : ℝ ↦ TangentSpace 𝓘(ℝ, ℝ) x) := by
  intro _ h
  have h0 : IsContMDiffRiemannianBundle 𝓘(ℝ, ℝ) 0 ℝ (fun x : ℝ ↦ TangentSpace 𝓘(ℝ, ℝ) x) :=
    h.of_le zero_le
  -- The constant unit vector field, as a continuous map into the tangent bundle.
  have hv : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 0
      (fun x : ℝ ↦ (TotalSpace.mk' ℝ x (1 : TangentSpace 𝓘(ℝ, ℝ) x) :
        TotalSpace ℝ (fun x : ℝ ↦ TangentSpace 𝓘(ℝ, ℝ) x))) := by
    rw [contMDiff_zero_iff]
    exact (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm.continuous.comp
      (continuous_id.prodMk continuous_const)
  have hcont : Continuous fun x : ℝ ↦ singularLineMetric.inner x (1 : ℝ) (1 : ℝ) :=
    (ContMDiff.inner_bundle hv hv).continuous
  simp only [singularLineMetric_inner, singularLineWeight, mul_one] at hcont
  -- Near `0` the weight `λ(x) = x⁻²` is large, while `λ(0) = 1`.
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.1 hcont.continuousAt 1 one_pos
  set x : ℝ := min (δ / 2) (1 / 2)
  have hx : 0 < x := lt_min (half_pos hδ) one_half_pos
  have hxδ : dist x 0 < δ := by
    rw [Real.dist_0_eq_abs, abs_of_pos hx]
    exact (min_le_left _ _).trans_lt (half_lt_self hδ)
  have hx2 : x ^ 2 ≤ 1 / 4 := by
    have : x ≤ 1 / 2 := min_le_right _ _
    nlinarith
  have hlam : 4 ≤ (x ^ 2)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) (by positivity)]
    linarith
  have := hball hxδ
  simp only [hx.ne', ↓reduceIte, Real.dist_eq, abs_lt] at this
  linarith [this.2]

/-- For the metric `singularLineMetric`, the gradient of `f(x) = x` is `λ⁻¹`: it is `x²` for
`x ≠ 0` and `1` at `0`. -/
theorem mgradient_id_singularLineMetric (x : ℝ) :
    let _ : RiemannianBundle (fun x : ℝ ↦ TangentSpace 𝓘(ℝ, ℝ) x) := ⟨singularLineMetric⟩
    mgradient 𝓘(ℝ, ℝ) (id : ℝ → ℝ) x = (if x = 0 then 1 else x ^ 2 : ℝ) := by
  intro _
  have h := inner_mgradient_model_space (id : ℝ → ℝ) x 1
  obtain ⟨m, hm⟩ : ∃ m : ℝ, mgradient 𝓘(ℝ, ℝ) (id : ℝ → ℝ) x = m := ⟨_, rfl⟩
  rw [hm] at h ⊢
  rw [fderiv_id, ContinuousLinearMap.id_apply] at h
  -- The inner product of the installed metric is `λ(x) v w`.
  have h' : singularLineMetric.inner x m (1 : ℝ) = 1 := h
  rw [singularLineMetric_inner, singularLineWeight, mul_one] at h'
  clear h
  split_ifs at h' ⊢ with hx
  · exact (one_mul m).symm.trans h'
  · have : x ^ 2 ≠ 0 := pow_ne_zero 2 hx
    field_simp at h'
    exact h'

/-- For the metric `singularLineMetric`, the negative gradient of `f(x) = x` is `-x²` off `0`. -/
private theorem neg_mgradient_id_singularLineMetric_apply {x : ℝ} (hx : x ≠ 0) :
    let _ : RiemannianBundle (fun x : ℝ ↦ TangentSpace 𝓘(ℝ, ℝ) x) := ⟨singularLineMetric⟩
    (-mgradient 𝓘(ℝ, ℝ) (id : ℝ → ℝ)) x = (-x ^ 2 : ℝ) := by
  intro _
  rw [Pi.neg_apply, mgradient_id_singularLineMetric]
  simp only [hx, ↓reduceIte]
  -- Both sides are the real number `-x²`, read in `ℝ` and in its tangent space.
  rfl

/-- For the metric `singularLineMetric`, the curve `t ↦ x₀ / (1 + x₀ t)` is a forward trajectory
of `-grad f`, for `f(x) = x` and `x₀ > 0`: it solves `x' = -x²`. -/
theorem isMIntegralCurveOn_neg_mgradient_id_singularLineMetric {x₀ : ℝ} (hx₀ : 0 < x₀) :
    let _ : RiemannianBundle (fun x : ℝ ↦ TangentSpace 𝓘(ℝ, ℝ) x) := ⟨singularLineMetric⟩
    IsMIntegralCurveOn (fun t ↦ x₀ / (1 + x₀ * t)) (-mgradient 𝓘(ℝ, ℝ) (id : ℝ → ℝ))
      (Ici 0) := by
  intro _
  rw [isMIntegralCurveOn_iff_isIntegralCurveOn]
  intro t ht
  have hpos : 0 < 1 + x₀ * t := by nlinarith [mem_Ici.1 ht]
  have hne : x₀ / (1 + x₀ * t) ≠ 0 := (div_pos hx₀ hpos).ne'
  have hderiv : HasDerivAt (fun t ↦ x₀ / (1 + x₀ * t)) (-(x₀ / (1 + x₀ * t)) ^ 2) t := by
    refine ((hasDerivAt_const t x₀).div (((hasDerivAt_id t).const_mul x₀).const_add 1)
      hpos.ne').congr_deriv ?_
    rw [div_pow]
    simp only [id]
    ring
  exact hderiv.hasDerivWithinAt.congr_deriv (neg_mgradient_id_singularLineMetric_apply hne).symm

/-- **The regularity of the metric cannot be dropped.** For the discontinuous metric
`singularLineMetric`, a forward trajectory of `-grad f`, for `f(x) = x`, stays in the compact
interval `[0, 1]` and converges to a point which is not a critical point of `f`. So, when the
metric is not `C¹`, the limit of a convergent forward trajectory need not be critical (compare
`IsMIntegralCurveOn.mem_criticalPoints_of_tendsto_neg_mgradient`), and a trapped trajectory need
not converge to a critical point (compare
`TauCeti.IsMorse.exists_tendsto_of_isMIntegralCurveOn_neg_mgradient`). -/
theorem exists_isMIntegralCurveOn_neg_mgradient_id_singularLineMetric :
    let _ : RiemannianBundle (fun x : ℝ ↦ TangentSpace 𝓘(ℝ, ℝ) x) := ⟨singularLineMetric⟩
    ∃ γ : ℝ → ℝ, IsMIntegralCurveOn γ (-mgradient 𝓘(ℝ, ℝ) (id : ℝ → ℝ)) (Ici 0) ∧
      MapsTo γ (Ici 0) (Icc 0 1) ∧
        ∃ p ∉ criticalPoints 𝓘(ℝ, ℝ) (id : ℝ → ℝ), Tendsto γ atTop (𝓝 p) := by
  intro _
  refine ⟨fun t ↦ 1 / (1 + 1 * t), isMIntegralCurveOn_neg_mgradient_id_singularLineMetric one_pos,
    ?_, 0, by simp [criticalPoints_id_real], ?_⟩
  · intro t (ht : 0 ≤ t)
    have hpos : 0 < 1 + 1 * t := by linarith
    exact ⟨by positivity, (div_le_one hpos).2 (by linarith)⟩
  · refine (tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left atTop 1 tendsto_id)).congr
      fun t ↦ ?_
    simp

end Singular

end TauCeti
