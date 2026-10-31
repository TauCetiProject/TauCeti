/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.LieDeriv
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Basic
public import TauCeti.Geometry.Manifold.IntegralCurve.GlobalFlow
import TauCeti.Analysis.Calculus.DifferentialForm.Flow
import TauCeti.Analysis.Calculus.ParametricFDeriv
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Chart
import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# Lie derivatives of differential forms along flows

Let `Z` be a complete `C²` vector field on a finite-dimensional manifold without boundary, with
flow `ψ`, and let `α` be a differential form. The pullbacks `ψₜ^* α` at a point `x` form a curve
in the alternating maps on `T_x M`, and its velocity is the pullback of the Lie derivative:

`d/dt (ψₜ^* α)ₓ = (ψₜ^* L_Z α)ₓ`

(`TauCeti.hasDerivAt_mpullback_globalFlow`). Here `L_Z α` is `TauCeti.mlieDerivForm`, which is
defined in charts with no reference to flows, so this is the flow characterization of the Lie
derivative of forms. At `t = 0` it reads `d/dt|₀ (ψₜ^* α)ₓ = (L_Z α)ₓ`.

Integrating it: if `L_Z α = c • α` for a real number `c`, then `ψₜ^* α = e^{ct} α` for every
time `t` (`TauCeti.mpullback_globalFlow_eq_exp_smul`). This is how a Liouville flow rescales the
symplectic form and its primitive, which turns hypersurfaces of contact type and the boundary of a
Liouville domain into one-parameter families with conjugate characteristic foliations.

In the preferred chart at a point the flow is a jointly `C²` family of maps, and the statement
reduces to its flat counterpart `TauCeti.hasDerivAt_compContinuousLinearMap_fderiv`.

## Main results

* `TauCeti.hasDerivAt_mpullback_globalFlow_zero`: the velocity of `ψₜ^* α` at `t = 0` is `L_Z α`.
* `TauCeti.hasDerivAt_mpullback_globalFlow`: the time derivative of `ψₜ^* α` is `ψₜ^* L_Z α`.
* `TauCeti.mpullback_globalFlow_eq_exp_smul`: if `L_Z α = c • α`, then `ψₜ^* α = e^{ct} α`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2012, Theorem 12.37 and
  Proposition 12.36.
-/

public section

noncomputable section

open Set Filter Bundle ContinuousAlternatingMap
open scoped Manifold Topology ContDiff

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I 2 M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}
  {Z : (x : M) → TangentSpace I x} {α : RoughForm I M F k}

variable (hc : IsCompleteVectorField Z)
  (hZ : ContMDiff I I.tangent 2 (fun y ↦ (⟨y, Z y⟩ : TangentBundle I M)))
include hc hZ

/-- The flow of `Z`, read in the chart at `y`, is jointly `C²` in time and coordinates near
`(0, y)`. -/
private theorem contDiffAt_extChartAt_globalFlow (y : M) :
    ContDiffAt ℝ 2 (fun p : ℝ × E ↦
      extChartAt I y (globalFlow Z (hZ.of_le one_le_two) hc p.1 ((extChartAt I y).symm p.2)))
      (0, extChartAt I y y) := by
  have hsymm : ContMDiffAt 𝓘(ℝ, E) I 2 (extChartAt I y).symm (extChartAt I y y) := by
    have h := contMDiffWithinAt_extChartAt_symm_range_self (I := I) (n := 2) y
    rwa [I.range_eq_univ, contMDiffWithinAt_univ] at h
  have hpair : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) (𝓘(ℝ, ℝ).prod I) 2
      (fun p : ℝ × E ↦ (p.1, (extChartAt I y).symm p.2)) (0, extChartAt I y y) :=
    contMDiffAt_fst.prodMk (ContMDiffAt.comp (0, extChartAt I y y) hsymm contMDiffAt_snd)
  have hflow := (contMDiff_globalFlow_uncurry hc (n := 2) (by norm_num) hZ).contMDiffAt
    (x := (0, (extChartAt I y).symm (extChartAt I y y)))
  have hcomp := (contMDiffAt_extChartAt (I := I) (n := 2) (x := y)).comp_of_eq
    (ContMDiffAt.comp (0, extChartAt I y y) hflow hpair) (by
      simp only [Function.comp_apply, extChartAt_to_inv]
      exact Flow.map_zero_apply _ y)
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod, contMDiffAt_iff_contDiffAt] at hcomp
  exact hcomp

/-- At time zero, the velocity of the flow of `Z` read in the chart at `y` is the coordinate
expression of `Z` in that chart. -/
private theorem hasDerivAt_extChartAt_globalFlow (y : M) {z : E}
    (hz : z ∈ (extChartAt I y).target) :
    HasDerivAt (fun s ↦
      extChartAt I y (globalFlow Z (hZ.of_le one_le_two) hc s ((extChartAt I y).symm z)))
      (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I y).symm Z (range I) z) 0 := by
  set q := (extChartAt I y).symm z
  have hq : q ∈ (extChartAt I y).source := (extChartAt I y).map_target hz
  have hcurve := ((isMIntegralCurve_globalFlow (hZ.of_le one_le_two) hc q).isMIntegralCurveOn
    univ).hasDerivAt_extChartAt (x := y) (mem_univ 0) univ_mem
    (by rw [Flow.map_zero_apply]; exact hq)
  rw [Flow.map_zero_apply] at hcurve
  refine hcurve.congr_deriv ?_
  -- In the tangent-bundle trivialization at `y`, the coordinate field is a coordinate change.
  have hVz := VectorField.mpullbackWithin_extChartAt_symm_apply Z hq
  rw [(extChartAt I y).right_inv hz] at hVz
  -- `tangentCoordChange` is by definition this fibre coordinate of the trivialization
  -- (`TangentBundle.trivializationAt_apply`, `tangentCoordChange_def`).
  rw [hVz]
  rfl

/-- While the orbit of `y` stays in the chart at `y`, the pullback of a form at `y` by the flow is
the flat pullback of its coordinate expression by the flow read in that chart. -/
private theorem compContinuousLinearMap_fderiv_eq_mpullback_globalFlow (y : M) {s : ℝ}
    (hs : globalFlow Z (hZ.of_le one_le_two) hc s y ∈ (extChartAt I y).source) :
    compContinuousLinearMap
        (α.inChartAt y (extChartAt I y (globalFlow Z (hZ.of_le one_le_two) hc s y)))
        (fderiv ℝ (fun z ↦
          extChartAt I y (globalFlow Z (hZ.of_le one_le_two) hc s ((extChartAt I y).symm z)))
          (extChartAt I y y)) =
      mpullback I I (globalFlow Z (hZ.of_le one_le_two) hc s) α y := by
  set ψ := globalFlow Z (hZ.of_le one_le_two) hc
  have hyt : extChartAt I y y ∈ (extChartAt I y).target := mem_extChartAt_target y
  have hψ : MDifferentiableAt I I (ψ s) ((extChartAt I y).symm (extChartAt I y y)) :=
    (contMDiff_globalFlow_apply hc (n := 2) (by norm_num) hZ s).mdifferentiableAt (by norm_num)
  have hsymm : MDifferentiableWithinAt 𝓘(ℝ, E) I (extChartAt I y).symm univ (extChartAt I y y) := by
    rw [← I.range_eq_univ]
    exact mdifferentiableWithinAt_extChartAt_symm hyt
  -- The flat pullback is the pullback by `ψ s` composed with the inverse chart, read in the chart.
  have h := RoughForm.mpullbackWithin_eq_compContinuousLinearMap α y
    (by simpa only [Function.comp_apply, extChartAt_to_inv] using hs)
    (hψ.comp_mdifferentiableWithinAt _ hsymm) uniqueDiffWithinAt_univ
  rw [fderivWithin_univ] at h
  simp only [Function.comp_apply, extChartAt_to_inv] at h
  rw [← RoughForm.inChartAt_extChartAt_self (mpullback I I (ψ s) α) y,
    RoughForm.inChartAt_mpullback α (ψ s) y hyt hψ, I.range_eq_univ]
  refine h.symm.trans ?_
  ext v
  rw [mpullbackWithin_apply, compContinuousLinearMap_apply]
  rfl

/-- **The Lie derivative is the velocity of pulled-back forms at time zero.** For a complete `C²`
vector field `Z` with flow `ψ` and a form `α` differentiable at `y`,
`d/dt|₀ (ψₜ^* α)_y = (L_Z α)_y`. -/
theorem hasDerivAt_mpullback_globalFlow_zero (y : M)
    (hα : MDifferentiableAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F))
      (fun z ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) z (α z)) y) :
    HasDerivAt (F := E [⋀^Fin k]→L[ℝ] F)
      (fun s ↦ mpullback I I (globalFlow Z (hZ.of_le one_le_two) hc s) α y)
      (mlieDerivForm Z α y) 0 := by
  set ψ := globalFlow Z (hZ.of_le one_le_two) hc
  -- The flow read in the chart at `y`, and the field read in the same chart.
  set F : ℝ × E → E := fun p ↦ extChartAt I y (ψ p.1 ((extChartAt I y).symm p.2))
  set V := VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I y).symm Z (range I) with hV
  have hyt : extChartAt I y y ∈ (extChartAt I y).target := mem_extChartAt_target y
  have hFsmooth : ContDiffAt ℝ 2 F (0, extChartAt I y y) := contDiffAt_extChartAt_globalFlow hc hZ y
  have hvel (z : E) (hz : z ∈ (extChartAt I y).target) : HasDerivAt (fun s ↦ F (s, z)) (V z) 0 :=
    hasDerivAt_extChartAt_globalFlow hc hZ y hz
  have hdiff : ∀ᶠ p in 𝓝 ((0 : ℝ), extChartAt I y y), DifferentiableAt ℝ F p :=
    (hFsmooth.eventually (by simp)).mono fun p hp ↦ hp.differentiableAt (by simp)
  have hFzero : ∀ z ∈ (extChartAt I y).target, F (0, z) = z := fun z hz ↦ by
    simp only [F]
    rw [Flow.map_zero_apply, (extChartAt I y).right_inv hz]
  have hFzero_nhds : (fun z ↦ F (0, z)) =ᶠ[𝓝 (extChartAt I y y)] id :=
    eventually_of_mem (extChartAt_target_mem_nhds y) hFzero
  -- The spatial derivative of the coordinate flow solves the variational equation at time zero:
  -- by symmetry of second derivatives, it differentiates to the derivative of the velocity `V`.
  have htime : timeFDeriv F 0 =ᶠ[𝓝 (extChartAt I y y)] V := by
    have hd : ∀ᶠ z in 𝓝 (extChartAt I y y), DifferentiableAt ℝ F (0, z) :=
      ((continuous_const.prodMk continuous_id).tendsto (extChartAt I y y)).eventually hdiff
    filter_upwards [extChartAt_target_mem_nhds y, hd] with z hz hdz
    exact (hasDerivAt_parameterCurve hdz).unique (hvel z hz)
  have hspatial : HasDerivAt (fun s ↦ fderiv ℝ (fun z ↦ F (s, z)) (extChartAt I y y))
      (fderiv ℝ V (F (0, extChartAt I y y)) ∘L
        fderiv ℝ (fun z ↦ F (0, z)) (extChartAt I y y)) 0 := by
    have h := hasDerivAt_spatialFDeriv (F := F) (t := 0) (x := extChartAt I y y)
      (by simpa only [minSmoothness_of_isRCLikeNormedField] using hFsmooth)
    rw [hFzero _ hyt, hFzero_nhds.fderiv_eq, fderiv_id, ContinuousLinearMap.comp_id,
      ← htime.fderiv_eq]
    refine h.congr_of_eventuallyEq ?_
    have hd : ∀ᶠ s in 𝓝 (0 : ℝ), DifferentiableAt ℝ F (s, extChartAt I y y) :=
      ((continuous_id.prodMk continuous_const).tendsto (0 : ℝ)).eventually hdiff
    filter_upwards [hd] with s hs
    exact fderiv_timeSlice hs
  have hflat := hasDerivAt_compContinuousLinearMap_fderiv («ω» := fun _ ↦ α.inChartAt y)
    (ψ := fun s z ↦ F (s, z)) (X := fun _ ↦ V) (x := extChartAt I y y) (t := 0)
    (by
      rw [hFzero _ hyt]
      exact (α.differentiableAt_inChartAt hα).comp ((0 : ℝ), extChartAt I y y)
        differentiableAt_snd)
    (by rw [hFzero _ hyt]; exact hvel _ hyt)
    hspatial
  -- Near time zero, the pullback at `y` is the flat pullback in the chart at `y`.
  have hsrc : ∀ᶠ s in 𝓝 (0 : ℝ), ψ s y ∈ (extChartAt I y).source := by
    have hcont : Continuous fun s ↦ ψ s y := ψ.continuous continuous_id continuous_const
    exact hcont.continuousAt.preimage_mem_nhds (by
      rw [Flow.map_zero_apply]
      exact (isOpen_extChartAt_source y).mem_nhds (mem_extChartAt_source y))
  have heq : (fun s ↦ mpullback I I (ψ s) α y) =ᶠ[𝓝 0]
      fun s ↦ (α.inChartAt y (F (s, extChartAt I y y))).compContinuousLinearMap
        (fderiv ℝ (fun z ↦ F (s, z)) (extChartAt I y y)) := by
    filter_upwards [hsrc] with s hs
    have hFs : F (s, extChartAt I y y) = extChartAt I y (ψ s y) := by
      simp only [F, extChartAt_to_inv]
    rw [hFs]
    exact (compContinuousLinearMap_fderiv_eq_mpullback_globalFlow hc hZ y hs).symm
  refine (hflat.congr_of_eventuallyEq heq).congr_deriv ?_
  rw [deriv_const, zero_add, hFzero _ hyt, hFzero_nhds.fderiv_eq, fderiv_id, mlieDerivForm_def,
    ← hV, I.range_eq_univ]
  -- `V` takes values in the tangent spaces of the model, which are `E` only up to unfolding.
  erw [lieDerivFormWithin_univ]
  ext v
  simp

/-- **Lie derivatives along flows.** For a complete `C²` vector field `Z` with flow `ψ` and a form
`α` differentiable at `ψₜ x`, the pullbacks `(ψₛ^* α)ₓ` have velocity `(ψₜ^* L_Z α)ₓ` at time
`t`. -/
theorem hasDerivAt_mpullback_globalFlow (x : M) (t : ℝ)
    (hα : MDifferentiableAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F))
      (fun z ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) z (α z))
      (globalFlow Z (hZ.of_le one_le_two) hc t x)) :
    HasDerivAt (F := E [⋀^Fin k]→L[ℝ] F)
      (fun s ↦ mpullback I I (globalFlow Z (hZ.of_le one_le_two) hc s) α x)
      (mpullback I I (globalFlow Z (hZ.of_le one_le_two) hc t) (mlieDerivForm Z α) x) t := by
  set ψ := globalFlow Z (hZ.of_le one_le_two) hc
  have hsmooth (s : ℝ) : MDifferentiable I I (ψ s) :=
    (contMDiff_globalFlow_apply hc (n := 2) (by norm_num) hZ s).mdifferentiable (by norm_num)
  set L : E →L[ℝ] E := mfderiv I I (ψ t) x
  -- By the group law, `ψ_{u + t}^* α = ψₜ^* (ψᵤ^* α)`, so the derivative at `t` is read at `0`.
  have hshift (u : ℝ) : mpullback I I (ψ (u + t)) α x =
      compContinuousLinearMapCLM (ι := Fin k) (F := F) L (mpullback I I (ψ u) α (ψ t x)) := by
    have hcomp : ψ (u + t) = ψ u ∘ ψ t := funext fun z ↦ ψ.map_add u t z
    rw [hcomp, mpullback_comp_at (hsmooth t x) (hsmooth u _)]
    ext v
    -- Both sides evaluate `ψᵤ^* α` at `ψₜ x` on the vectors `L (v i)`.
    rw [mpullback_apply]
    rfl
  have h0 := (compContinuousLinearMapCLM (ι := Fin k) (F := F) L).hasFDerivAt.comp_hasDerivAt
    (0 : ℝ) (hasDerivAt_mpullback_globalFlow_zero hc hZ (ψ t x) hα)
  have h := HasDerivAt.comp_sub_const (x := t) (a := t) (by rwa [sub_self])
  refine (h.congr_of_eventuallyEq (Eventually.of_forall fun s ↦ ?_)).congr_deriv ?_
  · have hs := hshift (s - t)
    rw [sub_add_cancel] at hs
    exact hs
  · ext v
    exact (mpullback_apply (ψ t) (mlieDerivForm Z α) x v).symm

/-- **Exponential rescaling along a flow.** If the Lie derivative of a differentiable form `α`
along a complete `C²` vector field `Z` is `c • α`, then the time-`t` map of the flow of `Z` pulls
`α` back to `e^{ct} α`. -/
theorem mpullback_globalFlow_eq_exp_smul {c : ℝ}
    (hα : MDifferentiable I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F))
      (fun z ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) z (α z)))
    (hL : mlieDerivForm Z α = c • α) (t : ℝ) :
    mpullback I I (globalFlow Z (hZ.of_le one_le_two) hc t) α = Real.exp (c * t) • α := by
  set ψ := globalFlow Z (hZ.of_le one_le_two) hc
  funext x
  -- The pullbacks at `x`, as alternating maps on the model space.
  set P : ℝ → E [⋀^Fin k]→L[ℝ] F := fun s ↦ mpullback I I (ψ s) α x
  have hderivP (s : ℝ) : HasDerivAt P (c • P s) s := by
    have h := hasDerivAt_mpullback_globalFlow hc hZ x s (hα _)
    rw [hL, mpullback_smul] at h
    -- The value at `x` of the form `c • ψₛ^* α` is `c • P s`.
    exact h
  -- `s ↦ e^{-cs} P s` has zero derivative, so it is constant.
  have hderiv (s : ℝ) : HasDerivAt (fun s ↦ Real.exp (-(c * s)) • P s) 0 s := by
    refine (((hasDerivAt_id' s).const_mul c).neg.exp.smul (hderivP s)).congr_deriv ?_
    module
  have hconst := is_const_of_deriv_eq_zero (fun s ↦ (hderiv s).differentiableAt)
    (fun s ↦ (hderiv s).deriv) t 0
  simp only [mul_zero, neg_zero, Real.exp_zero, one_smul] at hconst
  have hP0 : P 0 = α x := by
    have h : mpullback I I (ψ 0) α = α := by
      rw [ψ.map_zero, mpullback_id]
    exact congrFun h x
  have hPt : P t = Real.exp (c * t) • P 0 := by
    rw [← hconst, smul_smul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_smul]
  rw [hP0] at hPt
  -- The value at `x` of the form `e^{ct} • α` is `e^{ct} • α x`.
  exact hPt

end TauCeti
