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
Liouville domain into one-parameter families with conjugate characteristic foliations. For a
closed form with closed contraction `ι_Z α`, Cartan's formula gives `L_Z α = 0`, so the flow
preserves the form (`TauCeti.mpullback_globalFlow_of_mextDeriv_interior_eq_zero`); this is why
Hamiltonian flows are symplectic.

In the preferred chart at a point the flow is a jointly `C²` family of maps, and the statement
reduces to its flat counterpart `TauCeti.hasDerivAt_compContinuousLinearMap_fderiv`. This
reduction holds for every family of maps `ψᵤ` which is the identity near `y` at a time `t` and,
in the chart at `y`, is jointly `C²` with velocity `V` at time `t`: then
`d/du|_{u = t} (ψᵤ^* α)_y = (L_V α)_y` (`TauCeti.hasDerivAt_mpullback_of_eq_id`). Time-dependent
flows are the other instance (`TauCeti.Geometry.Manifold.DifferentialForm.Flow.TimeDependent`).

## Main results

* `TauCeti.hasDerivAt_mpullback_of_eq_id`: along a `C²` family of maps which is the identity
  near `y` at time `t`, the velocity of the pullbacks at `y` at time `t` is the Lie derivative.
* `TauCeti.hasDerivAt_mpullback_globalFlow_zero`: the velocity of `ψₜ^* α` at `t = 0` is `L_Z α`.
* `TauCeti.hasDerivAt_mpullback_globalFlow`: the time derivative of `ψₜ^* α` is `ψₜ^* L_Z α`.
* `TauCeti.mpullback_globalFlow_eq_exp_smul`: if `L_Z α = c • α`, then `ψₜ^* α = e^{ct} α`.
* `TauCeti.mpullback_globalFlow_of_mextDeriv_interior_eq_zero`: if `α` is closed and `ι_Z α` is
  closed, then `ψₜ^* α = α`.

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

/-! ### Pullbacks along a family of maps -/

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- While `f y` stays in the chart at `y`, the pullback of a form at `y` by `f` is the flat pullback
of its coordinate expression by `f` read in that chart. -/
private theorem compContinuousLinearMap_fderiv_eq_mpullback (y : M) {f : M → M}
    (hf : MDifferentiableAt I I f y) (hfy : f y ∈ (extChartAt I y).source) :
    compContinuousLinearMap (α.inChartAt y (extChartAt I y (f y)))
        (fderiv ℝ (fun z ↦ extChartAt I y (f ((extChartAt I y).symm z))) (extChartAt I y y)) =
      mpullback I I f α y := by
  have hyt : extChartAt I y y ∈ (extChartAt I y).target := mem_extChartAt_target y
  have hf' : MDifferentiableAt I I f ((extChartAt I y).symm (extChartAt I y y)) := by
    rwa [extChartAt_to_inv]
  have hsymm : MDifferentiableWithinAt 𝓘(ℝ, E) I (extChartAt I y).symm univ (extChartAt I y y) := by
    rw [← I.range_eq_univ]
    exact mdifferentiableWithinAt_extChartAt_symm hyt
  -- The flat pullback is the pullback by `f` composed with the inverse chart, read in the chart.
  have h := RoughForm.mpullbackWithin_eq_compContinuousLinearMap α y
    (by simpa only [Function.comp_apply, extChartAt_to_inv] using hfy)
    (hf'.comp_mdifferentiableWithinAt _ hsymm) uniqueDiffWithinAt_univ
  rw [fderivWithin_univ] at h
  simp only [Function.comp_apply, extChartAt_to_inv] at h
  rw [← RoughForm.inChartAt_extChartAt_self (mpullback I I f α) y,
    RoughForm.inChartAt_mpullback α f y hyt hf', I.range_eq_univ]
  refine h.symm.trans ?_
  ext v
  rw [mpullbackWithin_apply, compContinuousLinearMap_apply]
  rfl

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- **The Lie derivative is the velocity of pulled-back forms along a family of maps.** Let `ψᵤ` be
a family of maps of `M` which is the identity near `y` at time `t` and which, read in the chart at
`y`, is jointly `C²` near `(t, y)` and moves the points near `y` at time `t` with the coordinate
velocity of a vector field `V`. Then for a form `α` differentiable at `y`,
`d/du|_{u = t} (ψᵤ^* α)_y = (L_V α)_y`. -/
theorem hasDerivAt_mpullback_of_eq_id {ψ : ℝ → M → M} {V : (x : M) → TangentSpace I x} {t : ℝ}
    (y : M) (hid : ∀ᶠ x in 𝓝 y, ψ t x = x) (hψ : ∀ᶠ u in 𝓝 t, MDifferentiableAt I I (ψ u) y)
    (hcont : ContinuousAt (fun u ↦ ψ u y) t)
    (hsmooth : ContDiffAt ℝ 2
      (fun p : ℝ × E ↦ extChartAt I y (ψ p.1 ((extChartAt I y).symm p.2))) (t, extChartAt I y y))
    (hvel : ∀ᶠ z in 𝓝 (extChartAt I y y),
      HasDerivAt (fun u ↦ extChartAt I y (ψ u ((extChartAt I y).symm z)))
        (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I y).symm V (range I) z) t)
    (hα : MDifferentiableAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F))
      (fun z ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) z (α z)) y) :
    HasDerivAt (F := E [⋀^Fin k]→L[ℝ] F) (fun u ↦ mpullback I I (ψ u) α y)
      (mlieDerivForm V α y) t := by
  -- The family read in the chart at `y`, and the field read in the same chart.
  set G : ℝ × E → E := fun p ↦ extChartAt I y (ψ p.1 ((extChartAt I y).symm p.2))
  set W := VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I y).symm V (range I) with hW
  have hdiff : ∀ᶠ p in 𝓝 (t, extChartAt I y y), DifferentiableAt ℝ G p :=
    (hsmooth.eventually (by simp)).mono fun p hp ↦ hp.differentiableAt (by simp)
  have hGt_nhds : (fun z ↦ G (t, z)) =ᶠ[𝓝 (extChartAt I y y)] id := by
    have hid' : ∀ᶠ z in 𝓝 (extChartAt I y y), ψ t ((extChartAt I y).symm z) =
        (extChartAt I y).symm z :=
      (continuousAt_extChartAt_symm y).tendsto.eventually (p := fun x ↦ ψ t x = x)
        (by rwa [extChartAt_to_inv])
    filter_upwards [extChartAt_target_mem_nhds y, hid'] with z hz hz'
    simp only [G, hz', id_eq]
    exact (extChartAt I y).right_inv hz
  have hGt : G (t, extChartAt I y y) = extChartAt I y y := hGt_nhds.self_of_nhds
  -- The spatial derivative of the coordinate family solves the variational equation at time `t`:
  -- by symmetry of second derivatives, it differentiates to the derivative of the velocity `W`.
  have htime : timeFDeriv G t =ᶠ[𝓝 (extChartAt I y y)] W := by
    have hd : ∀ᶠ z in 𝓝 (extChartAt I y y), DifferentiableAt ℝ G (t, z) :=
      ((continuous_const.prodMk continuous_id).tendsto (extChartAt I y y)).eventually hdiff
    filter_upwards [hvel, hd] with z hz hdz
    exact (hasDerivAt_parameterCurve hdz).unique hz
  have hspatial : HasDerivAt (fun u ↦ fderiv ℝ (fun z ↦ G (u, z)) (extChartAt I y y))
      (fderiv ℝ W (G (t, extChartAt I y y)) ∘L
        fderiv ℝ (fun z ↦ G (t, z)) (extChartAt I y y)) t := by
    have h := hasDerivAt_spatialFDeriv (F := G) (t := t) (x := extChartAt I y y)
      (by simpa only [minSmoothness_of_isRCLikeNormedField] using hsmooth)
    rw [hGt, hGt_nhds.fderiv_eq, fderiv_id, ContinuousLinearMap.comp_id, ← htime.fderiv_eq]
    refine h.congr_of_eventuallyEq ?_
    have hd : ∀ᶠ u in 𝓝 t, DifferentiableAt ℝ G (u, extChartAt I y y) :=
      ((continuous_id.prodMk continuous_const).tendsto t).eventually hdiff
    filter_upwards [hd] with u hu
    exact fderiv_timeSlice hu
  have hflat := hasDerivAt_compContinuousLinearMap_fderiv («ω» := fun _ ↦ α.inChartAt y)
    (ψ := fun u z ↦ G (u, z)) (X := fun _ ↦ W) (x := extChartAt I y y) (t := t)
    (by
      rw [hGt]
      exact (α.differentiableAt_inChartAt hα).comp (t, extChartAt I y y)
        differentiableAt_snd)
    (by rw [hGt]; exact hvel.self_of_nhds)
    hspatial
  -- Near time `t`, the pullback at `y` is the flat pullback in the chart at `y`.
  have hsrc : ∀ᶠ u in 𝓝 t, ψ u y ∈ (extChartAt I y).source :=
    hcont.preimage_mem_nhds (by
      rw [hid.self_of_nhds]
      exact (isOpen_extChartAt_source y).mem_nhds (mem_extChartAt_source y))
  have heq : (fun u ↦ mpullback I I (ψ u) α y) =ᶠ[𝓝 t]
      fun u ↦ (α.inChartAt y (G (u, extChartAt I y y))).compContinuousLinearMap
        (fderiv ℝ (fun z ↦ G (u, z)) (extChartAt I y y)) := by
    filter_upwards [hsrc, hψ] with u hu hψu
    have hGu : G (u, extChartAt I y y) = extChartAt I y (ψ u y) := by
      simp only [G, extChartAt_to_inv]
    rw [hGu]
    exact (compContinuousLinearMap_fderiv_eq_mpullback y hψu hu).symm
  refine (hflat.congr_of_eventuallyEq heq).congr_deriv ?_
  rw [deriv_const, zero_add, hGt, hGt_nhds.fderiv_eq, fderiv_id, mlieDerivForm_def,
    ← hW, I.range_eq_univ]
  -- `W` takes values in the tangent spaces of the model, which are `E` only up to unfolding.
  erw [lieDerivFormWithin_univ]
  ext v
  simp

/-! ### Complete vector fields -/

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

/-- **The Lie derivative is the velocity of pulled-back forms at time zero.** For a complete `C²`
vector field `Z` with flow `ψ` and a form `α` differentiable at `y`,
`d/dt|₀ (ψₜ^* α)_y = (L_Z α)_y`. -/
theorem hasDerivAt_mpullback_globalFlow_zero (y : M)
    (hα : MDifferentiableAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F))
      (fun z ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) z (α z)) y) :
    HasDerivAt (F := E [⋀^Fin k]→L[ℝ] F)
      (fun s ↦ mpullback I I (globalFlow Z (hZ.of_le one_le_two) hc s) α y)
      (mlieDerivForm Z α y) 0 :=
  hasDerivAt_mpullback_of_eq_id (ψ := globalFlow Z (hZ.of_le one_le_two) hc) (V := Z) y
    (Eventually.of_forall (Flow.map_zero_apply _))
    (Eventually.of_forall fun s ↦
      (contMDiff_globalFlow_apply hc (n := 2) (by norm_num) hZ s).mdifferentiableAt
        (by norm_num))
    ((globalFlow Z (hZ.of_le one_le_two) hc).continuous continuous_id
      continuous_const).continuousAt
    (contDiffAt_extChartAt_globalFlow hc hZ y)
    (eventually_of_mem (extChartAt_target_mem_nhds y) fun _ hz ↦
      hasDerivAt_extChartAt_globalFlow hc hZ y hz) hα

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

/-- **Flows preserve closed forms with closed contraction.** For a closed smooth form `β` whose
contraction `ι_Z β` with a complete `C²` vector field `Z` is closed, the flow `ψ` of `Z` satisfies
`ψₜ^* β = β` for every time `t`, because Cartan's formula gives `L_Z β = d(ι_Z β) = 0`. -/
theorem mpullback_globalFlow_of_mextDeriv_interior_eq_zero {β : SmoothForm I M F (k + 1)}
    (hβ : β.IsClosed) (hZβ : mextDeriv (RoughForm.interior Z β.1) = 0) (t : ℝ) :
    mpullback (F := F) I I (globalFlow Z (hZ.of_le one_le_two) hc t) β.1 = β.1 := by
  -- Cartan's formula: `L_Z β = d(ι_Z β) = 0`.
  have hL : mlieDerivForm Z β.1 = (0 : ℝ) • β.1 := by
    rw [zero_smul, SmoothForm.mlieDerivForm_eq_mextDeriv_interior
      (hZ.mdifferentiable two_ne_zero) hβ, hZβ]
  simpa only [zero_mul, Real.exp_zero, one_smul] using
    mpullback_globalFlow_eq_exp_smul hc hZ β.mdifferentiable hL t

end TauCeti
