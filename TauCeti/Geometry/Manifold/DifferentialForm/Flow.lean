/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.LieDeriv
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Basic
public import TauCeti.Geometry.Manifold.IntegralCurve.GlobalFlow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.Calculus.DifferentialForm.Flow
import TauCeti.Analysis.Calculus.ParametricFDeriv
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Chart
import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
import TauCeti.Geometry.Manifold.MFDeriv.Parametric
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# Lie derivatives of differential forms along flows

Let `Z` be a `C²` vector field on a finite-dimensional manifold without boundary, with maximal
flow `φ` (`TauCeti.flowOf`), and let `α` be a differential form. Wherever the flow through a point
`x` is defined at time `t`, the pullbacks `φₜ^* α` at `x` form a curve in the alternating maps on
`T_x M`, and its velocity is the pullback of the Lie derivative:

`d/dt (φₜ^* α)ₓ = (φₜ^* L_Z α)ₓ`

(`TauCeti.hasDerivAt_mpullback_flowOf`). Here `L_Z α` is `TauCeti.mlieDerivForm`, which is
defined in charts with no reference to flows, so this is the flow characterization of the Lie
derivative of forms. At `t = 0` it reads `d/dt|₀ (φₜ^* α)ₓ = (L_Z α)ₓ`. No completeness is
needed.

Integrating it along the open interval of times at which the flow through `x` is defined: if
`L_Z α = g • α` for a continuous function `g`, then `(φₜ^* α)ₓ = exp (∫₀ᵗ g (φₛ x) ds) • αₓ`
(`TauCeti.mpullback_flowOf_apply_eq_exp_integral_smul`). This is how the local flow of a contact
Hamiltonian vector field rescales the contact form.

When `Z` is complete its maximal flow is the global flow `ψ` (`TauCeti.globalFlow`), and these
statements hold at every time and point (`TauCeti.hasDerivAt_mpullback_globalFlow`,
`TauCeti.mpullback_globalFlow_apply_eq_exp_integral_smul`). In particular, if `L_Z α = c • α` for a
real number `c`, then `ψₜ^* α = e^{ct} α` for every time `t`
(`TauCeti.mpullback_globalFlow_eq_exp_smul`). This is how a Liouville flow rescales the
symplectic form and its primitive, which turns hypersurfaces of contact type and the boundary of a
Liouville domain into one-parameter families with conjugate characteristic foliations. For a
closed form with closed contraction `ι_Z α`, Cartan's formula gives `L_Z α = 0`, so the flow
preserves the form (`TauCeti.mpullback_globalFlow_of_mextDeriv_interior_eq_zero`); this is why
Hamiltonian flows are symplectic.

In the preferred chart at a point the flow is a jointly `C²` family of maps, and the statement
reduces to its flat counterpart `TauCeti.hasDerivAt_compContinuousLinearMap_fderiv`. This
reduction holds for every jointly `C²` family of maps `ψᵤ` which is the identity near `y` at a
time `t` and moves the points near `y` with the velocity of a vector field `V` at time `t`: then
`d/du|_{u = t} (ψᵤ^* α)_y = (L_V α)_y` (`TauCeti.hasDerivAt_mpullback_of_eq_id`). Time-dependent
flows are the other instance (`TauCeti.Geometry.Manifold.DifferentialForm.Flow.TimeDependent`).

## Main results

* `TauCeti.hasDerivAt_mpullback_of_eq_id`: along a `C²` family of maps which is the identity
  near `y` at time `t`, the velocity of the pullbacks at `y` at time `t` is the Lie derivative.
* `TauCeti.hasDerivAt_mpullback_of_eq_comp`: for a family factoring as `ψᵤ = χᵤ ∘ g`, the
  velocity of the pullbacks by `ψᵤ` is the pullback by `g` of the velocity of those by `χᵤ`.
* `TauCeti.mpullback_eq_of_forall_mlieDerivForm_eq_zero`: pullbacks whose velocities are the
  pullbacks of vanishing Lie derivatives are independent of time.
* `TauCeti.hasDerivAt_mpullback_flowOf_zero`, `TauCeti.hasDerivAt_mpullback_globalFlow_zero`: the
  velocity of the pullbacks along the maximal or global flow at `t = 0` is `L_Z α`.
* `TauCeti.hasDerivAt_mpullback_flowOf`: wherever the maximal flow is defined, the time derivative
  of `φₜ^* α` is `φₜ^* L_Z α`.
* `TauCeti.mpullback_flowOf_apply_eq_exp_integral_smul`: if `L_Z α = g • α`, then
  `(φₜ^* α)ₓ = exp (∫₀ᵗ g (φₛ x) ds) • αₓ` wherever the maximal flow is defined.
* `TauCeti.hasDerivAt_mpullback_globalFlow`: the time derivative of `ψₜ^* α` is `ψₜ^* L_Z α`.
* `TauCeti.mpullback_globalFlow_apply_eq_exp_integral_smul`: if `L_Z α = g • α`, then
  `(ψₜ^* α)ₓ = exp (∫₀ᵗ g (ψₛ x) ds) • αₓ`.
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
/-- **The Lie derivative is the velocity of pulled-back forms along a family of maps.** Let `ψᵤ` be
a family of maps of `M` which is the identity near `y` at time `t`, is jointly `C²` near `(t, y)`,
and moves the points near `y` at time `t` with the velocity of a vector field `V`. Then for a form
`α` differentiable at `y`, `d/du|_{u = t} (ψᵤ^* α)_y = (L_V α)_y`. -/
theorem hasDerivAt_mpullback_of_eq_id {ψ : ℝ → M → M} {V : (x : M) → TangentSpace I x} {t : ℝ}
    (y : M) (hid : ∀ᶠ x in 𝓝 y, ψ t x = x)
    (hsmooth : ContMDiffAt (𝓘(ℝ, ℝ).prod I) I 2 (fun p : ℝ × M ↦ ψ p.1 p.2) (t, y))
    (hvel : ∀ᶠ x in 𝓝 y,
      HasMFDerivAt 𝓘(ℝ, ℝ) I (fun u ↦ ψ u x) t ((1 : ℝ →L[ℝ] ℝ).smulRight (V (ψ t x))))
    (hα : MDifferentiableAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F))
      (fun z ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) z (α z)) y) :
    HasDerivAt (F := E [⋀^Fin k]→L[ℝ] F) (fun u ↦ mpullback I I (ψ u) α y)
      (mlieDerivForm V α y) t := by
  -- The family read in the chart at `y`, and the field read in the same chart.
  set G : ℝ × E → E := fun p ↦ extChartAt I y (ψ p.1 ((extChartAt I y).symm p.2))
  set W := VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I y).symm V (range I) with hW
  have hGsmooth : ContDiffAt ℝ 2 G (t, extChartAt I y y) :=
    Manifold.contDiffAt_extChartAt_family hid.self_of_nhds hsmooth
  have hdiff : ∀ᶠ p in 𝓝 (t, extChartAt I y y), DifferentiableAt ℝ G p :=
    (hGsmooth.eventually (by simp)).mono fun p hp ↦ hp.differentiableAt (by simp)
  have hGt_nhds : (fun z ↦ G (t, z)) =ᶠ[𝓝 (extChartAt I y y)] id := by
    have hid' : ∀ᶠ z in 𝓝 (extChartAt I y y), ψ t ((extChartAt I y).symm z) =
        (extChartAt I y).symm z :=
      (continuousAt_extChartAt_symm y).tendsto.eventually (p := fun x ↦ ψ t x = x)
        (by rwa [extChartAt_to_inv])
    filter_upwards [extChartAt_target_mem_nhds y, hid'] with z hz hz'
    simp only [G, hz', id_eq]
    exact (extChartAt I y).right_inv hz
  have hGt : G (t, extChartAt I y y) = extChartAt I y y := hGt_nhds.self_of_nhds
  -- Read in the chart at `y`, the points near `y` move at time `t` with the coordinate velocity
  -- `W` of `V`.
  have hvel' : ∀ᶠ z in 𝓝 (extChartAt I y y), HasDerivAt (fun u ↦ G (u, z)) (W z) t := by
    have h : ∀ᶠ z in 𝓝 (extChartAt I y y),
        HasMFDerivAt 𝓘(ℝ, ℝ) I (fun u ↦ ψ u ((extChartAt I y).symm z)) t
            ((1 : ℝ →L[ℝ] ℝ).smulRight (V (ψ t ((extChartAt I y).symm z)))) ∧
          ψ t ((extChartAt I y).symm z) = (extChartAt I y).symm z :=
      (continuousAt_extChartAt_symm y).tendsto.eventually
        (p := fun x ↦ HasMFDerivAt 𝓘(ℝ, ℝ) I (fun u ↦ ψ u x) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (V (ψ t x))) ∧ ψ t x = x)
        (by rw [extChartAt_to_inv]; exact hvel.and hid)
    filter_upwards [extChartAt_target_mem_nhds y, h] with z hz ⟨hzv, hzid⟩
    have hsrc : ψ t ((extChartAt I y).symm z) ∈ (extChartAt I y).source :=
      hzid.symm ▸ (extChartAt I y).map_target hz
    refine (hzv.hasDerivAt_extChartAt_comp hsrc).congr_deriv ?_
    rw [hW]
    conv_rhs => rw [← (extChartAt I y).right_inv hz, ← hzid]
    rw [VectorField.mpullbackWithin_extChartAt_symm_apply V hsrc]
    -- `tangentCoordChange` is by definition this fibre coordinate of the trivialization
    -- (`TangentBundle.trivializationAt_apply`, `tangentCoordChange_def`).
    rfl
  -- The spatial derivative of the coordinate family solves the variational equation at time `t`:
  -- by symmetry of second derivatives, it differentiates to the derivative of the velocity `W`.
  have htime : timeFDeriv G t =ᶠ[𝓝 (extChartAt I y y)] W := by
    have hd : ∀ᶠ z in 𝓝 (extChartAt I y y), DifferentiableAt ℝ G (t, z) :=
      ((continuous_const.prodMk continuous_id).tendsto (extChartAt I y y)).eventually hdiff
    filter_upwards [hvel', hd] with z hz hdz
    exact (hasDerivAt_parameterCurve hdz).unique hz
  have hspatial : HasDerivAt (fun u ↦ fderiv ℝ (fun z ↦ G (u, z)) (extChartAt I y y))
      (fderiv ℝ W (G (t, extChartAt I y y)) ∘L
        fderiv ℝ (fun z ↦ G (t, z)) (extChartAt I y y)) t := by
    have h := hasDerivAt_spatialFDeriv (F := G) (t := t) (x := extChartAt I y y)
      (by simpa only [minSmoothness_of_isRCLikeNormedField] using hGsmooth)
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
    (by rw [hGt]; exact hvel'.self_of_nhds)
    hspatial
  -- Near time `t`, the maps `ψᵤ` are differentiable at `y` and keep `y` in the chart at `y`.
  have hψ : ∀ᶠ u in 𝓝 t, MDifferentiableAt I I (ψ u) y := by
    have h := ((continuous_id.prodMk continuous_const).tendsto t).eventually
      ((contMDiffAt_iff_contMDiffAt_nhds (by simp)).1 hsmooth)
    filter_upwards [h] with u hu
    exact (hu.comp_of_eq (contMDiffAt_const.prodMk contMDiffAt_id) rfl).mdifferentiableAt
      (by norm_num)
  have hcont : ContinuousAt (fun u ↦ ψ u y) t :=
    hsmooth.continuousAt.comp (f := fun u : ℝ ↦ (u, y))
      (continuous_id.prodMk continuous_const).continuousAt
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
    rw [hGu, RoughForm.mpullback_eq_compContinuousLinearMap α y hψu hu, I.range_eq_univ,
      fderivWithin_univ]
    -- The two coordinate expressions of `ψᵤ` differ only by unfolding `Function.comp`.
    rfl
  refine (hflat.congr_of_eventuallyEq heq).congr_deriv ?_
  rw [deriv_const, zero_add, hGt, hGt_nhds.fderiv_eq, fderiv_id, mlieDerivForm_def,
    ← hW, I.range_eq_univ]
  -- `W` takes values in the tangent spaces of the model, which are `E` only up to unfolding.
  erw [lieDerivFormWithin_univ]
  ext v
  simp

omit [FiniteDimensional ℝ E] [T2Space M] [I.Boundaryless] [IsManifold I 2 M] in
/-- **Moving the base point of pulled-back forms.** Let the maps `ψᵤ` factor near time `t` and
near `x` as `χᵤ ∘ g` through a map `g` differentiable at `x`, with each `χᵤ` differentiable at
`g x`. If the
pullbacks `(χᵤ^* α)_{g x}` have velocity `β (g x)` at time `t`, then the pullbacks `(ψᵤ^* α)ₓ` have
velocity `(g^* β)ₓ` there. -/
theorem hasDerivAt_mpullback_of_eq_comp {ψ χ : ℝ → M → M} {g : M → M} {β : RoughForm I M F k}
    {x : M} {t : ℝ} (hψ : ∀ᶠ u in 𝓝 t, ψ u =ᶠ[𝓝 x] χ u ∘ g) (hg : MDifferentiableAt I I g x)
    (hχ : ∀ᶠ u in 𝓝 t, MDifferentiableAt I I (χ u) (g x))
    (h : HasDerivAt (F := E [⋀^Fin k]→L[ℝ] F) (fun u ↦ mpullback I I (χ u) α (g x)) (β (g x)) t) :
    HasDerivAt (F := E [⋀^Fin k]→L[ℝ] F) (fun u ↦ mpullback I I (ψ u) α x)
      (mpullback I I g β x) t := by
  -- Pulling back along `g` composes with its derivative, a continuous linear operator.
  set L : E →L[ℝ] E := mfderiv I I g x
  have hL := (compContinuousLinearMapCLM (ι := Fin k) (F := F) L).hasFDerivAt.comp_hasDerivAt t h
  refine (hL.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards [hψ, hχ] with u hu hχu
    rw [hu.mpullback_eq, mpullback_comp_at hg hχu, mpullback_eq_compContinuousLinearMap_mfderiv]
    -- `compContinuousLinearMapCLM L` sends an alternating map to its composition with `L`.
    rfl
  · rw [mpullback_eq_compContinuousLinearMap_mfderiv]
    rfl

omit [FiniteDimensional ℝ E] [T2Space M] [I.Boundaryless] [IsManifold I 2 M] in
/-- **Pullbacks with vanishing Lie derivatives are constant.** If at every time `u` and point `x`
the pullbacks `(ψᵤ^* α)ₓ` have velocity `(ψᵤ^* L_{Vᵤ} α)ₓ`, and every Lie derivative `L_{Vᵤ} α`
vanishes, then `ψₛ^* α = ψₜ^* α` for all times `s` and `t`. -/
theorem mpullback_eq_of_forall_mlieDerivForm_eq_zero {ψ : ℝ → M → M}
    {V : ℝ → (x : M) → TangentSpace I x}
    (hd : ∀ u x, HasDerivAt (F := E [⋀^Fin k]→L[ℝ] F) (fun u ↦ mpullback I I (ψ u) α x)
      (mpullback I I (ψ u) (mlieDerivForm (V u) α) x) u)
    (hV : ∀ u, mlieDerivForm (V u) α = 0) (s t : ℝ) :
    mpullback I I (ψ s) α = mpullback I I (ψ t) α := by
  funext x
  have hderiv (u : ℝ) :
      HasDerivAt (F := E [⋀^Fin k]→L[ℝ] F) (fun u ↦ mpullback I I (ψ u) α x) 0 u := by
    have h := hd u x
    rwa [hV u, mpullback_zero] at h
  exact is_const_of_deriv_eq_zero (fun u ↦ (hderiv u).differentiableAt)
    (fun u ↦ (hderiv u).deriv) s t

/-! ### Maximal flows -/

section MaximalFlow

variable (hZ : ContMDiff I I.tangent 2 (fun y ↦ (⟨y, Z y⟩ : TangentBundle I M)))
include hZ

/-- **The Lie derivative is the velocity of pulled-back forms at time zero.** For a `C²` vector
field `Z` with maximal flow `φ` and a form `α` differentiable at `y`,
`d/dt|₀ (φₜ^* α)_y = (L_Z α)_y`. The field need not be complete. -/
theorem hasDerivAt_mpullback_flowOf_zero (y : M)
    (hα : MDifferentiableAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F))
      (fun z ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) z (α z)) y) :
    HasDerivAt (F := E [⋀^Fin k]→L[ℝ] F) (fun s ↦ mpullback I I (flowOf Z s) α y)
      (mlieDerivForm Z α y) 0 := by
  have hZ1 := hZ.of_le one_le_two
  refine hasDerivAt_mpullback_of_eq_id (ψ := flowOf Z) (V := Z) y
    (Eventually.of_forall (flowOf_zero hZ1))
    ((contMDiffOn_flowOf (n := 2) one_le_two hZ).contMDiffAt
      ((isOpen_flowDomain hZ1).mem_nhds (mem_flowDomain_zero hZ1 y)))
    (Eventually.of_forall fun x ↦ ?_) hα
  have hopen : {s | (s, x) ∈ flowDomain Z} ∈ 𝓝 (0 : ℝ) :=
    ((isOpen_flowDomain hZ1).preimage (continuous_id.prodMk continuous_const)).mem_nhds
      (mem_flowDomain_zero hZ1 x)
  exact ((isMIntegralCurveOn_flowOf hZ1 x).isMIntegralCurveAt hopen).hasMFDerivAt

/-- **Lie derivatives along maximal flows.** For a `C²` vector field `Z` with maximal flow `φ`, a
time `t` at which the flow through `x` is defined, and a form `α` differentiable at `φₜ x`, the
pullbacks `(φₛ^* α)ₓ` have velocity `(φₜ^* L_Z α)ₓ` at time `t`. -/
theorem hasDerivAt_mpullback_flowOf {t : ℝ} {x : M} (hx : (t, x) ∈ flowDomain Z)
    (hα : MDifferentiableAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F))
      (fun z ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) z (α z)) (flowOf Z t x)) :
    HasDerivAt (F := E [⋀^Fin k]→L[ℝ] F) (fun s ↦ mpullback I I (flowOf Z s) α x)
      (mpullback I I (flowOf Z t) (mlieDerivForm Z α) x) t := by
  have hZ1 := hZ.of_le one_le_two
  have hD := isOpen_flowDomain hZ1
  have hφ : ContMDiffAt I I 2 (flowOf Z t) x :=
    contMDiffAt_flowOf_comp (n := 2) one_le_two hZ contMDiffAt_const contMDiffAt_id hx
  -- Near `(0, x)`, the time-`t` map is defined at the second coordinate and the time given by the
  -- first coordinate is defined after it.
  have hev : ∀ᶠ p in 𝓝 ((0 : ℝ), x),
      (t, p.2) ∈ flowDomain Z ∧ (p.1, flowOf Z t p.2) ∈ flowDomain Z :=
    ((continuous_const.prodMk continuous_snd).continuousAt.eventually_mem (hD.mem_nhds hx)).and
      ((continuousAt_fst.prodMk (hφ.continuousAt.comp continuousAt_snd)).eventually_mem
        (hD.mem_nhds (mem_flowDomain_zero hZ1 _)))
  rw [nhds_prod_eq] at hev
  have hsub : Tendsto (fun s ↦ s - t) (𝓝 t) (𝓝 0) := by
    simpa using (continuous_sub_right t).tendsto t
  -- By the group law, `φₛ = φ_{s - t} ∘ φₜ` near `x` for `s` near `t`, so the derivative at `t` is
  -- read at `0`.
  have h0 := hasDerivAt_mpullback_flowOf_zero hZ (flowOf Z t x) hα
  refine hasDerivAt_mpullback_of_eq_comp (ψ := flowOf Z) (χ := fun s ↦ flowOf Z (s - t)) ?_
    (hφ.mdifferentiableAt (by norm_num)) ?_
    (HasDerivAt.comp_sub_const (x := t) (a := t) (by rwa [sub_self]))
  · filter_upwards [hsub.eventually hev.curry] with s hs
    refine hs.mono fun y hy ↦ ?_
    have h := (flowOf_add hZ1 hy.1 hy.2).2
    rw [add_sub_cancel] at h
    exact h.symm
  · filter_upwards [hsub.eventually hev.curry] with s hs
    exact (contMDiffAt_flowOf_comp (n := 2) one_le_two hZ contMDiffAt_const contMDiffAt_id
      hs.self_of_nhds.2).mdifferentiableAt (by norm_num)

/-- **Rescaling along a maximal flow.** If the Lie derivative of a differentiable form `α` along a
`C²` vector field `Z` is `g • α` for a continuous function `g`, then wherever the maximal flow `φ`
of `Z` through `x` is defined at time `t`, the time-`t` map pulls `α` back at `x` to
`exp (∫₀ᵗ g (φₛ x) ds) • α x`. -/
theorem mpullback_flowOf_apply_eq_exp_integral_smul {g : M → ℝ} (hg : Continuous g)
    (hα : MDifferentiable I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F))
      (fun z ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) z (α z)))
    (hL : mlieDerivForm Z α = fun y ↦ g y • α y) {t : ℝ} {x : M} (hx : (t, x) ∈ flowDomain Z) :
    mpullback I I (flowOf Z t) α x = Real.exp (∫ s in 0..t, g (flowOf Z s x)) • α x := by
  have hZ1 := hZ.of_le one_le_two
  -- The times at which the flow through `x` is defined form an open interval `J` containing `0`.
  set J : Set ℝ := {s | (s, x) ∈ flowDomain Z}
  have hJ : J = maximalIntegralCurveInterval Z x := by
    ext s
    exact mem_flowDomain
  have hJo : IsOpen J := hJ ▸ isOpen_maximalIntegralCurveInterval
  have hJc : J.OrdConnected := hJ ▸ ordConnected_maximalIntegralCurveInterval
  have hJ0 : (0 : ℝ) ∈ J := mem_flowDomain_zero hZ1 x
  -- The pullbacks at `x`, as alternating maps on the model space, and the integrated rate.
  set P : ℝ → E [⋀^Fin k]→L[ℝ] F := fun s ↦ mpullback I I (flowOf Z s) α x
  set G : ℝ → ℝ := fun s ↦ ∫ τ in 0..s, g (flowOf Z τ x)
  have hcont : ContinuousOn (fun s ↦ g (flowOf Z s x)) J :=
    hg.comp_continuousOn (isMIntegralCurveOn_flowOf hZ1 x).continuousOn
  have hG (s : ℝ) (hs : s ∈ J) : HasDerivAt G (g (flowOf Z s x)) s :=
    intervalIntegral.integral_hasDerivAt_right
      ((hcont.mono (hJc.uIcc_subset hJ0 hs)).intervalIntegrable)
      (hcont.stronglyMeasurableAtFilter hJo s hs) (hcont.continuousAt (hJo.mem_nhds hs))
  have hP (s : ℝ) (hs : s ∈ J) : HasDerivAt P (g (flowOf Z s x) • P s) s := by
    have h := hasDerivAt_mpullback_flowOf hZ hs (hα _)
    rwa [hL, mpullback_fun_smul] at h
  -- `s ↦ e^{-G s} P s` has zero derivative on the interval `J`, so it is constant there.
  have hderiv (s : ℝ) (hs : s ∈ J) : HasDerivAt (fun s ↦ Real.exp (-G s) • P s) 0 s := by
    refine ((hG s hs).neg.exp.smul (hP s hs)).congr_deriv ?_
    module
  have hconst := hJo.is_const_of_deriv_eq_zero hJc.isPreconnected
    (fun s hs ↦ (hderiv s hs).differentiableAt.differentiableWithinAt)
    (fun s hs ↦ (hderiv s hs).deriv) hx hJ0
  have hG0 : G 0 = 0 := intervalIntegral.integral_same
  have hP0 : P 0 = α x := by
    have h : mpullback I I (flowOf Z 0) α = α := by
      rw [show flowOf Z 0 = id from funext (flowOf_zero hZ1), mpullback_id]
    exact congrFun h x
  rw [hG0, neg_zero, Real.exp_zero, one_smul, hP0] at hconst
  have hPt : P t = Real.exp (G t) • (Real.exp (-G t) • P t) := by
    rw [smul_smul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_smul]
  rw [hconst] at hPt
  -- The value at `x` of the pulled-back form is `P t`.
  exact hPt

end MaximalFlow

/-! ### Complete vector fields -/

variable (hc : IsCompleteVectorField Z)
  (hZ : ContMDiff I I.tangent 2 (fun y ↦ (⟨y, Z y⟩ : TangentBundle I M)))
include hc hZ

/-- **The Lie derivative is the velocity of pulled-back forms at time zero.** For a complete `C²`
vector field `Z` with flow `ψ` and a form `α` differentiable at `y`,
`d/dt|₀ (ψₜ^* α)_y = (L_Z α)_y`. -/
theorem hasDerivAt_mpullback_globalFlow_zero (y : M)
    (hα : MDifferentiableAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F))
      (fun z ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) z (α z)) y) :
    HasDerivAt (F := E [⋀^Fin k]→L[ℝ] F)
      (fun s ↦ mpullback I I (globalFlow Z (hZ.of_le one_le_two) hc s) α y)
      (mlieDerivForm Z α y) 0 := by
  rw [← flowOf_eq_globalFlow (hZ.of_le one_le_two) hc]
  exact hasDerivAt_mpullback_flowOf_zero hZ y hα

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
  rw [← flowOf_eq_globalFlow (hZ.of_le one_le_two) hc] at hα ⊢
  exact hasDerivAt_mpullback_flowOf hZ (hc.mem_flowDomain t x) hα

/-- **Rescaling along a flow.** If the Lie derivative of a differentiable form `α` along a
complete `C²` vector field `Z` is `g • α` for a continuous function `g`, then the time-`t` map of
the flow `ψ` of `Z` pulls `α` back at `x` to `exp (∫₀ᵗ g (ψₛ x) ds) • α x`. -/
theorem mpullback_globalFlow_apply_eq_exp_integral_smul {g : M → ℝ} (hg : Continuous g)
    (hα : MDifferentiable I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F))
      (fun z ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) z (α z)))
    (hL : mlieDerivForm Z α = fun y ↦ g y • α y) (t : ℝ) (x : M) :
    mpullback I I (globalFlow Z (hZ.of_le one_le_two) hc t) α x =
      Real.exp (∫ s in 0..t, g (globalFlow Z (hZ.of_le one_le_two) hc s x)) • α x := by
  rw [← flowOf_eq_globalFlow (hZ.of_le one_le_two) hc]
  exact mpullback_flowOf_apply_eq_exp_integral_smul hZ hg hα hL (hc.mem_flowDomain t x)

/-- **Exponential rescaling along a flow.** If the Lie derivative of a differentiable form `α`
along a complete `C²` vector field `Z` is `c • α`, then the time-`t` map of the flow of `Z` pulls
`α` back to `e^{ct} α`. -/
theorem mpullback_globalFlow_eq_exp_smul {c : ℝ}
    (hα : MDifferentiable I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F))
      (fun z ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) z (α z)))
    (hL : mlieDerivForm Z α = c • α) (t : ℝ) :
    mpullback I I (globalFlow Z (hZ.of_le one_le_two) hc t) α = Real.exp (c * t) • α := by
  funext x
  rw [mpullback_globalFlow_apply_eq_exp_integral_smul hc hZ continuous_const hα hL t x,
    intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm, Pi.smul_apply]

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
