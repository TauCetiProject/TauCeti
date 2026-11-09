/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Flow.TimeDependent
import TauCeti.Analysis.ODE.ScalarLinear
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth

/-!
# Time-dependent families of forms along time-dependent flows

A time-dependent family of differential forms on a manifold `M` is represented by a single form
`α` on `ℝ × M`. Its *slice* at time `t` is the form `α_t = ι_t^* α` on `M`, pulled back along the
inclusion `ι_t : y ↦ (t, y)`, and its *time derivative* at time `t` is the slice
`ι_t^* (L_{∂_t} α)` of the Lie derivative along the unit vector field `∂_t` of the time coordinate.
This is the velocity of the slices: `d/dt (α_t)_y = (ι_t^* L_{∂_t} α)_y`
(`TauCeti.hasDerivAt_mpullback_prodMk`).

Let `X` be a jointly `C²` time-dependent vector field on a finite-dimensional manifold without
boundary whose suspension `Z = (1, X)` on `ℝ × M` is complete, and let `φ_{s,t}` be its
time-dependent flow (`TauCeti.timeDependentFlowOf`). The main result is the time-dependent
pullback differentiation identity

`d/dt (φ_{s,t}^* α_t)ₓ = (φ_{s,t}^* (ι_t^* L_{∂_t} α + L_{X_t} α_t))ₓ`

(`TauCeti.hasDerivAt_mpullback_timeDependentFlowOf_mpullback_prodMk`). It extends
`TauCeti.hasDerivAt_mpullback_timeDependentFlowOf`, where the form does not depend on time. The
proof reads the family through the flow `Ψ` of the suspension: `Ψ_r (s, y) = (s + r, φ_{s,s+r} y)`,
so `φ_{s,t}^* α_t = ι_s^* (Ψ_{t-s}^* α)`, whose velocity is `ι_s^* Ψ_{t-s}^* L_Z α` by the
autonomous identity `TauCeti.hasDerivAt_mpullback_flowOf`. The slices of `L_Z α` split as

`ι_t^* L_Z α = ι_t^* L_{∂_t} α + L_{X_t} α_t`

(`TauCeti.mpullback_prodMk_mlieDerivForm_timeDependentSuspensionField`), because the Lie derivative
is additive in the vector field and the slices of the Lie derivative along the vertical field
`(0, X)` are the Lie derivatives of the slices along `X_t`
(`TauCeti.mpullback_prodMk_mlieDerivForm_vertical`).

Integrating the identity gives **Moser's principle** for families of forms: if the rate
`ι_t^* L_{∂_t} α + L_{X_t} α_t` is `g_t • α_t` for a continuous function `g`, then
`(φ_{s,t}^* α_t)ₓ = exp (∫ₛᵗ g (u, φ_{s,u} x) du) • (α_s)ₓ`
(`TauCeti.mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_exp_integral_smul`). The case
`g = 0` is the invariance `φ_{s,t}^* α_t = α_s` of Moser's argument for symplectic forms
(`TauCeti.mpullback_timeDependentFlowOf_mpullback_prodMk_eq`). A nonzero `g` is the shape of the
rate in Gray's argument for a family of contact forms, where the time-dependent field is chosen
to make the rate a multiple of the contact form.

## Main results

* `TauCeti.hasDerivAt_mpullback_prodMk`: the slices of `α` have velocity `ι_t^* L_{∂_t} α`.
* `TauCeti.mpullback_prodMk_mlieDerivForm_vertical`: `ι_t^* L_{(0, X)} α = L_{X_t} α_t`.
* `TauCeti.mpullback_prodMk_mlieDerivForm_timeDependentSuspensionField`:
  `ι_t^* L_Z α = ι_t^* L_{∂_t} α + L_{X_t} α_t`.
* `TauCeti.hasDerivAt_mpullback_timeDependentFlowOf_mpullback_prodMk`: the time derivative of
  `φ_{s,t}^* α_t` is `φ_{s,t}^* (ι_t^* L_{∂_t} α + L_{X_t} α_t)`.
* `TauCeti.mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_exp_integral_smul`: if the
  rate is `g_t • α_t`, the flow rescales the slices by `exp (∫ₛᵗ g (u, φ_{s,u} x) du)`.
* `TauCeti.mpullback_timeDependentFlowOf_mpullback_prodMk_eq`: if the rate vanishes, then
  `φ_{s,t}^* α_t = α_s`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2012, Chapter 22 (the
  derivative of pullbacks of a time-dependent family of forms along a time-dependent flow, in
  Moser's proof of the Darboux theorem, Theorem 22.13).
* Hansjörg Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Theorem 2.2.2 (Gray stability, whose proof differentiates the same pullbacks).
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
  {X : ℝ → (x : M) → TangentSpace I x} {α : RoughForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) F k}

/-! ### Slices of Lie derivatives -/

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- **Time derivatives of slices.** For a form `α` on `ℝ × M` differentiable at `(t, x)`, the
slices `ι_u^* α`, pulled back along the inclusions `ι_u : y ↦ (u, y)`, have velocity
`ι_t^* (L_{∂_t} α)` at `x` at time `t`, where `∂_t = (1, 0)` is the unit vector field of the time
coordinate. -/
theorem hasDerivAt_mpullback_prodMk (t : ℝ) (x : M)
    (hα : MDifferentiableAt (𝓘(ℝ, ℝ).prod I)
      ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, (ℝ × E) [⋀^Fin k]→L[ℝ] F))
      (fun p ↦ TotalSpace.mk' ((ℝ × E) [⋀^Fin k]→L[ℝ] F) p (α p)) (t, x)) :
    HasDerivAt (F := E [⋀^Fin k]→L[ℝ] F)
      (fun u ↦ mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk u) α x)
      (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t)
        (mlieDerivForm (fun _ ↦ ((1 : ℝ), (0 : E))) α) x) t := by
  set L : E →L[ℝ] ℝ × E := mfderiv I (𝓘(ℝ, ℝ).prod I) (Prod.mk t) x
  -- The translations `τ_r (u, y) = (u + r, y)` move the points with velocity `∂_t`.
  have hτsmooth : ContMDiff (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod I)) (𝓘(ℝ, ℝ).prod I) 2
      (fun q : ℝ × (ℝ × M) ↦ (q.2.1 + q.1, q.2.2)) :=
    ((contMDiff_fst.comp contMDiff_snd).add contMDiff_fst).prodMk
      (contMDiff_snd.comp contMDiff_snd)
  have hτvel (p : ℝ × M) : HasMFDerivAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) (fun r ↦ (p.1 + r, p.2)) 0
      ((1 : ℝ →L[ℝ] ℝ).smulRight ((1 : ℝ), (0 : E))) := by
    have hadd : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun r : ℝ ↦ p.1 + r) 0 (ContinuousLinearMap.id ℝ ℝ) :=
      hasMFDerivAt_iff_hasFDerivAt.2 ((hasFDerivAt_id 0).const_add p.1)
    exact (hadd.prodMk (hasMFDerivAt_const p.2 0)).congr_mfderiv
      (ContinuousLinearMap.ext fun r ↦ Prod.ext (mul_one (M := ℝ) r).symm (smul_zero _).symm)
  have hτ := hasDerivAt_mpullback_of_eq_id (I := 𝓘(ℝ, ℝ).prod I)
    (ψ := fun r (p : ℝ × M) ↦ (p.1 + r, p.2)) (V := fun _ ↦ ((1 : ℝ), (0 : E))) (t := 0) (t, x)
    (Eventually.of_forall fun p ↦ by simp) hτsmooth.contMDiffAt
    (Eventually.of_forall hτvel) hα
  -- Since `ι_u = τ_{u - t} ∘ ι_t`, the slice at time `u` is `ι_t^* τ_{u - t}^* α`.
  have hslice (u : ℝ) : mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk u) α x =
      compContinuousLinearMapCLM (ι := Fin k) (F := F) L
        (mpullback (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) (fun p : ℝ × M ↦ (p.1 + (u - t), p.2))
          α (t, x)) := by
    have hcomp : Prod.mk u = (fun p : ℝ × M ↦ (p.1 + (u - t), p.2)) ∘ Prod.mk t := by
      funext y
      simp
    have hτr : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) 2
        (fun p : ℝ × M ↦ (p.1 + (u - t), p.2)) :=
      (contMDiff_fst.add contMDiff_const).prodMk contMDiff_snd
    rw [hcomp, mpullback_comp_at
      ((contMDiff_const.prodMk contMDiff_id : ContMDiff I (𝓘(ℝ, ℝ).prod I) 1
        (Prod.mk t : M → ℝ × M)).mdifferentiableAt one_ne_zero)
      (hτr.mdifferentiableAt (by norm_num))]
    exact mpullback_apply_eq_compContinuousLinearMapCLM _ _ x
  have h0 := (compContinuousLinearMapCLM (ι := Fin k) (F := F) L).hasFDerivAt.comp_hasDerivAt
    (0 : ℝ) hτ
  have h := HasDerivAt.comp_sub_const (x := t) (a := t) (by rwa [sub_self])
  refine (h.congr_of_eventuallyEq (Eventually.of_forall hslice)).congr_deriv ?_
  exact (mpullback_apply_eq_compContinuousLinearMapCLM _ _ x).symm

variable (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 2
  (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
include hX

/-- **Slices of Lie derivatives along vertical fields.** For a jointly `C²` time-dependent vector
field `X` and a form `α` on `ℝ × M` which is `C¹` at `(t, x)`, the slice at time `t` of the Lie
derivative of `α` along the vertical field `(0, X)` is the Lie derivative of the slice
`α_t = ι_t^* α` along `X_t`: `ι_t^* L_{(0, X)} α = L_{X_t} α_t` at `x`. -/
theorem mpullback_prodMk_mlieDerivForm_vertical (t : ℝ) (x : M)
    (hα : ContMDiffAt (𝓘(ℝ, ℝ).prod I) ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, (ℝ × E) [⋀^Fin k]→L[ℝ] F)) 1
      (fun p ↦ TotalSpace.mk' ((ℝ × E) [⋀^Fin k]→L[ℝ] F) p (α p)) (t, x)) :
    mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t)
        (mlieDerivForm (fun p : ℝ × M ↦ ((0 : ℝ), X p.1 p.2)) α) x =
      mlieDerivForm (X t) (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t) α) x := by
  have hX₁ := hX.of_le (m := 1) one_le_two
  have hD := isOpen_timeDependentFlowDomain hX₁
  have hflow := contMDiffOn_timeDependentFlowOf (n := 2) (by norm_num) hX
  set L : E →L[ℝ] ℝ × E := mfderiv I (𝓘(ℝ, ℝ).prod I) (Prod.mk t) x
  have hι : ContMDiff I (𝓘(ℝ, ℝ).prod I) 2 (Prod.mk t : M → ℝ × M) :=
    contMDiff_const.prodMk contMDiff_id
  -- The family `ψ_r (u, y) = (u, φ_{u,u+r} y)` is the identity at `r = 0` and moves the points
  -- with velocity `(0, X)` there.
  set ψ : ℝ → ℝ × M → ℝ × M := fun r p ↦ (p.1, timeDependentFlowOf X p.1 (p.1 + r) p.2)
  set e : ℝ × (ℝ × M) → (ℝ × ℝ) × M := fun q ↦ ((q.2.1, q.2.1 + q.1), q.2.2)
  have he : ContMDiff (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod I)) ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) 2 e :=
    ((contMDiff_fst.comp contMDiff_snd).prodMk
      ((contMDiff_fst.comp contMDiff_snd).add contMDiff_fst)).prodMk
      (contMDiff_snd.comp contMDiff_snd)
  have hψsmooth (r : ℝ) (p : ℝ × M) (hp : ((p.1, p.1 + r), p.2) ∈ timeDependentFlowDomain X) :
      ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod I)) (𝓘(ℝ, ℝ).prod I) 2
        (fun q : ℝ × (ℝ × M) ↦ ψ q.1 q.2) (r, p) :=
    (contMDiff_fst.comp contMDiff_snd).contMDiffAt.prodMk
      ((hflow.contMDiffAt (hD.mem_nhds hp)).comp (r, p) he.contMDiffAt)
  have hψvel (p : ℝ × M) : HasMFDerivAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) (fun r ↦ ψ r p) 0
      ((1 : ℝ →L[ℝ] ℝ).smulRight ((0 : ℝ), X p.1 (ψ 0 p).2)) := by
    have hadd : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun r : ℝ ↦ p.1 + r) 0 (ContinuousLinearMap.id ℝ ℝ) :=
      hasMFDerivAt_iff_hasFDerivAt.2 ((hasFDerivAt_id 0).const_add p.1)
    have hflowvel : HasMFDerivAt 𝓘(ℝ, ℝ) I (fun u ↦ timeDependentFlowOf X p.1 u p.2) (p.1 + 0)
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X p.1 (timeDependentFlowOf X p.1 p.1 p.2))) := by
      rw [add_zero]
      exact hasMFDerivAt_timeDependentFlowOf hX₁ (mem_timeDependentFlowDomain_self hX₁ p.1 p.2)
    have hγ := hflowvel.comp (0 : ℝ) hadd
    have hψ0 : (ψ 0 p).2 = timeDependentFlowOf X p.1 p.1 p.2 := by simp [ψ]
    rw [hψ0]
    exact ((hasMFDerivAt_const p.1 0).prodMk hγ).congr_mfderiv
      (ContinuousLinearMap.ext fun r ↦ Prod.ext (smul_zero _).symm (rfl))
  have hψ := hasDerivAt_mpullback_of_eq_id (I := 𝓘(ℝ, ℝ).prod I) (ψ := ψ)
    (V := fun p : ℝ × M ↦ ((0 : ℝ), X p.1 p.2)) (t := 0) (t, x)
    (Eventually.of_forall fun p ↦ by simp [ψ, timeDependentFlowOf_self hX₁])
    (hψsmooth 0 (t, x) (by simpa using mem_timeDependentFlowDomain_self hX₁ t x))
    (Eventually.of_forall hψvel) (hα.mdifferentiableAt one_ne_zero)
  -- Slicing at time `t` turns `ψ_r` into the time-dependent flow from `t` to `t + r`.
  have hslice : ContMDiffAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) 1
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) y
        (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t) α y)) x :=
    hα.mpullback_form hι.contMDiffAt (by norm_num)
  have hR₀ := hasDerivAt_mpullback_timeDependentFlowOf_self hX t x
    (hslice.mdifferentiableAt one_ne_zero)
  have hR := HasDerivAt.comp_const_add t (0 : ℝ) (by rwa [add_zero])
  have hdom : ∀ᶠ r in 𝓝 (0 : ℝ), ((t, t + r), x) ∈ timeDependentFlowDomain X :=
    (by fun_prop : Continuous fun r : ℝ ↦ ((t, t + r), x)).continuousAt.eventually_mem
      (hD.mem_nhds (by simpa using mem_timeDependentFlowDomain_self hX₁ t x))
  have heq : (fun r ↦ compContinuousLinearMapCLM (ι := Fin k) (F := F) L
        (mpullback (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) (ψ r) α (t, x))) =ᶠ[𝓝 0]
      fun r ↦ mpullback I I (timeDependentFlowOf X t (t + r))
        (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t) α) x := by
    filter_upwards [hdom] with r hr
    have hφ : MDifferentiableAt I I (timeDependentFlowOf X t (t + r)) x :=
      ((hflow.contMDiffAt (hD.mem_nhds hr)).comp x
        ((contMDiff_const (c := (t, t + r))).prodMk contMDiff_id).contMDiffAt).mdifferentiableAt
        (by norm_num)
    have hψr : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) (ψ r) (t, x) :=
      ((hψsmooth r (t, x) hr).comp (t, x)
        ((contMDiff_const (c := r)).prodMk contMDiff_id).contMDiffAt).mdifferentiableAt
        (by norm_num)
    -- Both sides are the pullback of `α` along `y ↦ (t, φ_{t,t+r} y)`.
    refine (mpullback_apply_eq_compContinuousLinearMapCLM (Prod.mk t) _ x).symm.trans ?_
    rw [← mpullback_comp_at (hι.mdifferentiableAt (by norm_num)) hψr,
      ← mpullback_comp_at hφ (hι.mdifferentiableAt (by norm_num))]
    rfl
  have hL := (compContinuousLinearMapCLM (ι := Fin k) (F := F) L).hasFDerivAt.comp_hasDerivAt
    (0 : ℝ) hψ
  exact (mpullback_apply_eq_compContinuousLinearMapCLM _ _ x).trans
    (hL.unique (hR.congr_of_eventuallyEq heq))

/-- **Slices of Lie derivatives along the suspension.** For a jointly `C²` time-dependent vector
field `X` with suspension `Z = (1, X)` and a form `α` on `ℝ × M` which is `C¹` at `(t, x)`, the
slice at time `t` of `L_Z α` is the time derivative of `α` plus the Lie derivative of the slice
along `X_t`: `ι_t^* L_Z α = ι_t^* L_{∂_t} α + L_{X_t} α_t` at `x`. -/
theorem mpullback_prodMk_mlieDerivForm_timeDependentSuspensionField (t : ℝ) (x : M)
    (hα : ContMDiffAt (𝓘(ℝ, ℝ).prod I) ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, (ℝ × E) [⋀^Fin k]→L[ℝ] F)) 1
      (fun p ↦ TotalSpace.mk' ((ℝ × E) [⋀^Fin k]→L[ℝ] F) p (α p)) (t, x)) :
    mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t)
        (mlieDerivForm (timeDependentSuspensionField X) α) x =
      mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t)
          (mlieDerivForm (fun _ ↦ ((1 : ℝ), (0 : E))) α) x +
        mlieDerivForm (X t) (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t) α) x := by
  -- The suspension is the sum of `∂_t` and the vertical field `(0, X)`.
  set V : (p : ℝ × M) → TangentSpace (𝓘(ℝ, ℝ).prod I) p := fun _ ↦ ((1 : ℝ), (0 : E))
  set W : (p : ℝ × M) → TangentSpace (𝓘(ℝ, ℝ).prod I) p := fun p ↦ ((0 : ℝ), X p.1 p.2)
  have hsplit : timeDependentSuspensionField X = V + W :=
    funext fun p ↦ Prod.ext ((timeDependentSuspensionField_fst X p).trans (add_zero 1).symm)
      ((timeDependentSuspensionField_snd X p).trans (zero_add _).symm)
  have h0 : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 2
      (fun p : ℝ × M ↦ (⟨p.2, (0 : ℝ → (x : M) → TangentSpace I x) p.1 p.2⟩ : TangentBundle I M)) :=
    (contMDiff_zeroSection ℝ (TangentSpace I)).comp contMDiff_snd
  have hV : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I).tangent
      (fun p ↦ (V p : TangentBundle (𝓘(ℝ, ℝ).prod I) (ℝ × M))) (t, x) :=
    (contMDiff_const_prod_field 1 h0).mdifferentiableAt (by norm_num)
  have hW : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I).tangent
      (fun p ↦ (W p : TangentBundle (𝓘(ℝ, ℝ).prod I) (ℝ × M))) (t, x) :=
    (contMDiff_const_prod_field 0 hX).mdifferentiableAt (by norm_num)
  rw [← mpullback_prodMk_mlieDerivForm_vertical hX t x hα, hsplit,
    mpullback_apply_eq_compContinuousLinearMapCLM, mpullback_apply_eq_compContinuousLinearMapCLM,
    mpullback_apply_eq_compContinuousLinearMapCLM, mlieDerivForm_add_left α hV hW, map_add]

/-! ### Pullbacks of families along time-dependent flows -/

variable (hc : IsCompleteVectorField (timeDependentSuspensionField X))
include hc

/-- The velocity of `φ_{s,u}^* α_u` at time `t` is `φ_{s,t}^* ι_t^* L_Z α`, where `Z` is the
suspension. Since the flow of `Z` is `Ψ_r (u, y) = (u + r, φ_{u,u+r} y)`, the pullback
`φ_{s,u}^* α_u` is `ι_s^* Ψ_{u-s}^* α`, and the velocity of `Ψ_r^* α` is `Ψ_r^* L_Z α`. -/
private theorem hasDerivAt_mpullback_timeDependentFlowOf_mpullback_prodMk_suspension
    (s t : ℝ) (x : M)
    (hα : MDifferentiableAt (𝓘(ℝ, ℝ).prod I)
      ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, (ℝ × E) [⋀^Fin k]→L[ℝ] F))
      (fun p ↦ TotalSpace.mk' ((ℝ × E) [⋀^Fin k]→L[ℝ] F) p (α p))
      (t, timeDependentFlowOf X s t x)) :
    HasDerivAt (F := E [⋀^Fin k]→L[ℝ] F)
      (fun u ↦ mpullback I I (timeDependentFlowOf X s u)
        (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk u) α) x)
      (mpullback I I (timeDependentFlowOf X s t)
        (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t)
          (mlieDerivForm (timeDependentSuspensionField X) α)) x) t := by
  have hX₁ := hX.of_le (m := 1) one_le_two
  have hZ := contMDiff_timeDependentSuspensionField hX
  have hφ := contMDiff_timeDependentFlowOf hc (n := 2) (by norm_num) hX
  have hι (u : ℝ) : MDifferentiable I (𝓘(ℝ, ℝ).prod I) (Prod.mk u : M → ℝ × M) :=
    (contMDiff_const.prodMk contMDiff_id : ContMDiff I (𝓘(ℝ, ℝ).prod I) 1
      (Prod.mk u : M → ℝ × M)).mdifferentiable one_ne_zero
  -- The flow of the suspension is `Ψ_r (u, y) = (u + r, φ_{u,u+r} y)`.
  have hΨ (r : ℝ) : flowOf (timeDependentSuspensionField X) r =
      fun p : ℝ × M ↦ (p.1 + r, timeDependentFlowOf X p.1 (p.1 + r) p.2) := by
    funext p
    have h := flowOf_timeDependentSuspensionField hX₁ (s := p.1) (t := p.1 + r) (x := p.2)
      ((timeDependentFlowDomain_eq_univ hc).symm ▸ mem_univ _)
    rwa [add_sub_cancel_left] at h
  have hΨsmooth (r : ℝ) : MDifferentiable (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I)
      (flowOf (timeDependentSuspensionField X) r) := by
    rw [hΨ]
    exact ((contMDiff_fst.add contMDiff_const).prodMk (hφ.comp
      ((contMDiff_fst.prodMk (contMDiff_fst.add contMDiff_const)).prodMk contMDiff_snd))
      ).mdifferentiable (by norm_num)
  set L : E →L[ℝ] ℝ × E := mfderiv I (𝓘(ℝ, ℝ).prod I) (Prod.mk s) x
  -- For every form `η` on `ℝ × M`, `φ_{s,u}^* η_u = ι_s^* Ψ_{u-s}^* η` at `x`.
  have hkey (η : RoughForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) F k) (u : ℝ) :
      mpullback I I (timeDependentFlowOf X s u) (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk u) η) x =
        compContinuousLinearMapCLM (ι := Fin k) (F := F) L
          (mpullback (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I)
            (flowOf (timeDependentSuspensionField X) (u - s)) η (s, x)) := by
    have hcomp : Prod.mk u ∘ timeDependentFlowOf X s u =
        flowOf (timeDependentSuspensionField X) (u - s) ∘ Prod.mk s := by
      rw [hΨ]
      funext y
      simp
    have hφu : MDifferentiableAt I I (timeDependentFlowOf X s u) x :=
      (hφ.comp ((contMDiff_const (c := (s, u))).prodMk contMDiff_id)).mdifferentiableAt
        (by norm_num)
    rw [← mpullback_comp_at hφu (hι u _), hcomp, mpullback_comp_at (hι s x) (hΨsmooth _ _)]
    exact mpullback_apply_eq_compContinuousLinearMapCLM _ _ x
  have hαΨ : MDifferentiableAt (𝓘(ℝ, ℝ).prod I)
      ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, (ℝ × E) [⋀^Fin k]→L[ℝ] F))
      (fun p ↦ TotalSpace.mk' ((ℝ × E) [⋀^Fin k]→L[ℝ] F) p (α p))
      (flowOf (timeDependentSuspensionField X) (t - s) (s, x)) := by
    rwa [flowOf_timeDependentSuspensionField hX₁
      ((timeDependentFlowDomain_eq_univ hc).symm ▸ mem_univ _)]
  have h := ((compContinuousLinearMapCLM (ι := Fin k) (F := F) L).hasFDerivAt.comp_hasDerivAt
    (t - s) (hasDerivAt_mpullback_flowOf hZ (hc.mem_flowDomain _ _) hαΨ)).comp_sub_const t s
  exact (h.congr_of_eventuallyEq (Eventually.of_forall fun u ↦ hkey α u)).congr_deriv
    (hkey _ t).symm

/-- **The time-dependent pullback differentiation identity.** Let `X` be a jointly `C²`
time-dependent vector field with complete suspension and time-dependent flow `φ`, and let `α` be
a form on `ℝ × M`, `C¹` at `(t, φ_{s,t} x)`, with slices `α_u = ι_u^* α`. Then the pullbacks
`(φ_{s,u}^* α_u)ₓ` have velocity `(φ_{s,t}^* (ι_t^* L_{∂_t} α + L_{X_t} α_t))ₓ` at time `t`: the
time derivative of the family plus the Lie derivative along the field at the current time. -/
theorem hasDerivAt_mpullback_timeDependentFlowOf_mpullback_prodMk (s t : ℝ) (x : M)
    (hα : ContMDiffAt (𝓘(ℝ, ℝ).prod I) ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, (ℝ × E) [⋀^Fin k]→L[ℝ] F)) 1
      (fun p ↦ TotalSpace.mk' ((ℝ × E) [⋀^Fin k]→L[ℝ] F) p (α p))
      (t, timeDependentFlowOf X s t x)) :
    HasDerivAt (F := E [⋀^Fin k]→L[ℝ] F)
      (fun u ↦ mpullback I I (timeDependentFlowOf X s u)
        (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk u) α) x)
      (mpullback I I (timeDependentFlowOf X s t)
        (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t)
            (mlieDerivForm (fun _ ↦ ((1 : ℝ), (0 : E))) α) +
          mlieDerivForm (X t) (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t) α)) x) t := by
  refine (hasDerivAt_mpullback_timeDependentFlowOf_mpullback_prodMk_suspension hX hc s t x
    (hα.mdifferentiableAt one_ne_zero)).congr_deriv ?_
  -- Both pullbacks at `x` only read their forms at `φ_{s,t} x`, where the splitting holds.
  exact (mpullback_apply_eq_compContinuousLinearMapCLM _ _ x).trans
    ((congrArg _ (mpullback_prodMk_mlieDerivForm_timeDependentSuspensionField hX t _ hα)).trans
      (mpullback_apply_eq_compContinuousLinearMapCLM (timeDependentFlowOf X s t)
        (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t)
            (mlieDerivForm (fun _ ↦ ((1 : ℝ), (0 : E))) α) +
          mlieDerivForm (X t) (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t) α)) x).symm)

/-- **Moser's principle for families of forms.** Let `X` be a jointly `C²` time-dependent vector
field with complete suspension and time-dependent flow `φ`, and let `α` be a `C¹` form on `ℝ × M`
with slices `α_t = ι_t^* α`. If the rate `ι_t^* L_{∂_t} α + L_{X_t} α_t` is `g_t • α_t` for a
continuous function `g` on `ℝ × M`, then the flow rescales the slices:
`(φ_{s,t}^* α_t)ₓ = exp (∫ₛᵗ g (u, φ_{s,u} x) du) • (α_s)ₓ`. -/
theorem mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_exp_integral_smul
    {g : ℝ × M → ℝ} (hg : Continuous g)
    (hα : ContMDiff (𝓘(ℝ, ℝ).prod I) ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, (ℝ × E) [⋀^Fin k]→L[ℝ] F)) 1
      (fun p ↦ TotalSpace.mk' ((ℝ × E) [⋀^Fin k]→L[ℝ] F) p (α p)))
    (hL : ∀ t, mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t)
          (mlieDerivForm (fun _ ↦ ((1 : ℝ), (0 : E))) α) +
        mlieDerivForm (X t) (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t) α) =
      fun y ↦ g (t, y) • mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t) α y)
    (s t : ℝ) (x : M) :
    mpullback I I (timeDependentFlowOf X s t) (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t) α) x =
      Real.exp (∫ u in s..t, g (u, timeDependentFlowOf X s u x)) •
        mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk s) α x := by
  have hX₁ := hX.of_le (m := 1) one_le_two
  -- The pullbacks at `x`, as alternating maps on the model space.
  set P : ℝ → E [⋀^Fin k]→L[ℝ] F := fun u ↦
    mpullback I I (timeDependentFlowOf X s u) (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk u) α) x
  have hcont : Continuous fun τ ↦ g (τ, timeDependentFlowOf X s τ x) :=
    hg.comp (continuous_id.prodMk ((contMDiff_timeDependentFlowOf hc (n := 2) (by norm_num)
      hX).continuous.comp (by fun_prop : Continuous fun τ : ℝ ↦ ((s, τ), x))))
  have hP (u : ℝ) (_ : u ∈ univ) : HasDerivAt P (g (u, timeDependentFlowOf X s u x) • P u) u := by
    have h := hasDerivAt_mpullback_timeDependentFlowOf_mpullback_prodMk hX hc s u x
      hα.contMDiffAt
    rwa [hL u, mpullback_fun_smul] at h
  have hP0 : P s = mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk s) α x := by
    have h : timeDependentFlowOf X s s = id := funext (timeDependentFlowOf_self hX₁ s)
    exact (congrArg (fun f ↦ mpullback I I f (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk s) α) x)
      h).trans (congrFun (mpullback_id _) x)
  rw [← hP0]
  exact eq_exp_integral_smul_of_hasDerivAt_smul (V := E [⋀^Fin k]→L[ℝ] F) isOpen_univ
    ordConnected_univ hcont.continuousOn hP (mem_univ s) (mem_univ t)

/-- **Moser's principle for families of forms**, invariance case. Let `X` be a jointly `C²`
time-dependent vector field with complete suspension and time-dependent flow `φ`, and let `α` be
a `C¹` form on `ℝ × M` with slices `α_t = ι_t^* α`. If `ι_t^* L_{∂_t} α + L_{X_t} α_t = 0` for
every time `t`, then `φ_{s,t}^* α_t = α_s` for all times `s` and `t`. -/
theorem mpullback_timeDependentFlowOf_mpullback_prodMk_eq
    (hα : ContMDiff (𝓘(ℝ, ℝ).prod I) ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, (ℝ × E) [⋀^Fin k]→L[ℝ] F)) 1
      (fun p ↦ TotalSpace.mk' ((ℝ × E) [⋀^Fin k]→L[ℝ] F) p (α p)))
    (hL : ∀ t, mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t)
          (mlieDerivForm (fun _ ↦ ((1 : ℝ), (0 : E))) α) +
        mlieDerivForm (X t) (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t) α) = 0)
    (s t : ℝ) :
    mpullback I I (timeDependentFlowOf X s t) (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t) α) =
      mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk s) α := by
  funext x
  have h := mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_exp_integral_smul hX hc
    (g := 0) continuous_const hα (fun t ↦ by rw [hL t]; funext y; simp) s t x
  simpa using h

end TauCeti
