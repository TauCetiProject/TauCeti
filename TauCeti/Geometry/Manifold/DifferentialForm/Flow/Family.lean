/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Flow.TimeDependent
import TauCeti.Analysis.ODE.ScalarLinear
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth

/-!
# Time-dependent families of forms along time-dependent flows

A time-dependent family of differential forms on a manifold `M` is represented by a single form
`α` on `ℝ × M`. Its *slice* at time `t` is the form `α_t = ι_t^* α` on `M`, pulled back along the
inclusion `ι_t : y ↦ (t, y)`, and its *time derivative* at time `t` is the slice
`ι_t^* (L_{∂_t} α)` of the Lie derivative along the unit vector field `∂_t` of the time coordinate.
This is the velocity of the slices: `d/dt (α_t)_y = (ι_t^* L_{∂_t} α)_y`
(`TauCeti.hasDerivAt_mpullback_prodMk`). For a smooth form, `L_{∂_t} α` is again a smooth form,
the time derivative `TauCeti.SmoothForm.timeDeriv`. Slices and time derivatives commute with
pullback along `id × f` for a smooth map `f`
(`TauCeti.SmoothForm.mpullback_prodMk_mpullback_prodMap`,
`TauCeti.SmoothForm.mpullback_prodMk_timeDeriv_mpullback_prodMap`).

Let `X` be a jointly `C²` time-dependent vector field on a finite-dimensional manifold without
boundary, with suspension `Z = (1, X)` on `ℝ × M`, and let `φ_{s,t}` be its time-dependent flow
(`TauCeti.timeDependentFlowOf`). The main result is the time-dependent pullback differentiation
identity

`d/dt (φ_{s,t}^* α_t)ₓ = (φ_{s,t}^* (ι_t^* L_{∂_t} α + L_{X_t} α_t))ₓ`

at every time `t` at which the flow from `(s, x)` is defined
(`TauCeti.hasDerivAt_mpullback_timeDependentFlowOf_mpullback_prodMk`). It extends
`TauCeti.hasDerivAt_mpullback_timeDependentFlowOf`, where the form does not depend on time. The
proof reads the family through the flow `Ψ` of the suspension: near `(s, x)`,
`Ψ_r (s, y) = (s + r, φ_{s,s+r} y)`, so `φ_{s,t}^* α_t = ι_s^* (Ψ_{t-s}^* α)` at `x`, whose
velocity is `ι_s^* Ψ_{t-s}^* L_Z α` by the autonomous identity
`TauCeti.hasDerivAt_mpullback_flowOf`. The slices of `L_Z α` split as

`ι_t^* L_Z α = ι_t^* L_{∂_t} α + L_{X_t} α_t`

(`TauCeti.mpullback_prodMk_mlieDerivForm_timeDependentSuspensionField`), because the Lie derivative
is additive in the vector field and the slices of the Lie derivative along the vertical field
`(0, X)` are the Lie derivatives of the slices along `X_t`
(`TauCeti.mpullback_prodMk_mlieDerivForm_vertical`).

Integrating the identity gives **Moser's principle** for families of forms: if the rate
`ι_t^* L_{∂_t} α + L_{X_t} α_t` is `g_t • α_t` for a continuous function `g`, then
`(φ_{s,t}^* α_t)ₓ = exp (∫ₛᵗ g (u, φ_{s,u} x) du) • (α_s)ₓ` whenever the flow from `(s, x)` is
defined up to time `t`; it suffices that the rate has this form, and `g` is continuous, at the
times of an interval containing `s` and `t`
(`TauCeti.mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_exp_integral_smul_of_mem`), and
for all `s`, `t` and `x` when the suspension is complete
(`TauCeti.mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_exp_integral_smul`). The rate
only has to be a multiple of the form along the trajectory of `x`, with a coefficient continuous in
time there
(`mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_exp_integral_smul_of_forall_mem_uIcc`);
this is how the rescaling is computed with a family of forms which is only defined, or only has the
required shape, near the trajectory. The case
`g = 0` is the invariance `φ_{s,t}^* α_t = α_s` of Moser's argument for symplectic forms, again
along the domain of the flow
(`TauCeti.mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_of_mem`) and everywhere for a
complete suspension (`TauCeti.mpullback_timeDependentFlowOf_mpullback_prodMk_eq`). A nonzero
`g` is the shape of the rate in Gray's argument for a family of contact forms, where the
time-dependent field is chosen to make the rate a multiple of the contact form. The invariance
also holds pointwise: it only needs the rate to vanish along the trajectory of the point, where
the flow is defined
(`TauCeti.mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_of_forall_mem_uIcc_of_mem`) or
for a complete suspension
(`TauCeti.mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_of_forall_mem_uIcc`). This is
how Moser's argument runs with a field cut off away from a region of interest.

## Main results

* `TauCeti.hasDerivAt_mpullback_prodMk`: the slices of `α` have velocity `ι_t^* L_{∂_t} α`.
* `TauCeti.SmoothForm.timeDeriv`, `TauCeti.SmoothForm.hasDerivAt_mpullback_prodMk_timeDeriv`: the
  same velocity for a smooth form, as a smooth form on `ℝ × M`.
* `TauCeti.SmoothForm.mpullback_prodMk_timeDeriv_mpullback_prodMap`: the time derivative of the
  pullback of a family along `id × f` is the pullback of its time derivative.
* `TauCeti.SmoothForm.mpullback_prodMk_mpullback_prodMap_id`: the slices of `(g × id)^* β` are
  `ι_u^* (g × id)^* β = ι_{g u}^* β`.
* `TauCeti.hasDerivAt_mpullback_prodMk_comp`: the same velocity for a form on `J × M`, for an open
  set `J` of times, with the slices read through a map `g : ℝ → J` which is the identity near the
  time considered.
* `TauCeti.mpullback_prodMk_mlieDerivForm_mpullback_prodMap`: the form `(g × id)^* β` on `ℝ × M`
  has the time derivative of `β` at the times near which `g` is the identity, so families over an
  open set of times can be read as families on `ℝ × M` there.
* `TauCeti.mpullback_prodMk_mlieDerivForm_vertical`: `ι_t^* L_{(0, X)} α = L_{X_t} α_t`.
* `TauCeti.mpullback_prodMk_mlieDerivForm_timeDependentSuspensionField`:
  `ι_t^* L_Z α = ι_t^* L_{∂_t} α + L_{X_t} α_t`.
* `TauCeti.hasDerivAt_mpullback_timeDependentFlowOf_mpullback_prodMk`: the time derivative of
  `φ_{s,t}^* α_t` is `φ_{s,t}^* (ι_t^* L_{∂_t} α + L_{X_t} α_t)`.
* `TauCeti.mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_exp_integral_smul_of_mem`: if
  the rate is `g_t • α_t` at the times of an interval containing `s` and `t`, the flow rescales the
  slices by `exp (∫ₛᵗ g (u, φ_{s,u} x) du)` where it is defined.
* `TauCeti.mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_exp_integral_smul`: the same
  everywhere, for a complete suspension.
* `mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_exp_integral_smul_of_forall_mem_uIcc`:
  the rescaling when the rate is a multiple of the form only along the trajectory of `x`.
* `TauCeti.mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_of_mem`: if the rate vanishes,
  then `(φ_{s,t}^* α_t)ₓ = (α_s)ₓ` where the flow is defined.
* `TauCeti.mpullback_timeDependentFlowOf_mpullback_prodMk_eq`: for a complete suspension, if the
  rate vanishes, then `φ_{s,t}^* α_t = α_s`.
* `TauCeti.mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_of_forall_mem_uIcc_of_mem`: if
  the rate vanishes along the trajectory of `x` between times `s` and `t`, then
  `(φ_{s,t}^* α_t)ₓ = (α_s)ₓ` where the flow is defined.
* `TauCeti.mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_of_forall_mem_uIcc`: the same
  for a complete suspension.

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
  refine hasDerivAt_mpullback_of_eq_comp (χ := fun u p ↦ (p.1 + (u - t), p.2))
    (Eventually.of_forall fun u ↦ EventuallyEq.of_eq (funext fun y ↦ by simp))
    ((contMDiff_const.prodMk contMDiff_id : ContMDiff I (𝓘(ℝ, ℝ).prod I) 1
      (Prod.mk t : M → ℝ × M)).mdifferentiableAt one_ne_zero)
    (Eventually.of_forall fun u ↦ ((contMDiff_fst.add contMDiff_const).prodMk contMDiff_snd :
      ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) 2
        (fun p : ℝ × M ↦ (p.1 + (u - t), p.2))).mdifferentiableAt (by norm_num))
    (HasDerivAt.comp_sub_const (x := t) (a := t) (by rwa [sub_self]))

/-! ### Families over an open set of times -/

section Opens

variable {J : TopologicalSpace.Opens ℝ}

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] in
/-- The slices of the pullback of a family over `J` along `g × id`, for a map `g : ℝ → J`, are
the slices at the times `g u`: `ι_u^* (g × id)^* β = ι_{g u}^* β`. -/
theorem SmoothForm.mpullback_prodMk_mpullback_prodMap_id
    (β : SmoothForm (𝓘(ℝ, ℝ).prod I) (J × M) F k) {g : ℝ → J}
    (hg : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ g) (u : ℝ) :
    SmoothForm.mpullback (Prod.mk u) (contMDiff_const.prodMk contMDiff_id)
        (SmoothForm.mpullback (Prod.map g id) (hg.prodMap contMDiff_id) β) =
      SmoothForm.mpullback (Prod.mk (g u)) (contMDiff_const.prodMk contMDiff_id) β := by
  have hcomp : Prod.map g id ∘ Prod.mk u = (Prod.mk (g u) : M → J × M) := by
    funext y
    simp
  rw [SmoothForm.mpullback_mpullback]
  simp only [hcomp]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] [IsManifold I 2 M] in
/-- A `C²` map `g : ℝ → J` which is the identity near `a`, translated to start at `a` and paired
with a constant point of `M`, moves with the velocity `∂_t = (1, 0)` at time `0`. -/
private theorem hasMFDerivAt_prodMk_comp_add {g : ℝ → J} (hg : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 2 g)
    {a : ℝ} (ha : (fun v ↦ (g v : ℝ)) =ᶠ[𝓝 a] id) (y : M) :
    HasMFDerivAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) (fun r ↦ (g (a + r), y)) 0
      ((1 : ℝ →L[ℝ] ℝ).smulRight (((1 : ℝ), (0 : E)) : ℝ × E)) := by
  set h : ℝ → J := fun r ↦ g (a + r)
  have hhs : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 2 h := hg.comp (contMDiff_const.add contMDiff_id)
  -- Near `0`, `h` reads `r ↦ a + r` in `ℝ`, so its differential is the identity.
  have hhd (v : ℝ) : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) h 0 v = v := by
    rw [← TauCeti.Manifold.mfderiv_subtype_val_comp_apply (U := J) (f := h) v,
      mfderiv_eq_fderiv]
    have heq : (Subtype.val ∘ h) =ᶠ[𝓝 0] fun r ↦ a + r := by
      have ht : Tendsto (fun r : ℝ ↦ a + r) (𝓝 0) (𝓝 a) := by
        simpa using (tendsto_const_nhds (x := a)).add (tendsto_id (x := 𝓝 (0 : ℝ)))
      filter_upwards [ht.eventually ha] with r hr
      exact hr
    rw [heq.fderiv_eq, fderiv_const_add, fderiv_fun_id]
    -- `mfderiv_eq_fderiv` reads the tangent spaces as `ℝ` through
    -- `NormedSpace.fromTangentSpace`, which is the identity by definition and has no simp lemmas.
    rfl
  refine ((hhs.mdifferentiableAt (by norm_num)).hasMFDerivAt.prodMk
    (hasMFDerivAt_const y (0 : ℝ))).congr_mfderiv (ContinuousLinearMap.ext fun (r : ℝ) ↦ ?_)
  -- The velocity `∂_t = (1, 0)` is computed in `ℝ × E`, the tangent space of `ℝ × M` read in the
  -- model.
  have hv : ((1 : ℝ →L[ℝ] ℝ).smulRight (((1 : ℝ), (0 : E)) : ℝ × E)) r = (r, 0) := by simp
  exact Eq.trans (b := ((r, 0) : ℝ × E)) (Prod.ext (hhd r) rfl) hv.symm

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- **Time derivatives of slices over an open set of times.** Let `β` be a form on `J × M`, for an
open set `J` of times, representing the family of its slices `β_t = ι_t^* β`, `t ∈ J`. Read the
slices through a `C²` map `g : ℝ → J` which is the identity near `u`. If `β` is differentiable at
`(g u, x)`, then `v ↦ (β_{g v})ₓ` has velocity `ι_{g u}^* (L_{∂_t} β)` at `x` at time `u`, where
`∂_t = (1, 0)` is the unit vector field of the time coordinate. This is
`TauCeti.hasDerivAt_mpullback_prodMk` for families which are only defined at the times of `J`. -/
theorem hasDerivAt_mpullback_prodMk_comp {β : RoughForm (𝓘(ℝ, ℝ).prod I) (J × M) F k}
    {g : ℝ → J} (hg : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 2 g) {u : ℝ}
    (hu : (fun v ↦ (g v : ℝ)) =ᶠ[𝓝 u] id) (x : M)
    (hβ : MDifferentiableAt (𝓘(ℝ, ℝ).prod I)
      ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, (ℝ × E) [⋀^Fin k]→L[ℝ] F))
      (fun p ↦ TotalSpace.mk' ((ℝ × E) [⋀^Fin k]→L[ℝ] F) p (β p)) (g u, x)) :
    HasDerivAt (F := E [⋀^Fin k]→L[ℝ] F)
      (fun v ↦ mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk (g v)) β x)
      (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk (g u))
        (mlieDerivForm (fun _ ↦ ((1 : ℝ), (0 : E))) β) x) u := by
  set p₀ : J × M := (g u, x)
  -- The maps `ψ_r (q, y) = (g (q + r), y)` of `J × M` move the points with velocity `∂_t`
  -- near `p₀`.
  set ψ : ℝ → J × M → J × M := fun r q ↦ (g ((q.1 : ℝ) + r), q.2)
  have hgu : (g u : ℝ) = u := hu.self_of_nhds
  have hnear : ∀ᶠ q in 𝓝 p₀, (fun v ↦ (g v : ℝ)) =ᶠ[𝓝 (q.1 : ℝ)] id := by
    have hc : Tendsto (fun q : J × M ↦ (q.1 : ℝ)) (𝓝 p₀) (𝓝 u) := by
      have hcont : Continuous fun q : J × M ↦ (q.1 : ℝ) :=
        continuous_subtypeVal.comp continuous_fst
      simpa [p₀, hgu] using hcont.continuousAt.tendsto (x := p₀)
    exact hc.eventually hu.eventually_nhds
  have hid : ∀ᶠ q in 𝓝 p₀, ψ 0 q = q := by
    filter_upwards [hnear] with q hq
    exact Prod.ext (Subtype.ext (by simp only [ψ, add_zero]; exact hq.self_of_nhds)) rfl
  have hψs (r : ℝ) : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) 2 (ψ r) :=
    (hg.comp ((contMDiff_subtypeVal.comp contMDiff_fst).add contMDiff_const)).prodMk
      contMDiff_snd
  have hsmooth : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod I)) (𝓘(ℝ, ℝ).prod I) 2
      (fun p : ℝ × (J × M) ↦ ψ p.1 p.2) (0, p₀) :=
    ((hg.comp ((contMDiff_subtypeVal.comp (contMDiff_fst.comp contMDiff_snd)).add
      contMDiff_fst)).prodMk (contMDiff_snd.comp contMDiff_snd)).contMDiffAt
  have hvel : ∀ᶠ q in 𝓝 p₀, HasMFDerivAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) (fun r ↦ ψ r q) 0
      ((1 : ℝ →L[ℝ] ℝ).smulRight (((1 : ℝ), (0 : E)) : ℝ × E)) := by
    filter_upwards [hnear] with q hq
    exact hasMFDerivAt_prodMk_comp_add hg hq q.2
  have hτ := hasDerivAt_mpullback_of_eq_id (I := 𝓘(ℝ, ℝ).prod I) (ψ := ψ)
    (V := fun _ ↦ ((1 : ℝ), (0 : E))) (t := 0) p₀ hid hsmooth hvel hβ
  -- Since `ι_{g v} = ψ_{v - u} ∘ ι_{g u}`, the slice at time `g v` is `ι_{g u}^* ψ_{v - u}^* β`.
  refine hasDerivAt_mpullback_of_eq_comp (χ := fun v ↦ ψ (v - u))
    (Eventually.of_forall fun v ↦ EventuallyEq.of_eq (funext fun y ↦ by simp [ψ, hgu]))
    ((contMDiff_const.prodMk contMDiff_id : ContMDiff I (𝓘(ℝ, ℝ).prod I) 1
      (Prod.mk (g u) : M → J × M)).mdifferentiableAt one_ne_zero)
    (Eventually.of_forall fun v ↦ (hψs (v - u)).mdifferentiableAt (by norm_num))
    (HasDerivAt.comp_sub_const (x := u) (a := u) (by rwa [sub_self]))

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- **Reading a family over an open set of times through a map of `ℝ`.** For a smooth map
`g : ℝ → J` which is the identity near `u`, the smooth form `(g × id)^* β` on `ℝ × M` represents
the family of slices `β_{g t}`, and its time derivative at time `u` is that of `β` at `g u`:
`ι_u^* L_{∂_t} ((g × id)^* β) = ι_{g u}^* L_{∂_t} β`. This transfers statements about families on
`ℝ × M` to families defined only at the times of `J`, near the times where `g` is the identity. -/
theorem mpullback_prodMk_mlieDerivForm_mpullback_prodMap
    (β : SmoothForm (𝓘(ℝ, ℝ).prod I) (J × M) F k) {g : ℝ → J}
    (hg : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ g) {u : ℝ} (hu : (fun v ↦ (g v : ℝ)) =ᶠ[𝓝 u] id) :
    mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk u) (mlieDerivForm (fun _ ↦ ((1 : ℝ), (0 : E)))
        (SmoothForm.mpullback (Prod.map g id) (hg.prodMap contMDiff_id) β).val) =
      mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk (g u))
        (mlieDerivForm (fun _ ↦ ((1 : ℝ), (0 : E))) β.val) := by
  funext x
  refine (hasDerivAt_mpullback_prodMk u x
    ((SmoothForm.mpullback _ (hg.prodMap contMDiff_id) β).mdifferentiableAt (u, x))).unique ?_
  refine (hasDerivAt_mpullback_prodMk_comp (hg.of_le (by simp)) hu x
    (β.mdifferentiableAt _)).congr_of_eventuallyEq (Eventually.of_forall fun v ↦ ?_)
  -- The slices of `(g × id)^* β` are the slices of `β` at the times `g v`.
  have h := congrArg Subtype.val (SmoothForm.mpullback_prodMk_mpullback_prodMap_id β hg v)
  simp only [SmoothForm.coe_mpullback] at h ⊢
  exact congrFun h x

end Opens

/-! ### The time derivative of a smooth family -/

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] in
/-- The **time derivative** `∂_t α` of a smooth form `α` on `ℝ × M`, which represents the
time-dependent family of its slices `α_t = ι_t^* α`: the Lie derivative `L_{∂_t} α` along the unit
vector field `∂_t = (1, 0)` of the time coordinate. It is again a smooth form, and its slices are
the velocities of the slices of `α` (`TauCeti.SmoothForm.hasDerivAt_mpullback_prodMk_timeDeriv`). -/
def SmoothForm.timeDeriv (α : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) F k) :
    SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) F k :=
  ⟨mlieDerivForm (fun _ ↦ ((1 : ℝ), (0 : E))) α.val, SmoothForm.mlieDerivForm_mem_smoothBundleForms
      α
    (contMDiff_const_prod_field 1 (X := 0)
      ((contMDiff_zeroSection ℝ (TangentSpace I)).comp contMDiff_snd))⟩

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] in
/-- The underlying form of the time derivative is the Lie derivative along `∂_t`. -/
@[simp]
theorem SmoothForm.coe_timeDeriv (α : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) F k) :
    α.timeDeriv.val = mlieDerivForm (fun _ ↦ ((1 : ℝ), (0 : E))) α.val :=
  (rfl)

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- The slices of the time derivative are the velocities of the slices:
`d/dt (α_t)ₓ = ((∂_t α)_t)ₓ`. -/
theorem SmoothForm.hasDerivAt_mpullback_prodMk_timeDeriv
    (α : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) F k) (t : ℝ) (x : M) :
    HasDerivAt (F := E [⋀^Fin k]→L[ℝ] F)
      (fun u ↦ (SmoothForm.mpullback (Prod.mk u) (contMDiff_const.prodMk contMDiff_id) α).val x)
      ((SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α.timeDeriv).val x)
      t := by
  simpa only [SmoothForm.coe_mpullback, SmoothForm.coe_timeDeriv] using
    hasDerivAt_mpullback_prodMk t x (α.mdifferentiableAt (t, x))

section Pullback

variable {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless] [TopologicalSpace M'] [ChartedSpace H' M']
  [IsManifold I' 2 M']

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] [I'.Boundaryless] in
/-- The slices of the pullback of a family of forms along `id × f` are the pullbacks along `f` of
the slices: `ι_t^* (id × f)^* α = f^* ι_t^* α`. -/
theorem SmoothForm.mpullback_prodMk_mpullback_prodMap (f : M → M') (hf : ContMDiff I I' ∞ f)
    (α : SmoothForm (𝓘(ℝ, ℝ).prod I') (ℝ × M') F k) (t : ℝ) :
    SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id)
        (SmoothForm.mpullback (Prod.map id f) (contMDiff_id.prodMap hf) α) =
      SmoothForm.mpullback f hf
        (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α) :=
  SmoothForm.mpullback_mpullback_of_comp_eq (contMDiff_const.prodMk contMDiff_id)
    (contMDiff_id.prodMap hf) hf (contMDiff_const.prodMk contMDiff_id) rfl α

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- **The time derivative commutes with pullback along `id × f`.** The slices of the time
derivative of `(id × f)^* α` are the pullbacks along `f` of the slices of `∂_t α`. -/
theorem SmoothForm.mpullback_prodMk_timeDeriv_mpullback_prodMap (f : M → M')
    (hf : ContMDiff I I' ∞ f) (α : SmoothForm (𝓘(ℝ, ℝ).prod I') (ℝ × M') F k) (t : ℝ) :
    SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id)
        (SmoothForm.mpullback (Prod.map id f) (contMDiff_id.prodMap hf) α).timeDeriv =
      SmoothForm.mpullback f hf
        (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α.timeDeriv) := by
  apply Subtype.ext
  funext x
  set L : E →L[ℝ] E' := mfderiv I I' f x
  have h₀ : HasDerivAt (F := E' [⋀^Fin k]→L[ℝ] F)
      (fun u ↦ (SmoothForm.mpullback (Prod.mk u) (contMDiff_const.prodMk contMDiff_id) α).val (f x))
      ((SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α.timeDeriv).val
        (f x)) t :=
    α.hasDerivAt_mpullback_prodMk_timeDeriv t (f x)
  have h := (SmoothForm.mpullback (Prod.map id f) (contMDiff_id.prodMap hf)
    α).hasDerivAt_mpullback_prodMk_timeDeriv t x
  -- The slices of the pullback are the slices of `α` composed with the differential of `f`.
  have hfun : (fun u ↦ (SmoothForm.mpullback (Prod.mk u) (contMDiff_const.prodMk contMDiff_id)
      (SmoothForm.mpullback (Prod.map id f) (contMDiff_id.prodMap hf) α)).val x) =
      ⇑(compContinuousLinearMapCLM (ι := Fin k) (F := F) L) ∘
        fun u ↦ (SmoothForm.mpullback (Prod.mk u) (contMDiff_const.prodMk contMDiff_id) α).val
          (f x) := by
    funext u
    rw [SmoothForm.mpullback_prodMk_mpullback_prodMap f hf, SmoothForm.coe_mpullback,
      mpullback_apply_eq_compContinuousLinearMapCLM]
    -- The sides agree by `Function.comp_apply` and `L = mfderiv f x`, up to the defeq of the
    -- tangent space at `f x` with `E'`, which blocks rewriting with `Function.comp_apply`.
    rfl
  rw [hfun] at h
  refine h.unique ?_
  rw [SmoothForm.coe_mpullback, mpullback_apply_eq_compContinuousLinearMapCLM]
  exact (compContinuousLinearMapCLM (ι := Fin k) (F := F) L).hasFDerivAt.comp_hasDerivAt t h₀

end Pullback

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
    (Eventually.of_forall fun p ↦ by simp [ψ, timeDependentFlowOf_self])
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
      mdifferentiableAt_timeDependentFlowOf hX₁ hr
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

/-- The velocity of `φ_{s,u}^* α_u` at a time `t` at which the flow from `(s, x)` is defined is
`φ_{s,t}^* ι_t^* L_Z α`, where `Z` is the suspension. Near `(s, x)` the flow of `Z` is
`Ψ_r (u, y) = (u + r, φ_{u,u+r} y)`, so for `u` near `t` the pullback `φ_{s,u}^* α_u` at `x` is
`ι_s^* Ψ_{u-s}^* α`, and the velocity of `Ψ_r^* α` is `Ψ_r^* L_Z α`. -/
private theorem hasDerivAt_mpullback_timeDependentFlowOf_mpullback_prodMk_suspension
    {s t : ℝ} {x : M} (h : ((s, t), x) ∈ timeDependentFlowDomain X)
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
  have hD := isOpen_timeDependentFlowDomain hX₁
  have hι (u : ℝ) : MDifferentiable I (𝓘(ℝ, ℝ).prod I) (Prod.mk u : M → ℝ × M) :=
    (contMDiff_const.prodMk contMDiff_id : ContMDiff I (𝓘(ℝ, ℝ).prod I) 1
      (Prod.mk u : M → ℝ × M)).mdifferentiable one_ne_zero
  set L : E →L[ℝ] ℝ × E := mfderiv I (𝓘(ℝ, ℝ).prod I) (Prod.mk s) x
  -- For `u` near `t`, the flow from `(s, x)` is still defined at time `u`.
  have hdom : ∀ᶠ u in 𝓝 t, ((s, u), x) ∈ timeDependentFlowDomain X :=
    (by fun_prop : Continuous fun u : ℝ ↦ ((s, u), x)).continuousAt.eventually_mem
      (hD.mem_nhds h)
  -- For every form `η` on `ℝ × M` and `u` near `t`, `φ_{s,u}^* η_u = ι_s^* Ψ_{u-s}^* η` at `x`.
  have hkey (η : RoughForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) F k) :
      (fun u ↦ mpullback I I (timeDependentFlowOf X s u)
          (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk u) η) x) =ᶠ[𝓝 t]
        fun u ↦ compContinuousLinearMapCLM (ι := Fin k) (F := F) L
          (mpullback (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I)
            (flowOf (timeDependentSuspensionField X) (u - s)) η (s, x)) := by
    filter_upwards [hdom] with u hu
    -- Near `x` the flow from `s` to `u` is defined, and there it is read off the flow of `Z`.
    have hcomp : Prod.mk u ∘ timeDependentFlowOf X s u =ᶠ[𝓝 x]
        flowOf (timeDependentSuspensionField X) (u - s) ∘ Prod.mk s := by
      filter_upwards [(by fun_prop : Continuous fun y : M ↦ ((s, u), y)).continuousAt.eventually_mem
        (hD.mem_nhds hu)] with y hy
      exact (flowOf_timeDependentSuspensionField hy).symm
    have hφu : MDifferentiableAt I I (timeDependentFlowOf X s u) x :=
      mdifferentiableAt_timeDependentFlowOf hX₁ hu
    have hΨu : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I)
        (flowOf (timeDependentSuspensionField X) (u - s)) (s, x) :=
      (contMDiffAt_flowOf_comp (n := 2) one_le_two hZ contMDiffAt_const contMDiffAt_id
        (mem_timeDependentFlowDomain.1 hu)).mdifferentiableAt (by norm_num)
    rw [← mpullback_comp_at hφu (hι u _), hcomp.mpullback_eq,
      mpullback_comp_at (hι s x) hΨu]
    exact mpullback_apply_eq_compContinuousLinearMapCLM _ _ x
  have hαΨ : MDifferentiableAt (𝓘(ℝ, ℝ).prod I)
      ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, (ℝ × E) [⋀^Fin k]→L[ℝ] F))
      (fun p ↦ TotalSpace.mk' ((ℝ × E) [⋀^Fin k]→L[ℝ] F) p (α p))
      (flowOf (timeDependentSuspensionField X) (t - s) (s, x)) := by
    rwa [flowOf_timeDependentSuspensionField h]
  have hd := ((compContinuousLinearMapCLM (ι := Fin k) (F := F) L).hasFDerivAt.comp_hasDerivAt
    (t - s) (hasDerivAt_mpullback_flowOf hZ (mem_timeDependentFlowDomain.1 h) hαΨ)).comp_sub_const
    t s
  exact (hd.congr_of_eventuallyEq (hkey α)).congr_deriv (hkey _).self_of_nhds.symm

/-- **The time-dependent pullback differentiation identity.** Let `X` be a jointly `C²`
time-dependent vector field with time-dependent flow `φ`, defined at `x` from time `s` to time
`t`, and let `α` be a form on `ℝ × M`, `C¹` at `(t, φ_{s,t} x)`, with slices `α_u = ι_u^* α`.
Then the pullbacks `(φ_{s,u}^* α_u)ₓ` have velocity
`(φ_{s,t}^* (ι_t^* L_{∂_t} α + L_{X_t} α_t))ₓ` at time `t`: the time derivative of the family
plus the Lie derivative along the field at the current time. -/
theorem hasDerivAt_mpullback_timeDependentFlowOf_mpullback_prodMk {s t : ℝ} {x : M}
    (h : ((s, t), x) ∈ timeDependentFlowDomain X)
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
  refine (hasDerivAt_mpullback_timeDependentFlowOf_mpullback_prodMk_suspension hX h
    (hα.mdifferentiableAt one_ne_zero)).congr_deriv ?_
  -- Both pullbacks at `x` only read their forms at `φ_{s,t} x`, where the splitting holds.
  exact (mpullback_apply_eq_compContinuousLinearMapCLM _ _ x).trans
    ((congrArg _ (mpullback_prodMk_mlieDerivForm_timeDependentSuspensionField hX t _ hα)).trans
      (mpullback_apply_eq_compContinuousLinearMapCLM (timeDependentFlowOf X s t)
        (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t)
            (mlieDerivForm (fun _ ↦ ((1 : ℝ), (0 : E))) α) +
          mlieDerivForm (X t) (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t) α)) x).symm)

/-- **Moser's principle for families of forms along a trajectory**, with a rescaling rate. Let
`X` be a jointly `C²` time-dependent vector field with time-dependent flow `φ`, defined at `x` from
time `s` to time `t`, and let `α` be a form on `ℝ × M` with slices `α_u = ι_u^* α`, which is `C¹`
along the trajectory of `x`. If, for every time `u` between `s` and `t`, the rate
`ι_u^* L_{∂_t} α + L_{X_u} α_u` at the point `φ_{s,u} x` is `g u` times `α_u` there, for a
function `g` continuous between `s` and `t`, then
`(φ_{s,t}^* α_t)ₓ = exp (∫ₛᵗ g u du) • (α_s)ₓ`. Nothing is assumed away from the trajectory of
`x`, nor at other times. -/
theorem mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_exp_integral_smul_of_forall_mem_uIcc
    {s t : ℝ} {x : M} (h : ((s, t), x) ∈ timeDependentFlowDomain X) {g : ℝ → ℝ}
    (hg : ContinuousOn g (uIcc s t))
    (hα : ∀ u ∈ uIcc s t, ContMDiffAt (𝓘(ℝ, ℝ).prod I)
      ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, (ℝ × E) [⋀^Fin k]→L[ℝ] F)) 1
      (fun p ↦ TotalSpace.mk' ((ℝ × E) [⋀^Fin k]→L[ℝ] F) p (α p))
      (u, timeDependentFlowOf X s u x))
    (hL : ∀ u ∈ uIcc s t, (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk u)
          (mlieDerivForm (fun _ ↦ ((1 : ℝ), (0 : E))) α) +
        mlieDerivForm (X u) (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk u) α))
          (timeDependentFlowOf X s u x) =
        g u • mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk u) α (timeDependentFlowOf X s u x)) :
    mpullback I I (timeDependentFlowOf X s t) (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t) α) x =
      Real.exp (∫ u in s..t, g u) • mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk s) α x := by
  -- The flow from `(s, x)` is defined at all times between `s` and `t`.
  have hJ := uIcc_subset_setOf_mem_timeDependentFlowDomain h
  -- The pullbacks at `x`, as alternating maps on the model space.
  set P : ℝ → E [⋀^Fin k]→L[ℝ] F := fun u ↦
    mpullback I I (timeDependentFlowOf X s u) (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk u) α) x
  have hP (u : ℝ) (hu : u ∈ uIcc s t) : HasDerivWithinAt P (g u • P u) (uIcc s t) u := by
    refine ((hasDerivAt_mpullback_timeDependentFlowOf_mpullback_prodMk hX (hJ hu)
      (hα u hu)).congr_deriv ?_).hasDerivWithinAt
    rw [mpullback_apply_eq_compContinuousLinearMapCLM, hL u hu, _root_.map_smul,
      ← mpullback_apply_eq_compContinuousLinearMapCLM]
    -- The remaining pullback is `P u`, by the definition of `P`.
    rfl
  have hP0 : P s = mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk s) α x := by
    have h : timeDependentFlowOf X s s = id := funext (timeDependentFlowOf_self X s)
    exact (congrArg (fun f ↦ mpullback I I f (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk s) α) x)
      h).trans (congrFun (mpullback_id _) x)
  rw [← hP0]
  exact eq_exp_integral_smul_of_hasDerivWithinAt_smul (V := E [⋀^Fin k]→L[ℝ] F) ordConnected_uIcc
    hg hP left_mem_uIcc right_mem_uIcc

/-- **Moser's principle for families of forms**, along the domain of the flow, on an interval of
times. Let `X` be a jointly `C²` time-dependent vector field with time-dependent flow `φ`,
defined at `x` from time `s` to time `t`, and let `α` be a `C¹` form on `ℝ × M` with slices
`α_u = ι_u^* α`. Let `T` be an interval of times containing `s` and `t`. If the rate
`ι_u^* L_{∂_t} α + L_{X_u} α_u` is `g_u • α_u` at every time `u ∈ T`, for a function `g` on
`ℝ × M` continuous on `T × M`, then the flow rescales the slices:
`(φ_{s,t}^* α_t)ₓ = exp (∫ₛᵗ g (u, φ_{s,u} x) du) • (α_s)ₓ`. Nothing is assumed at times outside
`T`. -/
theorem mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_exp_integral_smul_of_mem
    {T : Set ℝ} (hT : T.OrdConnected) {g : ℝ × M → ℝ} (hg : ContinuousOn g (T ×ˢ univ))
    (hα : ContMDiff (𝓘(ℝ, ℝ).prod I) ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, (ℝ × E) [⋀^Fin k]→L[ℝ] F)) 1
      (fun p ↦ TotalSpace.mk' ((ℝ × E) [⋀^Fin k]→L[ℝ] F) p (α p)))
    (hL : ∀ t ∈ T, mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t)
          (mlieDerivForm (fun _ ↦ ((1 : ℝ), (0 : E))) α) +
        mlieDerivForm (X t) (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t) α) =
      fun y ↦ g (t, y) • mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t) α y)
    {s t : ℝ} {x : M} (hs : s ∈ T) (ht : t ∈ T) (h : ((s, t), x) ∈ timeDependentFlowDomain X) :
    mpullback I I (timeDependentFlowOf X s t) (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t) α) x =
      Real.exp (∫ u in s..t, g (u, timeDependentFlowOf X s u x)) •
        mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk s) α x := by
  have hJ := uIcc_subset_setOf_mem_timeDependentFlowDomain h
  have hsub := hT.uIcc_subset hs ht
  refine
    mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_exp_integral_smul_of_forall_mem_uIcc
      hX h ?_ (fun _ _ ↦ hα.contMDiffAt) fun u hu ↦ by rw [hL u (hsub hu)]
  exact hg.comp (continuousOn_id.prodMk
    ((contMDiffOn_timeDependentFlowOf (n := 2) (by norm_num) hX).continuousOn.comp
      (by fun_prop : Continuous fun τ : ℝ ↦ ((s, τ), x)).continuousOn fun _ hτ ↦ hJ hτ))
    fun _ hτ ↦ ⟨hsub hτ, mem_univ _⟩

/-- **Moser's principle along a trajectory**, along the domain of the flow. Let `X` be a jointly
`C²` time-dependent vector field with time-dependent flow `φ`, defined at `x` from time `s` to time
`t`, and let `α` be a form on `ℝ × M` with slices `α_u = ι_u^* α`, which is `C¹` along the
trajectory of `x`. If the rate `ι_u^* L_{∂_t} α + L_{X_u} α_u` vanishes at the point `φ_{s,u} x`
for every time `u` between `s` and `t`, then `(φ_{s,t}^* α_t)ₓ = (α_s)ₓ`. Nothing is assumed away
from the trajectory of `x`. -/
theorem mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_of_forall_mem_uIcc_of_mem
    {s t : ℝ} {x : M} (h : ((s, t), x) ∈ timeDependentFlowDomain X)
    (hα : ∀ u ∈ uIcc s t, ContMDiffAt (𝓘(ℝ, ℝ).prod I)
      ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, (ℝ × E) [⋀^Fin k]→L[ℝ] F)) 1
      (fun p ↦ TotalSpace.mk' ((ℝ × E) [⋀^Fin k]→L[ℝ] F) p (α p))
      (u, timeDependentFlowOf X s u x))
    (hL : ∀ u ∈ uIcc s t, (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk u)
          (mlieDerivForm (fun _ ↦ ((1 : ℝ), (0 : E))) α) +
        mlieDerivForm (X u) (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk u) α))
          (timeDependentFlowOf X s u x) = 0) :
    mpullback I I (timeDependentFlowOf X s t) (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t) α) x =
      mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk s) α x := by
  simpa using
    mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_exp_integral_smul_of_forall_mem_uIcc
      hX h (g := 0) continuousOn_const hα fun u hu ↦ by rw [hL u hu, Pi.zero_apply, zero_smul]

/-- **Moser's principle for families of forms**, invariance case along the domain of the flow.
Let `X` be a jointly `C²` time-dependent vector field with time-dependent flow `φ`, defined at `x`
from time `s` to time `t`, and let `α` be a `C¹` form on `ℝ × M` with slices `α_t = ι_t^* α`. If
`ι_t^* L_{∂_t} α + L_{X_t} α_t = 0` for every time `t`, then `(φ_{s,t}^* α_t)ₓ = (α_s)ₓ`. -/
theorem mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_of_mem
    (hα : ContMDiff (𝓘(ℝ, ℝ).prod I) ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, (ℝ × E) [⋀^Fin k]→L[ℝ] F)) 1
      (fun p ↦ TotalSpace.mk' ((ℝ × E) [⋀^Fin k]→L[ℝ] F) p (α p)))
    (hL : ∀ t, mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t)
          (mlieDerivForm (fun _ ↦ ((1 : ℝ), (0 : E))) α) +
        mlieDerivForm (X t) (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t) α) = 0)
    {s t : ℝ} {x : M} (h : ((s, t), x) ∈ timeDependentFlowDomain X) :
    mpullback I I (timeDependentFlowOf X s t) (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t) α) x =
      mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk s) α x :=
  mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_of_forall_mem_uIcc_of_mem hX h
    (fun _ _ ↦ hα.contMDiffAt) fun u _ ↦ by rw [hL u, Pi.zero_apply]

variable (hc : IsCompleteVectorField (timeDependentSuspensionField X))
include hc

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
        mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk s) α x :=
  mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_exp_integral_smul_of_mem hX
    ordConnected_univ hg.continuousOn hα (fun t _ ↦ hL t) (mem_univ s) (mem_univ t)
    ((timeDependentFlowDomain_eq_univ hc).symm ▸ mem_univ _)

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
  exact mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_of_mem hX hα hL
    ((timeDependentFlowDomain_eq_univ hc).symm ▸ mem_univ _)

/-- **Moser's principle along a trajectory**, for a complete suspension. Let `X` be a jointly
`C²` time-dependent vector field with complete suspension and time-dependent flow `φ`, and let `α`
be a form on `ℝ × M` with slices `α_u = ι_u^* α`, which is `C¹` along the trajectory of `x`. If the
rate `ι_u^* L_{∂_t} α + L_{X_u} α_u` vanishes at the point `φ_{s,u} x` for every time `u` between
`s` and `t`, then `(φ_{s,t}^* α_t)ₓ = (α_s)ₓ`. -/
theorem mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_of_forall_mem_uIcc
    {s t : ℝ} {x : M}
    (hα : ∀ u ∈ uIcc s t, ContMDiffAt (𝓘(ℝ, ℝ).prod I)
      ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, (ℝ × E) [⋀^Fin k]→L[ℝ] F)) 1
      (fun p ↦ TotalSpace.mk' ((ℝ × E) [⋀^Fin k]→L[ℝ] F) p (α p))
      (u, timeDependentFlowOf X s u x))
    (hL : ∀ u ∈ uIcc s t, (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk u)
          (mlieDerivForm (fun _ ↦ ((1 : ℝ), (0 : E))) α) +
        mlieDerivForm (X u) (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk u) α))
          (timeDependentFlowOf X s u x) = 0) :
    mpullback I I (timeDependentFlowOf X s t) (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t) α) x =
      mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk s) α x :=
  mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_of_forall_mem_uIcc_of_mem hX
    ((timeDependentFlowDomain_eq_univ hc).symm ▸ mem_univ _) hα hL

end TauCeti
