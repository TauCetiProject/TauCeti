/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Flow
public import TauCeti.Geometry.Manifold.Flow.TimeDependent

/-!
# Lie derivatives of differential forms along time-dependent flows

Let `X` be a jointly `C²` time-dependent vector field on a finite-dimensional manifold without
boundary, and let `φ_{s,t}` be its time-dependent flow from time `s` to time `t`
(`TauCeti.timeDependentFlowOf`), a maximal flow defined on an open domain
(`TauCeti.timeDependentFlowDomain`). For a differential form `α`, the pullbacks `φ_{s,t}^* α` at a
point `x` form a curve in the alternating maps on `T_x M`, and wherever the flow from `(s, x)` is
defined its velocity is the pullback of the Lie derivative along the field at the current time:

`d/dt (φ_{s,t}^* α)ₓ = (φ_{s,t}^* L_{X_t} α)ₓ`

(`TauCeti.hasDerivAt_mpullback_timeDependentFlowOf_of_mem`). This is the time-dependent
counterpart of `TauCeti.hasDerivAt_mpullback_flowOf`. The Lie derivative `L_{X_t} α` is
`TauCeti.mlieDerivForm (X t) α`, defined in charts with no reference to flows.

At the base time itself, the flow `u ↦ φ_{t,u}` is a jointly `C²` family of maps which is the
identity at time `t` and moves with velocity `X t` there, so
`d/du|_{u = t} (φ_{t,u}^* α) = L_{X_t} α` is an instance of
`TauCeti.hasDerivAt_mpullback_of_eq_id`. The two-time composition law `φ_{s,u} = φ_{t,u} ∘ φ_{s,t}`,
valid near `x` for `u` near `t` because the domain is open, moves this to an arbitrary base time
`s`.

Integrating the identity: if `β` is closed and every contraction `ι_{X_u} β` is closed for the
times `u` between `s` and `t`, then `(φ_{s,t}^* β)ₓ = βₓ` wherever the flow from `(s, x)` is defined
up to time `t` (`TauCeti.mpullback_timeDependentFlowOf_apply_of_mextDeriv_interior_eq_zero`), since
Cartan's formula gives `L_{X_u} β = d(ι_{X_u} β) = 0`. No completeness is needed. For a symplectic
form `ω`, this says that the flow of a time-dependent symplectic vector field consists of
symplectomorphisms wherever it is defined; this is the input to the flux of a symplectic isotopy,
whose velocity one-forms `ι_{X_t} ω` are closed.

When the suspension `(t, x) ↦ (1, X t x)` is complete, the flow is defined everywhere, the velocity
identity holds at all times and points (`TauCeti.hasDerivAt_mpullback_timeDependentFlowOf`), and
the flow preserves a differentiable form `α` at all times exactly when `L_{X_t} α = 0` for every `t`
(`TauCeti.mpullback_timeDependentFlowOf_eq_self_iff`).

## Main results

* `TauCeti.hasDerivAt_mpullback_timeDependentFlowOf_self`: the velocity of `φ_{t,u}^* α` at
  `u = t` is `L_{X_t} α`.
* `TauCeti.hasDerivAt_mpullback_timeDependentFlowOf_of_mem`: the time derivative of
  `φ_{s,t}^* α` is `φ_{s,t}^* L_{X_t} α` wherever the flow is defined.
* `TauCeti.mpullback_timeDependentFlowOf_apply_of_mextDeriv_interior_eq_zero`: a closed form whose
  contractions with the `X u` are closed is preserved by the flow wherever it is defined.
* `TauCeti.hasDerivAt_mpullback_timeDependentFlowOf`,
  `TauCeti.mpullback_timeDependentFlowOf_of_mextDeriv_interior_eq_zero`: the same for a complete
  suspension, at all times and points.
* `TauCeti.mpullback_timeDependentFlowOf_eq_self_iff`: for a complete suspension, the flow
  preserves `α` exactly when every `L_{X_t} α` vanishes.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2012, Theorem 9.48
  (time-dependent flows) and Chapter 22 (derivatives of pullbacks along time-dependent flows in
  Moser's proof of the Darboux theorem).
* Dusa McDuff and Dietmar Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.2 (symplectic isotopies and their generating vector fields).
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
  {X : ℝ → (x : M) → TangentSpace I x} {α : RoughForm I M F k}

variable (hc : IsCompleteVectorField (timeDependentSuspensionField X))
  (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 2
    (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
include hX

/-! ### Maximal time-dependent flows -/

/-- **The Lie derivative is the velocity of pulled-back forms at the base time.** For a jointly
`C²` time-dependent vector field `X` and a form `α` differentiable at `y`, the pullbacks by the
time-dependent flow from time `t` satisfy `d/du|_{u = t} (φ_{t,u}^* α)_y = (L_{X_t} α)_y`. No
completeness is needed: the flow is `C²` on its open domain, which contains `((t, t), y)`. -/
theorem hasDerivAt_mpullback_timeDependentFlowOf_self (t : ℝ) (y : M)
    (hα : MDifferentiableAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F))
      (fun z ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) z (α z)) y) :
    HasDerivAt (F := E [⋀^Fin k]→L[ℝ] F)
      (fun u ↦ mpullback I I (timeDependentFlowOf X t u) α y)
      (mlieDerivForm (X t) α y) t := by
  have hX₁ := hX.of_le (m := 1) one_le_two
  exact hasDerivAt_mpullback_of_eq_id (ψ := timeDependentFlowOf X t) (V := X t) y
    (Eventually.of_forall (timeDependentFlowOf_self X t))
    (contMDiffAt_uncurry_timeDependentFlowOf (n := 2) one_le_two hX
      (mem_timeDependentFlowDomain_self hX₁ t y))
    (Eventually.of_forall fun x ↦
      hasMFDerivAt_timeDependentFlowOf hX₁ (mem_timeDependentFlowDomain_self hX₁ t x)) hα

/-- **Lie derivatives along time-dependent flows.** For a jointly `C²` time-dependent vector field
`X`, a point `x` at which the flow from time `s` is defined up to time `t`, and a form `α`
differentiable at `φ_{s,t} x`, the pullbacks `(φ_{s,u}^* α)ₓ` by the time-dependent flow from time
`s` have velocity `(φ_{s,t}^* L_{X_t} α)ₓ` at time `t`. No completeness is needed. -/
theorem hasDerivAt_mpullback_timeDependentFlowOf_of_mem {s t : ℝ} {x : M}
    (h : ((s, t), x) ∈ timeDependentFlowDomain X)
    (hα : MDifferentiableAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F))
      (fun z ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) z (α z)) (timeDependentFlowOf X s t x)) :
    HasDerivAt (F := E [⋀^Fin k]→L[ℝ] F)
      (fun u ↦ mpullback I I (timeDependentFlowOf X s u) α x)
      (mpullback I I (timeDependentFlowOf X s t) (mlieDerivForm (X t) α) x) t := by
  have hX₁ := hX.of_le (m := 1) one_le_two
  have hD := isOpen_timeDependentFlowDomain hX₁
  have hφ : MDifferentiableAt I I (timeDependentFlowOf X s t) x :=
    mdifferentiableAt_timeDependentFlowOf hX₁ h
  -- Near `(t, x)`, the flow from `s` is defined up to time `t` at the second coordinate, and the
  -- flow from `t` is defined at its image up to the time given by the first coordinate.
  have hev : ∀ᶠ p in 𝓝 (t, x), ((s, t), p.2) ∈ timeDependentFlowDomain X ∧
      ((t, p.1), timeDependentFlowOf X s t p.2) ∈ timeDependentFlowDomain X :=
    ((continuous_const.prodMk continuous_snd).continuousAt.eventually_mem (hD.mem_nhds h)).and
      (((continuous_const.prodMk continuous_fst).continuousAt.prodMk
        (hφ.continuousAt.comp continuousAt_snd)).eventually_mem
          (hD.mem_nhds (mem_timeDependentFlowDomain_self hX₁ t _)))
  rw [nhds_prod_eq] at hev
  -- By the composition law, `φ_{s,u} = φ_{t,u} ∘ φ_{s,t}` near `x` for `u` near `t`, so the
  -- derivative at `t` is read at the base time of the flow from `t`.
  refine hasDerivAt_mpullback_of_eq_comp (χ := timeDependentFlowOf X t) ?_ hφ ?_
    (hasDerivAt_mpullback_timeDependentFlowOf_self hX t _ hα)
  · filter_upwards [hev.curry] with u hu
    filter_upwards [hu] with y hy
    exact (timeDependentFlowOf_trans_of_mem hX₁ hy.1 hy.2).2.symm
  · filter_upwards [hev.curry] with u hu
    exact mdifferentiableAt_timeDependentFlowOf hX₁ hu.self_of_nhds.2

/-- **Time-dependent flows preserve closed forms with closed contractions, where they are
defined.** Let `X` be a jointly `C²` time-dependent vector field and `β` a differentiable closed
form whose contraction `ι_{X_u} β` is closed for every time `u` between `s` and `t`. If the flow
from `(s, x)` is defined up to time `t`, then `(φ_{s,t}^* β)ₓ = βₓ`, because Cartan's formula gives
`L_{X_u} β = d(ι_{X_u} β) = 0`. No completeness is needed. For a symplectic form `β`, these are the
time-dependent symplectic vector fields. -/
theorem mpullback_timeDependentFlowOf_apply_of_mextDeriv_interior_eq_zero
    {β : RoughForm I M F (k + 1)}
    (hβ : MDifferentiable I (I.prod 𝓘(ℝ, E [⋀^Fin (k + 1)]→L[ℝ] F))
      (fun z ↦ TotalSpace.mk' (E [⋀^Fin (k + 1)]→L[ℝ] F) z (β z)))
    (hdβ : mextDeriv β = 0) {s t : ℝ}
    (hXβ : ∀ u ∈ uIcc s t, mextDeriv (RoughForm.interior (X u) β) = 0) {x : M}
    (h : ((s, t), x) ∈ timeDependentFlowDomain X) :
    mpullback (F := F) I I (timeDependentFlowOf X s t) β x = β x := by
  -- The flow from `(s, x)` is defined at every time between `s` and `t`.
  have hJ := uIcc_subset_setOf_mem_timeDependentFlowDomain h
  -- The pullbacks at `x`, as alternating maps on the model space.
  set P : ℝ → E [⋀^Fin (k + 1)]→L[ℝ] F := fun u ↦ mpullback I I (timeDependentFlowOf X s u) β x
  -- Between `s` and `t` they have velocity `φ_{s,u}^* L_{X_u} β = 0`.
  have hd (u : ℝ) (hu : u ∈ uIcc s t) : HasDerivWithinAt P 0 (uIcc s t) u := by
    have hXu : MDifferentiable I I.tangent (fun y ↦ (⟨y, X u y⟩ : TangentBundle I M)) :=
      (hX.comp ((contMDiff_const (c := u)).prodMk contMDiff_id)).mdifferentiable two_ne_zero
    have h' := hasDerivAt_mpullback_timeDependentFlowOf_of_mem hX (hJ hu) (hβ _)
    rw [mlieDerivForm_eq_mextDeriv_interior hβ hXu hdβ, hXβ u hu, mpullback_zero] at h'
    exact h'.hasDerivWithinAt
  have hconst := (convex_uIcc s t).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f' := fun _ ↦ 0) (C := 0) hd (fun _ _ ↦ by simp) left_mem_uIcc right_mem_uIcc
  rw [zero_mul, norm_le_zero_iff, sub_eq_zero] at hconst
  have hid : timeDependentFlowOf X s s = id := funext (timeDependentFlowOf_self X s)
  exact hconst.trans ((congrArg (fun f ↦ mpullback I I f β x) hid).trans
    (congrFun (mpullback_id β) x))

/-! ### Complete suspensions -/

include hc

/-- **Lie derivatives along complete time-dependent flows.** For a jointly `C²` time-dependent
vector field `X` with complete suspension and a form `α` differentiable at `φ_{s,t} x`, the
pullbacks `(φ_{s,u}^* α)ₓ` by the time-dependent flow from time `s` have velocity
`(φ_{s,t}^* L_{X_t} α)ₓ` at time `t`. -/
theorem hasDerivAt_mpullback_timeDependentFlowOf (s t : ℝ) (x : M)
    (hα : MDifferentiableAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F))
      (fun z ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) z (α z)) (timeDependentFlowOf X s t x)) :
    HasDerivAt (F := E [⋀^Fin k]→L[ℝ] F)
      (fun u ↦ mpullback I I (timeDependentFlowOf X s u) α x)
      (mpullback I I (timeDependentFlowOf X s t) (mlieDerivForm (X t) α) x) t :=
  hasDerivAt_mpullback_timeDependentFlowOf_of_mem hX
    (mem_timeDependentFlowDomain.2 (hc.mem_flowDomain _ _)) hα

/-- **Invariance of forms under time-dependent flows.** For a jointly `C²` time-dependent vector
field `X` with complete suspension, the time-dependent flow preserves a differentiable form `α`,
`φ_{s,t}^* α = α` for all times `s` and `t`, exactly when `L_{X_t} α = 0` for every time `t`. -/
theorem mpullback_timeDependentFlowOf_eq_self_iff
    (hα : MDifferentiable I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F))
      (fun z ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) z (α z))) :
    (∀ s t, mpullback I I (timeDependentFlowOf X s t) α = α) ↔
      ∀ t, mlieDerivForm (X t) α = 0 := by
  have hid (s : ℝ) : mpullback I I (timeDependentFlowOf X s s) α = α := by
    have h : timeDependentFlowOf X s s = id := funext (timeDependentFlowOf_self X s)
    rw [h, mpullback_id]
  constructor
  · -- The pullbacks by the flow from `t` are constant, so their velocity at `t` vanishes.
    intro h t
    funext y
    have hd := hasDerivAt_mpullback_timeDependentFlowOf_self hX t y (hα y)
    have hconst : (fun u ↦ mpullback I I (timeDependentFlowOf X t u) α y) = fun _ ↦ α y :=
      funext fun u ↦ congrFun (h t u) y
    rw [hconst] at hd
    exact hd.unique (hasDerivAt_const (F := E [⋀^Fin k]→L[ℝ] F) t (α y))
  · -- With vanishing Lie derivatives, the pullbacks by the flow from `s` are constant.
    intro h s t
    rw [mpullback_eq_of_forall_mlieDerivForm_eq_zero
      (fun u x ↦ hasDerivAt_mpullback_timeDependentFlowOf hc hX s u x (hα _)) h t s, hid s]

/-- **Time-dependent flows preserve closed forms with closed contractions.** For a jointly `C²`
time-dependent vector field `X` with complete suspension and a differentiable closed form `β`
whose contraction `ι_{X_t} β` is closed for every time `t`, the time-dependent flow satisfies
`φ_{s,t}^* β = β`, because Cartan's formula gives `L_{X_t} β = d(ι_{X_t} β) = 0`. For a
symplectic form `β`, these are the time-dependent symplectic vector fields. -/
theorem mpullback_timeDependentFlowOf_of_mextDeriv_interior_eq_zero
    {β : RoughForm I M F (k + 1)}
    (hβ : MDifferentiable I (I.prod 𝓘(ℝ, E [⋀^Fin (k + 1)]→L[ℝ] F))
      (fun z ↦ TotalSpace.mk' (E [⋀^Fin (k + 1)]→L[ℝ] F) z (β z)))
    (hdβ : mextDeriv β = 0) (hXβ : ∀ t, mextDeriv (RoughForm.interior (X t) β) = 0) (s t : ℝ) :
    mpullback (F := F) I I (timeDependentFlowOf X s t) β = β :=
  funext fun _ ↦ mpullback_timeDependentFlowOf_apply_of_mextDeriv_interior_eq_zero hX hβ hdβ
    (fun u _ ↦ hXβ u) (mem_timeDependentFlowDomain.2 (hc.mem_flowDomain _ _))

end TauCeti
