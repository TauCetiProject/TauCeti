/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Flow
public import TauCeti.Geometry.Manifold.Flow.TimeDependent
import TauCeti.Geometry.Manifold.MFDeriv.Curve
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# Lie derivatives of differential forms along time-dependent flows

Let `X` be a jointly `C²` time-dependent vector field on a finite-dimensional manifold without
boundary whose suspension `(t, x) ↦ (1, X t x)` is complete, and let `φ_{s,t}` be its
time-dependent flow from time `s` to time `t` (`TauCeti.timeDependentFlowOf`). For a differential
form `α`, the pullbacks `φ_{s,t}^* α` at a point `x` form a curve in the alternating maps on
`T_x M`, and its velocity is the pullback of the Lie derivative along the field at the current
time:

`d/dt (φ_{s,t}^* α)ₓ = (φ_{s,t}^* L_{X_t} α)ₓ`

(`TauCeti.hasDerivAt_mpullback_timeDependentFlowOf`). This is the time-dependent counterpart of
`TauCeti.hasDerivAt_mpullback_globalFlow`. The Lie derivative `L_{X_t} α` is
`TauCeti.mlieDerivForm (X t) α`, defined in charts with no reference to flows.

At the base time itself, the flow `u ↦ φ_{t,u}` is a jointly `C²` family of maps which is the
identity at time `t` and moves with velocity `X t` there, so
`d/du|_{u = t} (φ_{t,u}^* α) = L_{X_t} α` is an instance of
`TauCeti.hasDerivAt_mpullback_of_eq_id`. The two-time composition law
`φ_{s,u} = φ_{t,u} ∘ φ_{s,t}` moves this to an arbitrary base time `s`.

Integrating the identity: the time-dependent flow preserves a differentiable form `α` at all
times exactly when `L_{X_t} α = 0` for every `t`
(`TauCeti.mpullback_timeDependentFlowOf_eq_self_iff`). For a closed form `β` this is the
condition that every contraction `ι_{X_t} β` is closed, by Cartan's formula
(`TauCeti.mpullback_timeDependentFlowOf_of_mextDeriv_interior_eq_zero`). For a symplectic form
`ω`, this says that the flow of a time-dependent symplectic vector field consists of
symplectomorphisms; this is the input to the flux of a symplectic isotopy, whose velocity
one-forms `ι_{X_t} ω` are closed.

## Main results

* `TauCeti.hasDerivAt_mpullback_timeDependentFlowOf_self`: the velocity of `φ_{t,u}^* α` at
  `u = t` is `L_{X_t} α`.
* `TauCeti.hasDerivAt_mpullback_timeDependentFlowOf`: the time derivative of `φ_{s,t}^* α` is
  `φ_{s,t}^* L_{X_t} α`.
* `TauCeti.mpullback_timeDependentFlowOf_eq_self_iff`: the flow preserves `α` exactly when every
  `L_{X_t} α` vanishes.
* `TauCeti.mpullback_timeDependentFlowOf_of_mextDeriv_interior_eq_zero`: a closed form whose
  contractions with all `X t` are closed is preserved by the flow.

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
include hc hX

/-- The time-dependent flow from time `t`, read in the chart at `y`, is jointly `C²` in time and
coordinates near `(t, y)`. -/
private theorem contDiffAt_extChartAt_timeDependentFlowOf (t : ℝ) (y : M) :
    ContDiffAt ℝ 2 (fun p : ℝ × E ↦
      extChartAt I y (timeDependentFlowOf X t p.1 ((extChartAt I y).symm p.2)))
      (t, extChartAt I y y) := by
  have hX₁ := hX.of_le (m := 1) one_le_two
  have hsymm : ContMDiffAt 𝓘(ℝ, E) I 2 (extChartAt I y).symm (extChartAt I y y) := by
    have h := contMDiffWithinAt_extChartAt_symm_range_self (I := I) (n := 2) y
    rwa [I.range_eq_univ, contMDiffWithinAt_univ] at h
  have hpair : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) 2
      (fun p : ℝ × E ↦ ((t, p.1), (extChartAt I y).symm p.2)) (t, extChartAt I y y) :=
    (contMDiffAt_const.prodMk contMDiffAt_fst).prodMk
      (ContMDiffAt.comp (t, extChartAt I y y) hsymm contMDiffAt_snd)
  have hflow := (contMDiff_timeDependentFlowOf hc (n := 2) (by norm_num) hX).contMDiffAt
    (x := ((t, t), (extChartAt I y).symm (extChartAt I y y)))
  have hcomp := (contMDiffAt_extChartAt (I := I) (n := 2) (x := y)).comp_of_eq
    (ContMDiffAt.comp (t, extChartAt I y y) hflow hpair) (by
      simp only [Function.comp_apply, extChartAt_to_inv]
      exact timeDependentFlowOf_self hX₁ t y)
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod, contMDiffAt_iff_contDiffAt] at hcomp
  exact hcomp

omit hc in
/-- At the base time `t`, the velocity of the time-dependent flow from `t`, read in the chart at
`y`, is the coordinate expression of `X t` in that chart. -/
private theorem hasDerivAt_extChartAt_timeDependentFlowOf (t : ℝ) (y : M) {z : E}
    (hz : z ∈ (extChartAt I y).target) :
    HasDerivAt (fun u ↦ extChartAt I y (timeDependentFlowOf X t u ((extChartAt I y).symm z)))
      (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I y).symm (X t) (range I) z) t := by
  have hX₁ := hX.of_le (m := 1) one_le_two
  set q := (extChartAt I y).symm z
  have hq : q ∈ (extChartAt I y).source := (extChartAt I y).map_target hz
  have hγ := hasMFDerivAt_timeDependentFlowOf hX₁ (mem_timeDependentFlowDomain_self hX₁ t q)
  set p := timeDependentFlowOf X t t q
  have hp : p = q := timeDependentFlowOf_self hX₁ t q
  have hpsrc : p ∈ (chartAt H y).source := hp ▸ extChartAt_source I y ▸ hq
  have hderiv := TauCeti.Manifold.hasDerivAt_comp_curve
    (mdifferentiableAt_extChartAt (I := I) hpsrc) hγ
  -- In the tangent-bundle trivialization at `y`, the coordinate field is a coordinate change.
  have hcoord : mvfderiv I (extChartAt I y) p (X t p) =
      VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I y).symm (X t) (range I)
        (extChartAt I y p) := by
    rw [VectorField.mpullbackWithin_extChartAt_symm_apply (X t) (extChartAt_source I y ▸ hpsrc)]
    simp only [mvfderiv]
    rw [(hasMFDerivAt_extChartAt (I := I) hpsrc).mfderiv,
      mfderiv_chartAt_eq_tangentCoordChange hpsrc]
    -- `tangentCoordChange` is by definition this fibre coordinate of the trivialization
    -- (`TangentBundle.trivializationAt_apply`, `tangentCoordChange_def`).
    rfl
  rw [hcoord, hp, (extChartAt I y).right_inv hz] at hderiv
  exact hderiv

/-- **The Lie derivative is the velocity of pulled-back forms at the base time.** For a jointly
`C²` time-dependent vector field `X` with complete suspension and a form `α` differentiable at
`y`, the pullbacks by the time-dependent flow from time `t` satisfy
`d/du|_{u = t} (φ_{t,u}^* α)_y = (L_{X_t} α)_y`. -/
theorem hasDerivAt_mpullback_timeDependentFlowOf_self (t : ℝ) (y : M)
    (hα : MDifferentiableAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F))
      (fun z ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) z (α z)) y) :
    HasDerivAt (F := E [⋀^Fin k]→L[ℝ] F)
      (fun u ↦ mpullback I I (timeDependentFlowOf X t u) α y)
      (mlieDerivForm (X t) α y) t := by
  have hX₁ := hX.of_le (m := 1) one_le_two
  have hflow := contMDiff_timeDependentFlowOf hc (n := 2) (by norm_num) hX
  exact hasDerivAt_mpullback_of_eq_id (ψ := timeDependentFlowOf X t) (V := X t) y
    (Eventually.of_forall (timeDependentFlowOf_self hX₁ t))
    (Eventually.of_forall fun u ↦ (hflow.comp
      ((contMDiff_const (c := (t, u))).prodMk contMDiff_id)).mdifferentiableAt (by norm_num))
    (hflow.comp (((contMDiff_const (c := t)).prodMk contMDiff_id).prodMk
      contMDiff_const)).continuous.continuousAt
    (contDiffAt_extChartAt_timeDependentFlowOf hc hX t y)
    (eventually_of_mem (extChartAt_target_mem_nhds y) fun _ hz ↦
      hasDerivAt_extChartAt_timeDependentFlowOf hX t y hz) hα

/-- **Lie derivatives along time-dependent flows.** For a jointly `C²` time-dependent vector field
`X` with complete suspension and a form `α` differentiable at `φ_{s,t} x`, the pullbacks
`(φ_{s,u}^* α)ₓ` by the time-dependent flow from time `s` have velocity `(φ_{s,t}^* L_{X_t} α)ₓ`
at time `t`. -/
theorem hasDerivAt_mpullback_timeDependentFlowOf (s t : ℝ) (x : M)
    (hα : MDifferentiableAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F))
      (fun z ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) z (α z)) (timeDependentFlowOf X s t x)) :
    HasDerivAt (F := E [⋀^Fin k]→L[ℝ] F)
      (fun u ↦ mpullback I I (timeDependentFlowOf X s u) α x)
      (mpullback I I (timeDependentFlowOf X s t) (mlieDerivForm (X t) α) x) t := by
  have hX₁ := hX.of_le (m := 1) one_le_two
  have hsmooth (a b : ℝ) : MDifferentiable I I (timeDependentFlowOf X a b) :=
    ((contMDiff_timeDependentFlowOf hc (n := 2) (by norm_num) hX).comp
      ((contMDiff_const (c := (a, b))).prodMk contMDiff_id)).mdifferentiable (by norm_num)
  set L : E →L[ℝ] E := mfderiv I I (timeDependentFlowOf X s t) x
  -- By the composition law, `φ_{s,u}^* α = φ_{s,t}^* (φ_{t,u}^* α)`, so the derivative at `t` is
  -- read at the base time of the flow from `t`.
  have hshift (u : ℝ) : mpullback I I (timeDependentFlowOf X s u) α x =
      compContinuousLinearMapCLM (ι := Fin k) (F := F) L
        (mpullback I I (timeDependentFlowOf X t u) α (timeDependentFlowOf X s t x)) := by
    have hcomp : timeDependentFlowOf X s u =
        timeDependentFlowOf X t u ∘ timeDependentFlowOf X s t :=
      funext fun z ↦ (timeDependentFlowOf_trans hc hX₁ s t u z).symm
    rw [hcomp, mpullback_comp_at (hsmooth s t x) (hsmooth t u _)]
    ext v
    -- Both sides evaluate `φ_{t,u}^* α` at `φ_{s,t} x` on the vectors `L (v i)`.
    rw [mpullback_apply]
    rfl
  have h := (compContinuousLinearMapCLM (ι := Fin k) (F := F) L).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_mpullback_timeDependentFlowOf_self hc hX t _ hα)
  refine (h.congr_of_eventuallyEq (Eventually.of_forall fun u ↦ hshift u)).congr_deriv ?_
  ext v
  exact (mpullback_apply (timeDependentFlowOf X s t) (mlieDerivForm (X t) α) x v).symm

/-- **Invariance of forms under time-dependent flows.** For a jointly `C²` time-dependent vector
field `X` with complete suspension, the time-dependent flow preserves a differentiable form `α`,
`φ_{s,t}^* α = α` for all times `s` and `t`, exactly when `L_{X_t} α = 0` for every time `t`. -/
theorem mpullback_timeDependentFlowOf_eq_self_iff
    (hα : MDifferentiable I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F))
      (fun z ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) z (α z))) :
    (∀ s t, mpullback I I (timeDependentFlowOf X s t) α = α) ↔
      ∀ t, mlieDerivForm (X t) α = 0 := by
  have hX₁ := hX.of_le (m := 1) one_le_two
  have hid (s : ℝ) : mpullback I I (timeDependentFlowOf X s s) α = α := by
    have h : timeDependentFlowOf X s s = id := funext (timeDependentFlowOf_self hX₁ s)
    rw [h, mpullback_id]
  constructor
  · -- The pullbacks by the flow from `t` are constant, so their velocity at `t` vanishes.
    intro h t
    funext y
    have hd := hasDerivAt_mpullback_timeDependentFlowOf_self hc hX t y (hα y)
    have hconst : (fun u ↦ mpullback I I (timeDependentFlowOf X t u) α y) = fun _ ↦ α y :=
      funext fun u ↦ congrFun (h t u) y
    rw [hconst] at hd
    exact hd.unique (hasDerivAt_const (F := E [⋀^Fin k]→L[ℝ] F) t (α y))
  · -- With vanishing Lie derivatives, the pullbacks at each point have zero velocity.
    intro h s t
    funext x
    set P : ℝ → E [⋀^Fin k]→L[ℝ] F := fun u ↦ mpullback I I (timeDependentFlowOf X s u) α x
    have hderiv (u : ℝ) : HasDerivAt P 0 u := by
      have hd := hasDerivAt_mpullback_timeDependentFlowOf hc hX s u x (hα _)
      rw [h u, mpullback_zero] at hd
      exact hd
    have hconst := is_const_of_deriv_eq_zero (fun u ↦ (hderiv u).differentiableAt)
      (fun u ↦ (hderiv u).deriv) t s
    simp only [P, hid s] at hconst
    exact hconst

/-- **Time-dependent flows preserve closed forms with closed contractions.** For a jointly `C²`
time-dependent vector field `X` with complete suspension and a closed smooth form `β` whose
contraction `ι_{X_t} β` is closed for every time `t`, the time-dependent flow satisfies
`φ_{s,t}^* β = β`, because Cartan's formula gives `L_{X_t} β = d(ι_{X_t} β) = 0`. For a
symplectic form `β`, these are the time-dependent symplectic vector fields. -/
theorem mpullback_timeDependentFlowOf_of_mextDeriv_interior_eq_zero
    {β : SmoothForm I M F (k + 1)} (hβ : β.IsClosed)
    (hXβ : ∀ t, mextDeriv (RoughForm.interior (X t) β.1) = 0) (s t : ℝ) :
    mpullback (F := F) I I (timeDependentFlowOf X s t) β.1 = β.1 := by
  refine (mpullback_timeDependentFlowOf_eq_self_iff hc hX β.mdifferentiable).2 (fun u ↦ ?_) s t
  -- The slice `X u` is a differentiable vector field.
  have hXu : MDifferentiable I I.tangent (fun y ↦ (⟨y, X u y⟩ : TangentBundle I M)) :=
    (hX.comp ((contMDiff_const (c := u)).prodMk contMDiff_id)).mdifferentiable two_ne_zero
  rw [SmoothForm.mlieDerivForm_eq_mextDeriv_interior hXu hβ, hXβ u]

end TauCeti
