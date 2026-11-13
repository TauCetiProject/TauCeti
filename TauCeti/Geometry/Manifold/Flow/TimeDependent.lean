/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.Complete
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import TauCeti.Geometry.Manifold.Diffeomorph.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Basic
public import TauCeti.Geometry.Manifold.MFDeriv.Curve
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# Time-dependent flows on manifolds

A time-dependent vector field on a manifold `M` is a family `X t` of vector fields on `M`, indexed
by the time `t : ℝ`. Its integral curves are the curves `γ` with `γ' u = X u (γ u)`. Adjoining the
clock equation `t' = 1` turns `X` into the autonomous vector field `(t, x) ↦ (1, X t x)` on
`ℝ × M`, its *suspension* (`TauCeti.timeDependentSuspensionField`), and the maximal flow of the
suspension yields the maximal time-dependent flow of `X`:
`TauCeti.timeDependentFlowOf X s t x` is the value at time `t` of the maximal integral curve of `X`
which passes through `x` at time `s`. It is defined on the set `TauCeti.timeDependentFlowDomain X`
of triples `((s, t), x)`, and is total, with junk values outside that set.

For a jointly `C^n` time-dependent field on a finite-dimensional boundaryless manifold, `1 ≤ n`,
this is the fundamental theorem on time-dependent flows: the domain is open and contains every
triple `((s, s), x)`, the flow is jointly `C^n` on it, its curves `t ↦ timeDependentFlowOf X s t x`
solve the equation and are the unique solutions through `x` at time `s`, and the two-time
composition law holds wherever its terms are defined. A time-dependent field vanishing outside a
compact subset of `M` at all times has a complete suspension, and then every time map is a `C^n`
diffeomorphism of `M`, with inverse the time map in the opposite direction.

Compactly supported time-dependent fields are the input to the isotopy extension theorem: the
velocity of a moving compact submanifold, extended to a compactly supported field on the ambient
manifold, has a complete suspension, and its time maps are the ambient diffeomorphisms that carry
the initial position of the submanifold to the later ones.

## Main definitions

* `TauCeti.timeDependentSuspensionField X`: the autonomous field `(t, x) ↦ (1, X t x)` on
  `ℝ × M`.
* `TauCeti.timeDependentFlowDomain X`: the domain of the maximal time-dependent flow.
* `TauCeti.timeDependentFlowOf X s t x`: the maximal time-dependent flow from time `s` to time `t`.
* `TauCeti.timeDependentFlowPartialDiffeomorph`: the time map from `s` to `t` as a partial
  diffeomorphism between the open sets on which it and its inverse are defined.
* `TauCeti.timeDependentFlowDiffeomorph`: for a complete suspension, the time map from `s` to `t`
  as a `C^n` diffeomorphism.
* `TauCeti.timeDependentFlowMFDerivEquiv`: for a complete suspension, the differential of the
  time map as a continuous linear equivalence of tangent spaces.

## Main results

* `TauCeti.flowOf_timeDependentSuspensionField`: the flow of the suspension advances the clock at
  unit speed and moves the point along the time-dependent flow.
* `TauCeti.isOpen_timeDependentFlowDomain` and `TauCeti.contMDiffOn_timeDependentFlowOf`: the
  domain is open and the flow is jointly `C^n` on it.
* `TauCeti.hasMFDerivAt_timeDependentFlowOf`: the curves of the flow solve `γ' u = X u (γ u)`;
  `TauCeti.curveVelocity_timeDependentFlowOf` states this for their velocity.
* `TauCeti.timeDependentFlowOf_eq_of_hasMFDerivAt`: every solution on an open interval is a curve
  of the flow.
* `TauCeti.timeDependentFlowOf_trans_of_mem` and `TauCeti.timeDependentFlowOf_trans`: the two-time
  composition law, where it is defined, and everywhere for a complete suspension.
* `TauCeti.timeDependentFlowOf_symm_of_mem`: flowing back from time `t` to time `s` undoes the flow
  from `s` to `t`.
* `TauCeti.contMDiffAt_timeDependentFlowOf`: the time map is `C^n` at every point where it is
  defined, and `TauCeti.contMDiffAt_timeDependentFlowOf_comp` its composite with `C^n` initial
  times, final times and initial points.
* `TauCeti.curveVelocity_timeDependentFlowOf_comp`: the transverse velocity of the trajectories
  through a curve of initial points is the derivative of the time map applied to its velocity.
* `TauCeti.contMDiffAt_totalSpaceMk_mfderiv_timeDependentFlowOf`: along a trajectory, the
  linearized flow `u ↦ dφ_{s, u} v` is one degree less regular than the field.
* `TauCeti.injective_mfderiv_timeDependentFlowOf`: the derivative of the time map is injective
  wherever the flow is defined, with no completeness assumption.
* `TauCeti.isCompleteVectorField_timeDependentSuspensionField`: a time-dependent field vanishing
  outside a fixed compact set has a complete suspension.
* `TauCeti.hasMFDerivAt_timeDependentFlowOf_comp`: a map moved by the flow at a varying time,
  `y ↦ timeDependentFlowOf X s (τ y) (v y)`, has derivative `dφ ∘ dv + dτ ⊗ X`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Theorem 9.48
  (the fundamental theorem on time-dependent flows).
* M. W. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Chapter 8, §1 (isotopy extension
  by compactly supported time-dependent vector fields).

The formalization adapts the time-dependent flow construction of the Tau Ceti contributors
(https://github.com/TauCetiProject/TauCeti/pull/20364).

The suspension construction is the manifold counterpart of `TauCeti.timeDependentSuspension` in
`TauCeti.Dynamics.Flow.TimeDependent`; the maximal flow is Tau Ceti's `TauCeti.flowOf`.
-/

public section

noncomputable section

open Set
open TauCeti.Manifold
open scoped Manifold ContDiff Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-! ### The suspension of a time-dependent vector field -/

/-- The **suspension** of a time-dependent vector field `X` on `M`: the autonomous vector field
`(t, x) ↦ (1, X t x)` on `ℝ × M`, whose first component advances the clock at unit speed. -/
def timeDependentSuspensionField (X : ℝ → (x : M) → TangentSpace I x) :
    (p : ℝ × M) → TangentSpace (𝓘(ℝ, ℝ).prod I) p :=
  fun p ↦ (1, X p.1 p.2)

/-- The clock component of the suspension is `1`. -/
@[simp]
theorem timeDependentSuspensionField_fst (X : ℝ → (x : M) → TangentSpace I x) (p : ℝ × M) :
    (timeDependentSuspensionField X p).1 = 1 :=
  (rfl)

/-- The spatial component of the suspension at `(t, x)` is `X t x`. -/
@[simp]
theorem timeDependentSuspensionField_snd (X : ℝ → (x : M) → TangentSpace I x) (p : ℝ × M) :
    (timeDependentSuspensionField X p).2 = X p.1 p.2 :=
  (rfl)

/-- For a jointly `C^n` time-dependent vector field `X` and a real number `c`, the field `(c, X)`
on `ℝ × M` is a `C^n` vector field. For `c = 1` it is the suspension of `X`, for `c = 0` it is the
vertical field of `X`, and for `X = 0` and `c = 1` it is the unit field `∂_t` of the time
coordinate. -/
theorem contMDiff_const_prod_field [IsManifold I 1 M] {n : ℕ∞ω}
    {X : ℝ → (x : M) → TangentSpace I x} (c : ℝ)
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent n
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M))) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I).tangent n
      (fun p : ℝ × M ↦ (⟨p, (c, X p.1 p.2)⟩ : TangentBundle (𝓘(ℝ, ℝ).prod I) (ℝ × M))) := by
  have hclock : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ).tangent n
      (fun s : ℝ ↦ (⟨s, c⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
    contMDiff_vectorSpace_iff_contDiff.2 contDiff_const
  exact (contMDiff_equivTangentBundleProd_symm (I := 𝓘(ℝ, ℝ)) (M := ℝ) (I' := I) (M' := M)).comp
    ((hclock.comp contMDiff_fst).prodMk hX)

/-- The suspension of a jointly `C^n` time-dependent vector field is a `C^n` vector field on
`ℝ × M`. -/
theorem contMDiff_timeDependentSuspensionField [IsManifold I 1 M] {n : ℕ∞ω}
    {X : ℝ → (x : M) → TangentSpace I x}
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent n
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M))) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I).tangent n
      (fun p : ℝ × M ↦ (⟨p, timeDependentSuspensionField X p⟩ :
        TangentBundle (𝓘(ℝ, ℝ).prod I) (ℝ × M))) :=
  contMDiff_const_prod_field 1 hX

/-! ### The maximal time-dependent flow -/

/-- The **domain of the maximal time-dependent flow** of `X`: the triples `((s, t), x)` such that
the maximal integral curve of `X` through `x` at time `s` is defined at time `t`. -/
def timeDependentFlowDomain (X : ℝ → (x : M) → TangentSpace I x) : Set ((ℝ × ℝ) × M) :=
  {p | (p.1.2 - p.1.1, (p.1.1, p.2)) ∈ flowDomain (timeDependentSuspensionField X)}

/-- The **maximal time-dependent flow** of `X`: `timeDependentFlowOf X s t x` is the value at
time `t` of the maximal integral curve of `X` passing through `x` at time `s`. It is read off the
maximal flow of the suspension of `X`, and has junk values outside
`timeDependentFlowDomain X`. -/
def timeDependentFlowOf (X : ℝ → (x : M) → TangentSpace I x) (s t : ℝ) (x : M) : M :=
  (flowOf (timeDependentSuspensionField X) (t - s) (s, x)).2

variable {X : ℝ → (x : M) → TangentSpace I x} {s t : ℝ} {x : M}

/-- Membership in the domain of the time-dependent flow is membership of `(t - s, (s, x))` in
the domain of the maximal flow of the suspension. -/
theorem mem_timeDependentFlowDomain :
    ((s, t), x) ∈ timeDependentFlowDomain X ↔
      (t - s, (s, x)) ∈ flowDomain (timeDependentSuspensionField X) :=
  Iff.rfl

/-- The time-dependent flow is the spatial component of the flow of the suspension. -/
theorem timeDependentFlowOf_def :
    timeDependentFlowOf X s t x = (flowOf (timeDependentSuspensionField X) (t - s) (s, x)).2 :=
  (rfl)

/-! ### Solutions of the time-dependent equation -/

/-- A curve of `M` solving the time-dependent equation lifts, through its clock, to an integral
curve of the suspension. -/
private theorem hasMFDerivAt_lift {γ : ℝ → M} {τ : ℝ}
    (hγ : HasMFDerivAt 𝓘(ℝ, ℝ) I γ (s + τ) ((1 : ℝ →L[ℝ] ℝ).smulRight (X (s + τ) (γ (s + τ))))) :
    HasMFDerivAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) (fun r ↦ (s + r, γ (s + r))) τ
      ((1 : ℝ →L[ℝ] ℝ).smulRight (timeDependentSuspensionField X (s + τ, γ (s + τ)))) := by
  have hadd : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun r : ℝ ↦ s + r) τ (ContinuousLinearMap.id ℝ ℝ) :=
    hasMFDerivAt_iff_hasFDerivAt.2 ((hasFDerivAt_id τ).const_add s)
  -- Both derivatives send `r` to `(r, r • X (s + τ) (γ (s + τ)))`, read in `ℝ × E`; the clock
  -- component on the right is `r • 1 = r * 1`.
  exact (hadd.prodMk (hγ.comp τ hadd)).congr_mfderiv
    (ContinuousLinearMap.ext fun r ↦ Prod.ext (mul_one (M := ℝ) r).symm rfl)

/-- A solution of the time-dependent equation on an open interval, lifted through its clock, is an
integral curve of the suspension. -/
private theorem isMIntegralCurveOn_lift {γ : ℝ → M} {a b : ℝ}
    (hγ : ∀ u ∈ Ioo a b, HasMFDerivAt 𝓘(ℝ, ℝ) I γ u ((1 : ℝ →L[ℝ] ℝ).smulRight (X u (γ u)))) :
    IsMIntegralCurveOn (fun r ↦ (s + r, γ (s + r))) (timeDependentSuspensionField X)
      (Ioo (a - s) (b - s)) := fun r hr ↦
  (hasMFDerivAt_lift (hγ _ ⟨by linarith [hr.1], by linarith [hr.2]⟩)).hasMFDerivWithinAt

/-- A solution `γ` of the time-dependent equation on an open interval containing `s` and `t` stays
in the domain of the time-dependent flow: `((s, t), γ s)` lies in it. -/
theorem mem_timeDependentFlowDomain_of_hasMFDerivAt {γ : ℝ → M} {a b : ℝ}
    (hγ : ∀ u ∈ Ioo a b, HasMFDerivAt 𝓘(ℝ, ℝ) I γ u ((1 : ℝ →L[ℝ] ℝ).smulRight (X u (γ u))))
    (hs : s ∈ Ioo a b) (ht : t ∈ Ioo a b) :
    ((s, t), γ s) ∈ timeDependentFlowDomain X := by
  rw [mem_timeDependentFlowDomain, mem_flowDomain]
  refine (isMIntegralCurveOn_lift (s := s) hγ).subset_maximalIntegralCurveInterval
    (x := (s, γ s)) ?_ (by simp) ?_ <;> constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]

/-- The constant curve at a point where `X` vanishes at all times solves the time-dependent
equation. -/
private theorem hasMFDerivAt_const_of_forall_eq_zero (hx : ∀ u, X u x = 0) (u : ℝ) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I (fun _ : ℝ ↦ x) u ((1 : ℝ →L[ℝ] ℝ).smulRight (X u x)) := by
  rw [hx u, ContinuousLinearMap.smulRight_zero]
  exact hasMFDerivAt_const x u

/-- A point at which `X` vanishes at all times stays in the domain of the time-dependent flow. -/
theorem mem_timeDependentFlowDomain_of_forall_eq_zero (hx : ∀ u, X u x = 0) (s t : ℝ) :
    ((s, t), x) ∈ timeDependentFlowDomain X :=
  mem_timeDependentFlowDomain_of_hasMFDerivAt (γ := fun _ ↦ x) (a := min s t - 1)
    (b := max s t + 1) (fun u _ ↦ hasMFDerivAt_const_of_forall_eq_zero hx u)
    ⟨by linarith [min_le_left s t], by linarith [le_max_left s t]⟩
    ⟨by linarith [min_le_right s t], by linarith [le_max_right s t]⟩

/-- The times at which the flow from `(s, x)` is defined form an interval. -/
theorem ordConnected_setOf_mem_timeDependentFlowDomain (s : ℝ) (x : M) :
    {u | ((s, u), x) ∈ timeDependentFlowDomain X}.OrdConnected := by
  refine ⟨fun p hp q hq u hu ↦ ?_⟩
  simp only [mem_ofPred_eq, mem_timeDependentFlowDomain, mem_flowDomain] at hp hq ⊢
  exact ordConnected_maximalIntegralCurveInterval.out hp hq
    ⟨by linarith [hu.1], by linarith [hu.2]⟩

/-- Two times at which the flow from `(s, x)` is defined, `s` and `t`, lie in a common open
interval of times at which it is defined. -/
theorem exists_Ioo_of_mem_timeDependentFlowDomain (h : ((s, t), x) ∈ timeDependentFlowDomain X) :
    ∃ a b, s ∈ Ioo a b ∧ t ∈ Ioo a b ∧
      ∀ u ∈ Ioo a b, ((s, u), x) ∈ timeDependentFlowDomain X := by
  rw [mem_timeDependentFlowDomain, mem_flowDomain] at h
  obtain ⟨γ, a, b, hγ, hγ0, h0, ht, -⟩ := exists_isMIntegralCurveOn_maximalIntegralCurve_eq h
  refine ⟨a + s, b + s, ⟨by linarith [h0.1], by linarith [h0.2]⟩,
    ⟨by linarith [ht.1], by linarith [ht.2]⟩, fun u hu ↦ ?_⟩
  rw [mem_timeDependentFlowDomain, mem_flowDomain]
  exact hγ.subset_maximalIntegralCurveInterval h0 hγ0 ⟨by linarith [hu.1], by linarith [hu.2]⟩

/-- **The clock of the suspension runs at unit speed.** Along the maximal integral curve of the
suspension through `(s, x)`, the time coordinate at flow time `τ` is `s + τ`. -/
theorem fst_flowOf_timeDependentSuspensionField {τ : ℝ}
    (hτ : (τ, (s, x)) ∈ flowDomain (timeDependentSuspensionField X)) :
    (flowOf (timeDependentSuspensionField X) τ (s, x)).1 = s + τ := by
  obtain ⟨γ, a, b, hγ, hγ0, h0, hτab, heq⟩ :=
    exists_isMIntegralCurveOn_maximalIntegralCurve_eq (mem_flowDomain.1 hτ)
  -- On the open interval `Ioo a b`, the clock coordinate minus the flow time has derivative zero.
  have hderiv (u : ℝ) (hu : u ∈ Ioo a b) : HasDerivAt (fun r ↦ (γ r).1 - r) 0 u := by
    have hc := (hγ.isMIntegralCurveAt (Ioo_mem_nhds hu.1 hu.2)).hasMFDerivAt
    -- A `HasDerivAt` statement is by definition a `HasFDerivAt` statement with derivative
    -- `smulRight 1`, and the clock velocity lies in `TangentSpace 𝓘(ℝ, ℝ) _`, which is `ℝ`.
    have hfst : HasDerivAt (fun r ↦ (γ r).1) (timeDependentSuspensionField X (γ u)).1 u :=
      hasMFDerivAt_iff_hasFDerivAt.1 hc.fst_curve
    rw [timeDependentSuspensionField_fst] at hfst
    have h := hfst.sub (hasDerivAt_id' u)
    rwa [sub_self] at h
  have hconst := isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
    (fun u hu ↦ (hderiv u hu).differentiableAt.differentiableWithinAt)
    (fun u hu ↦ (hderiv u hu).deriv) hτab h0
  rw [hγ0] at hconst
  rw [flowOf_apply, heq]
  linarith

/-- **The flow of the suspension** through `(s, x)` reaches the point
`(t, timeDependentFlowOf X s t x)` after time `t - s`. -/
theorem flowOf_timeDependentSuspensionField (h : ((s, t), x) ∈ timeDependentFlowDomain X) :
    flowOf (timeDependentSuspensionField X) (t - s) (s, x) = (t, timeDependentFlowOf X s t x) :=
  Prod.ext (by rw [fst_flowOf_timeDependentSuspensionField h]; ring) (rfl)

/-- The time-dependent flow from time `s` to time `s` is the identity. -/
@[simp]
theorem timeDependentFlowOf_self (X : ℝ → (x : M) → TangentSpace I x) (s : ℝ) (x : M) :
    timeDependentFlowOf X s s x = x := by
  rw [timeDependentFlowOf_def, sub_self, flowOf_zero]

/-- The linearized time-dependent flow from time `s` to time `s` is the identity. -/
@[simp]
theorem mfderiv_timeDependentFlowOf_self (X : ℝ → (x : M) → TangentSpace I x) (s : ℝ) (x : M) :
    mfderiv I I (timeDependentFlowOf X s s) x = ContinuousLinearMap.id ℝ (TangentSpace I x) := by
  have hid : timeDependentFlowOf X s s = id := funext (timeDependentFlowOf_self X s)
  rw [hid, mfderiv_id]

/-- If a triple `((s, t), x)` lies in the domain of the time-dependent flow, so does
`((s, s), x)`. -/
theorem mem_timeDependentFlowDomain_self_of_mem {X : ℝ → (x : M) → TangentSpace I x} {s t : ℝ}
    {x : M} (h : ((s, t), x) ∈ timeDependentFlowDomain X) :
    ((s, s), x) ∈ timeDependentFlowDomain X := by
  rw [mem_timeDependentFlowDomain, sub_self]
  exact mem_flowDomain_zero_of_mem (mem_timeDependentFlowDomain.1 h)

section Flow

variable [T2Space M] [IsManifold I 1 M] [BoundarylessManifold I M]
  (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 1
    (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
include hX

/-- **The curves of the time-dependent flow solve the equation.** At every time `t` at which it is
defined, the curve `u ↦ timeDependentFlowOf X s u x` has velocity
`X t (timeDependentFlowOf X s t x)`. -/
theorem hasMFDerivAt_timeDependentFlowOf (h : ((s, t), x) ∈ timeDependentFlowDomain X) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I (fun u ↦ timeDependentFlowOf X s u x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (timeDependentFlowOf X s t x))) := by
  have hW := contMDiff_timeDependentSuspensionField hX
  set c : ℝ → ℝ × M := fun τ ↦ flowOf (timeDependentSuspensionField X) τ (s, x)
  have hdom : {τ | (τ, (s, x)) ∈ flowDomain (timeDependentSuspensionField X)} =
      maximalIntegralCurveInterval (timeDependentSuspensionField X) (s, x) :=
    Set.ext fun _ ↦ mem_flowDomain
  have hc : IsMIntegralCurveAt c (timeDependentSuspensionField X) (t - s) :=
    (isMIntegralCurveOn_flowOf hW (s, x)).isMIntegralCurveAt
      (hdom ▸ isOpen_maximalIntegralCurveInterval.mem_nhds (mem_flowDomain.1 h))
  have hshift := (isMIntegralCurveAt_comp_sub (dt := s)).2 hc
  rw [sub_add_cancel] at hshift
  have hsnd := hshift.hasMFDerivAt.snd_curve
  have hpt : c (t - s) = (t, timeDependentFlowOf X s t x) :=
    flowOf_timeDependentSuspensionField h
  simp only [Function.comp_apply, timeDependentSuspensionField_snd, hpt] at hsnd
  -- `Prod.snd ∘ c ∘ (· - s)` is `fun u ↦ timeDependentFlowOf X s u x` by definition.
  exact hsnd

/-- The velocity of a curve of the time-dependent flow at every time `t` at which it is defined
is the field at time `t` at the current point. -/
theorem curveVelocity_timeDependentFlowOf (h : ((s, t), x) ∈ timeDependentFlowDomain X) :
    curveVelocity I (fun u ↦ timeDependentFlowOf X s u x) t =
      X t (timeDependentFlowOf X s t x) := by
  simpa only [curveVelocityWithin_univ] using curveVelocityWithin_eq_of_hasMFDerivWithinAt
    (hasMFDerivAt_timeDependentFlowOf hX h).hasMFDerivWithinAt uniqueDiffWithinAt_univ

/-- **Uniqueness of solutions.** A solution `γ` of the time-dependent equation on an open interval
containing `s` and `t` is the curve of the time-dependent flow through `γ s` at time `s`. -/
theorem timeDependentFlowOf_eq_of_hasMFDerivAt {γ : ℝ → M} {a b : ℝ}
    (hγ : ∀ u ∈ Ioo a b, HasMFDerivAt 𝓘(ℝ, ℝ) I γ u ((1 : ℝ →L[ℝ] ℝ).smulRight (X u (γ u))))
    (hs : s ∈ Ioo a b) (ht : t ∈ Ioo a b) :
    timeDependentFlowOf X s t (γ s) = γ t := by
  have h0 : (0 : ℝ) ∈ Ioo (a - s) (b - s) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hts : t - s ∈ Ioo (a - s) (b - s) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have heq := (isMIntegralCurveOn_lift (s := s) hγ).eqOn_maximalIntegralCurve (x := (s, γ s))
    (contMDiff_timeDependentSuspensionField hX) h0 (by simp) hts
  rw [timeDependentFlowOf_def, flowOf_apply, heq]
  simp only [add_sub_cancel]

/-- A point at which `X` vanishes at all times is fixed by the time-dependent flow. -/
theorem timeDependentFlowOf_eq_self_of_forall_eq_zero (hx : ∀ u, X u x = 0) (s t : ℝ) :
    timeDependentFlowOf X s t x = x :=
  timeDependentFlowOf_eq_of_hasMFDerivAt hX (γ := fun _ ↦ x) (a := min s t - 1)
    (b := max s t + 1) (fun u _ ↦ hasMFDerivAt_const_of_forall_eq_zero hx u)
    ⟨by linarith [min_le_left s t], by linarith [le_max_left s t]⟩
    ⟨by linarith [min_le_right s t], by linarith [le_max_right s t]⟩

/-- **The two-time composition law.** Flowing from time `r` to time `s` and then from `s` to `t`
is flowing from `r` to `t`, provided both steps are defined; the composite is then defined. -/
theorem timeDependentFlowOf_trans_of_mem {r : ℝ} (hrs : ((r, s), x) ∈ timeDependentFlowDomain X)
    (hst : ((s, t), timeDependentFlowOf X r s x) ∈ timeDependentFlowDomain X) :
    ((r, t), x) ∈ timeDependentFlowDomain X ∧
      timeDependentFlowOf X s t (timeDependentFlowOf X r s x) = timeDependentFlowOf X r t x := by
  have hpt := flowOf_timeDependentSuspensionField hrs
  have hst' : (t - s, flowOf (timeDependentSuspensionField X) (s - r) (r, x)) ∈
      flowDomain (timeDependentSuspensionField X) := by
    rw [hpt]
    exact hst
  obtain ⟨hmem, heq⟩ := flowOf_add (contMDiff_timeDependentSuspensionField hX) hrs hst'
  have htime : s - r + (t - s) = t - r := by ring
  rw [htime] at hmem heq
  refine ⟨hmem, ?_⟩
  rw [timeDependentFlowOf_def (s := r) (t := t), ← heq, hpt, timeDependentFlowOf_def]

/-- In finite dimensions, the domain of the time-dependent flow of a `C¹` field is open. -/
theorem isOpen_timeDependentFlowDomain [FiniteDimensional ℝ E] :
    IsOpen (timeDependentFlowDomain X) :=
  (isOpen_flowDomain (contMDiff_timeDependentSuspensionField hX)).preimage (by fun_prop)

end Flow

/-- In finite dimensions, the time-dependent flow of a `C^n` field, `1 ≤ n`, is jointly `C^n` in
the initial time, the final time and the initial point on its domain. -/
theorem contMDiffOn_timeDependentFlowOf [FiniteDimensional ℝ E] [T2Space M]
    [BoundarylessManifold I M] [IsManifold I 1 M] {n : ℕ∞} (hn : 1 ≤ n) [IsManifold I n M]
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent n
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M))) :
    ContMDiffOn ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) I n
      (fun p : (ℝ × ℝ) × M ↦ timeDependentFlowOf X p.1.1 p.1.2 p.2)
      (timeDependentFlowDomain X) := by
  have hflow := contMDiffOn_flowOf hn (contMDiff_timeDependentSuspensionField hX)
  have hs : ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) n
      (fun p : (ℝ × ℝ) × M ↦ p.1.1) :=
    contMDiff_fst.comp contMDiff_fst
  have ht : ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) n
      (fun p : (ℝ × ℝ) × M ↦ p.1.2) :=
    contMDiff_snd.comp contMDiff_fst
  have hg : ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod I)) n
      (fun p : (ℝ × ℝ) × M ↦ (p.1.2 - p.1.1, (p.1.1, p.2))) :=
    (ht.sub hs).prodMk (hs.prodMk contMDiff_snd)
  exact contMDiff_snd.comp_contMDiffOn (hflow.comp hg.contMDiffOn fun _ hp ↦ hp)

section Complete

variable [CompleteSpace E] [IsManifold I 1 M] [BoundarylessManifold I M]
  (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 1
    (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
include hX

/-- Every triple `((s, s), x)` lies in the domain of the time-dependent flow. -/
theorem mem_timeDependentFlowDomain_self (s : ℝ) (x : M) :
    ((s, s), x) ∈ timeDependentFlowDomain X := by
  rw [mem_timeDependentFlowDomain, sub_self]
  exact mem_flowDomain_zero (contMDiff_timeDependentSuspensionField hX) (s, x)

variable [T2Space M]

omit [CompleteSpace E] in
/-- Under a time-dependent field vanishing outside `K` at all times, the time-dependent flow keeps
every point in `K` together with its initial point. -/
theorem timeDependentFlowOf_mem_insert {K : Set M} (hXK : ∀ u, ∀ y ∉ K, X u y = 0)
    (h : ((s, t), x) ∈ timeDependentFlowDomain X) :
    timeDependentFlowOf X s t x ∈ insert x K := by
  by_contra hy
  rw [mem_insert_iff, not_or] at hy
  have hfix := fun u ↦ hXK u _ hy.2
  have hback := (timeDependentFlowOf_trans_of_mem hX h
    (mem_timeDependentFlowDomain_of_forall_eq_zero hfix t s)).2
  rw [timeDependentFlowOf_eq_self_of_forall_eq_zero hX hfix, timeDependentFlowOf_self] at hback
  exact hy.1 hback

/-- **A time-dependent field vanishing outside a fixed compact set has a complete suspension.**
The field may depend arbitrarily on time, and its suspension need not have compact support
in the time direction. -/
theorem isCompleteVectorField_timeDependentSuspensionField {K : Set M} (hK : IsCompact K)
    (hXK : ∀ u, ∀ y ∉ K, X u y = 0) :
    IsCompleteVectorField (timeDependentSuspensionField X) := by
  have hW := contMDiff_timeDependentSuspensionField hX
  rw [isCompleteVectorField_iff_maximalIntegralCurveInterval]
  rintro ⟨s, x⟩
  set W := timeDependentSuspensionField X
  have h0 : (0 : ℝ) ∈ maximalIntegralCurveInterval W (s, x) :=
    zero_mem_maximalIntegralCurveInterval hW.contMDiffAt
  -- On a bounded time interval `[a, b]`, the maximal integral curve stays in a compact set.
  have hmem {a b τ : ℝ} (hτ : τ ∈ maximalIntegralCurveInterval W (s, x)) (hτab : τ ∈ Icc a b) :
      maximalIntegralCurve W (s, x) τ ∈ Icc (s + a) (s + b) ×ˢ insert x K := by
    have hD : ((s, s + τ), x) ∈ timeDependentFlowDomain X := by
      rw [mem_timeDependentFlowDomain, add_sub_cancel_left]
      exact mem_flowDomain.2 hτ
    have hpt := flowOf_timeDependentSuspensionField hD
    rw [add_sub_cancel_left, flowOf_apply] at hpt
    rw [hpt]
    exact ⟨⟨by linarith [hτab.1], by linarith [hτab.2]⟩, timeDependentFlowOf_mem_insert hX hXK hD⟩
  have hC (a b : ℝ) : IsCompact (Icc (s + a) (s + b) ×ˢ insert x K) :=
    isCompact_Icc.prod (hK.insert x)
  refine maximalIntegralCurveInterval_eq_univ_of_not_bddAbove_not_bddBelow ?_ ?_
  · intro hbdd
    have hlub := isLUB_csSup ⟨0, h0⟩ hbdd
    obtain ⟨a, ha, hb0, hsub⟩ := exists_Ioo_subset_maximalIntegralCurveInterval_of_isLUB hlub
    obtain ⟨τ, hτ, hτC⟩ := (Filter.Eventually.and (Ioo_mem_nhdsLT hb0)
      (eventually_notMem_nhdsLT_maximalIntegralCurve hW hlub (hC a (sSup _)))).exists
    exact hτC (hmem (hsub ⟨by linarith [hτ.1], hτ.2⟩) ⟨by linarith [hτ.1], hτ.2.le⟩)
  · intro hbdd
    have hglb := isGLB_csInf ⟨0, h0⟩ hbdd
    obtain ⟨b, hb, ha0, hsub⟩ := exists_Ioo_subset_maximalIntegralCurveInterval_of_isGLB hglb
    obtain ⟨τ, hτ, hτC⟩ := (Filter.Eventually.and (Ioo_mem_nhdsGT ha0)
      (eventually_notMem_nhdsGT_maximalIntegralCurve hW hglb (hC (sInf _) b))).exists
    exact hτC (hmem (hsub ⟨hτ.1, by linarith [hτ.2]⟩) ⟨hτ.1.le, by linarith [hτ.2]⟩)

omit [CompleteSpace E] in
/-- **Flowing back undoes the flow.** If the flow from time `s` to time `t` is defined at `x`, then
the flow from `t` back to `s` is defined at its endpoint and returns it to `x`. -/
theorem timeDependentFlowOf_symm_of_mem (h : ((s, t), x) ∈ timeDependentFlowDomain X) :
    ((t, s), timeDependentFlowOf X s t x) ∈ timeDependentFlowDomain X ∧
      timeDependentFlowOf X t s (timeDependentFlowOf X s t x) = x := by
  obtain ⟨a, b, hs, ht, hab⟩ := exists_Ioo_of_mem_timeDependentFlowDomain h
  have hγ (u : ℝ) (hu : u ∈ Ioo a b) := hasMFDerivAt_timeDependentFlowOf hX (hab u hu)
  refine ⟨mem_timeDependentFlowDomain_of_hasMFDerivAt hγ ht hs, ?_⟩
  rw [timeDependentFlowOf_eq_of_hasMFDerivAt hX hγ ht hs, timeDependentFlowOf_self]

end Complete

/-- A jointly `C¹` time-dependent field on a finite-dimensional boundaryless manifold has a
local flow through every time and point. The solution through `(s, x)` starts at `x` at time `s`
and solves the nonautonomous equation for all times sufficiently close to `s`. -/
theorem exists_timeDependentFlow [FiniteDimensional ℝ E] [T2Space M]
    [IsManifold I 1 M] [BoundarylessManifold I M]
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 1
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M))) (s : ℝ) (x : M) :
    ∃ (U : Set (ℝ × M)) (Ψ : ℝ → ℝ × M → M), IsOpen U ∧ (s, x) ∈ U ∧
      (∀ p ∈ U, Ψ p.1 p = p.2) ∧
      ∀ p ∈ U, ∀ᶠ t in 𝓝 p.1, HasMFDerivAt 𝓘(ℝ, ℝ) I (fun u ↦ Ψ u p) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Ψ t p))) := by
  refine ⟨univ, fun t p ↦ timeDependentFlowOf X p.1 t p.2, isOpen_univ, mem_univ _,
    fun p _ ↦ timeDependentFlowOf_self X p.1 p.2, fun p _ ↦ ?_⟩
  have hdom : ∀ᶠ t in 𝓝 p.1, ((p.1, t), p.2) ∈ timeDependentFlowDomain X :=
    (by fun_prop : Continuous (fun t : ℝ ↦ ((p.1, t), p.2))).continuousAt.preimage_mem_nhds
      ((isOpen_timeDependentFlowDomain hX).mem_nhds (mem_timeDependentFlowDomain_self hX _ _))
  exact hdom.mono fun _ ht ↦ hasMFDerivAt_timeDependentFlowOf hX ht

/-! ### Time maps as partial diffeomorphisms -/

section PartialDiffeomorph

variable [FiniteDimensional ℝ E] [T2Space M] [BoundarylessManifold I M] [IsManifold I 1 M]
  {n : ℕ∞} (hn : 1 ≤ n) [IsManifold I n M]
  (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent n
    (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))

/-- The time map from `s` to `t` of the time-dependent flow of a jointly `C^n` field, `1 ≤ n`, on a
finite-dimensional boundaryless manifold, as a `C^n` partial diffeomorphism of `M`. Its source is
the open set of points from which the flow is defined from time `s` up to time `t`, its target is
the open set of points from which it is defined from time `t` back to time `s`, and its inverse is
the time map from `t` to `s`. No completeness is needed. -/
def timeDependentFlowPartialDiffeomorph (s t : ℝ) : PartialDiffeomorph I I M M n :=
  have hX₁ := hX.of_le (m := 1) (by exact_mod_cast hn)
  { toFun := timeDependentFlowOf X s t
    invFun := timeDependentFlowOf X t s
    source := {x | ((s, t), x) ∈ timeDependentFlowDomain X}
    target := {x | ((t, s), x) ∈ timeDependentFlowDomain X}
    map_source' _ hx := (timeDependentFlowOf_symm_of_mem hX₁ hx).1
    map_target' _ hx := (timeDependentFlowOf_symm_of_mem hX₁ hx).1
    left_inv' _ hx := (timeDependentFlowOf_symm_of_mem hX₁ hx).2
    right_inv' _ hx := (timeDependentFlowOf_symm_of_mem hX₁ hx).2
    open_source := (isOpen_timeDependentFlowDomain hX₁).preimage (by fun_prop)
    open_target := (isOpen_timeDependentFlowDomain hX₁).preimage (by fun_prop)
    contMDiffOn_toFun := (contMDiffOn_timeDependentFlowOf hn hX).comp
      ((contMDiff_const (c := (s, t))).prodMk contMDiff_id).contMDiffOn fun _ hx ↦ hx
    contMDiffOn_invFun := (contMDiffOn_timeDependentFlowOf hn hX).comp
      ((contMDiff_const (c := (t, s))).prodMk contMDiff_id).contMDiffOn fun _ hx ↦ hx }

/-- The partial diffeomorphism `timeDependentFlowPartialDiffeomorph` is the time-dependent flow. -/
@[simp]
theorem timeDependentFlowPartialDiffeomorph_apply (s t : ℝ) (x : M) :
    timeDependentFlowPartialDiffeomorph hn hX s t x = timeDependentFlowOf X s t x :=
  (rfl)

/-- The inverse of `timeDependentFlowPartialDiffeomorph` from `s` to `t` is the time-dependent
flow from `t` to `s`. -/
@[simp]
theorem timeDependentFlowPartialDiffeomorph_symm_apply (s t : ℝ) (x : M) :
    (timeDependentFlowPartialDiffeomorph hn hX s t).toPartialEquiv.symm x =
      timeDependentFlowOf X t s x :=
  (rfl)

/-- A point lies in the source of the time map from `s` to `t` exactly when the flow from `(s, x)`
is defined up to time `t`. -/
@[simp]
theorem mem_timeDependentFlowPartialDiffeomorph_source_iff {s t : ℝ} {x : M} :
    x ∈ (timeDependentFlowPartialDiffeomorph hn hX s t).source ↔
      ((s, t), x) ∈ timeDependentFlowDomain X :=
  (Iff.rfl)

/-- A point lies in the target of the time map from `s` to `t` exactly when the flow from `(t, x)`
is defined back to time `s`. -/
@[simp]
theorem mem_timeDependentFlowPartialDiffeomorph_target_iff {s t : ℝ} {x : M} :
    x ∈ (timeDependentFlowPartialDiffeomorph hn hX s t).target ↔
      ((t, s), x) ∈ timeDependentFlowDomain X :=
  (Iff.rfl)

end PartialDiffeomorph

/-! ### Complete suspensions -/

section Global

variable (hcomplete : IsCompleteVectorField (timeDependentSuspensionField X))
include hcomplete

/-- If the suspension is complete, the time-dependent flow is defined everywhere. -/
theorem timeDependentFlowDomain_eq_univ : timeDependentFlowDomain X = univ :=
  eq_univ_of_forall fun _ ↦ hcomplete.mem_flowDomain _ _

/-- If the suspension is complete, flowing from time `r` to time `s` and then from `s` to `t` is
flowing from `r` to `t`. -/
theorem timeDependentFlowOf_trans [T2Space M] [IsManifold I 1 M] [BoundarylessManifold I M]
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 1
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    (r s t : ℝ) (x : M) :
    timeDependentFlowOf X s t (timeDependentFlowOf X r s x) = timeDependentFlowOf X r t x :=
  (timeDependentFlowOf_trans_of_mem hX (hcomplete.mem_flowDomain _ _)
    (hcomplete.mem_flowDomain _ _)).2

variable [FiniteDimensional ℝ E] [T2Space M] [BoundarylessManifold I M] [IsManifold I 1 M]
  {n : ℕ∞} (hn : 1 ≤ n) [IsManifold I n M]
  (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent n
    (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
include hn hX

/-- If the suspension of a `C^n` time-dependent field, `1 ≤ n`, on a finite-dimensional manifold is
complete, its time-dependent flow is jointly `C^n` in both times and the initial point. -/
theorem contMDiff_timeDependentFlowOf :
    ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) I n
      (fun p : (ℝ × ℝ) × M ↦ timeDependentFlowOf X p.1.1 p.1.2 p.2) := by
  rw [← contMDiffOn_univ, ← timeDependentFlowDomain_eq_univ hcomplete]
  exact contMDiffOn_timeDependentFlowOf hn hX

/-- If the suspension of a `C^n` time-dependent field, `1 ≤ n`, on a finite-dimensional manifold is
complete, the time-dependent flow from time `s` to time `t` is a `C^n` diffeomorphism, with
inverse the time-dependent flow from `t` to `s`. -/
def timeDependentFlowDiffeomorph (s t : ℝ) : M ≃ₘ^n⟮I, I⟯ M :=
  have hX₁ := hX.of_le (m := 1) (by exact_mod_cast hn)
  { toFun := timeDependentFlowOf X s t
    invFun := timeDependentFlowOf X t s
    left_inv x := by
      rw [timeDependentFlowOf_trans hcomplete hX₁, timeDependentFlowOf_self]
    right_inv x := by
      rw [timeDependentFlowOf_trans hcomplete hX₁, timeDependentFlowOf_self]
    contMDiff_toFun := (contMDiff_timeDependentFlowOf hcomplete hn hX).comp
      ((contMDiff_const (c := (s, t))).prodMk contMDiff_id)
    contMDiff_invFun := (contMDiff_timeDependentFlowOf hcomplete hn hX).comp
      ((contMDiff_const (c := (t, s))).prodMk contMDiff_id) }

/-- The diffeomorphism `timeDependentFlowDiffeomorph` is the time-dependent flow. -/
@[simp]
theorem timeDependentFlowDiffeomorph_apply (s t : ℝ) (x : M) :
    timeDependentFlowDiffeomorph hcomplete hn hX s t x = timeDependentFlowOf X s t x :=
  (rfl)

/-- The inverse of `timeDependentFlowDiffeomorph` from `s` to `t` is the time-dependent flow from
`t` to `s`. -/
@[simp]
theorem timeDependentFlowDiffeomorph_symm_apply (s t : ℝ) (x : M) :
    (timeDependentFlowDiffeomorph hcomplete hn hX s t).symm x = timeDependentFlowOf X t s x :=
  (rfl)

/-- The **linearized time-dependent flow**: if the suspension of a `C^n` time-dependent field,
`1 ≤ n`, is complete, the differential of the flow from `s` to `t` at `x` is a continuous linear
equivalence `T_x M ≃ T_{φ_{s,t} x} M`, with inverse the differential of the flow from `t` to `s`. -/
def timeDependentFlowMFDerivEquiv (s t : ℝ) (x : M) :
    TangentSpace I x ≃L[ℝ] TangentSpace I (timeDependentFlowOf X s t x) :=
  (timeDependentFlowDiffeomorph hcomplete hn hX s t).mfderivToContinuousLinearEquiv
    (by exact_mod_cast (zero_lt_one.trans_le hn).ne') x

/-- The linearized time-dependent flow is the differential of the time map. -/
@[simp]
theorem coe_timeDependentFlowMFDerivEquiv (s t : ℝ) (x : M) :
    (timeDependentFlowMFDerivEquiv hcomplete hn hX s t x :
        TangentSpace I x →L[ℝ] TangentSpace I (timeDependentFlowOf X s t x)) =
      mfderiv I I (timeDependentFlowOf X s t) x :=
  Diffeomorph.mfderivToContinuousLinearEquiv_coe _ _

/-- The linearized time-dependent flow applies the differential of the time map. -/
@[simp]
theorem timeDependentFlowMFDerivEquiv_apply (s t : ℝ) (x : M) (v : TangentSpace I x) :
    timeDependentFlowMFDerivEquiv hcomplete hn hX s t x v =
      mfderiv I I (timeDependentFlowOf X s t) x v := by
  rw [← coe_timeDependentFlowMFDerivEquiv hcomplete hn hX]
  -- A continuous linear equivalence and its underlying continuous linear map agree pointwise.
  rfl

/-- The inverse of the linearized time-dependent flow from `s` to `t` at `x` is the differential
of the flow from `t` to `s` at the flowed point `φ_{s,t} x`. -/
@[simp]
theorem coe_timeDependentFlowMFDerivEquiv_symm (s t : ℝ) (x : M) :
    ((timeDependentFlowMFDerivEquiv hcomplete hn hX s t x).symm :
        TangentSpace I (timeDependentFlowOf X s t x) →L[ℝ] TangentSpace I x) =
      mfderiv I I (timeDependentFlowOf X t s) (timeDependentFlowOf X s t x) := by
  set e := timeDependentFlowMFDerivEquiv hcomplete hn hX s t x
  refine ContinuousLinearMap.ext fun v ↦ ?_
  -- The differential of the inverse diffeomorphism undoes that of the flow, at `e.symm v`; the
  -- diffeomorphism and its inverse unfold to the time maps.
  have h : mfderiv I I (timeDependentFlowOf X t s) (timeDependentFlowOf X s t x)
      (mfderiv I I (timeDependentFlowOf X s t) x (e.symm v)) = e.symm v :=
    (timeDependentFlowDiffeomorph hcomplete hn hX s t).mfderiv_symm_apply_mfderiv_apply
      (by exact_mod_cast (zero_lt_one.trans_le hn).ne') x (e.symm v)
  rw [← timeDependentFlowMFDerivEquiv_apply hcomplete hn hX s t,
    ContinuousLinearEquiv.apply_symm_apply] at h
  exact h.symm

/-- The inverse of the linearized time-dependent flow applies the differential of the reverse time
map at the flowed point. -/
@[simp]
theorem timeDependentFlowMFDerivEquiv_symm_apply (s t : ℝ) (x : M)
    (v : TangentSpace I (timeDependentFlowOf X s t x)) :
    (timeDependentFlowMFDerivEquiv hcomplete hn hX s t x).symm v =
      mfderiv I I (timeDependentFlowOf X t s) (timeDependentFlowOf X s t x) v := by
  rw [← coe_timeDependentFlowMFDerivEquiv_symm hcomplete hn hX]
  -- A continuous linear equivalence and its underlying continuous linear map agree pointwise.
  rfl

omit hn hX [IsManifold I n M] in
/-- **Derivative of a map moved by the time-dependent flow.** Let `τ : N → ℝ` and `v : N → M` have
derivatives `τ'` and `v'` at `z`, and let `X` be jointly `C¹` with complete suspension.
The map `y ↦ φ_{s, τ y} (v y)`, with `φ_{s, t} = timeDependentFlowOf X s t`, has derivative
`dφ_{s, τ z} ∘ v' + τ' ⊗ X_{τ z}` at `z`: the flow carries the derivative of `v`, and the varying
time adds the velocity of the flow at the moved point. -/
theorem hasMFDerivAt_timeDependentFlowOf_comp {F G N : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [TopologicalSpace N]
    [ChartedSpace G N]
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 1
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    {τ : N → ℝ} {v : N → M} {z : N} {τ' : TangentSpace J z →L[ℝ] ℝ}
    {v' : TangentSpace J z →L[ℝ] TangentSpace I (v z)}
    (hτ : HasMFDerivAt J 𝓘(ℝ, ℝ) τ z τ') (hv : HasMFDerivAt J I v z v') (s : ℝ) :
    HasMFDerivAt J I (fun y ↦ timeDependentFlowOf X s (τ y) (v y)) z
      (mfderiv I I (timeDependentFlowOf X s (τ z)) (v z) ∘L v' +
        τ'.smulRight (X (τ z) (timeDependentFlowOf X s (τ z) (v z)))) := by
  set Φ : ℝ × M → M := fun p ↦ timeDependentFlowOf X s p.1 p.2
  have hΦ : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) I Φ (τ z, v z) :=
    (((contMDiff_timeDependentFlowOf hcomplete le_rfl hX).comp
      (((contMDiff_const (c := s)).prodMk contMDiff_fst).prodMk contMDiff_snd)).mdifferentiable
        one_ne_zero) _
  refine (hΦ.hasMFDerivAt.comp z (hτ.prodMk hv)).congr_mfderiv (ContinuousLinearMap.ext fun a ↦ ?_)
  -- The composite sends `a` to the derivative of `Φ` on `(τ' a, v' a)`, which splits into the
  -- partial derivatives in the time and in the point; the first is the velocity of the flow.
  have hpart := mfderiv_prod_eq_add_apply (v := ((τ' a, v' a) : ℝ × E)) hΦ
  have htime : mfderiv 𝓘(ℝ, ℝ) I (fun t ↦ Φ (t, v z)) (τ z) =
      (1 : ℝ →L[ℝ] ℝ).smulRight (X (τ z) (timeDependentFlowOf X s (τ z) (v z))) :=
    (hasMFDerivAt_timeDependentFlowOf hX (hcomplete.mem_flowDomain _ _)).mfderiv
  dsimp only at hpart
  rw [htime] at hpart
  -- Tangent spaces of `ℝ` are `ℝ` only up to unfolding, so the sides are matched up to defeq:
  -- `(τ'.prod v') a` is `(τ' a, v' a)`, and the point derivative of `Φ` is that of the time map.
  refine hpart.trans ?_
  exact add_comm _ _

end Global

section Local

variable [FiniteDimensional ℝ E] [T2Space M] [IsManifold I 1 M] [BoundarylessManifold I M]

/-- Let `X` be a jointly `C^n` field, `1 ≤ n`, and let `σ`, `τ` and `c` be `C^n` at `z`, with the
flow from `(σ z, c z)` defined at time `τ z`. Then `y ↦ timeDependentFlowOf X (σ y) (τ y) (c y)`
is `C^n` at `z`. -/
theorem contMDiffAt_timeDependentFlowOf_comp {n : ℕ∞} (hn : 1 ≤ n)
    [IsManifold I n M] {F G N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [TopologicalSpace N] [ChartedSpace G N]
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent n
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    {σ τ : N → ℝ} {c : N → M} {z : N} (hσ : ContMDiffAt J 𝓘(ℝ, ℝ) n σ z)
    (hτ : ContMDiffAt J 𝓘(ℝ, ℝ) n τ z) (hc : ContMDiffAt J I n c z)
    (h : ((σ z, τ z), c z) ∈ timeDependentFlowDomain X) :
    ContMDiffAt J I n (fun y ↦ timeDependentFlowOf X (σ y) (τ y) (c y)) z := by
  have hflow : ContMDiffAt ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) I n
      (fun p : (ℝ × ℝ) × M ↦ timeDependentFlowOf X p.1.1 p.1.2 p.2) ((σ z, τ z), c z) :=
    (contMDiffOn_timeDependentFlowOf hn hX).contMDiffAt
      ((isOpen_timeDependentFlowDomain (hX.of_le (by exact_mod_cast hn))).mem_nhds h)
  exact hflow.comp (f := fun y ↦ ((σ y, τ y), c y)) z ((hσ.prodMk hτ).prodMk hc)

/-- The time map of the time-dependent flow of a jointly `C^n` field, `1 ≤ n`, is `C^n` at every
point at which it is defined. -/
theorem contMDiffAt_timeDependentFlowOf {n : ℕ∞} (hn : 1 ≤ n) [IsManifold I n M]
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent n
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    (h : ((s, t), x) ∈ timeDependentFlowDomain X) :
    ContMDiffAt I I n (timeDependentFlowOf X s t) x :=
  contMDiffAt_timeDependentFlowOf_comp hn hX contMDiffAt_const contMDiffAt_const contMDiffAt_id h

/-- **The linearized flow is `C^m` in time.** Let `X` be jointly `C^n`, `1 ≤ n`, with `m + 1 ≤ n`.
At every time `t` at which the flow from `(s, x)` is defined, the tangent vector
`dφ_{s, u} v` at `φ_{s, u}(x)` is a `C^m` function of `u` into the tangent bundle. -/
theorem contMDiffAt_totalSpaceMk_mfderiv_timeDependentFlowOf {m n : ℕ∞} (hn : 1 ≤ n)
    (hmn : m + 1 ≤ n) [IsManifold I n M]
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent n
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    (v : TangentSpace I x) (h : ((s, t), x) ∈ timeDependentFlowDomain X) :
    ContMDiffAt 𝓘(ℝ, ℝ) I.tangent m (fun u ↦ Bundle.TotalSpace.mk' E (timeDependentFlowOf X s u x)
      (mfderiv I I (timeDependentFlowOf X s u) x v)) t := by
  set W := {q : ℝ × M | ((s, q.1), q.2) ∈ timeDependentFlowDomain X}
  have hW : IsOpen W :=
    (isOpen_timeDependentFlowDomain (hX.of_le (by exact_mod_cast hn))).preimage (by fun_prop)
  have hf : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I n (fun q : ℝ × M ↦ timeDependentFlowOf X s q.1 q.2)
      W := fun q hq ↦ (contMDiffAt_timeDependentFlowOf_comp hn hX contMDiffAt_const
        contMDiffAt_fst contMDiffAt_snd hq).contMDiffWithinAt
  -- The tangent vector `(0, v)` to `ℝ × M` at `(u, x)` varies smoothly with `u`.
  have hlift : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I).tangent m
      (fun u : ℝ ↦ (equivTangentBundleProd 𝓘(ℝ, ℝ) ℝ I M).symm (⟨u, 0⟩, ⟨x, v⟩)) :=
    contMDiff_equivTangentBundleProd_symm.comp
      ((contMDiff_tangentBundle_mk_zero contMDiff_id).prodMk
        (contMDiff_tangentBundle_mk_constBase (v := fun _ ↦ @id E v) contMDiff_const x))
  have hmn' : (m : WithTop ℕ∞) + 1 ≤ n := by exact_mod_cast hmn
  have htan := ((hf.contMDiffOn_tangentMapWithin hmn' hW.uniqueMDiffOn)
    ((equivTangentBundleProd 𝓘(ℝ, ℝ) ℝ I M).symm (⟨t, 0⟩, ⟨x, v⟩)) h).contMDiffAt
    (((FiberBundle.continuous_proj (ℝ × E) (TangentSpace (𝓘(ℝ, ℝ).prod I) : ℝ × M → Type _)
      ).isOpen_preimage _ hW).mem_nhds h)
  refine (htan.comp t (hlift t)).congr_of_eventuallyEq ?_
  filter_upwards [(continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds
    (hW.mem_nhds (show (t, x) ∈ W from h))] with u (hu : (u, x) ∈ W)
  have hfu : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) I
      (fun q : ℝ × M ↦ timeDependentFlowOf X s q.1 q.2) (u, x) :=
    ((hf _ hu).contMDiffAt (hW.mem_nhds hu)).mdifferentiableAt
      (by exact_mod_cast (one_pos.trans_le hn).ne')
  -- The derivative in the second factor is the full derivative on `(0, v)`.
  have hcurry : mfderiv I I (timeDependentFlowOf X s u) x =
      (mfderiv (𝓘(ℝ, ℝ).prod I) I (fun q : ℝ × M ↦ timeDependentFlowOf X s q.1 q.2) (u, x)).comp
        (mfderiv I (𝓘(ℝ, ℝ).prod I) (fun y : M ↦ (u, y)) x) :=
    mfderiv_comp_of_eq hfu (mdifferentiableAt_const.prodMk mdifferentiableAt_id) rfl
  rw [mfderiv_prod_right] at hcurry
  -- `(equivTangentBundleProd _ _ _ _).symm` pairs the base points and the tangent vectors.
  have hpt : (equivTangentBundleProd 𝓘(ℝ, ℝ) ℝ I M).symm (⟨u, 0⟩, ⟨x, v⟩) = ⟨(u, x), (0, v)⟩ :=
    rfl
  rw [Function.comp_apply, hpt]
  simp only [tangentMapWithin, mfderivWithin_of_isOpen hW hu, hcurry]
  -- `mfderiv_prod_right` types `inr` into `TangentSpace 𝓘(ℝ, ℝ) u × TangentSpace I x`, which is
  -- `TangentSpace (𝓘(ℝ, ℝ).prod I) (u, x)` only up to unfolding `TangentSpace`, so
  -- `ContinuousLinearMap.comp_apply` and `inr_apply` do not rewrite here. The goal is the
  -- definitional equality `(D.comp (inr ℝ _ _)) v = D (0, v)` inside `TotalSpace.mk'`.
  rfl

variable (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 1
    (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
include hX

/-- Near a point of the domain of the flow from time `s`, the trajectories through the points of
a continuous family of initial points solve the field equation at time `t`. -/
theorem eventually_curveVelocity_timeDependentFlowOf_eq {α : Type*} [TopologicalSpace α]
    {c : α → M} {q : α} (hc : ContinuousAt c q)
    (h : ((s, t), c q) ∈ timeDependentFlowDomain X) :
    ∀ᶠ r in 𝓝 q, curveVelocity I (fun u ↦ timeDependentFlowOf X s u (c r)) t =
      X t (timeDependentFlowOf X s t (c r)) := by
  filter_upwards [(continuousAt_const.prodMk hc).preimage_mem_nhds
    ((isOpen_timeDependentFlowDomain hX).mem_nhds h)] with r hr
  exact curveVelocity_timeDependentFlowOf hX hr

/-- The transverse velocity of the trajectories through a curve of initial points is the
derivative of the flow applied to the velocity of the curve. -/
theorem curveVelocity_timeDependentFlowOf_comp {c : ℝ → M} {q : ℝ}
    (hc : MDifferentiableAt 𝓘(ℝ, ℝ) I c q) (h : ((s, t), c q) ∈ timeDependentFlowDomain X) :
    curveVelocity I (fun a ↦ timeDependentFlowOf X s t (c a)) q =
      mfderiv I I (timeDependentFlowOf X s t) (c q) (curveVelocity I c q) := by
  have hφ : MDifferentiableAt I I (timeDependentFlowOf X s t) (c q) :=
    (contMDiffAt_timeDependentFlowOf (n := 1) le_rfl hX h).mdifferentiableAt one_ne_zero
  simpa only [curveVelocityWithin_univ, Function.comp_def] using
    curveVelocityWithin_map hφ uniqueDiffWithinAt_univ hc.mdifferentiableWithinAt

/-- **The derivative of the flow is injective.** Wherever the time-dependent flow from `s` to `t`
is defined at `x`, flowing back from `t` to `s` is a left inverse near `x`, so `dφ_{s, t}` is
injective at `x`. No completeness of the field is needed. -/
theorem injective_mfderiv_timeDependentFlowOf (h : ((s, t), x) ∈ timeDependentFlowDomain X) :
    Function.Injective (mfderiv I I (timeDependentFlowOf X s t) x) := by
  have hφ : MDifferentiableAt I I (timeDependentFlowOf X s t) x :=
    (contMDiffAt_timeDependentFlowOf (n := 1) le_rfl hX h).mdifferentiableAt one_ne_zero
  have hψ : MDifferentiableAt I I (timeDependentFlowOf X t s) (timeDependentFlowOf X s t x) :=
    (contMDiffAt_timeDependentFlowOf (n := 1) le_rfl hX
      (timeDependentFlowOf_symm_of_mem hX h).1).mdifferentiableAt one_ne_zero
  have heq : timeDependentFlowOf X t s ∘ timeDependentFlowOf X s t =ᶠ[𝓝 x] id := by
    filter_upwards [(continuousAt_const.prodMk continuousAt_id).preimage_mem_nhds
      ((isOpen_timeDependentFlowDomain hX).mem_nhds h)] with y hy
    exact (timeDependentFlowOf_symm_of_mem hX hy).2
  exact mfderiv_injective_of_comp_eventuallyEq_id hψ hφ heq

end Local

end TauCeti
