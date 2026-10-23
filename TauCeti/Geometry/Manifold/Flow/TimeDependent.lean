/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.Complete
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import TauCeti.Geometry.Manifold.MFDeriv.Curve

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
* `TauCeti.timeDependentFlowDiffeomorph`: for a complete suspension, the time map from `s` to `t`
  as a `C^n` diffeomorphism.

## Main results

* `TauCeti.flowOf_timeDependentSuspensionField`: the flow of the suspension advances the clock at
  unit speed and moves the point along the time-dependent flow.
* `TauCeti.isOpen_timeDependentFlowDomain` and `TauCeti.contMDiffOn_timeDependentFlowOf`: the
  domain is open and the flow is jointly `C^n` on it.
* `TauCeti.hasMFDerivAt_timeDependentFlowOf`: the curves of the flow solve `γ' u = X u (γ u)`.
* `TauCeti.timeDependentFlowOf_eq_of_hasMFDerivAt`: every solution on an open interval is a curve
  of the flow.
* `TauCeti.timeDependentFlowOf_trans_of_mem` and `TauCeti.timeDependentFlowOf_trans`: the two-time
  composition law, where it is defined, and everywhere for a complete suspension.
* `TauCeti.isCompleteVectorField_timeDependentSuspensionField`: a time-dependent field vanishing
  outside a fixed compact set has a complete suspension.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Theorem 9.48
  (the fundamental theorem on time-dependent flows).
* M. W. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Chapter 8, §1 (isotopy extension
  by compactly supported time-dependent vector fields).

The suspension construction is the manifold counterpart of `TauCeti.timeDependentSuspension` in
`TauCeti.Dynamics.Flow.TimeDependent`; the maximal flow is Tau Ceti's `TauCeti.flowOf`.
-/

public section

noncomputable section

open Set
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

/-- The suspension of a jointly `C^n` time-dependent vector field is a `C^n` vector field on
`ℝ × M`. -/
theorem contMDiff_timeDependentSuspensionField [IsManifold I 1 M] {n : ℕ∞ω}
    {X : ℝ → (x : M) → TangentSpace I x}
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent n
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M))) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I).tangent n
      (fun p : ℝ × M ↦ (⟨p, timeDependentSuspensionField X p⟩ :
        TangentBundle (𝓘(ℝ, ℝ).prod I) (ℝ × M))) := by
  have hclock : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ).tangent n
      (fun s : ℝ ↦ (⟨s, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
    contMDiff_vectorSpace_iff_contDiff.2 contDiff_const
  exact (contMDiff_equivTangentBundleProd_symm (I := 𝓘(ℝ, ℝ)) (M := ℝ) (I' := I) (M' := M)).comp
    ((hclock.comp contMDiff_fst).prodMk hX)

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

section Flow

variable [T2Space M] [IsManifold I 1 M] [BoundarylessManifold I M]
  (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 1
    (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
include hX

/-- **The clock of the suspension runs at unit speed.** Along the maximal integral curve of the
suspension through `(s, x)`, the time coordinate at flow time `τ` is `s + τ`. -/
theorem fst_flowOf_timeDependentSuspensionField {τ : ℝ}
    (hτ : (τ, (s, x)) ∈ flowDomain (timeDependentSuspensionField X)) :
    (flowOf (timeDependentSuspensionField X) τ (s, x)).1 = s + τ := by
  have hW := contMDiff_timeDependentSuspensionField hX
  set γ := maximalIntegralCurve (timeDependentSuspensionField X) (s, x)
  set J := maximalIntegralCurveInterval (timeDependentSuspensionField X) (s, x)
  have h0 : (0 : ℝ) ∈ J := by
    obtain ⟨δ, a, b, hδ, hδ0, h0, -, -⟩ :=
      exists_isMIntegralCurveOn_maximalIntegralCurve_eq (mem_flowDomain.1 hτ)
    exact hδ.subset_maximalIntegralCurveInterval h0 hδ0 h0
  -- On the open interval `J`, the clock coordinate minus the flow time has derivative zero.
  have hderiv (u : ℝ) (hu : u ∈ J) : HasDerivAt (fun r ↦ (γ r).1 - r) 0 u := by
    have hγ := ((isMIntegralCurveOn_maximalIntegralCurve hW).isMIntegralCurveAt
      (isOpen_maximalIntegralCurveInterval.mem_nhds hu)).hasMFDerivAt
    -- A `HasDerivAt` statement is by definition a `HasFDerivAt` statement with derivative
    -- `smulRight 1`, and the clock velocity lies in `TangentSpace 𝓘(ℝ, ℝ) _`, which is `ℝ`.
    have hfst : HasDerivAt (fun r ↦ (γ r).1) (timeDependentSuspensionField X (γ u)).1 u :=
      hasMFDerivAt_iff_hasFDerivAt.1 (Manifold.hasMFDerivAt_fst_comp_curve hγ)
    rw [timeDependentSuspensionField_fst] at hfst
    have h := hfst.sub (hasDerivAt_id' u)
    rwa [sub_self] at h
  have hconst := isOpen_maximalIntegralCurveInterval.is_const_of_deriv_eq_zero
    isPreconnected_maximalIntegralCurveInterval
    (fun u hu ↦ (hderiv u hu).differentiableAt.differentiableWithinAt)
    (fun u hu ↦ (hderiv u hu).deriv) (mem_flowDomain.1 hτ) h0
  have hγ0 : γ 0 = (s, x) := maximalIntegralCurve_zero h0
  rw [hγ0] at hconst
  rw [flowOf_apply]
  linarith

/-- **The flow of the suspension** through `(s, x)` reaches the point
`(t, timeDependentFlowOf X s t x)` after time `t - s`. -/
theorem flowOf_timeDependentSuspensionField (h : ((s, t), x) ∈ timeDependentFlowDomain X) :
    flowOf (timeDependentSuspensionField X) (t - s) (s, x) = (t, timeDependentFlowOf X s t x) :=
  Prod.ext (by rw [fst_flowOf_timeDependentSuspensionField hX h]; ring) (rfl)

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
  have hsnd := Manifold.hasMFDerivAt_snd_comp_curve hshift.hasMFDerivAt
  have hpt : c (t - s) = (t, timeDependentFlowOf X s t x) :=
    flowOf_timeDependentSuspensionField hX h
  simp only [Function.comp_apply, timeDependentSuspensionField_snd, hpt] at hsnd
  -- `Prod.snd ∘ c ∘ (· - s)` is `fun u ↦ timeDependentFlowOf X s u x` by definition.
  exact hsnd

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
  have hpt := flowOf_timeDependentSuspensionField hX hrs
  have hst' : (t - s, flowOf (timeDependentSuspensionField X) (s - r) (r, x)) ∈
      flowDomain (timeDependentSuspensionField X) := by
    rw [hpt]
    exact hst
  obtain ⟨hmem, heq⟩ := flowOf_add (contMDiff_timeDependentSuspensionField hX) hrs hst'
  rw [show s - r + (t - s) = t - r by ring] at hmem heq
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

/-- The time-dependent flow from time `s` to time `s` is the identity. -/
@[simp]
theorem timeDependentFlowOf_self (s : ℝ) (x : M) : timeDependentFlowOf X s s x = x := by
  rw [timeDependentFlowOf_def, sub_self, flowOf_zero (contMDiff_timeDependentSuspensionField hX)]

variable [T2Space M]

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
  rw [timeDependentFlowOf_eq_self_of_forall_eq_zero hX hfix, timeDependentFlowOf_self hX] at hback
  exact hy.1 hback

/-- **A time-dependent field vanishing outside a fixed compact set has a complete suspension.**
Along a maximal integral curve of the suspension the clock runs at unit speed and the point stays
in the compact set together with its initial point, so the escape lemma rules out a finite
endpoint of the maximal interval. -/
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
    have hpt := flowOf_timeDependentSuspensionField hX hD
    rw [add_sub_cancel_left, flowOf_apply] at hpt
    rw [hpt]
    exact ⟨⟨by linarith [hτab.1], by linarith [hτab.2]⟩, timeDependentFlowOf_mem_insert hX hXK hD⟩
  have hC (a b : ℝ) : IsCompact (Icc (s + a) (s + b) ×ˢ insert x K) :=
    isCompact_Icc.prod (hK.insert x)
  refine maximalIntegralCurveInterval_eq_univ_of_not_bddAbove_not_bddBelow h0 ?_ ?_
  · intro hbdd
    have hlub := isLUB_csSup ⟨0, h0⟩ hbdd
    obtain ⟨a, ha, hb0, hsub⟩ := exists_Ioo_subset_maximalIntegralCurveInterval_of_isLUB h0 hlub
    obtain ⟨τ, hτ, hτC⟩ := (Filter.Eventually.and (Ioo_mem_nhdsLT hb0)
      (eventually_notMem_nhdsLT_maximalIntegralCurve hW h0 hlub (hC a (sSup _)))).exists
    exact hτC (hmem (hsub ⟨by linarith [hτ.1], hτ.2⟩) ⟨by linarith [hτ.1], hτ.2.le⟩)
  · intro hbdd
    have hglb := isGLB_csInf ⟨0, h0⟩ hbdd
    obtain ⟨b, hb, ha0, hsub⟩ := exists_Ioo_subset_maximalIntegralCurveInterval_of_isGLB h0 hglb
    obtain ⟨τ, hτ, hτC⟩ := (Filter.Eventually.and (Ioo_mem_nhdsGT ha0)
      (eventually_notMem_nhdsGT_maximalIntegralCurve hW h0 hglb (hC (sInf _) b))).exists
    exact hτC (hmem (hsub ⟨hτ.1, by linarith [hτ.2]⟩) ⟨hτ.1.le, by linarith [hτ.2]⟩)

end Complete

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
      rw [timeDependentFlowOf_trans hcomplete hX₁, timeDependentFlowOf_self hX₁]
    right_inv x := by
      rw [timeDependentFlowOf_trans hcomplete hX₁, timeDependentFlowOf_self hX₁]
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

end Global

end TauCeti
