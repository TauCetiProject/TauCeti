/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.IntegralCurve.Flow

/-!
# The maximal flow of a vector field

This file presents Tau Ceti's maximal integral curves as a partial flow whose arguments are ordered
as time followed by initial point.  The domain and value are adapters for
`maximalIntegralCurveFlowDomain` and `maximalIntegralCurve`, not independent constructions.  The
domain-aware group law records both the value equation and the condition that the composite time
remains in the interval of existence.

For finite-dimensional model spaces, the existing smooth-dependence theorem for maximal integral
curves gives joint openness of the domain and joint smoothness of the flow.  The escape theorem says
that a maximal trajectory approaching a finite right endpoint eventually leaves every compact set.

## Main declarations

* `TauCeti.flowDomain`: the domain of the maximal flow, in `(time, point)` order.
* `TauCeti.flowOf`: the maximal flow, total with junk values outside `flowDomain`.
* `TauCeti.isOpen_flowDomain`: openness of the domain in finite dimensions.
* `TauCeti.contMDiffOn_flowOf`: joint regularity of the flow in finite dimensions.
* `TauCeti.flowOf_add`: the domain-aware group law.
* `TauCeti.eventually_flowOf_notMem`: escape from compact sets at a finite right endpoint.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 9.
-/

public section

noncomputable section

open Function Manifold Set
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-- The domain of the maximal flow in `(time, point)` order.  This is
`maximalIntegralCurveFlowDomain` transported by `Prod.swap`. -/
def flowDomain (v : (x : M) → TangentSpace I x) : Set (ℝ × M) :=
  Prod.swap ⁻¹' maximalIntegralCurveFlowDomain v

/-- The maximal flow of a vector field, total with the same junk values as
`maximalIntegralCurve`. -/
def flowOf (v : (x : M) → TangentSpace I x) (t : ℝ) (x : M) : M :=
  maximalIntegralCurve v x t

/-- The maximal-flow adapter evaluates to the existing maximal integral curve. -/
@[simp]
theorem flowOf_apply (v : (x : M) → TangentSpace I x) (t : ℝ) (x : M) :
    flowOf v t x = maximalIntegralCurve v x t :=
  (rfl)

/-- Membership in the maximal-flow domain is membership in the maximal interval through the
initial point. -/
@[simp]
theorem mem_flowDomain {v : (x : M) → TangentSpace I x} {t : ℝ} {x : M} :
    (t, x) ∈ flowDomain v ↔ t ∈ maximalIntegralCurveInterval v x := by
  simp only [flowDomain, mem_preimage, Prod.swap_prod_mk,
    mem_maximalIntegralCurveFlowDomain]

variable [T2Space M] [BoundarylessManifold I M] [CompleteSpace E]

omit [CompleteSpace E] in
/-- The trajectory `t ↦ flowOf v t x` is an integral curve on its maximal interval of
existence. -/
theorem isMIntegralCurveOn_flowOf [IsManifold I 1 M] {v : (x : M) → TangentSpace I x}
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) (x : M) :
    IsMIntegralCurveOn (fun t ↦ flowOf v t x) v {t | (t, x) ∈ flowDomain v} := by
  have hcurve : (fun t ↦ flowOf v t x) = maximalIntegralCurve v x := by
    funext t
    exact flowOf_apply v t x
  have hdomain : {t | (t, x) ∈ flowDomain v} = maximalIntegralCurveInterval v x := by
    ext t
    exact mem_flowDomain
  rw [hcurve, hdomain]
  exact isMIntegralCurveOn_maximalIntegralCurve hv

omit [T2Space M] in
/-- Time zero belongs to the maximal-flow domain. -/
theorem mem_flowDomain_zero [IsManifold I 1 M] {v : (x : M) → TangentSpace I x}
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) (x : M) :
    ((0 : ℝ), x) ∈ flowDomain v := by
  rw [mem_flowDomain]
  exact zero_mem_maximalIntegralCurveInterval hv.contMDiffAt

omit [T2Space M] in
/-- The maximal flow fixes every point at time zero. -/
theorem flowOf_zero [IsManifold I 1 M] {v : (x : M) → TangentSpace I x}
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) (x : M) :
    flowOf v 0 x = x := by
  rw [flowOf_apply]
  exact maximalIntegralCurve_zero (mem_flowDomain.mp (mem_flowDomain_zero hv x))

omit [CompleteSpace E] in
/-- In finite dimensions, the domain of the maximal flow is jointly open in time and initial
point. -/
theorem isOpen_flowDomain [FiniteDimensional ℝ E] [IsManifold I 1 M]
    {v : (x : M) → TangentSpace I x}
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) :
    IsOpen (flowDomain v) := by
  simpa only [flowDomain] using
    (isOpen_maximalIntegralCurveFlowDomain hv).preimage continuous_swap

omit [CompleteSpace E] in
/-- In finite dimensions, a `C^n` vector field has a jointly `C^n` maximal flow on its domain. -/
theorem contMDiffOn_flowOf [FiniteDimensional ℝ E] {n : ℕ∞} (hn : 1 ≤ n)
    [IsManifold I 1 M] [IsManifold I n M] {v : (x : M) → TangentSpace I x}
    (hv : CMDiff n (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) I n (fun p : ℝ × M ↦ flowOf v p.1 p.2)
      (flowDomain v) := by
  have h := (contMDiffOn_maximalIntegralCurve hn hv).comp
    (contMDiff_snd.prodMk contMDiff_fst).contMDiffOn fun _ hp ↦ hp
  have hfun : ((fun p : M × ℝ ↦ maximalIntegralCurve v p.1 p.2) ∘
      fun p : ℝ × M ↦ (p.2, p.1)) =
    fun p : ℝ × M ↦ flowOf v p.1 p.2 := by
    funext p
    exact (flowOf_apply v p.1 p.2).symm
  have hdomain : (fun p : ℝ × M ↦ (p.2, p.1)) ⁻¹'
      maximalIntegralCurveFlowDomain v = flowDomain v := by
    rfl
  rw [hfun, hdomain] at h
  exact h

omit [CompleteSpace E] in
/-- The domain-aware group law for the maximal flow.  If time `s` is defined at `x` and time `t`
is defined after flowing for `s`, then time `s + t` is defined at `x` and gives the same value. -/
theorem flowOf_add [IsManifold I 1 M] {v : (x : M) → TangentSpace I x}
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) {s t : ℝ} {x : M}
    (hs : (s, x) ∈ flowDomain v) (ht : (t, flowOf v s x) ∈ flowDomain v) :
    (s + t, x) ∈ flowDomain v ∧ flowOf v t (flowOf v s x) = flowOf v (s + t) x := by
  have hs' : s ∈ maximalIntegralCurveInterval v x := mem_flowDomain.mp hs
  have ht' : t ∈ maximalIntegralCurveInterval v (maximalIntegralCurve v x s) := by
    simpa only [flowOf_apply] using mem_flowDomain.mp ht
  have hst : s + t ∈ maximalIntegralCurveInterval v x :=
    (mem_maximalIntegralCurveInterval_maximalIntegralCurve_iff hv hs').mp ht'
  refine ⟨mem_flowDomain.mpr hst, ?_⟩
  simpa only [flowOf_apply] using (maximalIntegralCurve_add hv hs' hst).symm

/-- At a finite right endpoint of a maximal interval, the trajectory eventually leaves every
compact set. -/
theorem eventually_flowOf_notMem [IsManifold I 1 M] {v : (x : M) → TangentSpace I x}
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) {x : M} {b : ℝ}
    (hb : IsLUB {t | (t, x) ∈ flowDomain v} b) {K : Set M} (hK : IsCompact K) :
    ∀ᶠ t in 𝓝[<] b, flowOf v t x ∉ K := by
  have hdomain : {t | (t, x) ∈ flowDomain v} = maximalIntegralCurveInterval v x := by
    ext t
    exact mem_flowDomain
  have hb' : IsLUB (maximalIntegralCurveInterval v x) b := by
    rw [← hdomain]
    exact hb
  simpa only [flowOf_apply] using
    eventually_notMem_nhdsLT_maximalIntegralCurve hv
      (mem_flowDomain.mp (mem_flowDomain_zero hv x)) hb' hK

end TauCeti
