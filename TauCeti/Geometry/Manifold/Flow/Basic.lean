/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.IntegralCurve.Flow
public import TauCeti.Geometry.Manifold.MFDeriv.Curve

/-!
# The maximal flow of a vector field

This file presents Tau Ceti's maximal integral curves as a partial flow whose arguments are ordered
as time followed by initial point.  The domain and value are adapters for
`maximalIntegralCurveFlowDomain` and `maximalIntegralCurve`, not independent constructions.  The
domain-aware group law records both the value equation and the condition that the composite time
remains in the interval of existence.

For finite-dimensional model spaces, the existing smooth-dependence theorem for maximal integral
curves gives joint openness of the domain and joint smoothness of the flow, so flowing a `C^n`
family of points for a `C^n` family of times is again `C^n`.  Along a trajectory, a function changes
at the rate of its derivative in the direction of the vector field.  The escape theorem says that a
maximal trajectory approaching a finite right endpoint eventually leaves every compact set.

## Main declarations

* `TauCeti.flowDomain`: the domain of the maximal flow, in `(time, point)` order.
* `TauCeti.flowOf`: the maximal flow, total with junk values outside `flowDomain`.
* `TauCeti.isOpen_flowDomain`: openness of the domain in finite dimensions.
* `TauCeti.contMDiffOn_flowOf`: joint regularity of the flow in finite dimensions.
* `TauCeti.contMDiffAt_flowOf_comp`: flowing `C^n` families of points for `C^n` families of times.
* `TauCeti.hasDerivAt_comp_flowOf`: the time derivative of a function along a trajectory.
* `TauCeti.flowOf_add`: the domain-aware group law.
* `TauCeti.flowOf_neg_flowOf`: flowing backwards undoes flowing forwards.
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
/-- A global integral curve of a `C¹` field is the maximal flow through its initial value.
No completeness hypothesis is needed on the field or the model space. -/
theorem flowOf_eq_of_isMIntegralCurve [IsManifold I 1 M]
    {v : (x : M) → TangentSpace I x}
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    {γ : ℝ → M} (hγ : IsMIntegralCurve γ v) (t : ℝ) :
    flowOf v t (γ 0) = γ t := by
  have h := (hγ.isMIntegralCurveOn (Ioo (-(|t| + 1)) (|t| + 1))).eqOn_maximalIntegralCurve hv
    (by constructor <;> linarith [abs_nonneg t]) rfl
  have ht : t ∈ Ioo (-(|t| + 1)) (|t| + 1) :=
    ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
  rw [flowOf_apply]
  exact h ht

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
/-- In finite dimensions, flowing a `C^n` family of initial points for a `C^n` family of times is
`C^n`, wherever the flow is defined. -/
theorem contMDiffAt_flowOf_comp [FiniteDimensional ℝ E] {n : ℕ∞} (hn : 1 ≤ n)
    [IsManifold I 1 M] [IsManifold I n M] {v : (x : M) → TangentSpace I x}
    (hv : CMDiff n (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
    {τ : N → ℝ} {f : N → M} {z : N} (hτ : ContMDiffAt J 𝓘(ℝ) n τ z)
    (hf : ContMDiffAt J I n f z) (hz : (τ z, f z) ∈ flowDomain v) :
    ContMDiffAt J I n (fun y ↦ flowOf v (τ y) (f y)) z :=
  ((contMDiffOn_flowOf hn hv).contMDiffAt
    ((isOpen_flowDomain (hv.of_le (by exact_mod_cast hn))).mem_nhds hz)).comp z (hτ.prodMk hf)

omit [CompleteSpace E] in
/-- **Derivative along a flow line.** The derivative in time of a function `g` along the
trajectory of `v` through `x` is the derivative of `g` in the direction of `v`. -/
theorem hasDerivAt_comp_flowOf [IsManifold I 1 M] {v : (x : M) → TangentSpace I x}
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {g : M → F} {t : ℝ} {x : M}
    (hx : (t, x) ∈ flowDomain v) (hg : MDifferentiableAt I 𝓘(ℝ, F) g (flowOf v t x)) :
    HasDerivAt (fun s ↦ g (flowOf v s x)) (mvfderiv I g (flowOf v t x) (v (flowOf v t x))) t := by
  have hopen : {s | (s, x) ∈ flowDomain v} ∈ 𝓝 t := by
    simpa only [mem_flowDomain, ofPred_mem_eq] using
      isOpen_maximalIntegralCurveInterval.mem_nhds (mem_flowDomain.mp hx)
  exact Manifold.hasDerivAt_comp_curve hg
    (((isMIntegralCurveOn_flowOf hv x).isMIntegralCurveAt hopen).hasMFDerivAt)

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

/-- The flow can be run backwards along a trajectory: if time `t` is defined at `x`, then time
`-t` is defined at `flowOf v t x`. -/
theorem neg_mem_flowDomain_flowOf [IsManifold I 1 M] {v : (x : M) → TangentSpace I x}
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) {t : ℝ} {x : M}
    (ht : (t, x) ∈ flowDomain v) : (-t, flowOf v t x) ∈ flowDomain v := by
  rw [mem_flowDomain, flowOf_apply,
    mem_maximalIntegralCurveInterval_maximalIntegralCurve_iff hv (mem_flowDomain.mp ht),
    add_neg_cancel, ← mem_flowDomain]
  exact mem_flowDomain_zero hv x

/-- Flowing for time `-t` undoes flowing for time `t`. -/
theorem flowOf_neg_flowOf [IsManifold I 1 M] {v : (x : M) → TangentSpace I x}
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) {t : ℝ} {x : M}
    (ht : (t, x) ∈ flowDomain v) : flowOf v (-t) (flowOf v t x) = x := by
  rw [(flowOf_add hv ht (neg_mem_flowDomain_flowOf hv ht)).2, add_neg_cancel, flowOf_zero hv]

/-- If `x` returns to itself at time `t`, it does so at every natural multiple of `t`. -/
theorem flowOf_natCast_mul_of_flowOf_eq [IsManifold I 1 M] {v : (x : M) → TangentSpace I x}
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) {t : ℝ} {x : M}
    (ht : (t, x) ∈ flowDomain v) (hx : flowOf v t x = x) (k : ℕ) :
    ((k : ℝ) * t, x) ∈ flowDomain v ∧ flowOf v ((k : ℝ) * t) x = x := by
  induction k with
  | zero => simpa only [Nat.cast_zero, zero_mul] using ⟨mem_flowDomain_zero hv x, flowOf_zero hv x⟩
  | succ k ih =>
    obtain ⟨hk, hkx⟩ := ih
    obtain ⟨hmem, heq⟩ := flowOf_add hv hk (t := t) (by rwa [hkx])
    rw [hkx, hx] at heq
    simpa only [Nat.cast_succ, add_one_mul] using ⟨hmem, heq.symm⟩

omit [CompleteSpace E] in
/-- If `x` returns to itself at time `s`, then so does every point `flowOf v t x` of its
trajectory. -/
theorem flowOf_flowOf_of_flowOf_eq [IsManifold I 1 M] {v : (x : M) → TangentSpace I x}
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) {s t : ℝ} {x : M}
    (ht : (t, x) ∈ flowDomain v) (hs : (s, x) ∈ flowDomain v) (hx : flowOf v s x = x) :
    (s, flowOf v t x) ∈ flowDomain v ∧ flowOf v s (flowOf v t x) = flowOf v t x := by
  obtain ⟨hst, heq⟩ := flowOf_add hv hs (hx.symm ▸ ht)
  have hs' : (s, flowOf v t x) ∈ flowDomain v := by
    rw [mem_flowDomain, flowOf_apply,
      mem_maximalIntegralCurveInterval_maximalIntegralCurve_iff hv (mem_flowDomain.mp ht), add_comm,
      ← mem_flowDomain]
    exact hst
  refine ⟨hs', ?_⟩
  rw [(flowOf_add hv ht hs').2, add_comm, ← heq, hx]

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
