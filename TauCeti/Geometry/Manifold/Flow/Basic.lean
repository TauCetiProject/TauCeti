/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Contractible
public import TauCeti.Geometry.Manifold.IntegralCurve.Flow
public import TauCeti.Geometry.Manifold.MFDeriv.Curve
public import TauCeti.Geometry.Manifold.RegularValue
import TauCeti.Dynamics.Flow.PeriodBound
import TauCeti.Geometry.Manifold.IntegralCurve.Monotone

/-!
# The maximal flow of a vector field

This file presents Tau Ceti's maximal integral curves as a partial flow whose arguments are ordered
as time followed by initial point.  The domain and value are adapters for
`maximalIntegralCurveFlowDomain` and `maximalIntegralCurve`, not independent constructions.  The
domain-aware group law records both the value equation and the condition that the composite time
remains in the interval of existence.

For complete normed model spaces, the existing smooth-dependence theorem for maximal integral
curves gives joint openness of the domain and joint smoothness of the flow, so flowing a `C^n`
family of points for a `C^n` family of times is again `C^n`.  At time zero, the derivative of the
flow is the field in the time direction and the identity in the space directions, so flowing for a
time `τ` vanishing at `x` has derivative `w ↦ w + dτ_x(w) • v x` at `x`.  Along a trajectory, a
function changes at the rate of its derivative in the direction of the vector field.  The escape
theorem says that a maximal trajectory approaching a finite right endpoint eventually leaves every
compact set.

## Main declarations

* `TauCeti.flowDomain`: the domain of the maximal flow, in `(time, point)` order.
* `TauCeti.flowOf`: the maximal flow, total with junk values outside `flowDomain`, recorded by
  `TauCeti.flowOf_of_notMem`.
* `TauCeti.ordConnected_setOf_mem_flowDomain`: the times of the flow through a point form an
  interval, and `TauCeti.isLUB_setOf_mem_flowDomain_of_notMem` identifies a finite right endpoint.
* `TauCeti.isMIntegralCurveAt_flowOf`: a trajectory is an integral curve near every time in its
  domain.
* `TauCeti.mfderiv_flowOf_trajectory_apply`, `TauCeti.mfderiv_flowOf_trajectory_zero_apply`: the
  derivative of a trajectory is the field.
* `TauCeti.hasDerivAt_comp_flowOf`: the time derivative of a function along a trajectory.
* `TauCeti.lt_apply_flowOf_of_le_apply`, `TauCeti.apply_flowOf_lt_of_apply_le`: a trajectory
  crosses a level transverse to the field only in the direction of the field.
* `TauCeti.flowOf_add`: the domain-aware group law, and `TauCeti.mem_flowDomain_flowOf_iff`, the
  times of the flow through a point of a trajectory.
* `TauCeti.flowOf_neg_flowOf`: flowing backwards undoes flowing forwards.
* `TauCeti.mem_flowDomain_of_flowOf_eq_of_ne_zero`: a trajectory with a nonzero return time is
  defined for all real time.
* `TauCeti.flowOf_ne_flowOf_of_lt`: a trajectory that does not return to its base point on
  `(0, T₀)` has no self-intersections on `(0, T₀]`.
* `TauCeti.isOpen_flowDomain`: openness of the domain for complete model spaces.
* `TauCeti.contMDiffOn_flowOf`: joint regularity of the flow for complete model spaces.
* `TauCeti.contMDiffAt_flowOf_comp`: flowing `C^n` families of points for `C^n` families of times.
* `TauCeti.mdifferentiableAt_flowOf_prod`, `TauCeti.mdifferentiableAt_flowOf_apply`: joint
  differentiability of the maximal flow and differentiability of its time-`t` maps.
* `TauCeti.isOpen_setOf_mem_flowDomain`: the parameters of a continuous family of times and
  points at which the flow is defined form an open set, and
  `TauCeti.isOpen_setOf_mem_flowDomain_and_flowOf_mem` the times and points whose trajectory is
  defined and in a given open set.
* `TauCeti.exists_nullhomotopic_flowOf_comp`: flowing a nullhomotopic map, for times at which the
  flow stays in a set `W`, gives a map nullhomotopic in `W`.
* `TauCeti.mfderiv_flowOf_zero_apply`: the derivative of the flow at time zero.
* `TauCeti.mfderiv_flowOf_zero_apply_eq_self`: the spatial derivative of the time-zero flow map is
  the identity.
* `TauCeti.hasMFDerivAt_flowOf_comp_of_eq_zero`: the derivative of flowing for a time that
  vanishes at the base point.
* `TauCeti.mfderiv_flowOf_comp_apply`: the differential of `(t, s) ↦ φₜ(f s)`.
* `TauCeti.mfderiv_flowOf_comp_prodMk_apply`: the differential of `y ↦ φ_{τ y}(f y)`.
* `TauCeti.mvfderiv_apply_eq_of_comp_flowOf_eventuallyEq`: a function that the flow rescales by
  `e^s` is differentiated to itself by the field, and
  `TauCeti.mvfderiv_apply_eq_one_of_eventually_apply_flowOf_eq_add`: a function that the flow
  translates at unit speed has derivative `1` along the field, so
  (`TauCeti.isRegularValue_of_apply_flowOf_eq_add`) the values it is translated through are
  regular.
* `TauCeti.mfderiv_flowOf_apply_self`: the differential of the time-`t` map carries the field to
  itself.
* `TauCeti.mfderiv_flowOf_add_apply`: the differential of the composition of two local flow maps.
* `TauCeti.mfderiv_flowOf_neg_mfderiv_flowOf_apply`,
  `TauCeti.mfderiv_flowOf_mfderiv_flowOf_neg_apply`: the differential of the time-`(-t)` map at
  `φₜ x` is a two-sided inverse of the differential of the time-`t` map at `x`, so the latter is
  bijective (`TauCeti.bijective_mfderiv_flowOf`), even for incomplete fields.
* `TauCeti.exists_pos_period_le_nhds_flowOf`: positive return times near a point where the field
  is nonzero are bounded away from zero.
* `TauCeti.eventually_flowOf_notMem`: escape from compact sets at a finite right endpoint.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 9.
-/

public section

noncomputable section

open Function Manifold Set Filter
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-! ### Adapter definitions and unconditional properties -/

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

/-- Time zero belongs to the maximal-flow domain of `x` as soon as some time does. -/
theorem mem_flowDomain_zero_of_mem {v : (x : M) → TangentSpace I x} {t : ℝ} {x : M}
    (ht : (t, x) ∈ flowDomain v) : ((0 : ℝ), x) ∈ flowDomain v :=
  mem_flowDomain.mpr (zero_mem_maximalIntegralCurveInterval_of_mem (mem_flowDomain.mp ht))

/-- The maximal flow fixes every point at time zero. -/
theorem flowOf_zero (v : (x : M) → TangentSpace I x) (x : M) : flowOf v 0 x = x := by
  rw [flowOf_apply, maximalIntegralCurve_zero]

/-- Outside the maximal-flow domain, the maximal flow takes the junk value `x`. -/
theorem flowOf_of_notMem {v : (x : M) → TangentSpace I x} {t : ℝ} {x : M}
    (ht : (t, x) ∉ flowDomain v) : flowOf v t x = x := by
  rw [flowOf_apply, maximalIntegralCurve_eq_of_not_mem (mem_flowDomain.not.mp ht)]

/-- The differential of the time-`0` local flow map `flowOf v 0` acts as the identity on every
tangent vector. -/
theorem mfderiv_flowOf_zero_apply_eq_self (v : (x : M) → TangentSpace I x) (x : M)
    (w : TangentSpace I x) :
    -- The tangent spaces at `flowOf v 0 x` and `x` are both the model space `E`.
    @Eq E (mfderiv I I (flowOf v 0) x w) w := by
  have h0 : flowOf v 0 = id := funext (flowOf_zero v)
  rw [h0, mfderiv_id]
  exact ContinuousLinearMap.id_apply w

/-- The times at which the flow through `x` is defined form an interval. -/
theorem ordConnected_setOf_mem_flowDomain (v : (x : M) → TangentSpace I x) (x : M) :
    {t | (t, x) ∈ flowDomain v}.OrdConnected := by
  simpa only [mem_flowDomain, ofPred_mem_eq] using
    (ordConnected_maximalIntegralCurveInterval (v := v) (x := x))

/-- The times between `0` and a time at which the flow through `x` is defined are times at which
it is defined. -/
theorem uIcc_subset_setOf_mem_flowDomain {v : (x : M) → TangentSpace I x} {t : ℝ} {x : M}
    (ht : (t, x) ∈ flowDomain v) : uIcc 0 t ⊆ {s | (s, x) ∈ flowDomain v} :=
  (ordConnected_setOf_mem_flowDomain v x).uIcc_subset (mem_flowDomain_zero_of_mem ht) ht

/-- If a trajectory is defined on `(0, b)` with `0 < b` but not at `b`, then `b` is the least
upper bound of its flow-domain times. -/
theorem isLUB_setOf_mem_flowDomain_of_notMem {v : (x : M) → TangentSpace I x} {b : ℝ} {x : M}
    (hb₀ : 0 < b) (hIoo : ∀ t ∈ Ioo 0 b, (t, x) ∈ flowDomain v)
    (hb : (b, x) ∉ flowDomain v) :
    IsLUB {t | (t, x) ∈ flowDomain v} b := by
  refine ⟨fun t ht ↦ le_of_not_gt fun hlt ↦ hb ?_, fun c hc ↦ le_of_not_gt fun hlt ↦ ?_⟩
  · exact uIcc_subset_setOf_mem_flowDomain ht (Icc_subset_uIcc ⟨hb₀.le, hlt.le⟩)
  · obtain ⟨t, ht₁, ht₂⟩ := exists_between (max_lt hb₀ hlt)
    exact (hc (hIoo t ⟨(le_max_left 0 c).trans_lt ht₁, ht₂⟩)).not_gt
      ((le_max_right 0 c).trans_lt ht₁)

/-! ### Trajectories, group law, and periodicity without completeness -/

section FlowLaw

variable [T2Space M] [BoundarylessManifold I M] [IsManifold I 1 M]
  {v : (x : M) → TangentSpace I x}

/-- The trajectory `t ↦ flowOf v t x` is an integral curve on its maximal interval of
existence. -/
theorem isMIntegralCurveOn_flowOf
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) (x : M) :
    IsMIntegralCurveOn (fun t ↦ flowOf v t x) v {t | (t, x) ∈ flowDomain v} := by
  have hcurve : (fun t ↦ flowOf v t x) = maximalIntegralCurve v x :=
    funext fun t ↦ flowOf_apply v t x
  have hdomain : {t | (t, x) ∈ flowDomain v} = maximalIntegralCurveInterval v x :=
    Set.ext fun _ ↦ mem_flowDomain
  rw [hcurve, hdomain]
  exact isMIntegralCurveOn_maximalIntegralCurve hv

/-- The trajectory `t ↦ flowOf v t x` is an integral curve near every time in its domain. -/
theorem isMIntegralCurveAt_flowOf
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) {t : ℝ} {x : M}
    (ht : (t, x) ∈ flowDomain v) :
    IsMIntegralCurveAt (fun s ↦ flowOf v s x) v t := by
  have hdom : {s | (s, x) ∈ flowDomain v} ∈ 𝓝 t := by
    simpa only [mem_flowDomain, ofPred_mem_eq] using
      isOpen_maximalIntegralCurveInterval.mem_nhds (mem_flowDomain.mp ht)
  exact (isMIntegralCurveOn_flowOf hv x).isMIntegralCurveAt hdom

/-- A global integral curve of a `C¹` field is the maximal flow through its initial value.
No completeness hypothesis is needed on the field or the model space. -/
theorem flowOf_eq_of_isMIntegralCurve
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    {γ : ℝ → M} (hγ : IsMIntegralCurve γ v) (t : ℝ) :
    flowOf v t (γ 0) = γ t := by
  rw [flowOf_apply]
  exact hγ.maximalIntegralCurve_eq hv t

/-- The velocity of a maximal-flow trajectory is the vector field at the current point,
whenever the trajectory is in its domain. -/
theorem curveVelocity_flowOf
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) {t : ℝ} {x : M}
    (ht : (t, x) ∈ flowDomain v) :
    Manifold.curveVelocity I (fun s ↦ flowOf v s x) t = v (flowOf v t x) := by
  simpa only [Manifold.curveVelocityWithin_univ] using
    Manifold.curveVelocityWithin_eq_of_hasMFDerivWithinAt
      (isMIntegralCurveAt_flowOf hv ht).hasMFDerivAt.hasMFDerivWithinAt uniqueDiffWithinAt_univ

/-- A maximal-flow trajectory is differentiable at every time in its domain. -/
theorem mdifferentiableAt_flowOf
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) {t : ℝ} {x : M}
    (ht : (t, x) ∈ flowDomain v) :
    MDifferentiableAt 𝓘(ℝ) I (fun s ↦ flowOf v s x) t :=
  (isMIntegralCurveAt_flowOf hv ht).hasMFDerivAt.mdifferentiableAt

/-- **The derivative of a trajectory.** At every time in its domain, the derivative of
`s ↦ flowOf v s x` sends `a` to `a • v (flowOf v t x)`. -/
theorem mfderiv_flowOf_trajectory_apply
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) {t : ℝ} {x : M}
    (ht : (t, x) ∈ flowDomain v) (a : ℝ) :
    mfderiv 𝓘(ℝ) I (fun s ↦ flowOf v s x) t a = a • v (flowOf v t x) := by
  rw [Manifold.mfderiv_apply_eq_smul_curveVelocity, curveVelocity_flowOf hv ht]

/-- **Derivative along a flow line.** The derivative in time of a function `g` along the
trajectory of `v` through `x` is the derivative of `g` in the direction of `v`. -/
theorem hasDerivAt_comp_flowOf
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {g : M → F} {t : ℝ} {x : M}
    (hx : (t, x) ∈ flowDomain v) (hg : MDifferentiableAt I 𝓘(ℝ, F) g (flowOf v t x)) :
    HasDerivAt (fun s ↦ g (flowOf v s x)) (mvfderiv I g (flowOf v t x) (v (flowOf v t x))) t :=
  Manifold.hasDerivAt_comp_curve hg (isMIntegralCurveAt_flowOf hv hx).hasMFDerivAt

/-- **Trajectories cross a level only upwards.** Let `f` be continuous, differentiable with
`df(v) > 0` at every point of the level `f⁻¹(c)`, and let `v` be `C¹`. If `c ≤ f x`, then
`c < f (φₜ x)` at every positive time `t` at which the trajectory of `x` is defined. -/
theorem lt_apply_flowOf_of_le_apply
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) {f : M → ℝ} {c : ℝ}
    (hf : Continuous f)
    (hfc : ∀ y, f y = c → MDifferentiableAt I 𝓘(ℝ) f y ∧ 0 < mvfderiv I f y (v y)) {x : M}
    (hx : c ≤ f x) {t : ℝ} (ht : 0 < t) (htx : (t, x) ∈ flowDomain v) :
    c < f (flowOf v t x) := by
  -- The trajectory is an integral curve on its open interval of existence, which contains
  -- `[0, t]`.
  have hdom : {τ | (τ, x) ∈ flowDomain v} = maximalIntegralCurveInterval v x :=
    ext fun _ ↦ mem_flowDomain
  have hs : IsOpen {τ | (τ, x) ∈ flowDomain v} := hdom ▸ isOpen_maximalIntegralCurveInterval
  have hIcc : Icc 0 t ⊆ {τ | (τ, x) ∈ flowDomain v} := hdom ▸
    ordConnected_maximalIntegralCurveInterval.out
      (mem_flowDomain.1 (mem_flowDomain_zero_of_mem htx)) (mem_flowDomain.1 htx)
  exact (isMIntegralCurveOn_flowOf hv x).lt_apply_of_le_apply hs hIcc
    (hf.comp_continuousOn ((isMIntegralCurveOn_flowOf hv x).continuousOn.mono hIcc))
    (fun τ _ hτ ↦ hfc _ hτ) (by rwa [flowOf_zero v]) ⟨ht, le_rfl⟩

/-- **Trajectories cross a level only downwards when the field decreases the function.** Let `f`
be continuous, differentiable with `df(v) < 0` at every point of the level `f⁻¹(c)`, and let `v`
be `C¹`. If `f x ≤ c`, then `f (φₜ x) < c` at every positive time `t` at which the trajectory of
`x` is defined: the forward flow carries `{f ≤ c}` into `{f < c}`. -/
theorem apply_flowOf_lt_of_apply_le
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) {f : M → ℝ} {c : ℝ}
    (hf : Continuous f)
    (hfc : ∀ y, f y = c → MDifferentiableAt I 𝓘(ℝ) f y ∧ mvfderiv I f y (v y) < 0) {x : M}
    (hx : f x ≤ c) {t : ℝ} (ht : 0 < t) (htx : (t, x) ∈ flowDomain v) :
    f (flowOf v t x) < c := by
  have hlt := lt_apply_flowOf_of_le_apply (f := -f) (c := -c) hv hf.neg
    (fun y hy ↦ by
      have hy' : f y = c := by simpa using hy
      refine ⟨(hfc y hy').1.neg, ?_⟩
      rw [mvfderiv_neg, neg_apply]
      exact neg_pos.2 (hfc y hy').2)
    (by simpa using hx) ht htx
  simpa using hlt

/-- The domain-aware group law for the maximal flow.  If time `s` is defined at `x` and time `t`
is defined after flowing for `s`, then time `s + t` is defined at `x` and gives the same value. -/
theorem flowOf_add
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

/-- The times of the flow through a point of a trajectory are those of the trajectory shifted: if
time `s` is defined at `x`, then time `t` is defined at `flowOf v s x` exactly when time `s + t`
is defined at `x`. -/
theorem mem_flowDomain_flowOf_iff
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) {s t : ℝ} {x : M}
    (hs : (s, x) ∈ flowDomain v) :
    (t, flowOf v s x) ∈ flowDomain v ↔ (s + t, x) ∈ flowDomain v := by
  rw [mem_flowDomain, flowOf_apply,
    mem_maximalIntegralCurveInterval_maximalIntegralCurve_iff hv (mem_flowDomain.mp hs),
    ← mem_flowDomain]

/-- The flow can be run backwards along a trajectory: if time `t` is defined at `x`, then time
`-t` is defined at `flowOf v t x`. -/
theorem neg_mem_flowDomain_flowOf
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) {t : ℝ} {x : M}
    (ht : (t, x) ∈ flowDomain v) : (-t, flowOf v t x) ∈ flowDomain v := by
  rw [mem_flowDomain_flowOf_iff hv ht, add_neg_cancel]
  exact mem_flowDomain_zero_of_mem ht

/-- Flowing for time `-t` undoes flowing for time `t`. -/
theorem flowOf_neg_flowOf
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) {t : ℝ} {x : M}
    (ht : (t, x) ∈ flowDomain v) : flowOf v (-t) (flowOf v t x) = x := by
  rw [(flowOf_add hv ht (neg_mem_flowDomain_flowOf hv ht)).2, add_neg_cancel, flowOf_zero]

/-- If `x` returns to itself at time `t`, it does so at every natural multiple of `t`. -/
theorem flowOf_natCast_mul_of_flowOf_eq
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) {t : ℝ} {x : M}
    (ht : (t, x) ∈ flowDomain v) (hx : flowOf v t x = x) (k : ℕ) :
    ((k : ℝ) * t, x) ∈ flowDomain v ∧ flowOf v ((k : ℝ) * t) x = x := by
  induction k with
  | zero =>
    simpa only [Nat.cast_zero, zero_mul] using ⟨mem_flowDomain_zero_of_mem ht, flowOf_zero v x⟩
  | succ k ih =>
    obtain ⟨hk, hkx⟩ := ih
    obtain ⟨hmem, heq⟩ := flowOf_add hv hk (t := t) (by rwa [hkx])
    rw [hkx, hx] at heq
    simpa only [Nat.cast_succ, add_one_mul] using ⟨hmem, heq.symm⟩

/-- If `x` returns to itself at a nonzero time `s` in its flow domain, then its trajectory is
defined for all real time. -/
theorem mem_flowDomain_of_flowOf_eq_of_ne_zero
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) {s : ℝ} {x : M}
    (hs : (s, x) ∈ flowDomain v) (hx : flowOf v s x = x) (hs0 : s ≠ 0) (t : ℝ) :
    (t, x) ∈ flowDomain v := by
  have hneg_dom : (-s, x) ∈ flowDomain v := hx ▸ neg_mem_flowDomain_flowOf hv hs
  have hneg_eq : flowOf v (-s) x = x := by
    have h := flowOf_neg_flowOf hv hs
    rwa [hx] at h
  obtain ⟨k, hk⟩ := exists_nat_gt (|t| / |s|)
  have hkt : |t| < (k : ℝ) * |s| := (div_lt_iff₀ (abs_pos.mpr hs0)).mp hk
  have hpos := (flowOf_natCast_mul_of_flowOf_eq hv hs hx k).1
  have hneg := (flowOf_natCast_mul_of_flowOf_eq hv hneg_dom hneg_eq k).1
  refine (ordConnected_setOf_mem_flowDomain v x).uIcc_subset hneg hpos ?_
  rw [mem_uIcc]
  rcases le_or_gt 0 s with hle | hlt
  · rw [abs_of_nonneg hle, abs_lt] at hkt
    exact Or.inl ⟨by linarith, hkt.2.le⟩
  · rw [abs_of_neg hlt, abs_lt] at hkt
    exact Or.inr ⟨by linarith, by linarith⟩

/-- If `x` returns to itself at a time `s` in its flow domain, then so does `flowOf v t x` for
every time `t`. When `s ≠ 0`, the trajectory through `x` is defined for all real time; when
`s = 0` and `(t, x) ∉ flowDomain v`, the junk value is `x`. -/
theorem flowOf_flowOf_of_flowOf_eq
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) {s t : ℝ} {x : M}
    (hs : (s, x) ∈ flowDomain v) (hx : flowOf v s x = x) :
    (s, flowOf v t x) ∈ flowDomain v ∧ flowOf v s (flowOf v t x) = flowOf v t x := by
  by_cases ht : (t, x) ∈ flowDomain v
  · obtain ⟨hst, heq⟩ := flowOf_add hv hs (hx.symm ▸ ht)
    have hs' : (s, flowOf v t x) ∈ flowDomain v :=
      (mem_flowDomain_flowOf_iff hv ht).2 (by rwa [add_comm])
    refine ⟨hs', ?_⟩
    rw [(flowOf_add hv ht hs').2, add_comm, ← heq, hx]
  · rcases eq_or_ne s 0 with rfl | hs0
    · rw [flowOf_of_notMem ht]
      exact ⟨hs, flowOf_zero v x⟩
    · exact absurd (mem_flowDomain_of_flowOf_eq_of_ne_zero hv hs hx hs0 t) ht

/-- **A trajectory without early returns has no self-intersections.** If `flowOf v r x ≠ x` for
every `r ∈ (0, T₀)`, then for `0 < s < t ≤ T₀` the points `flowOf v s x` and `flowOf v t x` are
distinct. -/
theorem flowOf_ne_flowOf_of_lt
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) {T₀ s t : ℝ} {x : M}
    (hmin : ∀ r ∈ Ioo 0 T₀, flowOf v r x ≠ x) (hs : 0 < s) (hst : s < t) (ht : t ≤ T₀) :
    flowOf v s x ≠ flowOf v t x := by
  intro h
  have hs_mem : s ∈ Ioo 0 T₀ := ⟨hs, hst.trans_le ht⟩
  have hs_dom : (s, x) ∈ flowDomain v := by
    by_contra hdom
    exact hmin s hs_mem (flowOf_of_notMem hdom)
  by_cases ht_dom : (t, x) ∈ flowDomain v
  · -- Flowing back by `-s` turns `flowOf v s x = flowOf v t x` into a return at `t - s ∈ (0, T₀)`.
    have hneg : (-s, flowOf v t x) ∈ flowDomain v := h ▸ neg_mem_flowDomain_flowOf hv hs_dom
    have hadd := (flowOf_add hv ht_dom hneg).2
    rw [← h, flowOf_neg_flowOf hv hs_dom] at hadd
    exact hmin (t + -s) ⟨by linarith, by linarith⟩ hadd.symm
  · exact hmin s hs_mem (h.trans (flowOf_of_notMem ht_dom))

end FlowLaw

/-! ### Local existence at time zero -/

section LocalExistence

variable [BoundarylessManifold I M] [CompleteSpace E] [IsManifold I 1 M]
  {v : (x : M) → TangentSpace I x}

/-- Time zero belongs to the maximal-flow domain whenever the vector field is `C¹` at `x`. -/
theorem mem_flowDomain_zero {x : M}
    (hv : CMDiffAt 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)) x) :
    ((0 : ℝ), x) ∈ flowDomain v :=
  mem_flowDomain.mpr (zero_mem_maximalIntegralCurveInterval hv)

end LocalExistence

/-! ### Openness, regularity, differentials, return times, and escape -/

section CompleteModel

variable [T2Space M] [BoundarylessManifold I M] [CompleteSpace E]

/-- On a complete normed model space, the domain of the maximal flow is jointly open in time
and initial point. -/
theorem isOpen_flowDomain [IsManifold I 1 M]
    {v : (x : M) → TangentSpace I x}
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) :
    IsOpen (flowDomain v) := by
  simpa only [flowDomain] using
    (isOpen_maximalIntegralCurveFlowDomain hv).preimage continuous_swap

/-- On a complete normed model space, a `C^n` vector field has a jointly `C^n` maximal flow on
its domain. -/
theorem contMDiffOn_flowOf {n : ℕ∞} (hn : 1 ≤ n)
    [IsManifold I 1 M] [IsManifold I n M] {v : (x : M) → TangentSpace I x}
    (hv : CMDiff n (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) I n (fun p : ℝ × M ↦ flowOf v p.1 p.2)
      (flowDomain v) := by
  have h := (contMDiffOn_maximalIntegralCurve hn hv).comp
    (contMDiff_snd.prodMk contMDiff_fst).contMDiffOn fun _ hp ↦ hp
  have hfun : ((fun p : M × ℝ ↦ maximalIntegralCurve v p.1 p.2) ∘
      fun p : ℝ × M ↦ (p.2, p.1)) =
    fun p : ℝ × M ↦ flowOf v p.1 p.2 :=
    funext fun p ↦ (flowOf_apply v p.1 p.2).symm
  have hdomain : (fun p : ℝ × M ↦ (p.2, p.1)) ⁻¹'
      maximalIntegralCurveFlowDomain v = flowDomain v :=
    Set.ext fun _ ↦ Iff.rfl
  rw [hfun, hdomain] at h
  exact h

/-- On a complete normed model space, flowing a `C^n` family of initial points for a `C^n` family
of times is `C^n`, wherever the flow is defined. -/
theorem contMDiffAt_flowOf_comp {n : ℕ∞} (hn : 1 ≤ n)
    [IsManifold I 1 M] [IsManifold I n M] {v : (x : M) → TangentSpace I x}
    (hv : CMDiff n (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
    {τ : N → ℝ} {f : N → M} {z : N} (hτ : ContMDiffAt J 𝓘(ℝ) n τ z)
    (hf : ContMDiffAt J I n f z) (hz : (τ z, f z) ∈ flowDomain v) :
    ContMDiffAt J I n (fun y ↦ flowOf v (τ y) (f y)) z :=
  ((contMDiffOn_flowOf hn hv).contMDiffAt
    ((isOpen_flowDomain (hv.of_le (by exact_mod_cast hn))).mem_nhds hz)).comp z (hτ.prodMk hf)

section C1

variable [IsManifold I 1 M] {v : (x : M) → TangentSpace I x}

/-- On a complete normed model space, the set of parameters `y` at which the flow of a continuous
family of initial points `f y` for a continuous family of times `τ y` is defined is open. -/
theorem isOpen_setOf_mem_flowDomain
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) {N : Type*} [TopologicalSpace N]
    {τ : N → ℝ} {f : N → M} (hτ : Continuous τ) (hf : Continuous f) :
    IsOpen {y | (τ y, f y) ∈ flowDomain v} :=
  (isOpen_flowDomain hv).preimage (hτ.prodMk hf)

/-- On a complete normed model space, the pairs `(t, y)` such that the trajectory through `y` is
defined at time `t` and is then in an open set `U` form an open set. -/
theorem isOpen_setOf_mem_flowDomain_and_flowOf_mem
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    {U : Set M} (hU : IsOpen U) :
    IsOpen {q : ℝ × M | q ∈ flowDomain v ∧ flowOf v q.1 q.2 ∈ U} :=
  (contMDiffOn_flowOf le_rfl hv).continuousOn.isOpen_inter_preimage (isOpen_flowDomain hv) hU

/-- **Flowing a nullhomotopic map.** On a complete normed model space, let `g : X → W` be
nullhomotopic in `W`, and let the maximal flow of a `C¹` field `v` be defined at time `t` and stay
in `W` at the times `u t`, `u ∈ [0, 1]`, from every point of `g`. Then `x ↦ φₜ(g x)` is
nullhomotopic in `W`: the times `u t` move `g` to it inside `W`. -/
theorem exists_nullhomotopic_flowOf_comp
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) {X : Type*} [TopologicalSpace X]
    {W : Set M} {g : C(X, W)} (hg : g.Nullhomotopic) {t : ℝ}
    (hdom : ∀ x, (t, (g x : M)) ∈ flowDomain v)
    (hmem : ∀ x, ∀ u ∈ Icc (0 : ℝ) 1, flowOf v (u * t) (g x) ∈ W) :
    ∃ g' : C(X, W), g'.Nullhomotopic ∧ ∀ x, (g' x : M) = flowOf v t (g x) := by
  have hcont : ContinuousOn (fun p : ℝ × M ↦ flowOf v p.1 p.2) (flowDomain v) :=
    (contMDiffOn_flowOf le_rfl hv).continuousOn
  let H : C(unitInterval × X, W) :=
    { toFun := fun p : unitInterval × X ↦
        ⟨flowOf v ((p.1 : ℝ) * t) (g p.2), hmem p.2 p.1 p.1.property⟩
      continuous_toFun := (hcont.comp_continuous
        (f := fun p : unitInterval × X ↦ ((p.1 : ℝ) * t, (g p.2 : M))) (by fun_prop)
        fun p ↦ uIcc_subset_setOf_mem_flowDomain (hdom p.2)
          ((convex_uIcc 0 t).smul_mem_of_zero_mem left_mem_uIcc right_mem_uIcc
            p.1.property)).subtype_mk _ }
  let g' : C(X, W) := ⟨fun x ↦ H (1, x), by fun_prop⟩
  let hH : ContinuousMap.Homotopy g g' :=
    { toContinuousMap := H
      map_zero_left := fun x ↦ Subtype.ext <| by simp [H]
      map_one_left := fun _ ↦ rfl }
  obtain ⟨y, hy⟩ := hg
  exact ⟨g', ⟨y, (ContinuousMap.Homotopic.symm ⟨hH⟩).trans hy⟩, fun x ↦ by simp [g', H]⟩

/-- On a complete normed model space, the maximal flow `(t, x) ↦ flowOf v t x` is jointly
differentiable at every point of its domain. -/
theorem mdifferentiableAt_flowOf_prod
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) {p : ℝ × M}
    (hp : p ∈ flowDomain v) :
    MDifferentiableAt (𝓘(ℝ).prod I) I (fun q : ℝ × M ↦ flowOf v q.1 q.2) p :=
  ((contMDiffOn_flowOf le_rfl hv).contMDiffAt
    ((isOpen_flowDomain hv).mem_nhds hp)).mdifferentiableAt one_ne_zero

/-- On a complete normed model space, the time-`t` map `y ↦ flowOf v t y` is differentiable at
every point `x` with `(t, x) ∈ flowDomain v`. -/
theorem mdifferentiableAt_flowOf_apply
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) {t : ℝ} {x : M}
    (ht : (t, x) ∈ flowDomain v) :
    MDifferentiableAt I I (flowOf v t) x :=
  (mdifferentiableAt_flowOf_prod hv ht).comp x
    (mdifferentiableAt_const.prodMk mdifferentiableAt_id)

/-- **The derivative of a trajectory at time zero.** The derivative of `s ↦ flowOf v s x` at
`s = 0` sends `a` to `a • v x`. -/
theorem mfderiv_flowOf_trajectory_zero_apply
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) (x : M) (a : ℝ) :
    mfderiv 𝓘(ℝ) I (fun s ↦ flowOf v s x) 0 a = a • v x := by
  rw [mfderiv_flowOf_trajectory_apply hv (mem_flowDomain_zero (hv x))]
  -- The tangent spaces at `flowOf v 0 x` and at `x` are both the model space `E`, so `v` may be
  -- treated as a non-dependent function here.
  exact congrArg (a • v ·) (flowOf_zero v x)

/-- **The derivative of the flow at time zero.** At `(0, x)`, the derivative of
`(t, y) ↦ flowOf v t y` sends the time direction to the field at `x` and is the identity in the
space direction. -/
theorem mfderiv_flowOf_zero_apply
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) (x : M) (a : ℝ)
    (w : TangentSpace I x) :
    -- The two sides live in tangent spaces at different points, both equal to `E` by definition,
    -- so the equation is stated in `E`.
    @Eq E (mfderiv (𝓘(ℝ).prod I) I (fun y : ℝ × M ↦ flowOf v y.1 y.2) (0, x) ((a, w) : ℝ × E))
      (a • v x + w) := by
  have hG := mdifferentiableAt_flowOf_prod hv (mem_flowDomain_zero (hv x))
  have h1 : @Eq E (mfderiv 𝓘(ℝ) I (fun t : ℝ ↦ flowOf v t x) 0 a) (a • v x) :=
    mfderiv_flowOf_trajectory_zero_apply hv x a
  have h2 : @Eq E (mfderiv I I (fun z : M ↦ flowOf v 0 z) x w) w :=
    mfderiv_flowOf_zero_apply_eq_self v x w
  -- The splitting of the derivative into its time and space parts is an equation in the tangent
  -- space at `flowOf v 0 x`, which is `E` by definition, so it composes with `h1` and `h2`.
  exact (mfderiv_prod_eq_add_apply hG).trans (congrArg₂ (· + ·) h1 h2)

/-- **Flowing for a time that vanishes at a point.** If `τ x = 0`, the map
`z ↦ flowOf v (τ z) z` has derivative `w ↦ w + dτ_x(w) • v x` at `x`. -/
theorem hasMFDerivAt_flowOf_comp_of_eq_zero
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) {x : M} {τ : M → ℝ}
    {dτ : TangentSpace I x →L[ℝ] ℝ} (hτ : HasMFDerivAt I 𝓘(ℝ) τ x dτ) (hτx : τ x = 0) :
    HasMFDerivAt I I (fun z ↦ flowOf v (τ z) z) x
      (ContinuousLinearMap.id ℝ (TangentSpace I x) + dτ.smulRight (v x)) := by
  have hG := mdifferentiableAt_flowOf_prod hv (hτx ▸ mem_flowDomain_zero (hv x))
  refine (hG.hasMFDerivAt.comp (f := fun z ↦ (τ z, id z)) x
    (hτ.prodMk (hasMFDerivAt_id x))).congr_mfderiv ?_
  refine ContinuousLinearMap.ext fun w ↦ ?_
  -- Evaluate the composite with the pairing `z ↦ (τ z, z)` at `w`, as an equation in `E`.
  change @Eq E (mfderiv (𝓘(ℝ).prod I) I (fun y : ℝ × M ↦ flowOf v y.1 y.2) (τ x, x)
    ((dτ w, w) : ℝ × E)) (w + dτ w • v x)
  rw [hτx, mfderiv_flowOf_zero_apply hv, add_comm]

/-- **The differential of a flow out of a map.** On a complete normed model space, at a point
`(t, s)` where `φₜ(f s)` is defined and `f` is differentiable at `s`, the differential of
`(t, s) ↦ φₜ(f s)` sends a tangent vector `(r, w)` to `r v + dφₜ(df w)`. -/
theorem mfderiv_flowOf_comp_apply
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N] {f : N → M}
    {p : ℝ × N} (hf : MDifferentiableAt J I f p.2) (hp : (p.1, f p.2) ∈ flowDomain v)
    (w : TangentSpace (𝓘(ℝ).prod J) p) :
    mfderiv (𝓘(ℝ).prod J) I (fun q : ℝ × N ↦ flowOf v q.1 (f q.2)) p w =
      w.1 • v (flowOf v p.1 (f p.2)) +
        mfderiv I I (flowOf v p.1) (f p.2) (mfderiv J I f p.2 w.2) := by
  have hcomp : mfderiv J I (flowOf v p.1 ∘ f) p.2 =
      (mfderiv I I (flowOf v p.1) (f p.2)).comp (mfderiv J I f p.2) :=
    mfderiv_comp p.2 (mdifferentiableAt_flowOf_apply hv hp) hf
  have hΦ : MDifferentiableAt (𝓘(ℝ).prod J) I (fun q : ℝ × N ↦ flowOf v q.1 (f q.2)) p :=
    (mdifferentiableAt_flowOf_prod hv hp).comp p
      (mdifferentiableAt_fst.prodMk (hf.comp p mdifferentiableAt_snd))
  refine (mfderiv_prod_eq_add_apply hΦ).trans ?_
  -- The trajectory through `f s` has velocity `v` at time `t`.
  rw [mfderiv_flowOf_trajectory_apply hv hp]
  exact congrArg₂ (· + ·) rfl (DFunLike.congr_fun hcomp w.2)

/-- **The differential of flowing a family of points for a family of times.** On a complete normed
model space, at a point `z` where `φ_{τ z}(f z)` is defined, the differential of
`y ↦ φ_{τ y}(f y)` sends a tangent vector `w` to `dτ(w) v + dφ_{τ z}(df w)`. This is
`TauCeti.mfderiv_flowOf_comp_apply` composed with the differential of `y ↦ (τ y, f y)`. -/
theorem mfderiv_flowOf_comp_prodMk_apply
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N] {τ : N → ℝ}
    {f : N → M} {z : N} (hτ : MDifferentiableAt J 𝓘(ℝ) τ z) (hf : MDifferentiableAt J I f z)
    (hz : (τ z, f z) ∈ flowDomain v) (w : TangentSpace J z) :
    mfderiv J I (fun y ↦ flowOf v (τ y) (f y)) z w =
      mvfderiv J τ z w • v (flowOf v (τ z) (f z)) +
        mfderiv I I (flowOf v (τ z)) (f z) (mfderiv J I f z w) := by
  have hΦ := mdifferentiableAt_flowOf_prod hv hz
  rw [show (fun y ↦ flowOf v (τ y) (f y)) =
      (fun q : ℝ × M ↦ flowOf v q.1 q.2) ∘ fun y ↦ (τ y, f y) from rfl,
    mfderiv_comp z hΦ (hτ.prodMk hf), ContinuousLinearMap.comp_apply, mfderiv_prodMk hτ hf]
  -- Apply the differential of `(t, x) ↦ φₜ(x)` to the vector `(dτ w, df w)`.
  have h := mfderiv_flowOf_comp_apply (f := id) (p := (τ z, f z)) hv mdifferentiableAt_id hz
    ((mfderiv J 𝓘(ℝ) τ z).prod (mfderiv J I f z) w)
  rw [mfderiv_id, ContinuousLinearMap.id_apply] at h
  exact h

/-- **A function rescaled by a flow is differentiated to itself by the field.** If `F` is
differentiable at `x` and `F(φ_s x) = e^s F(x)` for `s` near `0`, then `dF(v) = F` at `x`. -/
theorem mvfderiv_apply_eq_of_comp_flowOf_eventuallyEq
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    {F : M → ℝ} {x : M} (hF : MDifferentiableAt I 𝓘(ℝ) F x)
    (heq : (F ∘ fun s ↦ flowOf v s x) =ᶠ[𝓝 0] fun s ↦ Real.exp s * F x) :
    mvfderiv I F x (v x) = F x := by
  have hcurve := hasDerivAt_comp_flowOf hv (mem_flowDomain_zero (hv x))
    (by rwa [flowOf_zero v])
  rw [flowOf_zero v] at hcurve
  refine hcurve.unique (HasDerivAt.congr_of_eventuallyEq ?_ heq)
  simpa using (Real.hasDerivAt_exp 0).mul_const (F x)

/-- **A function translated by a flow has unit derivative along the field.** If `F` is
differentiable at `x` and `F(φ_s x) = F(x) + s` for `s` near `0`, then `dF(v) = 1` at `x`. -/
theorem mvfderiv_apply_eq_one_of_eventually_apply_flowOf_eq_add
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    {F : M → ℝ} {x : M} (hF : MDifferentiableAt I 𝓘(ℝ) F x)
    (heq : ∀ᶠ s in 𝓝 0, F (flowOf v s x) = F x + s) :
    mvfderiv I F x (v x) = 1 := by
  have hcurve := hasDerivAt_comp_flowOf hv (mem_flowDomain_zero (hv x))
    (by rwa [flowOf_zero v])
  rw [flowOf_zero v] at hcurve
  exact ((((hasDerivAt_id' (0 : ℝ)).const_add (F x)).congr_of_eventuallyEq heq).unique
    hcurve).symm

/-- **Values swept by a local flow are regular.** If `f` is differentiable on the band
`a < f < b` and the maximal flow `φ` of `v` translates `f` at unit speed there,
`f (φ_t x) = f x + t` whenever `f x` and `f x + t` lie in `(a, b)`, then every value in `(a, b)`
is a regular value of `f`. No completeness of `v` is needed: only the times near `0`, at which the
flow is defined, enter. -/
theorem isRegularValue_of_apply_flowOf_eq_add
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    {f : M → ℝ} {a b : ℝ} (hf : ∀ x, f x ∈ Ioo a b → MDifferentiableAt I 𝓘(ℝ) f x)
    (hfv : ∀ x t, f x ∈ Ioo a b → f x + t ∈ Ioo a b → f (flowOf v t x) = f x + t)
    {c : ℝ} (hc : c ∈ Ioo a b) : IsRegularValue I 𝓘(ℝ) f c := by
  rw [isRegularValue_iff]
  rintro x rfl
  rw [isRegularPoint_iff_mvfderiv_ne_zero]
  intro h0
  have h1 := mvfderiv_apply_eq_one_of_eventually_apply_flowOf_eq_add hv (hf x hc) <| by
    filter_upwards [(isOpen_Ioo.preimage (by fun_prop : Continuous fun s ↦ f x + s)).mem_nhds
      (by simpa using hc)] with s hs
    exact hfv x s hc hs
  rw [h0] at h1
  exact zero_ne_one h1

/-- **The flow preserves its generating field.** If time `t` is defined at `x`, the derivative of
the time-`t` map of the flow carries `v x` to `v (flowOf v t x)`. -/
theorem mfderiv_flowOf_apply_self
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) {t : ℝ} {x : M}
    (ht : (t, x) ∈ flowDomain v) :
    mfderiv I I (flowOf v t) x (v x) = v (flowOf v t x) := by
  -- The velocity at time `0` of the trajectory through `y` is `v y`.
  have hvel : ∀ y, mfderiv 𝓘(ℝ) I (fun s ↦ flowOf v s y) 0 (1 : ℝ) = v y := fun y ↦
    (mfderiv_flowOf_trajectory_zero_apply hv y 1).trans (one_smul ℝ (v y))
  have hcurve : ContinuousAt (fun s ↦ flowOf v s x) 0 :=
    (mdifferentiableAt_flowOf hv (mem_flowDomain_zero (hv x))).continuousAt
  -- Near `s = 0`, flowing for time `s` and then `t` is flowing for time `t` and then `s`.
  have hcomm : (flowOf v t ∘ fun s ↦ flowOf v s x) =ᶠ[𝓝 0]
      fun s ↦ flowOf v s (flowOf v t x) := by
    have h₁ : ∀ᶠ s in 𝓝 (0 : ℝ), (s, x) ∈ flowDomain v :=
      (isOpen_setOf_mem_flowDomain hv continuous_id continuous_const).mem_nhds
        (mem_flowDomain_zero (hv x))
    have h₂ : ∀ᶠ s in 𝓝 (0 : ℝ), (t, flowOf v s x) ∈ flowDomain v :=
      (continuousAt_const.prodMk hcurve).preimage_mem_nhds
        ((isOpen_flowDomain hv).mem_nhds (by simpa only [flowOf_zero v x] using ht))
    have h₃ : ∀ᶠ s in 𝓝 (0 : ℝ), (s, flowOf v t x) ∈ flowDomain v :=
      (isOpen_setOf_mem_flowDomain hv continuous_id continuous_const).mem_nhds
        (mem_flowDomain_zero (hv _))
    filter_upwards [h₁, h₂, h₃] with s hs hts hst
    rw [comp_apply, (flowOf_add hv hs hts).2, (flowOf_add hv ht hst).2, add_comm]
  have key := mfderiv_comp_apply_of_eq (0 : ℝ) (mdifferentiableAt_flowOf_apply hv ht)
    (mdifferentiableAt_flowOf hv (mem_flowDomain_zero (hv x))) (flowOf_zero v x) (1 : ℝ)
  have hvel' : mfderiv 𝓘(ℝ) I (flowOf v t ∘ fun s ↦ flowOf v s x) 0 (1 : ℝ) =
      v (flowOf v t x) := by
    rw [hcomm.mfderiv_eq]
    -- `tangentSpaceCast` is the identity of the model space.
    exact hvel _
  rw [hvel] at key
  exact key.symm.trans hvel'

/-- **Differential of the composition of two local flow maps.** Along a trajectory of a `C¹`
vector field, applying the differential of the time-`s` map at `p` and then the differential of
the time-`t` map at `q = flowOf v s p` equals the differential of the time-`(s + t)` map at
`p`. -/
theorem mfderiv_flowOf_add_apply
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) {s t : ℝ} {p q : M}
    (hs : (s, p) ∈ flowDomain v) (hq : flowOf v s p = q) (ht : (t, q) ∈ flowDomain v)
    (w : TangentSpace I p) :
    -- The tangent spaces at `flowOf v t q` and `flowOf v (s + t) p` are both the model space `E`.
    @Eq E (mfderiv I I (flowOf v t) q (mfderiv I I (flowOf v s) p w))
      (mfderiv I I (flowOf v (s + t)) p w) := by
  have hΦs := mdifferentiableAt_flowOf_apply hv hs
  have hΦt := mdifferentiableAt_flowOf_apply hv ht
  have hev : (flowOf v t ∘ flowOf v s) =ᶠ[𝓝 p] flowOf v (s + t) := by
    have h₁ : ∀ᶠ z in 𝓝 p, (s, z) ∈ flowDomain v :=
      (isOpen_setOf_mem_flowDomain hv continuous_const continuous_id).mem_nhds hs
    have h₂ : ∀ᶠ z in 𝓝 p, (t, flowOf v s z) ∈ flowDomain v :=
      hΦs.continuousAt.preimage_mem_nhds
        ((isOpen_setOf_mem_flowDomain hv continuous_const continuous_id).mem_nhds (hq ▸ ht))
    filter_upwards [h₁, h₂] with z hsz htz
    exact (flowOf_add hv hsz htz).2
  exact (mfderiv_comp_apply_of_eq p hΦt hΦs hq w).symm.trans (DFunLike.congr_fun hev.mfderiv_eq w)

/-- Flowing back for time `-t` undoes the differential of the time-`t` map of a local flow:
`dφ₋ₜ (dφₜ w) = w` for every tangent vector `w` at `x`, wherever `φₜ x` is defined. -/
theorem mfderiv_flowOf_neg_mfderiv_flowOf_apply
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    {t : ℝ} {x : M} (ht : (t, x) ∈ flowDomain v) (w : TangentSpace I x) :
    -- The two sides are tangent vectors at `flowOf v (-t) (flowOf v t x)` and at `x`, which are
    -- equal but not definitionally; all tangent spaces are the model space `E`.
    @Eq E (mfderiv I I (flowOf v (-t)) (flowOf v t x) (mfderiv I I (flowOf v t) x w)) w :=
  (mfderiv_flowOf_add_apply hv ht rfl (neg_mem_flowDomain_flowOf hv ht) w).trans <| by
    rw [add_neg_cancel]
    exact mfderiv_flowOf_zero_apply_eq_self v x w

/-- The differential of the time-`t` map of a local flow undoes flowing back for time `-t`:
`dφₜ (dφ₋ₜ u) = u` for every tangent vector `u` at `φₜ x`, wherever `φₜ x` is defined. -/
theorem mfderiv_flowOf_mfderiv_flowOf_neg_apply
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    {t : ℝ} {x : M} (ht : (t, x) ∈ flowDomain v) (u : TangentSpace I (flowOf v t x)) :
    -- `dφ₋ₜ u` is a tangent vector at `flowOf v (-t) (flowOf v t x)`, which equals `x` but not
    -- definitionally; all tangent spaces are the model space, so the equation is stated in `E`.
    @Eq E (mfderiv I I (flowOf v t) x (mfderiv I I (flowOf v (-t)) (flowOf v t x) u)) u :=
  (mfderiv_flowOf_add_apply hv (neg_mem_flowDomain_flowOf hv ht) (flowOf_neg_flowOf hv ht) ht
    u).trans <| by
    rw [neg_add_cancel]
    exact mfderiv_flowOf_zero_apply_eq_self v _ u

/-- **The differential of a local flow map is bijective.** For a `C¹` vector field `v`, the
differential at `x` of the time-`t` map of its maximal flow is a bijection
`T_x M → T_(φₜ x) M` wherever `φₜ x` is defined, with inverse the differential at `φₜ x` of the
time-`(-t)` map. The field need not be complete. -/
theorem bijective_mfderiv_flowOf
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) {t : ℝ} {x : M}
    (ht : (t, x) ∈ flowDomain v) : Function.Bijective (mfderiv I I (flowOf v t) x) :=
  ⟨Function.LeftInverse.injective (g := mfderiv I I (flowOf v (-t)) (flowOf v t x))
      (mfderiv_flowOf_neg_mfderiv_flowOf_apply hv ht),
    Function.RightInverse.surjective (mfderiv_flowOf_mfderiv_flowOf_neg_apply hv ht)⟩

private def flowOfPeriods
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) (x : M) : AddSubgroup ℝ where
  carrier := {t | (t, x) ∈ flowDomain v ∧ flowOf v t x = x}
  zero_mem' := ⟨mem_flowDomain_zero (hv x), flowOf_zero v x⟩
  add_mem' := by
    rintro s t ⟨hs, hsfix⟩ ⟨ht, htfix⟩
    obtain ⟨hst, heq⟩ := flowOf_add hv hs (hsfix.symm ▸ ht)
    rw [hsfix, htfix] at heq
    exact ⟨hst, heq.symm⟩
  neg_mem' := by
    rintro t ⟨ht, htfix⟩
    refine ⟨htfix ▸ neg_mem_flowDomain_flowOf hv ht, ?_⟩
    have hneg := flowOf_neg_flowOf hv ht
    rwa [htfix] at hneg

/-- Near a point where a `C¹` field does not vanish, positive return times in its maximal
flow domain are uniformly bounded away from zero. The field need not be complete. -/
theorem exists_pos_period_le_nhds_flowOf
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) {x : M} (hx : v x ≠ 0) :
    ∃ ε > 0, ∃ U ∈ 𝓝 x, ∀ y ∈ U, ∀ T > 0,
      (T, y) ∈ flowDomain v → flowOf v T y = y → ε ≤ T := by
  have hex : ∃ s, flowOf v s x ≠ x := by
    by_contra! h
    have hconst : (fun s ↦ flowOf v s x) = (fun _ : ℝ ↦ x) := funext h
    have hd : @Eq E (Manifold.curveVelocity I (fun s ↦ flowOf v s x) 0) (v x) :=
      (curveVelocity_flowOf hv (mem_flowDomain_zero (hv x))).trans
        (congrArg (fun y : M ↦ (v y : E)) (flowOf_zero v x))
    rw [hconst, Manifold.curveVelocity_const] at hd
    exact hx hd.symm
  obtain ⟨s, hs⟩ := hex
  have hsdom : (s, x) ∈ flowDomain v := by
    by_contra hdom
    exact hs (flowOf_of_notMem hdom)
  have hflow := (mdifferentiableAt_flowOf_prod hv hsdom).continuousAt
  have hne : ∀ᶠ p : ℝ × M in 𝓝 (s, x), flowOf v p.1 p.2 ≠ p.2 :=
    (hflow.prodMk continuousAt_snd).preimage_mem_nhds
      ((isOpen_ne_fun continuous_fst continuous_snd).mem_nhds hs)
  have hnotMem : ∀ᶠ p : ℝ × M in 𝓝 (s, x), p.1 ∉ flowOfPeriods hv p.2 :=
    hne.mono fun _ hp hreturn ↦ hp hreturn.2
  obtain ⟨ε, hε, U, hU, hbound⟩ := exists_pos_period_le_nhds_of_eventually_not_mem hnotMem
  exact ⟨ε, hε, U, hU, fun y hy T hT hdom hfix ↦ hbound y hy T hT ⟨hdom, hfix⟩⟩

/-- At a finite right endpoint of a maximal interval, the trajectory eventually leaves every
compact set. -/
theorem eventually_flowOf_notMem
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) {x : M} {b : ℝ}
    (hb : IsLUB {t | (t, x) ∈ flowDomain v} b) {K : Set M} (hK : IsCompact K) :
    ∀ᶠ t in 𝓝[<] b, flowOf v t x ∉ K := by
  have hdomain : {t | (t, x) ∈ flowDomain v} = maximalIntegralCurveInterval v x :=
    Set.ext fun _ ↦ mem_flowDomain
  simpa only [flowOf_apply] using
    eventually_notMem_nhdsLT_maximalIntegralCurve hv (hdomain ▸ hb) hK

end C1

end CompleteModel

end TauCeti
