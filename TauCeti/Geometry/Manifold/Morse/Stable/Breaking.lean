/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Stable.Transversality
import Mathlib.Geometry.Manifold.Metrizable
import TauCeti.Dynamics.Flow.Breaking
import TauCeti.Dynamics.Flow.ConnectingOrbit
import TauCeti.Geometry.Manifold.Morse.CriticalPoints

/-!
# Breaking of trajectories and finiteness of index-one trajectories on a compact manifold

Let `f` be a Morse function on a compact boundaryless manifold `M`, and `X` a pseudo-gradient field
adapted to `f` satisfying the Morse–Smale condition. This file proves that for critical points `p`
and `q` with `ind p = ind q + 1`, and a value `c` strictly between `f q` and `f p`, the level slice

`W^u(p) ∩ W^s(q) ∩ {f = c}`

is finite. Since `f` decreases strictly from `f p` to `f q` along every trajectory from `p` to
`q`, each such trajectory crosses the level `c` exactly once, so the slice represents the
unparametrized trajectories from `p` to `q`, which the mod-two Morse boundary counts.

The slice is closed, hence compact, and discrete.

* **Closedness** comes from the way trajectories break. If points of an invariant set disjoint from
  `W^s(x)` accumulate on `W^s(x)`, their orbits follow the limit into `x`, linger there and leave
  along `W^u(x)`, so the closure of the set also meets `W^u(x)` away from `x`. This is
  `Flow.exists_mem_closure_inter_unstableSet_of_mem_closure_inter_stableSet`, applied in a metric
  compatible with the topology of `M`, around a ball containing no other critical point. Iterating
  it, under the Morse–Smale condition, shows that the closure of `W^s(q)` meets the stable manifolds
  only of critical points of index larger than `ind q`, and the closure of `W^u(p)` meets the
  unstable manifolds only of critical points of index smaller than `ind p`. When the indices
  differ by one, a limit of points of the slice can therefore only lie on a trajectory from `p` to
  `q`.
* **Discreteness** comes from transversality. At a point `y` of the slice, the tangent space of
  `W^u(p) ∩ W^s(q)` is the line spanned by the velocity `X y`, on which `df_y` does not vanish,
  while `df_y` vanishes on the tangent cone of the level slice. So that tangent cone is zero, and
  `y` is isolated in the slice.

These are the manifold forms of the results of `TauCeti.Analysis.Calculus.Morse.Breaking` for a
negative-gradient flow on a vector space. On a compact manifold, compactness is supplied by the
ambient space.

## Main results

* `TauCeti.IsAdaptedPseudoGradient.mem_stableSet_of_forall_mem` and
  `TauCeti.IsAdaptedPseudoGradient.mem_unstableSet_of_forall_mem`: an orbit trapped in a closed set
  whose only critical point is `x` converges to `x`.
* `IsAdaptedPseudoGradient.exists_mem_closure_inter_unstableSet_of_mem_closure_inter_stableSet`
  and its time reversal: limits of trajectories break at a critical point.
* `IsMorseSmale.manifoldMorseIndex_lt_of_mem_closure_stableSet_inter_stableSet` and its time
  reversal `IsMorseSmale.manifoldMorseIndex_lt_of_mem_closure_unstableSet_inter_unstableSet`, in
  the namespace `TauCeti.IsAdaptedPseudoGradient`:
  the Morse index strictly increases (respectively decreases) at the critical points whose stable
  (respectively unstable) manifolds meet the closure of `W^s(q)` (respectively `W^u(p)`).
* `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.isClosed_unstableSet_inter_stableSet_inter_level`:
  an index-one level slice is closed.
* `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.isDiscrete_unstableSet_inter_stableSet_inter_level`:
  an index-one level slice is discrete.
* `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.finite_unstableSet_inter_stableSet_inter_level`:
  an index-one level slice is finite.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 3 (compactness of spaces of trajectories).
-/

public section

open Filter Metric Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} {x : M}

omit [FiniteDimensional ℝ E] in
/-- Near a critical point `x` of a Morse function on a compact manifold there is no other critical
point. -/
private theorem eventually_eq_of_mfderiv_eq_zero (hf : IsMorse 𝓘(ℝ, E) f) :
    ∀ᶠ z in 𝓝 x, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f z = 0 → z = x := by
  have hfin : {z : M | mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f z = 0}.Finite := by
    simpa only [criticalPoints_eq_setOf_mfderiv_eq_zero] using hf.finite_criticalPoints
  filter_upwards [(hfin.sdiff (t := {x})).isClosed.compl_mem_nhds (by simp)] with z hz hcrit
  by_contra hzx
  exact hz ⟨hcrit, hzx⟩

namespace IsAdaptedPseudoGradient

variable (hX : IsAdaptedPseudoGradient f X)
include hX

/-- **An orbit trapped near a critical point converges to it.** If the forward orbit of `w` stays
in a closed set `K` whose only critical point of the Morse function `f` is `x`, then the orbit
converges to `x`. -/
theorem mem_stableSet_of_forall_mem (hf : IsMorse 𝓘(ℝ, E) f) {K : Set M} (hK : IsClosed K)
    (hKx : ∀ z ∈ K, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f z = 0 → z = x) {w : M}
    (hw : ∀ t, 0 ≤ t → hX.flow t w ∈ K) : w ∈ hX.flow.stableSet x := by
  obtain ⟨z, hz, hlim⟩ := hX.exists_tendsto_atTop hf w
  rw [hKx z (hK.mem_of_tendsto hlim (eventually_atTop.2 ⟨0, hw⟩)) hz] at hlim
  exact Flow.mem_stableSet.2 hlim

/-- **An orbit trapped near a critical point in backward time converges to it.** If the backward
orbit of `w` stays in a closed set `K` whose only critical point of the Morse function `f` is `x`,
then the orbit converges to `x` in backward time. -/
theorem mem_unstableSet_of_forall_mem (hf : IsMorse 𝓘(ℝ, E) f) {K : Set M} (hK : IsClosed K)
    (hKx : ∀ z ∈ K, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f z = 0 → z = x) {w : M}
    (hw : ∀ t, t ≤ 0 → hX.flow t w ∈ K) : w ∈ hX.flow.unstableSet x := by
  obtain ⟨z, hz, hlim⟩ := hX.exists_tendsto_atBot hf w
  rw [hKx z (hK.mem_of_tendsto hlim (eventually_atBot.2 ⟨0, hw⟩)) hz] at hlim
  exact Flow.mem_unstableSet.2 hlim

/-- **Limits of trajectories break at a critical point.** Let `x` be a critical point of the Morse
function `f`, and `S` a set invariant under the flow and disjoint from the stable manifold `W^s(x)`.
If the closure of `S` meets `W^s(x)`, then it also meets the unstable manifold `W^u(x)` at a point
other than `x`. -/
theorem exists_mem_closure_inter_unstableSet_of_mem_closure_inter_stableSet
    (hf : IsMorse 𝓘(ℝ, E) f) {S : Set M} (hS : IsInvariant hX.flow S)
    (hSx : Disjoint S (hX.flow.stableSet x)) {y : M} (hy : y ∈ closure S ∩ hX.flow.stableSet x) :
    ∃ z ∈ closure S ∩ hX.flow.unstableSet x, z ≠ x := by
  have := Manifold.metrizableSpace 𝓘(ℝ, E) M
  let _ : MetricSpace M := TopologicalSpace.metrizableSpaceMetric M
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (eventually_eq_of_mfderiv_eq_zero hf)
  have hK : ∀ z ∈ closedBall x (ε / 2), mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f z = 0 → z = x := fun z hz ↦
    hball (closedBall_subset_ball (half_lt_self hε) hz)
  obtain ⟨z, hz, hzx⟩ := Flow.exists_mem_closure_inter_unstableSet_of_mem_closure_inter_stableSet
    (half_pos hε) (isClosed_sphere.isCompact)
    (fun w ↦ hX.mem_stableSet_of_forall_mem hf isClosed_closedBall hK)
    (fun w ↦ hX.mem_unstableSet_of_forall_mem hf isClosed_closedBall hK) hS hSx hy
  refine ⟨z, hz, fun h ↦ ?_⟩
  rw [h, dist_self] at hzx
  exact (half_pos hε).ne hzx

/-- **Limits of trajectories break at a critical point, in backward time.** Let `x` be a critical
point of the Morse function `f`, and `S` a set invariant under the flow and disjoint from the
unstable manifold `W^u(x)`. If the closure of `S` meets `W^u(x)`, then it also meets the stable
manifold `W^s(x)` at a point other than `x`. -/
theorem exists_mem_closure_inter_stableSet_of_mem_closure_inter_unstableSet
    (hf : IsMorse 𝓘(ℝ, E) f) {S : Set M} (hS : IsInvariant hX.flow S)
    (hSx : Disjoint S (hX.flow.unstableSet x)) {y : M}
    (hy : y ∈ closure S ∩ hX.flow.unstableSet x) :
    ∃ z ∈ closure S ∩ hX.flow.stableSet x, z ≠ x := by
  have := Manifold.metrizableSpace 𝓘(ℝ, E) M
  let _ : MetricSpace M := TopologicalSpace.metrizableSpaceMetric M
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (eventually_eq_of_mfderiv_eq_zero hf)
  have hK : ∀ z ∈ closedBall x (ε / 2), mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f z = 0 → z = x := fun z hz ↦
    hball (closedBall_subset_ball (half_lt_self hε) hz)
  obtain ⟨z, hz, hzx⟩ := Flow.exists_mem_closure_inter_stableSet_of_mem_closure_inter_unstableSet
    (half_pos hε) (isClosed_sphere.isCompact)
    (fun w ↦ hX.mem_stableSet_of_forall_mem hf isClosed_closedBall hK)
    (fun w ↦ hX.mem_unstableSet_of_forall_mem hf isClosed_closedBall hK) hS hSx hy
  refine ⟨z, hz, fun h ↦ ?_⟩
  rw [h, dist_self] at hzx
  exact (half_pos hε).ne hzx

omit hX in
/-- **The Morse index increases along a broken forward limit.** Under the Morse–Smale condition, if
the closure of the stable manifold of a critical point `q` meets the stable manifold of a different
critical point `b`, then `ind q < ind b`. -/
theorem IsMorseSmale.manifoldMorseIndex_lt_of_mem_closure_stableSet_inter_stableSet
    {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f) {b q : M}
    (hb : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f b = 0) (hq : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0) (hbq : b ≠ q)
    (hne : (closure (hX.flow.stableSet q) ∩ hX.flow.stableSet b).Nonempty) :
    manifoldMorseIndex 𝓘(ℝ, E) f q < manifoldMorseIndex 𝓘(ℝ, E) f b := by
  have hdf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f := hf.contMDiff.mdifferentiable (by simp)
  -- Break the limit at `b` and follow the outgoing orbit to the next critical point `a`, of
  -- smaller index; then induct on the index of `b`.
  induction hn : manifoldMorseIndex 𝓘(ℝ, E) f b using Nat.strong_induction_on generalizing b with
  | _ n ih =>
    obtain ⟨y, hy⟩ := hne
    obtain ⟨z, hz, hzb⟩ := hX.exists_mem_closure_inter_unstableSet_of_mem_closure_inter_stableSet hf
      (Flow.isInvariant_stableSet _ q) (Flow.disjoint_stableSet hbq.symm) hy
    obtain ⟨a, ha, hza⟩ := hX.exists_tendsto_atTop hf z
    have hza : z ∈ hX.flow.stableSet a := Flow.mem_stableSet.2 hza
    have hba : b ≠ a := fun hba ↦
      hzb (hX.eq_of_mem_unstableSet_inter_stableSet hdf ⟨hz.2, hba ▸ hza⟩)
    have hlt := h.manifoldMorseIndex_lt hf hb ha hba ⟨z, hz.2, hza⟩
    by_cases haq : a = q
    · subst haq
      omega
    · have := ih _ (by omega) ha haq ⟨z, hz.1, hza⟩ rfl
      omega

omit hX in
/-- **The Morse index decreases along a broken backward limit.** Under the Morse–Smale condition, if
the closure of the unstable manifold of a critical point `p` meets the unstable manifold of a
different critical point `a`, then `ind a < ind p`. -/
theorem IsMorseSmale.manifoldMorseIndex_lt_of_mem_closure_unstableSet_inter_unstableSet
    {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f) {a p : M}
    (ha : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f a = 0) (hp : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f p = 0) (hap : a ≠ p)
    (hne : (closure (hX.flow.unstableSet p) ∩ hX.flow.unstableSet a).Nonempty) :
    manifoldMorseIndex 𝓘(ℝ, E) f a < manifoldMorseIndex 𝓘(ℝ, E) f p := by
  have hdf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f := hf.contMDiff.mdifferentiable (by simp)
  -- Break the limit at `a` and follow the incoming orbit back to the previous critical point `b`,
  -- of larger index; then induct on the codimension `n - ind a`.
  induction hn : Module.finrank ℝ E - manifoldMorseIndex 𝓘(ℝ, E) f a
    using Nat.strong_induction_on generalizing a with
  | _ n ih =>
    obtain ⟨y, hy⟩ := hne
    obtain ⟨z, hz, hza⟩ := hX.exists_mem_closure_inter_stableSet_of_mem_closure_inter_unstableSet hf
      (Flow.isInvariant_unstableSet _ p) (Flow.disjoint_unstableSet hap.symm) hy
    obtain ⟨b, hb, hzb⟩ := hX.exists_tendsto_atBot hf z
    have hzb : z ∈ hX.flow.unstableSet b := Flow.mem_unstableSet.2 hzb
    have hba : b ≠ a := fun hba ↦
      hza (hX.eq_of_mem_unstableSet_inter_stableSet hdf ⟨hba ▸ hzb, hz.2⟩)
    have hlt := h.manifoldMorseIndex_lt hf hb ha hba ⟨z, hzb, hz.2⟩
    by_cases hbp : b = p
    · subst hbp
      exact hlt
    · have hle := manifoldMorseIndex_le_finrank (I := 𝓘(ℝ, E)) (f := f) (x := b)
      exact hlt.trans (ih _ (by omega) hb hbp ⟨z, hz.1, hzb⟩ rfl)

omit hX in
/-- **An index-one level slice is closed.** Under the Morse–Smale condition, if the critical points
`p` and `q` have Morse indices differing by one, then the points of the trajectories from `p` to `q`
lying on a level `c` strictly between `f q` and `f p` form a closed set. -/
theorem IsMorseSmale.isClosed_unstableSet_inter_stableSet_inter_level
    {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f) {p q : M}
    (hp : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f p = 0) (hq : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0)
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1) {c : ℝ}
    (hc : f q < c ∧ c < f p) :
    IsClosed (hX.flow.unstableSet p ∩ hX.flow.stableSet q ∩ {z | f z = c}) := by
  have hdf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f := hf.contMDiff.mdifferentiable (by simp)
  refine isClosed_of_closure_subset fun y hy ↦ ?_
  have hyU : y ∈ closure (hX.flow.unstableSet p) :=
    closure_mono (inter_subset_left.trans inter_subset_left) hy
  have hyS : y ∈ closure (hX.flow.stableSet q) :=
    closure_mono (inter_subset_left.trans inter_subset_right) hy
  have hyc : f y = c := (isClosed_eq hdf.continuous continuous_const).closure_subset
    (closure_mono inter_subset_right hy)
  -- The limit `y` lies on a trajectory from some critical point `a` to some critical point `b`.
  obtain ⟨a, ha, hya⟩ := hX.exists_tendsto_atBot hf y
  obtain ⟨b, hb, hyb⟩ := hX.exists_tendsto_atTop hf y
  have hya : y ∈ hX.flow.unstableSet a := Flow.mem_unstableSet.2 hya
  have hyb : y ∈ hX.flow.stableSet b := Flow.mem_stableSet.2 hyb
  -- A trajectory from a critical point to itself is constant, and lies off the level `c`.
  have hne : ∀ {x}, f x ≠ c → y ∈ hX.flow.unstableSet x ∩ hX.flow.stableSet x → False :=
    fun hx hy' ↦ hx (hX.eq_of_mem_unstableSet_inter_stableSet hdf hy' ▸ hyc)
  have hba : manifoldMorseIndex 𝓘(ℝ, E) f b ≤ manifoldMorseIndex 𝓘(ℝ, E) f a := by
    by_cases hab : a = b
    · rw [hab]
    · exact (h.manifoldMorseIndex_lt hf ha hb hab ⟨y, hya, hyb⟩).le
  -- The index of `a` is at most that of `p`, with equality only if `a = p`, and the index of `b`
  -- is at least that of `q`, with equality only if `b = q`. As the two differ by one, `a = p` and
  -- `b = q`: any other configuration forces a constant trajectory through `y` at `p` or `q`.
  have hap : a = p ∨ manifoldMorseIndex 𝓘(ℝ, E) f a < manifoldMorseIndex 𝓘(ℝ, E) f p :=
    or_iff_not_imp_left.2 fun hap ↦
      h.manifoldMorseIndex_lt_of_mem_closure_unstableSet_inter_unstableSet hf ha hp hap
        ⟨y, hyU, hya⟩
  have hbq : b = q ∨ manifoldMorseIndex 𝓘(ℝ, E) f q < manifoldMorseIndex 𝓘(ℝ, E) f b :=
    or_iff_not_imp_left.2 fun hbq ↦
      h.manifoldMorseIndex_lt_of_mem_closure_stableSet_inter_stableSet hf hb hq hbq ⟨y, hyS, hyb⟩
  have hab : a ≠ b := by
    rintro rfl
    rcases hap with rfl | hap
    · exact hne hc.2.ne' ⟨hya, hyb⟩
    rcases hbq with rfl | hbq
    · exact hne hc.1.ne ⟨hya, hyb⟩
    omega
  have hlt := h.manifoldMorseIndex_lt hf ha hb hab ⟨y, hya, hyb⟩
  obtain rfl : a = p := by
    rcases hap with hap | hap
    · exact hap
    rcases hbq with rfl | hbq <;> omega
  obtain rfl : b = q := by
    rcases hbq with hbq | hbq
    · exact hbq
    omega
  exact ⟨⟨hya, hyb⟩, hyc⟩

omit hX in
/-- **An index-one level slice is discrete.** Under the Morse–Smale condition, if the critical
points `p` and `q` have Morse indices differing by one, then on every level `c` the points of the
trajectories from `p` to `q` form a discrete set. -/
theorem IsMorseSmale.isDiscrete_unstableSet_inter_stableSet_inter_level
    {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f) {p q : M}
    (hp : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f p = 0) (hq : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0)
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1) (c : ℝ) :
    IsDiscrete (hX.flow.unstableSet p ∩ hX.flow.stableSet q ∩ {z | f z = c}) := by
  have hdf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f := hf.contMDiff.mdifferentiable (by simp)
  have hpq : p ≠ q := by
    rintro rfl
    omega
  refine isDiscrete_iff_discreteTopology.2 (discreteTopology_of_noAccPts fun y hy hacc ↦ ?_)
  obtain ⟨⟨hyu, hys⟩, hyc⟩ := hy
  obtain ⟨v, hv, hv0⟩ := mtangentConeAt_nonempty_of_accPt (I := 𝓘(ℝ, E)) hacc
  -- The tangent space `T` of `W^u(p) ∩ W^s(q)` at `y` is a line containing `X y ≠ 0`.
  set T := Submodule.span ℝ
    (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet p ∩ hX.flow.stableSet q) y) with hTdef
  have hT : Module.finrank ℝ T = 1 := by
    have := hX.finrank_span_mtangentConeAt_unstableSet_inter_stableSet_add_manifoldMorseIndex hf hp
      hq ⟨hyu, hys⟩ (h.span_mtangentConeAt_sup_eq_top hp hq ⟨hyu, hys⟩)
    rw [← hTdef] at this
    omega
  have hXT : X y ∈ T := Submodule.subset_span (hX.mem_mtangentConeAt_of_isInvariant
    (fun t _ hz ↦ ⟨Flow.isInvariant_unstableSet _ p t hz.1, Flow.isInvariant_stableSet _ q t hz.2⟩)
    ⟨hyu, hys⟩)
  have hX0 : X y ≠ 0 := fun h0 ↦ by
    have hfix := hX.flow_apply_of_mfderiv_eq_zero (hX.eq_zero_iff.1 h0)
    exact zero_ne_one (Flow.orbit_injective_of_ne_of_mem_unstableSet_inter_stableSet hpq
      ⟨hyu, hys⟩ (by simp [hfix]))
  obtain ⟨r, hr⟩ := (finrank_eq_one_iff_of_nonzero' (⟨X y, hXT⟩ : T)
    fun h0 ↦ hX0 (congrArg Subtype.val h0)).1 hT
    ⟨v, Submodule.subset_span (mtangentConeAt_mono inter_subset_left y hv)⟩
  have hrv : r • X y = v := congrArg Subtype.val hr
  -- `df_y` vanishes on the tangent cone of the level slice, but not on `X y`.
  have hdv : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y v = 0 :=
    mfderiv_apply_eq_zero_of_mem_mtangentConeAt (hdf y)
      (s := hX.flow.unstableSet p ∩ hX.flow.stableSet q ∩ {z | f z = c})
      (fun z hz ↦ hz.2.trans hyc.symm) hv
  have hdX : mvfderiv 𝓘(ℝ, E) f y (X y) < 0 :=
    hX.mvfderiv_apply_lt_zero y fun h0 ↦ hX0 (hX.eq_zero_iff.2 h0)
  have hdv' : r * mvfderiv 𝓘(ℝ, E) f y (X y) = 0 := by
    rw [← smul_eq_mul, ← map_smul, hrv]
    -- `mvfderiv` is `mfderiv` read through `NormedSpace.fromTangentSpace`, the identity of `ℝ`.
    exact (congrArg (NormedSpace.fromTangentSpace (f y)) hdv).trans (map_zero _)
  rcases mul_eq_zero.1 hdv' with hr0 | h0
  · exact hv0 (by rw [← hrv, hr0, zero_smul]; rfl)
  · exact hdX.ne h0

omit hX in
/-- **Finiteness of the index-one trajectories.** Under the Morse–Smale condition, if the critical
points `p` and `q` have Morse indices differing by one, then only finitely many trajectories run
from `p` to `q`: their points on a level `c` strictly between `f q` and `f p` form a finite set.
This is the finiteness behind the coefficients of the mod-two Morse boundary. -/
theorem IsMorseSmale.finite_unstableSet_inter_stableSet_inter_level
    {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f) {p q : M}
    (hp : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f p = 0) (hq : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0)
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1) {c : ℝ}
    (hc : f q < c ∧ c < f p) :
    (hX.flow.unstableSet p ∩ hX.flow.stableSet q ∩ {z | f z = c}).Finite :=
  (h.isClosed_unstableSet_inter_stableSet_inter_level hf hp hq hind hc).isCompact.finite
    (h.isDiscrete_unstableSet_inter_stableSet_inter_level hf hp hq hind c)

end IsAdaptedPseudoGradient

end TauCeti
