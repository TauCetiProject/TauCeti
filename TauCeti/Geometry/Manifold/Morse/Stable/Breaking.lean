/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Stable.LevelSlice
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
  it, along the strict decrease of `f` through the finitely many critical points, shows that the
  closure of `W^s(q)` meets the stable manifolds only of points from which a chain of trajectories
  runs to `q`, and the closure of `W^u(p)` meets the unstable manifolds only of points to which a
  chain of trajectories runs from `p`. As the Morse index drops along each trajectory under the
  Morse–Smale condition, besides `W^s(q)` itself, the closure of `W^s(q)` meets the stable
  manifolds only of critical points of index larger than `ind q`, and besides `W^u(p)` itself, the
  closure of `W^u(p)` meets the unstable manifolds only of critical points of index smaller than
  `ind p`. When the indices differ by one, a limit of points of the
  slice can therefore only lie on a trajectory from `p` to `q`.
* **Discreteness** comes from transversality: under the Morse–Smale condition the slice is
  discrete when the indices differ by one, by
  `TauCeti.IsAdaptedPseudoGradient.isDiscrete_unstableSet_inter_stableSet_level`.

These are the manifold forms of the results of `TauCeti.Analysis.Calculus.Morse.Breaking` for a
negative-gradient flow on a vector space. On a compact manifold, compactness is supplied by the
ambient space.

## Main results

* `IsAdaptedPseudoGradient.exists_tendsto_mem_unstableSet_of_tendsto_mem_stableSet` and its time
  reversal: a sequence converging into a stable (respectively unstable) manifold from outside it
  has orbit points, at times tending to `+∞` (respectively `-∞`), converging to the unstable
  (respectively stable) manifold.
* `IsAdaptedPseudoGradient.exists_mem_closure_inter_unstableSet_of_mem_closure_inter_stableSet`
  and its time reversal: limits of trajectories break at a critical point.
* `reflTransGen_of_mem_closure_unstableSet` and its time reversal
  `reflTransGen_of_mem_closure_stableSet`, in the namespace
  `TauCeti.IsAdaptedPseudoGradient`: if the closure of `W^u(p)` meets `W^u(a)`, then a chain of
  trajectories runs from `p` to `a` (respectively, if the closure of `W^s(q)` meets `W^s(b)`, then
  a chain of trajectories runs from `b` to `q`).
* `IsMorseSmale.manifoldMorseIndex_lt_of_mem_closure_stableSet_inter_stableSet` and its time
  reversal `IsMorseSmale.manifoldMorseIndex_lt_of_mem_closure_unstableSet_inter_unstableSet`, in
  the namespace `TauCeti.IsAdaptedPseudoGradient`:
  the Morse index strictly increases (respectively decreases) at the critical points other than `q`
  (respectively `p`) whose stable (respectively unstable) manifolds meet the closure of `W^s(q)`
  (respectively `W^u(p)`).
* `IsMorseSmale.nonempty_unstableSet_inter_stableSet_of_mem_closure_unstableSet_inter_unstableSet`
  and its time reversal
  `IsMorseSmale.nonempty_unstableSet_inter_stableSet_of_mem_closure_stableSet_inter_stableSet`, in
  the namespace `TauCeti.IsAdaptedPseudoGradient`: when the index drops by exactly one, a critical
  point whose unstable manifold meets the closure of `W^u(p)` is joined to `p` by a trajectory,
  and dually for the stable manifolds meeting the closure of `W^s(q)`.
* `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.isClosed_unstableSet_inter_stableSet_inter_level`:
  an index-one level slice is closed.
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

namespace IsAdaptedPseudoGradient

variable (hX : IsAdaptedPseudoGradient f X)
include hX

/-- **Sequences converging into a stable manifold break at its critical point.** Let `x` be a
point and `u` a sequence converging to a point `y` of the stable manifold `W^s(x)`, with infinitely
many terms off `W^s(x)`. Then along a subsequence, the points of the orbits of `u` at times tending
to `+∞` converge to a point of the unstable manifold `W^u(x)` other than `x`. -/
theorem exists_tendsto_mem_unstableSet_of_tendsto_mem_stableSet (hf : IsMorse 𝓘(ℝ, E) f) {y : M}
    (hy : y ∈ hX.flow.stableSet x) {u : ℕ → M} (hu : Tendsto u atTop (𝓝 y))
    (hux : ∃ᶠ n in atTop, u n ∉ hX.flow.stableSet x) :
    ∃ z ∈ hX.flow.unstableSet x, z ≠ x ∧ ∃ (n : ℕ → ℕ) (t : ℕ → ℝ),
      Tendsto n atTop atTop ∧ Tendsto t atTop atTop ∧
        Tendsto (fun k ↦ hX.flow (t k) (u (n k))) atTop (𝓝 z) := by
  have := Manifold.metrizableSpace 𝓘(ℝ, E) M
  let _ : MetricSpace M := TopologicalSpace.metrizableSpaceMetric M
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (hf.eventually_eq_of_mem_criticalPoints x)
  have hK : ∀ z ∈ closedBall x (ε / 2), mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f z = 0 → z = x := fun z hz hz0 ↦
    hball (closedBall_subset_ball (half_lt_self hε) hz)
      (mem_criticalPoints_iff_mfderiv_eq_zero.2 hz0)
  obtain ⟨z, hz, hzx, n, t, hn, ht, hlim⟩ :=
    Flow.exists_tendsto_mem_unstableSet_of_tendsto_mem_stableSet (half_pos hε)
      (isClosed_sphere.isCompact)
      (fun w ↦ hX.mem_stableSet_of_forall_mem hf isClosed_closedBall hK)
      (fun w ↦ hX.mem_unstableSet_of_forall_mem hf isClosed_closedBall hK) hy hu hux
  refine ⟨z, hz, fun h ↦ ?_, n, t, hn, ht, hlim⟩
  rw [h, dist_self] at hzx
  exact (half_pos hε).ne hzx

/-- **Sequences converging into an unstable manifold break at its critical point.** Let `x` be a
point and `u` a sequence converging to a point `y` of the unstable manifold `W^u(x)`, with
infinitely many terms off `W^u(x)`. Then along a subsequence, the points of the orbits of `u` at
times tending to `-∞` converge to a point of the stable manifold `W^s(x)` other than `x`. -/
theorem exists_tendsto_mem_stableSet_of_tendsto_mem_unstableSet (hf : IsMorse 𝓘(ℝ, E) f) {y : M}
    (hy : y ∈ hX.flow.unstableSet x) {u : ℕ → M} (hu : Tendsto u atTop (𝓝 y))
    (hux : ∃ᶠ n in atTop, u n ∉ hX.flow.unstableSet x) :
    ∃ z ∈ hX.flow.stableSet x, z ≠ x ∧ ∃ (n : ℕ → ℕ) (t : ℕ → ℝ),
      Tendsto n atTop atTop ∧ Tendsto t atTop atBot ∧
        Tendsto (fun k ↦ hX.flow (t k) (u (n k))) atTop (𝓝 z) := by
  have := Manifold.metrizableSpace 𝓘(ℝ, E) M
  let _ : MetricSpace M := TopologicalSpace.metrizableSpaceMetric M
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (hf.eventually_eq_of_mem_criticalPoints x)
  have hK : ∀ z ∈ closedBall x (ε / 2), mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f z = 0 → z = x := fun z hz hz0 ↦
    hball (closedBall_subset_ball (half_lt_self hε) hz)
      (mem_criticalPoints_iff_mfderiv_eq_zero.2 hz0)
  obtain ⟨z, hz, hzx, n, t, hn, ht, hlim⟩ :=
    Flow.exists_tendsto_mem_stableSet_of_tendsto_mem_unstableSet (half_pos hε)
      (isClosed_sphere.isCompact)
      (fun w ↦ hX.mem_stableSet_of_forall_mem hf isClosed_closedBall hK)
      (fun w ↦ hX.mem_unstableSet_of_forall_mem hf isClosed_closedBall hK) hy hu hux
  refine ⟨z, hz, fun h ↦ ?_, n, t, hn, ht, hlim⟩
  rw [h, dist_self] at hzx
  exact (half_pos hε).ne hzx

/-- **Limits of trajectories break at a critical point.** Let `x` be a critical point of the Morse
function `f`, and `S` a set invariant under the flow and disjoint from the stable manifold `W^s(x)`.
If the closure of `S` meets `W^s(x)`, then it also meets the unstable manifold `W^u(x)` at a point
other than `x`. -/
theorem exists_mem_closure_inter_unstableSet_of_mem_closure_inter_stableSet
    (hf : IsMorse 𝓘(ℝ, E) f) {S : Set M} (hS : IsInvariant hX.flow S)
    (hSx : Disjoint S (hX.flow.stableSet x)) {y : M} (hy : y ∈ closure S ∩ hX.flow.stableSet x) :
    ∃ z ∈ closure S ∩ hX.flow.unstableSet x, z ≠ x := by
  have := Manifold.metrizableSpace 𝓘(ℝ, E) M
  obtain ⟨u, huS, hu⟩ := mem_closure_iff_seq_limit.1 hy.1
  obtain ⟨z, hz, hzx, n, t, -, -, hlim⟩ :=
    hX.exists_tendsto_mem_unstableSet_of_tendsto_mem_stableSet hf hy.2 hu
      (Frequently.of_forall fun n ↦ hSx.notMem_of_mem_left (huS n))
  exact ⟨z, ⟨mem_closure_of_tendsto hlim (Eventually.of_forall fun k ↦ hS _ (huS _)), hz⟩, hzx⟩

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
  obtain ⟨u, huS, hu⟩ := mem_closure_iff_seq_limit.1 hy.1
  obtain ⟨z, hz, hzx, n, t, -, -, hlim⟩ :=
    hX.exists_tendsto_mem_stableSet_of_tendsto_mem_unstableSet hf hy.2 hu
      (Frequently.of_forall fun n ↦ hSx.notMem_of_mem_left (huS n))
  exact ⟨z, ⟨mem_closure_of_tendsto hlim (Eventually.of_forall fun k ↦ hS _ (huS _)), hz⟩, hzx⟩

omit hX in
/-- **The closure of `W^u(p)` meets only unstable manifolds below `p`.** If a point of the closure
of `W^u(p)` lies on `W^u(a)`, then a chain of trajectories runs from `p` to `a`. -/
theorem reflTransGen_of_mem_closure_unstableSet {hX : IsAdaptedPseudoGradient f X}
    (hf : IsMorse 𝓘(ℝ, E) f) {p a y : M}
    (hy : y ∈ closure (hX.flow.unstableSet p)) (hya : y ∈ hX.flow.unstableSet a) :
    Relation.ReflTransGen hX.FlowsTo p a := by
  -- Break the limit at `a` and follow the incoming orbit back to the previous critical point `b`,
  -- with `f a < f b`; then induct on the number of critical points with value above `f a`.
  induction hn : {c ∈ criticalPoints 𝓘(ℝ, E) f | f a < f c}.ncard
    using Nat.strong_induction_on generalizing a y with
  | _ n ih =>
    rcases eq_or_ne p a with rfl | hpa
    · exact Relation.ReflTransGen.refl
    obtain ⟨z, hz, hza⟩ := hX.exists_mem_closure_inter_stableSet_of_mem_closure_inter_unstableSet
      hf (Flow.isInvariant_unstableSet _ p) (Flow.disjoint_unstableSet hpa) ⟨hy, hya⟩
    obtain ⟨b, hb, hzb⟩ := hX.exists_tendsto_atBot hf z
    have hzb : z ∈ hX.flow.unstableSet b := Flow.mem_unstableSet.2 hzb
    have hba : b ≠ a := fun hba ↦
      hza (hX.eq_of_mem_unstableSet_inter_stableSet ⟨hba ▸ hzb, hz.2⟩)
    have hab := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hba ⟨hzb, hz.2⟩
    have hab : f a < f b := hab.1.trans hab.2
    have hlt : {c ∈ criticalPoints 𝓘(ℝ, E) f | f b < f c}.ncard <
        {c ∈ criticalPoints 𝓘(ℝ, E) f | f a < f c}.ncard := by
      refine ncard_lt_ncard ((ssubset_iff_of_subset fun c hc ↦ ?_).2 ?_)
        (hf.finite_criticalPoints.subset (sep_subset _ _))
      · exact ⟨hc.1, hab.trans hc.2⟩
      · exact ⟨b, ⟨mem_criticalPoints_iff_mfderiv_eq_zero.2 hb, hab⟩, fun hb' ↦ lt_irrefl _ hb'.2⟩
    exact (ih _ (hn ▸ hlt) hz.1 hzb rfl).tail (flowsTo_iff.2 ⟨z, hzb, hz.2⟩)

omit hX in
/-- **The closure of `W^s(q)` meets only stable manifolds above `q`.** If a point of the closure of
`W^s(q)` lies on `W^s(b)`, then a chain of trajectories runs from `b` to `q`. -/
theorem reflTransGen_of_mem_closure_stableSet {hX : IsAdaptedPseudoGradient f X}
    (hf : IsMorse 𝓘(ℝ, E) f) {q b y : M}
    (hy : y ∈ closure (hX.flow.stableSet q)) (hyb : y ∈ hX.flow.stableSet b) :
    Relation.ReflTransGen hX.FlowsTo b q := by
  -- Break the limit at `b` and follow the outgoing orbit to the next critical point `a`, with
  -- `f a < f b`; then induct on the number of critical points with value below `f b`.
  induction hn : {c ∈ criticalPoints 𝓘(ℝ, E) f | f c < f b}.ncard
    using Nat.strong_induction_on generalizing b y with
  | _ n ih =>
    rcases eq_or_ne q b with rfl | hqb
    · exact Relation.ReflTransGen.refl
    obtain ⟨z, hz, hzb⟩ := hX.exists_mem_closure_inter_unstableSet_of_mem_closure_inter_stableSet
      hf (Flow.isInvariant_stableSet _ q) (Flow.disjoint_stableSet hqb) ⟨hy, hyb⟩
    obtain ⟨a, ha, hza⟩ := hX.exists_tendsto_atTop hf z
    have hza : z ∈ hX.flow.stableSet a := Flow.mem_stableSet.2 hza
    have hba : b ≠ a := fun hba ↦
      hzb (hX.eq_of_mem_unstableSet_inter_stableSet ⟨hz.2, hba ▸ hza⟩)
    have hab := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hba ⟨hz.2, hza⟩
    have hab : f a < f b := hab.1.trans hab.2
    have hlt : {c ∈ criticalPoints 𝓘(ℝ, E) f | f c < f a}.ncard <
        {c ∈ criticalPoints 𝓘(ℝ, E) f | f c < f b}.ncard := by
      refine ncard_lt_ncard ((ssubset_iff_of_subset fun c hc ↦ ?_).2 ?_)
        (hf.finite_criticalPoints.subset (sep_subset _ _))
      · exact ⟨hc.1, hc.2.trans hab⟩
      · exact ⟨a, ⟨mem_criticalPoints_iff_mfderiv_eq_zero.2 ha, hab⟩, fun ha' ↦ lt_irrefl _ ha'.2⟩
    exact .head (flowsTo_iff.2 ⟨z, hz.2, hza⟩) (ih _ (hn ▸ hlt) hz.1 hza rfl)

omit hX in
/-- **The Morse index increases along a broken forward limit.** Under the Morse–Smale condition, if
the closure of the stable manifold of a critical point `q` meets the stable manifold of a different
critical point `b`, then `ind q < ind b`. -/
theorem IsMorseSmale.manifoldMorseIndex_lt_of_mem_closure_stableSet_inter_stableSet
    {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f) {b q : M}
    (hbq : b ≠ q)
    (hne : (closure (hX.flow.stableSet q) ∩ hX.flow.stableSet b).Nonempty) :
    manifoldMorseIndex 𝓘(ℝ, E) f q < manifoldMorseIndex 𝓘(ℝ, E) f b :=
  let ⟨_, hy, hyb⟩ := hne
  h.manifoldMorseIndex_lt_of_reflTransGen hf (reflTransGen_of_mem_closure_stableSet hf hy hyb)
    hbq.symm

omit hX in
/-- **The Morse index decreases along a broken backward limit.** Under the Morse–Smale condition, if
the closure of the unstable manifold of a point `p` meets the unstable manifold of a different
critical point `a`, then `ind a < ind p`. -/
theorem IsMorseSmale.manifoldMorseIndex_lt_of_mem_closure_unstableSet_inter_unstableSet
    {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f) {a p : M}
    (hap : a ≠ p)
    (hne : (closure (hX.flow.unstableSet p) ∩ hX.flow.unstableSet a).Nonempty) :
    manifoldMorseIndex 𝓘(ℝ, E) f a < manifoldMorseIndex 𝓘(ℝ, E) f p :=
  let ⟨_, hy, hya⟩ := hne
  h.manifoldMorseIndex_lt_of_reflTransGen hf (reflTransGen_of_mem_closure_unstableSet hf hy hya)
    hap

namespace IsMorseSmale

omit hX in
/-- **A broken backward limit at an adjacent index is a trajectory.** Under the Morse–Smale
condition, if the closure of the unstable manifold of a point `p` meets the unstable manifold of a
different critical point `a` with `ind a + 1 = ind p`, then some trajectory runs from `p` to `a`. -/
theorem nonempty_unstableSet_inter_stableSet_of_mem_closure_unstableSet_inter_unstableSet
    {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f) {a p : M}
    (hap : a ≠ p)
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f a + 1 = manifoldMorseIndex 𝓘(ℝ, E) f p)
    (hne : (closure (hX.flow.unstableSet p) ∩ hX.flow.unstableSet a).Nonempty) :
    (hX.flow.unstableSet p ∩ hX.flow.stableSet a).Nonempty := by
  -- Break the limit at `a`: the closure of `W^u(p)` meets `W^s(a)` at a point `z ≠ a`, which lies
  -- on a trajectory from some critical point `c` to `a`. No index fits strictly between those of
  -- `a` and `p`, so `c = p`.
  obtain ⟨y, hy⟩ := hne
  obtain ⟨z, hz, hza⟩ := hX.exists_mem_closure_inter_stableSet_of_mem_closure_inter_unstableSet hf
    (Flow.isInvariant_unstableSet _ p) (Flow.disjoint_unstableSet hap.symm) hy
  obtain ⟨c, -, hzc⟩ := hX.exists_tendsto_atBot hf z
  have hzc : z ∈ hX.flow.unstableSet c := Flow.mem_unstableSet.2 hzc
  by_cases hcp : c = p
  · exact ⟨z, hcp ▸ hzc, hz.2⟩
  have hca : c ≠ a := fun hca ↦
    hza (hX.eq_of_mem_unstableSet_inter_stableSet ⟨hca ▸ hzc, hz.2⟩)
  have h₁ := h.manifoldMorseIndex_lt_of_mem_closure_unstableSet_inter_unstableSet hf hcp
    ⟨z, hz.1, hzc⟩
  have h₂ := h.manifoldMorseIndex_lt hf hca ⟨z, hzc, hz.2⟩
  omega

omit hX in
/-- **A broken forward limit at an adjacent index is a trajectory.** Under the Morse–Smale
condition, if the closure of the stable manifold of a point `q` meets the stable manifold of a
different critical point `b` with `ind b = ind q + 1`, then some trajectory runs from `b` to `q`. -/
theorem nonempty_unstableSet_inter_stableSet_of_mem_closure_stableSet_inter_stableSet
    {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f) {b q : M}
    (hbq : b ≠ q)
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f b = manifoldMorseIndex 𝓘(ℝ, E) f q + 1)
    (hne : (closure (hX.flow.stableSet q) ∩ hX.flow.stableSet b).Nonempty) :
    (hX.flow.unstableSet b ∩ hX.flow.stableSet q).Nonempty := by
  -- Break the limit at `b`: the closure of `W^s(q)` meets `W^u(b)` at a point `z ≠ b`, which lies
  -- on a trajectory from `b` to some critical point `c`. No index fits strictly between those of
  -- `q` and `b`, so `c = q`.
  obtain ⟨y, hy⟩ := hne
  obtain ⟨z, hz, hzb⟩ := hX.exists_mem_closure_inter_unstableSet_of_mem_closure_inter_stableSet hf
    (Flow.isInvariant_stableSet _ q) (Flow.disjoint_stableSet hbq.symm) hy
  obtain ⟨c, -, hzc⟩ := hX.exists_tendsto_atTop hf z
  have hzc : z ∈ hX.flow.stableSet c := Flow.mem_stableSet.2 hzc
  by_cases hcq : c = q
  · exact ⟨z, hz.2, hcq ▸ hzc⟩
  have hbc : b ≠ c := fun hbc ↦
    hzb (hX.eq_of_mem_unstableSet_inter_stableSet ⟨hz.2, hbc ▸ hzc⟩)
  have h₁ := h.manifoldMorseIndex_lt_of_mem_closure_stableSet_inter_stableSet hf hcq
    ⟨z, hz.1, hzc⟩
  have h₂ := h.manifoldMorseIndex_lt hf hbc ⟨z, hz.2, hzc⟩
  omega

end IsMorseSmale

omit hX in
/-- **An index-one level slice is closed.** Under the Morse–Smale condition, if the critical points
`p` and `q` have Morse indices differing by one, then the points of the trajectories from `p` to `q`
lying on a level `c` strictly between `f q` and `f p` form a closed set. -/
theorem IsMorseSmale.isClosed_unstableSet_inter_stableSet_inter_level
    {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f) {p q : M}
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
  obtain ⟨a, -, hya⟩ := hX.exists_tendsto_atBot hf y
  obtain ⟨b, -, hyb⟩ := hX.exists_tendsto_atTop hf y
  have hya : y ∈ hX.flow.unstableSet a := Flow.mem_unstableSet.2 hya
  have hyb : y ∈ hX.flow.stableSet b := Flow.mem_stableSet.2 hyb
  -- A trajectory from a critical point to itself is constant, and lies off the level `c`.
  have hne : ∀ {x}, f x ≠ c → y ∈ hX.flow.unstableSet x ∩ hX.flow.stableSet x → False :=
    fun hx hy' ↦ hx (hX.eq_of_mem_unstableSet_inter_stableSet hy' ▸ hyc)
  have hba : manifoldMorseIndex 𝓘(ℝ, E) f b ≤ manifoldMorseIndex 𝓘(ℝ, E) f a := by
    by_cases hab : a = b
    · rw [hab]
    · exact (h.manifoldMorseIndex_lt hf hab ⟨y, hya, hyb⟩).le
  -- The index of `a` is at most that of `p`, with equality only if `a = p`, and the index of `b`
  -- is at least that of `q`, with equality only if `b = q`. As the two differ by one, `a = p` and
  -- `b = q`: any other configuration forces a constant trajectory through `y` at `p` or `q`.
  have hap : a = p ∨ manifoldMorseIndex 𝓘(ℝ, E) f a < manifoldMorseIndex 𝓘(ℝ, E) f p :=
    or_iff_not_imp_left.2 fun hap ↦
      h.manifoldMorseIndex_lt_of_mem_closure_unstableSet_inter_unstableSet hf hap
        ⟨y, hyU, hya⟩
  have hbq : b = q ∨ manifoldMorseIndex 𝓘(ℝ, E) f q < manifoldMorseIndex 𝓘(ℝ, E) f b :=
    or_iff_not_imp_left.2 fun hbq ↦
      h.manifoldMorseIndex_lt_of_mem_closure_stableSet_inter_stableSet hf hbq ⟨y, hyS, hyb⟩
  have hab : a ≠ b := by
    rintro rfl
    rcases hap with rfl | hap
    · exact hne hc.2.ne' ⟨hya, hyb⟩
    rcases hbq with rfl | hbq
    · exact hne hc.1.ne ⟨hya, hyb⟩
    omega
  have hlt := h.manifoldMorseIndex_lt hf hab ⟨y, hya, hyb⟩
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
/-- **Finiteness of the index-one trajectories.** Under the Morse–Smale condition, if the critical
points `p` and `q` have Morse indices differing by one, then only finitely many trajectories run
from `p` to `q`: their points on any level `c` form a finite set, which is empty unless `c` lies
strictly between `f q` and `f p`. This is the finiteness behind the coefficients of the mod-two
Morse boundary. -/
theorem IsMorseSmale.finite_unstableSet_inter_stableSet_inter_level
    {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f) {p q : M}
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1) (c : ℝ) :
    (hX.flow.unstableSet p ∩ hX.flow.stableSet q ∩ {z | f z = c}).Finite := by
  by_cases hc : f q < c ∧ c < f p
  · exact (h.isClosed_unstableSet_inter_stableSet_inter_level hf hind hc).isCompact.finite
      (hX.isDiscrete_unstableSet_inter_stableSet_level hf hind
        fun _ hy ↦ h.span_mtangentConeAt_sup_eq_top hy.1)
  · -- Outside `(f q, f p)` the slice is empty.
    have hpq : p ≠ q := by rintro rfl; omega
    refine finite_empty.subset fun y hy ↦ hc ?_
    exact hy.2 ▸ hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hpq hy.1

end IsAdaptedPseudoGradient

end TauCeti
