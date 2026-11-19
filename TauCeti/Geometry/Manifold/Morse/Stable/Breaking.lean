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
import TauCeti.Geometry.Manifold.Morse.Stable.LevelSlice

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
  it, under the Morse–Smale condition, shows that the closure of `W^s(q)` meets the stable
  manifolds only of points from which a chain of trajectories runs to `q`, and the closure of
  `W^u(p)` meets the unstable manifolds only of points to which a chain of trajectories runs from
  `p`. As the Morse index drops along each trajectory, besides `W^s(q)` itself, the closure of
  `W^s(q)` meets the stable manifolds only of critical points of index larger than `ind q`, and
  besides `W^u(p)` itself, the closure of `W^u(p)` meets the unstable manifolds only of critical
  points of index smaller than `ind p`. When the indices differ by one, a limit of points of the
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
* `IsAdaptedPseudoGradient.FlowsTo`: a trajectory runs from one point to another.
* `IsAdaptedPseudoGradient.lt_of_reflTransGen` and
  `IsAdaptedPseudoGradient.eq_of_reflTransGen_of_reflTransGen`: `f` strictly decreases along
  chains of trajectories, which therefore form a partial order.
* `IsAdaptedPseudoGradient.eq_or_mfderiv_eq_zero_of_reflTransGen` and
  `IsAdaptedPseudoGradient.finite_setOf_reflTransGen`: the points reached from `p` by chains of
  trajectories are `p` and finitely many critical points.
* `IsMorseSmale.manifoldMorseIndex_lt_of_reflTransGen`, in the namespace
  `TauCeti.IsAdaptedPseudoGradient`: the Morse index strictly decreases along chains of
  trajectories.
* `IsMorseSmale.reflTransGen_of_mem_closure_unstableSet` and its time reversal
  `IsMorseSmale.reflTransGen_of_mem_closure_stableSet`, in the namespace
  `TauCeti.IsAdaptedPseudoGradient`: if the closure of `W^u(p)` meets `W^u(a)`, then a chain of
  trajectories runs from `p` to `a` (respectively, if the closure of `W^s(q)` meets `W^s(b)`, then
  a chain of trajectories runs from `b` to `q`).
* `IsMorseSmale.manifoldMorseIndex_lt_of_mem_closure_stableSet_inter_stableSet` and its time
  reversal `IsMorseSmale.manifoldMorseIndex_lt_of_mem_closure_unstableSet_inter_unstableSet`, in
  the namespace `TauCeti.IsAdaptedPseudoGradient`:
  the Morse index strictly increases (respectively decreases) at the critical points other than `q`
  (respectively `p`) whose stable (respectively unstable) manifolds meet the closure of `W^s(q)`
  (respectively `W^u(p)`).
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

/-- **A trajectory runs from `a` to `b`**: the unstable manifold `W^u(a)` meets the stable manifold
`W^s(b)`. Its reflexive and transitive closure `Relation.ReflTransGen hX.FlowsTo` relates `a` to `b`
when `b = a` or a finite chain of trajectories, broken at critical points, runs from `a` to `b`. -/
def FlowsTo (a b : M) : Prop :=
  (hX.flow.unstableSet a ∩ hX.flow.stableSet b).Nonempty

omit hX in
/-- A trajectory runs from `a` to `b` exactly when `W^u(a) ∩ W^s(b)` is nonempty. -/
theorem flowsTo_iff {hX : IsAdaptedPseudoGradient f X} {a b : M} :
    hX.FlowsTo a b ↔ (hX.flow.unstableSet a ∩ hX.flow.stableSet b).Nonempty :=
  Iff.rfl

omit hX in
/-- **Points below `p` are critical.** A point reached from `p` by a chain of trajectories is `p`
itself or a critical point of `f`, the forward limit of the last trajectory. -/
theorem eq_or_mfderiv_eq_zero_of_reflTransGen {hX : IsAdaptedPseudoGradient f X} {p q : M}
    (hpq : Relation.ReflTransGen hX.FlowsTo p q) :
    q = p ∨ mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0 := by
  rcases hpq.cases_tail with rfl | ⟨b, -, hbq⟩
  · exact Or.inl rfl
  · obtain ⟨y, -, hy⟩ := flowsTo_iff.1 hbq
    exact Or.inr (hX.mfderiv_eq_zero_of_mem_stableSet hy)

omit hX in
/-- **Finitely many points lie below `p`.** For a Morse function on a compact manifold, the points
reached from `p` by chains of trajectories form a finite set: besides `p` they are critical points
of `f`. -/
theorem finite_setOf_reflTransGen {hX : IsAdaptedPseudoGradient f X} (hf : IsMorse 𝓘(ℝ, E) f)
    (p : M) :
    {q | Relation.ReflTransGen hX.FlowsTo p q}.Finite := by
  refine (hf.finite_criticalPoints.insert p).subset fun q hq ↦ ?_
  rcases eq_or_mfderiv_eq_zero_of_reflTransGen hq with rfl | hq
  · exact mem_insert _ _
  · exact mem_insert_of_mem _ (mem_criticalPoints_iff_mfderiv_eq_zero.2 hq)

omit hX in
/-- **The function strictly decreases along chains of trajectories.** If a chain of trajectories
runs from `p` to a different point `q`, then `f q < f p`. -/
theorem lt_of_reflTransGen {hX : IsAdaptedPseudoGradient f X} {p q : M}
    (hpq : Relation.ReflTransGen hX.FlowsTo p q) (hqp : q ≠ p) :
    f q < f p := by
  suffices q = p ∨ f q < f p from this.resolve_left hqp
  clear hqp
  induction hpq with
  | refl => exact Or.inl rfl
  | @tail b c _ hbc ih =>
    -- A trajectory from `b` to `c ≠ b` lies strictly between their critical values.
    have hcb : c = b ∨ f c < f b := by
      rcases eq_or_ne b c with rfl | hbc'
      · exact Or.inl rfl
      · obtain ⟨y, hy⟩ := flowsTo_iff.1 hbc
        have hy := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hbc' hy
        exact Or.inr (hy.1.trans hy.2)
    rcases ih with rfl | ih
    · exact hcb
    · rcases hcb with rfl | hcb
      · exact Or.inr ih
      · exact Or.inr (hcb.trans ih)

omit hX in
/-- **Chains of trajectories form a partial order.** If chains of trajectories run from `p` to `q`
and from `q` to `p`, then `p = q`. -/
theorem eq_of_reflTransGen_of_reflTransGen {hX : IsAdaptedPseudoGradient f X} {p q : M}
    (hpq : Relation.ReflTransGen hX.FlowsTo p q)
    (hqp : Relation.ReflTransGen hX.FlowsTo q p) :
    p = q := by
  by_contra hne
  exact (lt_of_reflTransGen hpq (Ne.symm hne)).asymm (lt_of_reflTransGen hqp hne)

omit hX in
/-- **The Morse index strictly decreases along chains of trajectories.** Under the Morse–Smale
condition, if a chain of trajectories runs from `p` to a different point `q`, then
`ind q < ind p`. -/
theorem IsMorseSmale.manifoldMorseIndex_lt_of_reflTransGen {hX : IsAdaptedPseudoGradient f X}
    (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f) {p q : M}
    (hpq : Relation.ReflTransGen hX.FlowsTo p q) (hqp : q ≠ p) :
    manifoldMorseIndex 𝓘(ℝ, E) f q < manifoldMorseIndex 𝓘(ℝ, E) f p := by
  suffices q = p ∨ manifoldMorseIndex 𝓘(ℝ, E) f q < manifoldMorseIndex 𝓘(ℝ, E) f p from
    this.resolve_left hqp
  clear hqp
  induction hpq with
  | refl => exact Or.inl rfl
  | @tail b c _ hbc ih =>
    rcases eq_or_ne b c with rfl | hbc'
    · exact ih
    have hcb := h.manifoldMorseIndex_lt hf hbc' (flowsTo_iff.1 hbc)
    rcases ih with rfl | ih
    · exact Or.inr hcb
    · exact Or.inr (hcb.trans ih)

omit hX in
/-- **The closure of `W^u(p)` meets only unstable manifolds below `p`.** Under the Morse–Smale
condition, if a point of the closure of `W^u(p)` lies on `W^u(a)`, then a chain of trajectories
runs from `p` to `a`. -/
theorem IsMorseSmale.reflTransGen_of_mem_closure_unstableSet {hX : IsAdaptedPseudoGradient f X}
    (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f) {p a y : M}
    (hy : y ∈ closure (hX.flow.unstableSet p)) (hya : y ∈ hX.flow.unstableSet a) :
    Relation.ReflTransGen hX.FlowsTo p a := by
  -- Break the limit at `a` and follow the incoming orbit back to the previous critical point `b`,
  -- of larger index; then induct on the codimension `n - ind a`.
  induction hn : Module.finrank ℝ E - manifoldMorseIndex 𝓘(ℝ, E) f a
    using Nat.strong_induction_on generalizing a y with
  | _ n ih =>
    rcases eq_or_ne p a with rfl | hpa
    · exact Relation.ReflTransGen.refl
    obtain ⟨z, hz, hza⟩ := hX.exists_mem_closure_inter_stableSet_of_mem_closure_inter_unstableSet
      hf (Flow.isInvariant_unstableSet _ p) (Flow.disjoint_unstableSet hpa) ⟨hy, hya⟩
    obtain ⟨b, -, hzb⟩ := hX.exists_tendsto_atBot hf z
    have hzb : z ∈ hX.flow.unstableSet b := Flow.mem_unstableSet.2 hzb
    have hba : b ≠ a := fun hba ↦
      hza (hX.eq_of_mem_unstableSet_inter_stableSet ⟨hba ▸ hzb, hz.2⟩)
    have hlt := h.manifoldMorseIndex_lt hf hba ⟨z, hzb, hz.2⟩
    have hle := manifoldMorseIndex_le_finrank (I := 𝓘(ℝ, E)) (f := f) (x := b)
    exact (ih _ (by omega) hz.1 hzb rfl).tail (flowsTo_iff.2 ⟨z, hzb, hz.2⟩)

omit hX in
/-- **The closure of `W^s(q)` meets only stable manifolds above `q`.** Under the Morse–Smale
condition, if a point of the closure of `W^s(q)` lies on `W^s(b)`, then a chain of trajectories
runs from `b` to `q`. -/
theorem IsMorseSmale.reflTransGen_of_mem_closure_stableSet {hX : IsAdaptedPseudoGradient f X}
    (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f) {q b y : M}
    (hy : y ∈ closure (hX.flow.stableSet q)) (hyb : y ∈ hX.flow.stableSet b) :
    Relation.ReflTransGen hX.FlowsTo b q := by
  -- Break the limit at `b` and follow the outgoing orbit to the next critical point `a`, of
  -- smaller index; then induct on the index of `b`.
  induction hn : manifoldMorseIndex 𝓘(ℝ, E) f b
    using Nat.strong_induction_on generalizing b y with
  | _ n ih =>
    rcases eq_or_ne q b with rfl | hqb
    · exact Relation.ReflTransGen.refl
    obtain ⟨z, hz, hzb⟩ := hX.exists_mem_closure_inter_unstableSet_of_mem_closure_inter_stableSet
      hf (Flow.isInvariant_stableSet _ q) (Flow.disjoint_stableSet hqb) ⟨hy, hyb⟩
    obtain ⟨a, -, hza⟩ := hX.exists_tendsto_atTop hf z
    have hza : z ∈ hX.flow.stableSet a := Flow.mem_stableSet.2 hza
    have hba : b ≠ a := fun hba ↦
      hzb (hX.eq_of_mem_unstableSet_inter_stableSet ⟨hz.2, hba ▸ hza⟩)
    have hlt := h.manifoldMorseIndex_lt hf hba ⟨z, hz.2, hza⟩
    exact .head (flowsTo_iff.2 ⟨z, hz.2, hza⟩) (ih _ (by omega) hz.1 hza rfl)

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
  h.manifoldMorseIndex_lt_of_reflTransGen hf (h.reflTransGen_of_mem_closure_stableSet hf hy hyb)
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
  h.manifoldMorseIndex_lt_of_reflTransGen hf (h.reflTransGen_of_mem_closure_unstableSet hf hy hya)
    hap

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
