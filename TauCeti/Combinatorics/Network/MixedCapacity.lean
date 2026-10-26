/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.ShortestAugmentation
public import TauCeti.Combinatorics.Network.VertexSplitting

/-!
# Flows with vertex and arrow capacities

Let `Q` be a finite arrow family with nonnegative capacities `cap` on its arrows, let `s ≠ t` be
terminals, and let `c v` be a nonnegative capacity on every vertex `v` other than `s` and `t`. An
ordinary `s`–`t` flow *respects the vertex capacities* when the total value entering every
nonterminal vertex `v` is at most `c v`; by conservation this is also the total value leaving `v`.
A *mixed separator* is a pair `(X, F)` of a vertex set `X` avoiding the terminals and a set `F` of
arrows such that every walk from `s` to `t` passes through a vertex of `X` or traverses an arrow of
`F`; equivalently, deleting `X` and `F` leaves no walk from `s` to `t`. Its weight is
`∑ v ∈ X, c v + ∑ a ∈ F, cap a`, counting an arrow of `F` even when it is incident to a vertex of
`X`.

This file proves the max-flow/min-cut theorem for these mixed capacities: the value of every flow
respecting the vertex capacities is at most the weight of every mixed separator, and some such flow
and some mixed separator attain equality, with every arrow value of the flow in any additive
subgroup containing all the capacities.

The proof reduces to ordinary flows by vertex splitting (`TauCeti.SplitHom`). The split network
keeps the capacity `cap e` on each original arrow, puts `c v` on the split arrow of each
nonterminal vertex, and the total capacity of all arrows on the split arrows of the terminals
(`TauCeti.mixedSplitCapacity`); its terminals are the exit `s⁺` of `s` and the entrance `t⁻` of
`t`. The flows respecting the vertex capacities correspond exactly to the ordinary `s⁺`–`t⁻` flows
of the split network, with the same values on the original arrows and the same value
(`TauCeti.Flow.mixedSplitEquiv`). A cut of the split network is mapped to the mixed separator
formed by its crossing split arrows and its crossing original arrows, of weight equal to the cut
capacity, and a mixed separator is mapped to a cut whose crossing arrows it contains. The two maps
between cuts and separators do not depend on the capacities of the terminal split arrows; only the
correspondence with all flows uses that those capacities bound the traffic through the terminals.

Taking every vertex capacity to be the total capacity of all arrows imposes no constraint
(`TauCeti.Flow.respectsVertexCapacity_arrowSum`), so ordinary max-flow/min-cut is the special case
in which mixed separators may as well contain no vertices.

## Main definitions

* `TauCeti.IsMixedSeparator X F s t`: every walk from `s` to `t` meets the vertex set `X`, which
  avoids `s` and `t`, or the arrow set `F`.
* `TauCeti.Flow.RespectsVertexCapacity f c`: the flow `f` carries at most `c v` into every vertex
  `v` other than its terminals.
* `TauCeti.mixedSplitCapacity cap c s t`: the capacities of the split arrows in the reduction.
* `TauCeti.Flow.mixedSplitEquiv`: the correspondence between flows respecting the vertex capacities
  and ordinary flows of the split network.

## Main results

* `TauCeti.SplitHom.isMixedSeparator_cutVertices_cutArrows`: the arrows leaving a cut of the split
  network form a mixed separator.
* `TauCeti.SplitHom.arrowSum_assignment_compl_eq_weight`: the capacity of a cut of the split
  network equals the weight of that mixed separator.
* `TauCeti.IsMixedSeparator.exists_cutVertices_subset`: every mixed separator contains the arrows
  leaving some cut of the split network.
* `TauCeti.Flow.RespectsVertexCapacity.val_le`: weak duality between flows and mixed separators.
* `TauCeti.Flow.exists_respectsVertexCapacity_val_eq_mem` and
  `TauCeti.Flow.exists_respectsVertexCapacity_val_eq`: the max-flow/min-cut theorem for mixed
  vertex and arrow capacities, with integrality in an additive subgroup.

## References

* L. R. Ford, D. R. Fulkerson, *Flows in Networks*, Princeton University Press, 1962.
* A. Schrijver, *Combinatorial Optimization: Polyhedra and Efficiency*, Springer, 2003.
-/

public section

namespace TauCeti

open Finset SplitHom

universe u v w

variable {V : Type u} {Q : V → V → Type v} {K : Type w}

/-! ### Mixed separators -/

/-- A *mixed separator* between `s` and `t` is a pair of a vertex set `X`, containing neither `s`
nor `t`, and a set `F` of arrows, each recorded with its endpoints, such that every walk from `s`
to `t` passes through a vertex of `X` or traverses an arrow of `F`. Equivalently, no walk from `s`
to `t` survives the deletion of the vertices of `X` and the arrows of `F`. -/
def IsMixedSeparator (X : Finset V) (F : Finset (Σ v w, Q v w)) (s t : V) : Prop :=
  s ∉ X ∧ t ∉ X ∧ ∀ p : ArrowWalk Q s t, (∃ v ∈ p.vertices, v ∈ X) ∨ ∃ a ∈ p.arrows, a ∈ F

theorem isMixedSeparator_iff {X : Finset V} {F : Finset (Σ v w, Q v w)} {s t : V} :
    IsMixedSeparator X F s t ↔
      s ∉ X ∧ t ∉ X ∧ ∀ p : ArrowWalk Q s t, (∃ v ∈ p.vertices, v ∈ X) ∨ ∃ a ∈ p.arrows, a ∈ F :=
  Iff.rfl

namespace IsMixedSeparator

variable {X X' : Finset V} {F F' : Finset (Σ v w, Q v w)} {s t : V}

theorem source_notMem (h : IsMixedSeparator X F s t) : s ∉ X :=
  (isMixedSeparator_iff.1 h).1

theorem target_notMem (h : IsMixedSeparator X F s t) : t ∉ X :=
  (isMixedSeparator_iff.1 h).2.1

/-- Every walk from `s` to `t` meets a mixed separator. -/
theorem exists_mem (h : IsMixedSeparator X F s t) (p : ArrowWalk Q s t) :
    (∃ v ∈ p.vertices, v ∈ X) ∨ ∃ a ∈ p.arrows, a ∈ F :=
  (isMixedSeparator_iff.1 h).2.2 p

/-- The terminals of a mixed separator are distinct, since the walk of length zero meets no
vertex set avoiding its terminal and no arrow set. -/
theorem ne (h : IsMixedSeparator X F s t) : s ≠ t := by
  rintro rfl
  rcases h.exists_mem (ArrowWalk.nil s) with ⟨v, hv, hvX⟩ | ⟨a, ha, -⟩
  · simp only [ArrowWalk.vertices, Quiver.Path.vertices_nil, List.mem_singleton] at hv
    exact h.source_notMem (hv ▸ hvX)
  · simp at ha

/-- Enlarging a mixed separator, while keeping its vertices away from the terminals, gives a mixed
separator. -/
theorem mono (h : IsMixedSeparator X F s t) (hX : X ⊆ X') (hF : F ⊆ F') (hs : s ∉ X')
    (ht : t ∉ X') : IsMixedSeparator X' F' s t :=
  isMixedSeparator_iff.2 ⟨hs, ht, fun p ↦ (h.exists_mem p).imp (fun ⟨v, hv, hvX⟩ ↦ ⟨v, hv, hX hvX⟩)
    fun ⟨a, ha, haF⟩ ↦ ⟨a, ha, hF haF⟩⟩

end IsMixedSeparator

/-! ### Cuts of the split network and mixed separators -/

section Cut

variable [Fintype V] [DecidableEq V] [∀ v w, Fintype (Q v w)] {s t : V}

/-- **Cuts give mixed separators.** For distinct terminals and a vertex set `S` of the split
network containing the exit of `s` but not the entrance of `t`, the vertices whose split arrows
leave `S` and the original arrows leaving `S` form a mixed separator between `s` and `t`. -/
theorem SplitHom.isMixedSeparator_cutVertices_cutArrows (hst : s ≠ t) {S : Finset (V × Bool)}
    (hs : (s, true) ∈ S) (ht : (t, false) ∉ S) :
    IsMixedSeparator (cutVertices S) (cutArrows Q S) s t := by
  refine isMixedSeparator_iff.2 ⟨fun h ↦ ((mem_cutVertices S).1 h).2 hs,
    fun h ↦ ht ((mem_cutVertices S).1 h).1, fun p ↦ ?_⟩
  by_contra hp
  simp only [not_or, not_exists, not_and] at hp
  -- Along a walk from `s` avoiding the separator, the exit of every vertex reached lies in `S`,
  -- and so does its entrance unless the vertex is `s`.
  have key {x : V} (q : ArrowWalk Q s x) (hX : ∀ v ∈ q.vertices, v ∉ cutVertices S)
      (hF : ∀ a ∈ q.arrows, a ∉ cutArrows Q S) : (x, true) ∈ S ∧ (x = s ∨ (x, false) ∈ S) := by
    induction q with
    | nil => exact ⟨hs, .inl rfl⟩
    | cons q e ih =>
      simp only [ArrowWalk.vertices, Quiver.Path.vertices_cons, List.concat_eq_append,
        List.mem_append, List.mem_singleton, ArrowWalk.arrows_cons] at hX hF
      have hy := (ih (fun v hv ↦ hX v (.inl hv)) fun a ha ↦ hF a (.inl ha)).1
      have hentrance := not_not.1 fun h ↦ hF _ (.inr rfl) ((mem_cutArrows Q S).2 ⟨hy, h⟩)
      exact ⟨not_not.1 fun h ↦ hX _ (.inr rfl) ((mem_cutVertices S).2 ⟨hentrance, h⟩),
        .inr hentrance⟩
  exact ht ((key p hp.1 hp.2).2.resolve_left hst.symm)

/-- **Cuts give mixed separators of equal weight.** For a vertex set `S` of the split network
containing the exit of `s` but not the entrance of `t`, and split capacities `φ` agreeing with the
vertex capacities `c` away from the terminals, the cut capacity of `S` equals the weight of the
mixed separator formed by the vertices whose split arrows leave `S` and the original arrows leaving
`S` (`TauCeti.SplitHom.isMixedSeparator_cutVertices_cutArrows`). -/
theorem SplitHom.arrowSum_assignment_compl_eq_weight [AddCommMonoid K] {S : Finset (V × Bool)}
    (hs : (s, true) ∈ S) (ht : (t, false) ∉ S) {cap : Assignment Q K} {φ c : V → K}
    (hφ : ∀ v, v ≠ s → v ≠ t → φ v = c v) :
    arrowSum (assignment cap φ) S Sᶜ =
      ∑ v ∈ cutVertices S, c v + ∑ a ∈ cutArrows Q S, cap a.2.2 := by
  rw [arrowSum_assignment_compl]
  congr 1
  refine sum_congr rfl fun v hv ↦ hφ v ?_ ?_
  · rintro rfl
    exact ((mem_cutVertices S).1 hv).2 hs
  · rintro rfl
    exact ht ((mem_cutVertices S).1 hv).1

/-- **Mixed separators give cuts.** Every mixed separator `(X, F)` between `s` and `t` contains the
crossing arrows of some vertex set of the split network containing the exit of `s` but not the
entrance of `t`: the vertices of `X` include those whose split arrows leave it, and `F` includes the
original arrows leaving it. -/
theorem IsMixedSeparator.exists_cutVertices_subset {X : Finset V} {F : Finset (Σ v w, Q v w)}
    (h : IsMixedSeparator X F s t) :
    ∃ S : Finset (V × Bool), (s, true) ∈ S ∧ (t, false) ∉ S ∧ cutVertices S ⊆ X ∧
      cutArrows Q S ⊆ F := by
  classical
  -- `R v`: some walk from `s` to `v` avoids the separator.
  let R (v : V) : Prop :=
    ∃ p : ArrowWalk Q s v, (∀ x ∈ p.vertices, x ∉ X) ∧ ∀ a ∈ p.arrows, a ∉ F
  have extend {u w : V} (hu : R u) (e : Q u w) (he : ⟨u, w, e⟩ ∉ F) (hw : w ∉ X) : R w := by
    obtain ⟨p, hpX, hpF⟩ := hu
    refine ⟨p.cons e, fun x hx ↦ ?_, fun a ha ↦ ?_⟩
    · simp only [ArrowWalk.vertices, Quiver.Path.vertices_cons, List.concat_eq_append,
        List.mem_append, List.mem_singleton] at hx
      exact hx.elim (hpX x) fun hx ↦ hx ▸ hw
    · simp only [ArrowWalk.arrows_cons, List.mem_append, List.mem_singleton] at ha
      exact ha.elim (hpF a) fun ha ↦ ha ▸ he
  -- The exit of `v` is reached when `R v`, and its entrance when an arrow outside `F` leads
  -- to `v` from a vertex satisfying `R`.
  let S : Finset (V × Bool) :=
    {x | x.2 = true ∧ R x.1 ∨ x.2 = false ∧ ∃ u, R u ∧ ∃ e : Q u x.1, ⟨u, x.1, e⟩ ∉ F}
  have hS_true (v : V) : (v, true) ∈ S ↔ R v := by simp [S]
  have hS_false (v : V) : (v, false) ∈ S ↔ ∃ u, R u ∧ ∃ e : Q u v, ⟨u, v, e⟩ ∉ F := by simp [S]
  refine ⟨S, (hS_true s).2 ⟨ArrowWalk.nil s, ?_, by simp⟩, fun ht ↦ ?_, fun v hv ↦ ?_,
    fun a ha ↦ ?_⟩
  · simpa using h.source_notMem
  · obtain ⟨u, hu, e, he⟩ := (hS_false t).1 ht
    obtain ⟨p, hpX, hpF⟩ := extend hu e he h.target_notMem
    rcases h.exists_mem p with ⟨x, hx, hxX⟩ | ⟨a, ha, haF⟩
    exacts [hpX x hx hxX, hpF a ha haF]
  · rw [mem_cutVertices, hS_false, hS_true] at hv
    obtain ⟨⟨u, hu, e, he⟩, hv⟩ := hv
    exact not_not.1 fun hvX ↦ hv (extend hu e he hvX)
  · obtain ⟨v, w, e⟩ := a
    rw [mem_cutArrows, hS_true, hS_false] at ha
    exact not_not.1 fun he ↦ ha.2 ⟨v, ha.1, e, he⟩

/-- Every mixed separator `(X, F)` gives a vertex set of the split network containing the exit of
`s` but not the entrance of `t`, whose cut capacity is at most the weight of `(X, F)`, whenever the
capacities of the vertices of `X` and of the arrows of `F` are nonnegative. -/
theorem IsMixedSeparator.exists_arrowSum_le [AddCommMonoid K] [PartialOrder K]
    [IsOrderedAddMonoid K] {X : Finset V} {F : Finset (Σ v w, Q v w)}
    (h : IsMixedSeparator X F s t) {cap : Assignment Q K} {c : V → K}
    (hcap : ∀ a ∈ F, 0 ≤ cap a.2.2) (hc : ∀ v ∈ X, 0 ≤ c v) :
    ∃ S : Finset (V × Bool), (s, true) ∈ S ∧ (t, false) ∉ S ∧
      arrowSum (assignment cap c) S Sᶜ ≤ ∑ v ∈ X, c v + ∑ a ∈ F, cap a.2.2 := by
  obtain ⟨S, hs, ht, hX, hF⟩ := h.exists_cutVertices_subset
  refine ⟨S, hs, ht, ?_⟩
  rw [arrowSum_assignment_compl]
  exact add_le_add (sum_le_sum_of_subset_of_nonneg hX fun v hv _ ↦ hc v hv)
    (sum_le_sum_of_subset_of_nonneg hF fun a ha _ ↦ hcap a ha)

end Cut

/-! ### Flows respecting vertex capacities -/

section Flow

variable [Fintype V] [∀ v w, Fintype (Q v w)] [AddCommGroup K] {cap : Assignment Q K} {c : V → K}
  {s t : V}

section SplitCapacity

variable [DecidableEq V]

variable (cap c s t) in
/-- The capacities of the split arrows in the reduction of mixed capacities to arrow capacities:
the vertex capacity `c v` on the split arrow of every vertex `v` other than `s` and `t`, and the
total capacity of all arrows on the split arrows of `s` and `t`, which bounds the traffic through
the terminals. -/
def mixedSplitCapacity : V → K :=
  fun v ↦ if v = s ∨ v = t then arrowSum cap univ univ else c v

theorem mixedSplitCapacity_of_ne {v : V} (hs : v ≠ s) (ht : v ≠ t) :
    mixedSplitCapacity cap c s t v = c v := by
  simp [mixedSplitCapacity, hs, ht]

theorem mixedSplitCapacity_of_eq_or_eq {v : V} (hv : v = s ∨ v = t) :
    mixedSplitCapacity cap c s t v = arrowSum cap univ univ := by
  simp [mixedSplitCapacity, hv]

/-- The values of a flow on the split arrows of the split network: the value entering each vertex,
except for the sink `t`, whose split arrow carries the value leaving it. -/
private def splitValue (f : Assignment Q K) (t : V) : V → K :=
  fun v ↦ if v = t then arrowSum f {v} univ else arrowSum f univ {v}

private theorem splitValue_of_ne (f : Assignment Q K) {v : V} (hv : v ≠ t) :
    splitValue f t v = arrowSum f univ {v} := by
  simp [splitValue, hv]

private theorem splitValue_self (f : Assignment Q K) : splitValue f t t = arrowSum f {t} univ := by
  simp [splitValue]

end SplitCapacity

variable [PartialOrder K] [IsOrderedAddMonoid K]

/-- An ordinary `s`–`t` flow *respects the vertex capacities* `c` when the total value entering
each vertex `v` other than `s` and `t` is at most `c v`. By conservation, this is also the total
value leaving `v`. -/
def Flow.RespectsVertexCapacity (f : Flow cap s t) (c : V → K) : Prop :=
  ∀ v, v ≠ s → v ≠ t → arrowSum f.toFun univ {v} ≤ c v

omit [IsOrderedAddMonoid K] in
theorem Flow.respectsVertexCapacity_iff {f : Flow cap s t} :
    f.RespectsVertexCapacity c ↔ ∀ v, v ≠ s → v ≠ t → arrowSum f.toFun univ {v} ≤ c v :=
  Iff.rfl

omit [IsOrderedAddMonoid K] in
/-- A flow respecting the vertex capacities carries at most `c v` into each nonterminal vertex
`v`. -/
theorem Flow.RespectsVertexCapacity.le {f : Flow cap s t} (hf : f.RespectsVertexCapacity c)
    {v : V} (hs : v ≠ s) (ht : v ≠ t) : arrowSum f.toFun univ {v} ≤ c v :=
  Flow.respectsVertexCapacity_iff.1 hf v hs ht

/-- Every flow respects the vertex capacities equal to the total capacity of all arrows. -/
theorem Flow.respectsVertexCapacity_arrowSum (f : Flow cap s t) :
    f.RespectsVertexCapacity fun _ ↦ arrowSum cap univ univ :=
  Flow.respectsVertexCapacity_iff.2 fun _ _ _ ↦ f.arrowSum_le_arrowSum_univ _ _

variable [DecidableEq V]

/-- The ordinary flow of the split network corresponding to a flow respecting the vertex
capacities: the same values on the original arrows, and on each split arrow the value through its
vertex. -/
private def toSplitFlow (f : Flow cap s t) (hf : f.RespectsVertexCapacity c) :
    Flow (assignment cap (mixedSplitCapacity cap c s t)) (s, true) (t, false) where
  toFun := assignment f.toFun (splitValue f.toFun t)
  mem_Icc := by
    rw [Set.mem_Icc, ← assignment_zero, assignment_le_assignment_iff,
      assignment_le_assignment_iff]
    refine ⟨⟨f.mem_Icc.1, fun v ↦ ?_⟩, f.mem_Icc.2, fun v ↦ ?_⟩
    · unfold splitValue
      split_ifs <;> exact arrowSum_nonneg f.mem_Icc.1 _ _
    · by_cases hv : v = s ∨ v = t
      · rw [mixedSplitCapacity_of_eq_or_eq hv]
        unfold splitValue
        split_ifs <;> exact f.arrowSum_le_arrowSum_univ _ _
      · rw [not_or] at hv
        rw [mixedSplitCapacity_of_ne hv.1 hv.2, splitValue_of_ne _ hv.2]
        exact hf.le hv.1 hv.2
  conserve := by
    rintro ⟨v, _ | _⟩ hs ht
    · have hv : v ≠ t := fun h ↦ ht (h ▸ rfl)
      rw [excessAt_entrance, originalAssignment_assignment, assignment_split,
        splitValue_of_ne _ hv, sub_self]
    · have hv : v ≠ s := fun h ↦ hs (h ▸ rfl)
      rw [excessAt_exit, originalAssignment_assignment, assignment_split]
      by_cases hvt : v = t
      · rw [hvt, splitValue_self, sub_self]
      · rw [splitValue_of_ne _ hvt, ← excessAt_eq_arrowSum_sub]
        exact f.conserve v hv hvt
  excessAt_sink_nonneg := by
    rw [excessAt_entrance, originalAssignment_assignment, assignment_split, splitValue_self,
      ← excessAt_eq_arrowSum_sub]
    exact f.excessAt_sink_nonneg

/-- The flow respecting the vertex capacities corresponding to an ordinary flow of the split
network: its values on the original arrows. -/
private def ofSplitFlow (hst : s ≠ t)
    (g : Flow (assignment cap (mixedSplitCapacity cap c s t)) (s, true) (t, false)) :
    {f : Flow cap s t // f.RespectsVertexCapacity c} where
  val :=
    { toFun := originalAssignment g.toFun
      mem_Icc := ⟨fun _ _ e ↦ by simpa using g.lower_le (original e),
        fun _ _ e ↦ by simpa using g.le_upper (original e)⟩
      conserve := fun v hs ht ↦ excessAt_originalAssignment_eq_zero
        (g.conserve _ (by simp) (by simpa using ht)) (g.conserve _ (by simpa using hs) (by simp))
      excessAt_sink_nonneg := by
        rw [excessAt_originalAssignment, g.conserve (t, true) (by simpa using hst.symm) (by simp),
          add_zero]
        exact g.excessAt_sink_nonneg }
  property := Flow.respectsVertexCapacity_iff.2 fun v hs ht ↦ by
    refine arrowSum_originalAssignment_univ_singleton_le v ?_
      (g.conserve _ (by simp) (by simpa using ht))
    simpa [mixedSplitCapacity_of_ne hs ht] using g.le_upper (split v)

/-- **Vertex splitting for mixed capacities.** For distinct terminals, the ordinary `s`–`t` flows
respecting the vertex capacities `c` correspond to the ordinary `s⁺`–`t⁻` flows of the split
network with the capacities `cap` on original arrows and `mixedSplitCapacity cap c s t` on split
arrows. A flow keeps its values on the original arrows, and its split arrow at each vertex other
than `t` carries the value entering that vertex. -/
def Flow.mixedSplitEquiv (hst : s ≠ t) :
    {f : Flow cap s t // f.RespectsVertexCapacity c} ≃
      Flow (assignment cap (mixedSplitCapacity cap c s t)) (s, true) (t, false) where
  toFun f := toSplitFlow f.1 f.2
  invFun := ofSplitFlow hst
  left_inv f := Subtype.ext (Flow.ext (originalAssignment_assignment f.1.toFun _))
  right_inv g := by
    refine Flow.ext (assignment_ext (originalAssignment_assignment _ _) fun v ↦ ?_)
    -- The split arrow of `v` carries the value forced by conservation at a copy of `v`.
    dsimp only [toSplitFlow, ofSplitFlow]
    rw [assignment_split]
    by_cases hvt : v = t
    · subst hvt
      have h := g.conserve (v, true) (by simpa using hst.symm) (by simp)
      rw [excessAt_exit, sub_eq_zero] at h
      rw [splitValue_self, h]
    · have h := g.conserve (v, false) (by simp) (by simpa using hvt)
      rw [excessAt_entrance, sub_eq_zero] at h
      rw [splitValue_of_ne _ hvt, h]

variable (hst : s ≠ t)

@[simp]
theorem Flow.originalAssignment_mixedSplitEquiv_apply
    (f : {f : Flow cap s t // f.RespectsVertexCapacity c}) :
    originalAssignment (Flow.mixedSplitEquiv hst f).toFun = f.1.toFun :=
  originalAssignment_assignment _ _

/-- The split arrow of a vertex other than the sink carries the value entering that vertex. -/
theorem Flow.mixedSplitEquiv_apply_split (f : {f : Flow cap s t // f.RespectsVertexCapacity c})
    {v : V} (hv : v ≠ t) :
    (Flow.mixedSplitEquiv hst f).toFun (split v) = arrowSum f.1.toFun univ {v} :=
  (assignment_split _ _ v).trans (splitValue_of_ne _ hv)

/-- The split arrow of the sink carries the value leaving it. -/
theorem Flow.mixedSplitEquiv_apply_split_self
    (f : {f : Flow cap s t // f.RespectsVertexCapacity c}) :
    (Flow.mixedSplitEquiv hst f).toFun (split t) = arrowSum f.1.toFun {t} univ :=
  (assignment_split _ _ t).trans (splitValue_self _)

@[simp]
theorem Flow.mixedSplitEquiv_symm_apply_toFun
    (g : Flow (assignment cap (mixedSplitCapacity cap c s t)) (s, true) (t, false)) :
    ((Flow.mixedSplitEquiv hst).symm g).1.toFun = originalAssignment g.toFun :=
  (rfl)

/-- The correspondence preserves values. -/
@[simp]
theorem Flow.val_mixedSplitEquiv (f : {f : Flow cap s t // f.RespectsVertexCapacity c}) :
    (Flow.mixedSplitEquiv hst f).val = f.1.val := by
  rw [BoundedFlow.val_def, BoundedFlow.val_def, excessAt_entrance,
    Flow.mixedSplitEquiv_apply_split_self, Flow.originalAssignment_mixedSplitEquiv_apply,
    excessAt_eq_arrowSum_sub]

omit [DecidableEq V] hst in
/-- **Weak duality for mixed capacities.** The value of an ordinary flow respecting the vertex
capacities `c` is at most the weight of every mixed separator. -/
theorem Flow.RespectsVertexCapacity.val_le {f : Flow cap s t} (hf : f.RespectsVertexCapacity c)
    {X : Finset V} {F : Finset (Σ v w, Q v w)} (h : IsMixedSeparator X F s t) :
    f.val ≤ ∑ v ∈ X, c v + ∑ a ∈ F, cap a.2.2 := by
  classical
  have hst := h.ne
  have hX {v : V} (hv : v ∈ X) : v ≠ s ∧ v ≠ t :=
    ⟨fun h' ↦ h.source_notMem (h' ▸ hv), fun h' ↦ h.target_notMem (h' ▸ hv)⟩
  -- The capacities in the weight are nonnegative, since `f` lies between zero and them.
  have hcX (v : V) (hv : v ∈ X) : 0 ≤ mixedSplitCapacity cap c s t v := by
    rw [mixedSplitCapacity_of_ne (hX hv).1 (hX hv).2]
    exact (arrowSum_nonneg f.mem_Icc.1 _ _).trans (hf.le (hX hv).1 (hX hv).2)
  obtain ⟨S, hs, ht, hS⟩ :=
    h.exists_arrowSum_le (fun a _ ↦ (f.mem_Icc.1 _ _ a.2.2).trans (f.mem_Icc.2 _ _ a.2.2)) hcX
  rw [sum_congr rfl fun v hv ↦ mixedSplitCapacity_of_ne (hX hv).1 (hX hv).2] at hS
  rw [← Flow.val_mixedSplitEquiv hst ⟨f, hf⟩]
  exact ((Flow.mixedSplitEquiv hst ⟨f, hf⟩).val_le_arrowSum hs ht).trans hS

end Flow

/-! ### The max-flow/min-cut theorem for mixed capacities -/

section MaxFlowMinCut

variable [Fintype V] [∀ v w, Fintype (Q v w)] [AddCommGroup K] [LinearOrder K]
  [IsOrderedAddMonoid K] {cap : Assignment Q K} {c : V → K} {s t : V}

/-- **Max-flow/min-cut for mixed capacities, with integrality.** For distinct terminals,
nonnegative arrow capacities and nonnegative capacities on the nonterminal vertices, all lying in an
additive subgroup `H`, some ordinary flow respecting the vertex capacities, with every arrow value
in `H`, has value equal to the weight of some mixed separator. By weak duality
(`TauCeti.Flow.RespectsVertexCapacity.val_le`), this flow is maximum among the flows respecting the
vertex capacities and this separator has minimum weight. -/
theorem Flow.exists_respectsVertexCapacity_val_eq_mem (hst : s ≠ t) (hcap : 0 ≤ cap)
    (hc : ∀ v, v ≠ s → v ≠ t → 0 ≤ c v) (H : AddSubgroup K)
    (hcapH : ∀ ⦃v w⦄ (e : Q v w), cap e ∈ H) (hcH : ∀ v, v ≠ s → v ≠ t → c v ∈ H) :
    ∃ f : Flow cap s t, f.RespectsVertexCapacity c ∧ (∀ ⦃v w⦄ (e : Q v w), f.toFun e ∈ H) ∧
      ∃ X F, IsMixedSeparator X F s t ∧ f.val = ∑ v ∈ X, c v + ∑ a ∈ F, cap a.2.2 := by
  classical
  -- The split capacities are nonnegative and lie in `H`.
  have hsplit (v : V) :
      0 ≤ mixedSplitCapacity cap c s t v ∧ mixedSplitCapacity cap c s t v ∈ H := by
    by_cases hv : v = s ∨ v = t
    · rw [mixedSplitCapacity_of_eq_or_eq hv]
      exact ⟨arrowSum_nonneg hcap _ _, arrowSum_mem hcapH _ _⟩
    · rw [not_or] at hv
      rw [mixedSplitCapacity_of_ne hv.1 hv.2]
      exact ⟨hc v hv.1 hv.2, hcH v hv.1 hv.2⟩
  have hsplit₀ : 0 ≤ assignment cap (mixedSplitCapacity cap c s t) := by
    rw [← assignment_zero, assignment_le_assignment_iff]
    exact ⟨hcap, fun v ↦ (hsplit v).1⟩
  have hsplitH ⦃x y : V × Bool⦄ (e : SplitHom Q x y) :
      assignment cap (mixedSplitCapacity cap c s t) e ∈ H := by
    rcases x with ⟨v, _ | _⟩ <;> rcases y with ⟨w, _ | _⟩
    · exact e.elim
    · obtain rfl : v = w := e.2
      rw [eq_split e, assignment_split]
      exact (hsplit v).2
    · obtain ⟨e, rfl⟩ := exists_original e
      rw [assignment_original]
      exact hcapH e
    · exact e.elim
  obtain ⟨g, hg, hgH⟩ := Flow.exists_isMaximum_mem (s := (s, true)) (t := (t, false)) hsplit₀ H
    hsplitH
  obtain ⟨S, hs, ht, hval⟩ := hg.exists_val_eq_arrowSum (by simp)
  refine ⟨((Flow.mixedSplitEquiv hst).symm g).1, ((Flow.mixedSplitEquiv hst).symm g).2,
    fun _ _ e ↦ ?_, cutVertices S, cutArrows Q S, isMixedSeparator_cutVertices_cutArrows hst hs ht,
    ?_⟩
  · rw [Flow.mixedSplitEquiv_symm_apply_toFun, originalAssignment_apply]
    exact hgH (original e)
  rw [← Flow.val_mixedSplitEquiv hst, Equiv.apply_symm_apply, hval,
    arrowSum_assignment_compl_eq_weight hs ht fun _ ↦ mixedSplitCapacity_of_ne]

/-- **Max-flow/min-cut for mixed capacities.** For distinct terminals, nonnegative arrow
capacities and nonnegative capacities on the nonterminal vertices, some ordinary flow respecting
the vertex capacities has value equal to the weight of some mixed separator. -/
theorem Flow.exists_respectsVertexCapacity_val_eq (hst : s ≠ t) (hcap : 0 ≤ cap)
    (hc : ∀ v, v ≠ s → v ≠ t → 0 ≤ c v) :
    ∃ f : Flow cap s t, f.RespectsVertexCapacity c ∧
      ∃ X F, IsMixedSeparator X F s t ∧ f.val = ∑ v ∈ X, c v + ∑ a ∈ F, cap a.2.2 :=
  let ⟨f, hf, _, hXF⟩ := Flow.exists_respectsVertexCapacity_val_eq_mem hst hcap hc ⊤
    (fun _ _ _ ↦ AddSubgroup.mem_top _) fun _ _ _ ↦ AddSubgroup.mem_top _
  ⟨f, hf, hXF⟩

end MaxFlowMinCut

end TauCeti
