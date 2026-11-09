/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.Walk.Basic

/-!
# Decomposing multigraph walks

This file splits an edge-labelled multigraph walk at the first occurrence of a specified vertex
and extracts a path by bypassing repeated vertices.  The extracted path keeps its endpoints and
uses vertices and edge identities in their original order, so it can replace a walk in
connectivity arguments without losing the distinction between parallel edges.

The interface is adapted from Mathlib's `SimpleGraph.Walk.takeUntil`,
`SimpleGraph.Walk.dropUntil`, and `SimpleGraph.Walk.bypass`.
-/

public section

universe u v

namespace Graph.Walk

variable {α : Type u} {β : Type v} {G : Graph α β}
variable {x y z a : α}

open List

section Split

variable [DecidableEq α]

/-- The initial segment of a walk ending at the first occurrence of a specified vertex. -/
def takeUntil {x y : α} : (p : G.Walk x y) → (a : α) → a ∈ p.support → G.Walk x a
  | .nil, a, ha => by
      simp only [support_nil, List.mem_singleton] at ha
      subst a
      exact .nil
  | .cons e h p, a, ha =>
      if hxa : x = a then
        hxa ▸ .nil
      else
        .cons e h (takeUntil p a (by simpa [Ne.symm hxa] using ha))

/-- The final segment of a walk starting at the first occurrence of a specified vertex. -/
def dropUntil {x y : α} : (p : G.Walk x y) → (a : α) → a ∈ p.support → G.Walk a y
  | .nil, a, ha => by
      simp only [support_nil, List.mem_singleton] at ha
      subst a
      exact .nil
  | .cons e h p, a, ha =>
      if hxa : x = a then
        hxa ▸ .cons e h p
      else
        dropUntil p a (by simpa [Ne.symm hxa] using ha)

@[simp]
theorem takeUntil_cons_of_ne (e : β) (h : G.IsLink e x y) (p : G.Walk y z)
    (hxa : x ≠ a) (ha : a ∈ (Graph.Walk.cons e h p).support) :
    (Graph.Walk.cons e h p).takeUntil a ha =
      Graph.Walk.cons e h (p.takeUntil a (by simpa [Ne.symm hxa] using ha)) := by
  simp [takeUntil, hxa]

@[simp]
theorem dropUntil_cons_of_ne (e : β) (h : G.IsLink e x y) (p : G.Walk y z)
    (hxa : x ≠ a) (ha : a ∈ (Graph.Walk.cons e h p).support) :
    (Graph.Walk.cons e h p).dropUntil a ha =
      p.dropUntil a (by simpa [Ne.symm hxa] using ha) := by
  simp [dropUntil, hxa]

@[simp]
theorem takeUntil_first (p : G.Walk x y) :
    p.takeUntil x p.start_mem_support = Graph.Walk.nil := by
  cases p <;> simp [takeUntil]

@[simp]
theorem dropUntil_first (p : G.Walk x y) :
    p.dropUntil x p.start_mem_support = p := by
  cases p <;> simp [dropUntil]

/-- Splitting at a vertex and rejoining the two pieces recovers the original walk. -/
@[simp]
theorem takeUntil_append_dropUntil (p : G.Walk x y) (ha : a ∈ p.support) :
    (p.takeUntil a ha).append (p.dropUntil a ha) = p := by
  induction p generalizing a with
  | nil =>
      simp only [support_nil, List.mem_singleton] at ha
      subst a
      simp
  | @cons x y z e h p ih =>
      by_cases hxa : x = a
      · subst a
        simp
      · have ha' : a ∈ p.support := by simpa [Ne.symm hxa] using ha
        rw [takeUntil_cons_of_ne e h p hxa ha, dropUntil_cons_of_ne e h p hxa ha,
          cons_append, ih ha']

omit [DecidableEq α] in
/-- A vertex occurs on a walk exactly when the walk can be split there. -/
theorem mem_support_iff_exists_append {p : G.Walk x y} :
    a ∈ p.support ↔ ∃ (q : G.Walk x a) (r : G.Walk a y), p = q.append r := by
  classical
  constructor
  · intro ha
    exact ⟨p.takeUntil a ha, p.dropUntil a ha, (p.takeUntil_append_dropUntil ha).symm⟩
  · rintro ⟨q, r, rfl⟩
    rw [support_append]
    exact List.mem_append_left _ q.end_mem_support

/-- The splitting vertex occurs exactly once in the initial segment. -/
@[simp]
theorem count_support_takeUntil_eq_one (p : G.Walk x y) (ha : a ∈ p.support) :
    (p.takeUntil a ha).support.count a = 1 := by
  induction p generalizing a with
  | nil =>
      simp only [support_nil, List.mem_singleton] at ha
      subst a
      simp
  | @cons x y z e h p ih =>
      by_cases hxa : x = a
      · subst a
        simp
      · have ha' : a ∈ p.support := by simpa [Ne.symm hxa] using ha
        rw [takeUntil_cons_of_ne e h p hxa ha, support_cons, List.count_cons, ih ha']
        simp [hxa]

/-- The support of the initial segment is a prefix of the original support. -/
theorem support_takeUntil_prefix_support (p : G.Walk x y) (ha : a ∈ p.support) :
    (p.takeUntil a ha).support <+: p.support := by
  have hsup := congrArg support (p.takeUntil_append_dropUntil ha)
  rw [support_append] at hsup
  rw [← hsup]
  exact List.prefix_append _ _

/-- The support of the final segment is a suffix of the original support. -/
theorem support_dropUntil_suffix_support (p : G.Walk x y) (ha : a ∈ p.support) :
    (p.dropUntil a ha).support <:+ p.support := by
  have hsup := congrArg support (p.takeUntil_append_dropUntil ha)
  rw [support_append_eq_support_dropLast_append] at hsup
  rw [← hsup]
  exact List.suffix_append _ _

/-- The edges of the initial segment are a prefix of the original edge list. -/
theorem edges_takeUntil_prefix_edges (p : G.Walk x y) (ha : a ∈ p.support) :
    (p.takeUntil a ha).edges <+: p.edges := by
  have hedges := congrArg edges (p.takeUntil_append_dropUntil ha)
  rw [edges_append] at hedges
  rw [← hedges]
  exact List.prefix_append _ _

/-- The edges of the final segment are a suffix of the original edge list. -/
theorem edges_dropUntil_suffix_edges (p : G.Walk x y) (ha : a ∈ p.support) :
    (p.dropUntil a ha).edges <:+ p.edges := by
  have hedges := congrArg edges (p.takeUntil_append_dropUntil ha)
  rw [edges_append] at hedges
  rw [← hedges]
  exact List.suffix_append _ _

theorem support_takeUntil_subset_support (p : G.Walk x y) (ha : a ∈ p.support) :
    (p.takeUntil a ha).support ⊆ p.support :=
  (p.support_takeUntil_prefix_support ha).subset

theorem support_dropUntil_subset_support (p : G.Walk x y) (ha : a ∈ p.support) :
    (p.dropUntil a ha).support ⊆ p.support :=
  (p.support_dropUntil_suffix_support ha).subset

theorem edges_takeUntil_subset_edges (p : G.Walk x y) (ha : a ∈ p.support) :
    (p.takeUntil a ha).edges ⊆ p.edges :=
  (p.edges_takeUntil_prefix_edges ha).subset

theorem edges_dropUntil_subset_edges (p : G.Walk x y) (ha : a ∈ p.support) :
    (p.dropUntil a ha).edges ⊆ p.edges :=
  (p.edges_dropUntil_suffix_edges ha).subset

theorem length_takeUntil_le_length (p : G.Walk x y) (ha : a ∈ p.support) :
    (p.takeUntil a ha).length ≤ p.length := by
  have hlen := congrArg length (p.takeUntil_append_dropUntil ha)
  simp only [length_append] at hlen
  omega

theorem length_dropUntil_le_length (p : G.Walk x y) (ha : a ∈ p.support) :
    (p.dropUntil a ha).length ≤ p.length := by
  have hlen := congrArg length (p.takeUntil_append_dropUntil ha)
  simp only [length_append] at hlen
  omega

/-- An initial segment of a trail is a trail. -/
protected theorem IsTrail.takeUntil {p : G.Walk x y} (hp : p.IsTrail)
    (ha : a ∈ p.support) : (p.takeUntil a ha).IsTrail :=
  (isTrail_def _).mpr <|
    List.Nodup.sublist (p.edges_takeUntil_prefix_edges ha).sublist ((isTrail_def p).mp hp)

/-- A final segment of a trail is a trail. -/
protected theorem IsTrail.dropUntil {p : G.Walk x y} (hp : p.IsTrail)
    (ha : a ∈ p.support) : (p.dropUntil a ha).IsTrail :=
  (isTrail_def _).mpr <|
    List.Nodup.sublist (p.edges_dropUntil_suffix_edges ha).sublist ((isTrail_def p).mp hp)

/-- An initial segment of a path is a path. -/
protected theorem IsPath.takeUntil {p : G.Walk x y} (hp : p.IsPath)
    (ha : a ∈ p.support) : (p.takeUntil a ha).IsPath :=
  (isPath_def _).mpr <|
    List.Nodup.sublist (p.support_takeUntil_prefix_support ha).sublist ((isPath_def p).mp hp)

/-- A final segment of a path is a path. -/
protected theorem IsPath.dropUntil {p : G.Walk x y} (hp : p.IsPath)
    (ha : a ∈ p.support) : (p.dropUntil a ha).IsPath :=
  (isPath_def _).mpr <|
    List.Nodup.sublist (p.support_dropUntil_suffix_support ha).sublist ((isPath_def p).mp hp)

end Split

/-- A path from outside a vertex set to a vertex in it has an initial segment whose endpoint is
the first visited vertex in the set.  Every other vertex of the segment is outside the set, and
the segment uses only vertices and edge identities of the original path. -/
theorem IsPath.exists_initialSegment_to_set {p : G.Walk x y} (hp : p.IsPath)
    {S : Set α} (hx : x ∉ S) (hy : y ∈ S) :
    ∃ (z : α) (q : G.Walk x z), q.IsPath ∧ z ∈ S ∧
      (∀ w ∈ q.support, w ≠ x → w ≠ z → w ∉ S) ∧
      q.support ⊆ p.support ∧ q.edges ⊆ p.edges := by
  induction p with
  | nil => exact (hx hy).elim
  | @cons x y z e h p ih =>
      have hp' := (isPath_cons e h p).mp hp
      by_cases hyS : y ∈ S
      · refine ⟨y, .cons e h .nil, ?_, hyS, ?_, ?_, ?_⟩
        · have hxy : x ≠ y := by
            intro hxy
            subst y
            exact hx hyS
          exact (isPath_cons e h .nil).mpr
            ⟨(isPath_def .nil).mpr (by simp),
              by simpa only [support_nil, List.mem_singleton] using hxy⟩
        · simp
        · intro w hw
          simp only [support_cons, support_nil, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
          rcases hw with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr p.start_mem_support
        · simp
      · obtain ⟨w, q, hq, hwS, hinter, hsupport, hedges⟩ := ih hp'.1 hyS hy
        refine ⟨w, .cons e h q, (isPath_cons e h q).mpr ⟨hq, ?_⟩, hwS, ?_, ?_, ?_⟩
        · exact fun hmem ↦ hp'.2 (hsupport hmem)
        · intro a ha hax haw
          simp only [support_cons, List.mem_cons] at ha
          rcases ha with rfl | ha
          · exact (hax rfl).elim
          · by_cases hay : a = y
            · exact hay ▸ hyS
            · exact hinter a ha hay haw
        · intro a ha
          simp only [support_cons, List.mem_cons] at ha ⊢
          exact ha.elim (fun h ↦ Or.inl h) fun h ↦ Or.inr (hsupport h)
        · intro f hf
          simp only [edges_cons, List.mem_cons] at hf ⊢
          exact hf.elim (fun h ↦ Or.inl h) fun h ↦ Or.inr (hedges h)

/-- An edge identity occurs on a walk exactly when the walk can be split around one traversal of
that edge. -/
theorem mem_edges_iff_exists_append {p : G.Walk x y} {e : β} :
    e ∈ p.edges ↔ ∃ (u v : α) (h : G.IsLink e u v) (q : G.Walk x u) (r : G.Walk v y),
      p = q.append (cons e h r) := by
  constructor
  · intro he
    induction p with
    | nil => simp at he
    | @cons x z y f hf p ih =>
      by_cases hfe : f = e
      · subst f
        exact ⟨x, z, hf, nil, p, (nil_append _).symm⟩
      · have he' : e ∈ p.edges := by simpa [Ne.symm hfe] using he
        obtain ⟨u, v, h, q, r, rfl⟩ := ih he'
        exact ⟨u, v, h, cons f hf q, r, (cons_append ..).symm⟩
  · rintro ⟨u, v, h, q, r, rfl⟩
    simp [edges_append]

/-- A path whose endpoints are joined by an edge that it traverses consists of that edge alone. -/
theorem IsPath.eq_toWalk_of_isLink_mem_edges {p : G.Walk x y} (hp : p.IsPath)
    (h : G.IsLink e x y) (he : e ∈ p.edges) : p = h.toWalk := by
  obtain ⟨u, v, huv, q, r, rfl⟩ := mem_edges_iff_exists_append.1 he
  rw [isPath_def, support_append, support_cons, List.tail_cons, List.nodup_append] at hp
  rcases huv.eq_and_eq_or_eq_and_eq h with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · subst u
    subst v
    rw [(isPath_iff_nil.mp ((isPath_def q).2 hp.1)).eq_nil,
      (isPath_iff_nil.mp ((isPath_def r).2 hp.2.1)).eq_nil]
    rw [h.toWalk_eq_cons]
    rw [nil_append]
  · subst u
    subst v
    exact absurd (hp.2.2 x q.start_mem_support x r.start_mem_support rfl) (by simp)

/-- A path cannot traverse a loop edge. -/
theorem IsPath.not_isLoopAt_of_mem_edges {p : G.Walk x y} (hp : p.IsPath)
    (he : e ∈ p.edges) (a : α) : ¬G.IsLoopAt e a := by
  intro hloop
  obtain ⟨u, v, huv, q, r, rfl⟩ := mem_edges_iff_exists_append.1 he
  rw [isPath_def, support_append, support_cons, List.tail_cons, List.nodup_append] at hp
  rcases huv.eq_and_eq_or_eq_and_eq hloop with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals exact hp.2.2 _ q.end_mem_support _ r.start_mem_support rfl

section Extraction

variable [DecidableEq α]

/-- Remove closed portions of a walk between repeated vertices, retaining the endpoints. -/
def bypass {x y : α} : G.Walk x y → G.Walk x y
  | .nil => .nil
  | .cons e h p =>
      let q := p.bypass
      if hx : x ∈ q.support then q.dropUntil x hx else .cons e h q

@[simp]
theorem bypass_nil : (Graph.Walk.nil : G.Walk x x).bypass = Graph.Walk.nil := (rfl)

theorem bypass_cons (e : β) (h : G.IsLink e x y) (p : G.Walk y z) :
    (Graph.Walk.cons e h p).bypass =
      if hx : x ∈ p.bypass.support then p.bypass.dropUntil x hx
      else Graph.Walk.cons e h p.bypass := (rfl)

/-- Bypassing repeated vertices produces a path. -/
theorem bypass_isPath (p : G.Walk x y) : p.bypass.IsPath := by
  induction p with
  | nil => simp
  | @cons x y z e h p ih =>
      rw [bypass_cons]
      split_ifs with hx
      · exact ih.dropUntil hx
      · simpa using (isPath_cons e h p.bypass).2 ⟨ih, hx⟩

/-- Bypassing preserves the order of the retained vertices. -/
theorem support_bypass_sublist_support (p : G.Walk x y) :
    p.bypass.support <+ p.support := by
  induction p with
  | nil => simp
  | @cons x y z e h p ih =>
      rw [bypass_cons]
      split_ifs with hx
      · simpa only [support_cons] using
          ((p.bypass.support_dropUntil_suffix_support hx).sublist.trans ih).cons x
      · simpa only [support_cons] using ih.cons_cons x

/-- Bypassing preserves the order and identity of the retained edges. -/
theorem edges_bypass_sublist_edges (p : G.Walk x y) :
    p.bypass.edges <+ p.edges := by
  induction p with
  | nil => simp
  | @cons x y z e h p ih =>
      rw [bypass_cons]
      split_ifs with hx
      · simpa only [edges_cons] using
          ((p.bypass.edges_dropUntil_suffix_edges hx).sublist.trans ih).cons e
      · simpa only [edges_cons] using ih.cons_cons e

theorem support_bypass_subset_support (p : G.Walk x y) :
    p.bypass.support ⊆ p.support :=
  p.support_bypass_sublist_support.subset

theorem edges_bypass_subset_edges (p : G.Walk x y) :
    p.bypass.edges ⊆ p.edges :=
  p.edges_bypass_sublist_edges.subset

theorem length_bypass_le_length (p : G.Walk x y) : p.bypass.length ≤ p.length := by
  simpa only [length_edges] using p.edges_bypass_sublist_edges.length_le

/-- Bypassing a path does not change it. -/
theorem IsPath.bypass_eq_self {p : G.Walk x y} (hp : p.IsPath) : p.bypass = p := by
  induction p with
  | nil => simp
  | @cons x y z e h p ih =>
      rw [isPath_cons] at hp
      rw [bypass_cons, ih hp.1]
      simp [hp.2]

@[simp]
theorem bypass_eq_self_iff_isPath {p : G.Walk x y} : p.bypass = p ↔ p.IsPath :=
  ⟨fun h => h ▸ p.bypass_isPath, IsPath.bypass_eq_self⟩

end Extraction

end Graph.Walk

namespace Graph.Reachable

variable {α : Type u} {β : Type v} {G : Graph α β} {x y : α}

/-- Every pair of reachable vertices is joined by a path retaining actual multigraph edge
identities. -/
theorem exists_isPath (h : G.Reachable x y) :
    ∃ p : G.Walk x y, p.IsPath := by
  classical
  exact h.elim fun p => ⟨p.bypass, p.bypass_isPath⟩

end Graph.Reachable
