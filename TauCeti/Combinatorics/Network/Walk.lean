/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Quiver.Path.Vertices
public import Mathlib.Data.Fintype.Card
public import Mathlib.Order.WellFounded
public import Mathlib.Data.List.Nodup
public import TauCeti.Combinatorics.Network.Basic

/-!
# Directed walks along an explicit arrow family

A directed walk along an arrow family `Q : V → V → Type*` is a Mathlib `Quiver.Path` for the
quiver whose arrows from `v` to `w` are the terms of `Q v w`. The quiver is supplied explicitly,
as `@Quiver.Path V ⟨Q⟩ s t`, so that several arrow families on one vertex type, such as a network
and its residual network, have their own walks without competing `Quiver` instances.
`TauCeti.ArrowWalk Q s t` abbreviates this type, and the abbreviations in its namespace expose the
Mathlib path operations through dot notation.

A walk records the identities of the arrows it traverses, which `TauCeti.ArrowWalk.arrows` lists
in order with repetitions. A directed *path* repeats no vertex, and a directed *cycle* is a closed
walk of positive length that repeats no vertex other than its common endpoints. Since the target
of each traversed arrow is a later vertex of the walk, neither repeats an arrow; this is what
bounds the value a path or cycle places on a single arrow in flow augmentation. Every walk
contains a path between the same endpoints that uses only arrows of the walk, and every closed
walk of positive length contains a cycle at the same vertex that uses only arrows of the walk.
The *bottleneck* of a walk for capacities `c` is the least capacity of an arrow it traverses, and
a vertex is *positively reachable* from another when some walk joins them along arrows of positive
capacity; for residual capacities these are augmenting walks.

## Main definitions

* `TauCeti.ArrowWalk Q s t`: directed walks from `s` to `t` along the arrow family `Q`.
* `TauCeti.ArrowWalk.arrows`: the arrows traversed by a walk, in order.
* `TauCeti.ArrowWalk.IsPath` and `TauCeti.ArrowWalk.IsCycle`: directed paths and cycles.
* `TauCeti.Assignment.IsAcyclic`: arrow assignments whose positive support contains no directed
  cycle.
* `TauCeti.ArrowWalk.bottleneck`: the least capacity along a walk that traverses an arrow.
* `TauCeti.PositiveReachable c s t`: some walk from `s` to `t` traverses only arrows of positive
  capacity for `c`.
* `TauCeti.ReachableWithout F s t`: some walk from `s` to `t` traverses no arrow of the set `F`
  of arrows, so `t` stays reachable from `s` after deleting the arrows of `F`.

## Main results

* `TauCeti.ArrowWalk.map_target_arrows`: the targets of the traversed arrows are the vertices of
  the walk after its first.
* `TauCeti.ArrowWalk.IsPath.nodup_arrows` and `TauCeti.ArrowWalk.IsCycle.nodup_arrows`: paths and
  cycles traverse every arrow at most once.
* `TauCeti.ArrowWalk.exists_isPath_arrows_subset`: every walk contains a path with the same
  endpoints.
* `TauCeti.ArrowWalk.exists_isCycle_arrows_subset`: every closed walk of positive length contains
  a cycle.
* `TauCeti.ArrowWalk.le_bottleneck_iff` and `TauCeti.ArrowWalk.exists_mem_bottleneck_eq`: the
  bottleneck is the minimum of the capacities along the walk.
* `TauCeti.positiveReachable_iff_exists_isPath` and `TauCeti.positiveReachable_iff_reflTransGen`:
  positive reachability is witnessed by a path, and is the reflexive transitive closure of being
  joined by an arrow of positive capacity; `TauCeti.exists_isCycle_iff_transGen` is the
  counterpart for cycles.
* `TauCeti.Assignment.isAcyclic_iff_forall_not_transGen`: an assignment is acyclic exactly when
  no vertex reaches itself in one or more steps along arrows of positive value.
* `TauCeti.positiveReachable_iff_nonempty_arrowWalk`: positive reachability is reachability along
  the arrow family `TauCeti.PositiveHom c` of arrows of positive capacity.
* `TauCeti.PositiveReachable.mem_of_mem`: a vertex set that no arrow of positive capacity leaves
  contains every vertex positively reachable from one of its members, and
  `TauCeti.ReachableWithout.mem_of_mem` is the counterpart for deleted arrows.
* `TauCeti.positiveReachable_map_iff` and `TauCeti.positiveReachable_map_iff_of_strictMono`: a
  coefficient map preserving and reflecting positivity, such as a strictly monotone map fixing
  zero, does not change positive reachability.
-/

public section

namespace TauCeti

universe u v w

variable {V : Type u} {Q : V → V → Type v}

variable (Q) in
/-- Directed walks from `s` to `t` along the arrow family `Q`: Mathlib's quiver paths for the
quiver with arrow types `Q`, supplied explicitly rather than as an instance. -/
abbrev ArrowWalk (s t : V) := @Quiver.Path V ⟨Q⟩ s t

namespace ArrowWalk

/-- The walk of length zero at `s`. -/
abbrev nil (s : V) : ArrowWalk Q s s :=
  @Quiver.Path.nil V ⟨Q⟩ s

/-- The walk `p` followed by the arrow `e`. -/
abbrev cons {s t x : V} (p : ArrowWalk Q s t) (e : Q t x) : ArrowWalk Q s x :=
  @Quiver.Path.cons V ⟨Q⟩ s t x p e

/-- The walk `p` followed by the walk `p'`. -/
abbrev comp {s t x : V} (p : ArrowWalk Q s t) (p' : ArrowWalk Q t x) : ArrowWalk Q s x :=
  @Quiver.Path.comp V ⟨Q⟩ s t x p p'

/-- The number of arrows traversed by a walk. -/
abbrev length {s t : V} (p : ArrowWalk Q s t) : ℕ :=
  @Quiver.Path.length V ⟨Q⟩ s t p

/-- The vertices visited by a walk, in order, from its source to its target. -/
abbrev vertices {s t : V} (p : ArrowWalk Q s t) : List V :=
  @Quiver.Path.vertices V ⟨Q⟩ s t p

/-- The arrows traversed by a walk, in order and with repetitions, each recorded with its
endpoints. -/
def arrows {s : V} : ∀ {t : V}, ArrowWalk Q s t → List (Σ x y, Q x y)
  | _, @Quiver.Path.nil _ .(_) _ => []
  | _, @Quiver.Path.cons _ .(_) _ _ _ p e => arrows p ++ [⟨_, _, e⟩]

@[simp]
theorem arrows_nil (s : V) : (nil s : ArrowWalk Q s s).arrows = [] :=
  (rfl)

@[simp]
theorem arrows_cons {s t x : V} (p : ArrowWalk Q s t) (e : Q t x) :
    (p.cons e).arrows = p.arrows ++ [⟨_, _, e⟩] :=
  (rfl)

@[simp]
theorem arrows_comp {s t x : V} (p : ArrowWalk Q s t) (p' : ArrowWalk Q t x) :
    (p.comp p').arrows = p.arrows ++ p'.arrows := by
  induction p' with
  | nil => simp [comp]
  | cons p' e ih => simp [comp, ← List.append_assoc, ← ih]

@[simp]
theorem length_arrows {s t : V} (p : ArrowWalk Q s t) : p.arrows.length = p.length := by
  induction p with
  | nil => simp
  | cons p e ih => simp [ih]

@[simp]
theorem arrows_eq_nil_iff {s t : V} {p : ArrowWalk Q s t} : p.arrows = [] ↔ p.length = 0 := by
  rw [← List.length_eq_zero_iff, length_arrows]

/-- A walk between distinct vertices traverses an arrow. -/
theorem arrows_ne_nil {s t : V} (p : ArrowWalk Q s t) (hst : s ≠ t) : p.arrows ≠ [] :=
  fun h ↦ hst (@Quiver.Path.eq_of_length_zero V ⟨Q⟩ s t p (arrows_eq_nil_iff.1 h))

/-- The targets of the arrows traversed by a walk are its vertices after the first. -/
theorem map_target_arrows {s t : V} (p : ArrowWalk Q s t) :
    p.arrows.map (fun a ↦ a.2.1) = p.vertices.tail := by
  induction p with
  | nil => simp
  | cons p e ih =>
    simp only [arrows_cons, List.map_append, ih, vertices, Quiver.Path.vertices_cons,
      List.concat_eq_append, List.map_singleton]
    rw [List.tail_append_of_ne_nil (@Quiver.Path.vertices_ne_nil V ⟨Q⟩ _ _ p)]

/-- The vertices of a walk are its source followed by the targets of its arrows. -/
theorem vertices_eq_cons_map_target_arrows {s t : V} (p : ArrowWalk Q s t) :
    p.vertices = s :: p.arrows.map (fun a ↦ a.2.1) := by
  rw [map_target_arrows]
  exact List.eq_cons_of_mem_head? (@Quiver.Path.vertices_head? V ⟨Q⟩ s t p)

/-- A walk whose vertices after the first are distinct traverses no arrow twice. -/
theorem nodup_arrows_of_nodup_tail {s t : V} {p : ArrowWalk Q s t}
    (hp : p.vertices.tail.Nodup) : p.arrows.Nodup :=
  List.Nodup.of_map (fun a ↦ a.2.1) (p.map_target_arrows ▸ hp)

/-! ### Paths and cycles -/

/-- A directed *path*: a walk that visits no vertex twice. -/
def IsPath {s t : V} (p : ArrowWalk Q s t) : Prop :=
  p.vertices.Nodup

theorem isPath_def {s t : V} (p : ArrowWalk Q s t) : p.IsPath ↔ p.vertices.Nodup :=
  Iff.rfl

@[simp]
theorem isPath_nil (s : V) : (nil s : ArrowWalk Q s s).IsPath := by
  simp [isPath_def]

/-- A path traverses every arrow at most once. -/
theorem IsPath.nodup_arrows {s t : V} {p : ArrowWalk Q s t} (hp : p.IsPath) : p.arrows.Nodup :=
  nodup_arrows_of_nodup_tail hp.tail

/-- A directed *cycle*: a closed walk of positive length that visits no vertex twice, apart from
its common first and last vertex. A loop is a cycle of length one. -/
def IsCycle {s : V} (c : ArrowWalk Q s s) : Prop :=
  0 < c.length ∧ c.vertices.tail.Nodup

theorem isCycle_def {s : V} (c : ArrowWalk Q s s) :
    c.IsCycle ↔ 0 < c.length ∧ c.vertices.tail.Nodup :=
  Iff.rfl

/-- A loop is a cycle. -/
theorem isCycle_loop {s : V} (e : Q s s) : ((nil s).cons e).IsCycle := by
  simp [isCycle_def]

/-- A cycle traverses every arrow at most once. -/
theorem IsCycle.nodup_arrows {s : V} {c : ArrowWalk Q s s} (hc : c.IsCycle) : c.arrows.Nodup :=
  nodup_arrows_of_nodup_tail hc.2

/-- A cycle traverses at least one arrow. -/
theorem IsCycle.arrows_ne_nil {s : V} {c : ArrowWalk Q s s} (hc : c.IsCycle) : c.arrows ≠ [] :=
  fun h ↦ hc.1.ne' (arrows_eq_nil_iff.1 h)

/-- An initial segment of a path is a path. -/
theorem IsPath.of_comp_left {s t x : V} {p : ArrowWalk Q s t} {p' : ArrowWalk Q t x}
    (hp : (p.comp p').IsPath) : p.IsPath := by
  have hcomp : (p.comp p').vertices = p.vertices.dropLast ++ p'.vertices :=
    @Quiver.Path.vertices_comp V ⟨Q⟩ _ _ _ p p'
  have hend : p.vertices.dropLast ++ [t] = p.vertices :=
    @Quiver.Path.dropLast_append_end_eq V ⟨Q⟩ _ _ p
  rw [isPath_def, hcomp] at hp
  rw [isPath_def, ← hend]
  exact hp.sublist <|
    (List.singleton_sublist.2 (@Quiver.Path.start_mem_vertices V ⟨Q⟩ _ _ p')).append_left _

/-- **Path extraction.** Every walk contains a path with the same endpoints that traverses only
arrows of the walk. -/
theorem exists_isPath_arrows_subset {s t : V} (p : ArrowWalk Q s t) :
    ∃ p' : ArrowWalk Q s t, p'.IsPath ∧ p'.arrows ⊆ p.arrows := by
  induction p with
  | nil => exact ⟨nil s, isPath_nil s, List.Subset.refl _⟩
  | @cons x y p e ih =>
    obtain ⟨p', hp', hsub⟩ := ih
    have harrows : arrows (Q := Q) (cons p e) = arrows (Q := Q) p ++ [⟨_, _, e⟩] :=
      arrows_cons p e
    rw [harrows]
    by_cases hy : y ∈ p'.vertices
    · -- `y` already occurs on `p'`: keep the initial segment of `p'` ending at `y`
      obtain ⟨p₁, p₂, hp⟩ := @Quiver.Path.exists_eq_comp_of_mem_vertices V ⟨Q⟩ _ _ p' _ hy
      have hp : p' = comp (Q := Q) p₁ p₂ := hp
      subst hp
      refine ⟨p₁, hp'.of_comp_left, List.subset_append_of_subset_left _ (fun a ha ↦ hsub ?_)⟩
      rw [arrows_comp]
      exact List.mem_append_left _ ha
    · -- `y` is new: extend `p'` by `e`
      have hv : (p'.cons e).vertices = p'.vertices.concat y :=
        @Quiver.Path.vertices_cons V ⟨Q⟩ _ _ _ p' e
      refine ⟨p'.cons e, by rw [isPath_def, hv]; exact hp'.concat hy, ?_⟩
      rw [arrows_cons]
      exact List.append_subset.2
        ⟨List.subset_append_of_subset_left _ hsub, List.subset_append_right _ _⟩

/-- **Cycle extraction.** Every closed walk of positive length contains a cycle at the same vertex
that traverses only arrows of the walk. -/
theorem exists_isCycle_arrows_subset {s : V} (c : ArrowWalk Q s s) (hc : 0 < c.length) :
    ∃ c' : ArrowWalk Q s s, c'.IsCycle ∧ c'.arrows ⊆ c.arrows := by
  cases c with
  | nil => simp at hc
  | @cons u _ p e =>
    obtain ⟨p', hp', hsub⟩ := exists_isPath_arrows_subset (Q := Q) p
    refine ⟨p'.cons e, ⟨by simp, ?_⟩, ?_⟩
    · have hv : (p'.cons e).vertices = p'.vertices.concat s :=
        @Quiver.Path.vertices_cons V ⟨Q⟩ _ _ _ p' e
      have hne : p'.vertices ≠ [] := @Quiver.Path.vertices_ne_nil V ⟨Q⟩ _ _ p'
      have hh : p'.vertices.head hne = s := @Quiver.Path.vertices_head_eq V ⟨Q⟩ _ _ p' hne
      have hhead : p'.vertices = s :: p'.vertices.tail := by
        conv_lhs => rw [← List.cons_head_tail hne, hh]
      rw [isPath_def, hhead, List.nodup_cons] at hp'
      rw [hv, List.concat_eq_append, List.tail_append_of_ne_nil hne]
      exact hp'.2.append (List.nodup_singleton s) (List.disjoint_singleton.2 hp'.1)
    · rw [arrows_cons, arrows_cons]
      exact List.append_subset.2
        ⟨List.subset_append_of_subset_left _ hsub, List.subset_append_right _ _⟩

/-! ### Bottlenecks -/

section Bottleneck

variable {K : Type w} [LinearOrder K]

/-- The *bottleneck* of a walk `p` that traverses at least one arrow, for the capacities `c`: the
least capacity of an arrow traversed by `p`. -/
def bottleneck (c : Assignment Q K) {s t : V} (p : ArrowWalk Q s t) (hne : p.arrows ≠ []) : K :=
  (p.arrows.map fun a ↦ c a.2.2).min (by simpa using hne)

variable {c : Assignment Q K} {s t : V} {p : ArrowWalk Q s t} {hne : p.arrows ≠ []}

/-- A value is at most the bottleneck exactly when it is at most every capacity along the walk. -/
theorem le_bottleneck_iff {x : K} :
    x ≤ p.bottleneck c hne ↔ ∀ a ∈ p.arrows, x ≤ c a.2.2 := by
  simp only [bottleneck, List.le_min_iff, List.forall_mem_map]

theorem bottleneck_le {a : Σ x y, Q x y} (ha : a ∈ p.arrows) : p.bottleneck c hne ≤ c a.2.2 :=
  le_bottleneck_iff.1 le_rfl a ha

/-- The bottleneck is attained on an arrow traversed by the walk. -/
theorem exists_mem_bottleneck_eq : ∃ a ∈ p.arrows, p.bottleneck c hne = c a.2.2 := by
  simpa [bottleneck, eq_comm] using List.min_mem (l := p.arrows.map fun a ↦ c a.2.2)
    (by simpa using hne)

/-- The bottleneck lies in every set that contains the capacities along the walk. -/
theorem bottleneck_mem {A : Set K} (h : ∀ a ∈ p.arrows, c a.2.2 ∈ A) : p.bottleneck c hne ∈ A := by
  obtain ⟨a, ha, hb⟩ := exists_mem_bottleneck_eq (c := c) (hne := hne)
  exact hb ▸ h a ha

/-- A value is below the bottleneck exactly when it is below every capacity along the walk. -/
theorem lt_bottleneck_iff {x : K} :
    x < p.bottleneck c hne ↔ ∀ a ∈ p.arrows, x < c a.2.2 :=
  ⟨fun h _ ha ↦ h.trans_le (bottleneck_le ha), bottleneck_mem (A := {y | x < y})⟩

end Bottleneck

end ArrowWalk

/-- An arrow-disjoint family of walks between distinct vertices has distinct members: a walk
between distinct vertices traverses some arrow, which a second copy of it would share. -/
theorem injective_of_pairwise_disjoint_arrows {s t : V} (hst : s ≠ t) {ι : Type*}
    {P : ι → ArrowWalk Q s t} (hP : Pairwise fun i j ↦ (P i).arrows.Disjoint (P j).arrows) :
    Function.Injective P := by
  intro i j hij
  by_contra hne
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _ ((P j).arrows_ne_nil hst)
  exact hP hne (hij ▸ ha) ha

/-! ### Reachability along arrows of positive capacity -/

section PositiveReachable

variable {K : Type w} [Zero K] [LT K]

/-- The vertex `t` is *positively reachable* from `s` for the capacities `c` when some walk from `s`
to `t` traverses only arrows of positive capacity. For the residual capacities of a flow, such a
walk is an augmenting walk. -/
def PositiveReachable (c : Assignment Q K) (s t : V) : Prop :=
  ∃ p : ArrowWalk Q s t, ∀ a ∈ p.arrows, 0 < c a.2.2

variable {c : Assignment Q K} {s t x : V}

theorem positiveReachable_def :
    PositiveReachable c s t ↔ ∃ p : ArrowWalk Q s t, ∀ a ∈ p.arrows, 0 < c a.2.2 :=
  Iff.rfl

/-- Positive reachability is unchanged by a coefficient map that preserves and reflects
positivity. -/
theorem positiveReachable_map_iff {L : Type*} [Zero L] [LT L] {φ : K → L}
    (hφ : ∀ x, 0 < φ x ↔ 0 < x) : PositiveReachable (c.map φ) s t ↔ PositiveReachable c s t := by
  simp only [positiveReachable_def, Assignment.map_apply, hφ]

@[refl, simp]
theorem PositiveReachable.refl (c : Assignment Q K) (s : V) : PositiveReachable c s s :=
  ⟨ArrowWalk.nil s, by simp⟩

/-- A positively reachable vertex stays reachable along a further arrow of positive capacity. -/
theorem PositiveReachable.tail (h : PositiveReachable c s t) (e : Q t x) (he : 0 < c e) :
    PositiveReachable c s x := by
  obtain ⟨p, hp⟩ := h
  refine ⟨p.cons e, fun a ha ↦ ?_⟩
  rw [ArrowWalk.arrows_cons, List.mem_append, List.mem_singleton] at ha
  rcases ha with ha | rfl
  exacts [hp a ha, he]

/-- The head of an arrow of positive capacity is positively reachable from its tail. -/
theorem PositiveReachable.single (e : Q s t) (he : 0 < c e) : PositiveReachable c s t :=
  (PositiveReachable.refl c s).tail e he

@[trans]
theorem PositiveReachable.trans (h : PositiveReachable c s t) (h' : PositiveReachable c t x) :
    PositiveReachable c s x := by
  obtain ⟨p, hp⟩ := h
  obtain ⟨p', hp'⟩ := h'
  refine ⟨p.comp p', fun a ha ↦ ?_⟩
  rw [ArrowWalk.arrows_comp, List.mem_append] at ha
  exact ha.elim (hp a) (hp' a)

/-- The target of every arrow on a walk from `s` along arrows of positive capacity is positively
reachable from `s`. -/
theorem positiveReachable_of_mem_arrows {p : ArrowWalk Q s t} (hp : ∀ a ∈ p.arrows, 0 < c a.2.2)
    {a : Σ x y, Q x y} (ha : a ∈ p.arrows) : PositiveReachable c s a.2.1 := by
  induction p with
  | nil => simp at ha
  | cons p e ih =>
    simp only [ArrowWalk.arrows_cons, List.mem_append, List.mem_singleton] at hp ha
    rcases ha with ha | rfl
    · exact ih (fun a ha ↦ hp a (.inl ha)) ha
    · exact positiveReachable_def.2 ⟨ArrowWalk.cons p e, fun a ha ↦ hp a (by simpa using ha)⟩

/-- Positive reachability is witnessed by a path. -/
theorem positiveReachable_iff_exists_isPath :
    PositiveReachable c s t ↔ ∃ p : ArrowWalk Q s t, p.IsPath ∧ ∀ a ∈ p.arrows, 0 < c a.2.2 := by
  refine ⟨fun ⟨p, hp⟩ ↦ ?_, fun ⟨p, _, hp⟩ ↦ ⟨p, hp⟩⟩
  obtain ⟨p', hp', hsub⟩ := p.exists_isPath_arrows_subset
  exact ⟨p', hp', fun a ha ↦ hp a (hsub ha)⟩

/-- Positive reachability is the reflexive transitive closure of being joined by an arrow of
positive capacity. -/
theorem positiveReachable_iff_reflTransGen :
    PositiveReachable c s t ↔ Relation.ReflTransGen (fun v w ↦ ∃ e : Q v w, 0 < c e) s t := by
  constructor
  · rintro ⟨p, hp⟩
    induction p with
    | nil => exact .refl
    | cons p e ih =>
      simp only [ArrowWalk.arrows_cons, List.mem_append, List.mem_singleton] at hp
      exact .tail (ih fun a ha ↦ hp a (.inl ha)) ⟨e, hp _ (.inr rfl)⟩
  · intro h
    induction h with
    | refl => exact .refl c s
    | tail _ he ih => exact ih.tail he.choose he.choose_spec

/-- **Cycles of positive arrows.** Some cycle at `v` traverses only arrows of positive capacity
exactly when `v` reaches itself in one or more steps along arrows of positive capacity. -/
theorem exists_isCycle_iff_transGen {v : V} :
    (∃ p : ArrowWalk Q v v, p.IsCycle ∧ ∀ a ∈ p.arrows, 0 < c a.2.2) ↔
      Relation.TransGen (fun v w ↦ ∃ e : Q v w, 0 < c e) v v := by
  constructor
  · rintro ⟨p, hp, hpos⟩
    cases p with
    | nil => simp [ArrowWalk.isCycle_def] at hp
    | cons p e =>
      simp only [ArrowWalk.arrows_cons, List.mem_append, List.mem_singleton] at hpos
      exact Relation.TransGen.tail'_iff.2 ⟨_, positiveReachable_iff_reflTransGen.1
        ⟨p, fun a ha ↦ hpos a (.inl ha)⟩, e, hpos _ (.inr rfl)⟩
  · intro h
    obtain ⟨u, hvu, e, he⟩ := Relation.TransGen.tail'_iff.1 h
    obtain ⟨p, hp⟩ := positiveReachable_iff_reflTransGen.2 hvu
    obtain ⟨p', hp', hsub⟩ := (p.cons e).exists_isCycle_arrows_subset (by simp)
    refine ⟨p', hp', fun a ha ↦ ?_⟩
    have ha := hsub ha
    rw [ArrowWalk.arrows_cons, List.mem_append, List.mem_singleton] at ha
    rcases ha with ha | rfl
    exacts [hp a ha, he]

namespace Assignment

/-- An arrow assignment is *acyclic* when no directed cycle traverses only arrows of positive
value. -/
def IsAcyclic (f : Assignment Q K) : Prop :=
  ∀ ⦃v : V⦄ (c : ArrowWalk Q v v), c.IsCycle → ¬∀ a ∈ c.arrows, 0 < f a.2.2

theorem isAcyclic_def (f : Assignment Q K) :
    f.IsAcyclic ↔ ∀ ⦃v : V⦄ (c : ArrowWalk Q v v), c.IsCycle → ¬∀ a ∈ c.arrows, 0 < f a.2.2 :=
  Iff.rfl

/-- An assignment is acyclic exactly when no vertex reaches itself in one or more steps along
arrows of positive value. -/
theorem isAcyclic_iff_forall_not_transGen (f : Assignment Q K) :
    f.IsAcyclic ↔ ∀ v, ¬Relation.TransGen (fun v w ↦ ∃ e : Q v w, 0 < f e) v v := by
  simp only [← exists_isCycle_iff_transGen, not_exists, not_and]
  exact ⟨fun h v c ↦ h c, fun h v c ↦ h v c⟩

end Assignment

variable (c) in
/-- The arrows of positive capacity for `c`, retaining their identities: the arrow family of the
part of `Q` along which positive reachability travels. -/
abbrev PositiveHom (v w : V) : Type v :=
  {e : Q v w // 0 < c e}

/-- Positive reachability is reachability along the arrows of positive capacity. -/
theorem positiveReachable_iff_nonempty_arrowWalk :
    PositiveReachable c s t ↔ Nonempty (ArrowWalk (PositiveHom c) s t) := by
  rw [positiveReachable_iff_reflTransGen]
  constructor
  · intro h
    induction h with
    | refl => exact ⟨ArrowWalk.nil s⟩
    | tail _ he ih => exact ⟨ih.some.cons ⟨he.choose, he.choose_spec⟩⟩
  · rintro ⟨p⟩
    induction p with
    | nil => exact .refl
    | cons _ e ih => exact .tail ih ⟨e.1, e.2⟩

/-- A vertex set that no arrow of positive capacity leaves is closed under positive reachability.
-/
theorem PositiveReachable.mem_of_mem {C : Set V} (h : PositiveReachable c s t) (hs : s ∈ C)
    (hC : ∀ ⦃v w : V⦄ (e : Q v w), v ∈ C → 0 < c e → w ∈ C) : t ∈ C := by
  rw [positiveReachable_iff_reflTransGen] at h
  induction h with
  | refl => exact hs
  | tail _ he ih => exact hC he.choose ih he.choose_spec

end PositiveReachable

/-- Positive reachability is unchanged by a strictly monotone coefficient map fixing zero. -/
theorem positiveReachable_map_iff_of_strictMono {K L : Type*} [Zero K] [LinearOrder K] [Zero L]
    [Preorder L] {c : Assignment Q K} {φ : K → L} (hφ : StrictMono φ) (hφ₀ : φ 0 = 0) {s t : V} :
    PositiveReachable (c.map φ) s t ↔ PositiveReachable c s t :=
  positiveReachable_map_iff fun x ↦ by rw [← hφ₀, hφ.lt_iff_lt]

open Relation in
/-- If no vertex reaches itself along positive arrows and some arrow is positive, there is a
positive path between distinct vertices, with no positive arrow entering its initial vertex and no
positive arrow leaving its final vertex. -/
lemma exists_isPath_of_isAcyclic {K : Type w} [Zero K] [LinearOrder K] [Finite V]
    {f : Assignment Q K} (hf : 0 ≤ f) (hacyc : f.IsAcyclic) {x y : V} (e : Q x y)
    (he : 0 < f e) :
    ∃ (s t : V) (p : ArrowWalk Q s t), p.IsPath ∧ s ≠ t ∧ (∀ a ∈ p.arrows, 0 < f a.2.2) ∧
      (∀ w (e : Q w s), f e = 0) ∧ ∀ w (e : Q t w), f e = 0 := by
  rw [Assignment.isAcyclic_iff_forall_not_transGen] at hacyc
  set R : V → V → Prop := fun v w ↦ ∃ e : Q v w, 0 < f e
  have : IsTrans V (TransGen R) := ⟨fun _ _ _ ↦ TransGen.trans⟩
  have : IsTrans V (flip (TransGen R)) := ⟨fun _ _ _ h₁ h₂ ↦ TransGen.trans h₂ h₁⟩
  have : Std.Irrefl (TransGen R) := ⟨hacyc⟩
  have : Std.Irrefl (flip (TransGen R)) := ⟨hacyc⟩
  obtain ⟨s, hs, hmin⟩ := (Finite.wellFounded_of_trans_of_irrefl (TransGen R)).has_min
    {s | ReflTransGen R s x} ⟨x, .refl⟩
  obtain ⟨t, ht, hmax⟩ := (Finite.wellFounded_of_trans_of_irrefl (flip (TransGen R))).has_min
    {t | ReflTransGen R y t} ⟨y, .refl⟩
  have hst : TransGen R s t := (TransGen.tail' hs ⟨e, he⟩).trans_left ht
  obtain ⟨p, hp, hpos⟩ :=
    positiveReachable_iff_exists_isPath.1 (positiveReachable_iff_reflTransGen.2 hst.to_reflTransGen)
  refine ⟨s, t, p, hp, fun h ↦ hacyc s (h ▸ hst), hpos, fun w e' ↦ ?_, fun w e' ↦ ?_⟩
  · refine le_antisymm (not_lt.1 fun h ↦ ?_) (hf _ _ e')
    exact hmin w (ReflTransGen.head ⟨e', h⟩ hs) (.single ⟨e', h⟩)
  · refine le_antisymm (not_lt.1 fun h ↦ ?_) (hf _ _ e')
    exact hmax w (ht.tail ⟨e', h⟩) (.single ⟨e', h⟩)

/-! ### Reachability after deleting arrows -/

section ReachableWithout

variable {F G : Set (Σ x y, Q x y)} {s t x : V}

/-- The vertex `t` is *reachable from `s` without the arrows of `F`* when some walk from `s` to `t`
traverses no arrow of `F`: reachability after deleting the arrows of `F`, which are identified in
the total arrow type, so that parallel arrows are deleted separately. -/
def ReachableWithout (F : Set (Σ x y, Q x y)) (s t : V) : Prop :=
  ∃ p : ArrowWalk Q s t, ∀ a ∈ p.arrows, a ∉ F

theorem reachableWithout_def :
    ReachableWithout F s t ↔ ∃ p : ArrowWalk Q s t, ∀ a ∈ p.arrows, a ∉ F :=
  Iff.rfl

/-- Deleting no arrows, reachability is the existence of a walk. -/
@[simp]
theorem reachableWithout_empty_iff :
    ReachableWithout (∅ : Set (Σ x y, Q x y)) s t ↔ Nonempty (ArrowWalk Q s t) := by
  simp [reachableWithout_def]

@[refl, simp]
theorem ReachableWithout.refl (F : Set (Σ x y, Q x y)) (s : V) : ReachableWithout F s s :=
  ⟨ArrowWalk.nil s, by simp⟩

/-- A reachable vertex stays reachable along a further arrow outside `F`. -/
theorem ReachableWithout.tail (h : ReachableWithout F s t) (e : Q t x) (he : ⟨t, x, e⟩ ∉ F) :
    ReachableWithout F s x := by
  obtain ⟨p, hp⟩ := h
  refine ⟨p.cons e, fun a ha ↦ ?_⟩
  rw [ArrowWalk.arrows_cons, List.mem_append, List.mem_singleton] at ha
  rcases ha with ha | rfl
  exacts [hp a ha, he]

@[trans]
theorem ReachableWithout.trans (h : ReachableWithout F s t) (h' : ReachableWithout F t x) :
    ReachableWithout F s x := by
  obtain ⟨p, hp⟩ := h
  obtain ⟨p', hp'⟩ := h'
  refine ⟨p.comp p', fun a ha ↦ ?_⟩
  rw [ArrowWalk.arrows_comp, List.mem_append] at ha
  exact ha.elim (hp a) (hp' a)

/-- Deleting fewer arrows preserves reachability. -/
theorem ReachableWithout.mono (hFG : F ⊆ G) (h : ReachableWithout G s t) :
    ReachableWithout F s t :=
  let ⟨p, hp⟩ := h
  ⟨p, fun a ha haF ↦ hp a ha (hFG haF)⟩

/-- Reachability after deleting arrows is witnessed by a path. -/
theorem reachableWithout_iff_exists_isPath :
    ReachableWithout F s t ↔ ∃ p : ArrowWalk Q s t, p.IsPath ∧ ∀ a ∈ p.arrows, a ∉ F := by
  refine ⟨fun ⟨p, hp⟩ ↦ ?_, fun ⟨p, _, hp⟩ ↦ ⟨p, hp⟩⟩
  obtain ⟨p', hp', hsub⟩ := p.exists_isPath_arrows_subset
  exact ⟨p', hp', fun a ha ↦ hp a (hsub ha)⟩

/-- A vertex set that no arrow outside `F` leaves contains every vertex reachable without the
arrows of `F` from one of its members. -/
theorem ReachableWithout.mem_of_mem {C : Set V} (h : ReachableWithout F s t) (hs : s ∈ C)
    (hC : ∀ ⦃v w : V⦄ (e : Q v w), v ∈ C → ⟨v, w, e⟩ ∉ F → w ∈ C) : t ∈ C := by
  obtain ⟨p, hp⟩ := h
  induction p with
  | nil => exact hs
  | cons p e ih =>
    simp only [ArrowWalk.arrows_cons, List.mem_append, List.mem_singleton] at hp
    exact hC e (ih fun a ha ↦ hp a (.inl ha)) (hp _ (.inr rfl))

end ReachableWithout

end TauCeti
