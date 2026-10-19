/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Quiver.Path.Vertices
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
bounds the value a path or cycle places on a single arrow in flow augmentation. The *bottleneck* of
a walk for capacities `c` is the least capacity of an arrow it traverses.

## Main definitions

* `TauCeti.ArrowWalk Q s t`: directed walks from `s` to `t` along the arrow family `Q`.
* `TauCeti.ArrowWalk.arrows`: the arrows traversed by a walk, in order.
* `TauCeti.ArrowWalk.IsPath` and `TauCeti.ArrowWalk.IsCycle`: directed paths and cycles.
* `TauCeti.ArrowWalk.bottleneck`: the least capacity along a walk that traverses an arrow.

## Main results

* `TauCeti.ArrowWalk.map_target_arrows`: the targets of the traversed arrows are the vertices of
  the walk after its first.
* `TauCeti.ArrowWalk.IsPath.nodup_arrows` and `TauCeti.ArrowWalk.IsCycle.nodup_arrows`: paths and
  cycles traverse every arrow at most once.
* `TauCeti.ArrowWalk.le_bottleneck_iff` and `TauCeti.ArrowWalk.exists_mem_bottleneck_eq`: the
  bottleneck is the minimum of the capacities along the walk.
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
  simp [bottleneck, List.le_min_iff]

theorem bottleneck_le {a : Σ x y, Q x y} (ha : a ∈ p.arrows) : p.bottleneck c hne ≤ c a.2.2 :=
  le_bottleneck_iff.1 le_rfl a ha

/-- The bottleneck is attained on an arrow traversed by the walk. -/
theorem exists_mem_bottleneck_eq : ∃ a ∈ p.arrows, p.bottleneck c hne = c a.2.2 := by
  simpa [bottleneck, eq_comm] using List.min_mem (l := p.arrows.map fun a ↦ c a.2.2)
    (by simpa using hne)

/-- A value is below the bottleneck exactly when it is below every capacity along the walk. -/
theorem lt_bottleneck_iff {x : K} :
    x < p.bottleneck c hne ↔ ∀ a ∈ p.arrows, x < c a.2.2 := by
  refine ⟨fun h a ha ↦ h.trans_le (bottleneck_le ha), fun h ↦ ?_⟩
  obtain ⟨a, ha, hb⟩ := exists_mem_bottleneck_eq (c := c) (hne := hne)
  exact hb ▸ h a ha

end Bottleneck

end ArrowWalk

end TauCeti
