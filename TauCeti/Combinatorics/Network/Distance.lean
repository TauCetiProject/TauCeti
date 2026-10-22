/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Fintype.Card
public import TauCeti.Combinatorics.Network.Walk

/-!
# Distances along arrows of positive capacity

For capacities `c` on an arrow family `Q`, the *positive distance* `positiveEDist c s t` is the
least length of a walk from `s` to `t` that traverses only arrows of positive capacity, and `⊤`
when there is no such walk. For the residual capacities of a flow it is the length of a shortest
augmenting walk, the quantity that controls shortest-path augmentation.
The definition follows Mathlib's `SimpleGraph.edist`, the infimum in `ℕ∞` of the lengths of
walks.

Along every arrow of positive capacity the distance from `s` rises by at most one, and conversely
every function vanishing at `s` with this property is a lower bound for the distance from `s`.
Along a shortest walk the distance rises by exactly one at every arrow, so a shortest walk is a
path, and a finite positive distance is less than the number of vertices.

## Main definitions

* `TauCeti.positiveEDist c s t`: the positive distance from `s` to `t` for the capacities `c`.

## Main results

* `TauCeti.positiveEDist_ne_top_iff`: the positive distance is finite exactly for positively
  reachable vertices, and `TauCeti.PositiveReachable.exists_length_eq_positiveEDist` gives a walk
  attaining it.
* `TauCeti.positiveEDist_le_add_one` and `TauCeti.le_positiveEDist`: the positive distance from
  `s` is the largest function vanishing at `s` that rises by at most one along every arrow of
  positive capacity.
* `TauCeti.positiveEDist_eq_add_one_of_mem_arrows` and `TauCeti.positiveEDist_lt_of_mem_arrows`:
  every arrow of a shortest walk raises the distance by one.
* `TauCeti.ArrowWalk.isPath_of_length_eq_positiveEDist`: a shortest walk is a path.
* `TauCeti.positiveEDist_lt_card`: finite positive distances are less than the number of vertices.
-/

public section

namespace TauCeti

universe u v w

variable {V : Type u} {Q : V → V → Type v} {K : Type w} [Zero K] [LT K]

/-- The *positive distance* from `s` to `t` for the capacities `c`: the least length of a walk from
`s` to `t` that traverses only arrows of positive capacity, or `⊤` if `t` is not positively
reachable from `s`. For residual capacities it is the length of a shortest augmenting walk. -/
noncomputable def positiveEDist (c : Assignment Q K) (s t : V) : ℕ∞ :=
  ⨅ p : {p : ArrowWalk Q s t // ∀ a ∈ p.arrows, 0 < c a.2.2}, (p.1.length : ℕ∞)

variable {c : Assignment Q K} {s t x : V}

theorem positiveEDist_def :
    positiveEDist c s t =
      ⨅ p : {p : ArrowWalk Q s t // ∀ a ∈ p.arrows, 0 < c a.2.2}, (p.1.length : ℕ∞) := by
  rw [positiveEDist]

theorem positiveEDist_le_length (p : ArrowWalk Q s t) (hp : ∀ a ∈ p.arrows, 0 < c a.2.2) :
    positiveEDist c s t ≤ p.length :=
  iInf_le (fun p : {p : ArrowWalk Q s t // ∀ a ∈ p.arrows, 0 < c a.2.2} ↦ (p.1.length : ℕ∞))
    ⟨p, hp⟩

@[simp]
theorem positiveEDist_self (c : Assignment Q K) (s : V) : positiveEDist c s s = 0 :=
  nonpos_iff_eq_zero.1 <| (positiveEDist_le_length (ArrowWalk.nil s) (by simp)).trans_eq (by simp)

theorem positiveEDist_ne_top_iff : positiveEDist c s t ≠ ⊤ ↔ PositiveReachable c s t := by
  rw [positiveEDist, ENat.iInf_natCast_ne_top, positiveReachable_def]
  exact ⟨fun ⟨p⟩ ↦ ⟨p.1, p.2⟩, fun ⟨p, hp⟩ ↦ ⟨⟨p, hp⟩⟩⟩

theorem positiveEDist_eq_top_iff : positiveEDist c s t = ⊤ ↔ ¬PositiveReachable c s t :=
  positiveEDist_ne_top_iff.not_right

/-- A positively reachable vertex is reached by a walk of shortest length along arrows of positive
capacity. -/
theorem PositiveReachable.exists_length_eq_positiveEDist (h : PositiveReachable c s t) :
    ∃ p : ArrowWalk Q s t, (∀ a ∈ p.arrows, 0 < c a.2.2) ∧
      (p.length : ℕ∞) = positiveEDist c s t := by
  obtain ⟨p, hp⟩ := positiveReachable_def.1 h
  have : Nonempty {p : ArrowWalk Q s t // ∀ a ∈ p.arrows, 0 < c a.2.2} := ⟨⟨p, hp⟩⟩
  obtain ⟨p, hp⟩ :=
    ENat.exists_eq_iInf fun p : {p : ArrowWalk Q s t // ∀ a ∈ p.arrows, 0 < c a.2.2} ↦
      (p.1.length : ℕ∞)
  exact ⟨p.1, p.2, hp⟩

@[simp]
theorem positiveEDist_eq_zero_iff : positiveEDist c s t = 0 ↔ s = t := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ positiveEDist_self c s⟩
  obtain ⟨p, -, hlen⟩ :=
    (positiveEDist_ne_top_iff.1 (h ▸ ENat.zero_ne_top)).exists_length_eq_positiveEDist
  exact @Quiver.Path.eq_of_length_zero V ⟨Q⟩ s t p (by exact_mod_cast hlen.trans h)

/-- Following an arrow of positive capacity raises the positive distance by at most one. -/
theorem positiveEDist_le_add_one (e : Q t x) (he : 0 < c e) :
    positiveEDist c s x ≤ positiveEDist c s t + 1 := by
  by_cases h : PositiveReachable c s t
  · obtain ⟨p, hp, hlen⟩ := h.exists_length_eq_positiveEDist
    rw [← hlen]
    refine (positiveEDist_le_length (p.cons e) fun a ha ↦ ?_).trans_eq (by simp)
    rw [ArrowWalk.arrows_cons, List.mem_append, List.mem_singleton] at ha
    rcases ha with ha | rfl
    exacts [hp a ha, he]
  · simp [positiveEDist_eq_top_iff.2 h]

/-- A lower bound for positive distances: a function vanishing at `s` that rises by at most one
along every arrow of positive capacity is at most the positive distance from `s`. -/
theorem le_positiveEDist {φ : V → ℕ∞} (hs : φ s = 0)
    (h : ∀ ⦃u v : V⦄ (e : Q u v), 0 < c e → φ v ≤ φ u + 1) (t : V) :
    φ t ≤ positiveEDist c s t := by
  suffices ∀ p : ArrowWalk Q s t, (∀ a ∈ p.arrows, 0 < c a.2.2) → φ t ≤ p.length from
    le_iInf fun p ↦ this p.1 p.2
  intro p hp
  induction p with
  | nil => simp [hs]
  | cons p e ih =>
    simp only [ArrowWalk.arrows_cons, List.mem_append, List.mem_singleton] at hp
    calc φ _ ≤ φ _ + 1 := h e (hp _ (.inr rfl))
      _ ≤ (ArrowWalk.length p : ℕ∞) + 1 := by gcongr; exact ih fun a ha ↦ hp a (.inl ha)
      _ = ArrowWalk.length (ArrowWalk.cons p e) := by simp [ArrowWalk.length]

/-- The last arrow of a shortest walk along arrows of positive capacity raises the positive
distance by one, and the rest of the walk is again a shortest walk. -/
private theorem length_eq_positiveEDist_of_cons {p : ArrowWalk Q s t} {e : Q t x}
    (hp : ∀ a ∈ (p.cons e).arrows, 0 < c a.2.2)
    (hlen : ((p.cons e).length : ℕ∞) = positiveEDist c s x) :
    (p.length : ℕ∞) = positiveEDist c s t ∧ positiveEDist c s x = positiveEDist c s t + 1 := by
  simp only [ArrowWalk.arrows_cons, List.mem_append, List.mem_singleton] at hp
  have h₁ : positiveEDist c s t ≤ p.length := positiveEDist_le_length p fun a ha ↦ hp a (.inl ha)
  have h₂ : positiveEDist c s x ≤ positiveEDist c s t + 1 :=
    positiveEDist_le_add_one e (hp _ (.inr rfl))
  have hlen : (p.length : ℕ∞) + 1 = positiveEDist c s x := by simpa using hlen
  have h : (p.length : ℕ∞) = positiveEDist c s t :=
    le_antisymm ((ENat.add_le_add_iff_right ENat.one_ne_top).1 (hlen ▸ h₂)) h₁
  exact ⟨h, le_antisymm h₂ (h ▸ hlen.le)⟩

/-- **Shortest walks.** Every arrow of a shortest walk along arrows of positive capacity from `s`
raises the positive distance from `s` by one. -/
theorem positiveEDist_eq_add_one_of_mem_arrows {p : ArrowWalk Q s t}
    (hp : ∀ a ∈ p.arrows, 0 < c a.2.2) (hlen : (p.length : ℕ∞) = positiveEDist c s t)
    {a : Σ x y, Q x y} (ha : a ∈ p.arrows) :
    positiveEDist c s a.2.1 = positiveEDist c s a.1 + 1 := by
  induction p with
  | nil => simp at ha
  | cons p e ih =>
    obtain ⟨hlen', he⟩ := length_eq_positiveEDist_of_cons hp hlen
    simp only [ArrowWalk.arrows_cons, List.mem_append, List.mem_singleton] at hp ha
    rcases ha with ha | rfl
    exacts [ih (fun a ha ↦ hp a (.inl ha)) hlen' ha, he]

/-- The positive distance from `s` strictly increases along every arrow of a shortest walk along
arrows of positive capacity from `s`. -/
theorem positiveEDist_lt_of_mem_arrows {p : ArrowWalk Q s t}
    (hp : ∀ a ∈ p.arrows, 0 < c a.2.2) (hlen : (p.length : ℕ∞) = positiveEDist c s t)
    {a : Σ x y, Q x y} (ha : a ∈ p.arrows) :
    positiveEDist c s a.1 < positiveEDist c s a.2.1 := by
  have h := positiveEDist_eq_add_one_of_mem_arrows hp hlen ha
  have htop : positiveEDist c s a.2.1 ≠ ⊤ :=
    positiveEDist_ne_top_iff.2 (positiveReachable_of_mem_arrows hp ha)
  rw [h] at htop ⊢
  exact (ENat.lt_add_one_iff fun h ↦ htop (by simp [h])).2 le_rfl

/-- The `i`-th vertex of a shortest walk along arrows of positive capacity from `s` is at positive
distance `i` from `s`. -/
private theorem map_positiveEDist_vertices {p : ArrowWalk Q s t}
    (hp : ∀ a ∈ p.arrows, 0 < c a.2.2) (hlen : (p.length : ℕ∞) = positiveEDist c s t) :
    p.vertices.map (positiveEDist c s) = (List.range (p.length + 1)).map ((↑) : ℕ → ℕ∞) := by
  induction p with
  | nil => simp [ArrowWalk.vertices, ArrowWalk.length]
  | cons p e ih =>
    obtain ⟨hlen', -⟩ := length_eq_positiveEDist_of_cons hp hlen
    simp only [ArrowWalk.arrows_cons, List.mem_append] at hp
    have ih := ih (fun a ha ↦ hp a (.inl ha)) hlen'
    simp only [ArrowWalk.vertices, ArrowWalk.length, Quiver.Path.vertices_cons,
      Quiver.Path.length_cons, List.concat_eq_append, List.map_append,
      List.map_singleton] at ih hlen ⊢
    rw [ih, List.range_succ (n := ArrowWalk.length p + 1), List.map_append, List.map_singleton,
      hlen]

/-- A shortest walk along arrows of positive capacity is a path. -/
theorem ArrowWalk.isPath_of_length_eq_positiveEDist {p : ArrowWalk Q s t}
    (hp : ∀ a ∈ p.arrows, 0 < c a.2.2) (hlen : (p.length : ℕ∞) = positiveEDist c s t) :
    p.IsPath :=
  (ArrowWalk.isPath_def p).2 <| List.Nodup.of_map (positiveEDist c s) <|
    map_positiveEDist_vertices hp hlen ▸ List.nodup_range.map Nat.cast_injective

/-- A positively reachable vertex is at positive distance less than the number of vertices. -/
theorem positiveEDist_lt_card [Fintype V] (h : PositiveReachable c s t) :
    positiveEDist c s t < Fintype.card V := by
  obtain ⟨p, hp, hpos⟩ := positiveReachable_iff_exists_isPath.1 h
  have hcard : p.vertices.length ≤ Fintype.card V :=
    ((ArrowWalk.isPath_def p).1 hp).length_le_card
  have hlen : p.vertices.length = p.length + 1 := @Quiver.Path.vertices_length V ⟨Q⟩ _ _ p
  exact (positiveEDist_le_length p hpos).trans_lt (by norm_cast; omega)

end TauCeti
