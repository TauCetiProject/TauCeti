/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
public import Mathlib.Combinatorics.Quiver.Path.Weight
public import Mathlib.Order.Bounds.Basic
public import TauCeti.Combinatorics.Network.Walk

/-!
# Weights of walks and weighted distances

For a weight `w : TauCeti.Assignment Q R` on the arrows of an arrow family `Q`, the weight
`TauCeti.walkWeight w p` of a walk `p` is the sum of the weights of the arrows it traverses, with
repetitions. It abbreviates Mathlib's `Quiver.Path.addWeight` for the quiver whose arrows are `Q`,
in the way `TauCeti.ArrowWalk.length` abbreviates `Quiver.Path.length`.

A walk is *shortest* when it weighs at most as much as every walk with the same ends, and a weight
is *conservative* when every closed walk has nonnegative weight. The distance from `s` to `t` takes
values in `WithTop R` and is a relation, not a function: `TauCeti.IsDist w s t x` says that `x` is
the least element of the set made of `⊤` and the weights of the walks from `s` to `t`. Thus the
distance is `⊤` exactly when there is no walk, it is the weight of a shortest walk when there is
one, and no `x` satisfies the relation when the weights of the walks from `s` to `t` have no least
element, as for a closed walk of negative weight that can be repeated. No infimum is taken, so no
junk value appears in that case.

## Main definitions

* `TauCeti.walkWeight w p`: the weight of the walk `p` for the arrow weight `w`.
* `TauCeti.IsShortest w p`: `p` weighs at most as much as every walk with the ends of `p`.
* `TauCeti.IsConservative w`: every closed walk has nonnegative weight.
* `TauCeti.IsDist w s t x`: `x` is the distance from `s` to `t`.

## Main results

* `TauCeti.walkWeight_eq_sum_arrows`: the weight of a walk is the sum of `w` over the list of
  arrows that it traverses.
* `TauCeti.isDist_top_iff` and `TauCeti.isDist_coe_iff`: the distance is `⊤` exactly when there
  is no walk, and a value `x : R` exactly when some shortest walk has weight `x`.
* `TauCeti.IsDist.unique`: at most one value is the distance.
* `TauCeti.IsDist.le_add`: the triangle inequality.
* `TauCeti.IsShortest.of_comp_left` and `TauCeti.IsShortest.of_comp_right`: the two parts of a
  shortest walk are shortest walks.
* `TauCeti.IsShortest.walkWeight_nonneg`: a closed walk at a vertex of a shortest walk has
  nonnegative weight.
* `TauCeti.exists_isPath_walkWeight_le` and `TauCeti.IsConservative.exists_isPath_walkWeight_le`:
  when the closed walks at the vertices of a walk have nonnegative weight, some path with the
  same ends weighs at most as much as the walk.
-/

public section

namespace TauCeti

variable {V : Type*} {Q : V → V → Type*} {R : Type*}

section AddMonoid

variable [AddMonoid R]

/-- The weight of a walk for the arrow weight `w`: the sum of the weights of the arrows that the
walk traverses, with repetitions. It is Mathlib's `Quiver.Path.addWeight` for the quiver whose
arrows are `Q`. -/
abbrev walkWeight (w : Assignment Q R) {s t : V} (p : ArrowWalk Q s t) : R :=
  @Quiver.Path.addWeight V ⟨Q⟩ R _ (fun {_ _} e ↦ w e) s t p

/-- The walk of length zero has weight zero. This is not a simp lemma, since simp already rewrites
its left-hand side by `Quiver.Path.addWeight_nil`. -/
theorem walkWeight_nil (w : Assignment Q R) (s : V) :
    walkWeight w (ArrowWalk.nil s : ArrowWalk Q s s) = 0 :=
  @Quiver.Path.addWeight_nil V ⟨Q⟩ R _ (fun {_ _} e ↦ w e) s

/-- The weight of `p.cons e` is the weight of `p` plus the weight of `e`. This is not a simp lemma,
since simp already rewrites its left-hand side by `Quiver.Path.addWeight_cons`. -/
theorem walkWeight_cons (w : Assignment Q R) {s t x : V} (p : ArrowWalk Q s t) (e : Q t x) :
    walkWeight w (p.cons e) = walkWeight w p + w e :=
  @Quiver.Path.addWeight_cons V ⟨Q⟩ R _ (fun {_ _} e ↦ w e) s t x p e

/-- The weight of `p.comp q` is the weight of `p` plus the weight of `q`. This is not a simp
lemma, since simp already rewrites its left-hand side by `Quiver.Path.addWeight_comp`. -/
theorem walkWeight_comp (w : Assignment Q R) {s t x : V} (p : ArrowWalk Q s t)
    (q : ArrowWalk Q t x) : walkWeight w (p.comp q) = walkWeight w p + walkWeight w q :=
  @Quiver.Path.addWeight_comp V ⟨Q⟩ R _ (fun {_ _} e ↦ w e) s t x p q

/-- The weight of a walk is the sum of the weights of the arrows that it traverses, in order. -/
theorem walkWeight_eq_sum_arrows (w : Assignment Q R) {s t : V} (p : ArrowWalk Q s t) :
    walkWeight w p = (p.arrows.map fun a ↦ w a.2.2).sum := by
  induction p with
  | nil => simp
  | cons p e ih => simp only [walkWeight_cons, ArrowWalk.arrows_cons, List.map_append,
      List.sum_append, ih, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]

section LE

variable [LE R]

/-- A shortest walk: its weight is at most the weight of every walk with the same ends. -/
def IsShortest (w : Assignment Q R) {s t : V} (p : ArrowWalk Q s t) : Prop :=
  ∀ q : ArrowWalk Q s t, walkWeight w p ≤ walkWeight w q

theorem isShortest_def {w : Assignment Q R} {s t : V} {p : ArrowWalk Q s t} :
    IsShortest w p ↔ ∀ q : ArrowWalk Q s t, walkWeight w p ≤ walkWeight w q :=
  Iff.rfl

/-- A weight is conservative when every closed walk has nonnegative weight. -/
def IsConservative (w : Assignment Q R) : Prop :=
  ∀ ⦃v : V⦄ (c : ArrowWalk Q v v), 0 ≤ walkWeight w c

theorem isConservative_def {w : Assignment Q R} :
    IsConservative w ↔ ∀ ⦃v : V⦄ (c : ArrowWalk Q v v), 0 ≤ walkWeight w c :=
  Iff.rfl

/-- The distance from `s` to `t`, as a relation: `x` is the least element of the set made of `⊤`
and the weights of the walks from `s` to `t`. It is `⊤` when there is no walk, and no `x`
satisfies it when the weights of the walks from `s` to `t` have no least element. -/
def IsDist (w : Assignment Q R) (s t : V) (x : WithTop R) : Prop :=
  IsLeast (insert ⊤ (Set.range fun p : ArrowWalk Q s t ↦ ((walkWeight w p : R) : WithTop R))) x

theorem isDist_def {w : Assignment Q R} {s t : V} {x : WithTop R} :
    IsDist w s t x ↔
      IsLeast (insert ⊤ (Set.range fun p : ArrowWalk Q s t ↦ ((walkWeight w p : R) : WithTop R)))
        x :=
  Iff.rfl

variable {w : Assignment Q R} {s t u : V}

/-- The distance is `⊤` exactly when there is no walk. -/
theorem isDist_top_iff : IsDist w s t ⊤ ↔ IsEmpty (ArrowWalk Q s t) := by
  refine ⟨fun h ↦ ⟨fun p ↦ WithTop.not_top_le_coe _ (h.2 (Set.mem_insert_of_mem _ ⟨p, rfl⟩))⟩,
    fun h ↦ ⟨Set.mem_insert _ _, ?_⟩⟩
  rintro _ (rfl | ⟨p, rfl⟩)
  · exact le_top
  · exact isEmptyElim p

/-- The distance is a value `x : R` exactly when some shortest walk has weight `x`. -/
theorem isDist_coe_iff {x : R} :
    IsDist w s t x ↔ ∃ p : ArrowWalk Q s t, IsShortest w p ∧ walkWeight w p = x := by
  constructor
  · rintro ⟨hx | ⟨p, hp⟩, hle⟩
    · exact absurd hx WithTop.coe_ne_top
    · have hp : walkWeight w p = x := WithTop.coe_injective hp
      refine ⟨p, fun q ↦ ?_, hp⟩
      rw [hp]
      exact WithTop.coe_le_coe.1 (hle (Set.mem_insert_of_mem _ ⟨q, rfl⟩))
  · rintro ⟨p, hp, rfl⟩
    refine ⟨Set.mem_insert_of_mem _ ⟨p, rfl⟩, ?_⟩
    rintro _ (rfl | ⟨q, rfl⟩)
    · exact le_top
    · exact WithTop.coe_le_coe.2 (hp q)

/-- A shortest walk realizes the distance between its ends. -/
theorem IsShortest.isDist {p : ArrowWalk Q s t} (hp : IsShortest w p) :
    IsDist w s t ((walkWeight w p : R) : WithTop R) :=
  isDist_coe_iff.2 ⟨p, hp, rfl⟩

/-- **Triangle inequality** for distances. -/
theorem IsDist.le_add {x y z : WithTop R} (hst : IsDist w s t x) (htu : IsDist w t u y)
    (hsu : IsDist w s u z) : z ≤ x + y := by
  induction x using WithTop.recTopCoe with
  | top => rw [WithTop.top_add]; exact le_top
  | coe a =>
    induction y using WithTop.recTopCoe with
    | top => rw [WithTop.add_top]; exact le_top
    | coe b =>
      obtain ⟨p, -, rfl⟩ := isDist_coe_iff.1 hst
      obtain ⟨q, -, rfl⟩ := isDist_coe_iff.1 htu
      rw [← WithTop.coe_add, ← walkWeight_comp]
      exact hsu.2 (Set.mem_insert_of_mem _ ⟨p.comp q, rfl⟩)

/-- **Optimal substructure**: an initial segment of a shortest walk is a shortest walk. -/
theorem IsShortest.of_comp_left [AddRightReflectLE R] {p : ArrowWalk Q s t}
    {q : ArrowWalk Q t u} (h : IsShortest w (p.comp q)) : IsShortest w p := fun p' ↦
  le_of_add_le_add_right (by simpa only [walkWeight_comp] using h (p'.comp q))

/-- **Optimal substructure**: a final segment of a shortest walk is a shortest walk. -/
theorem IsShortest.of_comp_right [AddLeftReflectLE R] {p : ArrowWalk Q s t}
    {q : ArrowWalk Q t u} (h : IsShortest w (p.comp q)) : IsShortest w q := fun q' ↦
  le_of_add_le_add_left (by simpa only [walkWeight_comp] using h (p.comp q'))

/-- A closed walk at a vertex of a shortest walk has nonnegative weight. -/
theorem IsShortest.walkWeight_nonneg [AddLeftReflectLE R] [AddRightReflectLE R]
    {p : ArrowWalk Q s t} (h : IsShortest w p) {v : V} (hv : v ∈ p.vertices)
    (c : ArrowWalk Q v v) : 0 ≤ walkWeight w c := by
  obtain ⟨p₁, p₂, rfl⟩ := @Quiver.Path.exists_eq_comp_of_mem_vertices V ⟨Q⟩ _ _ p _ hv
  have h' := h (ArrowWalk.comp p₁ (c.comp p₂))
  simp only [walkWeight_comp] at h'
  refine le_of_add_le_add_right (a := walkWeight w p₂) ?_
  rw [zero_add]
  exact le_of_add_le_add_left h'

end LE

/-- At most one value is the distance from `s` to `t`. -/
theorem IsDist.unique [PartialOrder R] {w : Assignment Q R} {s t : V} {x y : WithTop R}
    (hx : IsDist w s t x) (hy : IsDist w s t y) : x = y :=
  IsLeast.unique hx hy

section Preorder

variable [Preorder R] [AddLeftMono R] [AddRightMono R] {s t : V}

/-- If the closed walks at the vertices of a walk have nonnegative weight, then some path with
the ends of the walk weighs at most as much as the walk. -/
theorem exists_isPath_walkWeight_le (w : Assignment Q R) (p : ArrowWalk Q s t)
    (hc : ∀ v ∈ p.vertices, ∀ c : ArrowWalk Q v v, 0 ≤ walkWeight w c) :
    ∃ p' : ArrowWalk Q s t, p'.IsPath ∧ walkWeight w p' ≤ walkWeight w p := by
  induction p with
  | nil => exact ⟨ArrowWalk.nil s, ArrowWalk.isPath_nil s, le_rfl⟩
  | @cons x y p e ih =>
    have hmem : ∀ v, v ∈ ArrowWalk.vertices (Q := Q) p →
        v ∈ ArrowWalk.vertices (Q := Q) (ArrowWalk.cons p e) := fun v hv ↦
      (@Quiver.Path.mem_vertices_cons V ⟨Q⟩ _ _ _ p e v).2 (Or.inl hv)
    obtain ⟨p', hp', hle⟩ := ih fun v hv ↦ hc v (hmem v hv)
    by_cases hy : y ∈ p'.vertices
    · -- `y` already occurs on `p'`: keep the initial segment of `p'` ending at `y`, which drops
      -- a closed walk at `y` of nonnegative weight
      obtain ⟨p₁, p₂, rfl⟩ := @Quiver.Path.exists_eq_comp_of_mem_vertices V ⟨Q⟩ _ _ p' _ hy
      refine ⟨p₁, hp'.of_comp_left, ?_⟩
      have h0 := hc y (@Quiver.Path.end_mem_vertices V ⟨Q⟩ _ _ _) (ArrowWalk.cons p₂ e)
      simp only [walkWeight_comp, walkWeight_cons] at hle h0 ⊢
      calc walkWeight w p₁ ≤ walkWeight w p₁ + (walkWeight w p₂ + w e) :=
            le_add_of_nonneg_right h0
        _ = walkWeight w p₁ + walkWeight w p₂ + w e := (add_assoc _ _ _).symm
        _ ≤ walkWeight w p + w e := add_le_add_left hle _
    · -- `y` is new: extend `p'` by `e`
      refine ⟨ArrowWalk.cons p' e, hp'.cons hy e, ?_⟩
      rw [walkWeight_cons, walkWeight_cons]
      exact add_le_add_left hle (w e)

/-- For a conservative weight, every walk weighs at least as much as some path with the same
ends. -/
theorem IsConservative.exists_isPath_walkWeight_le {w : Assignment Q R} (hw : IsConservative w)
    (p : ArrowWalk Q s t) : ∃ p' : ArrowWalk Q s t, p'.IsPath ∧ walkWeight w p' ≤ walkWeight w p :=
  TauCeti.exists_isPath_walkWeight_le w p fun _ _ c ↦ hw c

end Preorder

end AddMonoid

end TauCeti
