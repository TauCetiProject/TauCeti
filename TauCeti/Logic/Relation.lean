/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Basic
public import Mathlib.Logic.Relation

/-!
# Closures of relations: totality and local agreement

Read `r : α → α → Prop` as the edge relation of a directed graph. Saying that
`Relation.ReflTransGen r` relates every pair of points is the "any two points are joined by a
chain" form of connectedness; saying that every nonempty proper subset of `α` has an edge leaving
it is the "no disconnecting cut" form. `Relation.forall_reflTransGen_iff` is the translation
between the two, for an arbitrary relation on an arbitrary type; it is the all-points form of
`Relation.forall_reflTransGen_left_iff`, which says the same about the chains starting at one
point.

The class of a point under the equivalence relation `Relation.EqvGen r` only depends on the edges
of `r` at the points of that class: two relations with the same edges, in either direction, at
every point of the class generate the same class (`Relation.eqvGen_iff_of_forall_symmGen_iff`).

## Main results

* `Relation.forall_reflTransGen_left_iff`: every point is reachable from `i` exactly when every
  proper subset containing `i` has an outgoing edge.
* `Relation.forall_reflTransGen_iff`: totality of `Relation.ReflTransGen r` is exactly the absence
  of a nonempty proper subset with no outgoing edge.
* `Relation.eqvGen_iff_of_forall_symmGen_iff`: relations agreeing at every point of an
  equivalence class of one of them generate the same class.
-/

public section

namespace Relation

/-- **Reachability from a point is the absence of a cut around it.** Every point is reached from
`i` by an `r`-chain exactly when every proper subset `s` containing `i` carries an edge from a
point of `s` to a point outside `s`. -/
theorem forall_reflTransGen_left_iff {α : Type*} (r : α → α → Prop) (i : α) :
    (∀ j, ReflTransGen r i j) ↔
      ∀ s : Set α, i ∈ s → s ≠ Set.univ → ∃ a ∈ s, ∃ b ∉ s, r a b := by
  refine ⟨fun h s hi hs ↦ ?_, fun h j ↦ ?_⟩
  · obtain ⟨b, hb⟩ := (Set.ne_univ_iff_exists_notMem s).1 hs
    by_contra hcut
    -- With no edge leaving `s`, every point reachable from `i ∈ s` stays in `s`.
    have hmem : ∀ c, ReflTransGen r i c → c ∈ s := fun c hc ↦ by
      induction hc with
      | refl => exact hi
      | tail _ hcd ih => by_contra hd; exact hcut ⟨_, ih, _, hd, hcd⟩
    exact hb (hmem b (h b))
  · by_contra hij
    obtain ⟨a, ha, b, hb, hab⟩ := h {k | ReflTransGen r i k} .refl
      ((Set.ne_univ_iff_exists_notMem _).2 ⟨j, hij⟩)
    exact hb (ha.tail hab)

/-- **Totality of a reflexive transitive closure is the absence of a disconnecting cut.** Every
pair of points is joined by an `r`-chain exactly when every nonempty proper subset `s` carries an
edge from a point of `s` to a point outside `s`. This is `Relation.forall_reflTransGen_left_iff`
at every starting point. -/
theorem forall_reflTransGen_iff {α : Type*} (r : α → α → Prop) :
    (∀ i j, ReflTransGen r i j) ↔
      ∀ s : Set α, s.Nonempty → s ≠ Set.univ → ∃ i ∈ s, ∃ j ∉ s, r i j :=
  ⟨fun h s ⟨i, hi⟩ ↦ (forall_reflTransGen_left_iff r i).1 (h i) s hi,
    fun h i ↦ (forall_reflTransGen_left_iff r i).2 fun s hi ↦ h s ⟨i, hi⟩⟩

/-- **Equivalence classes only depend on the edges at their points.** If `r` and `r'` have the same
edges, in either direction, at every point of the `Relation.EqvGen r`-class of `x`, then the two
relations generate the same class of `x`. -/
theorem eqvGen_iff_of_forall_symmGen_iff {α : Type*} {r r' : α → α → Prop} {x : α}
    (h : ∀ y, EqvGen r x y → ∀ z, SymmGen r y z ↔ SymmGen r' y z) {y : α} :
    EqvGen r x y ↔ EqvGen r' x y := by
  simp only [← reflTransGen_symmGen] at h ⊢
  refine ⟨fun hy => ?_, fun hy => ?_⟩
  · induction hy with
    | refl => exact .refl
    | tail hab hbc ih => exact ih.tail ((h _ hab _).1 hbc)
  · induction hy with
    | refl => exact .refl
    | tail _ hbc ih => exact ih.tail ((h _ ih _).2 hbc)

end Relation
