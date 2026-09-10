/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Basic
public import Mathlib.Logic.Relation

/-!
# Totality of a reflexive transitive closure as the absence of a closed proper subset

Read `r : α → α → Prop` as the edge relation of a directed graph. Saying that
`Relation.ReflTransGen r` relates every pair of points is the "any two points are joined by a
chain" form of connectedness; saying that every nonempty proper subset of `α` has an edge leaving
it is the "no disconnecting cut" form. `TauCeti.forall_reflTransGen_iff` is the translation
between the two, for an arbitrary relation on an arbitrary type.

## Main results

* `TauCeti.forall_reflTransGen_iff`: totality of `Relation.ReflTransGen r` is exactly the absence
  of a nonempty proper subset with no outgoing edge.
-/

public section

namespace TauCeti

/-- **Totality of a reflexive transitive closure is the absence of a disconnecting cut.** Every
pair of points is joined by an `r`-chain exactly when every nonempty proper subset `s` carries an
edge from a point of `s` to a point outside `s`. -/
theorem forall_reflTransGen_iff {α : Type*} (r : α → α → Prop) :
    (∀ i j, Relation.ReflTransGen r i j) ↔
      ∀ s : Set α, s.Nonempty → s ≠ Set.univ → ∃ i ∈ s, ∃ j ∉ s, r i j := by
  constructor
  · rintro h s ⟨a, ha⟩ hs
    obtain ⟨b, hb⟩ : ∃ b, b ∉ s := by
      by_contra hcon
      exact hs (Set.eq_univ_of_forall fun x ↦ by
        by_contra hx
        exact hcon ⟨x, hx⟩)
    have key : ∀ x y, Relation.ReflTransGen r x y → x ∈ s → y ∉ s → ∃ i ∈ s, ∃ j ∉ s, r i j := by
      intro x y hxy
      induction hxy with
      | refl => exact fun hx hy ↦ absurd hx hy
      | @tail c d _ hcd ih =>
        intro hx hd
        by_cases hc : c ∈ s
        · exact ⟨c, hc, d, hd, hcd⟩
        · exact ih hx hc
    exact key a b (h a b) ha hb
  · intro h i j
    by_contra hij
    have hs : {k | Relation.ReflTransGen r i k} ≠ Set.univ := by
      intro hs
      have hj : j ∈ {k | Relation.ReflTransGen r i k} := by rw [hs]; trivial
      exact hij hj
    obtain ⟨a, ha, b, hb, hab⟩ := h _ ⟨i, Relation.ReflTransGen.refl⟩ hs
    exact hb (Relation.ReflTransGen.tail ha hab)

end TauCeti
