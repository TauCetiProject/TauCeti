/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Stallings.Fold.Cardinality
public import TauCeti.Combinatorics.Graph.Stallings.Flower

/-!
# Examples of Stallings folds

Three folds of small flowers are computed, covering the cases a fold has to handle: folding two
edges with distinct termini, folding two loops, and folding a loop with an edge that is not a
loop.

* The flower of the words `a b` and `a c`, folded along the two initial `a`-darts, has two
  vertices and three pairs of mutually reverse darts. It is folded as soon as the labels at
  each of its two vertices are distinct.
* The flower of the words `a` and `a`, two loops with the same label, folds to a single loop.
* In the flower of the words `a` and `a b`, folding the loop with the first dart of the other
  petal identifies the interior vertex of that petal with the base vertex. This identification
  of vertices is forced: every morphism of graphs identifying the two darts identifies these
  vertices.

## References

* I. Kapovich and A. Myasnikov, *Stallings foldings and subgroups of free groups*,
  Section 2, Definition 2.4 and Lemma 2.5.
-/

public section

namespace TauCeti.StallingsGraph

variable {α : Type*} (a b c : α × Bool)

/-! ### Two petals with a common first letter -/

/-- Folding the initial darts of the petals `a b` and `a c` leaves two vertices: the base vertex
and the common image of the two interior vertices. -/
theorem card_foldAt_V_flower_fork :
    Nat.card ((flower [[a, b], [a, c]]).foldAt (flowerDart _ ⟨0, by simp⟩ ⟨0, by simp⟩ true)
      (flowerDart _ ⟨1, by simp⟩ ⟨0, by simp⟩ true) rfl rfl).graph.V = 2 := by
  have h := card_foldAt_V_add_one (flower [[a, b], [a, c]])
    (flowerDart _ ⟨0, by simp⟩ ⟨0, by simp⟩ true) (flowerDart _ ⟨1, by simp⟩ ⟨0, by simp⟩ true)
    rfl rfl fun h => by
      simpa using (flowerPos_eq_flowerPos_iff [[a, b], [a, c]] ⟨0, by simp⟩ ⟨1, by simp⟩ 1 1).mp h
  simpa using h

/-- Folding the initial darts of the petals `a b` and `a c` leaves three pairs of mutually
reverse darts. -/
theorem card_foldAt_E_flower_fork :
    Nat.card ((flower [[a, b], [a, c]]).foldAt (flowerDart _ ⟨0, by simp⟩ ⟨0, by simp⟩ true)
      (flowerDart _ ⟨1, by simp⟩ ⟨0, by simp⟩ true) rfl rfl).graph.E = 6 := by
  have h := card_foldAt_E_add_two (flower [[a, b], [a, c]])
    (flowerDart _ ⟨0, by simp⟩ ⟨0, by simp⟩ true) (flowerDart _ ⟨1, by simp⟩ ⟨0, by simp⟩ true)
    (by simp) rfl rfl
  simpa using h

/-- In the fold of the petals `a b` and `a c` along their initial darts, the image of the
interior vertices is not the base vertex: the folded `a`-dart is not a loop. -/
theorem foldHom_mapV_flower_fork_ne_base :
    ((flower [[a, b], [a, c]]).foldHom (flowerDart _ ⟨0, by simp⟩ ⟨0, by simp⟩ true)
      (flowerDart _ ⟨1, by simp⟩ ⟨0, by simp⟩ true) rfl rfl).graphHom.mapV
        (flowerPos [[a, b], [a, c]] ⟨0, by simp⟩ 1) ≠
      ((flower [[a, b], [a, c]]).foldAt (flowerDart _ ⟨0, by simp⟩ ⟨0, by simp⟩ true)
        (flowerDart _ ⟨1, by simp⟩ ⟨0, by simp⟩ true) rfl rfl).base := by
  intro h
  have hb := ((flower [[a, b], [a, c]]).foldHom (flowerDart _ ⟨0, by simp⟩ ⟨0, by simp⟩ true)
    (flowerDart _ ⟨1, by simp⟩ ⟨0, by simp⟩ true) rfl rfl).map_base
  obtain h₁ | ⟨-, h₂⟩ | ⟨-, h₂⟩ := (foldHom_mapV_eq_iff ..).mp (h.trans hb.symm)
  · simpa using (flowerPos_eq_flowerPos_iff [[a, b], [a, c]] ⟨0, by simp⟩ ⟨0, by simp⟩ 1 0).mp h₁
  · simpa using (flowerPos_eq_flowerPos_iff [[a, b], [a, c]] ⟨0, by simp⟩ ⟨1, by simp⟩ 0 1).mp h₂
  · simpa using (flowerPos_eq_flowerPos_iff [[a, b], [a, c]] ⟨0, by simp⟩ ⟨0, by simp⟩ 0 1).mp h₂

/-- Both words `a b` and `a c` have two letters. -/
private theorem fork_length (i : ℕ) (hi : i < [[a, b], [a, c]].length) :
    [[a, b], [a, c]][i].length = 2 := by
  obtain rfl | rfl : i = 0 ∨ i = 1 := by simp at hi; omega
  all_goals rfl

/-- The letters of the words `a b` and `a c`. -/
private theorem fork_getElem (i j : ℕ) (hi : i < [[a, b], [a, c]].length)
    (hj : j < [[a, b], [a, c]][i].length) :
    [[a, b], [a, c]][i][j] = if j = 0 then a else if i = 0 then b else c := by
  have hj' := fork_length a b c i hi ▸ hj
  obtain rfl | rfl : i = 0 ∨ i = 1 := by simp at hi; omega
  all_goals obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
  all_goals rfl

/-- The fold of the petals `a b` and `a c` along their initial darts is folded as soon as `b`
and `c` are distinct and neither is the inverse of `a`: the labels leaving the base vertex are
`a`, `b⁻¹`, `c⁻¹` and those leaving the other vertex are `a⁻¹`, `b`, `c`. In particular this
holds when the underlying generators of `a`, `b` and `c` are pairwise distinct. -/
theorem isFolded_foldAt_flower_fork (hbc : b ≠ c) (hab : b ≠ (a.1, !a.2))
    (hac : c ≠ (a.1, !a.2)) :
    ((flower [[a, b], [a, c]]).foldAt (flowerDart _ ⟨0, by simp⟩ ⟨0, by simp⟩ true)
      (flowerDart _ ⟨1, by simp⟩ ⟨0, by simp⟩ true) rfl rfl).IsFolded := by
  refine (isFolded_foldAt_iff ..).mpr <| forall_flower_E.mpr fun ⟨i, hi⟩ ⟨j, hj⟩ s =>
    forall_flower_E.mpr fun ⟨i', hi'⟩ ⟨j', hj'⟩ s' hV hl => ?_
  replace hV := (foldHom_mapV_eq_iff ..).mp hV
  refine (foldHom_mapE_eq_iff ..).mpr ?_
  have hj₂ : j < 2 := fork_length a b c i hi ▸ hj
  have hj₂' : j' < 2 := fork_length a b c i' hi' ▸ hj'
  -- Express the origins, labels and equalities of darts through petals, positions and letters.
  simp only [flowerDart_eq_iff, flower_rev, flower_label, flower_src, flower_tgt_forward,
    flowerPos_eq_flowerPos_iff, Fin.mk.injEq, Fin.getElem_fin, fork_getElem, fork_length]
    at hV hl ⊢
  obtain ⟨x, t⟩ := a
  obtain ⟨y, u⟩ := b
  obtain ⟨z, v⟩ := c
  simp only [ne_eq, Prod.mk.injEq, not_and, Bool.not_eq_not] at hab hac hbc
  cases s <;> cases s' <;> simp at hl <;> grind

/-! ### Two loops with the same label -/

/-- Folding two loops with the same label leaves the single vertex of their flower. -/
theorem card_foldAt_V_flower_loop_loop :
    Nat.card ((flower [[a], [a]]).foldAt (flowerDart _ ⟨0, by simp⟩ ⟨0, by simp⟩ true)
      (flowerDart _ ⟨1, by simp⟩ ⟨0, by simp⟩ true) rfl rfl).graph.V = 1 := by
  have h := card_foldAt_V_of_tgt_eq (flower [[a], [a]])
    (flowerDart _ ⟨0, by simp⟩ ⟨0, by simp⟩ true) (flowerDart _ ⟨1, by simp⟩ ⟨0, by simp⟩ true)
    rfl rfl rfl
  simpa using h

/-- Folding two loops with the same label leaves a single loop, that is, one pair of mutually
reverse darts. -/
theorem card_foldAt_E_flower_loop_loop :
    Nat.card ((flower [[a], [a]]).foldAt (flowerDart _ ⟨0, by simp⟩ ⟨0, by simp⟩ true)
      (flowerDart _ ⟨1, by simp⟩ ⟨0, by simp⟩ true) rfl rfl).graph.E = 2 := by
  have h := card_foldAt_E_add_two (flower [[a], [a]])
    (flowerDart _ ⟨0, by simp⟩ ⟨0, by simp⟩ true) (flowerDart _ ⟨1, by simp⟩ ⟨0, by simp⟩ true)
    (by simp) rfl rfl
  simpa using h

/-- The single loop obtained by folding two loops with the same label is a folded graph. -/
theorem isFolded_foldAt_flower_loop_loop :
    ((flower [[a], [a]]).foldAt (flowerDart _ ⟨0, by simp⟩ ⟨0, by simp⟩ true)
      (flowerDart _ ⟨1, by simp⟩ ⟨0, by simp⟩ true) rfl rfl).IsFolded := by
  have hlen (i : ℕ) (hi : i < [[a], [a]].length) : [[a], [a]][i] = [a] := by
    obtain rfl | rfl : i = 0 ∨ i = 1 := by simp at hi; omega
    all_goals rfl
  refine (isFolded_foldAt_iff ..).mpr <| forall_flower_E.mpr fun ⟨i, hi⟩ ⟨j, hj⟩ s =>
    forall_flower_E.mpr fun ⟨i', hi'⟩ ⟨j', hj'⟩ s' _ hl => ?_
  refine (foldHom_mapE_eq_iff ..).mpr ?_
  have hi₂ : i < 2 := by simpa using hi
  have hi₂' : i' < 2 := by simpa using hi'
  have hj₁ : j < 1 := by simpa [hlen] using hj
  have hj₁' : j' < 1 := by simpa [hlen] using hj'
  -- Express the labels and equalities of darts through petals, positions and letters.
  simp only [flowerDart_eq_iff, flower_rev, flower_label, Fin.mk.injEq, Fin.getElem_fin, hlen,
    List.getElem_singleton] at hl ⊢
  obtain ⟨x, t⟩ := a
  cases s <;> cases s' <;> simp at hl <;> grind

/-! ### A loop and an edge that is not a loop -/

/-- Folding the loop `a` with the first dart of the petal `a b` identifies the interior vertex
of that petal with the base vertex: a single vertex remains. -/
theorem card_foldAt_V_flower_loop_petal :
    Nat.card ((flower [[a], [a, b]]).foldAt (flowerDart _ ⟨0, by simp⟩ ⟨0, by simp⟩ true)
      (flowerDart _ ⟨1, by simp⟩ ⟨0, by simp⟩ true) rfl rfl).graph.V = 1 := by
  have h := card_foldAt_V_add_one (flower [[a], [a, b]])
    (flowerDart _ ⟨0, by simp⟩ ⟨0, by simp⟩ true) (flowerDart _ ⟨1, by simp⟩ ⟨0, by simp⟩ true)
    rfl rfl fun h => by
      simpa using (flowerPos_eq_flowerPos_iff [[a], [a, b]] ⟨0, by simp⟩ ⟨1, by simp⟩ 1 1).mp h
  simpa using h

/-- Folding the loop `a` with the first dart of the petal `a b` leaves two pairs of mutually
reverse darts, all of them loops at the single remaining vertex. -/
theorem card_foldAt_E_flower_loop_petal :
    Nat.card ((flower [[a], [a, b]]).foldAt (flowerDart _ ⟨0, by simp⟩ ⟨0, by simp⟩ true)
      (flowerDart _ ⟨1, by simp⟩ ⟨0, by simp⟩ true) rfl rfl).graph.E = 4 := by
  have h := card_foldAt_E_add_two (flower [[a], [a, b]])
    (flowerDart _ ⟨0, by simp⟩ ⟨0, by simp⟩ true) (flowerDart _ ⟨1, by simp⟩ ⟨0, by simp⟩ true)
    (by simp) rfl rfl
  simpa using h

/-- Identifying the loop `a` with the first dart of the petal `a b` forces the identification
of their termini: every morphism of graphs that identifies the two darts sends the interior
vertex of the petal to the image of the base vertex, although the two vertices are distinct.
So no morphism from the flower identifies the two darts while keeping these two vertices
distinct. -/
theorem mapV_eq_of_mapE_eq_flower_loop_petal {Δ : SerreGraph}
    (g : (flower [[a], [a, b]]).graph.Hom Δ)
    (h : g.mapE (flowerDart _ ⟨0, by simp⟩ ⟨0, by simp⟩ true) =
      g.mapE (flowerDart _ ⟨1, by simp⟩ ⟨0, by simp⟩ true)) :
    g.mapV (flowerPos [[a], [a, b]] ⟨1, by simp⟩ 1) = g.mapV (flower [[a], [a, b]]).base := by
  have ht := congrArg Δ.tgt h
  simp only [SerreGraph.Hom.map_tgt, flower_tgt_forward, zero_add] at ht
  rw [← ht, flower_base]
  exact congrArg g.mapV ((flowerPos_eq_none_iff _ _ _).mpr (by simp))

/-- The interior vertex of the petal `a b` is not the base vertex of the flower. -/
theorem flowerPos_flower_loop_petal_ne_base :
    flowerPos [[a], [a, b]] ⟨1, by simp⟩ 1 ≠ (flower [[a], [a, b]]).base :=
  fun h => by simpa using (flowerPos_eq_none_iff [[a], [a, b]] ⟨1, by simp⟩ 1).mp h

end TauCeti.StallingsGraph
