/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Scott.Rank
public import TauCeti.ModelTheory.BackAndForth.Graph
public import Mathlib.Combinatorics.SimpleGraph.Sum
import TauCeti.GroupTheory.Perm.Basic

/-!
# The internal Scott rank of `K₂ ⊔ K₃`

The disjoint union of a complete graph on two vertices and a complete graph on three vertices is
a structure that is not homogeneous: two vertices agree at back-and-forth level one without lying
in one automorphism orbit. Its internal Scott rank is therefore larger than the pure-set value one.

* At level one all vertices are back-and-forth equivalent: every vertex has a neighbour and a
  non-neighbour, so no single round separates them.
* At level two a vertex of `K₂` is separated from a vertex of `K₃`: after a neighbour of the `K₃`
  vertex is chosen, a common neighbour of both exists in `K₃` but not in `K₂`.
* At level two the back-and-forth class of every tuple is its automorphism orbit: equivalence at
  level two preserves the equality pattern and the component of every entry, and a permutation of
  each component realizes any such matching.

Hence every vertex has orbit rank two, every tuple has orbit rank at most two, and the internal
Scott rank is three.

The graph is `completeGraph (Fin 2) ⊕g completeGraph (Fin 3)`, a structure in the language of
graphs through `SimpleGraph.structure`.

## Main results

* `TauCeti.bfEquiv_two_iff_exists_equiv_completeGraph_two_sum_three`: tuples are equivalent at
  level two exactly when an automorphism carries one to the other.
* `TauCeti.orbitRank_completeGraph_two_sum_three`: every vertex has orbit rank two.
* `TauCeti.internalScottRank_completeGraph_two_sum_three`: the internal Scott rank is three.

## References

* Cameron Freer's `cameronfreer/infinitary-logic`, checkpoint
  `9f82bd572af2d79a043c6bc3f1b745f14e0bcaa4`, `scripts/check_orbit_rank_regressions.lean`
  proves the lower bound for this graph, and `graph_internalScottRank` in
  `scripts/check_rank_comparison_regressions.lean` computes an exact internal Scott rank for a
  different graph. Here the upper bound comes from the automorphism description of level two.
-/

public section

universe o

namespace TauCeti

open FirstOrder FirstOrder.Language Fin
open SimpleGraph (completeGraph)

/-- The graph `K₂ ⊔ K₃` on `Fin 2 ⊕ Fin 3`, abbreviated within this file. -/
private abbrev K : SimpleGraph (Fin 2 ⊕ Fin 3) := completeGraph (Fin 2) ⊕g completeGraph (Fin 3)

private local instance : Language.graph.Structure (Fin 2 ⊕ Fin 3) := K.structure

/-- Two vertices of `K₂ ⊔ K₃` are adjacent exactly when they are distinct and lie in the same
component. -/
private theorem adj_iff (x y : Fin 2 ⊕ Fin 3) : K.Adj x y ↔ x ≠ y ∧ x.isLeft = y.isLeft := by
  rcases x with x | x <;> rcases y with y | y <;> simp

private local instance : DecidableRel K.Adj := fun x y => decidable_of_iff _ (adj_iff x y).symm

/-- The finite combinatorics behind the level-two separation: from a vertex `p` of `K₂` move to
its neighbour `p'`; whatever neighbour `y` of a vertex `q` of `K₃` answers, some common neighbour
`z` of `q` and `y` has no matching common neighbour of `p` and `p'`. -/
private theorem separation : ∀ p q : Fin 2 ⊕ Fin 3, p.isLeft → q.isLeft = false →
    ∃ p', K.Adj p p' ∧ ∀ y, K.Adj q y → ∃ z, ∀ x,
      (K.Adj p x ↔ K.Adj q z) → (K.Adj p' x ↔ K.Adj y z) → False := by
  decide

/-- For any two vertices `v` and `w`, every vertex `x` has a counterpart `y` standing to `w` as
`x` stands to `v`: equal, adjacent, or neither. -/
private theorem exists_response : ∀ v w x : Fin 2 ⊕ Fin 3, ∃ y,
    (v = x ↔ w = y) ∧ (K.Adj v x ↔ K.Adj w y) := by
  decide

/-- Level-zero equivalence of two pairs of vertices. -/
private theorem bfEquiv_zero_snoc_iff (v w x y : Fin 2 ⊕ Fin 3) :
    BFEquiv (L := Language.graph) (0 : Ordinal.{o}) 2 (snoc ![v] x) (snoc ![w] y) ↔
      (v = x ↔ w = y) ∧ (K.Adj v x ↔ K.Adj w y) := by
  have hs (v x : Fin 2 ⊕ Fin 3) : snoc ![v] x = ![v, x] := by
    ext i
    fin_cases i <;> rfl
  rw [BFEquiv.zero, SimpleGraph.sameAtomicType_iff, hs, hs]
  revert v w x y
  decide

/-- All vertices of `K₂ ⊔ K₃` are back-and-forth equivalent at level one. -/
private theorem bfEquiv_one (v w : Fin 2 ⊕ Fin 3) :
    BFEquiv (L := Language.graph) (1 : Ordinal.{o}) 1 ![v] ![w] := by
  rw [← zero_add (1 : Ordinal.{o}), BFEquiv.add_one]
  refine ⟨?_, fun x => ?_, fun y => ?_⟩
  · rw [BFEquiv.zero, SimpleGraph.sameAtomicType_iff]
    simp
  · obtain ⟨y, hy⟩ := exists_response v w x
    exact ⟨y, (bfEquiv_zero_snoc_iff v w x y).mpr hy⟩
  · obtain ⟨x, hx⟩ := exists_response w v y
    exact ⟨x, (bfEquiv_zero_snoc_iff v w x y).mpr ⟨hx.1.symm, hx.2.symm⟩⟩

/-- Equivalence at level two keeps every entry of a tuple in the component `K₂`. -/
private theorem isLeft_of_bfEquiv_two {n : ℕ} {a b : Fin n → Fin 2 ⊕ Fin 3}
    (h : BFEquiv (L := Language.graph) (2 : Ordinal.{o}) n a b) (i : Fin n)
    (ha : (a i).isLeft) : (b i).isLeft := by
  by_contra hb
  obtain ⟨p', hp', hsep⟩ := separation (a i) (b i) ha (by simpa using hb)
  -- Forth: the neighbour `p'` of `a i` is answered by some `y`, a neighbour of `b i`.
  rw [show (2 : Ordinal.{o}) = 1 + 1 by norm_num, BFEquiv.add_one] at h
  obtain ⟨y, hy⟩ := h.2.1 p'
  rw [← zero_add (1 : Ordinal.{o}), BFEquiv.add_one] at hy
  have hy₀ := ((SimpleGraph.sameAtomicType_iff K K _ _).mp (BFEquiv.zero.mp hy.1)).2
    (castSucc i) (last n)
  simp only [snoc_castSucc, snoc_last] at hy₀
  -- Back: a common neighbour `z` of `b i` and `y` has no answer.
  obtain ⟨z, hz⟩ := hsep y (hy₀.mp hp')
  obtain ⟨x, hx⟩ := hy.2.2 z
  have hx₀ := ((SimpleGraph.sameAtomicType_iff K K _ _).mp (BFEquiv.zero.mp hx)).2
  have h₁ := hx₀ (castSucc (castSucc i)) (last _)
  have h₂ := hx₀ (castSucc (last n)) (last _)
  simp only [snoc_castSucc, snoc_last] at h₁ h₂
  exact hz x h₁ h₂

/-- Equivalence at level two keeps every entry of a tuple in its component. -/
private theorem isLeft_eq_of_bfEquiv_two {n : ℕ} {a b : Fin n → Fin 2 ⊕ Fin 3}
    (h : BFEquiv (L := Language.graph) (2 : Ordinal.{o}) n a b) (i : Fin n) :
    (a i).isLeft = (b i).isLeft :=
  Bool.eq_iff_iff.mpr ⟨isLeft_of_bfEquiv_two h i, isLeft_of_bfEquiv_two h.symm i⟩

/-- Tuples of `K₂ ⊔ K₃` are back-and-forth equivalent at level two exactly when some
automorphism carries one to the other. -/
theorem bfEquiv_two_iff_exists_equiv_completeGraph_two_sum_three {n : ℕ}
    (a b : Fin n → Fin 2 ⊕ Fin 3) :
    letI := (completeGraph (Fin 2) ⊕g completeGraph (Fin 3)).structure
    BFEquiv (L := Language.graph) (2 : Ordinal.{o}) n a b ↔
      ∃ σ : (Fin 2 ⊕ Fin 3) ≃[Language.graph] (Fin 2 ⊕ Fin 3), σ ∘ a = b := by
  refine ⟨fun h => ?_, fun ⟨σ, hσ⟩ => hσ ▸ σ.bfEquiv _ a⟩
  have hab := (SimpleGraph.sameAtomicType_iff K K a b).mp h.sameAtomicType
  obtain ⟨σ, hσc, hσ⟩ := exists_perm_apply_eq_of_eq_iff Sum.isLeft hab.1
    (isLeft_eq_of_bfEquiv_two h)
  let e : K ≃g K :=
    { toEquiv := σ
      map_rel_iff' := fun {x y} => by
        rw [adj_iff, adj_iff, σ.injective.ne_iff, hσc x, hσc y] }
  exact ⟨e.toLanguageEquiv, funext fun i => (e.toLanguageEquiv_apply (a i)).trans (hσ i)⟩

/-- Every tuple of `K₂ ⊔ K₃` is orbit-stable at level two. -/
private theorem two_mem_orbitStable {n : ℕ} (a : Fin n → Fin 2 ⊕ Fin 3) :
    (2 : Ordinal) ∈ orbitStable (L := Language.graph) a := by
  rw [mem_orbitStable_iff]
  intro b h β
  obtain ⟨σ, rfl⟩ := (bfEquiv_two_iff_exists_equiv_completeGraph_two_sum_three a b).mp h
  exact σ.bfEquiv β a

/-- Every vertex of `K₂ ⊔ K₃` has orbit rank two: all vertices agree at level one, while
level two separates the two components. -/
theorem orbitRank_completeGraph_two_sum_three (v : Fin 2 ⊕ Fin 3) :
    letI := (completeGraph (Fin 2) ⊕g completeGraph (Fin 3)).structure
    orbitRank (L := Language.graph) ![v] = 2 := by
  refine le_antisymm (orbitRank_le _ (two_mem_orbitStable _)) ?_
  rw [← one_add_one_eq_two, Order.add_one_le_iff, lt_iff_not_ge, orbitRank_le_iff,
    mem_orbitStable_iff]
  intro h
  obtain ⟨w, hw⟩ : ∃ w : Fin 2 ⊕ Fin 3, v.isLeft ≠ w.isLeft := by
    rcases v with _ | _
    exacts [⟨.inr 0, by simp⟩, ⟨.inl 0, by simp⟩]
  exact hw (isLeft_eq_of_bfEquiv_two (h ![w] (bfEquiv_one v w) 2) 0)

/-- The internal Scott rank of `K₂ ⊔ K₃` is three. -/
theorem internalScottRank_completeGraph_two_sum_three :
    letI := (completeGraph (Fin 2) ⊕g completeGraph (Fin 3)).structure
    internalScottRank (L := Language.graph) (Fin 2 ⊕ Fin 3) = 3 := by
  rw [show (3 : Ordinal) = 2 + 1 by norm_num]
  exact internalScottRank_eq_add_one_of_mem_orbitStable_of_orbitRank_eq
    (fun _ a => two_mem_orbitStable a)
    (orbitRank_completeGraph_two_sum_three (Sum.inl 0))

end TauCeti
