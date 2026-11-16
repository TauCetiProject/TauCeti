/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import TauCeti.GroupTheory.Coxeter.Bipartite

import TauCeti.Algebra.BigOperators.Group.List
import TauCeti.Combinatorics.SimpleGraph.Acyclic
import TauCeti.Data.List.OneDegenerateOrder
import TauCeti.GroupTheory.Coxeter.Basic

/-!
# Conjugacy of Coxeter elements on a forest

Let `cs` be a Coxeter system with Coxeter matrix `M`. A *Coxeter element* is a product of all the
simple reflections, each exactly once, in some order. Different orders usually give different
elements, but two moves on the word preserve the conjugacy class of the product:

* moving the first letter to the end conjugates the product by that simple reflection, and more
  generally rotating a word `l₁ ++ l₂` to `l₂ ++ l₁` conjugates the product
  (`CoxeterSystem.isConj_wordProd_append_comm`);
* exchanging two adjacent letters that are not joined in the Coxeter graph does not change the
  product, since the corresponding simple reflections commute.

When the Coxeter graph is a forest, as it is for every finite Weyl group, these two moves connect
any two orderings of the simple reflections (`List.eq_of_isOneDegenerateOrder`): peeling off letters
joined to at most one remaining letter lists the letters in a one-degenerate order, in which each
letter is joined to at most one earlier letter (`List.exists_perm_isOneDegenerateOrder`). Hence
**all Coxeter elements of a Coxeter system whose Coxeter graph is a forest are conjugate**
(`CoxeterSystem.isConj_wordProd_of_perm`), and each of them is conjugate to the bipartite Coxeter
element of any two-colouring of the Coxeter graph
(`CoxeterSystem.isConj_wordProd_bipartiteCoxeterElement`). So the order of a Coxeter element and its
eigenvalues in any linear representation depend only on the Coxeter system. The statement only uses
the graph induced on the letters of the word, so it also applies to the products of the simple
reflections of any subset of the indices on which the Coxeter graph is a forest.

The hypothesis on the graph cannot simply be dropped: for the affine Coxeter system of type
`Ã₂`, whose Coxeter graph is a triangle, the Coxeter elements `s₁ s₂ s₃` and `s₁ s₃ s₂` are not
conjugate.

## Main results

* `CoxeterSystem.isConj_wordProd_of_perm`: if the Coxeter graph induced on the letters of a word
  without repeated letters is a forest, every rearrangement of the word spells a conjugate element.
* `CoxeterSystem.isConj_wordProd_bipartiteCoxeterElement`: on a forest, every Coxeter element is
  conjugate to the bipartite Coxeter element.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. V, §6, no. 1, Lemma 1.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge University Press (1990),
  § 3.16.
-/

public section

namespace CoxeterSystem

variable {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

/-- **Coxeter elements on a forest are conjugate.** If the Coxeter graph induces a forest on the
letters of a word with no repeated letter, then every rearrangement of the word spells an element
conjugate to the one it spells. In particular, when the Coxeter graph is a forest, all Coxeter
elements, the products of all the simple reflections each taken once, are conjugate. -/
theorem isConj_wordProd_of_perm {l l' : List B} (hl : l.Nodup)
    (hM : (M.graph.induce {i | i ∈ l}).IsAcyclic) (h : l.Perm l') :
    IsConj (cs.wordProd l) (cs.wordProd l') := by
  obtain ⟨S, hS, hel⟩ := List.exists_perm_isOneDegenerateOrder hl hM
  rw [← ConjClasses.mk_eq_mk_iff_isConj]
  refine List.eq_of_isOneDegenerateOrder (fun _ _ h ↦ h.symm) (hS.nodup_iff.mpr hl) hel
    (fun l ↦ ConjClasses.mk (cs.wordProd l)) (fun l l' _ hce ↦ ?_)
    (fun a t _ ↦ ConjClasses.mk_eq_mk_iff_isConj.mpr (cs.isConj_wordProd_append_comm [a] t))
    hS.symm (h.symm.trans hS.symm)
  obtain ⟨hp, hce⟩ := List.commEquiv_iff.mp hce
  exact congrArg ConjClasses.mk (List.prod_map_eq_of_perm _ hp fun x y hxy hyx ↦
    cs.commute_simple_of_not_adj (hce x y hxy hyx))

/-- **On a forest, every Coxeter element is conjugate to the bipartite Coxeter element.** If the
Coxeter graph is a forest, the product of all the simple reflections, each exactly once and in any
order, is conjugate to the bipartite Coxeter element of any two-colouring of the Coxeter graph. -/
theorem isConj_wordProd_bipartiteCoxeterElement [Fintype B] (hM : M.graph.IsAcyclic)
    (c : M.graph.Coloring Bool) {l : List B} (hl : l.Nodup) (hl' : ∀ i, i ∈ l) :
    IsConj (cs.wordProd l) (cs.bipartiteCoxeterElement c) := by
  obtain ⟨l₁, l₂, -, -, hnd, hmem, heq⟩ := cs.exists_wordProd_eq_bipartiteCoxeterElement c
  rw [← heq]
  exact cs.isConj_wordProd_of_perm hl (hM.induce _)
    ((List.perm_ext_iff_of_nodup hl hnd).mpr fun i ↦ iff_of_true (hl' i) (hmem i))

end CoxeterSystem
