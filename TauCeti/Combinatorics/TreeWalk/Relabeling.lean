/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.TreeWalk.Canonical
public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Counting the relabelings of a walk

A walk with `r` distinct vertices has exactly `n.descFactorial r` realizations on an `n`-element
vertex set with the same first-visit canonical labeling. In particular, the count is zero when
there are too few available vertices. No closedness or tree assumption is needed.

`canonicalWalkRelabelingEquiv` identifies these realizations with embeddings of the visited
vertices into the new vertex set. This supplies the multiplicity of a fixed walk shape when
summing trace words in the moment method, independently of any probabilistic assumptions.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.1.3, proof of Lemma 2.1.6.
-/

public section

open Finset

namespace TauCeti.TreeWalk

variable {α β : Type*} [DecidableEq α] [DecidableEq β] {k : ℕ}

/-- Restrict a path's codomain to its visited vertices. -/
private def visitedWalk (w : Fin (k + 1) → β) : Fin (k + 1) → ↥(univ.image w) :=
  fun i ↦ ⟨w i, mem_image_of_mem w (mem_univ i)⟩

private theorem visitedWalk_surjective (w : Fin (k + 1) → β) :
    Function.Surjective (visitedWalk w) := by
  rintro ⟨x, hx⟩
  obtain ⟨i, -, rfl⟩ := mem_image.mp hx
  exact ⟨i, rfl⟩

private theorem canonicalWalk_visitedWalk (w : Fin (k + 1) → β) :
    canonicalWalk (visitedWalk w) = canonicalWalk w := by
  exact (canonicalWalk_comp (visitedWalk w) Subtype.val
    (fun _ _ _ _ h ↦ Subtype.ext h)).symm

/-- Injectively assigning new labels to the visited vertices gives a realization of the same
canonical walk. -/
private def relabelWalk (w : Fin (k + 1) → β) (f : ↥(univ.image w) ↪ α) :
    {v : Fin (k + 1) → α // canonicalWalk v = canonicalWalk w} :=
  ⟨f ∘ visitedWalk w, (canonicalWalk_comp (visitedWalk w) f
    (fun _ _ _ _ h ↦ f.injective h)).trans (canonicalWalk_visitedWalk w)⟩

private theorem relabelWalk_bijective (w : Fin (k + 1) → β) :
    Function.Bijective (relabelWalk (α := α) w) := by
  constructor
  · intro f g h
    ext x
    obtain ⟨i, rfl⟩ := visitedWalk_surjective w x
    exact congrFun (congrArg Subtype.val h) i
  · intro v
    -- Choose one occurrence of each visited vertex. Equality of canonical walks guarantees
    -- that its new label is independent of this choice and that distinct vertices stay distinct.
    let r := Function.surjInv (visitedWalk_surjective w)
    have hr (x : ↥(univ.image w)) : visitedWalk w (r x) = x :=
      Function.surjInv_eq (visitedWalk_surjective w) x
    have heq (i j : Fin (k + 1)) : v.val i = v.val j ↔ w i = w j := by
      rw [← canonicalWalk_eq_iff v.val, v.property, canonicalWalk_eq_iff w]
    let f : ↥(univ.image w) ↪ α := ⟨fun x ↦ v.val (r x), by
      intro x y h
      have hxy := (heq (r x) (r y)).mp h
      have hvxy : visitedWalk w (r x) = visitedWalk w (r y) := Subtype.ext hxy
      simpa only [hr] using hvxy⟩
    refine ⟨f, Subtype.ext (funext fun i ↦ ?_)⟩
    exact (heq _ i).mpr (congrArg Subtype.val (hr (visitedWalk w i)))

/-- Realizations of a fixed canonical walk are precisely the injective assignments of labels
to its visited vertices. This does not require the walk to be closed or to traverse a tree. -/
noncomputable def canonicalWalkRelabelingEquiv (w : Fin (k + 1) → β) :
    (↥(univ.image w) ↪ α) ≃ {v : Fin (k + 1) → α // canonicalWalk v = canonicalWalk w} :=
  Equiv.ofBijective (relabelWalk w) (relabelWalk_bijective w)

/-- The relabeling equivalence assigns the chosen new label at each visit. -/
@[simp] theorem canonicalWalkRelabelingEquiv_apply (w : Fin (k + 1) → β)
    (f : ↥(univ.image w) ↪ α) (i : Fin (k + 1)) :
    (canonicalWalkRelabelingEquiv w f).val i = f ⟨w i, mem_image_of_mem w (mem_univ i)⟩ :=
  (rfl)

/-- The inverse equivalence recovers the label of every visited vertex from any occurrence. -/
@[simp] theorem canonicalWalkRelabelingEquiv_symm_apply (w : Fin (k + 1) → β)
    (v : {v : Fin (k + 1) → α // canonicalWalk v = canonicalWalk w}) (i : Fin (k + 1)) :
    (canonicalWalkRelabelingEquiv w).symm v ⟨w i, mem_image_of_mem w (mem_univ i)⟩ = v.val i := by
  have h := congrArg (fun u ↦ u.val i) ((canonicalWalkRelabelingEquiv w).apply_symm_apply v)
  simpa only [canonicalWalkRelabelingEquiv_apply] using h

/-- A canonical walk shape with `r` distinct vertices has `n.descFactorial r` realizations on an
`n`-element vertex set. This includes the zero count when `n < r` and the one-vertex, zero-step
path. -/
theorem card_canonicalWalk_eq [Finite α] (w : Fin (k + 1) → β) :
    Nat.card {v : Fin (k + 1) → α // canonicalWalk v = canonicalWalk w} =
      (Nat.card α).descFactorial #(univ.image w) := by
  classical
  let := Fintype.ofFinite α
  rw [← Nat.card_congr (canonicalWalkRelabelingEquiv (α := α) w), Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card, Fintype.card_embedding_eq, Fintype.card_coe]

end TauCeti.TreeWalk
