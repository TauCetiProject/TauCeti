/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.ChevalleyRelations

/-!
# Orthogonal Weyl words in the type-D spin carrier

For a unit `u`, the pinned rank-one word at node `i` is
`nᵢ(u) = xᵢ(u) x₋ᵢ(-u⁻¹) xᵢ(u)`. At orthogonal Bourbaki nodes, these words commute,
with independent unit parameters, over every commutative value ring. In particular the words
at parameter one satisfy the length-two braid relation. The proof also records that each word
centralizes both signed root subgroups at every orthogonal node.

These are identities in the full-weight spin carrier, not just identities of its induced
permutations of weights. They provide the orthogonal braid moves for Weyl transport of root
subgroups without asserting that Weyl words depend only on their Weyl-group image, or that the
torus normalizer splits. No identification with an independently pinned group is asserted.

## Main results

* `TauCeti.TypeDSpinCarrier.commute_weylWord_rootSubgroupPoints`: a rank-one word centralizes
  either signed root subgroup at an orthogonal node.
* `TauCeti.TypeDSpinCarrier.commute_weylWord_weylWord`: rank-one words at orthogonal nodes commute.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 19 and Chapter 6.
* R. W. Carter, *Simple Groups of Lie Type*, §§5.2 and 6.4.
* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapters 4--6, Plate IV.

The construction uses the zero-commutator relations of
`TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.ChevalleyRelations` and Mathlib's
`Commute.mul_left` and `Commute.mul_right`.
-/

public section

namespace TauCeti.TypeDSpinCarrier

universe u

variable {n : ℕ} {hn : 4 ≤ n}

/-- The pinned rank-one word at `i`, with any unit parameter, centralizes either signed
simple-root subgroup at an orthogonal node. This holds over arbitrary commutative rings. -/
theorem commute_weylWord_rootSubgroupPoints {i : Fin n} {k : Fin n ⊕ Fin n}
    (hik : CartanMatrix.D n i (Sum.elim id id k) = 0)
    (A : Type u) [CommRing A] (u : Aˣ) (t : Multiplicative A) :
    Commute
      (rootSubgroupPoints n hn (.inl i) A (Multiplicative.ofAdd (u : A)) *
        rootSubgroupPoints n hn (.inr i) A (Multiplicative.ofAdd (-((u⁻¹ : Aˣ) : A))) *
        rootSubgroupPoints n hn (.inl i) A (Multiplicative.ofAdd (u : A)))
      (rootSubgroupPoints n hn k A t) := by
  have hik' : i ≠ Sum.elim id id k := by
    intro h
    simp [h] at hik
  cases k with
  | inl j =>
    have he := commute_rootSubgroupPoints_inl_inl (hn := hn) hik A
      (Multiplicative.ofAdd (u : A)) t
    have hf := commute_rootSubgroupPoints_inr_inl (hn := hn) hik' A
      (Multiplicative.ofAdd (-((u⁻¹ : Aˣ) : A))) t
    exact (he.mul_left hf).mul_left he
  | inr j =>
    have he := commute_rootSubgroupPoints_inl_inr (hn := hn) hik' A
      (Multiplicative.ofAdd (u : A)) t
    have hf := commute_rootSubgroupPoints_inr_inr (hn := hn) hik A
      (Multiplicative.ofAdd (-((u⁻¹ : Aˣ) : A))) t
    exact (he.mul_left hf).mul_left he

/-- Pinned rank-one words at orthogonal type-D nodes commute, with independent unit parameters.
At parameter one this is the length-two braid relation in the spin carrier itself. -/
theorem commute_weylWord_weylWord {i j : Fin n} (hij : CartanMatrix.D n i j = 0)
    (A : Type u) [CommRing A] (u v : Aˣ) :
    Commute
      (rootSubgroupPoints n hn (.inl i) A (Multiplicative.ofAdd (u : A)) *
        rootSubgroupPoints n hn (.inr i) A (Multiplicative.ofAdd (-((u⁻¹ : Aˣ) : A))) *
        rootSubgroupPoints n hn (.inl i) A (Multiplicative.ofAdd (u : A)))
      (rootSubgroupPoints n hn (.inl j) A (Multiplicative.ofAdd (v : A)) *
        rootSubgroupPoints n hn (.inr j) A (Multiplicative.ofAdd (-((v⁻¹ : Aˣ) : A))) *
        rootSubgroupPoints n hn (.inl j) A (Multiplicative.ofAdd (v : A))) := by
  have he := commute_weylWord_rootSubgroupPoints (hn := hn) (k := .inl j) hij A u
    (Multiplicative.ofAdd (v : A))
  have hf := commute_weylWord_rootSubgroupPoints (hn := hn) (k := .inr j) hij A u
    (Multiplicative.ofAdd (-((v⁻¹ : Aˣ) : A)))
  exact (he.mul_right hf).mul_right he

end TauCeti.TypeDSpinCarrier
