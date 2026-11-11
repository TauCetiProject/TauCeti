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
centralizes both signed root subgroups at every orthogonal node. The results are stated for
arbitrary parameters in the three factors, so the pinned unit words are special cases.

These are identities in the full-weight spin carrier, not just identities of its induced
permutations of weights. They provide the orthogonal braid moves for Weyl transport of root
subgroups without asserting that Weyl words depend only on their Weyl-group image, or that the
torus normalizer splits. No identification with an independently pinned group is asserted.

## Main results

* `TauCeti.TypeDSpinCarrier.commute_rootSubgroupPoints_mul_mul_rootSubgroupPoints`:
  a three-factor root product centralizes either signed root subgroup at an orthogonal node.
* `TauCeti.TypeDSpinCarrier.commute_rootSubgroupPoints_mul_mul_rootSubgroupPoints_mul_mul`:
  three-factor root products at orthogonal nodes commute.

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

/-- A positive-negative-positive root product at `i`, with arbitrary parameters, centralizes
either signed simple-root subgroup at an orthogonal node over every commutative ring. -/
theorem commute_rootSubgroupPoints_mul_mul_rootSubgroupPoints
    {i : Fin n} {k : Fin n ⊕ Fin n} (hik : CartanMatrix.D n i (Sum.elim id id k) = 0)
    (A : Type u) [CommRing A] (a b c t : Multiplicative A) :
    Commute
      (rootSubgroupPoints n hn (.inl i) A a *
        rootSubgroupPoints n hn (.inr i) A b * rootSubgroupPoints n hn (.inl i) A c)
      (rootSubgroupPoints n hn k A t) := by
  have hik' : i ≠ Sum.elim id id k := by
    intro h
    simp [h] at hik
  cases k with
  | inl j =>
    have ha := commute_rootSubgroupPoints_inl_inl (hn := hn) hik A a t
    have hb := commute_rootSubgroupPoints_inr_inl (hn := hn) hik' A b t
    have hc := commute_rootSubgroupPoints_inl_inl (hn := hn) hik A c t
    exact (ha.mul_left hb).mul_left hc
  | inr j =>
    have ha := commute_rootSubgroupPoints_inl_inr (hn := hn) hik' A a t
    have hb := commute_rootSubgroupPoints_inr_inr (hn := hn) hik A b t
    have hc := commute_rootSubgroupPoints_inl_inr (hn := hn) hik' A c t
    exact (ha.mul_left hb).mul_left hc

/-- Positive-negative-positive root products at orthogonal type-D nodes commute, with arbitrary
parameters. Specializing to pinned rank-one words gives the length-two braid relation. -/
theorem commute_rootSubgroupPoints_mul_mul_rootSubgroupPoints_mul_mul
    {i j : Fin n} (hij : CartanMatrix.D n i j = 0)
    (A : Type u) [CommRing A] (a b c a' b' c' : Multiplicative A) :
    Commute
      (rootSubgroupPoints n hn (.inl i) A a *
        rootSubgroupPoints n hn (.inr i) A b * rootSubgroupPoints n hn (.inl i) A c)
      (rootSubgroupPoints n hn (.inl j) A a' *
        rootSubgroupPoints n hn (.inr j) A b' * rootSubgroupPoints n hn (.inl j) A c') := by
  have ha := commute_rootSubgroupPoints_mul_mul_rootSubgroupPoints
    (hn := hn) (k := .inl j) hij A a b c a'
  have hb := commute_rootSubgroupPoints_mul_mul_rootSubgroupPoints
    (hn := hn) (k := .inr j) hij A a b c b'
  have hc := commute_rootSubgroupPoints_mul_mul_rootSubgroupPoints
    (hn := hn) (k := .inl j) hij A a b c c'
  exact (ha.mul_right hb).mul_right hc

end TauCeti.TypeDSpinCarrier
