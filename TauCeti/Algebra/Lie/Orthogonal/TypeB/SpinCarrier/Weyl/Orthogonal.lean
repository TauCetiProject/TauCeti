/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.ChevalleyRelations

/-!
# Orthogonal rank-one Weyl words in the type-B spin carrier

For orthogonal numbered simple roots, the rank-one word
`xᵢ(u) x₋ᵢ(-u⁻¹) xᵢ(u)` centralizes both signed root subgroups at the other node.
Consequently two such words commute, with independent unit parameters over every commutative
value ring. This is the length-two braid move used when transporting root subgroups along Weyl
words. The statements concern the actual root-subgroup products, not just their images in an
abstract Weyl group, and retain nonreduced rings and characteristic two.

The construction uses the zero-commutator relations of
`TauCeti.TypeBSpinCarrier` and Mathlib's multiplicative closure rules for `Commute`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, §6 (rank-one representatives and relations).
* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2 (Chevalley commutator relations).
-/

public section

namespace TauCeti.TypeBSpinCarrier

universe u

variable {n : ℕ}

local notation "CM" => CartanMatrix.B (n + 1)

/-- A rank-one Weyl word centralizes either signed simple-root subgroup at an orthogonal
node. The parameter of the root subgroup need not be a unit. -/
theorem commute_weylWord_rootSubgroupPoints
    {i : Fin (n + 1)} {j : Fin (n + 1) ⊕ Fin (n + 1)}
    (hij : CM i (j.elim id id) = 0) (A : Type u) [CommRing A]
    (u : Aˣ) (t : Multiplicative A) :
    Commute
      (rootSubgroupPoints n (.inl i) A (Multiplicative.ofAdd (u : A)) *
        rootSubgroupPoints n (.inr i) A (Multiplicative.ofAdd (-(↑u⁻¹ : A))) *
        rootSubgroupPoints n (.inl i) A (Multiplicative.ofAdd (u : A)))
      (rootSubgroupPoints n j A t) := by
  have hne : i ≠ j.elim id id := by
    intro h
    simp [← h, CartanMatrix.B_diag] at hij
  cases j with
  | inl j =>
    exact ((commute_rootSubgroupPoints_inl_inl hij A _ _).mul_left
      (commute_rootSubgroupPoints_inr_inl hne A _ _)).mul_left
        (commute_rootSubgroupPoints_inl_inl hij A _ _)
  | inr j =>
    exact ((commute_rootSubgroupPoints_inl_inr hne A _ _).mul_left
      (commute_rootSubgroupPoints_inr_inr hij A _ _)).mul_left
        (commute_rootSubgroupPoints_inl_inr hne A _ _)

/-- The length-two braid relation for orthogonal rank-one Weyl words of the type-B spin
carrier, allowing independent unit parameters over any commutative ring. -/
theorem commute_weylWord_weylWord {i j : Fin (n + 1)} (hij : CM i j = 0)
    (A : Type u) [CommRing A] (u v : Aˣ) :
    Commute
      (rootSubgroupPoints n (.inl i) A (Multiplicative.ofAdd (u : A)) *
        rootSubgroupPoints n (.inr i) A (Multiplicative.ofAdd (-(↑u⁻¹ : A))) *
        rootSubgroupPoints n (.inl i) A (Multiplicative.ofAdd (u : A)))
      (rootSubgroupPoints n (.inl j) A (Multiplicative.ofAdd (v : A)) *
        rootSubgroupPoints n (.inr j) A (Multiplicative.ofAdd (-(↑v⁻¹ : A))) *
        rootSubgroupPoints n (.inl j) A (Multiplicative.ofAdd (v : A))) :=
  ((commute_weylWord_rootSubgroupPoints hij A u _).mul_right
    (commute_weylWord_rootSubgroupPoints hij A u _)).mul_right
      (commute_weylWord_rootSubgroupPoints hij A u _)

end TauCeti.TypeBSpinCarrier
