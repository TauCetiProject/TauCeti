/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.BigOperators
public import TauCeti.Combinatorics.NoncrossingPartition.Reverse
public import TauCeti.Probability.FreeProbability.Cumulant.Basic

/-!
# Free cumulants of adjoints

Let `A` be a monoid with an involution `star` that reverses products, such as a `*`-algebra, and
let `φ : A → R` be a functional into a commutative ring with involution that commutes with the
involutions, `φ (star x) = star (φ x)`. For `R = ℂ` this says that `φ` is hermitian; every
positive linear functional on a unital `*`-algebra over `ℂ` is hermitian, in particular every state
of a `*`-probability space or of a C⋆-probability space.

Taking adjoints reverses words: `star (a₁ * ⋯ * aₙ) = star aₙ * ⋯ * star a₁`. Passing from a word
`a₁, …, aₙ` to the word of adjoints in reversed order `star aₙ, …, star a₁`, that is from `a` to
`star (a ∘ Fin.rev)`, therefore conjugates each block moment `φ_π` and moves the partition `π`
along the reversal `NoncrossingPartition.reverse n` of `NC(n)`. Since reversal is an
automorphism of `NC(n)`, Möbius inversion turns this into the same statement for the free
cumulants:

`κ_n(star aₙ, …, star a₁) = star κ_n(a₁, …, aₙ)`.

In particular, the free cumulants `κ_n(a, …, a)` of a self-adjoint element `a` are self-adjoint,
that is, real when `R = ℂ`.

## Main results

* `TauCeti.partitionMoment_star_comp_rev` and `TauCeti.partitionCumulant_star_comp_rev` — taking
  adjoints in reversed order conjugates the block moments and the cumulants and reverses the
  partition.
* `TauCeti.freeCumulant_star_comp_rev` — `κ_n(star aₙ, …, star a₁) = star κ_n(a₁, …, aₙ)`.
* `TauCeti.isSelfAdjoint_freeCumulant` and `TauCeti.isSelfAdjoint_freeCumulant_const` — the free
  cumulant of a word equal to its reversed adjoint, in particular of a constant word with a
  self-adjoint letter, is self-adjoint.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lectures 1 and 11.
-/

public section

open Finset

namespace TauCeti

variable {R A : Type*} [Monoid A] [StarMul A] {n : ℕ}

section Moment

variable [CommMonoid R] [StarMul R] {φ : A → R}

/-- If `φ` commutes with the involutions, passing from a word `a₁, …, aₙ` to the reversed word
of adjoints `star aₙ, …, star a₁` conjugates the block moment of a noncrossing partition `π` and
replaces `π` by its reversal. -/
theorem partitionMoment_star_comp_rev (hφ : ∀ x, φ (star x) = star (φ x)) (a : Fin n → A)
    (π : NoncrossingPartition (univ : Finset (Fin n))) :
    partitionMoment φ (star (a ∘ Fin.rev)) (NoncrossingPartition.reverse n π).1 =
      star (partitionMoment φ a π.1) := by
  rw [partitionMoment_def, partitionMoment_def, NoncrossingPartition.prod_parts_reverse,
    star_prod]
  refine prod_congr rfl fun B _ => ?_
  -- `star` is a monoid hom into the opposite monoid, so it reverses products.
  have hstar := unop_map_list_prod (starMulEquiv : A ≃* Aᵐᵒᵖ) (B.sort.map a)
  simp only [starMulEquiv_apply, MulOpposite.unop_op] at hstar
  -- Along the reversed part, the letters are the adjoints of those along `B` in reversed order.
  rw [← hφ, sort_map_revPerm, hstar]
  simp [List.map_reverse, Function.comp_def]

end Moment

section Cumulant

variable [CommRing R] [StarRing R] {φ : A → R}

/-- If `φ` commutes with the involutions, passing from a word `a₁, …, aₙ` to the reversed word
of adjoints `star aₙ, …, star a₁` conjugates the free cumulant of a noncrossing partition `π` and
replaces `π` by its reversal. -/
theorem partitionCumulant_star_comp_rev (hφ : ∀ x, φ (star x) = star (φ x)) (a : Fin n → A)
    (π : NoncrossingPartition (univ : Finset (Fin n))) :
    partitionCumulant φ (star (a ∘ Fin.rev)) (NoncrossingPartition.reverse n π) =
      star (partitionCumulant φ a π) := by
  -- The conjugated cumulants of the reversed partitions satisfy the moment–cumulant formula for
  -- the reversed word of adjoints, so they are its cumulants.
  have h := eq_partitionCumulant_of_forall_sum_Iic φ (star (a ∘ Fin.rev))
    (fun σ => star (partitionCumulant φ a (NoncrossingPartition.reverse n σ))) fun τ => by
      rw [← NoncrossingPartition.reverse_reverse τ, partitionMoment_star_comp_rev hφ,
        ← sum_Iic_partitionCumulant, star_sum]
      exact sum_equiv (NoncrossingPartition.reverse n).toEquiv (fun σ => by simp) fun σ _ => by
        simp
  rw [← h]
  simp

/-- **Free cumulants of adjoints.** If `φ` commutes with the involutions, the free cumulant of
the reversed word of adjoints is the conjugate of the free cumulant,
`κ_n(star aₙ, …, star a₁) = star κ_n(a₁, …, aₙ)`. -/
theorem freeCumulant_star_comp_rev (hφ : ∀ x, φ (star x) = star (φ x)) (a : Fin n → A) :
    freeCumulant φ (star (a ∘ Fin.rev)) univ = star (freeCumulant φ a univ) := by
  rw [freeCumulant_def, freeCumulant_def, ← partitionCumulant_star_comp_rev hφ, OrderIso.map_top]

/-- If `φ` commutes with the involutions, the free cumulant of a word that equals its reversed
word of adjoints, `star (a ∘ Fin.rev) = a`, is self-adjoint. -/
theorem isSelfAdjoint_freeCumulant (hφ : ∀ x, φ (star x) = star (φ x)) {a : Fin n → A}
    (ha : star (a ∘ Fin.rev) = a) : IsSelfAdjoint (freeCumulant φ a univ) := by
  rw [IsSelfAdjoint, ← freeCumulant_star_comp_rev hφ, ha]

/-- If `φ` commutes with the involutions, the free cumulants `κ_n(x, …, x)` of a self-adjoint
element `x` are self-adjoint. -/
theorem isSelfAdjoint_freeCumulant_const (hφ : ∀ x, φ (star x) = star (φ x)) {x : A}
    (hx : IsSelfAdjoint x) : IsSelfAdjoint (freeCumulant φ (fun _ : Fin n => x) univ) :=
  isSelfAdjoint_freeCumulant hφ (funext fun _ => hx.star_eq)

end Cumulant

end TauCeti
