/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Square roots in a group

The **square roots** of an element `x` of a magma `M` are the `g` with `g * g = x`. A
multiplicative equivalence `e : M ≃* N` carries them bijectively onto the square roots of `e x`
(`MulEquiv.squareRootMap`). Applied to conjugation in a group, this shows that the number of
square roots depends only on the conjugacy class of `x` (`TauCeti.card_squareRoot_conj`). That is
what makes the square-root count a class function, and hence expandable in the basis of
irreducible characters. In a group of odd order squaring is a bijection
(`Nat.Coprime.pow_left_bijective`), so every element has exactly one square root
(`TauCeti.card_squareRoot_of_odd_card`).

## Main statements

* `MulEquiv.squareRootMap`: a multiplicative equivalence `e` is a bijection between the square
  roots of `x` and those of `e x`.
* `TauCeti.card_squareRoot_conj`: conjugate elements of a group have equally many square roots.
* `TauCeti.mul_self_eq_one_iff_of_odd_card` and `TauCeti.card_squareRoot_of_odd_card`: in a group
  of odd order, `g * g = 1` only for `g = 1`, and every element has exactly one square root.

## Implementation notes

`Nat.card` is used for the count, so no finiteness or decidability assumption is needed to state
the result.  It follows the usual junk-value convention: on a group in which some element has
infinitely many square roots, `Nat.card` returns `0` at that element rather than a cardinal, so the
count below is a genuine number of square roots only when that subtype is finite — as it is for a
finite group.  The statements are unaffected either way, since conjugation is a bijection whether
or not the two sides are finite.
-/

public section

namespace MulEquiv

variable {M N : Type*} [Mul M] [Mul N]

/-- **A multiplicative equivalence permutes square roots**: `e` restricts to a bijection from the
square roots of `x` onto the square roots of `e x`. -/
def squareRootMap (e : M ≃* N) (x : M) :
    {g : M // g * g = x} ≃ {g : N // g * g = e x} :=
  e.toEquiv.subtypeEquiv fun g => by simp [← map_mul]

/-- `MulEquiv.squareRootMap` applies `e` to the underlying element.

The definition is not `@[expose]`d, so this is how it applies outside this file: the generic
`Equiv.subtypeEquiv_apply` cannot fire on the opaque `MulEquiv.squareRootMap`. -/
@[simp]
theorem squareRootMap_apply_coe (e : M ≃* N) (x : M) (g : {g : M // g * g = x}) :
    (e.squareRootMap x g : N) = e g :=
  (rfl)

/-- The inverse of `MulEquiv.squareRootMap` applies `e.symm`; as with
`MulEquiv.squareRootMap_apply_coe`, this is what the opaque definition needs in place of
`Equiv.subtypeEquiv_symm`. -/
@[simp]
theorem squareRootMap_symm_apply_coe (e : M ≃* N) (x : M) (g : {g : N // g * g = e x}) :
    ((e.squareRootMap x).symm g : M) = e.symm g :=
  (rfl)

end MulEquiv

namespace TauCeti

variable {G : Type*} [Group G]

/-- **The number of square roots is a class function of the group element**: `x` and its
conjugate `h * x * h⁻¹` have equally many square roots, since conjugation by `h` is a
multiplicative equivalence (`MulEquiv.squareRootMap`).  The counts are `Nat.card`s, hence both
`0` in the degenerate case of infinitely many square roots. -/
theorem card_squareRoot_conj (x h : G) :
    Nat.card {g : G // g * g = h * x * h⁻¹} = Nat.card {g : G // g * g = x} := by
  rw [← MulAut.conj_apply]
  exact (Nat.card_congr ((MulAut.conj h).squareRootMap x)).symm

/-- In a group of odd order, `g * g = 1` only for `g = 1`: squaring is a bijection, since `2` is
coprime to the order. -/
theorem mul_self_eq_one_iff_of_odd_card (hG : Odd (Nat.card G)) {g : G} :
    g * g = 1 ↔ g = 1 := by
  refine ⟨fun h => hG.coprime_two_right.pow_left_bijective.1 ?_, fun h => by simp [h]⟩
  simp only [pow_two, h, mul_one]

/-- **In a group of odd order every element has exactly one square root**: squaring is a
bijection, since `2` is coprime to the order. -/
theorem card_squareRoot_of_odd_card (hG : Odd (Nat.card G)) (x : G) :
    Nat.card {g : G // g * g = x} = 1 := by
  have hbij := hG.coprime_two_right.pow_left_bijective (G := G)
  obtain ⟨g, hg⟩ := hbij.2 x
  rw [Nat.card_eq_one_iff_unique]
  exact ⟨⟨fun a b => Subtype.ext <| hbij.1 <| by simp only [pow_two, a.2, b.2]⟩,
    ⟨⟨g, by rw [← pow_two]; exact hg⟩⟩⟩

end TauCeti
