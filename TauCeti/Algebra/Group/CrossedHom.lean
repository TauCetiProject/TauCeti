/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.GroupTheory.Commutator.Basic

import Mathlib.Tactic.LinearCombination

/-!
# Crossed homomorphisms twisted by a unit-valued function

Let `H` be a multiplicative type, `R` a semiring and `χ : H → Rˣ` a unit-valued function. A
function `F : H → R` is a **crossed homomorphism** for `χ` when

  `F (x * y) = χ x * F y + F x`

for all `x y : H` (`TauCeti.IsCrossedHom`). When `H` is a group and `χ : H →* Rˣ` is a character,
these are exactly the `1`-cocycles for the action of `H` on `R` through `χ`, written without a
module structure on `R`.

This file develops the elementary calculus for arbitrary unit-valued twists. Over a monoid and
an additively cancellative semiring, crossed homomorphisms vanish at `1`, their values at natural
powers are geometric sums, and they are additive on products where the twist is trivial. Over a
group and a ring, their values at inverses are determined by their values at the original
elements. Only the commutator formula needs a multiplicative character.

Continuous crossed homomorphisms and uniqueness on topological generating sets are treated in
`TauCeti/Topology/Algebra/Group/CrossedHom.lean`. For `R = ℤ_p`, their values on a minimal
generating tuple are what Labute's prescription property of a continuous character prescribes.

## Main definitions

* `TauCeti.IsCrossedHom`: `F : H → R` is a crossed homomorphism for the unit-valued `χ`.

## Main results

* `TauCeti.IsCrossedHom.ringHom_comp`: composing with a semiring homomorphism `φ` gives a crossed
  homomorphism for `Units.map φ ∘ χ`.
* `TauCeti.IsCrossedHom.map_pow`: `F (x ^ k) = (1 + χ x + ⋯ + χ x ^ (k - 1)) * F x`.
* `TauCeti.IsCrossedHom.map_list_prod_of_forall_eq_one`: on a product of elements on which `χ` is
  trivial, `F` is additive.
* `TauCeti.IsCrossedHom.map_commutatorElement`: for a character into a commutative ring,
  `F ⁅x, y⁆ = (χ x - 1) * F y - (χ y - 1) * F x`.

## References

* J.-P. Serre, *Galois Cohomology*, Ch. I, §2.3.
* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132, §2.
-/

public section

namespace TauCeti

section Semiring

variable {H : Type*} [Mul H] {R : Type*} [Semiring R]

/-- A function `F : H → R` is a **crossed homomorphism** for the unit-valued function `χ` when
`F (x * y) = χ x * F y + F x` for all `x y : H`. Here `χ` is any function `H → Rˣ`; when `H` is a
group and `χ : H →* Rˣ` is a character, this is the `1`-cocycle condition for the action of `H` on
`R` through `χ`. -/
def IsCrossedHom (χ : H → Rˣ) (F : H → R) : Prop :=
  ∀ x y, F (x * y) = (χ x : R) * F y + F x

variable {χ : H → Rˣ} {F : H → R}

/-- The defining property of `IsCrossedHom`. -/
theorem isCrossedHom_iff : IsCrossedHom χ F ↔ ∀ x y, F (x * y) = (χ x : R) * F y + F x :=
  Iff.rfl

namespace IsCrossedHom

variable (hF : IsCrossedHom χ F)
include hF

/-- The cocycle identity of a crossed homomorphism. -/
theorem map_mul (x y : H) : F (x * y) = (χ x : R) * F y + F x :=
  hF x y

/-- Precomposing a crossed homomorphism with a multiplicative map gives a crossed homomorphism
for the precomposed unit-valued twist. -/
theorem comp {H' : Type*} [Mul H'] {F'' : Type*} [FunLike F'' H' H] [MulHomClass F'' H' H]
    (φ : F'') {χ' : H' → Rˣ} (hχ' : ∀ x, χ' x = χ (φ x)) :
    IsCrossedHom χ' (F ∘ φ) := fun x y ↦ by
  simpa only [Function.comp_apply, _root_.map_mul, hχ'] using hF.map_mul (φ x) (φ y)

/-- Composing a crossed homomorphism with a semiring homomorphism `φ : R →+* S` gives a crossed
homomorphism for the unit-valued twist `Units.map φ ∘ χ`. -/
theorem ringHom_comp {S : Type*} [Semiring S] (φ : R →+* S) :
    IsCrossedHom (Units.map (φ : R →* S) ∘ χ) (φ ∘ F) := fun x y ↦ by
  simpa only [Function.comp_apply, Units.coe_map, MonoidHom.coe_ofClass, map_add, _root_.map_mul]
    using congrArg φ (hF.map_mul x y)

end IsCrossedHom

end Semiring

section MulOneClass

variable {H : Type*} [MulOneClass H] {R : Type*} [Semiring R] [IsLeftCancelAdd R]
  {χ : H → Rˣ} {F : H → R}

namespace IsCrossedHom

variable (hF : IsCrossedHom χ F)
include hF

/-- A crossed homomorphism into an additively cancellative semiring vanishes at `1`, even when
its twist is not multiplicative. -/
theorem map_one : F 1 = 0 := by
  apply (χ 1).mul_right_inj.mp
  have h := hF.map_mul 1 1
  rw [one_mul, add_comm] at h
  simpa only [mul_zero] using add_eq_left.mp h.symm

grind_pattern map_one => IsCrossedHom χ F

/-- On a product of elements where the twist is trivial, a crossed homomorphism is additive. -/
theorem map_list_prod_of_forall_eq_one {l : List H} (hl : ∀ a ∈ l, χ a = 1) :
    F l.prod = (l.map F).sum := by
  induction l with
  | nil => simp [hF.map_one]
  | cons a l ih =>
    rw [List.prod_cons, hF.map_mul, hl a (by simp), Units.val_one, one_mul,
      ih fun b hb ↦ hl b (by simp [hb]), List.map_cons, List.sum_cons, add_comm]

end IsCrossedHom

end MulOneClass

section Monoid

variable {H : Type*} [Monoid H] {R : Type*} [Semiring R] [IsLeftCancelAdd R]
  {χ : H → Rˣ} {F : H → R}

namespace IsCrossedHom

variable (hF : IsCrossedHom χ F)
include hF

/-- The value of a crossed homomorphism at a power is a geometric sum in the twist times the
value at the base. -/
theorem map_pow (x : H) (k : ℕ) :
    F (x ^ k) = (∑ j ∈ Finset.range k, (χ x : R) ^ j) * F x := by
  induction k with
  | zero => simp [hF.map_one]
  | succ k ih =>
    rw [pow_succ', hF.map_mul, ih, geom_sum_succ, add_mul, one_mul, mul_assoc]

/-- On an element where the twist is trivial, a crossed homomorphism is additive along powers:
`F (x ^ k) = k * F x`. -/
theorem map_pow_of_eq_one {x : H} (hx : χ x = 1) (k : ℕ) : F (x ^ k) = k * F x := by
  simp [hF.map_pow, hx]

end IsCrossedHom

end Monoid

section Ring

variable {H : Type*} [Group H] {R : Type*} [Ring R]
  {χ : H → Rˣ} {F : H → R}

namespace IsCrossedHom

variable (hF : IsCrossedHom χ F)
include hF

/-- The value of a crossed homomorphism at an inverse, multiplied through by the twist. -/
theorem mul_map_inv (x : H) : (χ x : R) * F x⁻¹ = -F x := by
  have h := hF.map_mul x x⁻¹
  rw [mul_inv_cancel, hF.map_one] at h
  exact eq_neg_of_add_eq_zero_left h.symm

/-- The value of a crossed homomorphism at an inverse. -/
theorem map_inv (x : H) : F x⁻¹ = -(((χ x)⁻¹ : Rˣ) : R) * F x := by
  calc F x⁻¹ = (((χ x)⁻¹ : Rˣ) : R) * ((χ x : R) * F x⁻¹) := by
        rw [← mul_assoc, Units.inv_mul, one_mul]
    _ = -(((χ x)⁻¹ : Rˣ) : R) * F x := by rw [hF.mul_map_inv, mul_neg, neg_mul]

end IsCrossedHom

end Ring

section CommRing

open scoped commutatorElement

variable {H : Type*} [Group H] {R : Type*} [CommRing R]
  {F' : Type*} [FunLike F' H Rˣ] [MonoidHomClass F' H Rˣ] {χ : F'} {F : H → R}

/-- The value of a crossed homomorphism on the commutator `⁅x, y⁆ = x * y * x⁻¹ * y⁻¹`; the
character kills the commutator because `Rˣ` is commutative. -/
theorem IsCrossedHom.map_commutatorElement (hF : IsCrossedHom χ F) (x y : H) :
    F ⁅x, y⁆ = ((χ x : R) - 1) * F y - ((χ y : R) - 1) * F x := by
  have h : ⁅x, y⁆ * (y * x) = x * y := by
    simp [commutatorElement_def, mul_assoc]
  have h1 := hF.map_mul ⁅x, y⁆ (y * x)
  rw [h, hF.map_mul x y, hF.map_mul y x, _root_.map_commutatorElement,
    commutatorElement_eq_one_iff_mul_comm.2 (mul_comm (χ x) (χ y)), Units.val_one, one_mul] at h1
  linear_combination -h1

end CommRing

end TauCeti
