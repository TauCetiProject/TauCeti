/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Invertible
import Mathlib.Data.Nat.Cast.Basic

/-!
# Invertibility of numerals in rings

If `2` is a unit in a semiring, zero is the only element that doubles to zero
(`IsUnit.eq_zero_of_add_self_eq_zero`). Ring homomorphisms preserve `Invertible` instances on
numeric literals `n ≥ 2` (`TauCeti.invertibleMapOfNat`).
-/

public section

/-- If `2` is a unit, only zero doubles to zero. -/
theorem IsUnit.eq_zero_of_add_self_eq_zero {R : Type*} [Semiring R] (h2 : IsUnit (2 : R)) :
    ∀ x : R, x + x = 0 → x = 0 := by
  intro x hx
  exact h2.mul_right_eq_zero.mp (by rwa [two_mul])

namespace TauCeti

/-- Ring homomorphisms preserve invertibility of numeric literals `n ≥ 2`. -/
abbrev invertibleMapOfNat {R S F : Type*} [NonAssocSemiring R] [NonAssocSemiring S] [FunLike F R S]
    [RingHomClass F R S] (f : F) (n : ℕ) [n.AtLeastTwo] [Invertible (ofNat(n) : R)] :
    Invertible (ofNat(n) : S) :=
  (Invertible.map f (ofNat(n) : R)).copy ofNat(n) (by exact (map_ofNat f n).symm)

end TauCeti
