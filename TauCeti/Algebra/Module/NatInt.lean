/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Group.Action.Units
public import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Ring.Int.Units

/-!
# Integer unit signs acting on modules

The sign action of an integer unit agrees with the action of its image in the scalar ring.
This lets integer signs in the scalar ring, such as powers of `-1`, combine with integer unit
actions.

Without any compatibility between the scalar action and a product, the scalars `±1` still commute
with multiplication, because `(-1) • a` is the additive inverse of `a`.

When a natural number `n` is a unit of the scalar ring, `Ring.inverse_natCast_smul_nsmul` divides
`n • v` by `n`.
Cross-multiplication of natural scalar-multiple relations is given by
`TauCeti.nsmul_eq_nsmul_of_nsmul_eq`.
-/

public section

namespace TauCeti

/-- Acting by the image of an integer unit in the scalar ring and then by a second integer unit
is the action of their product as integer units. -/
theorem intCast_smul_units_smul {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]
    (u' u : ℤˣ) (v : V) : ((u' : ℤ) : R) • u • v = (u' * u) • v := by
  rw [mul_smul, Units.smul_def u', ← Int.cast_smul_eq_zsmul R]

/-- Without any compatibility between the `R`-action and the product, the scalars `±1` still
commute with multiplication, because `(-1) • a` is the additive inverse of `a`. -/
theorem intUnits_smul_mul_smul {R A : Type*} [Ring R] [NonUnitalNonAssocSemiring A] [Module R A]
    (u v : ℤˣ) (a b : A) :
    (((u : ℤ) : R) • a) * (((v : ℤ) : R) • b) = (((u * v : ℤˣ) : ℤ) : R) • (a * b) := by
  let : AddCommGroup A := Module.addCommMonoidToAddCommGroup R
  let : NonUnitalNonAssocRing A := { ‹NonUnitalNonAssocSemiring A›, this with }
  rcases Int.units_eq_one_or u with rfl | rfl <;> rcases Int.units_eq_one_or v with rfl | rfl <;>
    simp

/-- Cross-multiplication for natural scalar multiples: if `d₁ • x = m₁ • y₁` and
`d₂ • x = m₂ • y₂`, then `(d₂ * m₁) • y₁ = (d₁ * m₂) • y₂`. -/
theorem nsmul_eq_nsmul_of_nsmul_eq {M : Type*} [AddMonoid M]
    {d₁ m₁ d₂ m₂ : ℕ} {x y₁ y₂ : M}
    (h₁ : d₁ • x = m₁ • y₁) (h₂ : d₂ • x = m₂ • y₂) :
    (d₂ * m₁) • y₁ = (d₁ * m₂) • y₂ := by
  rw [mul_smul, ← h₁, ← mul_smul, mul_comm d₂ d₁, mul_smul, h₂, ← mul_smul]

end TauCeti

/-- Dividing `n • v` by a natural number `n` that is a unit of the scalar ring gives back `v`. -/
theorem Ring.inverse_natCast_smul_nsmul {R V : Type*} [Semiring R] [AddCommMonoid V] [Module R V]
    {n : ℕ} (hn : IsUnit (n : R)) (v : V) : Ring.inverse (n : R) • n • v = v := by
  rw [← Nat.cast_smul_eq_nsmul R, smul_smul, Ring.inverse_mul_cancel _ hn, one_smul]
