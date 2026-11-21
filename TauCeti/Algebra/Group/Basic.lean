/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Commute.Defs

/-!
# Basic identities in groups

## Main results

* `TauCeti.inv_mul_eq_inv_mul_iff_mul_inv_eq_mul_inv`: in a group, `b⁻¹ * a = d⁻¹ * c` if and only
  if `a * c⁻¹ = b * d⁻¹`. In a commutative group, Mathlib's
  `inv_mul_eq_inv_mul_iff_mul_eq_mul` gives the equivalent `a * d = c * b`.
* `Commute.apply_right_of_conj`: if `g` commutes with `h` and a map `T` takes `g * h * g⁻¹` to
  `g * T h * g⁻¹`, then `g` commutes with `T h`. So a map that commutes with conjugation maps
  every centralizer to itself.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G] {a b c d : G}

/-- Two left quotients `b⁻¹ * a` and `d⁻¹ * c` are equal exactly when the right quotients
`a * c⁻¹` and `b * d⁻¹` are. -/
@[to_additive /-- Two left differences `-b + a` and `-d + c` are equal exactly when the right
differences `a + -c` and `b + -d` are. -/]
theorem inv_mul_eq_inv_mul_iff_mul_inv_eq_mul_inv : b⁻¹ * a = d⁻¹ * c ↔ a * c⁻¹ = b * d⁻¹ := by
  rw [inv_mul_eq_iff_eq_mul, mul_inv_eq_iff_eq_mul, mul_assoc]

end TauCeti

namespace Commute

variable {G : Type*} [Group G] {g h : G}

/-- If `g` commutes with `h` and a map `T` takes `g * h * g⁻¹` to `g * T h * g⁻¹`, then `g`
commutes with `T h`. -/
@[to_additive /-- If `g` commutes with `h` and a map `T` takes `g + h + -g` to `g + T h + -g`,
then `g` commutes with `T h`. -/]
theorem apply_right_of_conj {T : G → G} (hc : Commute g h)
    (hT : T (g * h * g⁻¹) = g * T h * g⁻¹) : Commute g (T h) := by
  rw [hc.mul_inv_cancel, eq_mul_inv_iff_mul_eq] at hT
  exact hT.symm

end Commute
