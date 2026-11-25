/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Tactic.Ring

/-!
# Binary quartic forms and their invariants

A binary quartic form `a x⁴ + b x³ y + c x² y² + d x y³ + e y⁴` over a commutative ring `R` is
recorded by its five coefficients in descending `x`-degree, `BinaryQuartic R = Fin 5 → R`.
All integer coefficients are allowed; the middle coefficients are not assumed even.

The classical invariants of degrees two and three are
`I = 12ae - 3bd + c²` and `J = 72ace + 9bcd - 27ad² - 27b²e - 2c³`.
The discriminant `BinaryQuartic.disc` is the sixteen-term integral polynomial of degree six,
so it is defined over every commutative ring, including rings in which `3` is not invertible,
and the identity `27 Δ = 4 I³ - J²` is a theorem (`BinaryQuartic.disc_relation`). The three
invariants are homogeneous of degrees two, three and six in the coefficients and commute with
ring homomorphisms; the scaled form `r f` is the coefficientwise scalar multiple `r • f`.

The invariants `I` and `J` order binary quartic forms by height in the parametrisation of
two-Selmer elements of elliptic curves; the integer pairs they take are classified in
`TauCeti.NumberTheory.BinaryQuartic.Eligible`.

## References

* M. Bhargava, A. Shankar, *Binary quartic forms having bounded invariants, and the
  boundedness of the average rank of elliptic curves*, Ann. of Math. 181 (2015), §2, (4).
-/

public section

namespace TauCeti

/-- A binary quartic form `a x⁴ + b x³ y + c x² y² + d x y³ + e y⁴` over `R`, recorded by its
coefficients in descending `x`-degree: `f 0 = a`, `f 1 = b`, `f 2 = c`, `f 3 = d`, `f 4 = e`. -/
abbrev BinaryQuartic (R : Type*) := Fin 5 → R

namespace BinaryQuartic

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The degree-two invariant `I(f) = 12ae - 3bd + c²` of a binary quartic form. -/
def invI (f : BinaryQuartic R) : R := 12 * f 0 * f 4 - 3 * f 1 * f 3 + f 2 ^ 2

/-- The degree-three invariant `J(f) = 72ace + 9bcd - 27ad² - 27b²e - 2c³` of a binary
quartic form. -/
def invJ (f : BinaryQuartic R) : R :=
  72 * f 0 * f 2 * f 4 + 9 * f 1 * f 2 * f 3 - 27 * f 0 * f 3 ^ 2 - 27 * f 1 ^ 2 * f 4 -
    2 * f 2 ^ 3

/-- The discriminant of a binary quartic form, the integral polynomial of degree six in the
coefficients with `27 Δ = 4 I³ - J²` (`disc_relation`). -/
def disc (f : BinaryQuartic R) : R :=
  256 * f 0 ^ 3 * f 4 ^ 3 - 192 * f 0 ^ 2 * f 1 * f 3 * f 4 ^ 2 -
    128 * f 0 ^ 2 * f 2 ^ 2 * f 4 ^ 2 + 144 * f 0 ^ 2 * f 2 * f 3 ^ 2 * f 4 -
    27 * f 0 ^ 2 * f 3 ^ 4 + 144 * f 0 * f 1 ^ 2 * f 2 * f 4 ^ 2 -
    6 * f 0 * f 1 ^ 2 * f 3 ^ 2 * f 4 - 80 * f 0 * f 1 * f 2 ^ 2 * f 3 * f 4 +
    18 * f 0 * f 1 * f 2 * f 3 ^ 3 + 16 * f 0 * f 2 ^ 4 * f 4 - 4 * f 0 * f 2 ^ 3 * f 3 ^ 2 -
    27 * f 1 ^ 4 * f 4 ^ 2 + 18 * f 1 ^ 3 * f 2 * f 3 * f 4 - 4 * f 1 ^ 3 * f 3 ^ 3 -
    4 * f 1 ^ 2 * f 2 ^ 3 * f 4 + f 1 ^ 2 * f 2 ^ 2 * f 3 ^ 2

theorem invI_def (f : BinaryQuartic R) :
    invI f = 12 * f 0 * f 4 - 3 * f 1 * f 3 + f 2 ^ 2 := (rfl)

theorem invJ_def (f : BinaryQuartic R) :
    invJ f = 72 * f 0 * f 2 * f 4 + 9 * f 1 * f 2 * f 3 - 27 * f 0 * f 3 ^ 2 -
      27 * f 1 ^ 2 * f 4 - 2 * f 2 ^ 3 := (rfl)

theorem disc_def (f : BinaryQuartic R) :
    disc f = 256 * f 0 ^ 3 * f 4 ^ 3 - 192 * f 0 ^ 2 * f 1 * f 3 * f 4 ^ 2 -
      128 * f 0 ^ 2 * f 2 ^ 2 * f 4 ^ 2 + 144 * f 0 ^ 2 * f 2 * f 3 ^ 2 * f 4 -
      27 * f 0 ^ 2 * f 3 ^ 4 + 144 * f 0 * f 1 ^ 2 * f 2 * f 4 ^ 2 -
      6 * f 0 * f 1 ^ 2 * f 3 ^ 2 * f 4 - 80 * f 0 * f 1 * f 2 ^ 2 * f 3 * f 4 +
      18 * f 0 * f 1 * f 2 * f 3 ^ 3 + 16 * f 0 * f 2 ^ 4 * f 4 - 4 * f 0 * f 2 ^ 3 * f 3 ^ 2 -
      27 * f 1 ^ 4 * f 4 ^ 2 + 18 * f 1 ^ 3 * f 2 * f 3 * f 4 - 4 * f 1 ^ 3 * f 3 ^ 3 -
      4 * f 1 ^ 2 * f 2 ^ 3 * f 4 + f 1 ^ 2 * f 2 ^ 2 * f 3 ^ 2 := (rfl)

/-- The discriminant relation `27 Δ = 4 I³ - J²`, an identity over every commutative ring. -/
theorem disc_relation (f : BinaryQuartic R) : 27 * disc f = 4 * invI f ^ 3 - invJ f ^ 2 := by
  rw [disc_def, invI_def, invJ_def]
  ring

/-- `I` is homogeneous of degree two in the coefficients. -/
@[simp]
theorem invI_smul (r : R) (f : BinaryQuartic R) : invI (r • f) = r ^ 2 * invI f := by
  simp only [invI_def, Pi.smul_apply, smul_eq_mul]
  ring

/-- `J` is homogeneous of degree three in the coefficients. -/
@[simp]
theorem invJ_smul (r : R) (f : BinaryQuartic R) : invJ (r • f) = r ^ 3 * invJ f := by
  simp only [invJ_def, Pi.smul_apply, smul_eq_mul]
  ring

/-- The discriminant is homogeneous of degree six in the coefficients. -/
@[simp]
theorem disc_smul (r : R) (f : BinaryQuartic R) : disc (r • f) = r ^ 6 * disc f := by
  simp only [disc_def, Pi.smul_apply, smul_eq_mul]
  ring

section map

variable {F : Type*} [FunLike F R S] [RingHomClass F R S]

/-- `I` commutes with base change of the coefficients. -/
@[simp]
theorem invI_comp (φ : F) (f : BinaryQuartic R) : invI (φ ∘ f) = φ (invI f) := by
  simp [invI_def, map_ofNat]

/-- `J` commutes with base change of the coefficients. -/
@[simp]
theorem invJ_comp (φ : F) (f : BinaryQuartic R) : invJ (φ ∘ f) = φ (invJ f) := by
  simp [invJ_def, map_ofNat]

/-- The discriminant commutes with base change of the coefficients. -/
@[simp]
theorem disc_comp (φ : F) (f : BinaryQuartic R) : disc (φ ∘ f) = φ (disc f) := by
  simp [disc_def, map_ofNat]

end map

end BinaryQuartic

end TauCeti
