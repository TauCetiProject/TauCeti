/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisGroups.Resolvent.Quartic.Basic
public import TauCeti.RingTheory.Polynomial.Resultant.Discriminant

/-!
# The discriminant of the quartic resolvent cubic

The depressed quartic

`X⁴ + pX² + qX + r`

and its cubic resolvent

`X³ - pX² - 4rX + (4pr - q²)`

have the same discriminant. Consequently the resolvent cubic is separable exactly when the
quartic is separable. In particular, resolvents of separable quartics require no additional
separation hypothesis.

The discriminant calculation is valid over an arbitrary commutative ring. The proof evaluates
the Sylvester determinant of the quartic and compares the resulting formula with Mathlib's
`Cubic.discr` formula for the resolvent.

## Main results

* `Polynomial.discr_depressedQuartic`: the explicit discriminant of a depressed quartic.
* `TauCeti.discr_resolventCubic`: a depressed quartic and its resolvent cubic have equal
  discriminants.
* `TauCeti.separable_resolventCubic_iff`: the quartic is separable exactly when its resolvent is.
* `TauCeti.separable_resolventCubic`: a separable quartic has a separable resolvent cubic.

## References

* K. Conrad, *Galois groups of cubics and quartics (not in characteristic 2)*, Theorem 3.4.
-/

public section

open Polynomial

namespace TauCeti

variable {R : Type*} [CommRing R]

/-- A depressed quartic and its resolvent cubic have the same discriminant. -/
theorem discr_resolventCubic (p q r : R) :
    (X ^ 4 + C p * X ^ 2 + C q * X + C r : R[X]).discr =
      (resolventCubic p q r).discr := by
  nontriviality R
  have hres : resolventCubic p q r =
      (Cubic.toPoly ⟨1, -p, -(4 * r), 4 * p * r - q ^ 2⟩ : R[X]) := by
    simp [resolventCubic_def, Cubic.toPoly]
    ring
  rw [hres, Cubic.toPoly_discr one_ne_zero, Cubic.discr, Polynomial.discr_depressedQuartic]
  ring

/-- The resolvent cubic of a depressed quartic is separable exactly when the quartic is
separable. This holds over every commutative ring, where separability of a monic polynomial is
equivalent to its discriminant being a unit. -/
@[simp]
theorem separable_resolventCubic_iff (p q r : R) :
    (resolventCubic p q r).Separable ↔
      (X ^ 4 + C p * X ^ 2 + C q * X + C r : R[X]).Separable := by
  nontriviality R
  have hquartic : (X ^ 4 + C p * X ^ 2 + C q * X + C r : R[X]).Monic := by
    have hdeg : degree (C p * X ^ 2 + C q * X + C r : R[X]) < 4 := by
      compute_degree
      norm_num
    simpa only [add_assoc] using monic_X_pow_add hdeg
  rw [← (monic_resolventCubic p q r).isUnit_discr_iff,
    ← hquartic.isUnit_discr_iff, discr_resolventCubic]

/-- The resolvent cubic of a separable depressed quartic is separable. -/
theorem separable_resolventCubic (p q r : R)
    (h : (X ^ 4 + C p * X ^ 2 + C q * X + C r : R[X]).Separable) :
    (resolventCubic p q r).Separable :=
  (separable_resolventCubic_iff p q r).2 h

end TauCeti
