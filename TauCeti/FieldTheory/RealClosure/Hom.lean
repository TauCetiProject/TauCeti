/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsRealClosed.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.RingTheory.SimpleRing.Basic

/-! # Ring homomorphisms out of a real closed field

A ring homomorphism from an ordered real closed field into a nontrivial ordered ring is strictly
monotone: it maps the nonnegative elements, which are squares, to squares.

## Main results

* `RingHom.strictMono_of_isRealClosed`: a ring homomorphism from an ordered real closed field to
  a nontrivial ordered ring is strictly monotone.

## References

S. Basu, R. Pollack, and M.-F. Roy,
[Algorithms in Real Algebraic Geometry](https://doi.org/10.1007/3-540-33099-2),
second edition, Chapter 2, for real closed fields and their ordered extensions.
-/

public section

namespace RingHom

variable {R S : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
  [Ring S] [LinearOrder S] [IsOrderedRing S] [Nontrivial S]

/-- A ring homomorphism from an ordered real closed field into a nontrivial ordered ring is
strictly monotone, since the nonnegative elements of a real closed field are squares. -/
theorem strictMono_of_isRealClosed (f : R →+* S) : StrictMono f :=
  (ringHom_monotone (fun _ ↦ IsRealClosed.nonneg_iff_isSquare.mp) f).strictMono_of_injective
    f.injective

end RingHom
