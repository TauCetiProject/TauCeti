/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.AdjoinRoot

import TauCeti.RingTheory.AdjoinRoot.Basic

/-!
# Separability in terms of `AdjoinRoot`

A polynomial `f` over a commutative ring is separable, that is, coprime to its derivative, if and
only if its derivative is a unit in `R[X]/(f)` (`Polynomial.separable_iff_isUnit_mk_derivative`).
The right-hand side is the form in which separability enters standard étale presentations, where
the derivative must be invertible modulo `f`. The equivalence is the case `g = derivative f` of
`AdjoinRoot.isUnit_mk_iff_isCoprime`: the class of `g` is a unit of `R[X]/(f)` exactly when `f`
and `g` are coprime.

This is kept apart from `TauCeti.RingTheory.AdjoinRoot.Basic` because `Polynomial.Separable` lives
in `Mathlib.FieldTheory.Separable`, which the consumers of that file do not otherwise need.
-/

public section

open Polynomial

namespace Polynomial

variable {R : Type*} [CommRing R] {f : R[X]}

/-- A polynomial is separable if and only if its derivative is a unit modulo it. -/
theorem separable_iff_isUnit_mk_derivative :
    f.Separable ↔ IsUnit (AdjoinRoot.mk f (derivative f)) :=
  (separable_def f).trans AdjoinRoot.isUnit_mk_iff_isCoprime.symm

end Polynomial

end
