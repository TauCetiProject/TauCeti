/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Differentials.LocallyFreeQuotient
public import Mathlib.AlgebraicGeometry.AffineSpace

/-!
# Checks for locally free quotients of the differentials: the empty scheme and rank zero

* On the empty scheme `Spec 0`, `Ω_{X/k}` admits a locally free quotient of every rank `d`. A
  definition demanding that the quotient have rank `d` at some point, or be nonzero, would fail
  here, although the empty scheme is smooth.
* On the affine line `𝔸¹_k`, `Ω_{𝔸¹/k}` admits a locally free quotient of rank `0`: the zero
  quotient.
-/

public section

open AlgebraicGeometry CategoryTheory TauCeti.AlgebraicGeometry

namespace TauCeti.LocallyFreeQuotientEmptyExample

universe u

variable (k : Type u) [Field k]

-- On the empty scheme `Spec 0`, `Ω_{X/k}` has a locally free quotient of every rank `d`.
example (d : ℕ) : HasLocallyFreeQuotientOfDifferentials k (Spec (.of PUnit.{u + 1})) d :=
  hasLocallyFreeQuotientOfDifferentials_of_isEmpty k _ d

-- `Ω_{𝔸¹/k}` has a locally free quotient of rank `0`.
example : HasLocallyFreeQuotientOfDifferentials k (𝔸(ULift.{u} (Fin 1); Spec (.of k))) 0 :=
  hasLocallyFreeQuotientOfDifferentials_zero k _

end TauCeti.LocallyFreeQuotientEmptyExample
