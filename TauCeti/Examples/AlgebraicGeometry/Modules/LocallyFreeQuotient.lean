/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Differentials.LocallyFreeQuotient
public import Mathlib.AlgebraicGeometry.AffineSpace

/-!
# Checks for locally free quotients of the differentials

For the affine line `𝔸¹_k` over a field `k`, `Ω_{𝔸¹/k}` admits a locally free quotient of rank `1`
(the identity of `𝒪·dx`, as `𝔸¹_k` is smooth of relative dimension `1`), but none of rank `2`:
the fibre of `Ω_{𝔸¹/k}` at any point is one-dimensional.
-/

public section

open AlgebraicGeometry CategoryTheory TauCeti.AlgebraicGeometry


namespace TauCeti.LocallyFreeQuotientExample

universe u

variable (k : Type u) [Field k]

-- `Ω_{𝔸¹/k}` has a locally free quotient of rank `1`.
example : HasLocallyFreeQuotientOfDifferentials k (𝔸(ULift.{u} (Fin 1); Spec (.of k))) 1 :=
  hasLocallyFreeQuotientOfDifferentials_of_smoothOfRelativeDimension k _ 1

-- `Ω_{𝔸¹/k}` has no locally free quotient of rank `2`.
example : ¬ HasLocallyFreeQuotientOfDifferentials k (𝔸(ULift.{u} (Fin 1); Spec (.of k))) 2 :=
  fun h ↦ absurd (le_of_hasLocallyFreeQuotientOfDifferentials k _ 1 h) (by norm_num)

end TauCeti.LocallyFreeQuotientExample
