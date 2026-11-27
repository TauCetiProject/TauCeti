/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import TauCeti.RingTheory.Kaehler.FormallyEtale

/-!
# Kähler differentials of a rational function field

The rational function field `k(X)` is a localization of the polynomial ring `k[X]`, hence formally
étale over `k[X]`. Base-changing Mathlib's polynomial differential basis along `k[X] → k(X)` shows
that `Ω[k(X)⁄k]` is free of rank one over `k(X)` with basis `d X`, and in particular `d X ≠ 0`.

## Main definitions

* `TauCeti.kaehlerBasisRatFunc`: `d X` is a basis of `Ω[k(X)⁄k]`.

## Main results

* `TauCeti.kaehlerBasisRatFunc_apply`: evaluating `kaehlerBasisRatFunc` gives
  `D k (RatFunc k) RatFunc.X`.
* `RatFunc.D_X_ne_zero`: `D k (RatFunc k) RatFunc.X ≠ 0`.
-/

public section

noncomputable section

namespace TauCeti

open Module Polynomial KaehlerDifferential

open scoped nonZeroDivisors

variable (k : Type*) [Field k]

/-- `d X` is a basis of the module of Kähler differentials of the rational function field
`k(X)` over `k`. -/
def kaehlerBasisRatFunc : Basis Unit (RatFunc k) Ω[RatFunc k⁄k] :=
  haveI : Algebra.FormallyEtale k[X] (RatFunc k) :=
    Algebra.FormallyEtale.of_isLocalization (Rₘ := RatFunc k) (k[X])⁰
  kaehlerBasisOfFormallyEtale k k[X] (RatFunc k)
    ((Basis.singleton Unit k[X]).map (KaehlerDifferential.polynomialEquiv k).symm)

@[simp]
theorem kaehlerBasisRatFunc_apply (i : Unit) :
    kaehlerBasisRatFunc k i = D k (RatFunc k) RatFunc.X := by
  have : Algebra.FormallyEtale k[X] (RatFunc k) :=
    Algebra.FormallyEtale.of_isLocalization (Rₘ := RatFunc k) (k[X])⁰
  rw [kaehlerBasisRatFunc, kaehlerBasisOfFormallyEtale_apply]
  simp [KaehlerDifferential.map_D, RatFunc.algebraMap_X]

/-- The differential of the variable of a rational function field is nonzero. -/
@[simp]
theorem _root_.RatFunc.D_X_ne_zero : D k (RatFunc k) RatFunc.X ≠ 0 := by
  simpa only [kaehlerBasisRatFunc_apply] using (kaehlerBasisRatFunc k).ne_zero ()

end TauCeti

end
