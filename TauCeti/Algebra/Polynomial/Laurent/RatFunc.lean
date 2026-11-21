/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import TauCeti.Algebra.Polynomial.Laurent.Basic
import Mathlib.RingTheory.Localization.LocalizationLocalization
import TauCeti.Algebra.Polynomial.Laurent.Polynomial

/-!
# The rational function field as fraction field of Laurent polynomials

Let `K` be an integral domain. Since `RatFunc.X` is nonzero in the rational function field
`RatFunc K`, evaluating Laurent polynomials at `RatFunc.X` yields a `K`-algebra embedding
`TauCeti.laurentToRatFunc K : K[T;T⁻¹] →ₐ[K] RatFunc K` extending `K[X] → RatFunc K`. Because
`K[T;T⁻¹]` is the localization of `K[X]` away from `X` and `RatFunc K` is the fraction field of
`K[X]`, `RatFunc K` is also a fraction field of `K[T;T⁻¹]`
(`TauCeti.isFractionRing_ratFunc_of_laurent`).

## Main definitions

* `TauCeti.laurentToRatFunc`: the `K`-algebra map `K[T;T⁻¹] →ₐ[K] RatFunc K` sending `T` to
  `RatFunc.X`.

## Main results

* `TauCeti.laurentToRatFunc_T`: `laurentToRatFunc K (T n) = RatFunc.X ^ n`.
* `TauCeti.laurentToRatFunc_toLaurent`: `laurentToRatFunc K` extends `algebraMap K[X] (RatFunc K)`
  along `Polynomial.toLaurent`.
* `TauCeti.isFractionRing_ratFunc_of_laurent`: equipped with `laurentToRatFunc K`, `RatFunc K` is
  a fraction field of `K[T;T⁻¹]`.
* `TauCeti.laurentToRatFunc_injective`: `laurentToRatFunc K` is injective.
-/

public section

open Polynomial
open scoped LaurentPolynomial

namespace TauCeti

variable (K : Type*) [CommRing K] [IsDomain K]

/-- The `K`-algebra map `K[T;T⁻¹] → RatFunc K` sending `T` to `RatFunc.X`. -/
noncomputable def laurentToRatFunc : K[T;T⁻¹] →ₐ[K] RatFunc K :=
  laurentEval (Units.mk0 (RatFunc.X : RatFunc K)
    (RatFunc.algebraMap_X (K := K) ▸ RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero))

/-- `laurentToRatFunc K` sends the Laurent monomial `T n` to `RatFunc.X ^ n`. -/
@[simp]
theorem laurentToRatFunc_T (n : ℤ) :
    laurentToRatFunc K (LaurentPolynomial.T n) = (RatFunc.X : RatFunc K) ^ n := by
  rw [laurentToRatFunc, laurentEval_T, Units.val_zpow_eq_zpow_val, Units.val_mk0]

/-- `laurentToRatFunc K` extends `algebraMap K[X] (RatFunc K)` along `Polynomial.toLaurent`. -/
@[simp]
theorem laurentToRatFunc_toLaurent (p : K[X]) :
    laurentToRatFunc K p.toLaurent = algebraMap K[X] (RatFunc K) p := by
  rw [laurentToRatFunc, laurentEval_eq_eval₂, LaurentPolynomial.eval₂_toLaurent, Units.val_mk0,
    ← Polynomial.aeval_def, RatFunc.aeval_X_left_eq_algebraMap]

/-- Equipped with `laurentToRatFunc K`, `RatFunc K` is a fraction field of `K[T;T⁻¹]`. -/
theorem isFractionRing_ratFunc_of_laurent :
    letI : Algebra K[T;T⁻¹] (RatFunc K) := (laurentToRatFunc K).toRingHom.toAlgebra
    IsFractionRing K[T;T⁻¹] (RatFunc K) := by
  let _ : Algebra K[T;T⁻¹] (RatFunc K) := (laurentToRatFunc K).toRingHom.toAlgebra
  have : IsScalarTower K[X] K[T;T⁻¹] (RatFunc K) :=
    .of_algebraMap_eq fun p ↦ (laurentToRatFunc_toLaurent K p).symm
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (Submonoid.powers (X : K[X])) K[T;T⁻¹] (RatFunc K)

/-- `laurentToRatFunc K` is injective. -/
theorem laurentToRatFunc_injective : Function.Injective (laurentToRatFunc K) :=
  letI : Algebra K[T;T⁻¹] (RatFunc K) := (laurentToRatFunc K).toRingHom.toAlgebra
  haveI : IsFractionRing K[T;T⁻¹] (RatFunc K) := isFractionRing_ratFunc_of_laurent K
  IsFractionRing.injective K[T;T⁻¹] (RatFunc K)

end TauCeti
