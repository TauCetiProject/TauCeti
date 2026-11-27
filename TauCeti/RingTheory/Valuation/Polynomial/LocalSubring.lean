/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.RingTheory.Valuation.LocalSubring
import TauCeti.RingTheory.Valuation.Polynomial.Basic

/-!
# Polynomial evaluation at nonunits of a valuation subring

For the tautological valuation of a valuation subring containing a field of constants, a polynomial
with nonzero constant term evaluated at an element of value less than `1` has value exactly `1`:
the constant term strictly dominates all the others. This is the constant-term estimate used in
Stichtenoth's proof that valuation rings of algebraic function fields are discrete (Lemma 1.1.7).

## Main results

* `TauCeti.valuation_aeval_eq_one`: a polynomial with nonzero constant term has value `1` when
  evaluated at an element of the maximal ideal of a valuation subring containing the coefficients.
-/

public section

open Polynomial

namespace TauCeti

universe u v

variable {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]
  {A : ValuationSubring F}

/-- A polynomial with nonzero constant term, evaluated at a nonunit of a valuation subring
containing the constants, is a unit: the constant term dominates. -/
theorem valuation_aeval_eq_one (hk : ∀ c : k, algebraMap k F c ∈ A) {x : F}
    (hx : A.valuation x < 1) {p : k[X]} (hp : p.coeff 0 ≠ 0) :
    A.valuation (aeval x p) = 1 := by
  have hkle : ∀ c : k, A.valuation (algebraMap k F c) ≤ 1 :=
    fun c ↦ (A.valuation_le_one_iff _).2 (hk c)
  have : A.valuation.IsTrivialOn k := .of_le_one _ hkle
  obtain ⟨q, hq⟩ : (X : k[X]) ∣ p - C (p.coeff 0) := X_dvd_iff.2 (by simp)
  have hsplit : aeval x p = x * aeval x q + algebraMap k F (p.coeff 0) := by
    have := congrArg (aeval x) hq
    simp only [map_sub, map_mul, aeval_X, aeval_C] at this
    linear_combination (norm := ring_nf) this
  rw [hsplit, Valuation.map_add_eq_of_lt_right, Valuation.IsTrivialOn.eq_one _ hp]
  rw [Valuation.IsTrivialOn.eq_one (A := k) _ hp, map_mul]
  calc A.valuation x * A.valuation (aeval x q)
      ≤ A.valuation x * 1 := by gcongr; exact A.valuation.aeval_le_one hkle hx.le q
    _ = A.valuation x := mul_one _
    _ < 1 := hx

end TauCeti
