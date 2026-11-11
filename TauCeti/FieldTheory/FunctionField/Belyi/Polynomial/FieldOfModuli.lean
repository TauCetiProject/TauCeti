/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Belyi.FieldOfModuli
public import TauCeti.FieldTheory.FunctionField.Belyi.Polynomial.GaloisAction
import TauCeti.FieldTheory.IsAlgClosed.Automorphism

/-!
# Fields of moduli of polynomial Belyi pairs with rational coefficients

A polynomial `q ∈ k[X]` of positive degree whose critical values lie in `{0, 1}` defines the
algebraic Belyi pair `TauCeti.AlgebraicBelyiPair.ofPolynomial q`. If `q` has rational
coefficients, every automorphism of `k` fixes its class
(`TauCeti.AlgebraicBelyiPair.IsoClass.stabilizer_mk_ofPolynomial_eq_top`). Over an algebraically
closed field, such as `ℂ` or `AlgebraicClosure ℚ`, only the rationals are fixed by all of
`Gal(k/ℚ)`, so the field of moduli of the class is `ℚ`.

## Main results

* `TauCeti.AlgebraicBelyiPair.IsoClass.fieldOfModuli_mk_ofPolynomial`: over an algebraically
  closed field, the field of moduli of a polynomial Belyi pair with rational coefficients is `ℚ`.
-/

public section

open Polynomial

universe u

namespace TauCeti

namespace AlgebraicBelyiPair

namespace IsoClass

variable {k : Type u} [Field k] [CharZero k] {q : k[X]} (hq : 0 < q.natDegree)
  (hcrit : ∀ (L : Type u) [Field L] [Algebra k L], q.criticalValues L ⊆ {0, 1})

/-- Over an algebraically closed field, such as `ℂ` or `AlgebraicClosure ℚ`, the field of moduli
of the class of a polynomial Belyi pair with rational coefficients is `ℚ`. -/
theorem fieldOfModuli_mk_ofPolynomial [IsAlgClosed k] (hℚ : q ∈ lifts (algebraMap ℚ k)) :
    (mk (ofPolynomial q hq hcrit)).fieldOfModuli = ⊥ := by
  rw [fieldOfModuli_def, stabilizer_mk_ofPolynomial_eq_top hq hcrit hℚ,
    IsAlgClosed.fixedField_top_eq_bot]

end IsoClass

end AlgebraicBelyiPair

end TauCeti
