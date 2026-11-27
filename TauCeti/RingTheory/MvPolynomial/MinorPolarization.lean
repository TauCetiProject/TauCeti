/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.DeterminantalIdeal
public import TauCeti.Algebra.MvPolynomial.PolynomialOperator
import TauCeti.RingTheory.Derivation.Determinant
import TauCeti.RingTheory.MvPolynomial.DeterminantalIdeal

/-!
# Polarization operators on the generic minors

Let `X = (X (a, v))` be the generic `m × n` matrix, with entries the variables of
`MvPolynomial (m × n) R`. The **polarization operator** `∑ v, X (x, v) ∂ / ∂ X (y, v)`, a sum of
the derivations `TauCeti.polynomialOperator`, replaces the variables of the row `y` by those of the
row `x`; for the action of `gl m` on polynomials in the entries of `X` by substitution, it is the
derivative of the matrix unit `E x y`.

On the generic minor `Matrix.mvPolynomialMinor R r c` on the rows `r` and the columns `c`, the
polarization operator from the row `r j` to the row `r i` replaces the row `j` of the minor by its
row `i`. So it fixes the minor when `i = j` and kills it otherwise, the result then having two
equal rows (`Matrix.sum_polynomialOperator_mvPolynomialMinor`). This is the computation behind the
highest weight vectors of the actions of `gl m` and `gl n` on polynomials in the entries of `X`
that are products of minors.

## Main results

* `Matrix.sum_polynomialOperator_mvPolynomialMinor`: the polarization operators on a generic minor.

## References

* H. Weyl, *The Classical Groups*, Princeton University Press (1939), Chapter II
  (polarization).
-/

public section

namespace Matrix

open MvPolynomial Finset TauCeti

variable {R m n t : Type*} [CommRing R] [Fintype t] [DecidableEq t]

/-- **Polarization of a generic minor.** The polarization operator
`∑ v, X (r i, v) ∂ / ∂ X (r j, v)`, which replaces the row `r j` of the generic matrix by the row
`r i`, fixes the minor on the rows `r` and the columns `c` when `i = j`, and kills it otherwise. -/
theorem sum_polynomialOperator_mvPolynomialMinor [Fintype n] (r : t → m) (c : t → n) (i j : t) :
    ∑ v, polynomialOperator R (r i, v) (r j, v) (mvPolynomialMinor R r c) =
      if i = j then mvPolynomialMinor R r c else 0 := by
  classical
  by_cases hr : Function.Injective r
  swap
  -- A minor on repeated rows vanishes, and so do both sides.
  · simp [mvPolynomialMinor_eq_zero_of_not_injective_left hr c]
  rw [mvPolynomialMinor_eq_det_submatrix]
  set M := (mvPolynomialX m n R).submatrix r c
  let D : Derivation R (MvPolynomial (m × n) R) (MvPolynomial (m × n) R) :=
    ∑ v : n, polynomialOperator R (r i, v) (r j, v)
  have hD (P : MvPolynomial (m × n) R) : D P = ∑ v, polynomialOperator R (r i, v) (r j, v) P :=
    _root_.sum_apply _ _ P
  -- `D` acts on the entries of `M` as the left multiplication by the matrix unit `E j i`.
  have hmap : M.map D = M * 0 - -single j i 1 * M := by
    ext a b
    rw [Matrix.mul_zero, zero_sub, Matrix.neg_mul, neg_neg, map_apply, hD]
    by_cases ha : a = j
    · subst ha
      simp [M, single_mul_apply_same, polynomialOperator_X]
    · simp [M, single_mul_apply_of_ne (h := ha), hr.ne ha]
  rw [← hD, Derivation.leibniz_det_of_map_eq_mul_sub_mul D hmap, trace_zero, trace_neg,
    sub_neg_eq_add, zero_add]
  by_cases hij : i = j
  · subst hij
    simp [trace_single_eq_same]
  · simp [hij, trace_single_eq_of_ne (h := Ne.symm hij)]

end Matrix
