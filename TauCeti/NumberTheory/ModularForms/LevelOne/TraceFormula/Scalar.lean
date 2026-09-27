/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.ExplicitElement
public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.PeriodAction
public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.DoubleCoset
public import TauCeti.RingTheory.MvPolynomial.Finrank
public import TauCeti.RingTheory.Polynomial.Dickson
public import TauCeti.NumberTheory.HurwitzClassNumber
public import Mathlib.LinearAlgebra.Trace

/-!
# The scalar contribution to the level-one trace formula

For a nonzero integer `a`, the scalar matrix `aI` has determinant `a²` and one class modulo
simultaneous sign. Popa and Zagier's explicit element has coefficient `1/6` on this class. On
binary forms of degree `w`, `aI` acts by `aʷ`, so its contribution to the ambient trace is
`(w + 1) aʷ / 6`. This is the scalar term in the ambient conjugacy-type calculation of the
Eichler–Selberg trace formula. The period-polynomial transfer gives the cusp-form trace as
`(tr(Tₙ | W_w) - σ_{w+1}(n))/2`. The scalar term has no Eisenstein correction, and its half
agrees with the two `t = ±2a` boundary terms involving `H(0) = -1/12`.

The coefficient is computed from Popa–Zagier's four weighted regions, while the trace uses the
standard basis of degree-`w` binary monomials. The scalar calculation is independent of the
other elliptic, hyperbolic, and parabolic conjugacy types.

## References

* A. Popa and D. Zagier, *An elementary proof of the Eichler–Selberg trace formula*,
  J. Reine Angew. Math. **762** (2020), 105–122, arXiv:1711.00327, §4, eq. (15).
-/

public section

open Matrix MvPolynomial MulOpposite MonoidAlgebra

namespace TauCeti

namespace TraceFormulaMatrixModule

/-- The coefficient of a nonzero scalar class in Popa–Zagier's element is `1/6`. -/
theorem coeff_popaZagierElement_scalar {k : Type*} [DivisionRing k] [CharZero k]
    (a : ℤ) (ha : a ≠ 0) :
    (popaZagierElement k (a ^ 2)).coeff
      (mk (TraceFormulaMatrix.diagonal a a (pow_two a).symm)) = 1 / 6 := by
  rcases lt_or_gt_of_ne ha with h | h
  · rw [coeff_popaZagierElement_mk]
    simp [PopaZagier.weight, PopaZagier.weight₁,
      PopaZagier.weight₂, PopaZagier.weight₃, PopaZagier.weight₄,
      PopaZagier.chainWeight₃, h.le, h, not_le.mpr h]
    norm_num
  · rw [coeff_popaZagierElement_mk_of_pos _ (Or.inr ⟨by simp, by simpa using h⟩)]
    simp [PopaZagier.weight, PopaZagier.weight₁,
      PopaZagier.weight₂, PopaZagier.weight₃, PopaZagier.weight₄,
      PopaZagier.chainWeight₃, h, not_le.mpr h]
    norm_num

/-- A scalar matrix acts on degree-`w` binary forms by `aʷ`. -/
theorem binaryFormAction_scalar {R : Type*} [CommRing R] (w : ℕ) (hw : Even w) (a : ℤ) :
    binaryFormAction (R := R) hw (mk (TraceFormulaMatrix.diagonal a a (pow_two a).symm)) =
      (a : R) ^ w • (1 : Module.End R (homogeneousSubmodule (Fin 2) R w)) := by
  simpa only [binaryFormAction_mk, TraceFormulaMatrix.val_diagonal] using
    (binaryFormRep_op_scalar (R := R) (w := w) a)

private theorem weighted_scalar_trace (w : ℕ) (hw : Even w) (a : ℤ) (ha : a ≠ 0) :
    (popaZagierElement ℚ (a ^ 2)).coeff
        (mk (TraceFormulaMatrix.diagonal a a (pow_two a).symm)) *
        LinearMap.trace ℚ (homogeneousSubmodule (Fin 2) ℚ w)
          (binaryFormAction (R := ℚ) hw
            (mk (TraceFormulaMatrix.diagonal a a (pow_two a).symm))) =
      (w + 1 : ℕ) * (a : ℚ) ^ w / 6 := by
  rw [coeff_popaZagierElement_scalar a ha, binaryFormAction_scalar w hw a]
  simp only [map_smul, LinearMap.trace_one, finrank_homogeneousSubmodule_fin_two, smul_eq_mul]
  ring

/-- The scalar-class summand of Popa–Zagier's element contributes `(w + 1) aʷ / 6` to the
trace of its action on all binary forms of degree `w`. -/
theorem trace_periodAction_single_scalar (w : ℕ) (hw : Even w) (a : ℤ) (ha : a ≠ 0) :
    LinearMap.trace ℚ (homogeneousSubmodule (Fin 2) ℚ w)
        (periodAction (R := ℚ) hw
          (single (mk (TraceFormulaMatrix.diagonal a a (pow_two a).symm))
            ((popaZagierElement ℚ (a ^ 2)).coeff
              (mk (TraceFormulaMatrix.diagonal a a (pow_two a).symm))))) =
      (w + 1 : ℕ) * (a : ℚ) ^ w / 6 := by
  rw [periodAction_single, map_smul, smul_eq_mul]
  exact weighted_scalar_trace w hw a ha

/-- The scalar contribution to the ambient trace matches the pair of `t = ±2a`
terms in Zagier's class-number sum. Both sides are halved when passing to the cusp-form trace. -/
theorem trace_periodAction_single_scalar_eq_neg_dickson_eval_mul_hurwitzClassNumber_zero
    (w : ℕ) (hw : Even w)
    (a : ℤ) (ha : a ≠ 0) :
    LinearMap.trace ℚ (homogeneousSubmodule (Fin 2) ℚ w)
          (periodAction (R := ℚ) hw
            (single (mk (TraceFormulaMatrix.diagonal a a (pow_two a).symm))
              ((popaZagierElement ℚ (a ^ 2)).coeff
                (mk (TraceFormulaMatrix.diagonal a a (pow_two a).symm))))) =
      -((Polynomial.dickson 2 ((a : ℚ) ^ 2) w).eval (2 * (a : ℚ)) *
            hurwitzClassNumber 0 +
          (Polynomial.dickson 2 ((a : ℚ) ^ 2) w).eval (-2 * (a : ℚ)) *
            hurwitzClassNumber 0) := by
  rw [trace_periodAction_single_scalar w hw a ha]
  have hminus : (Polynomial.dickson 2 ((a : ℚ) ^ 2) w).eval (-2 * (a : ℚ)) =
      (w + 1 : ℕ) * (a : ℚ) ^ w := by
    simpa [neg_sq, neg_pow, hw.neg_one_pow] using
      (Polynomial.dickson_two_sq_eval_two_mul (-(a : ℚ)) w)
  rw [Polynomial.dickson_two_sq_eval_two_mul, hminus, hurwitzClassNumber_zero]
  push_cast
  ring

end TraceFormulaMatrixModule

end TauCeti
