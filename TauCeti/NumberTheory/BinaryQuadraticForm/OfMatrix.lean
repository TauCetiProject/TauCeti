/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
public import TauCeti.NumberTheory.BinaryQuadraticForm.Basic
import TauCeti.Algebra.QuadraticDiscriminant

/-!
# The binary quadratic form of a `2 × 2` matrix

To a matrix `M = !![a, b; c, d]` we attach the binary quadratic form
`Q_M = c x² + (d - a) x y - b y²`, whose value at `v = (x, y)` is the determinant of the matrix
with columns `v` and `M v` (this is not the Gram form `vᵀ M v`). Its roots are the fixed points of
`M` acting by Möbius transformations: for invertible `M`, `Q_M(z, 1)` is Mathlib's
`Matrix.GeneralLinearGroup.fixpointPolynomial`. The discriminant of `Q_M` is `tr(M)² - 4 det M`,
Mathlib's `Matrix.discr M`,
and conjugating `M` by `γ ∈ SL(2, R)` acts on `Q_M` by the action `γ • f = f ∘ γ⁻¹` of
`TauCeti.BinaryQuadraticForm.Basic`.

Over `ℤ`, `M ↦ Q_M` is a bijection between the matrices of trace `t` and determinant `n` and the
forms of discriminant `t² - 4 n`: the form determines `c`, `b` and `d - a`, the trace determines
`a + d`, and `(d - a)² + 4 b c = t² - 4 n` forces `d - a ≡ t (mod 2)`. This is the correspondence
through which the Eichler–Selberg trace formula counts the elliptic conjugacy classes of matrices
of determinant `n` by the Hurwitz class numbers `H(4 n - t²)`.

## Main definitions

* `TauCeti.BinaryQuadraticForm.ofMatrix`: the form `Q_M = c x² + (d - a) x y - b y²`.
* `TauCeti.BinaryQuadraticForm.ofMatrixEquiv`: for `t n : ℤ`, the bijection `M ↦ Q_M` from the
  integer matrices of trace `t` and determinant `n` to the forms of discriminant `t² - 4 n`.

## Main results

* `TauCeti.BinaryQuadraticForm.discrim_ofMatrix`: the discriminant of `Q_M` is
  `tr(M)² - 4 det M`.
* `TauCeti.BinaryQuadraticForm.ofMatrix_conj`: `Q_{γ M γ⁻¹} = γ • Q_M` for `γ ∈ SL(2, R)`.
* `TauCeti.BinaryQuadraticForm.ofMatrix_inj_of_trace_eq`: an integer `2 × 2` matrix is determined
  by its trace and its form `Q_M`.

## References

* A. Popa and D. Zagier, *An elementary proof of the Eichler–Selberg trace formula*,
  J. Reine Angew. Math. **762** (2020), 105–122, arXiv:1711.00327, §1.
-/

public section

open Matrix
open scoped MatrixGroups

namespace TauCeti

namespace BinaryQuadraticForm

variable {R : Type*} [CommRing R]

/-- The binary quadratic form `Q_M = c x² + (d - a) x y - b y²` of the matrix `M = !![a, b; c, d]`
(see `eval_ofMatrix`). -/
def ofMatrix (M : Matrix (Fin 2) (Fin 2) R) : BinaryQuadraticForm R :=
  ⟨M 1 0, M 1 1 - M 0 0, -M 0 1⟩

/-- The `x²`-coefficient of `Q_M` is the lower left entry `c` of `M`. -/
@[simp]
theorem ofMatrix_a (M : Matrix (Fin 2) (Fin 2) R) : (ofMatrix M).a = M 1 0 := (rfl)

/-- The `x y`-coefficient of `Q_M` is the difference `d - a` of the diagonal entries of `M`. -/
@[simp]
theorem ofMatrix_b (M : Matrix (Fin 2) (Fin 2) R) : (ofMatrix M).b = M 1 1 - M 0 0 := (rfl)

/-- The `y²`-coefficient of `Q_M` is `-b`, the negated upper right entry of `M`. -/
@[simp]
theorem ofMatrix_c (M : Matrix (Fin 2) (Fin 2) R) : (ofMatrix M).c = -M 0 1 := (rfl)

/-- The value of `Q_M` at `(x, y)` is the determinant of the matrix with columns `(x, y)` and
`M (x, y)`. -/
theorem eval_ofMatrix (M : Matrix (Fin 2) (Fin 2) R) (x y : R) :
    (ofMatrix M).eval x y = det !![x, (M *ᵥ ![x, y]) 0; y, (M *ᵥ ![x, y]) 1] := by
  simp only [eval_def, ofMatrix_a, ofMatrix_b, ofMatrix_c, det_fin_two_of, mulVec, dotProduct,
    Fin.sum_univ_two, cons_val_zero, cons_val_one]
  ring

/-- The discriminant of `Q_M` is `tr(M)² - 4 det M`. -/
@[simp]
theorem discrim_ofMatrix (M : Matrix (Fin 2) (Fin 2) R) :
    (ofMatrix M).discrim = M.trace ^ 2 - 4 * M.det := by
  simp only [discrim_def, discrim, trace_fin_two, det_fin_two, ofMatrix_a, ofMatrix_b, ofMatrix_c]
  ring

/-- The discriminant of `Q_M` is Mathlib's discriminant `Matrix.discr M` of `M`. -/
theorem discrim_ofMatrix_eq_discr (M : Matrix (Fin 2) (Fin 2) R) :
    (ofMatrix M).discrim = M.discr := by
  rw [discrim_ofMatrix, discr_fin_two]

/-- For `g ∈ GL(2, R)`, `Q_g(z, 1)` is Mathlib's fixed-point polynomial of `g` evaluated at `z`,
whose roots are the fixed points of `g` acting by Möbius transformations. -/
theorem eval_ofMatrix_eq_eval_fixpointPolynomial (g : GL (Fin 2) R) (z : R) :
    (ofMatrix (g : Matrix (Fin 2) (Fin 2) R)).eval z 1 =
      (GeneralLinearGroup.fixpointPolynomial g).eval z := by
  simp only [eval_def, ofMatrix_a, ofMatrix_b, ofMatrix_c, GeneralLinearGroup.fixpointPolynomial,
    Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X]
  ring

/-- Conjugation by `γ ∈ SL(2, R)` acts on `Q_M` as `γ` acts on forms: `Q_{γ M γ⁻¹} = γ • Q_M`. -/
theorem ofMatrix_conj (γ : SL(2, R)) (M : Matrix (Fin 2) (Fin 2) R) :
    ofMatrix (γ * M * γ⁻¹ : Matrix (Fin 2) (Fin 2) R) = γ • ofMatrix M := by
  simp only [BinaryQuadraticForm.ext_iff, SpecialLinearGroup.coe_inv, adjugate_fin_two, ofMatrix_a,
    ofMatrix_b, ofMatrix_c, smul_a, smul_b, smul_c, mul_apply, Fin.sum_univ_two, of_apply,
    cons_val', cons_val_zero, cons_val_one]
  refine ⟨?_, ?_, ?_⟩ <;> ring

/-- Over `ℤ`, a `2 × 2` matrix is determined by its trace and its form `Q_M`. -/
theorem ofMatrix_inj_of_trace_eq {M N : Matrix (Fin 2) (Fin 2) ℤ} (h : M.trace = N.trace) :
    ofMatrix M = ofMatrix N ↔ M = N := by
  refine ⟨fun hMN ↦ ?_, congrArg ofMatrix⟩
  -- the form gives `c`, `b` and `d - a`, and the trace gives `a + d`
  simp only [BinaryQuadraticForm.ext_iff, ofMatrix_a, ofMatrix_b, ofMatrix_c, neg_inj] at hMN
  rw [trace_fin_two, trace_fin_two] at h
  ext i j
  fin_cases i <;> fin_cases j <;> lia

private theorem two_mul_ediv_two_of_discrim_eq {f : BinaryQuadraticForm ℤ} {t n : ℤ}
    (hf : f.discrim = t ^ 2 - 4 * n) : 2 * ((t - f.b) / 2) = t - f.b :=
  Int.two_mul_ediv_two_of_even <| by
    have := Int.discrim_emod_four f.a f.b f.c
    rw [← discrim_def, hf] at this
    grind [Int.sq_emod_four t]

/-- For `t n : ℤ`, `M ↦ Q_M` is a bijection from the integer matrices of trace `t` and determinant
`n` to the integral forms of discriminant `t² - 4 n`. The inverse sends `f = ⟨a, b, c⟩` to
`!![(t - b) / 2, -c; a, t - (t - b) / 2]`; as `b² - 4 a c = t² - 4 n` forces `b ≡ t (mod 2)`, its
lower right entry is `(t + b) / 2`. -/
def ofMatrixEquiv (t n : ℤ) : {M : Matrix (Fin 2) (Fin 2) ℤ // M.trace = t ∧ M.det = n} ≃
    {f : BinaryQuadraticForm ℤ // f.discrim = t ^ 2 - 4 * n} where
  toFun M := ⟨ofMatrix M.1, by rw [discrim_ofMatrix, M.2.1, M.2.2]⟩
  invFun f := ⟨!![(t - f.1.b) / 2, -f.1.c; f.1.a, t - (t - f.1.b) / 2], by
    rw [trace_fin_two_of, det_fin_two_of]
    grind [two_mul_ediv_two_of_discrim_eq f.2, discrim_def, discrim]⟩
  left_inv M := by
    obtain ⟨M, rfl, -⟩ := M
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [trace_fin_two, ofMatrix_a, ofMatrix_b, ofMatrix_c, neg_neg, Fin.zero_eta,
        Fin.mk_one, of_apply, cons_val', cons_val_zero, cons_val_one, cons_val_fin_one] <;> omega
  right_inv f := by
    ext <;> simp [sub_sub, ← two_mul, two_mul_ediv_two_of_discrim_eq f.2]

/-- `ofMatrixEquiv t n` sends a matrix `M` to its form `Q_M`. -/
@[simp]
theorem coe_ofMatrixEquiv_apply {t n : ℤ}
    (M : {M : Matrix (Fin 2) (Fin 2) ℤ // M.trace = t ∧ M.det = n}) :
    (ofMatrixEquiv t n M : BinaryQuadraticForm ℤ) = ofMatrix M :=
  (rfl)

/-- The inverse of `ofMatrixEquiv t n` sends `f = ⟨a, b, c⟩` to
`!![(t - b) / 2, -c; a, t - (t - b) / 2]`. -/
@[simp]
theorem coe_ofMatrixEquiv_symm_apply {t n : ℤ}
    (f : {f : BinaryQuadraticForm ℤ // f.discrim = t ^ 2 - 4 * n}) :
    ((ofMatrixEquiv t n).symm f : Matrix (Fin 2) (Fin 2) ℤ) =
      !![(t - f.1.b) / 2, -f.1.c; f.1.a, t - (t - f.1.b) / 2] :=
  (rfl)

end BinaryQuadraticForm

end TauCeti
