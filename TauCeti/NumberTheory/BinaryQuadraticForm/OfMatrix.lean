/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.LinearAlgebra.Matrix.Trace
public import TauCeti.NumberTheory.BinaryQuadraticForm.Basic

/-!
# The binary quadratic form of a `2 × 2` matrix

To a matrix `M = !![a, b; c, d]` we attach the binary quadratic form
`Q_M = c x² + (d - a) x y - b y²`, whose value at `v = (x, y)` is the determinant of the matrix
with columns `v` and `M v`. Its roots are the fixed points of `M` acting by Möbius
transformations, its discriminant is `tr(M)² - 4 det M`, and conjugating `M` by `γ ∈ SL(2, R)`
acts on `Q_M` by the action `γ • f = f ∘ γ⁻¹` of `TauCeti.BinaryQuadraticForm.Basic`.

Over `ℤ`, `M ↦ Q_M` is a bijection between the matrices of trace `t` and determinant `n` and the
forms of discriminant `t² - 4 n`: the form determines `c`, `b` and `d - a`, the trace determines
`a + d`, and `b² - 4 a c = t² - 4 n` forces `d - a ≡ t (mod 2)`. This is the correspondence through
which the Eichler–Selberg trace formula counts the elliptic conjugacy classes of matrices of
determinant `n` by the Hurwitz class numbers `H(4 n - t²)`.

## Main definitions

* `TauCeti.BinaryQuadraticForm.ofMatrix`: the form `Q_M = c x² + (d - a) x y - b y²`.
* `TauCeti.BinaryQuadraticForm.traceDetEquiv`: for `t n : ℤ`, the bijection `M ↦ Q_M` from the
  integer matrices of trace `t` and determinant `n` to the forms of discriminant `t² - 4 n`.

## Main results

* `TauCeti.BinaryQuadraticForm.discrim_ofMatrix`: the discriminant of `Q_M` is
  `tr(M)² - 4 det M`.
* `TauCeti.BinaryQuadraticForm.ofMatrix_conj`: `Q_{γ M γ⁻¹} = γ • Q_M` for `γ ∈ SL(2, R)`.

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

/-- The binary quadratic form `Q_M = c x² + (d - a) x y - b y²` of the matrix `M = !![a, b; c, d]`.
Its value at `v = (x, y)` is the determinant of the matrix with columns `v` and `M v`. -/
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
  simp [discrim_def, discrim, trace_fin_two, det_fin_two]
  ring

/-- Conjugation by `γ ∈ SL(2, R)` acts on `Q_M` as `γ` acts on forms: `Q_{γ M γ⁻¹} = γ • Q_M`. -/
theorem ofMatrix_conj (γ : SL(2, R)) (M : Matrix (Fin 2) (Fin 2) R) :
    ofMatrix (γ * M * γ⁻¹ : Matrix (Fin 2) (Fin 2) R) = γ • ofMatrix M := by
  ext <;> simp [SpecialLinearGroup.coe_inv, adjugate_fin_two, mul_apply, Fin.sum_univ_two] <;> ring

/-- If `b² - 4 a c = t² - 4 n` then `b ≡ t (mod 2)`. -/
private theorem two_dvd_sub_b {f : BinaryQuadraticForm ℤ} {t n : ℤ}
    (hf : f.discrim = t ^ 2 - 4 * n) : 2 ∣ t - f.b := by
  have : Even (t ^ 2 - f.b ^ 2) := ⟨2 * (n - f.a * f.c), by
    simp only [discrim_def, discrim] at hf
    linear_combination -hf⟩
  exact (by simpa [Int.even_sub, Int.even_pow] using this : Even (t - f.b)).two_dvd

/-- For `t n : ℤ`, `M ↦ Q_M` is a bijection from the integer matrices of trace `t` and determinant
`n` to the integral forms of discriminant `t² - 4 n`. The inverse sends `f = ⟨a, b, c⟩` to
`!![(t - b) / 2, -c; a, (t + b) / 2]`, where `b ≡ t (mod 2)` since `b² - 4 a c = t² - 4 n`. -/
def traceDetEquiv (t n : ℤ) :
    {M : Matrix (Fin 2) (Fin 2) ℤ // M.trace = t ∧ M.det = n} ≃
      {f : BinaryQuadraticForm ℤ // f.discrim = t ^ 2 - 4 * n} where
  toFun M := ⟨ofMatrix M.1, by rw [discrim_ofMatrix, M.2.1, M.2.2]⟩
  invFun f := ⟨!![(t - f.1.b) / 2, -f.1.c; f.1.a, t - (t - f.1.b) / 2], by
    obtain ⟨⟨a, b, c⟩, hf⟩ := f
    have h2 : 2 * ((t - b) / 2) = t - b := Int.mul_ediv_cancel' (two_dvd_sub_b hf)
    refine ⟨by simp [trace_fin_two_of], ?_⟩
    rw [det_fin_two_of]
    refine mul_left_cancel₀ (four_ne_zero (α := ℤ)) ?_
    simp only [discrim_def, discrim] at hf
    linear_combination (t + b - 2 * ((t - b) / 2)) * h2 - hf⟩
  left_inv M := by
    obtain ⟨M, ht, -⟩ := M
    ext i j
    fin_cases i <;> fin_cases j <;> simp [← ht, trace_fin_two] <;> omega
  right_inv f := by
    obtain ⟨⟨a, b, c⟩, hf⟩ := f
    have h2 : 2 * ((t - b) / 2) = t - b := Int.mul_ediv_cancel' (two_dvd_sub_b hf)
    ext <;> simp
    omega

end BinaryQuadraticForm

end TauCeti
