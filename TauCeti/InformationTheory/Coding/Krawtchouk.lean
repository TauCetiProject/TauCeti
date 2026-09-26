/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.Binomial
public import TauCeti.InformationTheory.Coding.MacWilliams.Basic

/-!
# The Krawtchouk form of the MacWilliams identity

The integer `krawtchouk q n w j` is the q-ary Krawtchouk value `K_w(j)` for
words of length `n`. For `j ≤ n`, its generating function is
`(1 + (q - 1) Z)^(n-j) (1 - Z)^j`. Taking coefficients in the MacWilliams identity gives

`#C * A_w(C⊥) = ∑ j, A_j(C) * krawtchouk q n w j`.

Thus the weight distribution of the dual can be computed directly from that of the code,
using an explicit finite sum of binomial coefficients. The coefficient identity is integral;
the normalized version has rational coefficients.

## References

F. J. MacWilliams and N. J. A. Sloane, *The Theory of Error-Correcting Codes*,
North-Holland (1977), Chapter 5, §2; W. C. Huffman and V. Pless,
*Fundamentals of Error-Correcting Codes*, Cambridge University Press (2003), §7.2.
-/

public section

namespace TauCeti

open Finset Polynomial

/-- The q-ary Krawtchouk value `K_w(j)` for length `n`, as an integer binomial sum.
The coding-theoretic range is `2 ≤ q` and `j ≤ n`; the sum is defined for all indices. -/
def krawtchouk (q n w j : ℕ) : ℤ :=
  ∑ a ∈ range (w + 1),
    (-1 : ℤ) ^ a * (q - 1 : ℤ) ^ (w - a) * (j.choose a : ℤ) *
      ((n - j).choose (w - a) : ℤ)

theorem krawtchouk_def (q n w j : ℕ) :
    krawtchouk q n w j = ∑ a ∈ range (w + 1),
      (-1 : ℤ) ^ a * (q - 1 : ℤ) ^ (w - a) * (j.choose a : ℤ) *
        ((n - j).choose (w - a) : ℤ) := (rfl)

/-- The degree-zero Krawtchouk value is one. -/
@[simp]
theorem krawtchouk_zero (q n j : ℕ) : krawtchouk q n 0 j = 1 := by
  simp [krawtchouk_def]

/-- The generating-function characterization of the Krawtchouk values. -/
@[simp]
theorem coeff_krawtchouk_generating (q n w j : ℕ) :
    (((1 + (q - 1 : Polynomial ℤ) * X) ^ (n - j) * (1 - X) ^ j : Polynomial ℤ).coeff w) =
      krawtchouk q n w j := by
  rw [mul_comm, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    krawtchouk_def]
  refine sum_congr rfl fun a _ ↦ ?_
  have hneg : (1 - X : Polynomial ℤ) = C 1 + C (-1) * X := by simp [sub_eq_add_neg]
  rw [hneg, coeff_C_add_C_mul_X_pow]
  have hpos : (1 + (q - 1 : Polynomial ℤ) * X) = C 1 + C (q - 1 : ℤ) * X := by
    simp
  rw [hpos, coeff_C_add_C_mul_X_pow]
  simp only [one_pow, mul_one]
  ring

/-- Krawtchouk values above the length vanish on the range of word weights. -/
@[simp]
theorem krawtchouk_eq_zero_of_lt (q n w j : ℕ) (hj : j ≤ n) (hw : n < w) :
    krawtchouk q n w j = 0 := by
  rw [krawtchouk_def]
  apply sum_eq_zero
  intro a _
  by_cases hja : j < a
  · simp [Nat.choose_eq_zero_of_lt hja]
  · have hnj : n - j < w - a := by omega
    simp [Nat.choose_eq_zero_of_lt hnj]

variable {ι F : Type*} [Fintype ι] [Field F] [Finite F] [DecidableEq F]

/-- The coefficient form of the MacWilliams identity, without division. -/
theorem natCard_mul_weightDistribution_euclideanDual (w : ℕ) (C : Submodule F (ι → F)) :
    (Nat.card C : ℤ) * (Submodule.euclideanDual C : Set (ι → F)).weightDistribution w =
      ∑ j ∈ range (Fintype.card ι + 1), (C : Set (ι → F)).weightDistribution j *
        krawtchouk (Nat.card F) (Fintype.card ι) w j := by
  have h := congrArg (MvPolynomial.aeval ![1, (X : Polynomial ℤ)])
    (Submodule.natCard_mul_weightEnumerator_euclideanDual C)
  rw [map_mul, map_natCast, Set.aeval_weightEnumerator] at h
  have hvars : (fun i ↦ MvPolynomial.aeval ![1, (X : Polynomial ℤ)]
      (![MvPolynomial.X 0 + (Nat.card F - 1 : MvPolynomial (Fin 2) ℤ) * MvPolynomial.X 1,
        MvPolynomial.X 0 - MvPolynomial.X 1] i)) =
      ![1 + (Nat.card F - 1 : Polynomial ℤ) * X, 1 - X] := by
    funext i
    fin_cases i <;> simp
  rw [MvPolynomial.comp_aeval_apply, hvars, Set.weightEnumerator_def] at h
  simp only [map_sum, map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
    Matrix.cons_val_zero, Matrix.cons_val_one] at h
  have hc := congrArg (fun p : Polynomial ℤ ↦ p.coeff w) h
  simpa only [coeff_natCast_mul, Set.coeff_weightPolynomial, finsetSum_coeff,
    Polynomial.algebraMap_eq, mul_assoc, coeff_C_mul, coeff_krawtchouk_generating] using hc

/-- The dual weight distribution is the normalized Krawtchouk transform of the original
weight distribution. The denominator is nonzero since every linear code contains zero. -/
theorem weightDistribution_euclideanDual_eq_sum_div (w : ℕ) (C : Submodule F (ι → F)) :
    ((Submodule.euclideanDual C : Set (ι → F)).weightDistribution w : ℚ) =
      (∑ j ∈ range (Fintype.card ι + 1),
        ((C : Set (ι → F)).weightDistribution j : ℚ) *
          (krawtchouk (Nat.card F) (Fintype.card ι) w j : ℚ)) / Nat.card C := by
  have hcard : (Nat.card C : ℚ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := C)).ne'
  apply (eq_div_iff hcard).mpr
  rw [mul_comm]
  exact_mod_cast natCard_mul_weightDistribution_euclideanDual w C

end TauCeti
