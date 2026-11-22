/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.RandomMatrices.GaussianEnsemble.Basic

/-!
# Completeness relations for the coordinate matrices of the Gaussian ensembles

The Gaussian ensemble `TauCeti.Probability.gaussianEnsemble β n g` is real-linear in the array
`g`, so it is the combination `∑ p, g p • E p` of its coordinate matrices
`E p = gaussianEnsemble β n (Pi.single p 1)` (`TauCeti.Probability.gaussianEnsemble_eq_sum_smul`).
Matrix Brownian motion driven by real coordinates `B p` is therefore `H₀ + ∑ p, B p t • E p`, and
every second-order computation for it, such as the quadratic covariation of two linear
functionals or the Itô correction for a function of the matrix, reduces to a sum over `p` of
products of two entries of `E p`. This file evaluates these sums.

Each `E p` is a scaled matrix unit, or a scaled sum or difference of two matrix units. For
`β ≠ 1` and `i < j`,

* `E (i, i) = n^{-1/2} • single i i 1`,
* `E (i, j) = (2n)^{-1/2} • (single i j 1 + single j i 1)`,
* `E (j, i) = I (2n)^{-1/2} • (single i j 1 - single j i 1)`;

for `β = 1` the diagonal coordinate matrices are `(2/n)^{1/2} • single i i 1`, the upper ones are
`n^{-1/2} • (single i j 1 + single j i 1)` and the lower ones vanish, since the real symmetric
ensemble does not read the lower coordinates. The nonzero coordinate matrices are orthonormal for
the real inner product `(β n / 2) Re tr (A B)` on the Hermitian (`β = 2`) or real symmetric
(`β = 1`) matrices, and their completeness relation is

* `∑ p, E p a b • E p = n⁻¹ • single b a 1` for `β ≠ 1`, and
  `∑ p, E p a b • E p = n⁻¹ • (single a b 1 + single b a 1)` for `β = 1`.

Contracting it gives the forms used in stochastic calculus:

* `∑ p, tr (A E p) • E p` is `n⁻¹ • A` for `β ≠ 1` and `n⁻¹ • (A + Aᵀ)` for `β = 1`;
* `∑ p, tr (A E p) * tr (B E p)` is `n⁻¹ tr (A B)` for `β ≠ 1` and `n⁻¹ (tr (A B) + tr (A Bᵀ))`
  for `β = 1`. For Hermitian `A`, `B` and `β = 2`, or real symmetric `A`, `B` and `β = 1`, both
  are `(2 / (β n)) tr (A B)`, the rate of the quadratic covariation of `tr (A H)` and `tr (B H)`;
* `∑ p, (x ⬝ᵥ E p *ᵥ y) * (z ⬝ᵥ E p *ᵥ w)` is `n⁻¹ (x ⬝ᵥ w) (z ⬝ᵥ y)` for `β ≠ 1`, with the
  extra term `n⁻¹ (x ⬝ᵥ z) (y ⬝ᵥ w)` for `β = 1`. Taking `x` and `z` to be the conjugates of
  unit eigenvectors `u`, `v` evaluates the sums `∑ p, ⟪v, E p u⟫ ⟪u, E p v⟫` and
  `∑ p, ⟪u, E p u⟫ ⟪v, E p v⟫`, which enter the drift and the brackets of the eigenvalues of
  matrix Brownian motion through Hadamard's variation formulas;
* `∑ p, E p * M * E p` is `(n⁻¹ tr M) • 1` for `β ≠ 1` and `n⁻¹ • (Mᵀ + tr M • 1)` for `β = 1`.
  For `M = 1` and `β ∈ {1, 2}` its trace `∑ p, tr (E p ^ 2) = n - 1 + 2 / β` is the Itô drift of
  `tr H²`.

## Main results

* `TauCeti.Probability.gaussianEnsemble_eq_sum_smul`: the expansion in coordinate matrices.
* `TauCeti.Probability.gaussianEnsemble_single_of_lt_of_ne_one` and its siblings: the
  coordinate matrices as combinations of matrix units.
* `TauCeti.Probability.sum_gaussianEnsemble_single_apply_smul_of_ne_one` and
  `TauCeti.Probability.sum_gaussianEnsemble_one_single_apply_smul`: the completeness relations.
* `TauCeti.Probability.sum_trace_mul_gaussianEnsemble_single_mul_trace_mul_of_ne_one` and
  `TauCeti.Probability.sum_trace_mul_gaussianEnsemble_one_single_mul_trace_mul`: trace pairings.
* `sum_dotProduct_mulVec_gaussianEnsemble_single_mul_dotProduct_mulVec_of_ne_one` and
  `sum_dotProduct_mulVec_gaussianEnsemble_one_single_mul_dotProduct_mulVec`: pairings with
  vectors.
* `TauCeti.Probability.sum_gaussianEnsemble_single_mul_mul_gaussianEnsemble_single_of_ne_one`
  and its `β = 1` counterpart: the sum `∑ p, E p * M * E p`.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §4.3.1 (proof of Theorem 4.3.2).
* T. Tao, *Topics in Random Matrix Theory*, Graduate Studies in Mathematics 132, AMS (2012),
  §3.1.
-/

public section

open Matrix

namespace TauCeti

namespace Probability

variable {β n : ℕ}

/-- **Expansion in coordinate matrices.** The Gaussian ensemble of an array `g` is the
combination, with coefficients `g p`, of the ensembles `gaussianEnsemble β n (Pi.single p 1)` of
the coordinate arrays. -/
theorem gaussianEnsemble_eq_sum_smul (g : Fin n × Fin n → ℝ) :
    gaussianEnsemble β n g = ∑ p, g p • gaussianEnsemble β n (Pi.single p 1) := by
  have h := map_sum (AddMonoidHom.mk' (gaussianEnsemble β n) gaussianEnsemble_add)
    (fun p ↦ Pi.single p (g p)) Finset.univ
  simp only [AddMonoidHom.mk'_apply, Finset.univ_sum_single] at h
  rw [h]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [← gaussianEnsemble_smul, ← Pi.single_smul, smul_eq_mul, mul_one]

/-! ### The coordinate matrices as combinations of matrix units -/

/-- For `β ≠ 1` the diagonal coordinate `(i, i)` gives `n^{-1/2}` times the matrix unit at
`(i, i)`. -/
@[simp]
theorem gaussianEnsemble_single_self_of_ne_one (hβ : β ≠ 1) (i : Fin n) :
    gaussianEnsemble β n (Pi.single (i, i) 1) = (Real.sqrt n : ℂ)⁻¹ • single i i 1 := by
  ext c d
  simp only [gaussianEnsemble_apply, hβ, ite_false, Pi.single_apply, apply_ite ((↑) : ℝ → ℂ),
    Complex.ofReal_one, Complex.ofReal_zero, Matrix.single_apply, Matrix.smul_apply, Prod.ext_iff,
    smul_eq_mul]
  split_ifs <;> first | ring1 | (exfalso; grind)

/-- For `β ≠ 1` and `i < j` the coordinate `(i, j)` gives the real off-diagonal direction
`(2n)^{-1/2} (single i j 1 + single j i 1)`. -/
@[simp]
theorem gaussianEnsemble_single_of_lt_of_ne_one (hβ : β ≠ 1) {i j : Fin n} (h : i < j) :
    gaussianEnsemble β n (Pi.single (i, j) 1) =
      ((Real.sqrt n : ℂ)⁻¹ / Real.sqrt 2) • (single i j 1 + single j i 1) := by
  ext c d
  simp only [gaussianEnsemble_apply, hβ, ite_false, Pi.single_apply, apply_ite ((↑) : ℝ → ℂ),
    Complex.ofReal_one, Complex.ofReal_zero, Matrix.single_apply, Matrix.smul_apply,
    Matrix.add_apply, Prod.ext_iff, smul_eq_mul]
  split_ifs <;> first | ring1 | (exfalso; grind)

/-- For `β ≠ 1` and `j < i` the coordinate `(i, j)` gives the imaginary off-diagonal direction
`I (2n)^{-1/2} (single j i 1 - single i j 1)`. -/
@[simp]
theorem gaussianEnsemble_single_of_gt_of_ne_one (hβ : β ≠ 1) {i j : Fin n} (h : j < i) :
    gaussianEnsemble β n (Pi.single (i, j) 1) =
      ((Real.sqrt n : ℂ)⁻¹ * Complex.I / Real.sqrt 2) • (single j i 1 - single i j 1) := by
  ext c d
  simp only [gaussianEnsemble_apply, hβ, ite_false, Pi.single_apply, apply_ite ((↑) : ℝ → ℂ),
    Complex.ofReal_one, Complex.ofReal_zero, Matrix.single_apply, Matrix.smul_apply,
    Matrix.sub_apply, Prod.ext_iff, smul_eq_mul]
  split_ifs <;> first | ring1 | (exfalso; grind)

/-- For `β = 1` the diagonal coordinate `(i, i)` gives `√2 / √n` times the matrix unit at
`(i, i)`. -/
@[simp]
theorem gaussianEnsemble_one_single_self (i : Fin n) :
    gaussianEnsemble 1 n (Pi.single (i, i) 1) =
      ((Real.sqrt n : ℂ)⁻¹ * Real.sqrt 2) • single i i 1 := by
  ext c d
  simp only [gaussianEnsemble_apply, ite_true, Pi.single_apply, apply_ite ((↑) : ℝ → ℂ),
    Complex.ofReal_one, Complex.ofReal_zero, Matrix.single_apply, Matrix.smul_apply, Prod.ext_iff,
    smul_eq_mul, Complex.ofReal_mul]
  split_ifs <;> first | ring1 | (exfalso; grind)

/-- For `β = 1` and `i < j` the coordinate `(i, j)` gives
`n^{-1/2} (single i j 1 + single j i 1)`. -/
@[simp]
theorem gaussianEnsemble_one_single_of_lt {i j : Fin n} (h : i < j) :
    gaussianEnsemble 1 n (Pi.single (i, j) 1) =
      (Real.sqrt n : ℂ)⁻¹ • (single i j 1 + single j i 1) := by
  ext c d
  simp only [gaussianEnsemble_apply, ite_true, Pi.single_apply, apply_ite ((↑) : ℝ → ℂ),
    Complex.ofReal_one, Complex.ofReal_zero, Matrix.single_apply, Matrix.smul_apply,
    Matrix.add_apply, Prod.ext_iff, smul_eq_mul, Complex.ofReal_mul]
  split_ifs <;> first | ring1 | (exfalso; grind)

/-- For `β = 1` the strictly lower coordinates are not read: their coordinate matrices vanish. -/
@[simp]
theorem gaussianEnsemble_one_single_of_gt {i j : Fin n} (h : j < i) :
    gaussianEnsemble 1 n (Pi.single (i, j) 1) = 0 := by
  ext c d
  simp only [gaussianEnsemble_apply, ite_true, Pi.single_apply, apply_ite ((↑) : ℝ → ℂ),
    Complex.ofReal_one, Complex.ofReal_zero, Matrix.zero_apply, Prod.ext_iff, Complex.ofReal_mul]
  split_ifs <;> first | ring1 | (exfalso; grind)

/-! ### The completeness relations -/

/-- Summing against the coordinate indicator `p ↦ Pi.single p 1 q` evaluates at `q`. -/
private theorem sum_ofReal_single_apply_smul {M : Type*} [AddCommMonoid M] [Module ℂ M]
    (q : Fin n × Fin n) (f : Fin n × Fin n → M) :
    ∑ p, (((Pi.single p 1 : Fin n × Fin n → ℝ) q : ℝ) : ℂ) • f p = f q := by
  simp [Pi.single_apply, apply_ite ((↑) : ℝ → ℂ), ite_smul]

/-- The square of the diagonal scale `n^{-1/2}` of the ensembles. -/
private theorem inv_sqrt_mul_inv_sqrt (m : ℕ) :
    (Real.sqrt m : ℂ)⁻¹ * (Real.sqrt m : ℂ)⁻¹ = (m : ℂ)⁻¹ := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]
  simp

private theorem sqrt_two_mul_sqrt_two : (Real.sqrt 2 : ℂ) * Real.sqrt 2 = 2 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt zero_le_two]
  norm_num

/-- The square of the off-diagonal real coefficient `(2n)^{-1/2}` of the `β ≠ 1` ensemble. -/
private theorem offDiag_re_mul_self :
    (Real.sqrt n : ℂ)⁻¹ / Real.sqrt 2 * ((Real.sqrt n : ℂ)⁻¹ / Real.sqrt 2) = (n : ℂ)⁻¹ / 2 := by
  rw [div_mul_div_comm, inv_sqrt_mul_inv_sqrt, sqrt_two_mul_sqrt_two]

/-- The square of the off-diagonal imaginary coefficient `I (2n)^{-1/2}` of the `β ≠ 1`
ensemble. -/
private theorem offDiag_im_mul_self :
    (Real.sqrt n : ℂ)⁻¹ * Complex.I / Real.sqrt 2 *
      ((Real.sqrt n : ℂ)⁻¹ * Complex.I / Real.sqrt 2) = -((n : ℂ)⁻¹ / 2) := by
  rw [div_mul_div_comm, mul_mul_mul_comm, inv_sqrt_mul_inv_sqrt, Complex.I_mul_I,
    sqrt_two_mul_sqrt_two]
  ring

/-- **Completeness relation for `β ≠ 1`.** Weighting each coordinate matrix of the Hermitian
ensemble by its `(a, b)` entry and summing gives `n⁻¹` times the matrix unit at `(b, a)`:
`∑ p, E p a b * E p c d = n⁻¹` if `(c, d) = (b, a)` and `0` otherwise. -/
theorem sum_gaussianEnsemble_single_apply_smul_of_ne_one (hβ : β ≠ 1) (a b : Fin n) :
    ∑ p, gaussianEnsemble β n (Pi.single p 1) a b • gaussianEnsemble β n (Pi.single p 1) =
      (n : ℂ)⁻¹ • single b a 1 := by
  -- The `(a, b)` entry of `E p` only sees the coordinates `(a, b)` and `(b, a)`.
  rcases lt_trichotomy a b with hab | rfl | hab
  · calc _ = ∑ p, (((Real.sqrt n : ℂ)⁻¹ / Real.sqrt 2) •
            ((((Pi.single p 1 : Fin n × Fin n → ℝ) (a, b) : ℝ) : ℂ) •
              gaussianEnsemble β n (Pi.single p 1)) +
          ((Real.sqrt n : ℂ)⁻¹ * Complex.I / Real.sqrt 2) •
            ((((Pi.single p 1 : Fin n × Fin n → ℝ) (b, a) : ℝ) : ℂ) •
              gaussianEnsemble β n (Pi.single p 1))) :=
          Finset.sum_congr rfl fun p _ ↦ by
            rw [gaussianEnsemble_apply_of_lt_of_ne_one _ hβ hab, smul_smul, smul_smul, ← add_smul]
            congr 1; ring
      _ = _ := by
          rw [Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.smul_sum,
            sum_ofReal_single_apply_smul, sum_ofReal_single_apply_smul,
            gaussianEnsemble_single_of_lt_of_ne_one hβ hab,
            gaussianEnsemble_single_of_gt_of_ne_one hβ hab, smul_smul, smul_smul,
            offDiag_re_mul_self, offDiag_im_mul_self]
          module
  · calc _ = ∑ p, (Real.sqrt n : ℂ)⁻¹ •
            ((((Pi.single p 1 : Fin n × Fin n → ℝ) (a, a) : ℝ) : ℂ) •
              gaussianEnsemble β n (Pi.single p 1)) :=
          Finset.sum_congr rfl fun p _ ↦ by
            rw [gaussianEnsemble_apply_self_of_ne_one _ hβ, smul_smul]
      _ = _ := by
          rw [← Finset.smul_sum, sum_ofReal_single_apply_smul,
            gaussianEnsemble_single_self_of_ne_one hβ, smul_smul, inv_sqrt_mul_inv_sqrt]
  · calc _ = ∑ p, (((Real.sqrt n : ℂ)⁻¹ / Real.sqrt 2) •
            ((((Pi.single p 1 : Fin n × Fin n → ℝ) (b, a) : ℝ) : ℂ) •
              gaussianEnsemble β n (Pi.single p 1)) -
          ((Real.sqrt n : ℂ)⁻¹ * Complex.I / Real.sqrt 2) •
            ((((Pi.single p 1 : Fin n × Fin n → ℝ) (a, b) : ℝ) : ℂ) •
              gaussianEnsemble β n (Pi.single p 1))) :=
          Finset.sum_congr rfl fun p _ ↦ by
            rw [gaussianEnsemble_apply_of_gt_of_ne_one _ hβ hab, smul_smul, smul_smul, ← sub_smul]
            congr 1; ring
      _ = _ := by
          rw [Finset.sum_sub_distrib, ← Finset.smul_sum, ← Finset.smul_sum,
            sum_ofReal_single_apply_smul, sum_ofReal_single_apply_smul,
            gaussianEnsemble_single_of_lt_of_ne_one hβ hab,
            gaussianEnsemble_single_of_gt_of_ne_one hβ hab, smul_smul, smul_smul,
            offDiag_re_mul_self, offDiag_im_mul_self]
          module

/-- **Completeness relation for `β = 1`.** Weighting each coordinate matrix of the real symmetric
ensemble by its `(a, b)` entry and summing gives `n⁻¹ (single a b 1 + single b a 1)`; on the
diagonal this is `2 / n` times the matrix unit. -/
theorem sum_gaussianEnsemble_one_single_apply_smul (a b : Fin n) :
    ∑ p, gaussianEnsemble 1 n (Pi.single p 1) a b • gaussianEnsemble 1 n (Pi.single p 1) =
      (n : ℂ)⁻¹ • (single a b 1 + single b a 1) := by
  -- The `(a, b)` entry of `E p` only sees the coordinate `(min a b, max a b)`.
  rcases lt_trichotomy a b with hab | rfl | hab
  · calc _ = ∑ p, (Real.sqrt n : ℂ)⁻¹ •
            ((((Pi.single p 1 : Fin n × Fin n → ℝ) (a, b) : ℝ) : ℂ) •
              gaussianEnsemble 1 n (Pi.single p 1)) :=
          Finset.sum_congr rfl fun p _ ↦ by
            rw [gaussianEnsemble_apply_of_lt_of_eq_one _ rfl hab, smul_smul]
      _ = _ := by
          rw [← Finset.smul_sum, sum_ofReal_single_apply_smul,
            gaussianEnsemble_one_single_of_lt hab, smul_smul, inv_sqrt_mul_inv_sqrt]
  · calc _ = ∑ p, ((Real.sqrt n : ℂ)⁻¹ * Real.sqrt 2) •
            ((((Pi.single p 1 : Fin n × Fin n → ℝ) (a, a) : ℝ) : ℂ) •
              gaussianEnsemble 1 n (Pi.single p 1)) :=
          Finset.sum_congr rfl fun p _ ↦ by
            rw [gaussianEnsemble_apply_self_of_eq_one _ rfl, smul_smul, Complex.ofReal_mul,
              mul_assoc]
      _ = _ := by
          rw [← Finset.smul_sum, sum_ofReal_single_apply_smul, gaussianEnsemble_one_single_self,
            smul_smul, mul_mul_mul_comm, inv_sqrt_mul_inv_sqrt, sqrt_two_mul_sqrt_two]
          module
  · calc _ = ∑ p, (Real.sqrt n : ℂ)⁻¹ •
            ((((Pi.single p 1 : Fin n × Fin n → ℝ) (b, a) : ℝ) : ℂ) •
              gaussianEnsemble 1 n (Pi.single p 1)) :=
          Finset.sum_congr rfl fun p _ ↦ by
            rw [gaussianEnsemble_apply_of_gt_of_eq_one _ rfl hab, smul_smul]
      _ = _ := by
          rw [← Finset.smul_sum, sum_ofReal_single_apply_smul,
            gaussianEnsemble_one_single_of_lt hab, smul_smul, inv_sqrt_mul_inv_sqrt, add_comm]

/-- The entrywise form of `sum_gaussianEnsemble_single_apply_smul_of_ne_one`. -/
private theorem sum_gaussianEnsemble_single_apply_mul_apply_of_ne_one (hβ : β ≠ 1)
    (a b c d : Fin n) :
    ∑ p, gaussianEnsemble β n (Pi.single p 1) a b * gaussianEnsemble β n (Pi.single p 1) c d =
      ((n : ℂ)⁻¹ • single b a 1 : Matrix (Fin n) (Fin n) ℂ) c d := by
  rw [← sum_gaussianEnsemble_single_apply_smul_of_ne_one hβ a b, Matrix.sum_apply]
  simp only [Matrix.smul_apply, smul_eq_mul]

/-- The entrywise form of `sum_gaussianEnsemble_one_single_apply_smul`. -/
private theorem sum_gaussianEnsemble_one_single_apply_mul_apply (a b c d : Fin n) :
    ∑ p, gaussianEnsemble 1 n (Pi.single p 1) a b * gaussianEnsemble 1 n (Pi.single p 1) c d =
      ((n : ℂ)⁻¹ • (single a b 1 + single b a 1) : Matrix (Fin n) (Fin n) ℂ) c d := by
  rw [← sum_gaussianEnsemble_one_single_apply_smul a b, Matrix.sum_apply]
  simp only [Matrix.smul_apply, smul_eq_mul]

/-! ### Contracted forms -/

/-- **Reproducing property for `β ≠ 1`.** Expanding a complex matrix `A` against the coordinate
matrices of the Hermitian ensemble through the pairing `tr (A E p)` recovers `n⁻¹ • A`. -/
theorem sum_trace_mul_gaussianEnsemble_single_smul_of_ne_one (hβ : β ≠ 1)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    ∑ p, trace (A * gaussianEnsemble β n (Pi.single p 1)) • gaussianEnsemble β n (Pi.single p 1) =
      (n : ℂ)⁻¹ • A := by
  ext c d
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, trace, diag_apply, Matrix.mul_apply,
    Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (γ := Fin n × Fin n), ← Finset.mul_sum,
    sum_gaussianEnsemble_single_apply_mul_apply_of_ne_one hβ]
  simp [Matrix.single_apply, ite_and, mul_comm]

/-- **Reproducing property for `β = 1`.** Expanding a complex matrix `A` against the coordinate
matrices of the real symmetric ensemble through the pairing `tr (A E p)` gives
`n⁻¹ • (A + Aᵀ)`, which is `(2 / n) • A` when `A` is symmetric. -/
theorem sum_trace_mul_gaussianEnsemble_one_single_smul (A : Matrix (Fin n) (Fin n) ℂ) :
    ∑ p, trace (A * gaussianEnsemble 1 n (Pi.single p 1)) • gaussianEnsemble 1 n (Pi.single p 1) =
      (n : ℂ)⁻¹ • (A + Aᵀ) := by
  ext c d
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, trace, diag_apply, Matrix.mul_apply,
    Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (γ := Fin n × Fin n), ← Finset.mul_sum,
    sum_gaussianEnsemble_one_single_apply_mul_apply]
  simp [Matrix.single_apply, ite_and, mul_add, Finset.sum_add_distrib]
  ring

/-- **Trace pairings for `β ≠ 1`.** `∑ p, tr (A E p) tr (B E p) = n⁻¹ tr (A B)` for all complex
matrices `A` and `B`. For Hermitian `A` and `B` both traces are real, and this is the rate
`(2 / (β n)) tr (A B)` at `β = 2` of the quadratic covariation of `tr (A H)` and `tr (B H)`. -/
theorem sum_trace_mul_gaussianEnsemble_single_mul_trace_mul_of_ne_one (hβ : β ≠ 1)
    (A B : Matrix (Fin n) (Fin n) ℂ) :
    ∑ p, trace (A * gaussianEnsemble β n (Pi.single p 1)) *
        trace (B * gaussianEnsemble β n (Pi.single p 1)) =
      (n : ℂ)⁻¹ * trace (A * B) := by
  have h := congrArg (fun X ↦ trace (B * X))
    (sum_trace_mul_gaussianEnsemble_single_smul_of_ne_one hβ A)
  simp only [Matrix.mul_sum, Matrix.mul_smul, trace_sum, trace_smul, smul_eq_mul] at h
  rw [trace_mul_comm B A] at h
  simpa only [mul_comm (trace (A * _))] using h

/-- **Trace pairings for `β = 1`.** `∑ p, tr (A E p) tr (B E p) = n⁻¹ (tr (A B) + tr (A Bᵀ))`
for all complex matrices `A` and `B`. For real symmetric `A` and `B` this is the rate
`(2 / (β n)) tr (A B)` at `β = 1` of the quadratic covariation of `tr (A H)` and `tr (B H)`. -/
theorem sum_trace_mul_gaussianEnsemble_one_single_mul_trace_mul
    (A B : Matrix (Fin n) (Fin n) ℂ) :
    ∑ p, trace (A * gaussianEnsemble 1 n (Pi.single p 1)) *
        trace (B * gaussianEnsemble 1 n (Pi.single p 1)) =
      (n : ℂ)⁻¹ * (trace (A * B) + trace (A * Bᵀ)) := by
  have h := congrArg (fun X ↦ trace (B * X)) (sum_trace_mul_gaussianEnsemble_one_single_smul A)
  simp only [Matrix.mul_sum, Matrix.mul_smul, trace_sum, trace_smul, smul_eq_mul, Matrix.mul_add,
    trace_add] at h
  rw [trace_mul_comm B A, ← trace_transpose (B * Aᵀ), transpose_mul, transpose_transpose] at h
  simpa only [mul_comm (trace (A * _))] using h

/-- **Pairings with vectors for `β ≠ 1`.**
`∑ p, (x ⬝ᵥ E p *ᵥ y) (z ⬝ᵥ E p *ᵥ w) = n⁻¹ (x ⬝ᵥ w) (z ⬝ᵥ y)`. For unit vectors `u`, `v`,
`(x, y, z, w) = (star v, u, star u, v)` gives `∑ p, ⟪v, E p u⟫ ⟪u, E p v⟫ = n⁻¹`, and
`(star u, u, star v, v)` gives `∑ p, ⟪u, E p u⟫ ⟪v, E p v⟫ = n⁻¹ |⟪u, v⟫|²`. -/
theorem sum_dotProduct_mulVec_gaussianEnsemble_single_mul_dotProduct_mulVec_of_ne_one
    (hβ : β ≠ 1) (x y z w : Fin n → ℂ) :
    ∑ p, (x ⬝ᵥ gaussianEnsemble β n (Pi.single p 1) *ᵥ y) *
        (z ⬝ᵥ gaussianEnsemble β n (Pi.single p 1) *ᵥ w) =
      (n : ℂ)⁻¹ * ((x ⬝ᵥ w) * (z ⬝ᵥ y)) := by
  have h (u v : Fin n → ℂ) (M : Matrix (Fin n) (Fin n) ℂ) :
      u ⬝ᵥ M *ᵥ v = trace (vecMulVec v u * M) := by
    rw [vecMulVec_mul, trace_vecMulVec, dotProduct_mulVec, dotProduct_comm]
  simp_rw [h]
  rw [sum_trace_mul_gaussianEnsemble_single_mul_trace_mul_of_ne_one hβ, vecMulVec_mul_vecMulVec,
    trace_vecMulVec, dotProduct_smul, smul_eq_mul, dotProduct_comm y z]

/-- **Pairings with vectors for `β = 1`.** `∑ p, (x ⬝ᵥ E p *ᵥ y) (z ⬝ᵥ E p *ᵥ w)` is
`n⁻¹ ((x ⬝ᵥ w) (z ⬝ᵥ y) + (x ⬝ᵥ z) (y ⬝ᵥ w))`. For real vectors `u`, `v`,
`(x, y, z, w) = (v, u, v, u)` gives `∑ p, ⟪v, E p u⟫² = n⁻¹ (⟪u, v⟫² + ‖u‖² ‖v‖²)`, and
`(u, u, v, v)` gives `∑ p, ⟪u, E p u⟫ ⟪v, E p v⟫ = (2 / n) ⟪u, v⟫²`. -/
theorem sum_dotProduct_mulVec_gaussianEnsemble_one_single_mul_dotProduct_mulVec
    (x y z w : Fin n → ℂ) :
    ∑ p, (x ⬝ᵥ gaussianEnsemble 1 n (Pi.single p 1) *ᵥ y) *
        (z ⬝ᵥ gaussianEnsemble 1 n (Pi.single p 1) *ᵥ w) =
      (n : ℂ)⁻¹ * ((x ⬝ᵥ w) * (z ⬝ᵥ y) + (x ⬝ᵥ z) * (y ⬝ᵥ w)) := by
  have h (u v : Fin n → ℂ) (M : Matrix (Fin n) (Fin n) ℂ) :
      u ⬝ᵥ M *ᵥ v = trace (vecMulVec v u * M) := by
    rw [vecMulVec_mul, trace_vecMulVec, dotProduct_mulVec, dotProduct_comm]
  simp_rw [h]
  rw [sum_trace_mul_gaussianEnsemble_one_single_mul_trace_mul, transpose_vecMulVec,
    vecMulVec_mul_vecMulVec, vecMulVec_mul_vecMulVec, trace_vecMulVec, trace_vecMulVec,
    dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul, dotProduct_comm y z]

/-- **The sum `∑ p, E p * M * E p` for `β ≠ 1`** is the scalar matrix `(n⁻¹ tr M) • 1`. -/
theorem sum_gaussianEnsemble_single_mul_mul_gaussianEnsemble_single_of_ne_one (hβ : β ≠ 1)
    (M : Matrix (Fin n) (Fin n) ℂ) :
    ∑ p, gaussianEnsemble β n (Pi.single p 1) * M * gaussianEnsemble β n (Pi.single p 1) =
      ((n : ℂ)⁻¹ * trace M) • 1 := by
  ext a d
  simp only [Matrix.sum_apply, Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (γ := Fin n × Fin n)]
  have h (b c : Fin n) : ∑ p, gaussianEnsemble β n (Pi.single p 1) a b * M b c *
      gaussianEnsemble β n (Pi.single p 1) c d =
      M b c * ∑ p, gaussianEnsemble β n (Pi.single p 1) a b *
        gaussianEnsemble β n (Pi.single p 1) c d := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ ↦ by ring
  simp_rw [h, sum_gaussianEnsemble_single_apply_mul_apply_of_ne_one hβ]
  simp [Matrix.single_apply, Matrix.one_apply, ite_and, trace, Finset.mul_sum, mul_comm]

/-- **The sum `∑ p, E p * M * E p` for `β = 1`** is `n⁻¹ • (Mᵀ + tr M • 1)`. -/
theorem sum_gaussianEnsemble_one_single_mul_mul_gaussianEnsemble_one_single
    (M : Matrix (Fin n) (Fin n) ℂ) :
    ∑ p, gaussianEnsemble 1 n (Pi.single p 1) * M * gaussianEnsemble 1 n (Pi.single p 1) =
      (n : ℂ)⁻¹ • (Mᵀ + trace M • 1) := by
  ext a d
  simp only [Matrix.sum_apply, Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (γ := Fin n × Fin n)]
  have h (b c : Fin n) : ∑ p, gaussianEnsemble 1 n (Pi.single p 1) a b * M b c *
      gaussianEnsemble 1 n (Pi.single p 1) c d =
      M b c * ∑ p, gaussianEnsemble 1 n (Pi.single p 1) a b *
        gaussianEnsemble 1 n (Pi.single p 1) c d := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ ↦ by ring
  simp_rw [h, sum_gaussianEnsemble_one_single_apply_mul_apply]
  simp [Matrix.single_apply, Matrix.one_apply, ite_and, trace, Finset.mul_sum, mul_add,
    Finset.sum_add_distrib, mul_comm]

end Probability

end TauCeti
