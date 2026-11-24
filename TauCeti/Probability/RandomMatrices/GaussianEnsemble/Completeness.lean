/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.RandomMatrices.GaussianEnsemble.Basic
import TauCeti.Analysis.Complex.Sqrt
import TauCeti.LinearAlgebra.Matrix.Trace.Contraction

/-!
# Completeness relations for the coordinate matrices of the Gaussian ensembles

The Gaussian ensemble `TauCeti.Probability.gaussianEnsemble β n g` is real-linear in the array
`g`, so it is the combination `∑ p, g p • E p` of its coordinate matrices
`E p = gaussianEnsemble β n (Pi.single p 1)` (`TauCeti.Probability.gaussianEnsemble_eq_sum_smul`
in `GaussianEnsemble.Basic`).
Matrix Brownian motion driven by real coordinates `B p` is therefore `H₀ + ∑ p, B p t • E p`, and
every second-order computation for it, such as the quadratic covariation of two linear
functionals or the Itô correction for a function of the matrix, reduces to a sum over `p` of
products of two entries of `E p`. This file evaluates these sums.

Each `E p` is a scaled matrix unit, or a scaled sum or difference of two matrix units
(`TauCeti.Probability.gaussianEnsemble_single_of_lt_of_ne_one` and its siblings in
`GaussianEnsemble.Basic`). For `β ≠ 1` and `i < j`,

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

* `TauCeti.Probability.sum_gaussianEnsemble_single_apply_mul_apply_of_ne_one` and
  `TauCeti.Probability.sum_gaussianEnsemble_one_single_apply_mul_apply`: the entry covariances
  `∑ p, E p a b * E p c d`.
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

/-! ### The completeness relations -/

/-- **Entry covariance for `β ≠ 1`.** For the coordinate matrices `E p` of the Hermitian
ensemble, `∑ p, E p a b * E p c d` is `n⁻¹` when `(c, d) = (b, a)` and `0` otherwise: the
`(a, b)` entry of `E p` only sees the coordinates `(a, b)` and `(b, a)`. -/
theorem sum_gaussianEnsemble_single_apply_mul_apply_of_ne_one (hβ : β ≠ 1) (a b c d : Fin n) :
    ∑ p, gaussianEnsemble β n (Pi.single p 1) a b * gaussianEnsemble β n (Pi.single p 1) c d =
      if b = c ∧ a = d then (n : ℂ)⁻¹ else 0 := by
  have hn := Complex.mul_self_ofReal_sqrt (Nat.cast_nonneg (α := ℝ) n)
  have h2 := Complex.mul_self_ofReal_sqrt (zero_le_two (α := ℝ))
  push_cast at hn h2
  rcases lt_trichotomy a b with hab | hab | hab <;>
    simp [Pi.single_apply, apply_ite ((↑) : ℝ → ℂ), mul_add, add_mul, add_div, sub_div, mul_sub,
      sub_mul, ite_div, ite_mul, mul_ite, Finset.sum_add_distrib, Finset.sum_sub_distrib, hβ, hab,
      Matrix.single_apply] <;>
    split_ifs <;> grind [Complex.I_sq]

/-- **Entry covariance for `β = 1`.** For the coordinate matrices `E p` of the real symmetric
ensemble, `∑ p, E p a b * E p c d` is `n⁻¹` times the number of the conditions
`(c, d) = (a, b)` and `(c, d) = (b, a)` that hold: the `(a, b)` entry of `E p` only sees the
coordinate `(min a b, max a b)`. -/
theorem sum_gaussianEnsemble_one_single_apply_mul_apply (a b c d : Fin n) :
    ∑ p, gaussianEnsemble 1 n (Pi.single p 1) a b * gaussianEnsemble 1 n (Pi.single p 1) c d =
      (n : ℂ)⁻¹ * ((if a = c ∧ b = d then 1 else 0) + if b = c ∧ a = d then 1 else 0) := by
  have hn := Complex.mul_self_ofReal_sqrt (Nat.cast_nonneg (α := ℝ) n)
  have h2 := Complex.mul_self_ofReal_sqrt (zero_le_two (α := ℝ))
  push_cast at hn h2
  rcases lt_trichotomy a b with hab | hab | hab <;>
    simp [Pi.single_apply, apply_ite ((↑) : ℝ → ℂ), mul_add, ite_mul, mul_ite, hab,
      Matrix.single_apply] <;>
    split_ifs <;> grind

/-- **Completeness relation for `β ≠ 1`.** Weighting each coordinate matrix of the Hermitian
ensemble by its `(a, b)` entry and summing gives `n⁻¹` times the matrix unit at `(b, a)`. -/
theorem sum_gaussianEnsemble_single_apply_smul_of_ne_one (hβ : β ≠ 1) (a b : Fin n) :
    ∑ p, gaussianEnsemble β n (Pi.single p 1) a b • gaussianEnsemble β n (Pi.single p 1) =
      (n : ℂ)⁻¹ • single b a 1 := by
  ext c d
  simp [Matrix.sum_apply, sum_gaussianEnsemble_single_apply_mul_apply_of_ne_one hβ,
    Matrix.single_apply]

/-- **Completeness relation for `β = 1`.** Weighting each coordinate matrix of the real symmetric
ensemble by its `(a, b)` entry and summing gives `n⁻¹ (single a b 1 + single b a 1)`; on the
diagonal this is `2 / n` times the matrix unit. -/
theorem sum_gaussianEnsemble_one_single_apply_smul (a b : Fin n) :
    ∑ p, gaussianEnsemble 1 n (Pi.single p 1) a b • gaussianEnsemble 1 n (Pi.single p 1) =
      (n : ℂ)⁻¹ • (single a b 1 + single b a 1) := by
  ext c d
  simp [Matrix.sum_apply, sum_gaussianEnsemble_one_single_apply_mul_apply, Matrix.single_apply]

/-! ### Contracted forms -/

/-- **Reproducing property for `β ≠ 1`.** Expanding a complex matrix `A` against the coordinate
matrices of the Hermitian ensemble through the pairing `tr (A E p)` recovers `n⁻¹ • A`. -/
theorem sum_trace_mul_gaussianEnsemble_single_smul_of_ne_one (hβ : β ≠ 1)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    ∑ p, trace (A * gaussianEnsemble β n (Pi.single p 1)) • gaussianEnsemble β n (Pi.single p 1) =
      (n : ℂ)⁻¹ • A := by
  ext c d
  rw [sum_trace_mul_smul_apply]
  simp [sum_gaussianEnsemble_single_apply_mul_apply_of_ne_one hβ, ite_and, mul_comm]

/-- **Reproducing property for `β = 1`.** Expanding a complex matrix `A` against the coordinate
matrices of the real symmetric ensemble through the pairing `tr (A E p)` gives
`n⁻¹ • (A + Aᵀ)`, which is `(2 / n) • A` when `A` is symmetric. -/
theorem sum_trace_mul_gaussianEnsemble_one_single_smul (A : Matrix (Fin n) (Fin n) ℂ) :
    ∑ p, trace (A * gaussianEnsemble 1 n (Pi.single p 1)) • gaussianEnsemble 1 n (Pi.single p 1) =
      (n : ℂ)⁻¹ • (A + Aᵀ) := by
  ext c d
  rw [sum_trace_mul_smul_apply]
  simp [sum_gaussianEnsemble_one_single_apply_mul_apply, ite_and, mul_add, Finset.sum_add_distrib]
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
  simp_rw [dotProduct_mulVec_eq_trace_vecMulVec_mul]
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
  simp_rw [dotProduct_mulVec_eq_trace_vecMulVec_mul]
  rw [sum_trace_mul_gaussianEnsemble_one_single_mul_trace_mul, transpose_vecMulVec,
    vecMulVec_mul_vecMulVec, vecMulVec_mul_vecMulVec, trace_vecMulVec, trace_vecMulVec,
    dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul, dotProduct_comm y z]

/-- **The sum `∑ p, E p * M * E p` for `β ≠ 1`** is the scalar matrix `(n⁻¹ tr M) • 1`. -/
theorem sum_gaussianEnsemble_single_mul_mul_gaussianEnsemble_single_of_ne_one (hβ : β ≠ 1)
    (M : Matrix (Fin n) (Fin n) ℂ) :
    ∑ p, gaussianEnsemble β n (Pi.single p 1) * M * gaussianEnsemble β n (Pi.single p 1) =
      ((n : ℂ)⁻¹ * trace M) • 1 := by
  ext a d
  rw [sum_mul_mul_apply]
  simp_rw [sum_gaussianEnsemble_single_apply_mul_apply_of_ne_one hβ]
  simp [Matrix.one_apply, ite_and, trace, Finset.mul_sum, mul_comm]

/-- **The sum `∑ p, E p * M * E p` for `β = 1`** is `n⁻¹ • (Mᵀ + tr M • 1)`. -/
theorem sum_gaussianEnsemble_one_single_mul_mul_gaussianEnsemble_one_single
    (M : Matrix (Fin n) (Fin n) ℂ) :
    ∑ p, gaussianEnsemble 1 n (Pi.single p 1) * M * gaussianEnsemble 1 n (Pi.single p 1) =
      (n : ℂ)⁻¹ • (Mᵀ + trace M • 1) := by
  ext a d
  rw [sum_mul_mul_apply]
  simp_rw [sum_gaussianEnsemble_one_single_apply_mul_apply]
  simp [Matrix.one_apply, ite_and, trace, Finset.mul_sum, mul_add,
    Finset.sum_add_distrib, mul_comm]

end Probability

end TauCeti
