/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.RandomMatrices.GaussianEnsemble.Basic
import TauCeti.LinearAlgebra.Matrix.Trace.Contraction
import TauCeti.Probability.RandomMatrices.GaussianEnsemble.Covariance

/-!
# Completeness relations for the coordinate matrices of the Gaussian ensembles

The Gaussian ensemble `TauCeti.Probability.gaussianEnsemble β n g` is real-linear in the array
`g`, so it is the combination `∑ p, g p • E p` of its coordinate matrices
`E p = gaussianEnsemble β n (Pi.single p 1)`
(`TauCeti.Probability.gaussianEnsemble_eq_sum_smul_single` in `GaussianEnsemble.Basic`).
Matrix Brownian motion driven by real coordinates `B p` is therefore `H₀ + ∑ p, B p t • E p`, and
every second-order computation for it, such as the Itô correction for a function of the matrix,
reduces to a sum over `p` of products of two entries of `E p`. The entry covariances
`∑ p, E p a b * E p c d` and the scalar pairings derived from them are in
`GaussianEnsemble.Covariance`; this file evaluates the matrix-valued sums.

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

Contracting it gives the matrix-valued forms used in stochastic calculus:

* `∑ p, tr (A E p) • E p` is `n⁻¹ • A` for `β ≠ 1` and `n⁻¹ • (A + Aᵀ)` for `β = 1`;
* `∑ p, E p * M * E p` is `(n⁻¹ tr M) • 1` for `β ≠ 1` and `n⁻¹ • (Mᵀ + tr M • 1)` for `β = 1`.
  For `M = 1` and `β ∈ {1, 2}` its trace `∑ p, tr (E p ^ 2) = n - 1 + 2 / β` is the Itô drift of
  `tr H²`.

## Main results

* `TauCeti.Probability.sum_gaussianEnsemble_single_apply_smul_of_ne_one` and
  `TauCeti.Probability.sum_gaussianEnsemble_one_single_apply_smul`: the completeness relations.
* `TauCeti.Probability.sum_trace_mul_gaussianEnsemble_single_smul_of_ne_one` and
  `TauCeti.Probability.sum_trace_mul_gaussianEnsemble_one_single_smul`: the reproducing property.
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

/-- **Completeness relation for `β ≠ 1`.** Weighting each coordinate matrix of the Hermitian
ensemble by its `(a, b)` entry and summing gives `n⁻¹` times the matrix unit at `(b, a)`. -/
theorem sum_gaussianEnsemble_single_apply_smul_of_ne_one (hβ : β ≠ 1) (a b : Fin n) :
    ∑ p, gaussianEnsemble β n (Pi.single p 1) a b • gaussianEnsemble β n (Pi.single p 1) =
      (n : ℂ)⁻¹ • single b a 1 := by
  ext c d
  simp [Matrix.sum_apply, sum_gaussianEnsemble_single_apply_mul_apply_of_ne_one hβ,
    Matrix.single_apply, and_comm]

/-- **Completeness relation for `β = 1`.** Weighting each coordinate matrix of the real symmetric
ensemble by its `(a, b)` entry and summing gives `n⁻¹ (single a b 1 + single b a 1)`; on the
diagonal this is `2 / n` times the matrix unit. -/
theorem sum_gaussianEnsemble_one_single_apply_smul (a b : Fin n) :
    ∑ p, gaussianEnsemble 1 n (Pi.single p 1) a b • gaussianEnsemble 1 n (Pi.single p 1) =
      (n : ℂ)⁻¹ • (single a b 1 + single b a 1) := by
  ext c d
  simp [Matrix.sum_apply, sum_gaussianEnsemble_one_single_apply_mul_apply, Matrix.single_apply,
    and_comm, add_comm]

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
    Finset.sum_add_distrib, mul_comm, add_comm]

end Probability

end TauCeti
