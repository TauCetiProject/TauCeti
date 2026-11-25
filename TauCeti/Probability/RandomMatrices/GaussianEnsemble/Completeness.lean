/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.RandomMatrices.GaussianEnsemble.Basic
import TauCeti.Data.Matrix.Mul
import TauCeti.Probability.RandomMatrices.GaussianEnsemble.Covariance

/-!
# The contracted completeness relation for the coordinate matrices of the Gaussian ensembles

The Gaussian ensemble `TauCeti.Probability.gaussianEnsemble β n g` is real-linear in the array
`g`, so it is the combination `∑ p, g p • E p` of its coordinate matrices
`E p = gaussianEnsemble β n (Pi.single p 1)`
(`TauCeti.Probability.gaussianEnsemble_eq_sum_smul_single` in `GaussianEnsemble.Basic`).
Matrix Brownian motion driven by real coordinates `B p` is therefore `H₀ + ∑ p, B p t • E p`, and
the Itô correction of a smooth function `F` of the matrix is `½ ∑ p, D²F (H) [E p, E p]`. The
entry covariances `∑ p, E p a b * E p c d` and the scalar pairings derived from them are in
`GaussianEnsemble.Covariance`. This file contracts the entry covariances into the matrix sum

* `∑ p, E p * M * E p = (n⁻¹ tr M) • 1` for `β ≠ 1`, and
  `∑ p, E p * M * E p = n⁻¹ • (Mᵀ + tr M • 1)` for `β = 1`.

This is the sum that evaluates the Itô drift of an eigenvalue in its projector form. When `H` has
distinct eigenvalues `λⱼ` with spectral projectors `Pⱼ`, write `Rᵢ = ∑_{j ≠ i} (λᵢ - λⱼ)⁻¹ Pⱼ` for
the reduced resolvent at `λᵢ`; the second derivative is `D²λᵢ (H) [A, A] = 2 tr (Pᵢ A Rᵢ A)`.
The drift of `λᵢ` is therefore `tr (Pᵢ ∑ p, E p * Rᵢ * E p)`. For `β ≠ 1` it equals
`n⁻¹ tr Rᵢ = n⁻¹ ∑_{j ≠ i} (λᵢ - λⱼ)⁻¹`. For `β = 1` the extra term is `n⁻¹ tr (Pᵢ Rᵢᵀ)`, which
vanishes for real symmetric `H`, so the drift has the same value. This is the drift of Dyson's
equation (Anderson–Guionnet–Zeitouni, Theorem 4.3.2), computed without choosing eigenvectors. For
`M = 1` and `β ∈ {1, 2}` the trace `∑ p, tr (E p ^ 2) = n - 1 + 2 / β` is the Itô drift of
`tr H²`.

## Main results

* `TauCeti.Probability.sum_gaussianEnsemble_single_mul_mul_gaussianEnsemble_single_of_ne_one`
  and `TauCeti.Probability.sum_gaussianEnsemble_one_single_mul_mul_gaussianEnsemble_one_single`:
  the sum `∑ p, E p * M * E p`.

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
