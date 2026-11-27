/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Hermite.Function.Dilation
public import TauCeti.Probability.Determinantal.Count
public import TauCeti.Probability.RandomMatrices.BetaEnsemble.Hermite
import Mathlib.Data.Nat.Factorial.SuperFactorial

/-!
# The Hermite ensemble at `β = 2` is determinantal

The Hermite beta ensemble at `β = 2` has density proportional to
`exp (-(n / 2) ∑ᵢ xᵢ²) ∏_{i<j} (xᵢ - xⱼ)²`; up to the identification of its
law with the unordered eigenvalues of the Gaussian unitary ensemble, this is the setting of
Anderson–Guionnet–Zeitouni, Lemma 3.2.2. The factor `exp (-(n / 4) x²)` times the probabilists'
Hermite polynomial `Hₖ(√n x)` is, after normalization, the Hermite function `ψₖ` dilated to the
scale `√(n / 2)`. Row operations replace the Vandermonde determinant by the determinant of these
monic polynomials. So the density is `det [φₖ(xⱼ)]² / n!` for the orthonormal functions
`φₖ(x) = (n / 2) ^ (1 / 4) ψₖ(√(n / 2) x)`, `k < n`. Equivalently it is
`det [Kₙ(xᵢ, xⱼ)] / n!` for the Hermite kernel `Kₙ(x, y) = ∑_{k<n} φₖ(x) φₖ(y)`.

The ensemble is therefore the finite determinantal ensemble of the functions `φₖ`. Its gap
probabilities are finite determinants, and the diagonal of its kernel integrates to `n`.
Comparing normalizations evaluates the partition function, the Gaussian Selberg integral at
`β = 2`: `∫ exp (-(n / 2) ∑ᵢ xᵢ²) ∏_{i<j} (xᵢ - xⱼ)² dx = sf(n) (2π) ^ (n / 2) n ^ (-n² / 2)`,
where `sf(n) = 1! 2! ⋯ n!` is the superfactorial.

## Main definitions

* `TauCeti.Probability.hermiteEnsembleFunction n k`: the Hermite function `ψₖ` dilated to the
  scale of the size `n` ensemble, `x ↦ (n / 2) ^ (1 / 4) ψₖ(√(n / 2) x)`; this is
  `TauCeti.dilatedHermiteFunction` at the scale `√(n / 2)`.
* `TauCeti.Probability.hermiteKernel n`: the Hermite kernel `∑_{k<n} φₖ(x) φₖ(y)`.

## Main results

* `TauCeti.Probability.integral_hermiteEnsembleFunction_mul_hermiteEnsembleFunction`: for `n ≠ 0`
  the functions `hermiteEnsembleFunction n k` are orthonormal in `L²(ℝ)`.
* `TauCeti.Probability.integral_hermiteKernel_mul_hermiteKernel` and
  `TauCeti.Probability.integral_hermiteKernel_mul_hermiteEnsembleFunction`: the Hermite kernel is
  the kernel of the orthogonal projection onto the span of the `φₖ`, `k < n`.
* `TauCeti.Probability.hermiteBetaPartition_two`: the partition function at `β = 2` is
  `sf(n) (2π) ^ (n / 2) / n ^ (n² / 2)`.
* `TauCeti.Probability.hermiteBetaPDFReal_two_eq_determinantalDensity` and
  `TauCeti.Probability.hermiteBetaPDFReal_two_eq_det_hermiteKernel`: the density at `β = 2` is
  the determinantal density of the functions `φₖ`, and `det [Kₙ(xᵢ, xⱼ)] / n!`.
* `TauCeti.Probability.hermiteBetaEnsemble_two_eq_determinantalEnsemble`: the ensemble at
  `β = 2` is the determinantal ensemble of the functions `φₖ`.
* `TauCeti.Probability.measureReal_hermiteBetaEnsemble_two_particleCount_eq_zero`: the
  probability that no particle lies in `B` is `det (I - [∫_B φᵢ φⱼ])`.
* `TauCeti.Probability.integral_hermiteKernel_self`: `∫ Kₙ(x, x) dx = n`.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*,
  Cambridge University Press (2010), §3.2.1, Lemma 3.2.2, and Theorem 2.5.2 with (2.5.4).
-/

public section

noncomputable section

open MeasureTheory Matrix Polynomial Real
open scoped Nat

namespace TauCeti.Probability

variable {n : ℕ}

/-! ### The dilated Hermite functions and the Hermite kernel -/

/-- The `k`th **Hermite function at the scale of the size `n` Hermite ensemble**,
`x ↦ (n / 2) ^ (1 / 4) ψₖ(√(n / 2) x)`, where `ψₖ` is `TauCeti.hermiteFunction`. Up to a
positive constant it is `Hₖ(√n x) exp (-(n / 4) x²)` for the probabilists' Hermite polynomial
`Hₖ` (`TauCeti.Probability.hermiteEnsembleFunction_eq`). It is `TauCeti.dilatedHermiteFunction`
at the scale `√(n / 2)`, so for `n ≠ 0` these functions are orthonormal in `L²(ℝ)`. -/
def hermiteEnsembleFunction (n k : ℕ) (x : ℝ) : ℝ :=
  dilatedHermiteFunction √(n / 2) k x

/-- The Hermite function at the scale of the size `n` ensemble is the dilated Hermite function
at the scale `√(n / 2)`. -/
theorem hermiteEnsembleFunction_eq_dilatedHermiteFunction (n k : ℕ) :
    hermiteEnsembleFunction n k = dilatedHermiteFunction √(n / 2) k :=
  (rfl)

/-- Defining formula for `TauCeti.Probability.hermiteEnsembleFunction`. -/
theorem hermiteEnsembleFunction_def (n k : ℕ) (x : ℝ) :
    hermiteEnsembleFunction n k x = √(√(n / 2)) * hermiteFunction k (√(n / 2) * x) :=
  dilatedHermiteFunction_def _ k x

/-- The dilated Hermite function is a normalized Hermite polynomial in `√n x` times the
Gaussian factor `exp (-(n / 4) x²)`. -/
theorem hermiteEnsembleFunction_eq (n k : ℕ) (x : ℝ) :
    hermiteEnsembleFunction n k x =
      √(√(n / 2)) / √(k ! * √π) * aeval (√n * x) (hermite k) * rexp (-(n * x ^ 2 / 4)) := by
  have h2 : √((n : ℝ) / 2) * √2 = √n := by
    rw [← sqrt_mul (by positivity), div_mul_cancel₀ _ two_ne_zero]
  have hsq : (√((n : ℝ) / 2) * x) ^ 2 / 2 = n * x ^ 2 / 4 := by
    rw [mul_pow, sq_sqrt (by positivity)]
    ring
  rw [hermiteEnsembleFunction_def, hermiteFunction_def, hsq, mul_right_comm _ x, h2]
  ring

/-- The dilated Hermite functions are continuous. -/
@[fun_prop]
theorem continuous_hermiteEnsembleFunction (n k : ℕ) :
    Continuous (hermiteEnsembleFunction n k) :=
  continuous_dilatedHermiteFunction _ k

/-- The dilated Hermite functions are square integrable. -/
theorem memLp_two_hermiteEnsembleFunction (n k : ℕ) :
    MemLp (hermiteEnsembleFunction n k) 2 volume :=
  memLp_two_dilatedHermiteFunction _ k

/-- **Orthonormality** of the dilated Hermite functions: for `n ≠ 0`,
`∫ φᵢ φⱼ = if i = j then 1 else 0`. -/
theorem integral_hermiteEnsembleFunction_mul_hermiteEnsembleFunction (hn : n ≠ 0) (i j : ℕ) :
    ∫ x, hermiteEnsembleFunction n i x * hermiteEnsembleFunction n j x =
      if i = j then 1 else 0 :=
  integral_dilatedHermiteFunction_mul_dilatedHermiteFunction (sqrt_pos.2 (by positivity)) i j

/-- Orthonormality of the first `n` dilated Hermite functions, in the form taken by the
determinantal ensemble API. -/
private theorem integral_hermiteEnsembleFunction_mul_star_hermiteEnsembleFunction (i j : Fin n) :
    ∫ x, hermiteEnsembleFunction n i x * star (hermiteEnsembleFunction n j x) =
      if i = j then 1 else 0 := by
  simp [integral_hermiteEnsembleFunction_mul_hermiteEnsembleFunction (Fin.pos i).ne', Fin.val_inj]

/-- The **Hermite kernel** of size `n`, `Kₙ(x, y) = ∑_{k<n} φₖ(x) φₖ(y)` for the dilated Hermite
functions `φₖ = TauCeti.Probability.hermiteEnsembleFunction n k`. It is the kernel of the
orthogonal projection of `L²(ℝ)` onto the span of the `φₖ`, `k < n`, and the correlation kernel
of the Hermite ensemble at `β = 2`. -/
def hermiteKernel (n : ℕ) (x y : ℝ) : ℝ :=
  finiteRankKernel (fun k : Fin n ↦ hermiteEnsembleFunction n k) x y

/-- Defining formula for `TauCeti.Probability.hermiteKernel`. -/
theorem hermiteKernel_def (n : ℕ) (x y : ℝ) :
    hermiteKernel n x y = finiteRankKernel (fun k : Fin n ↦ hermiteEnsembleFunction n k) x y :=
  (rfl)

/-- The Hermite kernel as a sum over `k < n`. -/
theorem hermiteKernel_eq_sum (n : ℕ) (x y : ℝ) :
    hermiteKernel n x y =
      ∑ k ∈ Finset.range n, hermiteEnsembleFunction n k x * hermiteEnsembleFunction n k y := by
  rw [hermiteKernel_def, finiteRankKernel_def]
  simp only [star_trivial]
  exact Fin.sum_univ_eq_sum_range (fun k ↦ hermiteEnsembleFunction n k x *
    hermiteEnsembleFunction n k y) n

/-- The Hermite kernel is symmetric. -/
theorem hermiteKernel_comm (n : ℕ) (x y : ℝ) : hermiteKernel n x y = hermiteKernel n y x := by
  simpa [hermiteKernel_def] using
    star_finiteRankKernel (fun k : Fin n ↦ hermiteEnsembleFunction n k) x y

/-- **The reproducing identity** of the Hermite kernel: `∫ Kₙ(x, z) Kₙ(z, y) dz = Kₙ(x, y)`. -/
theorem integral_hermiteKernel_mul_hermiteKernel (n : ℕ) (x y : ℝ) :
    ∫ z, hermiteKernel n x z * hermiteKernel n z y = hermiteKernel n x y := by
  simp_rw [hermiteKernel_def]
  exact integral_finiteRankKernel_mul_finiteRankKernel
    (fun k : Fin n ↦ memLp_two_hermiteEnsembleFunction n k)
    integral_hermiteEnsembleFunction_mul_star_hermiteEnsembleFunction x y

/-- The Hermite kernel fixes the dilated Hermite functions it is built from:
`∫ Kₙ(x, y) φₖ(y) dy = φₖ(x)` for `k < n`. -/
theorem integral_hermiteKernel_mul_hermiteEnsembleFunction {k : ℕ} (hk : k < n) (x : ℝ) :
    ∫ y, hermiteKernel n x y * hermiteEnsembleFunction n k y = hermiteEnsembleFunction n k x := by
  simp_rw [hermiteKernel_def]
  exact integral_finiteRankKernel_mul_generator
    (fun k : Fin n ↦ memLp_two_hermiteEnsembleFunction n k)
    integral_hermiteEnsembleFunction_mul_star_hermiteEnsembleFunction x ⟨k, hk⟩

/-- The diagonal of the Hermite kernel integrates to the number of particles. -/
theorem integral_hermiteKernel_self (n : ℕ) : ∫ x, hermiteKernel n x x = n := by
  simp_rw [hermiteKernel_def]
  simpa using integral_finiteRankKernel_self
    (fun k : Fin n ↦ memLp_two_hermiteEnsembleFunction n k)
    fun i ↦ by simpa using integral_hermiteEnsembleFunction_mul_star_hermiteEnsembleFunction i i

/-! ### The determinantal density -/

/-- The evaluation matrix of the dilated Hermite functions factors as a diagonal matrix of
normalizations, the matrix of monic Hermite polynomials and a diagonal matrix of Gaussian
factors; the polynomial matrix has the Vandermonde determinant of `√n x`. -/
private theorem det_hermiteEnsembleFunction (x : Fin n → ℝ) :
    det (Matrix.of fun i j : Fin n ↦ hermiteEnsembleFunction n i (x j)) =
      (∏ i : Fin n, √(√(n / 2)) / √((i : ℕ)! * √π)) * (∏ j : Fin n, √n ^ (j : ℕ)) *
        (∏ j, rexp (-(n * x j ^ 2 / 4))) * det (vandermonde x) := by
  set P : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j ↦ aeval (√n * x j) (hermite i)
  have hM : (Matrix.of fun i j : Fin n ↦ hermiteEnsembleFunction n i (x j)) =
      diagonal (fun i : Fin n ↦ √(√(n / 2)) / √((i : ℕ)! * √π)) * P *
        diagonal (fun j ↦ rexp (-(n * x j ^ 2 / 4))) := by
    ext i j
    simp [P, hermiteEnsembleFunction_eq, diagonal_mul, mul_diagonal]
  have hV : vandermonde (fun i ↦ √n * x i) =
      vandermonde x * diagonal (fun j : Fin n ↦ √n ^ (j : ℕ)) := by
    ext i j
    simp [vandermonde_apply, mul_diagonal, mul_pow, mul_comm]
  have hP : det P = (∏ j : Fin n, √n ^ (j : ℕ)) * det (vandermonde x) := by
    have h := det_eval_matrixOfPolynomials_eq_det_vandermonde (fun i ↦ √n * x i)
      (fun j : Fin n ↦ (hermite j).map (algebraMap ℤ ℝ))
      (fun j ↦ by rw [(hermite_monic j).natDegree_map, natDegree_hermite])
      (fun j ↦ (hermite_monic j).map _)
    simp only [eval_map_algebraMap] at h
    rw [hV, det_mul, det_diagonal] at h
    rw [← det_transpose, mul_comm, h, transpose_of]
  rw [hM, det_mul, det_mul, det_diagonal, det_diagonal, hP]
  ring

/-- The normalizing constants of the dilated Hermite functions, squared, against the
superfactorial form of the Gaussian Selberg constant at `β = 2`. -/
private theorem hermiteEnsemble_const_eq (n : ℕ) :
    (∏ i : Fin n, √(√(n / 2)) / √((i : ℕ)! * √π)) ^ 2 * (∏ j : Fin n, √n ^ (j : ℕ)) ^ 2 /
        (n ! : ℝ) = √n ^ (n ^ 2) / (√(2 * π) ^ n * n.superFactorial) := by
  have hsf : (n.superFactorial : ℝ) = (∏ i : Fin n, ((i : ℕ)! : ℝ)) * n ! := by
    rw [← Nat.prod_range_succ_factorial, Finset.prod_range_succ, Nat.cast_mul, Nat.cast_prod,
      Fin.prod_univ_eq_prod_range (fun i ↦ ((i ! : ℕ) : ℝ))]
  have hc : (∏ i : Fin n, √(√(n / 2)) / √((i : ℕ)! * √π)) ^ 2 =
      √(n / 2) ^ n / ((∏ i : Fin n, ((i : ℕ)! : ℝ)) * √π ^ n) := by
    rw [← Finset.prod_pow]
    simp (disch := positivity) only [div_pow, sq_sqrt]
    rw [Finset.prod_div_distrib, Finset.prod_mul_distrib]
    simp [div_pow]
  have hsum : (∑ j : Fin n, (j : ℕ)) * 2 = n * (n - 1) := by
    rw [Fin.sum_univ_eq_sum_range (fun j ↦ j), Finset.sum_range_id_mul_two]
  have hpow : (∏ j : Fin n, √(n : ℝ) ^ (j : ℕ)) ^ 2 * √n ^ n = √n ^ (n ^ 2) := by
    rw [Finset.prod_pow_eq_pow_sum, ← pow_mul, hsum, ← pow_add]
    congr 1
    rcases n with _ | m
    · rfl
    · simp only [Nat.add_sub_cancel]
      ring
  have hs2 : √((n : ℝ) / 2) = √n / √2 := sqrt_div (Nat.cast_nonneg n) 2
  rw [hc, hsf, hs2, div_pow, sqrt_mul zero_le_two, mul_pow, ← hpow]
  field_simp

/-- The determinantal density of the first `n` dilated Hermite functions is an explicit multiple
of the Hermite weight at `β = 2`. -/
private theorem determinantalDensity_hermiteEnsembleFunction (x : Fin n → ℝ) :
    determinantalDensity (fun k : Fin n ↦ hermiteEnsembleFunction n k) x =
      √n ^ (n ^ 2) / (√(2 * π) ^ n * n.superFactorial) * hermiteBetaWeight 2 n x := by
  have he : (∏ j, rexp (-(n * x j ^ 2 / 4))) ^ 2 = rexp (-(2 * n / 4) * ∑ i, x i ^ 2) := by
    rw [← exp_sum, ← exp_natCast_mul, Finset.mul_sum, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    push_cast
    ring
  rw [determinantalDensity_def, det_hermiteEnsembleFunction, hermiteBetaWeight_eq,
    norm_eq_abs, sq_abs, rpow_two, sq_abs, Fintype.card_fin, ← hermiteEnsemble_const_eq, ← he]
  ring

/-! ### The partition function and the ensemble -/

/-- **The Gaussian Selberg integral at `β = 2`**: the partition function of the Hermite ensemble
at `β = 2` is `sf(n) (2π) ^ (n / 2) / n ^ (n² / 2)`, where `sf(n) = 1! 2! ⋯ n!` is the
superfactorial. -/
theorem hermiteBetaPartition_two (n : ℕ) :
    hermiteBetaPartition 2 n = n.superFactorial * √(2 * π) ^ n / √n ^ (n ^ 2) := by
  have h := integral_determinantalDensity (μ := volume)
    (fun k : Fin n ↦ memLp_two_hermiteEnsembleFunction n k)
    integral_hermiteEnsembleFunction_mul_star_hermiteEnsembleFunction
  simp_rw [determinantalDensity_hermiteEnsembleFunction] at h
  rw [integral_const_mul, ← volume_pi, ← hermiteBetaPartition_def] at h
  rw [eq_inv_of_mul_eq_one_right h, inv_div, mul_comm]

/-- **The Hermite density at `β = 2` is determinantal**: it is `det [φᵢ(xⱼ)]² / n!` for the
orthonormal dilated Hermite functions `φₖ = TauCeti.Probability.hermiteEnsembleFunction n k`,
`k < n`. -/
theorem hermiteBetaPDFReal_two_eq_determinantalDensity (n : ℕ) (x : Fin n → ℝ) :
    hermiteBetaPDFReal 2 n x =
      determinantalDensity (fun k : Fin n ↦ hermiteEnsembleFunction n k) x := by
  rw [determinantalDensity_hermiteEnsembleFunction, hermiteBetaPDFReal_def,
    hermiteBetaPartition_two, inv_div, mul_comm (n.superFactorial : ℝ)]

/-- The Hermite density at `β = 2` is `det [Kₙ(xᵢ, xⱼ)] / n!` for the Hermite kernel `Kₙ`. -/
theorem hermiteBetaPDFReal_two_eq_det_hermiteKernel (n : ℕ) (x : Fin n → ℝ) :
    hermiteBetaPDFReal 2 n x = det (Matrix.of fun i j ↦ hermiteKernel n (x i) (x j)) / n ! := by
  rw [hermiteBetaPDFReal_two_eq_determinantalDensity,
    determinantalDensity_eq_re_det_finiteRankKernel_div_factorial]
  simp [hermiteKernel_def]

/-- **The Hermite ensemble at `β = 2` is determinantal**: it is the labelled determinantal
ensemble of the dilated Hermite functions `φₖ`, `k < n`, with respect to Lebesgue measure. -/
theorem hermiteBetaEnsemble_two_eq_determinantalEnsemble (n : ℕ) :
    hermiteBetaEnsemble 2 n =
      determinantalEnsemble volume (fun k : Fin n ↦ hermiteEnsembleFunction n k) := by
  rw [hermiteBetaEnsemble_def, determinantalEnsemble_def, ← volume_pi]
  congr 1
  funext x
  rw [hermiteBetaPDF_def, hermiteBetaPDFReal_two_eq_determinantalDensity]

/-- **Gap probabilities of the Hermite ensemble at `β = 2`**: no particle lies in the window `B`
with probability `det (I - [∫_B φᵢ φⱼ])`, a determinant of size `n`. -/
theorem measureReal_hermiteBetaEnsemble_two_particleCount_eq_zero (n : ℕ) {B : Set ℝ}
    (hB : NullMeasurableSet B) :
    (hermiteBetaEnsemble 2 n).real {x | particleCount x B = 0} =
      det (1 - Matrix.of fun i j : Fin n ↦
        ∫ x in B, hermiteEnsembleFunction n i x * hermiteEnsembleFunction n j x) := by
  rw [hermiteBetaEnsemble_two_eq_determinantalEnsemble]
  simpa using measureReal_determinantalEnsemble_particleCount_eq_zero
    (fun k : Fin n ↦ memLp_two_hermiteEnsembleFunction n k)
    integral_hermiteEnsembleFunction_mul_star_hermiteEnsembleFunction hB

end TauCeti.Probability
