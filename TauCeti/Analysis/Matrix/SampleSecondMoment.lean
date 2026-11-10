/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Trace
public import TauCeti.Analysis.Convex.FiniteMean

/-!
# The empirical second-moment matrix

For a finite sample `v : ι → n → 𝕜` of vectors over `ℝ` or `ℂ`, the uncentered empirical
second-moment matrix is

`M̂ = r⁻¹ ∑ᵢ vᵢ vᵢᴴ`, with entries `M̂ₖₗ = r⁻¹ ∑ᵢ vᵢₖ conj (vᵢₗ)`,

where `r = card ι`. It is the mean (`TauCeti.finiteMean`) of the rank-one matrices `vᵢ vᵢᴴ`,
so it is Hermitian and positive semidefinite. Evaluated on random samples it is the natural
estimator of a population second-moment matrix `E[V Vᴴ]`; each of its entries is a sample mean of
products of coordinates, which is what makes the second-moment bounds for sample means apply to it
entry by entry.

## Main declarations

* `TauCeti.sampleSecondMoment`: the empirical second-moment matrix of a finite sample.
* `TauCeti.sampleSecondMoment_apply`: its entries are sample means of coordinate products.
* `TauCeti.isHermitian_sampleSecondMoment`, `TauCeti.posSemidef_sampleSecondMoment`: it is
  Hermitian, and positive semidefinite in finite dimension.
* `Matrix.sampleCovariance`: the sample covariance matrix `X Xᴴ / n` of a `p × n` data matrix, whose
  columns are the samples; `Matrix.sampleCovariance_eq_sampleSecondMoment` identifies it with the
  empirical second-moment matrix of the columns, and `Matrix.isHermitian_sampleCovariance` and
  `Matrix.posSemidef_sampleCovariance` give Hermitian and positive semidefinite.
* `Matrix.re_trace_sampleCovariance`: its real trace is the column-normalized sum of squared
  entry norms.

## References

* R. Vershynin, *High-Dimensional Probability* (2018), §4.7: the sample covariance matrix.
-/

public section

open Matrix
open scoped ComplexOrder

namespace TauCeti

variable {𝕜 ι n : Type*} [RCLike 𝕜] [Fintype ι]

/-- The uncentered empirical second-moment matrix `r⁻¹ ∑ᵢ vᵢ vᵢᴴ` of a finite sample
`v : ι → n → 𝕜`, where `r = card ι`: the mean of the rank-one matrices `vᵢ vᵢᴴ`. The empty sample
has second-moment matrix `0`. -/
noncomputable def sampleSecondMoment (v : ι → n → 𝕜) : Matrix n n 𝕜 :=
  finiteMean 𝕜 fun i ↦ vecMulVec (v i) (star (v i))

theorem sampleSecondMoment_def (v : ι → n → 𝕜) :
    sampleSecondMoment v = finiteMean 𝕜 fun i ↦ vecMulVec (v i) (star (v i)) :=
  (rfl)

/-- The `(k, l)` entry of the empirical second-moment matrix is the sample mean of the products
`vᵢₖ conj (vᵢₗ)`. -/
@[simp]
theorem sampleSecondMoment_apply (v : ι → n → 𝕜) (k l : n) :
    sampleSecondMoment v k l = finiteMean 𝕜 fun i ↦ v i k * star (v i l) := by
  simp [sampleSecondMoment_def, finiteMean_eq_inv_smul_sum, Matrix.sum_apply, vecMulVec_apply]

/-- The empirical second-moment matrix is Hermitian. -/
theorem isHermitian_sampleSecondMoment (v : ι → n → 𝕜) : (sampleSecondMoment v).IsHermitian :=
  IsHermitian.ext fun k l ↦ by
    simp [finiteMean_eq_inv_smul_sum, star_sum, mul_comm]

/-- The empirical second-moment matrix is positive semidefinite. -/
theorem posSemidef_sampleSecondMoment (v : ι → n → 𝕜) :
    (sampleSecondMoment v).PosSemidef := by
  -- Mathlib proves positive semidefiniteness of `vecMulVec a (star a)` only for finite `n`; the
  -- quadratic form on a finitely supported `x` is `star s * s` for `s = ∑ⱼ star (aⱼ) * xⱼ`.
  have hrank (a : n → 𝕜) : (vecMulVec a (star a)).PosSemidef := by
    refine ⟨IsHermitian.ext fun k l ↦ by simp [vecMulVec_apply, mul_comm], fun x ↦ ?_⟩
    have : (x.sum fun i xi ↦ x.sum fun j xj ↦ star xi * vecMulVec a (star a) i j * xj) =
        star (x.sum fun j xj ↦ star (a j) * xj) * x.sum fun j xj ↦ star (a j) * xj := by
      simp only [Finsupp.sum, star_sum, Finset.sum_mul, Finset.mul_sum, vecMulVec_apply]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
      simp only [star_mul, star_star, Pi.star_apply]
      ring
    rw [this]
    exact star_mul_self_nonneg _
  rw [sampleSecondMoment_def, finiteMean_eq_inv_smul_sum]
  exact (posSemidef_sum _ fun i _ ↦ hrank (v i)).smul (by positivity)

end TauCeti

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {p n : Type*} [Fintype n]

/-- The sample covariance matrix `X Xᴴ / n` of a `p × n` data matrix `X`, with the `n` columns
as samples. When `n` is empty it is `0`. -/
noncomputable def sampleCovariance (X : Matrix p n 𝕜) : Matrix p p 𝕜 :=
  (1 / (Fintype.card n : ℝ)) • (X * Xᴴ)

theorem sampleCovariance_def (X : Matrix p n 𝕜) :
    sampleCovariance X = (1 / (Fintype.card n : ℝ)) • (X * Xᴴ) :=
  (rfl)

/-- The `(i, j)` entry of the sample covariance matrix. -/
@[simp]
theorem sampleCovariance_apply (X : Matrix p n 𝕜) (i j : p) :
    sampleCovariance X i j = (1 / (Fintype.card n : ℝ)) • ∑ k, X i k * star (X j k) := by
  simp [sampleCovariance_def, Matrix.mul_apply]

/-- The real trace of a sample covariance matrix is the column-normalized sum of squared entry
norms. This holds for empty index types, with the usual zero conventions. -/
theorem re_trace_sampleCovariance [Fintype p] (X : Matrix p n 𝕜) :
    RCLike.re (sampleCovariance X).trace =
      (1 / (Fintype.card n : ℝ)) * ∑ i, ∑ j, ‖X i j‖ ^ 2 := by
  rw [sampleCovariance_def, Matrix.trace_smul, RCLike.real_smul_eq_coe_mul,
    RCLike.re_ofReal_mul]
  congr 1
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    RCLike.star_def, RCLike.mul_conj]

/-- The sample covariance matrix of `X` is the empirical second-moment matrix of its columns. -/
theorem sampleCovariance_eq_sampleSecondMoment (X : Matrix p n 𝕜) :
    sampleCovariance X = TauCeti.sampleSecondMoment (fun k i ↦ X i k) := by
  ext i j
  simp [TauCeti.finiteMean_eq_inv_smul_sum, RCLike.real_smul_eq_coe_mul]

/-- The sample covariance matrix is Hermitian. -/
theorem isHermitian_sampleCovariance (X : Matrix p n 𝕜) : (sampleCovariance X).IsHermitian := by
  rw [sampleCovariance_eq_sampleSecondMoment]
  exact TauCeti.isHermitian_sampleSecondMoment _

/-- The sample covariance matrix is positive semidefinite. -/
theorem posSemidef_sampleCovariance (X : Matrix p n 𝕜) :
    (sampleCovariance X).PosSemidef := by
  rw [sampleCovariance_eq_sampleSecondMoment]
  exact TauCeti.posSemidef_sampleSecondMoment _

end Matrix
