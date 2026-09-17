/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Wishart.Transforms

import TauCeti.Analysis.SpecialFunctions.Log.SumLogOneSub
import TauCeti.LinearAlgebra.Matrix.Trace
import TauCeti.Probability.Moments.Basic
import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# Moments of Wishart laws

A law `μ` on the symmetric matrices has the *Wishart trace transform* of degree `n` and scale `S`
when, for every symmetric `Θ`, the moment-generating function of the trace statistic
`A ↦ trace (Θ * A)` is `det (1 - (2 * t) • (√S * Θ * √S)) ^ (-n / 2)` wherever that pencil is
positive definite. Both Wishart families have this transform, and it determines their first two
moments. This file derives them once, for every law with a Wishart trace transform of
positive-semidefinite scale: a symmetric trace statistic has mean `n * trace (Θ * S)` and variance
`2 * n * trace (Θ * S * Θ * S)`, two such statistics have covariance
`2 * n * trace (Θ * S * Φ * S)`, and the matrix itself has mean `n • S` and entrywise covariance
`n * (S i k * S j l + S i l * S j k)`. The transform also forces finite moments of all orders.
These are the second-order data of a Wishart law: `n • S` is its centre, and the covariance
describes the fluctuation of every linear statistic of it.

The moments come from the cumulant-generating function at `0`. Near `0` the pencil is positive
definite, so the transform makes the trace statistic exponentially integrable there, and
diagonalizing the sandwich `√S * Θ * √S` writes the cumulant-generating function as
`-n / 2 * ∑ j, log (1 - 2 * t * λ j)`. Its first two derivatives at `0` are the mean and the
variance of the statistic; polarization gives covariances, and the symmetrized elementary matrices
`TauCeti.symmetricEntry i j` recover the entries.

The last section specializes these results to the Gaussian-Gram family `wishartGramMeasure ν S`,
whose trace transform is `TauCeti.mgf_trace_mul_wishartGramMeasure_sqrt`.

## Main results

* `TauCeti.memLp_trace_mul_of_mgf_trace_mul_eq_det_rpow`,
  `TauCeti.memLp_coe_apply_of_mgf_trace_mul_eq_det_rpow` and
  `TauCeti.memLp_id_of_mgf_trace_mul_eq_det_rpow` give finite moments of all orders for trace
  statistics, entries and the matrix itself;
* `TauCeti.integral_trace_mul_of_mgf_trace_mul_eq_det_rpow`,
  `TauCeti.variance_trace_mul_of_mgf_trace_mul_eq_det_rpow` and
  `TauCeti.covariance_trace_mul_of_mgf_trace_mul_eq_det_rpow` compute the mean and variance of a
  trace statistic and the covariance of two;
* `TauCeti.integral_id_of_mgf_trace_mul_eq_det_rpow`,
  `TauCeti.integral_coe_apply_of_mgf_trace_mul_eq_det_rpow` and
  `TauCeti.covariance_coe_apply_of_mgf_trace_mul_eq_det_rpow` give the Bochner mean and the
  entrywise mean and covariance;
* `TauCeti.integral_id_wishartGramMeasure`, `TauCeti.covariance_coe_apply_wishartGramMeasure` and
  their companions specialize all of these to the Gaussian-Gram family.

## References

* R. J. Muirhead, *Aspects of Multivariate Statistical Theory*, Wiley (1982), Theorem 3.2.3.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

open scoped RealInnerProductSpace Matrix MatrixOrder NNReal Topology

namespace TauCeti

variable {p : ℕ} {μ : Measure (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ))}
  {S : Matrix (Fin p) (Fin p) ℝ} {n : ℝ}

/-! ### Laws with a Wishart trace transform -/

section TraceStatistic

variable {Θ : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)}

/-- A Wishart trace transform at a single `Θ` already forces total mass `1`: at `t = 0` the
moment-generating function is the total mass, and the determinant power is `1`. -/
private lemma isProbabilityMeasure_of_mgf_trace_mul_eq_det_rpow
    (hmgf : ∀ t : ℝ,
      (1 - (2 * t) • (CFC.sqrt S * (Θ : Matrix (Fin p) (Fin p) ℝ) * CFC.sqrt S)).PosDef →
      mgf (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
          ((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace) μ t =
        (1 - (2 * t) • (CFC.sqrt S * (Θ : Matrix (Fin p) (Fin p) ℝ) * CFC.sqrt S)).det
          ^ (-n / 2)) :
    IsProbabilityMeasure μ := by
  have h := hmgf 0 (by simpa using Matrix.PosDef.one)
  simp only [mul_zero, zero_smul, sub_zero, Matrix.det_one, Real.one_rpow] at h
  exact isProbabilityMeasure_of_mgf_zero_eq_one h

private lemma zero_mem_interior_integrableExpSet_of_mgf_trace_mul_eq_det_rpow
    (hmgf : ∀ t : ℝ,
      (1 - (2 * t) • (CFC.sqrt S * (Θ : Matrix (Fin p) (Fin p) ℝ) * CFC.sqrt S)).PosDef →
      mgf (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
          ((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace) μ t =
        (1 - (2 * t) • (CFC.sqrt S * (Θ : Matrix (Fin p) (Fin p) ℝ) * CFC.sqrt S)).det
          ^ (-n / 2)) :
    (0 : ℝ) ∈ interior
      (integrableExpSet (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
        (((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace)) μ) := by
  rw [mem_interior_iff_mem_nhds]
  have hB : (CFC.sqrt S * (Θ : Matrix (Fin p) (Fin p) ℝ) * CFC.sqrt S).IsHermitian :=
    Matrix.isHermitian_sqrt_mul_mul_sqrt S (selfAdjoint.isHermitian_coe Θ)
  filter_upwards [((continuous_const_mul (2 : ℝ)).tendsto' 0 0 (mul_zero 2)).eventually
    hB.eventually_posDef_one_sub_smul] with t ht
  -- The mgf is a positive determinant power, so its defining integral is not the junk value `0`.
  have hne : mgf (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
      (((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace)) μ t ≠ 0 := by
    rw [hmgf t ht]
    exact (Real.rpow_pos_of_pos ht.det_pos _).ne'
  exact Integrable.of_integral_ne_zero hne

private lemma cgf_trace_mul_eventuallyEq_sum_log_of_mgf_trace_mul_eq_det_rpow
    (hmgf : ∀ t : ℝ,
      (1 - (2 * t) • (CFC.sqrt S * (Θ : Matrix (Fin p) (Fin p) ℝ) * CFC.sqrt S)).PosDef →
      mgf (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
          ((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace) μ t =
        (1 - (2 * t) • (CFC.sqrt S * (Θ : Matrix (Fin p) (Fin p) ℝ) * CFC.sqrt S)).det
          ^ (-n / 2)) :
    cgf (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
        (((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace)) μ =ᶠ[𝓝 0]
      fun t => -n / 2 * ∑ j,
        Real.log (1 - 2 * t *
          (Matrix.isHermitian_sqrt_mul_mul_sqrt S
            (selfAdjoint.isHermitian_coe Θ)).eigenvalues j) := by
  let B := CFC.sqrt S * (Θ : Matrix (Fin p) (Fin p) ℝ) * CFC.sqrt S
  let hB : B.IsHermitian :=
    Matrix.isHermitian_sqrt_mul_mul_sqrt S (selfAdjoint.isHermitian_coe Θ)
  filter_upwards [((continuous_const_mul (2 : ℝ)).tendsto' 0 0 (mul_zero 2)).eventually
      hB.eventually_posDef_one_sub_smul] with t ht
  have hdet := hB.det_one_sub_smul (2 * t)
  simp only [RCLike.ofReal_real_eq_id, id_eq] at hdet
  rw [cgf, hmgf t ht, Real.log_rpow ht.det_pos, hdet, Real.log_prod]
  intro j _
  rw [hB.posDef_one_sub_smul_iff] at ht
  exact (sub_pos.2 (ht j)).ne'

/-- Under a law with a Wishart trace transform at `Θ`, the trace statistic `A ↦ trace (Θ * A)`
has finite moments of all orders. -/
theorem memLp_trace_mul_of_mgf_trace_mul_eq_det_rpow
    (hmgf : ∀ t : ℝ,
      (1 - (2 * t) • (CFC.sqrt S * (Θ : Matrix (Fin p) (Fin p) ℝ) * CFC.sqrt S)).PosDef →
      mgf (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
          ((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace) μ t =
        (1 - (2 * t) • (CFC.sqrt S * (Θ : Matrix (Fin p) (Fin p) ℝ) * CFC.sqrt S)).det
          ^ (-n / 2))
    (q : ℝ≥0) :
    MemLp (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
        ((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace) q μ :=
  memLp_of_mem_interior_integrableExpSet
    (zero_mem_interior_integrableExpSet_of_mgf_trace_mul_eq_det_rpow hmgf) q

/-- **The mean of a symmetric trace statistic under a law with a Wishart trace transform.** If
the trace statistic `A ↦ trace (Θ * A)` has the Wishart moment-generating function of degree `n`
and positive-semidefinite scale `S`, then its mean is `n * trace (Θ * S)`. -/
theorem integral_trace_mul_of_mgf_trace_mul_eq_det_rpow (hS : S.PosSemidef)
    (hmgf : ∀ t : ℝ,
      (1 - (2 * t) • (CFC.sqrt S * (Θ : Matrix (Fin p) (Fin p) ℝ) * CFC.sqrt S)).PosDef →
      mgf (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
          ((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace) μ t =
        (1 - (2 * t) • (CFC.sqrt S * (Θ : Matrix (Fin p) (Fin p) ℝ) * CFC.sqrt S)).det
          ^ (-n / 2)) :
    ∫ A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
        ((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace ∂μ =
      n * ((Θ : Matrix (Fin p) (Fin p) ℝ) * S).trace := by
  let X := fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
    ((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace
  let hB := Matrix.isHermitian_sqrt_mul_mul_sqrt S (selfAdjoint.isHermitian_coe Θ)
  have := isProbabilityMeasure_of_mgf_trace_mul_eq_det_rpow hmgf
  have hzero := zero_mem_interior_integrableExpSet_of_mgf_trace_mul_eq_det_rpow hmgf
  have heq := cgf_trace_mul_eventuallyEq_sum_log_of_mgf_trace_mul_eq_det_rpow hmgf
  calc
    ∫ A, X A ∂μ = deriv (cgf X μ) 0 := by
      simpa [X] using (deriv_cgf_zero hzero).symm
    _ = deriv (fun t => -n / 2 * ∑ j, Real.log (1 - 2 * t * hB.eigenvalues j)) 0 :=
      heq.deriv_eq
    _ = n * ∑ j, hB.eigenvalues j :=
      (hasDerivAt_neg_half_mul_sum_log n hB.eigenvalues).deriv
    _ = n * (CFC.sqrt S * (Θ : Matrix (Fin p) (Fin p) ℝ) * CFC.sqrt S).trace := by
      rw [hB.trace_eq_sum_eigenvalues]
      simp
    _ = n * ((Θ : Matrix (Fin p) (Fin p) ℝ) * S).trace := by
      rw [hS.trace_sqrt_mul_mul_sqrt]

/-- **The variance of a symmetric trace statistic under a law with a Wishart trace transform.** If
the trace statistic `A ↦ trace (Θ * A)` has the Wishart moment-generating function of degree `n`
and positive-semidefinite scale `S`, then its variance is `2 * n * trace (Θ * S * Θ * S)`. -/
theorem variance_trace_mul_of_mgf_trace_mul_eq_det_rpow (hS : S.PosSemidef)
    (hmgf : ∀ t : ℝ,
      (1 - (2 * t) • (CFC.sqrt S * (Θ : Matrix (Fin p) (Fin p) ℝ) * CFC.sqrt S)).PosDef →
      mgf (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
          ((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace) μ t =
        (1 - (2 * t) • (CFC.sqrt S * (Θ : Matrix (Fin p) (Fin p) ℝ) * CFC.sqrt S)).det
          ^ (-n / 2)) :
    Var[fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
        ((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace; μ] =
      2 * n *
        (((Θ : Matrix (Fin p) (Fin p) ℝ) * S * (Θ : Matrix (Fin p) (Fin p) ℝ) * S).trace) := by
  let X := fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
    ((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace
  let B := CFC.sqrt S * (Θ : Matrix (Fin p) (Fin p) ℝ) * CFC.sqrt S
  let hB : B.IsHermitian :=
    Matrix.isHermitian_sqrt_mul_mul_sqrt S (selfAdjoint.isHermitian_coe Θ)
  have := isProbabilityMeasure_of_mgf_trace_mul_eq_det_rpow hmgf
  have hzero := zero_mem_interior_integrableExpSet_of_mgf_trace_mul_eq_det_rpow hmgf
  have heq := cgf_trace_mul_eventuallyEq_sum_log_of_mgf_trace_mul_eq_det_rpow hmgf
  have hcumulant : iteratedDeriv 2 (cgf X μ) 0 = 2 * n * ∑ j, hB.eigenvalues j ^ 2 := by
    rw [heq.iteratedDeriv_eq 2]
    exact iteratedDeriv_two_neg_half_mul_sum_log n hB.eigenvalues
  rw [variance_eq_integral (by fun_prop)]
  have hsecond := iteratedDeriv_two_cgf_eq_integral hzero
  have hfirst := deriv_cgf_zero hzero
  norm_num at hfirst
  rw [hfirst] at hsecond
  simp only [zero_mul, Real.exp_zero, mul_one, mgf_zero, div_one] at hsecond
  have hsq : ∑ j, hB.eigenvalues j ^ 2 = (B * B).trace := by
    simpa only [RCLike.ofReal_real_eq_id, id_eq]
      using hB.trace_mul_self_eq_sum_eigenvalues_sq.symm
  rw [← hsecond, hcumulant, hsq, hS.trace_sqrt_mul_mul_sqrt_mul_self]

end TraceStatistic

section Matrix

variable
  (hmgf : ∀ (Θ : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) (t : ℝ),
    (1 - (2 * t) • (CFC.sqrt S * (Θ : Matrix (Fin p) (Fin p) ℝ) * CFC.sqrt S)).PosDef →
    mgf (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
        ((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace) μ t =
      (1 - (2 * t) • (CFC.sqrt S * (Θ : Matrix (Fin p) (Fin p) ℝ) * CFC.sqrt S)).det
        ^ (-n / 2))
include hmgf

omit hmgf in
/-- **The covariance of two symmetric trace statistics under a law with a Wishart trace
transform.** If the trace statistics at `Θ`, `Φ`, and `Θ + Φ` have the Wishart
moment-generating function of degree `n` and positive-semidefinite scale `S`, then the statistics
at `Θ` and `Φ` have covariance `2 * n * trace (Θ * S * Φ * S)`. -/
theorem covariance_trace_mul_of_mgf_trace_mul_eq_det_rpow (hS : S.PosSemidef)
    (Θ Φ : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ))
    (hΘ : ∀ t : ℝ,
      (1 - (2 * t) • (CFC.sqrt S * (Θ : Matrix (Fin p) (Fin p) ℝ) * CFC.sqrt S)).PosDef →
      mgf (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
          ((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace) μ t =
        (1 - (2 * t) • (CFC.sqrt S * (Θ : Matrix (Fin p) (Fin p) ℝ) * CFC.sqrt S)).det
          ^ (-n / 2))
    (hΦ : ∀ t : ℝ,
      (1 - (2 * t) • (CFC.sqrt S * (Φ : Matrix (Fin p) (Fin p) ℝ) * CFC.sqrt S)).PosDef →
      mgf (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
          ((Φ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace) μ t =
        (1 - (2 * t) • (CFC.sqrt S * (Φ : Matrix (Fin p) (Fin p) ℝ) * CFC.sqrt S)).det
          ^ (-n / 2))
    (hΘΦ : ∀ t : ℝ,
      (1 - (2 * t) • (CFC.sqrt S * ((Θ + Φ : selfAdjoint.submodule ℝ
        (Matrix (Fin p) (Fin p) ℝ)) : Matrix (Fin p) (Fin p) ℝ) * CFC.sqrt S)).PosDef →
      mgf (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
          (((Θ + Φ : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
            Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace) μ t =
        (1 - (2 * t) • (CFC.sqrt S * ((Θ + Φ : selfAdjoint.submodule ℝ
          (Matrix (Fin p) (Fin p) ℝ)) : Matrix (Fin p) (Fin p) ℝ) * CFC.sqrt S)).det
          ^ (-n / 2)) :
    cov[fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
          ((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace,
        fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
          ((Φ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace; μ] =
      2 * n *
        (((Θ : Matrix (Fin p) (Fin p) ℝ) * S *
          (Φ : Matrix (Fin p) (Fin p) ℝ) * S).trace) := by
  let X := fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
    ((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace
  let Y := fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
    ((Φ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace
  have := isProbabilityMeasure_of_mgf_trace_mul_eq_det_rpow hΘ
  have hX : MemLp X 2 μ := memLp_trace_mul_of_mgf_trace_mul_eq_det_rpow hΘ 2
  have hY : MemLp Y 2 μ := memLp_trace_mul_of_mgf_trace_mul_eq_det_rpow hΦ 2
  have hsum : X + Y = fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
      ((((Θ + Φ : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
        Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace) := by
    funext A
    simp [X, Y, Matrix.add_mul, Matrix.trace_add]
  have hpolar := variance_add hX hY
  rw [hsum, variance_trace_mul_of_mgf_trace_mul_eq_det_rpow hS hΘΦ,
    variance_trace_mul_of_mgf_trace_mul_eq_det_rpow hS hΘ,
    variance_trace_mul_of_mgf_trace_mul_eq_det_rpow hS hΦ] at hpolar
  rw [Submodule.coe_add, Matrix.trace_add_mul_add_mul] at hpolar
  dsimp [X, Y] at hpolar
  linarith

/-- Every entry of a matrix whose law has a Wishart trace transform has finite moments of all
orders. -/
theorem memLp_coe_apply_of_mgf_trace_mul_eq_det_rpow (i j : Fin p) (q : ℝ≥0) :
    MemLp (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
        (A : Matrix (Fin p) (Fin p) ℝ) i j) q μ := by
  simpa only [trace_symmetricEntry_mul_coe] using
    memLp_trace_mul_of_mgf_trace_mul_eq_det_rpow (hmgf (symmetricEntry i j)) q

/-- A matrix whose law has a Wishart trace transform has finite moments of all orders. -/
theorem memLp_id_of_mgf_trace_mul_eq_det_rpow (q : ℝ≥0) :
    MemLp (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) => A) q μ := by
  have hcoordinates : MemLp
      (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
        symmetricCoordinates p A) q μ :=
    MemLp.of_eval fun ij => by
      simpa only [symmetricCoordinates_apply] using
        memLp_coe_apply_of_mgf_trace_mul_eq_det_rpow hmgf ij.1.1 ij.1.2 q
  have hcomp :
      ((symmetricCoordinates p).symm.toContinuousLinearMap ∘
        fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) => symmetricCoordinates p A) =
        fun A => A := by
    funext A
    simp
  rw [← hcomp]
  exact (symmetricCoordinates p).symm.toContinuousLinearMap.comp_memLp' hcoordinates

/-- A matrix whose law has a Wishart trace transform is integrable. -/
theorem integrable_id_of_mgf_trace_mul_eq_det_rpow :
    Integrable (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) => A) μ :=
  memLp_one_iff_integrable.1 (by exact_mod_cast memLp_id_of_mgf_trace_mul_eq_det_rpow hmgf 1)

/-- **The entrywise mean of a law with a Wishart trace transform** of degree `n` and
positive-semidefinite scale `S` is `n Sᵢⱼ`. -/
theorem integral_coe_apply_of_mgf_trace_mul_eq_det_rpow (hS : S.PosSemidef) (i j : Fin p) :
    ∫ A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
        (A : Matrix (Fin p) (Fin p) ℝ) i j ∂μ = n * S i j := by
  have h := integral_trace_mul_of_mgf_trace_mul_eq_det_rpow hS (hmgf (symmetricEntry i j))
  simpa only [trace_symmetricEntry_mul_coe, trace_symmetricEntry_mul i j hS.1] using h

/-- **The mean of a law with a Wishart trace transform** of degree `n` and positive-semidefinite
scale `S` is `n • S`. -/
theorem integral_id_of_mgf_trace_mul_eq_det_rpow (hS : S.PosSemidef) :
    ∫ A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ), A ∂μ =
      n • (⟨S, Matrix.isHermitian_iff_isSelfAdjoint.1 hS.1⟩ :
        selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) := by
  have hcoordinates : Integrable
      (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
        symmetricCoordinates p A) μ :=
    (symmetricCoordinates p).toContinuousLinearMap.integrable_comp
      (integrable_id_of_mgf_trace_mul_eq_det_rpow hmgf)
  apply (symmetricCoordinates p).injective
  funext ij
  rw [← (symmetricCoordinates p).integral_comp_comm,
    eval_integral (fun ij => hcoordinates.eval ij)]
  simp only [symmetricCoordinates_apply, Submodule.coe_smul, Matrix.smul_apply]
  rw [integral_coe_apply_of_mgf_trace_mul_eq_det_rpow hmgf hS]
  simp

/-- **The entrywise covariance of a law with a Wishart trace transform** of degree `n` and
positive-semidefinite scale `S` is `n (Sᵢₖ Sⱼₗ + Sᵢₗ Sⱼₖ)`. -/
theorem covariance_coe_apply_of_mgf_trace_mul_eq_det_rpow (hS : S.PosSemidef)
    (i j k l : Fin p) :
    cov[fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
          (A : Matrix (Fin p) (Fin p) ℝ) i j,
        fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
          (A : Matrix (Fin p) (Fin p) ℝ) k l; μ] =
      n * (S i k * S j l + S i l * S j k) := by
  have h := covariance_trace_mul_of_mgf_trace_mul_eq_det_rpow hS
    (symmetricEntry i j) (symmetricEntry k l) (hmgf _) (hmgf _) (hmgf _)
  rw [trace_symmetricEntry_mul_mul_symmetricEntry_mul i j k l hS.1] at h
  have hij : (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
      (((symmetricEntry i j : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
        Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace) =
      fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
        (A : Matrix (Fin p) (Fin p) ℝ) i j := by
    funext A
    exact trace_symmetricEntry_mul_coe i j A
  have hkl : (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
      (((symmetricEntry k l : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
        Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace) =
      fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
        (A : Matrix (Fin p) (Fin p) ℝ) k l := by
    funext A
    exact trace_symmetricEntry_mul_coe k l A
  rw [hij, hkl] at h
  rw [h]
  ring

end Matrix

/-! ### The Gaussian-Gram family -/

/-- Every symmetric trace statistic `A ↦ trace (Θ * A)` has finite moments of all orders under a
Gaussian-Gram Wishart law. -/
theorem memLp_trace_mul_wishartGramMeasure
    (Θ : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) (S : Matrix (Fin p) (Fin p) ℝ)
    (ν : ℕ) (q : ℝ≥0) :
    MemLp (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
        ((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace) q
      (wishartGramMeasure ν S) :=
  memLp_trace_mul_of_mgf_trace_mul_eq_det_rpow
    (fun _ ht => mgf_trace_mul_wishartGramMeasure_sqrt ν S ht) q

/-- Every entry of a Gaussian-Gram Wishart matrix has finite moments of all orders. -/
theorem memLp_coe_apply_wishartGramMeasure (S : Matrix (Fin p) (Fin p) ℝ) (ν : ℕ)
    (i j : Fin p) (q : ℝ≥0) :
    MemLp (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
        (A : Matrix (Fin p) (Fin p) ℝ) i j) q (wishartGramMeasure ν S) :=
  memLp_coe_apply_of_mgf_trace_mul_eq_det_rpow
    (fun _ _ ht => mgf_trace_mul_wishartGramMeasure_sqrt ν S ht) i j q

/-- A Gaussian-Gram Wishart matrix has finite moments of all orders. -/
theorem memLp_id_wishartGramMeasure (S : Matrix (Fin p) (Fin p) ℝ) (ν : ℕ) (q : ℝ≥0) :
    MemLp (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) => A) q
      (wishartGramMeasure ν S) :=
  memLp_id_of_mgf_trace_mul_eq_det_rpow
    (fun _ _ ht => mgf_trace_mul_wishartGramMeasure_sqrt ν S ht) q

/-- A Gaussian-Gram Wishart matrix is integrable. -/
theorem integrable_id_wishartGramMeasure (S : Matrix (Fin p) (Fin p) ℝ) (ν : ℕ) :
    Integrable (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) => A)
      (wishartGramMeasure ν S) :=
  integrable_id_of_mgf_trace_mul_eq_det_rpow
    (fun _ _ ht => mgf_trace_mul_wishartGramMeasure_sqrt ν S ht)

/-- **The mean of a symmetric trace statistic under a Gaussian-Gram Wishart law.** The
statistic `A ↦ trace (Θ * A)` has mean `ν * trace (Θ * S)`. -/
theorem integral_trace_mul_wishartGramMeasure (hS : S.PosSemidef)
    (Θ : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) (ν : ℕ) :
    ∫ A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
        ((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace
      ∂wishartGramMeasure ν S =
      (ν : ℝ) * ((Θ : Matrix (Fin p) (Fin p) ℝ) * S).trace :=
  integral_trace_mul_of_mgf_trace_mul_eq_det_rpow hS
    (fun _ ht => mgf_trace_mul_wishartGramMeasure_sqrt ν S ht)

/-- **The variance of a symmetric trace statistic under a Gaussian-Gram Wishart law.** The
statistic `A ↦ trace (Θ * A)` has variance `2 * ν * trace (Θ * S * Θ * S)`, twice the degree
times the trace of the square of `Θ * S`. -/
theorem variance_trace_mul_wishartGramMeasure (hS : S.PosSemidef)
    (Θ : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) (ν : ℕ) :
    Var[fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
        ((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace;
      wishartGramMeasure ν S] =
      2 * (ν : ℝ) *
        (((Θ : Matrix (Fin p) (Fin p) ℝ) * S * (Θ : Matrix (Fin p) (Fin p) ℝ) * S).trace) :=
  variance_trace_mul_of_mgf_trace_mul_eq_det_rpow hS
    (fun _ ht => mgf_trace_mul_wishartGramMeasure_sqrt ν S ht)

/-- **The covariance of two symmetric trace statistics under a Gaussian-Gram Wishart law.** The
statistics `A ↦ trace (Θ * A)` and `A ↦ trace (Φ * A)` have covariance
`2 * ν * trace (Θ * S * Φ * S)`. -/
theorem covariance_trace_mul_wishartGramMeasure (hS : S.PosSemidef)
    (Θ Φ : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) (ν : ℕ) :
    cov[fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
          ((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace,
        fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
          ((Φ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace;
        wishartGramMeasure ν S] =
      2 * (ν : ℝ) *
        (((Θ : Matrix (Fin p) (Fin p) ℝ) * S *
          (Φ : Matrix (Fin p) (Fin p) ℝ) * S).trace) :=
  covariance_trace_mul_of_mgf_trace_mul_eq_det_rpow
    hS Θ Φ (fun _ ht => mgf_trace_mul_wishartGramMeasure_sqrt ν S ht)
      (fun _ ht => mgf_trace_mul_wishartGramMeasure_sqrt ν S ht)
      (fun _ ht => mgf_trace_mul_wishartGramMeasure_sqrt ν S ht)

/-- **The entrywise mean of a Gaussian-Gram Wishart matrix** is `ν Sᵢⱼ`. -/
theorem integral_coe_apply_wishartGramMeasure (hS : S.PosSemidef) (ν : ℕ) (i j : Fin p) :
    ∫ A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
        (A : Matrix (Fin p) (Fin p) ℝ) i j ∂wishartGramMeasure ν S =
      (ν : ℝ) * S i j :=
  integral_coe_apply_of_mgf_trace_mul_eq_det_rpow
    (fun _ _ ht => mgf_trace_mul_wishartGramMeasure_sqrt ν S ht) hS i j

/-- **The mean of a Gaussian-Gram Wishart matrix** is the degree times its scale matrix. -/
theorem integral_id_wishartGramMeasure (hS : S.PosSemidef) (ν : ℕ) :
    ∫ A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ), A ∂wishartGramMeasure ν S =
      (ν : ℝ) •
        (⟨S, Matrix.isHermitian_iff_isSelfAdjoint.1 hS.1⟩ :
          selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :=
  integral_id_of_mgf_trace_mul_eq_det_rpow
    (fun _ _ ht => mgf_trace_mul_wishartGramMeasure_sqrt ν S ht) hS

/-- **The entrywise covariance of a Gaussian-Gram Wishart matrix** is
`ν (Sᵢₖ Sⱼₗ + Sᵢₗ Sⱼₖ)`. -/
theorem covariance_coe_apply_wishartGramMeasure (hS : S.PosSemidef) (ν : ℕ)
    (i j k l : Fin p) :
    cov[fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
          (A : Matrix (Fin p) (Fin p) ℝ) i j,
        fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
          (A : Matrix (Fin p) (Fin p) ℝ) k l;
        wishartGramMeasure ν S] =
      (ν : ℝ) * (S i k * S j l + S i l * S j k) :=
  covariance_coe_apply_of_mgf_trace_mul_eq_det_rpow
    (fun _ _ ht => mgf_trace_mul_wishartGramMeasure_sqrt ν S ht) hS i j k l

end TauCeti
