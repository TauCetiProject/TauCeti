/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Wishart.Transforms

import TauCeti.Analysis.SpecialFunctions.Log.SumLogOneSub
import TauCeti.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# Moments of the Gaussian-Gram Wishart family

This file computes the first two moments of the Gaussian-Gram Wishart family
`wishartGramMeasure ν S`.  A symmetric trace statistic `A ↦ trace (Θ * A)` has mean
`ν * trace (Θ * S)` and variance `2 * ν * trace (Θ * S * Θ * S)`, two such statistics have
covariance `2 * ν * trace (Θ * S * Φ * S)`, and the matrix itself has mean `(ν : ℝ) • S` and
entrywise covariance `ν * (S i k * S j l + S i l * S j k)`.  These are the second-order data of
the family: they exhibit `(ν : ℝ) • S` as its centre and describe the fluctuation of any
quadratic form in the underlying Gaussian sample.

## Main results

* `TauCeti.memLp_trace_mul_wishartGramMeasure`, `TauCeti.memLp_coe_apply_wishartGramMeasure`
  and `TauCeti.memLp_id_wishartGramMeasure` give finite moments of all orders for trace
  statistics, entries and the matrix itself;
* `TauCeti.integral_trace_mul_wishartGramMeasure` computes the mean of every symmetric trace
  statistic;
* `TauCeti.variance_trace_mul_wishartGramMeasure` computes its variance;
* `TauCeti.covariance_trace_mul_wishartGramMeasure` computes the covariance of two trace
  statistics;
* `TauCeti.integral_id_wishartGramMeasure` gives the Bochner mean, while
  `TauCeti.integral_coe_apply_wishartGramMeasure` and
  `TauCeti.covariance_coe_apply_wishartGramMeasure` give the entrywise mean and covariance.

## References

* R. J. Muirhead, *Aspects of Multivariate Statistical Theory*, Wiley (1982), Theorem 3.2.3.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

open scoped RealInnerProductSpace Matrix MatrixOrder NNReal Topology

namespace TauCeti

variable {p ν : ℕ} {S : Matrix (Fin p) (Fin p) ℝ}

private lemma zero_mem_interior_integrableExpSet_trace_mul_wishartGramMeasure
    (Θ : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) (S : Matrix (Fin p) (Fin p) ℝ)
    (ν : ℕ) :
    (0 : ℝ) ∈ interior
      (integrableExpSet (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
        (((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace))
        (wishartGramMeasure ν S)) := by
  by_cases hν : ν = 0
  · subst ν
    rw [integrableExpSet_trace_mul_wishartGramMeasure_zero]
    simp
  · rw [mem_interior_iff_mem_nhds]
    have hB : (CFC.sqrt S * (Θ : Matrix (Fin p) (Fin p) ℝ) * CFC.sqrt S).IsHermitian :=
      Matrix.isHermitian_sqrt_mul_mul_sqrt S (selfAdjoint.isHermitian_coe Θ)
    filter_upwards [((continuous_const_mul (2 : ℝ)).tendsto' 0 0 (mul_zero 2)).eventually
      hB.eventually_posDef_one_sub_smul] with t ht
    exact (mem_integrableExpSet_trace_mul_wishartGramMeasure_iff (Nat.pos_of_ne_zero hν) S t).2 ht

private lemma cgf_trace_mul_wishartGramMeasure_eventuallyEq_sum_log
    (Θ : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) (S : Matrix (Fin p) (Fin p) ℝ)
    (ν : ℕ) :
    cgf (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
        (((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace))
        (wishartGramMeasure ν S) =ᶠ[𝓝 0]
      fun t => -(ν : ℝ) / 2 * ∑ j,
        Real.log (1 - 2 * t *
          (Matrix.isHermitian_sqrt_mul_mul_sqrt S
            (selfAdjoint.isHermitian_coe Θ)).eigenvalues j) := by
  let B := CFC.sqrt S * (Θ : Matrix (Fin p) (Fin p) ℝ) * CFC.sqrt S
  let hB : B.IsHermitian :=
    Matrix.isHermitian_sqrt_mul_mul_sqrt S (selfAdjoint.isHermitian_coe Θ)
  filter_upwards [((continuous_const_mul (2 : ℝ)).tendsto' 0 0 (mul_zero 2)).eventually
      hB.eventually_posDef_one_sub_smul] with t ht
  rw [cgf_trace_mul_wishartGramMeasure_sqrt ν S ht, hB.det_one_sub_smul]
  rw [Real.log_prod]
  · rfl
  · intro j _
    rw [hB.posDef_one_sub_smul_iff] at ht
    exact (sub_pos.2 (ht j)).ne'

/-! ### Finite moments -/

/-- Every symmetric trace statistic `A ↦ trace (Θ * A)` has finite moments of all orders under a
Gaussian-Gram Wishart law. -/
theorem memLp_trace_mul_wishartGramMeasure
    (Θ : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) (S : Matrix (Fin p) (Fin p) ℝ)
    (ν : ℕ) (q : ℝ≥0) :
    MemLp (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
        ((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace) q
      (wishartGramMeasure ν S) :=
  memLp_of_mem_interior_integrableExpSet
    (zero_mem_interior_integrableExpSet_trace_mul_wishartGramMeasure Θ S ν) q

/-- Every entry of a Gaussian-Gram Wishart matrix has finite moments of all orders. -/
theorem memLp_coe_apply_wishartGramMeasure (S : Matrix (Fin p) (Fin p) ℝ) (ν : ℕ)
    (i j : Fin p) (q : ℝ≥0) :
    MemLp (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
        (A : Matrix (Fin p) (Fin p) ℝ) i j) q (wishartGramMeasure ν S) := by
  simpa only [trace_symmetricEntry_mul_coe] using
    memLp_trace_mul_wishartGramMeasure (symmetricEntry i j) S ν q

/-- A Gaussian-Gram Wishart matrix has finite moments of all orders. -/
theorem memLp_id_wishartGramMeasure (S : Matrix (Fin p) (Fin p) ℝ) (ν : ℕ) (q : ℝ≥0) :
    MemLp (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) => A) q
      (wishartGramMeasure ν S) := by
  have hcoordinates : MemLp
      (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
        symmetricCoordinates p A) q (wishartGramMeasure ν S) :=
    MemLp.of_eval fun ij => by
      simpa only [symmetricCoordinates_apply] using
        memLp_coe_apply_wishartGramMeasure S ν ij.1.1 ij.1.2 q
  have hcomp :
      ((symmetricCoordinates p).symm.toContinuousLinearMap ∘
        fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) => symmetricCoordinates p A) =
        fun A => A := by
    funext A
    simp
  rw [← hcomp]
  exact (symmetricCoordinates p).symm.toContinuousLinearMap.comp_memLp' hcoordinates

/-- A Gaussian-Gram Wishart matrix is integrable. -/
theorem integrable_id_wishartGramMeasure (S : Matrix (Fin p) (Fin p) ℝ) (ν : ℕ) :
    Integrable (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) => A)
      (wishartGramMeasure ν S) :=
  memLp_one_iff_integrable.1 (by exact_mod_cast memLp_id_wishartGramMeasure S ν 1)

/-! ### Trace statistics -/

/-- **The mean of a symmetric trace statistic under a Gaussian-Gram Wishart law.** The
statistic `A ↦ trace (Θ * A)` has mean `ν * trace (Θ * S)`. -/
theorem integral_trace_mul_wishartGramMeasure (hS : S.PosSemidef)
    (Θ : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) (ν : ℕ) :
    ∫ A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
        ((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace
      ∂wishartGramMeasure ν S =
      (ν : ℝ) * ((Θ : Matrix (Fin p) (Fin p) ℝ) * S).trace := by
  let X := fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
    ((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace
  let hB := Matrix.isHermitian_sqrt_mul_mul_sqrt S (selfAdjoint.isHermitian_coe Θ)
  have hzero := zero_mem_interior_integrableExpSet_trace_mul_wishartGramMeasure Θ S ν
  have heq := cgf_trace_mul_wishartGramMeasure_eventuallyEq_sum_log Θ S ν
  calc
    ∫ A, X A ∂wishartGramMeasure ν S = deriv (cgf X (wishartGramMeasure ν S)) 0 := by
      simpa [X] using (deriv_cgf_zero hzero).symm
    _ = deriv (fun t => -(ν : ℝ) / 2 * ∑ j, Real.log (1 - 2 * t * hB.eigenvalues j)) 0 :=
      heq.deriv_eq
    _ = (ν : ℝ) * ∑ j, hB.eigenvalues j :=
      (hasDerivAt_neg_half_mul_sum_log (ν : ℝ) hB.eigenvalues).deriv
    _ = (ν : ℝ) *
        (CFC.sqrt S * (Θ : Matrix (Fin p) (Fin p) ℝ) * CFC.sqrt S).trace := by
      rw [hB.trace_eq_sum_eigenvalues]
      simp
    _ = (ν : ℝ) * ((Θ : Matrix (Fin p) (Fin p) ℝ) * S).trace := by
      rw [hS.trace_sqrt_mul_mul_sqrt]

/-- **The variance of a symmetric trace statistic under a Gaussian-Gram Wishart law.** The
statistic `A ↦ trace (Θ * A)` has variance `2 * ν * trace (Θ * S * Θ * S)`, twice the degree
times the trace of the square of `Θ * S`. -/
theorem variance_trace_mul_wishartGramMeasure (hS : S.PosSemidef)
    (Θ : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) (ν : ℕ) :
    Var[fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
        ((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace;
      wishartGramMeasure ν S] =
      2 * (ν : ℝ) *
        (((Θ : Matrix (Fin p) (Fin p) ℝ) * S * (Θ : Matrix (Fin p) (Fin p) ℝ) * S).trace) := by
  let X := fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
    ((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace
  let B := CFC.sqrt S * (Θ : Matrix (Fin p) (Fin p) ℝ) * CFC.sqrt S
  let hB : B.IsHermitian :=
    Matrix.isHermitian_sqrt_mul_mul_sqrt S (selfAdjoint.isHermitian_coe Θ)
  have hzero := zero_mem_interior_integrableExpSet_trace_mul_wishartGramMeasure Θ S ν
  have heq := cgf_trace_mul_wishartGramMeasure_eventuallyEq_sum_log Θ S ν
  have hcumulant : iteratedDeriv 2 (cgf X (wishartGramMeasure ν S)) 0 =
      2 * (ν : ℝ) * ∑ j, hB.eigenvalues j ^ 2 := by
    rw [heq.iteratedDeriv_eq 2]
    exact iteratedDeriv_two_neg_half_mul_sum_log (ν : ℝ) hB.eigenvalues
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
          (Φ : Matrix (Fin p) (Fin p) ℝ) * S).trace) := by
  let X := fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
    ((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace
  let Y := fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
    ((Φ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace
  have hX : MemLp X 2 (wishartGramMeasure ν S) :=
    memLp_trace_mul_wishartGramMeasure Θ S ν 2
  have hY : MemLp Y 2 (wishartGramMeasure ν S) :=
    memLp_trace_mul_wishartGramMeasure Φ S ν 2
  have hsum : X + Y = fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
      ((((Θ + Φ : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
        Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace) := by
    funext A
    simp [X, Y, Matrix.add_mul, Matrix.trace_add]
  have hpolar := variance_add hX hY
  rw [hsum, variance_trace_mul_wishartGramMeasure hS (Θ + Φ) ν,
    variance_trace_mul_wishartGramMeasure hS Θ ν,
    variance_trace_mul_wishartGramMeasure hS Φ ν] at hpolar
  rw [Submodule.coe_add, Matrix.trace_add_mul_add_mul] at hpolar
  dsimp [X, Y] at hpolar
  linarith

/-! ### Matrix entries -/

/-- **The entrywise mean of a Gaussian-Gram Wishart matrix** is `ν Sᵢⱼ`. -/
theorem integral_coe_apply_wishartGramMeasure (hS : S.PosSemidef) (ν : ℕ) (i j : Fin p) :
    ∫ A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
        (A : Matrix (Fin p) (Fin p) ℝ) i j ∂wishartGramMeasure ν S =
      (ν : ℝ) * S i j := by
  have h := integral_trace_mul_wishartGramMeasure hS (symmetricEntry i j) ν
  simpa only [trace_symmetricEntry_mul_coe, trace_symmetricEntry_mul i j hS.1] using h

/-- **The mean of a Gaussian-Gram Wishart matrix** is the degree times its scale matrix. -/
theorem integral_id_wishartGramMeasure (hS : S.PosSemidef) (ν : ℕ) :
    ∫ A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ), A ∂wishartGramMeasure ν S =
      (ν : ℝ) •
        (⟨S, Matrix.isHermitian_iff_isSelfAdjoint.1 hS.1⟩ :
          selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) := by
  have hcoordinates : Integrable
      (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
        symmetricCoordinates p A) (wishartGramMeasure ν S) :=
    (symmetricCoordinates p).toContinuousLinearMap.integrable_comp
      (integrable_id_wishartGramMeasure S ν)
  apply (symmetricCoordinates p).injective
  funext ij
  rw [← (symmetricCoordinates p).integral_comp_comm,
    eval_integral (fun ij => hcoordinates.eval ij)]
  simp only [symmetricCoordinates_apply, Submodule.coe_smul, Matrix.smul_apply]
  rw [integral_coe_apply_wishartGramMeasure hS]
  simp

/-- **The entrywise covariance of a Gaussian-Gram Wishart matrix** is
`ν (Sᵢₖ Sⱼₗ + Sᵢₗ Sⱼₖ)`. -/
theorem covariance_coe_apply_wishartGramMeasure (hS : S.PosSemidef) (ν : ℕ)
    (i j k l : Fin p) :
    cov[fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
          (A : Matrix (Fin p) (Fin p) ℝ) i j,
        fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
          (A : Matrix (Fin p) (Fin p) ℝ) k l;
        wishartGramMeasure ν S] =
      (ν : ℝ) * (S i k * S j l + S i l * S j k) := by
  have h := covariance_trace_mul_wishartGramMeasure hS
    (symmetricEntry i j) (symmetricEntry k l) ν
  rw [trace_symmetricEntry_mul_mul_symmetricEntry_mul i j k l hS.1] at h
  have hi : (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
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
  rw [hi, hkl] at h
  rw [h]
  ring

end TauCeti
