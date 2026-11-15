/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.LKJ.Basic
public import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Probability.Moments.Basic
import TauCeti.Analysis.Matrix.PosSemidef.Basic

/-!
# Exponential integrability of LKJ linear observables

Every real linear observable of an LKJ correlation matrix has finite exponential moments of
all orders. We express these observables by the Frobenius trace pairing with a bundled symmetric
matrix, as for Wishart laws. The bound on correlation entries gives a uniform bound on each trace
statistic; there is no claim of a closed-form moment-generating function.

`integrableExpSet_trace_mul_lkjMeasure` gives the exact domain, including the zero measure at
invalid shapes and the Dirac laws in dimensions zero and one. The `HasLaw` version transfers
this domain to random matrices on an arbitrary probability space.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti.Probability

/-- Every real trace statistic under an LKJ law has exponential-integrability domain `ℝ`.
This also holds for nonpositive shapes, where the measure is zero. -/
@[simp]
theorem integrableExpSet_trace_mul_lkjMeasure (p : ℕ) (η : ℝ)
    (Θ : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
    integrableExpSet (fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
      ((Θ : Matrix (Fin p) (Fin p) ℝ) * (R : Matrix (Fin p) (Fin p) ℝ)).trace)
      (lkjMeasure p η) = univ := by
  by_cases hη : 0 < η
  · have := isProbabilityMeasure_lkjMeasure (p := p) hη
    ext t
    simp only [integrableExpSet, mem_ofPred_eq, mem_univ, iff_true]
    refine integrable_exp_mul_of_mem_Icc
      (a := -(∑ i, ∑ j, |(Θ : Matrix (Fin p) (Fin p) ℝ) i j|))
      (b := ∑ i, ∑ j, |(Θ : Matrix (Fin p) (Fin p) ℝ) i j|)
      (selfAdjoint.continuous_trace_mul_coe Θ).measurable.aemeasurable ?_
    filter_upwards [ae_posDef_lkjMeasure p η, ae_diag_eq_one_lkjMeasure p η] with R hR hd
    apply abs_le.mp
    calc
      |((Θ : Matrix (Fin p) (Fin p) ℝ) * (R : Matrix (Fin p) (Fin p) ℝ)).trace| =
          |∑ i, ∑ j, (Θ : Matrix (Fin p) (Fin p) ℝ) i j *
            (R : Matrix (Fin p) (Fin p) ℝ) j i| := by
        simp [Matrix.trace, Matrix.mul_apply]
      _ ≤ ∑ i, ∑ j, |(Θ : Matrix (Fin p) (Fin p) ℝ) i j *
            (R : Matrix (Fin p) (Fin p) ℝ) j i| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun i _ ↦ Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ i, ∑ j, |(Θ : Matrix (Fin p) (Fin p) ℝ) i j| := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        apply mul_le_of_le_one_right (abs_nonneg _)
        simpa only [Real.norm_eq_abs] using
          hR.posSemidef.norm_le_one_of_apply_self_eq_one (hd j) (hd i)
  · simp [lkjMeasure_of_nonpos (not_lt.mp hη), integrableExpSet]

end TauCeti.Probability

namespace ProbabilityTheory.HasLaw

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {p : ℕ} {η : ℝ}
    {X : Ω → selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)}

/-- Every real trace statistic of a random matrix with an LKJ law has finite exponential
moments of every order. -/
theorem integrableExpSet_trace_mul_lkjMeasure
    (hX : HasLaw X (TauCeti.Probability.lkjMeasure p η) P)
    (Θ : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
    integrableExpSet (fun ω ↦
      ((Θ : Matrix (Fin p) (Fin p) ℝ) * (X ω : Matrix (Fin p) (Fin p) ℝ)).trace) P = univ := by
  apply Set.eq_univ_of_forall
  intro t
  have ht := TauCeti.Probability.integrableExpSet_trace_mul_lkjMeasure p η Θ
  rw [Set.eq_univ_iff_forall] at ht
  exact hX.integrable_fun_comp (ht t)

end ProbabilityTheory.HasLaw
