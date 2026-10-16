/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Matrix.Scaling.Basic
public import TauCeti.InformationTheory.KullbackLeibler.Finite
public import TauCeti.MeasureTheory.OptimalTransport.Finite.TransportMatrix

/-!
# The relative entropy of a finite real transport plan

Let `μ` and `ν` be probability vectors on finite types `ι` and `κ`, and let `f : ι × κ → ℝ` be a
real transport plan with marginals `μ` and `ν` (`TauCeti.RealPlans μ ν`). This file computes the
relative entropy `Matrix.relEntropy` of `f` against the product `μ ⊗ ν` of its marginals, which is
the Kullback–Leibler divergence of the plan from the independent plan. It equals
`H(μ) + H(ν) - H(f)`, where `H` is the Shannon entropy `∑ negMulLog`, and it lies between `0` and
`H(μ) + H(ν)`. The marginals may have zero entries, on whose rows and columns the plan vanishes.

## Main results

* `TauCeti.relEntropy_vecMulVec_eq_of_mem_realPlans`: the relative entropy of a real plan against
  the product of its marginals is `H(μ) + H(ν) - H(f)`.
* `TauCeti.relEntropy_vecMulVec_nonneg_of_mem_realPlans` and
  `TauCeti.relEntropy_vecMulVec_le_of_mem_realPlans`: it lies between `0` and `H(μ) + H(ν)`.

The finite measure KL divergence is also identified with matrix relative entropy,
including Mathlib's finite-measure mass correction.
-/

public section

noncomputable section

open scoped ENNReal BigOperators

namespace TauCeti

open Real

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {μ : PMF ι} {ν : PMF κ} {f : ι × κ → ℝ}

/-- The relative entropy of a real plan `f` against the product of its marginals is
`H(μ) + H(ν) - H(f)`, where `H` is the Shannon entropy `∑ negMulLog`. In particular it differs from
the negative entropy `-H(f)` by a constant on the real plans with marginals `μ` and `ν`. -/
theorem relEntropy_vecMulVec_eq_of_mem_realPlans (hf : f ∈ RealPlans μ ν) :
    Matrix.relEntropy (Matrix.of fun i j ↦ f (i, j))
        (Matrix.vecMulVec (fun i ↦ (μ i).toReal) fun j ↦ (ν j).toReal) =
      ∑ i, negMulLog (μ i).toReal + ∑ j, negMulLog (ν j).toReal - ∑ q, negMulLog (f q) := by
  -- The logarithm of a product splits on every cell that carries mass.
  have hcell : ∀ i j, f (i, j) * log ((μ i).toReal * (ν j).toReal) =
      f (i, j) * log (μ i).toReal + f (i, j) * log (ν j).toReal := fun i j ↦ by
    rcases (hf.1 (i, j)).eq_or_lt with h | h
    · simp [← h]
    · rw [log_mul (h.trans_le (le_toReal_fst_of_mem_realPlans hf (i, j))).ne'
        (h.trans_le (le_toReal_snd_of_mem_realPlans hf (i, j))).ne', mul_add]
  have hrow : ∑ i, ∑ j, f (i, j) * log (μ i).toReal = ∑ i, (μ i).toReal * log (μ i).toReal := by
    simp_rw [← Finset.sum_mul, hf.2.1]
  have hcol : ∑ i, ∑ j, f (i, j) * log (ν j).toReal = ∑ j, (ν j).toReal * log (ν j).toReal := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hf.2.2]
  simp only [Matrix.relEntropy_def, Matrix.of_apply, Matrix.vecMulVec_apply, hcell,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, hrow, hcol, negMulLog, Fintype.sum_prod_type]
  simp only [neg_mul, Finset.sum_neg_distrib]
  ring

/-- The relative entropy of a real plan against the product of its marginals is nonnegative. -/
theorem relEntropy_vecMulVec_nonneg_of_mem_realPlans (hf : f ∈ RealPlans μ ν) :
    0 ≤ Matrix.relEntropy (Matrix.of fun i j ↦ f (i, j))
      (Matrix.vecMulVec (fun i ↦ (μ i).toReal) fun j ↦ (ν j).toReal) := by
  refine Matrix.relEntropy_nonneg_of_nonneg (fun i j ↦ hf.1 (i, j))
    (fun i j ↦ mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg) (fun i j h ↦ ?_) ?_
  · simp only [Matrix.vecMulVec_apply, mul_eq_zero] at h
    rcases h with h | h
    · exact le_antisymm (h ▸ le_toReal_fst_of_mem_realPlans hf (i, j)) (hf.1 (i, j))
    · exact le_antisymm (h ▸ le_toReal_snd_of_mem_realPlans hf (i, j)) (hf.1 (i, j))
  · simp only [Matrix.of_apply, Matrix.vecMulVec_apply, ← Finset.mul_sum, ← Finset.sum_mul,
      hf.2.1, PMF.sum_toReal_eq_one, one_mul]

/-- The relative entropy of a real plan against the product of its marginals is at most
`H(μ) + H(ν)`. -/
theorem relEntropy_vecMulVec_le_of_mem_realPlans (hf : f ∈ RealPlans μ ν) :
    Matrix.relEntropy (Matrix.of fun i j ↦ f (i, j))
        (Matrix.vecMulVec (fun i ↦ (μ i).toReal) fun j ↦ (ν j).toReal) ≤
      ∑ i, negMulLog (μ i).toReal + ∑ j, negMulLog (ν j).toReal := by
  rw [relEntropy_vecMulVec_eq_of_mem_realPlans hf, sub_le_self_iff]
  refine Finset.sum_nonneg fun q _ ↦ negMulLog_nonneg (hf.1 q) ?_
  calc f q ≤ (μ q.1).toReal := le_toReal_fst_of_mem_realPlans hf q
    _ ≤ 1 := ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using μ.coe_le_one q.1)

end TauCeti

open MeasureTheory InformationTheory Matrix

namespace MeasureTheory.Measure

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [MeasurableSpace κ] [MeasurableSingletonClass κ]

/-- For finite measures on a finite product with strictly positive reference masses,
KL divergence is matrix entropy plus Mathlib's finite-measure mass correction.
The plan is encoded by its singleton masses; no separate nonnegativity assumption on
`P` is needed. -/
theorem klDiv_eq_ofReal_relEntropy_add_mass_correction_of_real_singleton
    (π R : Measure (ι × κ)) [IsFiniteMeasure π] [IsFiniteMeasure R]
    (P K : Matrix ι κ ℝ)
    (hπ : ∀ i j, π.real {(i, j)} = P i j)
    (hR : ∀ i j, R.real {(i, j)} = K i j)
    (hK : ∀ i j, 0 < K i j) :
    klDiv π R = ENNReal.ofReal
      (Matrix.relEntropy P K + R.real Set.univ - π.real Set.univ) := by
  have hRpos : ∀ q : ι × κ, R {q} ≠ 0 := by
    rintro ⟨i, j⟩ hzero
    have h := hK i j
    rw [← hR i j] at h
    simp [Measure.real, hzero] at h
  rw [TauCeti.klDiv_eq_ofReal_sum_log_singleton hRpos]
  have hsum :
      (∑ q : ι × κ, π.real {q} * Real.log (π.real {q} / R.real {q})) =
        Matrix.relEntropy P K := by
    rw [Matrix.relEntropy_def, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hπ i j, hR i j]
    by_cases hP : P i j = 0
    · simp [hP]
    · rw [Real.log_div hP (ne_of_gt (hK i j))]
      ring
  rw [hsum]

end MeasureTheory.Measure
