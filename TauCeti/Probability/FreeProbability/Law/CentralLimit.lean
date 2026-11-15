/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.FreeProbability.CentralLimit
public import TauCeti.Probability.FreeProbability.Law.Convergence

/-!
# Weak convergence in the free central limit theorem

In a C⋆-probability space, the laws of normalized sums of centered free selfadjoint elements
converge weakly to the centered semicircle law. The general theorem assumes uniform bounds on
each scalar moment and convergence of the average variance; identical distribution is not
required. The identically distributed case is provided separately.

These are weak-convergence consequences of the algebraic moment free CLT and the method of
moments. No trace, faithful state, or uniform operator-norm bound on the summands is assumed.
The conclusion includes variance zero, when the limit is the point mass at zero, and asserts
neither operator-norm convergence nor almost-sure convergence.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Theorem 8.10.
* P. Billingsley, *Probability and Measure*, 3rd ed., Theorem 30.2.
-/

public section

open MeasureTheory Filter Topology Finset
open scoped ComplexOrder NNReal

namespace TauCeti.IsFreelyIndependentElements

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {φ : A →ₚ[ℂ] ℂ} {a : ℕ → A}

private theorem tendsto_law_inv_sqrt_smul_sum_of_tendsto_moments
    (hφ : φ 1 = 1) (ha : ∀ j, IsSelfAdjoint (a j)) {v : ℝ≥0}
    (hmom : ∀ n : ℕ,
      Tendsto (fun N : ℕ => φ (((Real.sqrt N : ℂ)⁻¹ • ∑ j ∈ range N, a j) ^ n)) atTop
        (𝓝 ((∫ x, x ^ n ∂Probability.semicircleReal 0 v : ℝ) : ℂ))) :
    Tendsto (β := ProbabilityMeasure ℝ) (fun N : ℕ =>
      ⟨φ.law ((Real.sqrt N)⁻¹ • ∑ j ∈ range N, a j),
        φ.isProbabilityMeasure_law hφ
          ((IsSelfAdjoint.all _).smul (isSelfAdjoint_sum _ fun j _ => ha j))⟩) atTop
      (𝓝 (Probability.semicircleReal 0 v).toProbabilityMeasure) := by
  apply PositiveLinearMap.tendsto_law_of_tendsto_apply_pow (fun _ => φ) (fun _ => hφ)
    (fun N : ℕ => (Real.sqrt N)⁻¹ • ∑ j ∈ range N, a j)
    (fun _ => (IsSelfAdjoint.all _).smul (isSelfAdjoint_sum _ fun j _ => ha j))
    (K := Set.Icc (0 - 2 * Real.sqrt v) (0 + 2 * Real.sqrt v)) isCompact_Icc
  · exact ae_iff.mp (Probability.ae_mem_Icc_semicircleReal 0 v)
  · intro n
    simpa only [RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.ofReal_eq_complex_ofReal,
      Complex.ofReal_inv, Measure.coe_toProbabilityMeasure, PositiveLinearMap.coe_toLinearMap] using
      hmom n

/-- **The weak free central limit theorem.** Centered free selfadjoint elements whose moments
are uniformly bounded in each degree and whose average variance tends to `v ≥ 0` have
normalized-sum laws converging weakly to `semicircleReal 0 v`. No common compact support of the
approximating laws is required. -/
theorem tendsto_law_inv_sqrt_smul_sum_semicircleReal
    (h : IsFreelyIndependentElements φ.toLinearMap a) (hφ : φ 1 = 1)
    (ha : ∀ j, IsSelfAdjoint (a j)) (hcen : ∀ j, φ (a j) = 0)
    (hbdd : ∀ k : ℕ, ∃ M, ∀ j, ‖φ (a j ^ k)‖ ≤ M) {v : ℝ≥0}
    (hvar : Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ j ∈ range N, φ (a j ^ 2)) atTop
      (𝓝 ((v : ℝ) : ℂ))) :
    Tendsto (β := ProbabilityMeasure ℝ) (fun N : ℕ =>
      ⟨φ.law ((Real.sqrt N)⁻¹ • ∑ j ∈ range N, a j),
        φ.isProbabilityMeasure_law hφ
          ((IsSelfAdjoint.all _).smul (isSelfAdjoint_sum _ fun j _ => ha j))⟩) atTop
      (𝓝 (Probability.semicircleReal 0 v).toProbabilityMeasure) := by
  exact tendsto_law_inv_sqrt_smul_sum_of_tendsto_moments hφ ha
    (h.tendsto_apply_inv_sqrt_smul_sum_pow_semicircleReal hφ hcen hbdd hvar)

/-- **The weak free central limit theorem for identically distributed elements.** If centered
free selfadjoint elements have the same scalar moments and variance `v ≥ 0`, the laws of their
normalized sums converge weakly to `semicircleReal 0 v`. Equality of scalar moments suffices;
no trace or faithfulness is needed. -/
theorem tendsto_law_inv_sqrt_smul_sum_of_apply_pow_eq
    (h : IsFreelyIndependentElements φ.toLinearMap a) (hφ : φ 1 = 1)
    (ha : ∀ j, IsSelfAdjoint (a j))
    (hid : ∀ j k : ℕ, φ (a j ^ k) = φ (a 0 ^ k)) (hcen : φ (a 0) = 0) {v : ℝ≥0}
    (hv : φ (a 0 ^ 2) = ((v : ℝ) : ℂ)) :
    Tendsto (β := ProbabilityMeasure ℝ) (fun N : ℕ =>
      ⟨φ.law ((Real.sqrt N)⁻¹ • ∑ j ∈ range N, a j),
        φ.isProbabilityMeasure_law hφ
          ((IsSelfAdjoint.all _).smul (isSelfAdjoint_sum _ fun j _ => ha j))⟩) atTop
      (𝓝 (Probability.semicircleReal 0 v).toProbabilityMeasure) := by
  exact tendsto_law_inv_sqrt_smul_sum_of_tendsto_moments hφ ha
    (h.tendsto_apply_inv_sqrt_smul_sum_pow_of_apply_pow_eq hφ hid hcen hv)

end TauCeti.IsFreelyIndependentElements
