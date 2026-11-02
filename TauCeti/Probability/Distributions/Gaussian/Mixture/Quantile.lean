/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Gaussian.Mixture.Basic
public import TauCeti.Probability.Quantile
import TauCeti.Probability.Distributions.Gaussian.Cdf

/-!
# Cdfs and quantiles of Gaussian mixtures

The cdf of a scalar Gaussian mixture is the weighted sum `∑ i, pᵢ * F_{N(mᵢ, vᵢ)}` of the
component cdfs, where a zero-variance component contributes a unit step at its mean. The
quantile at a level `0 < u < 1` is characterized by the Galois adjunction `Q(u) ≤ x ↔ u ≤ F(x)`
with this cdf.

As soon as one positive-weight component has nonzero variance, the cdf is strictly increasing on
the whole line. The mixture then has full topological support, its quantile is continuous on
`(0, 1)` even if other components are atoms, and the quantile tends to minus and plus infinity
at the endpoints. If every positive-weight component has nonzero variance, the cdf is moreover
continuous, so every interior quantile is the unique real root of `F(x) = u`.

## References

* G. McLachlan and D. Peel, *Finite Mixture Models*, Wiley (2000), Chapter 1.
-/

public section

noncomputable section

open Convexity Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι]
variable {p : StdSimplex ℝ≥0 ι} {m : ι → ℝ} {v : ι → ℝ≥0} {u x : ℝ}

/-- The cdf of a Gaussian mixture is the weighted sum of the Gaussian cdfs, including the unit
steps of zero-variance components. -/
theorem cdf_gaussianMixtureMeasure (p : StdSimplex ℝ≥0 ι) (m : ι → ℝ) (v : ι → ℝ≥0) (x : ℝ) :
    cdf (gaussianMixtureMeasure p m v) x =
      ∑ i, (p.weights i : ℝ) * cdf (gaussianReal (m i) (v i)) x := by
  rw [cdf_eq_real, measureReal_def, gaussianMixtureMeasure_def, Measure.finsetSum_apply,
    ENNReal.toReal_sum fun i _ ↦ by simp [ENNReal.mul_eq_top]]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.coe_toReal, cdf_eq_real,
    measureReal_def]

/-- **Quantile adjunction.** At an interior level, the Gaussian-mixture quantile lies below `x`
exactly when the mixture cdf at `x` reaches the level. -/
theorem quantile_gaussianMixtureMeasure_le_iff (hu : u ∈ Ioo 0 1) :
    (gaussianMixtureMeasure p m v).quantile u ≤ x ↔
      u ≤ ∑ i, (p.weights i : ℝ) * cdf (gaussianReal (m i) (v i)) x := by
  rw [Measure.quantile_le_iff _ hu.1 hu.2, cdf_gaussianMixtureMeasure]

/-- The cdf of a Gaussian mixture is strictly increasing as soon as one positive-weight
component has nonzero variance. -/
theorem strictMono_cdf_gaussianMixtureMeasure (h : ∃ i, 0 < p.weights i ∧ v i ≠ 0) :
    StrictMono (cdf (gaussianMixtureMeasure p m v)) := by
  intro x y hxy
  obtain ⟨j, hj, hvj⟩ := h
  simp only [cdf_gaussianMixtureMeasure]
  exact Finset.sum_lt_sum
    (fun i _ ↦ mul_le_mul_of_nonneg_left (monotone_cdf _ hxy.le) (NNReal.coe_nonneg _))
    ⟨j, Finset.mem_univ j,
      mul_lt_mul_of_pos_left (strictMono_cdf_gaussianReal (m j) hvj hxy) (NNReal.coe_pos.mpr hj)⟩

/-- A Gaussian mixture with a positive-weight component of nonzero variance has full topological
support. -/
@[simp]
theorem support_gaussianMixtureMeasure (h : ∃ i, 0 < p.weights i ∧ v i ≠ 0) :
    (gaussianMixtureMeasure p m v).support = univ :=
  Measure.support_eq_univ_of_strictMono_cdf _ (strictMono_cdf_gaussianMixtureMeasure h)

/-- If every positive-weight component has nonzero variance, the mixture cdf is continuous. -/
theorem continuous_cdf_gaussianMixtureMeasure (hv : ∀ i, 0 < p.weights i → v i ≠ 0) :
    Continuous (cdf (gaussianMixtureMeasure p m v)) := by
  have := nullSingletonClass_gaussianMixtureMeasure (m := m) hv
  exact Measure.continuous_cdf_of_noAtoms _

/-- If every positive-weight component has nonzero variance, each interior quantile is the
unique real root of the mixture cdf. -/
theorem quantile_gaussianMixtureMeasure_eq_iff (hv : ∀ i, 0 < p.weights i → v i ≠ 0)
    (hu : u ∈ Ioo 0 1) :
    (gaussianMixtureMeasure p m v).quantile u = x ↔
      ∑ i, (p.weights i : ℝ) * cdf (gaussianReal (m i) (v i)) x = u := by
  rw [← cdf_gaussianMixtureMeasure]
  constructor
  · rintro rfl
    exact Measure.cdf_quantile _ (continuous_cdf_gaussianMixtureMeasure hv) hu.1 hu.2
  · intro h
    rw [← h]
    obtain ⟨i, hi⟩ := p.support_weights_nonempty
    have hwi : 0 < p.weights i := pos_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
    exact Measure.quantile_cdf _
      ((strictMono_cdf_gaussianMixtureMeasure ⟨i, hwi, hv i hwi⟩).strictMonoOn _)
      (by rw [h]; exact hu)

/-- If every positive-weight component has nonzero variance, the quantile is strictly increasing
on `(0, 1)`. -/
theorem strictMonoOn_quantile_gaussianMixtureMeasure (hv : ∀ i, 0 < p.weights i → v i ≠ 0) :
    StrictMonoOn (gaussianMixtureMeasure p m v).quantile (Ioo 0 1) :=
  Measure.strictMonoOn_quantile _ (continuous_cdf_gaussianMixtureMeasure hv)

/-- The quantile is continuous on `(0, 1)` as soon as one positive-weight component has nonzero
variance, even when other components are atoms. -/
theorem continuousOn_quantile_gaussianMixtureMeasure (h : ∃ i, 0 < p.weights i ∧ v i ≠ 0) :
    ContinuousOn (gaussianMixtureMeasure p m v).quantile (Ioo 0 1) :=
  Measure.continuousOn_quantile_of_strictMonoOn _ ordConnected_univ
    ((strictMono_cdf_gaussianMixtureMeasure h).strictMonoOn _) (mapsTo_univ _ _)

/-- With a positive-weight component of nonzero variance, the quantile tends to minus infinity as
the level tends to zero. -/
theorem tendsto_quantile_gaussianMixtureMeasure_nhdsGT_zero
    (h : ∃ i, 0 < p.weights i ∧ v i ≠ 0) :
    Tendsto (fun u ↦ ((gaussianMixtureMeasure p m v).quantile u : EReal)) (𝓝[>] 0) (𝓝 ⊥) :=
  Measure.tendsto_quantile_nhdsGT_zero_of_cdf_pos _ fun x ↦
    (cdf_nonneg _ (x - 1)).trans_lt (strictMono_cdf_gaussianMixtureMeasure h (by linarith))

/-- With a positive-weight component of nonzero variance, the quantile tends to plus infinity as
the level tends to one. -/
theorem tendsto_quantile_gaussianMixtureMeasure_nhdsLT_one
    (h : ∃ i, 0 < p.weights i ∧ v i ≠ 0) :
    Tendsto (fun u ↦ ((gaussianMixtureMeasure p m v).quantile u : EReal)) (𝓝[<] 1) (𝓝 ⊤) :=
  Measure.tendsto_quantile_nhdsLT_one_of_cdf_lt_one _ fun x ↦
    (strictMono_cdf_gaussianMixtureMeasure h (by linarith : x < x + 1)).trans_le
      (cdf_le_one _ (x + 1))

end TauCeti.Probability
