/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.ChiSquared.Quantile
public import TauCeti.Probability.Distributions.InverseGamma.Quantile
public import TauCeti.Probability.Distributions.Wishart.Inverse.Marginal
public import TauCeti.Probability.Distributions.Wishart.Marginal
public import TauCeti.Probability.Quantile.Map

/-!
# Diagonal quantiles of Wishart laws

Every diagonal entry of a Wishart matrix is a scaled chi-squared variable. The marginal identities
in `TauCeti.Probability.Distributions.Wishart.Marginal` cover both the natural-degree Gaussian-Gram
family and the real-degree density family; this file uses them to compute diagonal quantiles. For a
positive-semidefinite scale `S`, the Gaussian-Gram formula includes zero degrees and zero diagonal
scale, when the entry is constant.

Diagonal entries of inverse-Wishart matrices are inverse-gamma variables. Their quantiles are
therefore the scale divided by an inverse regularized Gamma value. The one-sided endpoint limits
record the support of all three kinds of diagonal marginal.

## Main results

* `TauCeti.Probability.quantile_map_coe_apply_wishartGramMeasure` computes Gaussian-Gram Wishart
  diagonal quantiles, including the degenerate cases;
* `TauCeti.Probability.quantile_map_coe_apply_nonsingularWishartMeasure` computes nonsingular
  Wishart diagonal quantiles;
* `TauCeti.Probability.quantile_map_coe_apply_inverseWishartMeasure` computes inverse-Wishart
  diagonal quantiles;
* the six `tendsto_quantile_map_coe_apply_*` theorems give their one-sided endpoint limits.

## References

* R. J. Muirhead, *Aspects of Multivariate Statistical Theory*, Wiley, 1982, chapter 3.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped Matrix

namespace TauCeti.Probability

variable {p : ℕ} {n u : ℝ} {S : Matrix (Fin p) (Fin p) ℝ}

/-- The quantile of a Gaussian-Gram Wishart diagonal entry is its diagonal scale times the
chi-squared quantile. The formula includes zero degrees and zero scale. -/
@[simp]
theorem quantile_map_coe_apply_wishartGramMeasure (hS : S.PosSemidef) (ν : ℕ) (i : Fin p)
    (hu : u ∈ Ioo 0 1) :
    ((wishartGramMeasure ν S).map
      (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
        (A : Matrix (Fin p) (Fin p) ℝ) i i)).quantile u =
        S i i * (2 * inverseRegularizedGamma (ν / 2) u) := by
  let _ := isProbabilityMeasure_chiSquaredMeasure (Nat.cast_nonneg ν)
  rw [map_coe_apply_wishartGramMeasure hS ν i,
    Measure.quantile_map_of_monotone
      (fun _ _ hxy ↦ mul_le_mul_of_nonneg_left hxy hS.diag_nonneg)
      (continuous_const.mul continuous_id) hu.1 hu.2,
    quantile_chiSquaredMeasure (Nat.cast_nonneg ν) hu]

/-- The quantile of a nonsingular Wishart diagonal entry is its diagonal scale times the
chi-squared quantile. -/
@[simp]
theorem quantile_map_coe_apply_nonsingularWishartMeasure (hS : S.PosDef)
    (hn : (p : ℝ) - 1 < n)
    (i : Fin p) (hu : u ∈ Ioo 0 1) :
    ((nonsingularWishartMeasure n S).map
      (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
        (A : Matrix (Fin p) (Fin p) ℝ) i i)).quantile u =
        S i i * (2 * inverseRegularizedGamma (n / 2) u) := by
  have hn0 : 0 < n := by
    have hp : 1 ≤ p := Nat.one_le_iff_ne_zero.2 fun hp ↦ by
      simpa [hp] using i.isLt
    have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  let _ := isProbabilityMeasure_chiSquaredMeasure hn0.le
  rw [map_coe_apply_nonsingularWishartMeasure hS hn i,
    Measure.quantile_map_of_monotone
      (fun _ _ hxy ↦ mul_le_mul_of_nonneg_left hxy hS.diag_pos.le)
      (continuous_const.mul continuous_id) hu.1 hu.2,
    quantile_chiSquaredMeasure hn0.le hu]

/-- The quantile of an inverse-Wishart diagonal entry is its diagonal scale divided by twice an
inverse regularized Gamma value at the complementary level. -/
@[simp]
theorem quantile_map_coe_apply_inverseWishartMeasure (hS : S.PosDef)
    (hn : (p : ℝ) - 1 < n) (i : Fin p) (hu : u ∈ Ioo 0 1) :
    ((inverseWishartMeasure n S).map
      (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
        (A : Matrix (Fin p) (Fin p) ℝ) i i)).quantile u =
        (S i i / 2) / inverseRegularizedGamma ((n - p + 1) / 2) (1 - u) := by
  rw [map_coe_apply_inverseWishartMeasure hS i,
    quantile_inverseGammaMeasure (by linarith) (half_pos hS.diag_pos) hu]

/-- Gaussian-Gram Wishart diagonal quantiles tend to zero at the lower endpoint, including zero
degrees and zero diagonal scale. -/
theorem tendsto_quantile_map_coe_apply_wishartGramMeasure_nhdsGT_zero
    (hS : S.PosSemidef) (ν : ℕ) (i : Fin p) :
    Tendsto (fun u ↦ (((wishartGramMeasure ν S).map
      (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
        (A : Matrix (Fin p) (Fin p) ℝ) i i)).quantile u : EReal))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  rw [map_coe_apply_wishartGramMeasure hS ν i]
  let _ := isProbabilityMeasure_chiSquaredMeasure (Nat.cast_nonneg ν)
  have hlim := EReal.Tendsto.const_mul
    (tendsto_quantile_chiSquaredMeasure_nhdsGT_zero (Nat.cast_nonneg ν))
    (Or.inl (EReal.coe_ne_bot (S i i))) (Or.inl (EReal.coe_ne_top (S i i)))
  simp only [mul_zero] at hlim
  apply hlim.congr'
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with u hu
  rw [Measure.quantile_map_of_monotone
    (fun _ _ hxy ↦ mul_le_mul_of_nonneg_left hxy hS.diag_nonneg)
    (continuous_const.mul continuous_id) hu.1 hu.2, EReal.coe_mul]

/-- At the upper endpoint, a Gaussian-Gram Wishart diagonal entry is unbounded exactly when its
degree and diagonal scale are both positive. -/
theorem tendsto_quantile_map_coe_apply_wishartGramMeasure_nhdsLT_one
    (hS : S.PosSemidef) (ν : ℕ) (i : Fin p) :
    Tendsto (fun u ↦ (((wishartGramMeasure ν S).map
      (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
        (A : Matrix (Fin p) (Fin p) ℝ) i i)).quantile u : EReal))
      (nhdsWithin 1 (Iio 1)) (nhds (if ν = 0 ∨ S i i = 0 then 0 else ⊤)) := by
  rw [map_coe_apply_wishartGramMeasure hS ν i]
  let _ := isProbabilityMeasure_chiSquaredMeasure (Nat.cast_nonneg ν)
  have hbase := tendsto_quantile_chiSquaredMeasure_nhdsLT_one (Nat.cast_nonneg ν)
  have hscaled := EReal.Tendsto.const_mul hbase
    (Or.inl (EReal.coe_ne_bot (S i i))) (Or.inl (EReal.coe_ne_top (S i i)))
  have heq :
      (fun u ↦ (S i i : EReal) * ((chiSquaredMeasure ν).quantile u : EReal))
        =ᶠ[nhdsWithin 1 (Iio 1)]
      fun u ↦ (((chiSquaredMeasure ν).map (S i i * ·)).quantile u : EReal) := by
    filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with u hu
    rw [Measure.quantile_map_of_monotone
      (fun _ _ hxy ↦ mul_le_mul_of_nonneg_left hxy hS.diag_nonneg)
      (continuous_const.mul continuous_id) hu.1 hu.2, EReal.coe_mul]
  by_cases hν : ν = 0
  · subst ν
    simpa using hscaled.congr' heq
  · by_cases hSii : S i i = 0
    · simpa [hν, hSii] using hscaled.congr' heq
    · have hSii' : 0 < S i i := lt_of_le_of_ne hS.diag_nonneg (Ne.symm hSii)
      simpa [hν, hSii, EReal.coe_mul_top_of_pos hSii'] using hscaled.congr' heq

/-- Nonsingular Wishart diagonal quantiles tend to zero at the lower endpoint. -/
theorem tendsto_quantile_map_coe_apply_nonsingularWishartMeasure_nhdsGT_zero
    (hS : S.PosDef) (hn : (p : ℝ) - 1 < n) (i : Fin p) :
    Tendsto (fun u ↦ (((nonsingularWishartMeasure n S).map
      (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
        (A : Matrix (Fin p) (Fin p) ℝ) i i)).quantile u : EReal))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  rw [map_coe_apply_nonsingularWishartMeasure hS hn i]
  have hn0 : 0 < n := by
    have hp : 1 ≤ p := Nat.one_le_iff_ne_zero.2 fun hp ↦ by simpa [hp] using i.isLt
    have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  let _ := isProbabilityMeasure_chiSquaredMeasure hn0.le
  have hlim := EReal.Tendsto.const_mul
    (tendsto_quantile_chiSquaredMeasure_nhdsGT_zero hn0.le)
    (Or.inl (EReal.coe_ne_bot (S i i))) (Or.inl (EReal.coe_ne_top (S i i)))
  simp only [mul_zero] at hlim
  apply hlim.congr'
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with u hu
  rw [Measure.quantile_map_of_monotone
    (fun _ _ hxy ↦ mul_le_mul_of_nonneg_left hxy hS.diag_pos.le)
    (continuous_const.mul continuous_id) hu.1 hu.2, EReal.coe_mul]

/-- Nonsingular Wishart diagonal quantiles tend to infinity at the upper endpoint. -/
theorem tendsto_quantile_map_coe_apply_nonsingularWishartMeasure_nhdsLT_one
    (hS : S.PosDef) (hn : (p : ℝ) - 1 < n) (i : Fin p) :
    Tendsto (fun u ↦ (((nonsingularWishartMeasure n S).map
      (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
        (A : Matrix (Fin p) (Fin p) ℝ) i i)).quantile u : EReal))
      (nhdsWithin 1 (Iio 1)) (nhds ⊤) := by
  rw [map_coe_apply_nonsingularWishartMeasure hS hn i]
  have hn0 : 0 < n := by
    have hp : 1 ≤ p := Nat.one_le_iff_ne_zero.2 fun hp ↦ by simpa [hp] using i.isLt
    have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  let _ := isProbabilityMeasure_chiSquaredMeasure hn0.le
  have hlim := tendsto_quantile_chiSquaredMeasure_nhdsLT_one hn0.le
  rw [ite_eq_right hn0.ne'] at hlim
  have hscaled := EReal.Tendsto.const_mul hlim
    (Or.inl (EReal.coe_ne_bot (S i i))) (Or.inl (EReal.coe_ne_top (S i i)))
  simpa only [EReal.coe_mul_top_of_pos hS.diag_pos] using hscaled.congr'
    (by
      filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with u hu
      rw [Measure.quantile_map_of_monotone
        (fun _ _ hxy ↦ mul_le_mul_of_nonneg_left hxy hS.diag_pos.le)
        (continuous_const.mul continuous_id) hu.1 hu.2, EReal.coe_mul])

/-- Inverse-Wishart diagonal quantiles tend to zero at the lower endpoint. -/
theorem tendsto_quantile_map_coe_apply_inverseWishartMeasure_nhdsGT_zero
    (hS : S.PosDef) (hn : (p : ℝ) - 1 < n) (i : Fin p) :
    Tendsto (fun u ↦ (((inverseWishartMeasure n S).map
      (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
        (A : Matrix (Fin p) (Fin p) ℝ) i i)).quantile u : EReal))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  rw [map_coe_apply_inverseWishartMeasure hS i]
  exact tendsto_quantile_inverseGammaMeasure_nhdsGT_zero (by linarith) (half_pos hS.diag_pos)

/-- Inverse-Wishart diagonal quantiles tend to infinity at the upper endpoint. -/
theorem tendsto_quantile_map_coe_apply_inverseWishartMeasure_nhdsLT_one
    (hS : S.PosDef) (hn : (p : ℝ) - 1 < n) (i : Fin p) :
    Tendsto (fun u ↦ (((inverseWishartMeasure n S).map
      (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
        (A : Matrix (Fin p) (Fin p) ℝ) i i)).quantile u : EReal))
      (nhdsWithin 1 (Iio 1)) (nhds ⊤) := by
  rw [map_coe_apply_inverseWishartMeasure hS i]
  exact tendsto_quantile_inverseGammaMeasure_nhdsLT_one (by linarith) (half_pos hS.diag_pos)

end TauCeti.Probability
