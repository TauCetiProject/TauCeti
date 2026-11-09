/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Probability.Distributions.LKJ.Marginal
public import TauCeti.Probability.Distributions.Beta.Quantile

import TauCeti.Probability.Distributions.Affine
import TauCeti.Probability.Distributions.Dirac

/-!
# Quantiles of LKJ matrix entries

For `η > 0` and `i ≠ j`, the off-diagonal entry `R i j` of a `p × p` LKJ matrix of shape `η` is
`-1 + 2 * X` with `X ~ Beta(α, α)` and `α = η + (p - 2) / 2`
(`TauCeti.Probability.map_coe_apply_lkjMeasure_of_ne`). Its quantile at an interior level `u` is
therefore `-1 + 2 * inverseRegularizedIncompleteBeta α α u`, and these quantiles tend to the
endpoints `-1` and `1` of the entry's support as `u` tends to `0` and `1`. Diagonal entries are
almost surely one, so their interior quantiles are one.

## Main results

* `TauCeti.Probability.quantile_map_coe_apply_lkjMeasure_of_ne`: the off-diagonal quantile;
* `TauCeti.Probability.tendsto_quantile_map_coe_apply_lkjMeasure_of_ne_nhdsGT_zero` and
  `TauCeti.Probability.tendsto_quantile_map_coe_apply_lkjMeasure_of_ne_nhdsLT_one`: its
  endpoint limits;
* `TauCeti.Probability.quantile_map_coe_apply_self_lkjMeasure`: the diagonal quantile.

## References

* D. Lewandowski, D. Kurowicka, H. Joe, *Generating random correlation matrices based on vines
  and extended onion method*, J. Multivariate Anal. 100 (2009), 1989–2001.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Topology

namespace TauCeti.Probability

variable {p : ℕ} {η : ℝ}

/-- The common shape `η + (p - 2) / 2` of the off-diagonal entries is positive. -/
private theorem entry_shape_pos (hη : 0 < η) {i j : Fin p} (hij : i ≠ j) :
    0 < η + ((p : ℝ) - 2) / 2 := by
  have hp : 2 ≤ p := by
    rcases i with ⟨i, hi⟩
    rcases j with ⟨j, hj⟩
    simp only [ne_eq, Fin.mk.injEq] at hij
    omega
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  linarith

/-- **Quantiles of an off-diagonal LKJ entry.** For `η > 0`, `i ≠ j` and an interior level
`u`, the quantile of the entry `R i j` of a `p × p` LKJ matrix of shape `η` is
`-1 + 2 * inverseRegularizedIncompleteBeta α α u` with `α = η + (p - 2) / 2`. -/
theorem quantile_map_coe_apply_lkjMeasure_of_ne (hη : 0 < η) {i j : Fin p} (hij : i ≠ j)
    {u : ℝ} (hu : u ∈ Ioo 0 1) :
    ((lkjMeasure p η).map (fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
        (R : Matrix (Fin p) (Fin p) ℝ) i j)).quantile u =
      -1 + 2 * inverseRegularizedIncompleteBeta (η + ((p : ℝ) - 2) / 2)
        (η + ((p : ℝ) - 2) / 2) u := by
  have ha := entry_shape_pos hη hij
  have := isProbabilityMeasureBeta ha ha
  rw [map_coe_apply_lkjMeasure_of_ne hη hij, quantile_map_affine_pos two_pos hu.1 hu.2,
    quantile_betaMeasure ha ha hu]

/-- Off-diagonal LKJ entry quantiles tend to the lower support endpoint `-1`. -/
theorem tendsto_quantile_map_coe_apply_lkjMeasure_of_ne_nhdsGT_zero (hη : 0 < η) {i j : Fin p}
    (hij : i ≠ j) :
    Tendsto ((lkjMeasure p η).map
        (fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
          (R : Matrix (Fin p) (Fin p) ℝ) i j)).quantile (𝓝[>] 0) (𝓝 (-1)) := by
  have ha := entry_shape_pos hη hij
  have h := ((tendsto_inverseRegularizedIncompleteBeta_zero ha ha).const_mul 2).const_add (-1)
  simp only [mul_zero, add_zero] at h
  apply h.congr'
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with u hu
  exact (quantile_map_coe_apply_lkjMeasure_of_ne hη hij hu).symm

/-- Off-diagonal LKJ entry quantiles tend to the upper support endpoint `1`. -/
theorem tendsto_quantile_map_coe_apply_lkjMeasure_of_ne_nhdsLT_one (hη : 0 < η) {i j : Fin p}
    (hij : i ≠ j) :
    Tendsto ((lkjMeasure p η).map
        (fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
          (R : Matrix (Fin p) (Fin p) ℝ) i j)).quantile (𝓝[<] 1) (𝓝 1) := by
  have ha := entry_shape_pos hη hij
  have h := ((tendsto_inverseRegularizedIncompleteBeta_one ha ha).const_mul 2).const_add (-1)
  norm_num only [mul_one, neg_add_cancel_left] at h
  apply h.congr'
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with u hu
  exact (quantile_map_coe_apply_lkjMeasure_of_ne hη hij hu).symm

/-- **Quantiles of a diagonal LKJ entry.** For `η > 0`, every interior quantile of a diagonal
entry of an LKJ matrix is one. -/
theorem quantile_map_coe_apply_self_lkjMeasure (hη : 0 < η) (i : Fin p) {u : ℝ}
    (hu : u ∈ Ioo 0 1) :
    ((lkjMeasure p η).map (fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
        (R : Matrix (Fin p) (Fin p) ℝ) i i)).quantile u = 1 := by
  rw [map_coe_apply_self_lkjMeasure hη i, Measure.quantile_dirac 1 hu.1 hu.2.le]

end TauCeti.Probability
