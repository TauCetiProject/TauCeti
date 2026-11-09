/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Probability.Distributions.LKJ.PartialCorrelation
public import TauCeti.Probability.Distributions.LKJ.Symmetry
public import TauCeti.Probability.Distributions.Beta.Quantile
import TauCeti.Probability.Distributions.Affine
import TauCeti.Probability.Distributions.Dirac

/-!
# Entries of LKJ matrices

Let `R` be a `p × p` correlation matrix with the LKJ law of shape `η > 0`. Every off-diagonal
entry `R i j` is a centered symmetric Beta variable: it has the law of `-1 + 2 * X` for
`X ~ Beta(α, α)` with `α = η + (p - 2) / 2`, equivalently `(R i j + 1) / 2 ~ Beta(α, α)`.
Diagonal entries are almost surely one.

An entry `R i 0` of the first column is the first partial correlation of row `i`, so the
independent-Beta construction of the LKJ law gives its law directly. Permutation invariance of the
LKJ law moves any off-diagonal position to the first column.

The entry law gives the variance `1 / (2 * η + p - 1)` of an off-diagonal entry, the interior
quantile `-1 + 2 * inverseRegularizedIncompleteBeta α α u` with one-sided limits `-1` and `1`,
and the constant quantile one of a diagonal entry.

## Main results

* `TauCeti.Probability.map_coe_apply_lkjMeasure_of_ne` and
  `TauCeti.Probability.map_coe_apply_add_one_div_two_lkjMeasure_of_ne`: the off-diagonal entry
  law.
* `TauCeti.Probability.map_coe_apply_self_lkjMeasure`: the diagonal entry law.
* `TauCeti.Probability.variance_coe_apply_lkjMeasure_of_ne`: the off-diagonal variance.
* `TauCeti.Probability.quantile_map_coe_apply_lkjMeasure_of_ne` and
  `TauCeti.Probability.quantile_map_coe_apply_self_lkjMeasure`: entry quantiles.

## References

* D. Lewandowski, D. Kurowicka, H. Joe, *Generating random correlation matrices based on vines
  and extended onion method*, J. Multivariate Anal. 100 (2009), 1989–2001.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Topology

namespace TauCeti.Probability

variable {p : ℕ} {η : ℝ}

/-! ### Entry laws -/

/-- The Beta shape `η + (p - 2) / 2` of an off-diagonal entry is positive. -/
private theorem entry_shape_pos (hη : 0 < η) {i j : Fin p} (hij : i ≠ j) :
    0 < η + ((p : ℝ) - 2) / 2 := by
  have := i.2; have := j.2; have := Fin.val_injective.ne hij
  have : (2 : ℝ) ≤ p := by exact_mod_cast (show 2 ≤ p by omega)
  linarith

/-- The entry `(1, 0)` of an LKJ matrix is a centered symmetric Beta variable. -/
private theorem map_coe_apply_one_zero_lkjMeasure {n : ℕ} (hη : 0 < η) :
    (lkjMeasure (n + 2) η).map
        (fun R : selfAdjoint.submodule ℝ (Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) ↦
          (R : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) 1 0) =
      (betaMeasure (η + n / 2) (η + n / 2)).map (fun x ↦ -1 + 2 * x) := by
  set μ := fun ij : strictLowerTriangle (n + 2) ↦
    (betaMeasure (lkjPartialCorrelationShape (n + 2) η ij)
      (lkjPartialCorrelationShape (n + 2) η ij)).map (fun x ↦ -1 + 2 * x)
  have (ij : strictLowerTriangle (n + 2)) : IsProbabilityMeasure (μ ij) := by
    have := isProbabilityMeasureBeta (lkjPartialCorrelationShape_pos hη ij)
      (lkjPartialCorrelationShape_pos hη ij)
    infer_instance
  have hshape : lkjPartialCorrelationShape (n + 2) η ⟨(1, 0), Fin.zero_lt_one⟩ = η + n / 2 := by
    rw [lkjPartialCorrelationShape_def, Fin.val_zero, show n + 2 - 1 - 0 = n + 1 by omega]
    push_cast
    ring
  rw [← map_correlationMatrix_map_correlationCoordinatesOfPartialCorrelation_pi_betaMeasure hη,
    Measure.map_map (selfAdjoint.measurable_coe_apply 1 0)
      (correlationMatrix (n + 2)).continuous.measurable,
    Measure.map_map ((selfAdjoint.measurable_coe_apply 1 0).comp
      (correlationMatrix (n + 2)).continuous.measurable)
      continuous_correlationCoordinatesOfPartialCorrelation.measurable]
  calc _ = (Measure.pi μ).map (Function.eval ⟨(1, 0), Fin.zero_lt_one⟩) := by
        congr 1
        funext z
        simp only [Function.comp_apply]
        rw [coe_correlationMatrix_apply_of_gt _ Fin.zero_lt_one,
          correlationCoordinatesOfPartialCorrelation_apply, partialCorrelationGram_apply_zero,
          Function.eval]
    _ = _ := by
        rw [(measurePreserving_eval μ _).map_eq]
        simp only [μ, hshape]

/-- **Off-diagonal entries of an LKJ matrix.** For `i ≠ j`, the entry `R i j` of an LKJ matrix of
shape `η > 0` has the law of `-1 + 2 * X` for `X ~ Beta(α, α)`, `α = η + (p - 2) / 2`. -/
theorem map_coe_apply_lkjMeasure_of_ne (hη : 0 < η) {i j : Fin p} (hij : i ≠ j) :
    (lkjMeasure p η).map (fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
        (R : Matrix (Fin p) (Fin p) ℝ) i j) =
      (betaMeasure (η + ((p : ℝ) - 2) / 2) (η + ((p : ℝ) - 2) / 2)).map
        (fun x ↦ -1 + 2 * x) := by
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 2 :=
    ⟨p - 2, by have := i.2; have := j.2; have := Fin.val_injective.ne hij; omega⟩
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair ![(1 : Fin (n + 2)), 0] ![i, j]
    (fun a b ↦ by fin_cases a <;> fin_cases b <;> simp)
    (fun a b ↦ by fin_cases a <;> fin_cases b <;> simp [hij, hij.symm])
  have hentry : (fun R : selfAdjoint.submodule ℝ (Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) ↦
      (R : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) i j) =
      (fun R : selfAdjoint.submodule ℝ (Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) ↦
        (R : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) 1 0) ∘
        Matrix.symmetricCongruenceLinearMap (σ.permMatrix ℝ) := by
    have h1 : σ 1 = i := hσ 0
    have h0 : σ 0 = j := hσ 1
    funext R
    rw [Function.comp_apply, Matrix.coe_symmetricCongruenceLinearMap_permMatrix_apply,
      Matrix.submatrix_apply, h1, h0]
  rw [hentry, ← Measure.map_map (selfAdjoint.measurable_coe_apply 1 0)
    (LinearMap.continuous_of_finiteDimensional _).measurable,
    map_symmetricCongruenceLinearMap_permMatrix_lkjMeasure, map_coe_apply_one_zero_lkjMeasure hη]
  congr 3 <;> push_cast <;> ring

/-- **Off-diagonal entries of an LKJ matrix, as Beta variables.** For `i ≠ j`, the rescaled entry
`(R i j + 1) / 2` of an LKJ matrix of shape `η > 0` has law `Beta(α, α)`,
`α = η + (p - 2) / 2`. -/
theorem map_coe_apply_add_one_div_two_lkjMeasure_of_ne (hη : 0 < η) {i j : Fin p}
    (hij : i ≠ j) :
    (lkjMeasure p η).map (fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
        ((R : Matrix (Fin p) (Fin p) ℝ) i j + 1) / 2) =
      betaMeasure (η + ((p : ℝ) - 2) / 2) (η + ((p : ℝ) - 2) / 2) := by
  have h := congrArg (Measure.map fun x : ℝ ↦ (x + 1) / 2) (map_coe_apply_lkjMeasure_of_ne hη hij)
  have hid : (fun x : ℝ ↦ (x + 1) / 2) ∘ (fun x ↦ -1 + 2 * x) = id := by
    funext x
    simp only [Function.comp_apply, id_eq]
    ring
  rwa [Measure.map_map (by fun_prop) (selfAdjoint.measurable_coe_apply i j),
    Measure.map_map (by fun_prop) (by fun_prop), hid, Measure.map_id] at h

/-- **Diagonal entries of an LKJ matrix.** A diagonal entry of an LKJ matrix of shape `η > 0` has
the Dirac law at one. -/
theorem map_coe_apply_self_lkjMeasure (hη : 0 < η) (i : Fin p) :
    (lkjMeasure p η).map (fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
        (R : Matrix (Fin p) (Fin p) ℝ) i i) = Measure.dirac 1 := by
  have := isProbabilityMeasure_lkjMeasure (p := p) hη
  rw [Measure.map_congr ((ae_diag_eq_one_lkjMeasure p η).mono fun R hR ↦ hR i),
    Measure.map_const, measure_univ, one_smul]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- For `i ≠ j`, the entry `R i j` of a random LKJ matrix of shape `η > 0` has the law of
`-1 + 2 * X` for `X ~ Beta(α, α)`, `α = η + (p - 2) / 2`. -/
theorem hasLaw_coe_apply_lkjMeasure_of_ne
    {R : Ω → selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)}
    (hR : HasLaw R (lkjMeasure p η) P) (hη : 0 < η) {i j : Fin p} (hij : i ≠ j) :
    HasLaw (fun ω ↦ (R ω : Matrix (Fin p) (Fin p) ℝ) i j)
      ((betaMeasure (η + ((p : ℝ) - 2) / 2) (η + ((p : ℝ) - 2) / 2)).map
        (fun x ↦ -1 + 2 * x)) P :=
  (⟨(selfAdjoint.measurable_coe_apply i j).aemeasurable,
      map_coe_apply_lkjMeasure_of_ne hη hij⟩ : HasLaw _ _ (lkjMeasure p η)).fun_comp hR

/-! ### Variance -/

/-- **Variance of an off-diagonal LKJ entry.** For `i ≠ j`, the entry `R i j` of an LKJ matrix of
shape `η > 0` has variance `1 / (2 * η + p - 1)`. -/
theorem variance_coe_apply_lkjMeasure_of_ne (hη : 0 < η) {i j : Fin p} (hij : i ≠ j) :
    variance (fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
        (R : Matrix (Fin p) (Fin p) ℝ) i j) (lkjMeasure p η) =
      1 / (2 * η + p - 1) := by
  have ha := entry_shape_pos hη hij
  have := isProbabilityMeasureBeta ha ha
  rw [← Function.id_comp (fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
      (R : Matrix (Fin p) (Fin p) ℝ) i j),
    ← variance_map aemeasurable_id (selfAdjoint.measurable_coe_apply i j).aemeasurable,
    map_coe_apply_lkjMeasure_of_ne hη hij, variance_map aemeasurable_id (by fun_prop),
    Function.id_comp, variance_const_add (by fun_prop), variance_const_mul,
    ← Function.id_def, variance_id_betaMeasure ha ha]
  have h2 : 2 * η + p - 1 = 2 * (η + ((p : ℝ) - 2) / 2) + 1 := by ring
  rw [h2]
  generalize η + ((p : ℝ) - 2) / 2 = a at ha ⊢
  field_simp
  ring

/-! ### Quantiles -/

/-- **Quantiles of an off-diagonal LKJ entry.** For `i ≠ j` and `0 < u < 1`, the `u`-quantile of
the entry `R i j` of an LKJ matrix of shape `η > 0` is
`-1 + 2 * inverseRegularizedIncompleteBeta α α u`, `α = η + (p - 2) / 2`. -/
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

/-- Quantiles of an off-diagonal LKJ entry tend to the lower support endpoint `-1` as the level
tends to zero. -/
theorem tendsto_quantile_map_coe_apply_lkjMeasure_of_ne_nhdsGT_zero (hη : 0 < η) {i j : Fin p}
    (hij : i ≠ j) :
    Tendsto ((lkjMeasure p η).map (fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
        (R : Matrix (Fin p) (Fin p) ℝ) i j)).quantile
      (𝓝[>] 0) (𝓝 (-1)) := by
  have ha := entry_shape_pos hη hij
  have h := ((tendsto_quantile_betaMeasure_nhdsGT_zero ha ha).const_mul 2).const_add (-1)
  rw [mul_zero, add_zero] at h
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with u hu
  rw [quantile_map_coe_apply_lkjMeasure_of_ne hη hij hu, quantile_betaMeasure ha ha hu]

/-- Quantiles of an off-diagonal LKJ entry tend to the upper support endpoint `1` as the level
tends to one. -/
theorem tendsto_quantile_map_coe_apply_lkjMeasure_of_ne_nhdsLT_one (hη : 0 < η) {i j : Fin p}
    (hij : i ≠ j) :
    Tendsto ((lkjMeasure p η).map (fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
        (R : Matrix (Fin p) (Fin p) ℝ) i j)).quantile
      (𝓝[<] 1) (𝓝 1) := by
  have ha := entry_shape_pos hη hij
  have h := ((tendsto_quantile_betaMeasure_nhdsLT_one ha ha).const_mul 2).const_add (-1)
  norm_num only [mul_one, neg_add_cancel_left] at h
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with u hu
  rw [quantile_map_coe_apply_lkjMeasure_of_ne hη hij hu, quantile_betaMeasure ha ha hu]

/-- Every quantile of a diagonal LKJ entry at a level in `(0, 1]` is one. -/
theorem quantile_map_coe_apply_self_lkjMeasure (hη : 0 < η) (i : Fin p) {u : ℝ}
    (hu : u ∈ Ioc 0 1) :
    ((lkjMeasure p η).map (fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
        (R : Matrix (Fin p) (Fin p) ℝ) i i)).quantile u = 1 := by
  rw [map_coe_apply_self_lkjMeasure hη i, Measure.quantile_dirac 1 hu.1 hu.2]

end TauCeti.Probability
