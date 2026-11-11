/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Probability.Distributions.LKJ.EntryVariance
public import TauCeti.Probability.Distributions.LKJ.PartialCorrelation
public import TauCeti.Probability.Distributions.LKJ.PrincipalBlock
public import TauCeti.Probability.Distributions.LKJ.Symmetry
public import Mathlib.Probability.Moments.Covariance

/-!
# Entries of LKJ matrices

Forgetting symmetry, an LKJ matrix of positive shape `η` has the law of the Gram matrix of
independent centered symmetric Beta partial correlations
(`TauCeti.Probability.map_coe_lkjMeasure`). Through this representation the marginal laws of
the independent-Beta construction become marginal laws of `TauCeti.Probability.lkjMeasure`.

* Every principal `q × q` block of a `p × p` LKJ matrix of shape `η` has the LKJ law of
  dimension `q` and shape `η + (p - q) / 2`
  (`TauCeti.Probability.map_symmetricCongruenceLinearMap_submatrix_one_lkjMeasure`, in
  `TauCeti.Probability.Distributions.LKJ.PrincipalBlock`).
* Consequently every off-diagonal entry `R i j` has the law of `-1 + 2 * X` with
  `X ~ Beta(α, α)` and `α = η + (p - 2) / 2`: the lower entry of a `2 × 2` LKJ matrix is its
  single partial correlation. Equivalently `(R i j + 1) / 2 ~ Beta(α, α)`. Diagonal entries
  are almost surely one.
* Off-diagonal entries have variance `1 / (2 * η + p - 1)`, and distinct strictly lower entries
  have covariance zero.

## Main results

* `TauCeti.Probability.map_coe_apply_lkjMeasure_of_ne` and
  `TauCeti.Probability.map_coe_apply_add_one_div_two_lkjMeasure_of_ne`: off-diagonal entry laws;
* `TauCeti.Probability.map_coe_apply_self_lkjMeasure`: diagonal entry laws;
* `TauCeti.Probability.variance_coe_apply_lkjMeasure_of_ne` and
  `TauCeti.Probability.covariance_coe_apply_lkjMeasure`: entry variances and covariances.

## References

* D. Lewandowski, D. Kurowicka, H. Joe, *Generating random correlation matrices based on vines
  and extended onion method*, J. Multivariate Anal. 100 (2009), 1989–2001.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

variable {p : ℕ} {η : ℝ}

/-- The lower entry of a `2 × 2` LKJ matrix is its single partial correlation, a centered
symmetric Beta variable of the same shape. -/
private theorem map_coe_apply_one_zero_lkjMeasure_two (hη : 0 < η) :
    (lkjMeasure 2 η).map (fun R : selfAdjoint.submodule ℝ (Matrix (Fin 2) (Fin 2) ℝ) ↦
        (R : Matrix (Fin 2) (Fin 2) ℝ) 1 0) =
      (betaMeasure η η).map (fun x ↦ -1 + 2 * x) := by
  let ij₀ : strictLowerTriangle 2 := ⟨(1, 0), Fin.zero_lt_one⟩
  have hshape : ∀ ij, lkjPartialCorrelationShape 2 η ij = η := fun ij ↦ by
    have := ij.2
    have : ij.1.2.val = 0 := by omega
    simp [lkjPartialCorrelationShape_eq, this]
  have (ij : strictLowerTriangle 2) :
      IsProbabilityMeasure ((betaMeasure (lkjPartialCorrelationShape 2 η ij)
        (lkjPartialCorrelationShape 2 η ij)).map (fun x ↦ -1 + 2 * x)) := by
    rw [hshape]
    have := isProbabilityMeasureBeta hη hη
    infer_instance
  have hentry : (fun R : selfAdjoint.submodule ℝ (Matrix (Fin 2) (Fin 2) ℝ) ↦
      (R : Matrix (Fin 2) (Fin 2) ℝ) 1 0) =
        (fun R : Matrix (Fin 2) (Fin 2) ℝ ↦ R 1 0) ∘
          (fun R : selfAdjoint.submodule ℝ (Matrix (Fin 2) (Fin 2) ℝ) ↦
            (R : Matrix (Fin 2) (Fin 2) ℝ)) := rfl
  rw [hentry, ← Measure.map_map (by fun_prop) measurable_subtype_coe, map_coe_lkjMeasure hη,
    Measure.map_map (by fun_prop) continuous_partialCorrelationGram.measurable]
  have hgram : (fun R : Matrix (Fin 2) (Fin 2) ℝ ↦ R 1 0) ∘ partialCorrelationGram =
      Function.eval ij₀ := by
    funext z
    exact partialCorrelationGram_apply_zero_of_pos z Fin.zero_lt_one
  rw [hgram, (measurePreserving_eval _ ij₀).map_eq, hshape]

/-- **Off-diagonal entries of LKJ matrices.** For `η > 0` and `i ≠ j`, the entry `R i j` of a
`p × p` LKJ matrix of shape `η` has the law of `-1 + 2 * X` with `X ~ Beta(α, α)` and
`α = η + (p - 2) / 2`. Dimensions are cast to the reals before subtraction. -/
theorem map_coe_apply_lkjMeasure_of_ne (hη : 0 < η) {i j : Fin p} (hij : i ≠ j) :
    (lkjMeasure p η).map (fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
        (R : Matrix (Fin p) (Fin p) ℝ) i j) =
      (betaMeasure (η + ((p : ℝ) - 2) / 2) (η + ((p : ℝ) - 2) / 2)).map
        (fun x ↦ -1 + 2 * x) := by
  have hf : Function.Injective ![j, i] := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [eq_comm]
  have h2 : (2 : ℝ) ≤ p := by
    have := Fintype.card_le_of_injective _ hf
    simp only [Fintype.card_fin] at this
    exact_mod_cast this
  have hentry : (fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
      (R : Matrix (Fin p) (Fin p) ℝ) i j) =
        (fun R : selfAdjoint.submodule ℝ (Matrix (Fin 2) (Fin 2) ℝ) ↦
          (R : Matrix (Fin 2) (Fin 2) ℝ) 1 0) ∘ Matrix.symmetricCongruenceLinearMap
            ((1 : Matrix (Fin p) (Fin p) ℝ).submatrix ![j, i] id) := by
    funext R
    simp only [Function.comp_apply, Matrix.coe_symmetricCongruenceLinearMap_apply,
      Matrix.transpose_submatrix, Matrix.transpose_one,
      Matrix.submatrix_one_mul_mul_submatrix_one]
    simp
  rw [hentry, ← Measure.map_map (by fun_prop)
      (LinearMap.continuous_of_finiteDimensional _).measurable,
    map_symmetricCongruenceLinearMap_submatrix_one_lkjMeasure _ hf hη,
    map_coe_apply_one_zero_lkjMeasure_two (by push_cast; linarith)]
  -- The block dimension is elaborated as `Nat.succ (Nat.succ 0)` from the type of `![j, i]`.
  norm_num

/-- **Off-diagonal entries of LKJ matrices, Beta form.** For `η > 0` and `i ≠ j`, the
affinely rescaled entry `(R i j + 1) / 2` of a `p × p` LKJ matrix of shape `η` has the law
`Beta(α, α)` with `α = η + (p - 2) / 2`. -/
theorem map_coe_apply_add_one_div_two_lkjMeasure_of_ne (hη : 0 < η) {i j : Fin p}
    (hij : i ≠ j) :
    (lkjMeasure p η).map (fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
        ((R : Matrix (Fin p) (Fin p) ℝ) i j + 1) / 2) =
      betaMeasure (η + ((p : ℝ) - 2) / 2) (η + ((p : ℝ) - 2) / 2) := by
  have hcomp : (fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
      ((R : Matrix (Fin p) (Fin p) ℝ) i j + 1) / 2) =
        (fun x : ℝ ↦ (x + 1) / 2) ∘
          (fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
            (R : Matrix (Fin p) (Fin p) ℝ) i j) := rfl
  rw [hcomp, ← Measure.map_map (by fun_prop) (selfAdjoint.measurable_coe_apply i j),
    map_coe_apply_lkjMeasure_of_ne hη hij, Measure.map_map (by fun_prop) (by fun_prop)]
  conv_rhs => rw [← Measure.map_id (μ := betaMeasure _ _)]
  congr 1
  funext x
  simp only [Function.comp_apply, id_eq]
  ring

/-- **Diagonal entries of LKJ matrices.** For `η > 0`, every diagonal entry of an LKJ matrix
is almost surely one, so its law is the Dirac mass at one. -/
theorem map_coe_apply_self_lkjMeasure (hη : 0 < η) (i : Fin p) :
    (lkjMeasure p η).map (fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
        (R : Matrix (Fin p) (Fin p) ℝ) i i) = Measure.dirac 1 := by
  have := isProbabilityMeasure_lkjMeasure (p := p) hη
  rw [Measure.map_congr ((ae_diag_eq_one_lkjMeasure p η).mono fun R hR ↦ hR i),
    Measure.map_const, measure_univ, one_smul]

/-- **Variance of an off-diagonal LKJ entry.** For `η > 0` and `i ≠ j`, the entry `R i j` of a
`p × p` LKJ matrix of shape `η` has variance `1 / (2 * η + p - 1)`. -/
theorem variance_coe_apply_lkjMeasure_of_ne (hη : 0 < η) {i j : Fin p} (hij : i ≠ j) :
    Var[fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
        (R : Matrix (Fin p) (Fin p) ℝ) i j; lkjMeasure p η] = 1 / (2 * η + p - 1) := by
  have hcomp : (fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
      (R : Matrix (Fin p) (Fin p) ℝ) i j) =
        (fun R : Matrix (Fin p) (Fin p) ℝ ↦ R i j) ∘
          (fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
            (R : Matrix (Fin p) (Fin p) ℝ)) := rfl
  rw [hcomp, ← variance_map Matrix.measurable_apply.aemeasurable
      measurable_subtype_coe.aemeasurable,
    map_coe_lkjMeasure hη, variance_map Matrix.measurable_apply.aemeasurable
      continuous_partialCorrelationGram.measurable.aemeasurable]
  exact variance_partialCorrelationGram hη hij

/-- **Covariances of LKJ entries.** Distinct strictly lower entries of an LKJ matrix have
covariance zero. Nonpositive shapes give the zero measure, for which the covariance is also
zero. Zero covariance does not assert independence of the entries. -/
theorem covariance_coe_apply_lkjMeasure {ij kl : strictLowerTriangle p} (hne : ij ≠ kl) :
    cov[fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
        (R : Matrix (Fin p) (Fin p) ℝ) ij.1.1 ij.1.2,
      fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
        (R : Matrix (Fin p) (Fin p) ℝ) kl.1.1 kl.1.2; lkjMeasure p η] = 0 := by
  rcases le_or_gt η 0 with hη | hη
  · simp [lkjMeasure_of_nonpos hη]
  have (ij : strictLowerTriangle p) : IsProbabilityMeasure
      (betaMeasure (lkjPartialCorrelationShape p η ij) (lkjPartialCorrelationShape p η ij)) :=
    isProbabilityMeasureBeta (lkjPartialCorrelationShape_pos hη ij)
      (lkjPartialCorrelationShape_pos hη ij)
  have hcomp (ij : strictLowerTriangle p) :
      (fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
        (R : Matrix (Fin p) (Fin p) ℝ) ij.1.1 ij.1.2) =
          (fun R : Matrix (Fin p) (Fin p) ℝ ↦ R ij.1.1 ij.1.2) ∘
            (fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
              (R : Matrix (Fin p) (Fin p) ℝ)) := rfl
  rw [hcomp ij, hcomp kl, ← covariance_map Matrix.measurable_apply.aestronglyMeasurable
      Matrix.measurable_apply.aestronglyMeasurable measurable_subtype_coe.aemeasurable,
    map_coe_lkjMeasure hη]
  exact covariance_apply_map_partialCorrelationGram_pi _ hne

end TauCeti.Probability
