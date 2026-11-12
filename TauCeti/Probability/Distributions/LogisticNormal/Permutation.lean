/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.LogisticNormal.Basic
import TauCeti.Probability.Distributions.Gaussian.Affine

/-!
# Relabeling the categories of a logistic-normal law

Relabeling a simplex vector also relabels its reference category and its Gaussian log-ratio
coordinates. The logistic chart commutes with this operation, and the logistic-normal law
transforms by reindexing its Gaussian mean and both covariance indices.

`map_comp_logisticNormalMeasure` permits an equivalence between different finite category
types, including a permutation of a single type. It holds for every covariance: relabeling
preserves positive semidefiniteness in both directions, so the invalid-covariance Dirac
fallback is preserved as well. Singular covariances and the one-category case are included.

The Gaussian transport reuses `map_comp_multivariateGaussian`; the deleted-category
bijection is Mathlib's `Equiv.subtypeEquiv`.

## References

* J. Aitchison and S. M. Shen, *Logistic-normal distributions: Some properties and uses*,
  Biometrika 67(2), 261–272, 1980.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Relabeling the log-ratio coordinates and the reference relabels the logistic chart. -/
theorem logisticNormalChart_comp (e : κ ≃ ι) (r : κ)
    (z : EuclideanSpace ℝ {i // i ≠ e r}) :
    logisticNormalChart r
        (WithLp.toLp 2 (fun j : {j // j ≠ r} ↦ z ⟨e j, e.injective.ne j.property⟩)) =
      WithLp.toLp 2 (fun j ↦ logisticNormalChart (e r) z (e j)) := by
  let e' : {j // j ≠ r} ≃ {i // i ≠ e r} :=
    e.subtypeEquiv (fun _ ↦ by simp)
  have hsum :
      ∑ j : {j // j ≠ r}, Real.exp (z ⟨e j, e.injective.ne j.property⟩) =
        ∑ i, Real.exp (z i) :=
    e'.sum_comp (fun i ↦ Real.exp (z i))
  ext j
  simp only [logisticNormalChart_apply, Equiv.funSplitAt_symm_apply, hsum,
    ne_eq, EmbeddingLike.apply_eq_iff_eq]

/-- Relabeling categories reindexes the Gaussian mean and covariance and moves the reference
category. The identity holds even for an invalid covariance's point-mass fallback. -/
theorem map_comp_logisticNormalMeasure (e : κ ≃ ι) (r : κ)
    (m : EuclideanSpace ℝ {i // i ≠ e r})
    (S : Matrix {i // i ≠ e r} {i // i ≠ e r} ℝ) :
    (logisticNormalMeasure (e r) m S).map (fun x ↦ WithLp.toLp 2 (fun j ↦ x (e j))) =
      logisticNormalMeasure r
        (WithLp.toLp 2 (fun j : {j // j ≠ r} ↦ m ⟨e j, e.injective.ne j.property⟩))
        (S.submatrix (fun j : {j // j ≠ r} ↦ ⟨e j, e.injective.ne j.property⟩)
          (fun j : {j // j ≠ r} ↦ ⟨e j, e.injective.ne j.property⟩)) := by
  let e' : {j // j ≠ r} ≃ {i // i ≠ e r} :=
    e.subtypeEquiv (fun _ ↦ by simp)
  have he' : ⇑e' = (fun j : {j // j ≠ r} ↦
      (⟨e j, e.injective.ne j.property⟩ : {i // i ≠ e r})) := by
    funext j
    simp [e']
  by_cases hS : S.PosSemidef
  · have hG := map_comp_multivariateGaussian m hS e'
    rw [he'] at hG
    rw [logisticNormalMeasure_def, logisticNormalMeasure_def, ← hG,
      Measure.map_map (measurable_logisticNormalChart r) (by fun_prop),
      Measure.map_map (by fun_prop) (measurable_logisticNormalChart (e r))]
    simp only [Function.comp_def, logisticNormalChart_comp]
  · have hS' : ¬ (S.submatrix e' e').PosSemidef := by
      simpa only [Matrix.posSemidef_submatrix_equiv] using hS
    rw [he'] at hS'
    rw [logisticNormalMeasure_of_not_posSemidef _ _ hS,
      logisticNormalMeasure_of_not_posSemidef _ _ hS', Measure.map_dirac' (by fun_prop),
      logisticNormalChart_comp]

end TauCeti.Probability

namespace ProbabilityTheory.HasLaw

open TauCeti.Probability

/-- Relabeling a logistic-normal random vector relabels its reference and Gaussian parameters,
including at singular and invalid covariances. -/
theorem comp_logisticNormalMeasure {Ω ι κ : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] {P : Measure Ω}
    {e : κ ≃ ι} {r : κ} {X : Ω → EuclideanSpace ℝ ι}
    {m : EuclideanSpace ℝ {i // i ≠ e r}}
    {S : Matrix {i // i ≠ e r} {i // i ≠ e r} ℝ}
    (hX : HasLaw X (logisticNormalMeasure (e r) m S) P) :
    HasLaw (fun ω ↦ WithLp.toLp 2 (fun j ↦ X ω (e j)))
      (logisticNormalMeasure r
        (WithLp.toLp 2 (fun j : {j // j ≠ r} ↦ m ⟨e j, e.injective.ne j.property⟩))
        (S.submatrix (fun j : {j // j ≠ r} ↦ ⟨e j, e.injective.ne j.property⟩)
          (fun j : {j // j ≠ r} ↦ ⟨e j, e.injective.ne j.property⟩))) P := by
  have hmap : HasLaw (fun x : EuclideanSpace ℝ ι ↦
      WithLp.toLp 2 (fun j ↦ x (e j))) _ (logisticNormalMeasure (e r) m S) :=
    ⟨(by fun_prop), map_comp_logisticNormalMeasure e r m S⟩
  exact hmap.comp hX

end ProbabilityTheory.HasLaw
