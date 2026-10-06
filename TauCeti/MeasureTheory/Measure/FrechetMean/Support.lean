/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.FrechetMean.Basic
public import TauCeti.MeasureTheory.Function.EssSup

/-!
# Chebyshev radii and the support of a measure

The essential-supremum distance from a center equals the supremum of distances over the
measure's support. Thus a bound on the Chebyshev radius is exactly containment of the support
in the corresponding closed ball. On an ordinary pseudometric space, finite radius is
exactly boundedness of the support; finite Chebyshev centers are centers of smallest enclosing
closed balls.

The support must be conull. We use the hereditarily Lindelöf hypothesis, which includes every
second-countable space and hence every Polish space. Neither probability normalization,
completeness nor separation of points is needed. Infinite radii and the zero measure are
included.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

section Extended

variable {X : Type*} [PseudoEMetricSpace X] [MeasurableSpace X]
  [HereditarilyLindelofSpace X] {μ : Measure X} {x : X}

/-- The Chebyshev radius is the supremum of distances from the center to the measure's
support, including when that supremum is infinite or the support is empty. -/
theorem chebyshevRadius_eq_iSup_support (μ : Measure X) (x : X) :
    chebyshevRadius μ x = ⨆ y ∈ μ.support, edist x y := by
  rw [chebyshevRadius_def, eLpNormEssSup_eq_essSup_enorm]
  simp only [enorm_eq_self]
  exact essSup_eq_iSup_support _ (continuous_const.edist continuous_id).lowerSemicontinuous
    μ.support_mem_ae

/-- A Chebyshev-radius bound is equivalent to containment of the support in a closed
extended ball. -/
theorem chebyshevRadius_le_iff_support_subset_closedEBall {r : ℝ≥0∞} :
    chebyshevRadius μ x ≤ r ↔ μ.support ⊆ Metric.closedEBall x r := by
  simp only [chebyshevRadius_eq_iSup_support, iSup_le_iff, subset_def,
    Metric.mem_closedEBall']

/-- The infinite-exponent Fréchet radius is the supremum of distances to the support. -/
theorem frechetRadius_top_eq_iSup_support [OpensMeasurableSpace X]
    (μ : Measure X) (x : X) :
    frechetRadius ⊤ μ x = ⨆ y ∈ μ.support, edist x y := by
  rw [frechetRadius_top
    (continuous_const.edist continuous_id).measurable.aestronglyMeasurable,
    chebyshevRadius_eq_iSup_support]

end Extended

section Metric

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  [HereditarilyLindelofSpace X] {μ : Measure X} {x : X}

/-- A nonnegative real bound on the Chebyshev radius is exactly containment of the support
in the corresponding ordinary closed ball. -/
theorem chebyshevRadius_le_ofReal_iff_support_subset_closedBall {r : ℝ} (hr : 0 ≤ r) :
    chebyshevRadius μ x ≤ ENNReal.ofReal r ↔ μ.support ⊆ Metric.closedBall x r := by
  simp only [chebyshevRadius_eq_iSup_support, iSup_le_iff, subset_def,
    Metric.mem_closedBall, edist_le_ofReal hr, dist_comm]

/-- Finite Chebyshev radius at any fixed center is equivalent to bounded support. -/
@[simp]
theorem chebyshevRadius_ne_top_iff_isBounded_support :
    chebyshevRadius μ x ≠ ⊤ ↔ Bornology.IsBounded μ.support := by
  constructor
  · intro h
    apply (Metric.isBounded_iff_subset_closedBall x).2
    exact ⟨(chebyshevRadius μ x).toReal,
      (chebyshevRadius_le_ofReal_iff_support_subset_closedBall ENNReal.toReal_nonneg).1
        (le_of_eq (ENNReal.ofReal_toReal h).symm)⟩
  · intro h
    obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall x).1 h
    have hsub : μ.support ⊆ Metric.closedBall x (max r 0) :=
      hr.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      ((chebyshevRadius_le_ofReal_iff_support_subset_closedBall (le_max_right _ _)).2 hsub)

/-- A finite Chebyshev center is exactly a center of a smallest enclosing closed ball of
nonnegative real radius. This remains valid for the zero measure. -/
theorem isChebyshevCenter_iff_exists_smallest_closedBall :
    IsChebyshevCenter μ x ↔ ∃ r : ℝ, 0 ≤ r ∧ μ.support ⊆ Metric.closedBall x r ∧
      ∀ y s, 0 ≤ s → μ.support ⊆ Metric.closedBall y s → r ≤ s := by
  rw [isChebyshevCenter_iff]
  constructor
  · rintro ⟨hfin, hmin⟩
    refine ⟨(chebyshevRadius μ x).toReal, ENNReal.toReal_nonneg, ?_, ?_⟩
    · exact (chebyshevRadius_le_ofReal_iff_support_subset_closedBall
        ENNReal.toReal_nonneg).1 (le_of_eq (ENNReal.ofReal_toReal hfin).symm)
    · intro y s hs hsub
      have hle := (hmin y).trans
        ((chebyshevRadius_le_ofReal_iff_support_subset_closedBall hs).2 hsub)
      exact (ENNReal.le_ofReal_iff_toReal_le hfin hs).1 hle
  · rintro ⟨r, hr, hsub, hmin⟩
    have hx := (chebyshevRadius_le_ofReal_iff_support_subset_closedBall hr).2 hsub
    have hfin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hx
    refine ⟨hfin, fun y ↦ ?_⟩
    by_cases hy : chebyshevRadius μ y = ⊤
    · simp [hy]
    · have hysub := (chebyshevRadius_le_ofReal_iff_support_subset_closedBall
        ENNReal.toReal_nonneg).1 (le_of_eq (ENNReal.ofReal_toReal hy).symm)
      exact hx.trans ((ENNReal.ofReal_le_ofReal
        (hmin y _ ENNReal.toReal_nonneg hysub)).trans_eq (ENNReal.ofReal_toReal hy))

end Metric

end TauCeti
