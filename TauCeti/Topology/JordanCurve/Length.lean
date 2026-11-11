/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.EMetricSpace.CurveLength
public import TauCeti.Topology.JordanCurve.Interval
import TauCeti.Topology.JordanCurve.Separation

/-!
# The length of a Jordan curve

The length of a Jordan curve `C` in an extended metric space is its one-dimensional Hausdorff
measure `μH[1] C`, and `C` is rectifiable when this is finite. This file relates that geometric
notion to parametrizations. A subset is a rectifiable Jordan curve exactly when it is the trace
`γ '' [a, b]` of a curve `γ : ℝ → X` that is continuous on `[a, b]`, closed (`γ a = γ b`),
injective on `[a, b)` and of bounded variation on `[a, b]`
(`TauCeti.isJordanCurve_and_hausdorffMeasure_lt_top_iff`). For every such parametrization the
total variation `eVariationOn γ (Icc a b)` equals `μH[1] C`
(`ContinuousOn.eVariationOn_eq_hausdorffMeasure_image`), so the parametric and geometric lengths
agree. The parametrization need not be absolutely continuous, Lipschitz or differentiable.

The length of a Jordan curve is at least twice its diameter
(`TauCeti.IsJordanCurve.two_mul_ediam_le_hausdorffMeasure`): two distinct points `p` and `q` cut
the curve into two connected arcs meeting only at `p` and `q`, and each arc has length at least
the distance from `p` to `q`. In particular every Jordan curve has positive length
(`TauCeti.IsJordanCurve.hausdorffMeasure_pos`). The constant is sharp: the boundaries of thin
rectangles have length arbitrarily close to twice their diameter.

The Euclidean-normalized measure `μHE[1]` coincides with `μH[1]`
(`MeasureTheory.Measure.euclideanHausdorffMeasure_one`), so these statements apply to either
normalization.

## Main results

* `TauCeti.isJordanCurve_and_hausdorffMeasure_lt_top_iff`: rectifiable Jordan curves are the
  traces of simple closed curves of bounded variation.
* `TauCeti.IsJordanCurve.two_mul_ediam_le_hausdorffMeasure`: a Jordan curve has length at least
  twice its diameter.
* `TauCeti.IsJordanCurve.hausdorffMeasure_pos`: a Jordan curve has positive length.
-/

public section

namespace TauCeti

open MeasureTheory Metric Set
open scoped ENNReal

variable {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] {C : Set X} {a b : ℝ}

/-- **Rectifiable Jordan curves are the traces of simple closed curves of bounded variation.**
For `a < b`, a subset `C` is a Jordan curve of finite one-dimensional Hausdorff measure exactly
when it is `γ '' [a, b]` for some `γ : ℝ → X` that is continuous on `[a, b]`, satisfies
`γ a = γ b`, is injective on `[a, b)` and has bounded variation on `[a, b]`. -/
theorem isJordanCurve_and_hausdorffMeasure_lt_top_iff (hab : a < b) :
    IsJordanCurve C ∧ μH[1] C < ∞ ↔ ∃ γ : ℝ → X, ContinuousOn γ (Icc a b) ∧ γ a = γ b ∧
      InjOn γ (Ico a b) ∧ BoundedVariationOn γ (Icc a b) ∧ γ '' Icc a b = C := by
  refine ⟨fun ⟨h, hfin⟩ => ?_, ?_⟩
  · obtain ⟨γ, hγ, hclosed, hinj, rfl⟩ := (isJordanCurve_iff_exists_injOn_Ico hab).1 h
    exact ⟨γ, hγ, hclosed, hinj,
      (hγ.boundedVariationOn_iff_hausdorffMeasure_image_lt_top
        (hinj.mono Ioo_subset_Ico_self)).2 hfin, rfl⟩
  · rintro ⟨γ, hγ, hclosed, hinj, hbv, rfl⟩
    exact ⟨isJordanCurve_image_Icc hab hγ hclosed hinj,
      (hγ.boundedVariationOn_iff_hausdorffMeasure_image_lt_top
        (hinj.mono Ioo_subset_Ico_self)).1 hbv⟩

/-- **A Jordan curve has length at least twice its diameter.** For a Jordan curve `C` in an
extended metric space, `2 * ediam C ≤ μH[1] C`. -/
theorem IsJordanCurve.two_mul_ediam_le_hausdorffMeasure (h : IsJordanCurve C) :
    2 * ediam C ≤ μH[1] C := by
  have := Measure.nullSingletonClass_hausdorff X (show (0 : ℝ) < 1 by norm_num)
  -- Each pair of points of `C` is at distance at most half the length of `C`.
  have hpair (p : X) (hp : p ∈ C) (q : X) (hq : q ∈ C) : edist p q * 2 ≤ μH[1] C := by
    rcases eq_or_ne p q with rfl | hpq
    · simp
    obtain ⟨A, B, -, hBc, hA, hB, hAB, hAB'⟩ :=
      h.exists_isCompact_isConnected_union_eq_inter_eq_pair hp hq
    have hpA : p ∈ A ∧ p ∈ B := by simpa using hAB'.ge (mem_insert p {q})
    have hqA : q ∈ A ∧ q ∈ B := by simpa using hAB'.ge (mem_insert_of_mem p rfl)
    have hsum : μH[1] C = μH[1] A + μH[1] B := by
      rw [← measure_union_add_inter A hBc.isClosed.measurableSet, hAB, hAB',
        (toFinite {p, q}).measure_zero, add_zero]
    rw [hsum, mul_two]
    exact add_le_add (hA.isPreconnected.edist_le_hausdorffMeasure hpA.1 hqA.1)
      (hB.isPreconnected.edist_le_hausdorffMeasure hpA.2 hqA.2)
  have h2 {x y : ℝ≥0∞} : x ≤ y / 2 ↔ x * 2 ≤ y :=
    ENNReal.le_div_iff_mul_le (.inl two_ne_zero) (.inl ENNReal.ofNat_ne_top)
  rw [mul_comm, ← h2]
  exact ediam_le fun p hp q hq => h2.2 (hpair p hp q hq)

/-- **A Jordan curve has positive length.** -/
theorem IsJordanCurve.hausdorffMeasure_pos (h : IsJordanCurve C) : 0 < μH[1] C := by
  have hdiam : 0 < ediam C := ediam_pos_iff.2 (not_subsingleton_iff.1 h.not_subsingleton)
  exact (ENNReal.mul_pos two_ne_zero hdiam.ne').trans_le h.two_mul_ediam_le_hausdorffMeasure

end TauCeti
