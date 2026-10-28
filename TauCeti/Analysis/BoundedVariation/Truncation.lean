/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Coarea
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# Scalar truncation and total variation

Clipping a locally integrable real function to an interval retains exactly the part of its
coarea integral over that interval. In particular, clipping cannot increase distributional
total variation. Splitting at a level is additive in variation, even if the variation is
infinite. These identities control truncation in approximation arguments without assuming
smoothness or excluding jumps. For finite variation, the discarded upper and lower tails
have variation tending to zero; symmetric bounded truncations therefore converge in the
variation seminorm.

All variations and perimeters are the variational quantities `TauCeti.totalVariationOn` and
`TauCeti.perimeter` on an arbitrary open set, against an additive Haar measure. The proofs
use the scalar coarea formula `TauCeti.totalVariationOn_eq_lintegral_perimeter`.

## References

* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, Theorem 3.40 and the scalar truncation consequences of the coarea formula.
-/

public section

open MeasureTheory Set TopologicalSpace Filter
open scoped ENNReal Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {Ω : Opens E} {u : E → ℝ}

/-- Truncating below at `a` retains the coarea integral over levels at least `a`. -/
theorem totalVariationOn_max_const_eq_lintegral_perimeter
    (hu : LocallyIntegrableOn u Ω μ) (a : ℝ) :
    totalVariationOn μ Ω (fun x => max (u x) a) =
      ∫⁻ t in Ici a, perimeter μ Ω {x | t < u x} := by
  have hmax : LocallyIntegrableOn (fun x => max (u x) a) Ω μ := by
    simpa only [Pi.sup_def] using hu.sup (locallyIntegrableOn_const a)
  rw [totalVariationOn_eq_lintegral_perimeter hmax]
  rw [← lintegral_indicator measurableSet_Ici]
  apply lintegral_congr
  intro t
  by_cases ht : a ≤ t
  · simp [ht, not_lt.mpr ht]
  · have hset : {x | t < max (u x) a} = univ := by
      ext x
      simp only [mem_ofPred_eq, mem_univ, iff_true]
      exact (lt_of_not_ge ht).trans_le (le_max_right _ _)
    rw [hset, perimeter_univ]
    simp [ht]

/-- Truncating above at `b` retains the coarea integral over levels below `b`. -/
theorem totalVariationOn_min_const_eq_lintegral_perimeter
    (hu : LocallyIntegrableOn u Ω μ) (b : ℝ) :
    totalVariationOn μ Ω (fun x => min (u x) b) =
      ∫⁻ t in Iio b, perimeter μ Ω {x | t < u x} := by
  have hmin : LocallyIntegrableOn (fun x => min (u x) b) Ω μ := by
    simpa only [Pi.inf_def] using hu.inf (locallyIntegrableOn_const b)
  rw [totalVariationOn_eq_lintegral_perimeter hmin]
  rw [← lintegral_indicator measurableSet_Iio]
  apply lintegral_congr
  intro t
  by_cases ht : t < b
  · simp [ht]
  · have hset : {x | t < min (u x) b} = ∅ := by
      ext x
      simp [lt_min_iff, ht]
    rw [hset, perimeter_empty]
    simp [ht]

/-- Variation splits exactly into the lower and upper truncations at any level.
Both sides may be infinite. -/
theorem totalVariationOn_min_const_add_max_const (hu : LocallyIntegrableOn u Ω μ) (a : ℝ) :
    totalVariationOn μ Ω (fun x => min (u x) a) +
      totalVariationOn μ Ω (fun x => max (u x) a) = totalVariationOn μ Ω u := by
  rw [totalVariationOn_min_const_eq_lintegral_perimeter hu,
    totalVariationOn_max_const_eq_lintegral_perimeter hu,
    totalVariationOn_eq_lintegral_perimeter hu, ← compl_Iio]
  exact lintegral_add_compl _ measurableSet_Iio

/-- Clipping to `[a,b]` retains precisely the coarea integral over `[a,b)`.
If `b ≤ a`, both the clipped function's variation and this integral vanish. -/
theorem totalVariationOn_max_min_const_eq_lintegral_perimeter
    (hu : LocallyIntegrableOn u Ω μ) (a b : ℝ) :
    totalVariationOn μ Ω (fun x => max a (min (u x) b)) =
      ∫⁻ t in Ico a b, perimeter μ Ω {x | t < u x} := by
  simp_rw [max_comm a]
  have hmin : LocallyIntegrableOn (fun x => min (u x) b) Ω μ := by
    simpa only [Pi.inf_def] using hu.inf (locallyIntegrableOn_const b)
  rw [totalVariationOn_max_const_eq_lintegral_perimeter hmin]
  rw [← lintegral_indicator measurableSet_Ico, ← lintegral_indicator measurableSet_Ici]
  apply lintegral_congr
  intro t
  by_cases ha : a ≤ t
  · by_cases hb : t < b
    · simp [ha, hb]
    · have hset : {x | t < min (u x) b} = ∅ := by
        ext x
        simp [lt_min_iff, hb]
      simp only [ha, mem_Ici, indicator_of_mem, mem_Ico, hb, and_false,
        not_false_eq_true, indicator_of_notMem, hset, perimeter_empty]
  · simp [ha]

/-- Clipping a locally integrable function to an interval does not increase its variation. -/
theorem totalVariationOn_max_min_const_le (hu : LocallyIntegrableOn u Ω μ) (a b : ℝ) :
    totalVariationOn μ Ω (fun x => max a (min (u x) b)) ≤ totalVariationOn μ Ω u := by
  rw [totalVariationOn_max_min_const_eq_lintegral_perimeter hu,
    totalVariationOn_eq_lintegral_perimeter hu]
  exact setLIntegral_le_lintegral _ _

/-- For finite variation, the variation of the upper tail tends to zero as its level
tends to positive infinity. Subtracting the level does not change this variation. -/
theorem tendsto_totalVariationOn_max_const_atTop (hu : LocallyIntegrableOn u Ω μ)
    (hfin : totalVariationOn μ Ω u ≠ ∞) :
    Tendsto (fun a : ℝ => totalVariationOn μ Ω (fun x => max (u x) a)) atTop (𝓝 0) := by
  simp_rw [totalVariationOn_max_const_eq_lintegral_perimeter hu,
    ← lintegral_indicator measurableSet_Ici]
  have hm := measurable_perimeter_setOf_lt hu.aestronglyMeasurable.aemeasurable
  have hlim := tendsto_lintegral_filter_of_dominated_convergence
    (μ := volume) (l := (atTop : Filter ℝ))
    (F := fun a => (Ici a).indicator (fun t => perimeter μ Ω {x | t < u x}))
    (f := fun _ : ℝ => (0 : ℝ≥0∞))
    (fun t => perimeter μ Ω {x | t < u x})
    (.of_forall fun a => hm.indicator measurableSet_Ici)
    (.of_forall fun a => .of_forall fun t => (indicator_le_self _ _) t)
    (by rwa [← totalVariationOn_eq_lintegral_perimeter hu]) ?_
  · simpa using hlim
  · refine .of_forall fun t => tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop t] with a ha
    simp [not_le.mpr ha]

/-- For finite variation, the variation of the lower tail tends to zero as its level
tends to negative infinity. Subtracting the level does not change this variation. -/
theorem tendsto_totalVariationOn_min_const_atBot (hu : LocallyIntegrableOn u Ω μ)
    (hfin : totalVariationOn μ Ω u ≠ ∞) :
    Tendsto (fun a : ℝ => totalVariationOn μ Ω (fun x => min (u x) a)) atBot (𝓝 0) := by
  have h := (tendsto_totalVariationOn_max_const_atTop hu.neg
    (by simpa only [totalVariationOn_neg] using hfin)).comp tendsto_neg_atBot_atTop
  simpa only [Function.comp_def, Pi.neg_apply, max_neg_neg, ← Pi.neg_def,
    totalVariationOn_neg] using h

/-- Symmetric bounded truncations approximate a function of finite variation in the
variation seminorm. Only local integrability is required, even on an unbounded open set. -/
theorem tendsto_totalVariationOn_sub_max_min_const (hu : LocallyIntegrableOn u Ω μ)
    (hfin : totalVariationOn μ Ω u ≠ ∞) :
    Tendsto (fun a : ℝ => totalVariationOn μ Ω
      (fun x => u x - max (-a) (min (u x) a))) atTop (𝓝 0) := by
  have hlim := ((tendsto_totalVariationOn_min_const_atBot hu hfin).comp
    tendsto_neg_atTop_atBot).add (tendsto_totalVariationOn_max_const_atTop hu hfin)
  simp only [add_zero] at hlim
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (.of_forall fun _ => bot_le)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with a ha
  have hdecomp : (fun x => u x - max (-a) (min (u x) a)) =
      (fun x => min (u x) (-a) - (-a)) + (fun x => max (u x) a - a) := by
    ext x
    simp only [Pi.add_apply]
    grind
  have hlo : LocallyIntegrableOn (fun x => min (u x) (-a) - (-a)) Ω μ := by
    simpa only [Pi.inf_def, Pi.sub_def] using
      (hu.inf (locallyIntegrableOn_const (-a))).sub (locallyIntegrableOn_const (-a))
  have hhi : LocallyIntegrableOn (fun x => max (u x) a - a) Ω μ := by
    simpa only [Pi.sup_def, Pi.sub_def] using
      (hu.sup (locallyIntegrableOn_const a)).sub (locallyIntegrableOn_const a)
  rw [hdecomp]
  simpa only [sub_eq_add_neg, totalVariationOn_add_const, Function.comp_apply] using
    totalVariationOn_add_le hlo hhi

end TauCeti
