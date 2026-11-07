/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Space
public import TauCeti.Analysis.BoundedVariation.Perimeter
public import TauCeti.MeasureTheory.Function.SchwarzRearrangement
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import TauCeti.Analysis.BoundedVariation.Ball
import TauCeti.Analysis.BoundedVariation.Coarea
import TauCeti.Analysis.BoundedVariation.Composition
import TauCeti.Analysis.BoundedVariation.Isoperimetric
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Schwarz rearrangement decreases total variation

The BV Pólya–Szegő inequality states that the symmetric decreasing rearrangement of the
positive part of an integrable real-valued function has no greater distributional total
variation. The comparison includes infinite variation and does not require bounded support
or regularity. In particular, Schwarz rearrangement of the positive part or absolute value
preserves whole-space BV membership.

The rearrangement is the canonical extended-nonnegative `TauCeti.schwarzRearrangement`,
applied to `ENNReal.ofReal ∘ u`, and then made real-valued with `ENNReal.toReal`. Integrability
ensures that the extended rearrangement is finite almost everywhere; its possibly infinite
value at the origin therefore causes no ambiguity in the BV statement.

The level-set comparison uses the sharp Euclidean perimeter inequality and the exact
perimeter of the ball with the same volume. Scalar coarea then integrates that comparison.
This establishes a BV bound; Sobolev membership of the rearrangement requires a further
argument excluding singular concentration of its derivative.

## References

* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*,
  Chapter 14 (symmetrization and the isoperimetric inequality).
* E. H. Lieb and M. Loss, *Analysis*, 2nd ed., Chapter 3 (rearrangement inequalities).
-/

public noncomputable section

open MeasureTheory Metric Module Set
open scoped ENNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-- A superlevel set of the Schwarz rearrangement has perimeter at most that of the
corresponding Lebesgue-measurable superlevel set of the original function. Either perimeter
may be infinite; a superlevel set of infinite volume is rearranged to the whole space. -/
theorem _root_.MeasureTheory.NullMeasurableSet.perimeter_setOf_lt_schwarzRearrangement_le
    {f : E → ℝ≥0∞} {t : ℝ≥0∞} (hs : NullMeasurableSet {x | t < f x} volume) :
    perimeter volume ⊤ {x | t < schwarzRearrangement volume f x} ≤
      perimeter volume ⊤ {x | t < f x} := by
  rcases eq_or_ne (volume {x | t < f x}) ∞ with hinf | hfin
  · have hset : {x | t < schwarzRearrangement volume f x} = univ := by
      rw [setOf_lt_schwarzRearrangement, hinf]
      exact volume.setOf_measure_ball_norm_lt_top
    simp only [hset, perimeter_univ, zero_le]
  obtain ⟨r, hr0, hr⟩ := (volume : Measure E).exists_nonneg_addHaar_ball_eq hfin
  have hset : {x | t < schwarzRearrangement volume f x} = ball 0 r := by
    rw [setOf_lt_schwarzRearrangement, ← hr]
    exact volume.setOf_addHaar_ball_norm_lt_addHaar_ball r
  rw [hset]
  rcases eq_or_lt_of_le hr0 with hrzero | hrpos
  · simp [← hrzero]
  have hs0 : volume {x | t < f x} ≠ 0 := by
    rw [← hr]
    exact (measure_ball_pos volume 0 hrpos).ne'
  apply (ENNReal.pow_le_pow_left_iff (n := finrank ℝ E) finrank_pos.ne').mp
  rw [perimeter_ball_pow finrank_pos.ne' hrpos, hr]
  exact hs.finrank_pow_mul_volume_ball_mul_volume_pow_le_perimeter_pow hfin finrank_pos.ne' hs0

variable {u : E → ℝ}

/-- **The BV Pólya–Szegő inequality.** The real-valued Schwarz rearrangement of the positive
part of an integrable function has total variation at most that of the original function.
Both sides are extended nonnegative numbers, so the assertion also permits infinite
variation. For nonnegative functions this is their usual Schwarz rearrangement. -/
theorem totalVariationOn_toReal_schwarzRearrangement_le (hu : Integrable u volume) :
    totalVariationOn volume ⊤
        (fun x ↦ (schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (u y)) x).toReal) ≤
      totalVariationOn volume ⊤ u := by
  let f : E → ℝ≥0∞ := fun x ↦ ENNReal.ofReal (u x)
  let v : E → ℝ := fun x ↦ (schwarzRearrangement volume f x).toReal
  have hf : AEMeasurable f volume := hu.aemeasurable.ennreal_ofReal
  have hae : ∀ᵐ x ∂volume, schwarzRearrangement volume f x ≠ ∞ :=
    hu.ae_schwarzRearrangement_ofReal_ne_top
  have hv : Integrable v volume := hu.toReal_schwarzRearrangement
  rw [totalVariationOn_eq_lintegral_perimeter (hv.locallyIntegrable.locallyIntegrableOn ⊤),
    totalVariationOn_eq_lintegral_perimeter (hu.locallyIntegrable.locallyIntegrableOn ⊤)]
  apply lintegral_mono_ae
  filter_upwards [volume.ae_ne (0 : ℝ)] with t ht
  rcases lt_or_gt_of_ne ht with htneg | htpos
  · have hvlevel : {x | t < v x} = univ :=
      eq_univ_of_forall fun x ↦ htneg.trans_le ENNReal.toReal_nonneg
    rw [hvlevel, perimeter_univ]
    exact zero_le
  · have hlevel : {x | t < v x} =ᵐ[volume]
        {x | ENNReal.ofReal t < schwarzRearrangement volume f x} := by
      filter_upwards [hae] with x hx
      exact propext (ENNReal.ofReal_lt_iff_lt_toReal htpos.le hx).symm
    have hsource : {x | ENNReal.ofReal t < f x} = {x | t < u x} := by
      ext x
      exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg htpos.le
    rw [perimeter_congr_ae (ae_restrict_of_ae hlevel)]
    have hs := nullMeasurableSet_lt (aemeasurable_const (b := ENNReal.ofReal t)) hf
    simpa only [hsource] using hs.perimeter_setOf_lt_schwarzRearrangement_le

/-- **Pólya–Szegő for signed functions.** Rearranging the absolute value of an integrable
real-valued function does not increase its total variation. -/
theorem totalVariationOn_toReal_schwarzRearrangement_norm_le (hu : Integrable u volume) :
    totalVariationOn volume ⊤
        (fun x ↦ (schwarzRearrangement volume (fun y ↦ ENNReal.ofReal ‖u y‖) x).toReal) ≤
      totalVariationOn volume ⊤ u := by
  refine (totalVariationOn_toReal_schwarzRearrangement_le hu.norm).trans ?_
  simpa only [Function.comp_def, ENNReal.coe_one, one_mul] using
    totalVariationOn_comp_lipschitz_le (hu.locallyIntegrable.locallyIntegrableOn ⊤)
      (lipschitzWith_one_norm : LipschitzWith 1 (norm : ℝ → ℝ))

/-- Schwarz rearrangement of the positive part preserves whole-space BV. -/
theorem MemBV.toReal_schwarzRearrangement (hu : MemBV volume ⊤ u) :
    MemBV volume ⊤
      (fun x ↦ (schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (u y)) x).toReal) := by
  have hint : Integrable u volume := by simpa using hu.integrableOn
  exact memBV_iff.mpr ⟨by simpa using hint.toReal_schwarzRearrangement,
    (totalVariationOn_toReal_schwarzRearrangement_le hint).trans_lt hu.totalVariationOn_lt_top⟩

/-- Rearranging the absolute value of a whole-space BV function preserves BV membership. -/
theorem MemBV.toReal_schwarzRearrangement_norm (hu : MemBV volume ⊤ u) :
    MemBV volume ⊤
      (fun x ↦ (schwarzRearrangement volume (fun y ↦ ENNReal.ofReal ‖u y‖) x).toReal) := by
  simpa only [Function.comp_def] using
    (hu.comp_lipschitz (lipschitzWith_one_norm : LipschitzWith 1 (norm : ℝ → ℝ))
      norm_zero).toReal_schwarzRearrangement

end TauCeti
