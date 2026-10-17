/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.ConditionalProbability
public import TauCeti.MeasureTheory.Measure.WithDensity
public import TauCeti.Probability.Density
public import TauCeti.Probability.Quantile

/-!
# Folding a real law

For a measure `μ` on `ℝ`, the law of `|X|` for `X` with law `μ` is the pushforward
`μ.map (|·|)`, the *folded* law. This file describes it in terms of `μ`.

The basic identity decomposes the folded law as `μ.restrict (Ici 0) + μ.neg.restrict (Ioi 0)`:
the nonnegative half of `μ` stays where it is and the negative half is reflected onto the positive
half-line. The other results follow from it.

* The cdf of the folded law at `x ≥ 0` is `cdf μ x - μ.real (Iio (-x))`, the mass of `[-x, x]`,
  and it vanishes below `0`. The atom of the folded law at `0` is the atom of `μ` there.
* If `μ` has a density `f` with respect to Lebesgue measure, the folded law has density
  `f x + f (-x)` on the positive half-line and `0` elsewhere.
* If `μ` is symmetric, the folded law has cdf `2 * cdf μ x - 1` at `x ≥ 0`, and its quantile at
  a positive level `u` is the quantile of `μ` at level `(1 + u) / 2`. If in addition `μ` has no
  atom at `0`, folding is the same as conditioning `μ` on `[0, ∞)`.

Symmetry is expressed by Mathlib's `MeasureTheory.Measure.IsNegInvariant`. The folded normal,
half-normal, half-Student t and half-Cauchy laws are folds of laws on `ℝ`, so their cdfs,
densities and quantiles are instances of these formulas.

## Main results

* `TauCeti.Probability.map_abs_eq_restrict_add_restrict` — the decomposition of the folded law;
* `TauCeti.Probability.cdf_map_abs_of_nonneg`, `TauCeti.Probability.cdf_map_abs_of_neg` — its cdf;
* `TauCeti.Probability.map_abs_apply_zero` — its atom at `0`;
* `TauCeti.Probability.map_abs_withDensity` — its density;
* `TauCeti.Probability.hasPDF_abs`, `TauCeti.Probability.pdf_abs` — the density of `|X|`;
* `TauCeti.Probability.cdf_map_abs_of_isNegInvariant` — the cdf `2 F(x) - 1` of a symmetric fold;
* `TauCeti.Probability.quantile_map_abs` — the quantile `Q_μ ((1 + u) / 2)` of a symmetric fold;
* `TauCeti.Probability.map_abs_eq_cond_Ici` — a symmetric law with no atom at `0` folds to its
  conditioning on `[0, ∞)`.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace TauCeti.Probability

variable {μ : Measure ℝ}

private theorem measurable_abs : Measurable fun x : ℝ => |x| := continuous_abs.measurable

/-- **The folded law.** Folding keeps the nonnegative half of `μ` in place and reflects its
negative half onto the positive half-line. -/
theorem map_abs_eq_restrict_add_restrict (μ : Measure ℝ) :
    μ.map (|·|) = μ.restrict (Ici 0) + μ.neg.restrict (Ioi 0) := by
  ext s hs
  have hpre : (|·|) ⁻¹' s = (s ∩ Ici 0) ∪ (-s ∩ Iio 0) := by
    ext x
    rcases le_or_gt 0 x with hx | hx
    · simp [hx, abs_of_nonneg hx, not_lt.2 hx]
    · simp [hx, abs_of_neg hx, not_le.2 hx]
  have hdisj : Disjoint (s ∩ Ici 0) (-s ∩ Iio 0) :=
    disjoint_left.2 fun x hx hx' => not_le.2 hx'.2 hx.2
  rw [Measure.map_apply measurable_abs hs, hpre,
    measure_union hdisj (hs.neg.inter measurableSet_Iio), Measure.add_apply,
    Measure.restrict_apply hs, Measure.restrict_apply hs, Measure.neg_apply,
    (by ext x; simp : -(s ∩ Ioi (0 : ℝ)) = -s ∩ Iio 0)]

/-- The cdf of the folded law at a nonnegative point `x` is the mass of `[-x, x]`, that is, the cdf
of `μ` at `x` minus its left limit at `-x`. -/
theorem cdf_map_abs_of_nonneg [IsProbabilityMeasure μ] {x : ℝ} (hx : 0 ≤ x) :
    cdf (μ.map (|·|)) x = cdf μ x - μ.real (Iio (-x)) := by
  have hpre : (|·|) ⁻¹' Iic x = Iic x \ Iio (-x) := by
    ext y
    simp [abs_le, and_comm]
  rw [cdf_eq_real, map_measureReal_apply measurable_abs measurableSet_Iic, hpre,
    measureReal_sdiff (Iio_subset_Iic_self.trans (Iic_subset_Iic.2 (by linarith)))
      measurableSet_Iio, cdf_eq_real]

/-- The folded law puts no mass on the negative half-line. -/
theorem cdf_map_abs_of_neg [IsProbabilityMeasure μ] {x : ℝ} (hx : x < 0) :
    cdf (μ.map (|·|)) x = 0 := by
  have hpre : (|·|) ⁻¹' Iic x = ∅ :=
    eq_empty_of_forall_notMem fun y hy => not_le.2 hx ((abs_nonneg y).trans hy)
  rw [cdf_eq_real, map_measureReal_apply measurable_abs measurableSet_Iic, hpre,
    measureReal_empty]

/-- The atom of the folded law at `0` is the atom of `μ` at `0`. -/
@[simp]
theorem map_abs_apply_zero (μ : Measure ℝ) : μ.map (|·|) {0} = μ {0} := by
  rw [Measure.map_apply measurable_abs (measurableSet_singleton 0)]
  congr 1
  ext x
  simp

/-- **The folded density.** If `μ` has density `f` with respect to Lebesgue measure, then the
folded law has density `f x + f (-x)` on the positive half-line and `0` elsewhere. -/
theorem map_abs_withDensity {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    (volume.withDensity f).map (|·|) =
      volume.withDensity ((Ioi 0).indicator fun x => f x + f (-x)) := by
  have hneg : (volume.withDensity f).neg = volume.withDensity fun x => f (-x) := by
    simpa [Measure.neg_def] using MeasurableEquiv.map_withDensity (MeasurableEquiv.neg ℝ) volume f
  rw [map_abs_eq_restrict_add_restrict, hneg, restrict_withDensity measurableSet_Ici,
    restrict_withDensity measurableSet_Ioi, Measure.restrict_congr_set Ioi_ae_eq_Ici.symm,
    ← withDensity_indicator measurableSet_Ioi, ← withDensity_indicator measurableSet_Ioi,
    ← withDensity_add_left (hf.indicator measurableSet_Ioi)]
  congr 1
  ext x
  by_cases hx : x ∈ Ioi 0 <;> simp [hx]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}

/-- The law of `|X|` for a variable `X` with a density is the folded density. -/
private theorem hasLaw_abs_withDensity [HasPDF X P] :
    HasLaw (fun ω => |X ω|)
      (volume.withDensity ((Ioi 0).indicator fun x => pdf X P volume x + pdf X P volume (-x)))
      P := by
  have hX : HasLaw X (volume.withDensity (pdf X P volume)) P :=
    ⟨HasPDF.aemeasurable X P volume, map_eq_withDensity_pdf X P volume⟩
  rw [← map_abs_withDensity (measurable_pdf X P volume)]
  exact HasLaw.comp ⟨measurable_abs.aemeasurable, rfl⟩ hX

private theorem measurable_foldedPDF [HasPDF X P] :
    Measurable ((Ioi 0).indicator fun x => pdf X P volume x + pdf X P volume (-x)) :=
  ((measurable_pdf X P volume).add ((measurable_pdf X P volume).comp measurable_neg)).indicator
    measurableSet_Ioi

/-- If `X` has a density, so does `|X|`. -/
theorem hasPDF_abs [HasPDF X P] : HasPDF (fun ω => |X ω|) P :=
  hasPDF_of_hasLaw_withDensity measurable_foldedPDF.aemeasurable hasLaw_abs_withDensity

/-- The density of `|X|` is `pdf X P x + pdf X P (-x)` on the positive half-line and `0`
elsewhere. -/
theorem pdf_abs [HasPDF X P] :
    pdf (fun ω => |X ω|) P volume =ᵐ[volume]
      (Ioi 0).indicator fun x => pdf X P volume x + pdf X P volume (-x) :=
  pdf_eq_of_hasLaw_withDensity measurable_foldedPDF.aemeasurable hasLaw_abs_withDensity

/-! ### Symmetric laws -/

/-- For a symmetric law, the mass below `-x` is the mass above `x`, which is `1 - cdf μ x`. -/
private theorem measureReal_Iio_neg [IsProbabilityMeasure μ] [μ.IsNegInvariant] (x : ℝ) :
    μ.real (Iio (-x)) = 1 - cdf μ x := by
  rw [← Set.neg_Ioi, measureReal_def, Measure.measure_neg, ← measureReal_def, ← compl_Iic,
    measureReal_compl measurableSet_Iic, probReal_univ, cdf_eq_real]

/-- The cdf of a symmetric law folded at `x ≥ 0` is `2 * cdf μ x - 1`. -/
theorem cdf_map_abs_of_isNegInvariant [IsProbabilityMeasure μ] [μ.IsNegInvariant] {x : ℝ}
    (hx : 0 ≤ x) : cdf (μ.map (|·|)) x = 2 * cdf μ x - 1 := by
  rw [cdf_map_abs_of_nonneg hx, measureReal_Iio_neg]
  ring

/-- **The quantile of a symmetric fold.** At a positive level `u`, the quantile of the folded law of
a symmetric law `μ` is the quantile of `μ` at level `(1 + u) / 2`. -/
theorem quantile_map_abs [IsProbabilityMeasure μ] [μ.IsNegInvariant] {u : ℝ} (hu : 0 < u) :
    (μ.map (|·|)).quantile u = μ.quantile ((1 + u) / 2) := by
  refine Measure.quantile_eq_of_le_cdf_iff _ _ fun x => ?_
  rcases le_or_gt 0 x with hx | hx
  · rw [cdf_map_abs_of_isNegInvariant hx]
    constructor <;> intro h <;> linarith
  · rw [cdf_map_abs_of_neg hx]
    -- Below `0`, the cdf of a symmetric law is at most `1 / 2`.
    have hle : cdf μ x ≤ 1 - cdf μ x := by
      rw [← measureReal_Iio_neg, cdf_eq_real]
      exact measureReal_mono (Iic_subset_Iio.2 (by linarith))
    constructor <;> intro h <;> linarith

/-- **Folding a symmetric law is conditioning it on `[0, ∞)`**, provided it has no atom at `0`. -/
theorem map_abs_eq_cond_Ici [IsProbabilityMeasure μ] [μ.IsNegInvariant] (h0 : μ {0} = 0) :
    μ.map (|·|) = cond μ (Ici 0) := by
  have hIoi : μ.restrict (Ioi 0) = μ.restrict (Ici 0) :=
    Measure.restrict_congr_set (Ioi_ae_eq_Ici' h0)
  have hhalf : μ (Ici 0) = 2⁻¹ := by
    have hsum : μ (Ici 0) + μ (Iio 0) = 1 := by
      rw [← measure_union (disjoint_left.2 fun x hx hx' => not_le.2 hx' hx) measurableSet_Iio,
        Ici_union_Iio, measure_univ]
    have hneg : μ (Iio 0) = μ (Ici 0) := by
      rw [← measure_congr (Ioi_ae_eq_Ici' h0), ← Measure.measure_neg, Set.neg_Iio, neg_zero]
    rw [hneg, ← mul_two] at hsum
    exact ENNReal.eq_inv_of_mul_eq_one_left hsum
  rw [map_abs_eq_restrict_add_restrict, Measure.neg_eq_self, hIoi, ProbabilityTheory.cond, hhalf,
    inv_inv, two_smul]

end TauCeti.Probability
