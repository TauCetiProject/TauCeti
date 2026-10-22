/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.ConditionalProbability
public import TauCeti.MeasureTheory.Measure.WithDensity
public import TauCeti.Probability.Density

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

* `TauCeti.Probability.hasPDF_abs`, `TauCeti.Probability.pdf_abs` — the density of `|X|`;
* `TauCeti.Probability.map_abs_eq_cond_Ici` — a symmetric law with no atom at `0` folds to its
  conditioning on `[0, ∞)`.

The identities about `μ.map (|·|)` that do not depend on a random variable live with the theory
they belong to. The decomposition `MeasureTheory.Measure.map_abs_eq_restrict_add_restrict` and the
atom `MeasureTheory.Measure.map_abs_apply_zero` are in `TauCeti.MeasureTheory.Measure.Real`, the
density `TauCeti.Probability.map_abs_withDensity` is in `TauCeti.MeasureTheory.Measure.WithDensity`,
the cdf formulas `MeasureTheory.Measure.cdf_map_abs_of_nonneg`,
`MeasureTheory.Measure.cdf_map_abs_of_neg` and `MeasureTheory.Measure.cdf_map_abs_of_isNegInvariant`
are in `TauCeti.Probability.Cdf`, and the quantile formula `MeasureTheory.Measure.quantile_map_abs`
is in `TauCeti.Probability.Quantile`.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

private theorem measurable_abs : Measurable fun x : ℝ => |x| := continuous_abs.measurable

namespace TauCeti.Probability

variable {μ : Measure ℝ}

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

private theorem measurable_foldedPDF :
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
  rw [μ.map_abs_eq_restrict_add_restrict, Measure.neg_eq_self, hIoi, ProbabilityTheory.cond,
    hhalf, inv_inv, two_smul]

end TauCeti.Probability
