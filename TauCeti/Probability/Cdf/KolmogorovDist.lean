/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.CDF

/-!
# The Kolmogorov distance

The Kolmogorov distance between two measures `μ` and `ν` on `ℝ` is the uniform distance
`⨆ t, |cdf μ t - cdf ν t|` between their cumulative distribution functions. Mathlib's `cdf` takes
values in `[0, 1]` for every measure, so the family is bounded and the supremum is an honest real
supremum with values in `[0, 1]`. For probability measures `cdf μ t = μ.real (Iic t)`, and the
distance vanishes exactly when the two measures are equal.

The definitions and lemmas below make no probability hypothesis unless they need one: for a
measure that is not a probability measure, Mathlib's `cdf` is a junk Stieltjes function, and the
distance is then the uniform distance between these junk functions.

## Main definitions

* `ProbabilityTheory.kolmogorovDist μ ν`: the Kolmogorov distance `⨆ t, |cdf μ t - cdf ν t|`.

## Main results

* `ProbabilityTheory.abs_cdf_sub_cdf_le_kolmogorovDist` and
  `ProbabilityTheory.abs_measureReal_Iic_sub_le_kolmogorovDist`: the distance dominates the
  discrepancy of the distribution functions at every point;
* `ProbabilityTheory.kolmogorovDist_le_iff` and `ProbabilityTheory.lt_kolmogorovDist_iff`: bounds
  on the distance are pointwise bounds on the discrepancy;
* `ProbabilityTheory.kolmogorovDist_nonneg` and `ProbabilityTheory.kolmogorovDist_le_one`: the
  distance lies in `[0, 1]`;
* `ProbabilityTheory.kolmogorovDist_comm`: symmetry;
* `ProbabilityTheory.kolmogorovDist_triangle`: the triangle inequality;
* `ProbabilityTheory.kolmogorovDist_eq_zero_iff_cdf_eq` and
  `ProbabilityTheory.kolmogorovDist_eq_zero_iff`: the distance vanishes exactly when the
  distribution functions agree, which for probability measures means that the measures agree.

## References

* Lipnowski, Tsimerman, *How large is A_g(𝔽_q)?*, arXiv v1, Corollary 5.14.
-/

public section

open MeasureTheory Set

namespace ProbabilityTheory

/-- The discrepancy of two distribution functions at a point is at most one. -/
theorem abs_cdf_sub_cdf_le_one (μ ν : Measure ℝ) (t : ℝ) : |cdf μ t - cdf ν t| ≤ 1 :=
  abs_sub_le_of_nonneg_of_le (cdf_nonneg μ t) (cdf_le_one μ t) (cdf_nonneg ν t) (cdf_le_one ν t)

/-- The discrepancies of two distribution functions form a family bounded above. -/
theorem bddAbove_range_abs_cdf_sub_cdf (μ ν : Measure ℝ) :
    BddAbove (range fun t ↦ |cdf μ t - cdf ν t|) :=
  ⟨1, by rintro _ ⟨t, rfl⟩; exact abs_cdf_sub_cdf_le_one μ ν t⟩

/-- The **Kolmogorov distance** between two measures on `ℝ`: the supremum over `t` of the
discrepancy `|cdf μ t - cdf ν t|` of their distribution functions. It is meaningful for probability
measures, for which `cdf μ t = μ.real (Iic t)`. -/
noncomputable def kolmogorovDist (μ ν : Measure ℝ) : ℝ := ⨆ t, |cdf μ t - cdf ν t|

/-- The defining formula of the Kolmogorov distance. -/
theorem kolmogorovDist_def (μ ν : Measure ℝ) :
    kolmogorovDist μ ν = ⨆ t, |cdf μ t - cdf ν t| := (rfl)

/-- The Kolmogorov distance dominates the discrepancy of the distribution functions at each
point. -/
theorem abs_cdf_sub_cdf_le_kolmogorovDist (μ ν : Measure ℝ) (t : ℝ) :
    |cdf μ t - cdf ν t| ≤ kolmogorovDist μ ν :=
  le_ciSup (bddAbove_range_abs_cdf_sub_cdf μ ν) t

/-- For probability measures, the Kolmogorov distance dominates `|μ (Iic x) - ν (Iic x)|` at each
point `x`. -/
theorem abs_measureReal_Iic_sub_le_kolmogorovDist (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (x : ℝ) :
    |μ.real (Iic x) - ν.real (Iic x)| ≤ kolmogorovDist μ ν := by
  rw [← cdf_eq_real, ← cdf_eq_real]
  exact abs_cdf_sub_cdf_le_kolmogorovDist μ ν x

/-- The Kolmogorov distance is at most `c` if and only if the discrepancy of the distribution
functions is at most `c` at every point. -/
theorem kolmogorovDist_le_iff {μ ν : Measure ℝ} {c : ℝ} :
    kolmogorovDist μ ν ≤ c ↔ ∀ t, |cdf μ t - cdf ν t| ≤ c :=
  ciSup_le_iff (bddAbove_range_abs_cdf_sub_cdf μ ν)

/-- A pointwise bound on the discrepancy of the distribution functions bounds the Kolmogorov
distance. -/
theorem kolmogorovDist_le {μ ν : Measure ℝ} {c : ℝ} (h : ∀ t, |cdf μ t - cdf ν t| ≤ c) :
    kolmogorovDist μ ν ≤ c :=
  kolmogorovDist_le_iff.2 h

/-- The Kolmogorov distance exceeds `c` if and only if the discrepancy of the distribution
functions exceeds `c` at some point. -/
theorem lt_kolmogorovDist_iff {μ ν : Measure ℝ} {c : ℝ} :
    c < kolmogorovDist μ ν ↔ ∃ t, c < |cdf μ t - cdf ν t| :=
  lt_ciSup_iff (bddAbove_range_abs_cdf_sub_cdf μ ν)

/-- The Kolmogorov distance is nonnegative. -/
theorem kolmogorovDist_nonneg (μ ν : Measure ℝ) : 0 ≤ kolmogorovDist μ ν :=
  (abs_nonneg _).trans (abs_cdf_sub_cdf_le_kolmogorovDist μ ν 0)

/-- The Kolmogorov distance is at most one. -/
theorem kolmogorovDist_le_one (μ ν : Measure ℝ) : kolmogorovDist μ ν ≤ 1 :=
  kolmogorovDist_le (abs_cdf_sub_cdf_le_one μ ν)

/-- The Kolmogorov distance is symmetric. -/
theorem kolmogorovDist_comm (μ ν : Measure ℝ) : kolmogorovDist μ ν = kolmogorovDist ν μ := by
  simp only [kolmogorovDist_def, abs_sub_comm]

/-- The Kolmogorov distance satisfies the triangle inequality. -/
theorem kolmogorovDist_triangle (μ ν ρ : Measure ℝ) :
    kolmogorovDist μ ρ ≤ kolmogorovDist μ ν + kolmogorovDist ν ρ :=
  kolmogorovDist_le fun t ↦ (abs_sub_le _ _ _).trans <|
    add_le_add (abs_cdf_sub_cdf_le_kolmogorovDist μ ν t) (abs_cdf_sub_cdf_le_kolmogorovDist ν ρ t)

/-- The Kolmogorov distance from a measure to itself is zero. -/
@[simp]
theorem kolmogorovDist_self (μ : Measure ℝ) : kolmogorovDist μ μ = 0 := by
  simp [kolmogorovDist_def]

/-- The Kolmogorov distance vanishes exactly when the distribution functions agree. -/
theorem kolmogorovDist_eq_zero_iff_cdf_eq {μ ν : Measure ℝ} :
    kolmogorovDist μ ν = 0 ↔ cdf μ = cdf ν := by
  refine ⟨fun h ↦ StieltjesFunction.ext fun t ↦ ?_, fun h ↦ by simp [kolmogorovDist_def, h]⟩
  have ht := abs_cdf_sub_cdf_le_kolmogorovDist μ ν t
  rw [h] at ht
  exact sub_eq_zero.1 (abs_nonpos_iff.1 ht)

/-- The Kolmogorov distance between probability measures vanishes exactly when the measures are
equal. -/
@[simp]
theorem kolmogorovDist_eq_zero_iff {μ ν : Measure ℝ} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : kolmogorovDist μ ν = 0 ↔ μ = ν := by
  rw [kolmogorovDist_eq_zero_iff_cdf_eq, Measure.cdf_eq_iff]

end ProbabilityTheory
