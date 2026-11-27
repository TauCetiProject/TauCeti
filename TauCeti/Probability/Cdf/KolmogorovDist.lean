/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.TotalVariation.Basic
public import TauCeti.Probability.Cdf

/-!
# The Kolmogorov distance

The Kolmogorov distance between two measures `μ` and `ν` on `ℝ` is the uniform distance
`⨆ t, |cdf μ t - cdf ν t|` between their cumulative distribution functions. Mathlib's `cdf` takes
values in `[0, 1]` for every measure, so the family is bounded and the supremum is an honest real
supremum with values in `[0, 1]`. For probability measures `cdf μ t = μ.real (Iic t)`, and the
distance vanishes exactly when the two measures are equal.

For probability measures the distance is at most half the total variation distance `tvDist`, it
is unchanged by an increasing reparametrization of the line and by reflection, and it is at least
half the mass of any atom of one law at which the distribution function of the other is
continuous. By right
continuity of distribution functions the supremum may be taken over rational points, so the
Kolmogorov distance between two random laws is measurable as soon as their distribution functions
are measurable at each rational point.

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
  distribution functions agree, which for probability measures means that the measures agree;
* `ProbabilityTheory.kolmogorovDist_le_tvDist_div_two`: for probability measures the Kolmogorov
  distance is at most half the total variation distance;
* `ProbabilityTheory.kolmogorovDist_eq_iSup_rat` and `ProbabilityTheory.measurable_kolmogorovDist`:
  the supremum may be taken over rational points, hence measurability of the distance between
  random laws;
* `ProbabilityTheory.kolmogorovDist_map_orderIso`, `ProbabilityTheory.kolmogorovDist_neg` and
  `ProbabilityTheory.kolmogorovDist_map_mul_add`: invariance under increasing homeomorphisms of
  `ℝ`, under the reflection `x ↦ -x`, and under `x ↦ a * x + b` with `a ≠ 0`;
* `ProbabilityTheory.kolmogorovDist_eq_iSup_measureReal_Iio`: for probability measures the
  supremum may be taken over the masses of open rays, the left limits of the distribution
  functions;
* `ProbabilityTheory.abs_measureReal_singleton_sub_le_two_mul_kolmogorovDist` and
  `ProbabilityTheory.measureReal_singleton_div_two_le_kolmogorovDist`: the jump bound, which gives
  `kolmogorovDist μ ν ≥ μ {x} / 2` when `cdf ν` is continuous at `x`.

## References

* Lipnowski, Tsimerman, *How large is A_g(𝔽_q)?*, arXiv v1, Corollary 5.14.
-/

public section

open Filter MeasureTheory Set
open scoped Topology

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

/-- For probability measures, the discrepancy of the distribution functions at each point is at
most half the total variation distance. -/
theorem abs_cdf_sub_cdf_le_tvDist_div_two (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (t : ℝ) : |cdf μ t - cdf ν t| ≤ tvDist μ ν / 2 := by
  rw [cdf_eq_real, cdf_eq_real]
  exact abs_measureReal_sub_le_tvDist_div_two (by simp) (Iic t)

/-- For probability measures, the Kolmogorov distance is at most half the total variation
distance. -/
theorem kolmogorovDist_le_tvDist_div_two (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : kolmogorovDist μ ν ≤ tvDist μ ν / 2 :=
  kolmogorovDist_le (abs_cdf_sub_cdf_le_tvDist_div_two μ ν)

/-- The supremum defining the Kolmogorov distance may be taken over rational points, by right
continuity of distribution functions. -/
theorem kolmogorovDist_eq_iSup_rat (μ ν : Measure ℝ) :
    kolmogorovDist μ ν = ⨆ q : ℚ, |cdf μ q - cdf ν q| := by
  have hbdd : BddAbove (range fun q : ℚ ↦ |cdf μ q - cdf ν q|) :=
    ⟨1, by rintro _ ⟨q, rfl⟩; exact abs_cdf_sub_cdf_le_one μ ν q⟩
  refine le_antisymm (kolmogorovDist_le fun t ↦ ?_)
    (ciSup_le fun q ↦ abs_cdf_sub_cdf_le_kolmogorovDist μ ν q)
  -- Approach `t` from the right along rationals, where the discrepancy is right continuous.
  obtain ⟨u, -, hut, hu⟩ := Real.exists_seq_rat_strictAnti_tendsto t
  have hc : ContinuousWithinAt (fun s ↦ |cdf μ s - cdf ν s|) (Ici t) t :=
    (((cdf μ).right_continuous t).sub ((cdf ν).right_continuous t)).abs
  exact le_of_tendsto' (hc.tendsto.comp (tendsto_nhdsWithin_iff.2
    ⟨hu, Eventually.of_forall fun n ↦ (hut n).le⟩)) fun n ↦ le_ciSup hbdd (u n)

/-- The Kolmogorov distance between two random laws is measurable when their distribution
functions are measurable at every rational point. -/
theorem measurable_kolmogorovDist {Ω : Type*} [MeasurableSpace Ω] {L M : Ω → Measure ℝ}
    (hL : ∀ q : ℚ, Measurable fun ω ↦ cdf (L ω) q) (hM : ∀ q : ℚ, Measurable fun ω ↦ cdf (M ω) q) :
    Measurable fun ω ↦ kolmogorovDist (L ω) (M ω) := by
  simp_rw [kolmogorovDist_eq_iSup_rat]
  exact Measurable.iSup fun q ↦ continuous_abs.measurable.comp ((hL q).sub (hM q))

/-- The Kolmogorov distance between probability measures is invariant under an order isomorphism
of `ℝ`, that is, under an increasing homeomorphism of the line. -/
@[simp]
theorem kolmogorovDist_map_orderIso (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (f : ℝ ≃o ℝ) :
    kolmogorovDist (μ.map f) (ν.map f) = kolmogorovDist μ ν := by
  simp only [kolmogorovDist_def, Measure.cdf_map_orderIso]
  exact f.symm.surjective.iSup_comp fun t ↦ |cdf μ t - cdf ν t|

/-- For probability measures, the Kolmogorov distance dominates `|μ (Iio x) - ν (Iio x)|` at each
point `x`: these masses are the left limits of the distribution functions. -/
theorem abs_measureReal_Iio_sub_le_kolmogorovDist (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (x : ℝ) :
    |μ.real (Iio x) - ν.real (Iio x)| ≤ kolmogorovDist μ ν := by
  rw [← Measure.leftLim_cdf, ← Measure.leftLim_cdf]
  exact le_of_tendsto (((cdf μ).mono.tendsto_leftLim x).sub ((cdf ν).mono.tendsto_leftLim x)).abs
    (eventually_nhdsWithin_of_forall fun t _ ↦ abs_cdf_sub_cdf_le_kolmogorovDist μ ν t)

/-- For probability measures, the supremum defining the Kolmogorov distance may be taken over the
masses of the open rays `Iio x`, that is, over the left limits of the distribution functions. -/
theorem kolmogorovDist_eq_iSup_measureReal_Iio (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    kolmogorovDist μ ν = ⨆ x, |μ.real (Iio x) - ν.real (Iio x)| := by
  have hbdd : BddAbove (range fun x ↦ |μ.real (Iio x) - ν.real (Iio x)|) :=
    ⟨kolmogorovDist μ ν, by
      rintro _ ⟨x, rfl⟩
      exact abs_measureReal_Iio_sub_le_kolmogorovDist μ ν x⟩
  refine le_antisymm (kolmogorovDist_le fun t ↦ ?_)
    (ciSup_le (abs_measureReal_Iio_sub_le_kolmogorovDist μ ν))
  -- For `s > t`, `ρ (Iio s)` lies between `cdf ρ t` and `cdf ρ s`, so it tends to `cdf ρ t`.
  have key : ∀ ρ : Measure ℝ, [IsProbabilityMeasure ρ] →
      Tendsto (fun s ↦ ρ.real (Iio s)) (𝓝[>] t) (𝓝 (cdf ρ t)) := fun ρ _ ↦
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (((cdf ρ).right_continuous t).tendsto.mono_left (nhdsWithin_mono t Ioi_subset_Ici_self))
      (eventually_nhdsWithin_of_forall fun s hs ↦ by
        rw [cdf_eq_real]
        exact measureReal_mono (Iic_subset_Iio.2 hs))
      (eventually_nhdsWithin_of_forall fun s _ ↦ by
        rw [cdf_eq_real]
        exact measureReal_mono Iio_subset_Iic_self)
  exact le_of_tendsto ((key μ).sub (key ν)).abs (Eventually.of_forall fun s ↦ le_ciSup hbdd s)

/-- The Kolmogorov distance between probability measures is invariant under the reflection
`x ↦ -x`. -/
@[simp]
theorem kolmogorovDist_neg (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    kolmogorovDist μ.neg ν.neg = kolmogorovDist μ ν := by
  simp only [kolmogorovDist_def, Measure.cdf_neg, sub_sub_sub_cancel_left]
  rw [← kolmogorovDist_def, kolmogorovDist_comm, kolmogorovDist_eq_iSup_measureReal_Iio]
  exact neg_surjective.iSup_comp fun x ↦ |ν.real (Iio x) - μ.real (Iio x)|

/-- The Kolmogorov distance between probability measures is invariant under the affine map
`x ↦ a * x + b` for `a ≠ 0`. -/
theorem kolmogorovDist_map_mul_add (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {a : ℝ} (ha : a ≠ 0) (b : ℝ) :
    kolmogorovDist (μ.map fun x ↦ a * x + b) (ν.map fun x ↦ a * x + b) = kolmogorovDist μ ν := by
  have hpos : ∀ c : ℝ, 0 < c → ∀ d : ℝ,
      kolmogorovDist (μ.map fun x ↦ c * x + d) (ν.map fun x ↦ c * x + d) =
        kolmogorovDist μ ν := fun c hc d ↦ by
    have hf : ⇑((OrderIso.mulLeft₀ c hc).trans (OrderIso.addRight d)) = fun x ↦ c * x + d := by
      ext x
      simp
    rw [← hf, kolmogorovDist_map_orderIso]
  rcases ha.lt_or_gt with ha | ha
  · -- A negative slope is a positive one followed by the reflection `x ↦ -x`.
    have hmap : ∀ ρ : Measure ℝ,
        ρ.map (fun x ↦ a * x + b) = (ρ.map fun x ↦ -a * x + -b).neg := fun ρ ↦ by
      rw [Measure.neg_def, Measure.map_map measurable_neg (by fun_prop)]
      congr 1
      ext x
      simp only [Function.comp_apply]
      ring
    rw [hmap μ, hmap ν, kolmogorovDist_neg, hpos (-a) (neg_pos.2 ha)]
  · exact hpos a ha b

/-- For probability measures, the masses of a point differ by at most twice the Kolmogorov
distance: the mass of `{x}` is the jump `μ (Iic x) - μ (Iio x)` of the distribution function. -/
theorem abs_measureReal_singleton_sub_le_two_mul_kolmogorovDist (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (x : ℝ) :
    |μ.real {x} - ν.real {x}| ≤ 2 * kolmogorovDist μ ν := by
  have hjump : ∀ ρ : Measure ℝ, [IsProbabilityMeasure ρ] →
      ρ.real {x} = ρ.real (Iic x) - ρ.real (Iio x) := fun ρ _ ↦ by
    rw [← Iio_union_right, measureReal_union (disjoint_singleton_right.2 (lt_irrefl x))
      (measurableSet_singleton x)]
    ring
  rw [hjump μ, hjump ν, two_mul]
  calc |μ.real (Iic x) - μ.real (Iio x) - (ν.real (Iic x) - ν.real (Iio x))|
      = |(μ.real (Iic x) - ν.real (Iic x)) - (μ.real (Iio x) - ν.real (Iio x))| := by
        congr 1
        ring
    _ ≤ |μ.real (Iic x) - ν.real (Iic x)| + |μ.real (Iio x) - ν.real (Iio x)| := abs_sub _ _
    _ ≤ kolmogorovDist μ ν + kolmogorovDist μ ν :=
      add_le_add (abs_measureReal_Iic_sub_le_kolmogorovDist μ ν x)
        (abs_measureReal_Iio_sub_le_kolmogorovDist μ ν x)

/-- **The jump bound.** If a probability measure `μ` has an atom of mass `a` at `x` and the
distribution function of the probability measure `ν` is continuous at `x`, then the Kolmogorov
distance between `μ` and `ν` is at least `a / 2`. -/
theorem measureReal_singleton_div_two_le_kolmogorovDist (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {x : ℝ} (hν : ContinuousAt (cdf ν) x) :
    μ.real {x} / 2 ≤ kolmogorovDist μ ν := by
  have h := abs_measureReal_singleton_sub_le_two_mul_kolmogorovDist μ ν x
  rw [measureReal_def ν, (Measure.continuousAt_cdf_iff ν x).1 hν, ENNReal.toReal_zero, sub_zero,
    abs_of_nonneg measureReal_nonneg] at h
  linarith

end ProbabilityTheory
