/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.FiniteMeasure.Ext
public import TauCeti.MeasureTheory.Measure.TotalVariation.Integral
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.BoundedLipschitz

/-!
# The bounded Lipschitz distance

The bounded Lipschitz distance between two measures `μ` and `ν` on a pseudometric space is the
largest discrepancy `|∫ f dμ - ∫ f dν|` over the test functions `f` that are `1`-Lipschitz and
bounded by `1` in absolute value. It is taken in `ℝ≥0∞`, as Mathlib's `etvDist` and
`levyProkhorovEDist` are; for finite measures it is finite.

For probability measures it is at most `2` and at most the total variation distance, it is
symmetric, satisfies the triangle inequality, and vanishes exactly when the two measures agree.
The last fact rests on an extensionality principle of independent interest: on a pseudometric
space with its Borel σ-algebra, a finite measure is determined by the integrals of the `1`-Lipschitz
functions bounded by `1`, since rescaled thickened indicators of a closed set are such functions
and decrease to its indicator. This principle is proved in
`TauCeti.MeasureTheory.Measure.FiniteMeasure.Ext`. On a Polish space the distance metrizes weak
convergence of probability measures, by the bounded-Lipschitz form of Kantorovich--Rubinstein
duality.

Unlike the Kolmogorov distance on `ℝ`, the bounded Lipschitz distance sees the geometry of the
space: the point masses at `0` and `1 / n` are at bounded Lipschitz distance `1 / n` but at
Kolmogorov distance `1`.

## Main definitions

* `MeasureTheory.boundedLipschitzDist μ ν`: the bounded Lipschitz distance.

## Main results

* `MeasureTheory.boundedLipschitzDist_le_iff`: upper bounds on the distance are bounds on the
  discrepancy of each test function;
* `MeasureTheory.boundedLipschitzDist_comm`, `MeasureTheory.boundedLipschitzDist_triangle`:
  symmetry and the triangle inequality;
* `MeasureTheory.boundedLipschitzDist_le_add`, `MeasureTheory.boundedLipschitzDist_le_two`: the
  distance is at most the sum of the total masses, hence at most `2` for probability measures;
* `MeasureTheory.boundedLipschitzDist_le_etvDist`,
  `MeasureTheory.toReal_boundedLipschitzDist_le_tvDist`: the distance is at most the total
  variation distance;
* `MeasureTheory.boundedLipschitzDist_eq_zero_iff`: for finite Borel measures the distance
  vanishes exactly when the measures agree;
* `MeasureTheory.ProbabilityMeasure.tendsto_boundedLipschitzDist_iff_tendsto`: on a Polish space,
  convergence in the bounded Lipschitz distance is weak convergence.

## References

* R. M. Dudley, *Real Analysis and Probability*, Cambridge University Press, 2002, Section 11.3.
* A. W. van der Vaart, J. A. Wellner, *Weak Convergence and Empirical Processes*, Springer, 1996,
  Section 1.12.
-/

public section

open Filter Set
open scoped BoundedContinuousFunction ENNReal NNReal Topology

namespace MeasureTheory

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]

/-- The **bounded Lipschitz distance** between two measures on a pseudometric space: the supremum,
over the `1`-Lipschitz real functions `f` bounded by `1` in absolute value, of the discrepancy
`|∫ f dμ - ∫ f dν|`. It takes values in `ℝ≥0∞`, and is finite for finite measures. -/
noncomputable def boundedLipschitzDist (μ ν : Measure X) : ℝ≥0∞ :=
  ⨆ (f : X → ℝ) (_ : LipschitzWith 1 f) (_ : ∀ x, ‖f x‖ ≤ 1),
    ENNReal.ofReal |∫ x, f x ∂μ - ∫ x, f x ∂ν|

/-- The defining formula of the bounded Lipschitz distance. -/
theorem boundedLipschitzDist_def (μ ν : Measure X) :
    boundedLipschitzDist μ ν = ⨆ (f : X → ℝ) (_ : LipschitzWith 1 f) (_ : ∀ x, ‖f x‖ ≤ 1),
      ENNReal.ofReal |∫ x, f x ∂μ - ∫ x, f x ∂ν| := (rfl)

section Basic

variable {μ ν : Measure X}

/-- The bounded Lipschitz distance dominates the discrepancy of each test function. -/
theorem ofReal_abs_integral_sub_integral_le_boundedLipschitzDist {f : X → ℝ}
    (hf : LipschitzWith 1 f) (hb : ∀ x, ‖f x‖ ≤ 1) :
    ENNReal.ofReal |∫ x, f x ∂μ - ∫ x, f x ∂ν| ≤ boundedLipschitzDist μ ν :=
  le_iSup₂_of_le f hf <| le_iSup_of_le hb le_rfl

/-- An upper bound on the bounded Lipschitz distance is a bound on the discrepancy of every
`1`-Lipschitz function bounded by `1`. -/
theorem boundedLipschitzDist_le_iff {c : ℝ≥0∞} :
    boundedLipschitzDist μ ν ≤ c ↔ ∀ f : X → ℝ, LipschitzWith 1 f → (∀ x, ‖f x‖ ≤ 1) →
      ENNReal.ofReal |∫ x, f x ∂μ - ∫ x, f x ∂ν| ≤ c := by
  simp only [boundedLipschitzDist, iSup_le_iff]

/-- The bounded Lipschitz distance is symmetric. -/
theorem boundedLipschitzDist_comm (μ ν : Measure X) :
    boundedLipschitzDist μ ν = boundedLipschitzDist ν μ := by
  simp only [boundedLipschitzDist, abs_sub_comm]

@[simp]
theorem boundedLipschitzDist_self (μ : Measure X) : boundedLipschitzDist μ μ = 0 := by
  simp [boundedLipschitzDist]

/-- The triangle inequality for the bounded Lipschitz distance. -/
theorem boundedLipschitzDist_triangle (μ ν ρ : Measure X) :
    boundedLipschitzDist μ ρ ≤ boundedLipschitzDist μ ν + boundedLipschitzDist ν ρ :=
  boundedLipschitzDist_le_iff.2 fun _f hf hb ↦
    (ENNReal.ofReal_le_ofReal (abs_sub_le _ _ _)).trans <| ENNReal.ofReal_add_le.trans <|
      add_le_add (ofReal_abs_integral_sub_integral_le_boundedLipschitzDist hf hb)
        (ofReal_abs_integral_sub_integral_le_boundedLipschitzDist hf hb)

/-- The bounded Lipschitz distance is at most the sum of the total masses. -/
theorem boundedLipschitzDist_le_add (μ ν : Measure X) :
    boundedLipschitzDist μ ν ≤ μ univ + ν univ := by
  have hle {ρ : Measure X} {f : X → ℝ} (hb : ∀ x, ‖f x‖ ≤ 1) :
      ENNReal.ofReal |∫ x, f x ∂ρ| ≤ ρ univ := by
    rw [← Real.eNorm_eq_ofReal_abs]
    refine (eNorm_integral_le_lintegral_eNorm f).trans ?_
    calc ∫⁻ x, ‖f x‖ₑ ∂ρ ≤ ∫⁻ _, 1 ∂ρ := lintegral_mono fun x ↦
          (Real.eNorm_eq_ofReal_abs _).trans_le (ENNReal.ofReal_le_one.2 (by simpa using hb x))
      _ = ρ univ := lintegral_one
  refine boundedLipschitzDist_le_iff.2 fun f _ hb ↦ ?_
  calc ENNReal.ofReal |∫ x, f x ∂μ - ∫ x, f x ∂ν|
      ≤ ENNReal.ofReal (|∫ x, f x ∂μ| + |∫ x, f x ∂ν|) := ENNReal.ofReal_le_ofReal (abs_sub _ _)
    _ ≤ ENNReal.ofReal |∫ x, f x ∂μ| + ENNReal.ofReal |∫ x, f x ∂ν| := ENNReal.ofReal_add_le
    _ ≤ μ univ + ν univ := add_le_add (hle hb) (hle hb)

/-- The bounded Lipschitz distance between probability measures is at most `2`. -/
theorem boundedLipschitzDist_le_two [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    boundedLipschitzDist μ ν ≤ 2 := by
  simpa [one_add_one_eq_two] using boundedLipschitzDist_le_add μ ν

/-- The bounded Lipschitz distance between finite measures is finite. -/
theorem boundedLipschitzDist_lt_top [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    boundedLipschitzDist μ ν < ∞ :=
  (boundedLipschitzDist_le_add μ ν).trans_lt <|
    ENNReal.add_lt_top.2 ⟨measure_lt_top μ univ, measure_lt_top ν univ⟩

/-- The bounded Lipschitz distance between finite measures is finite. -/
@[simp]
theorem boundedLipschitzDist_ne_top [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    boundedLipschitzDist μ ν ≠ ∞ :=
  boundedLipschitzDist_lt_top.ne

/-- The bounded Lipschitz distance is at most the total variation distance. -/
theorem boundedLipschitzDist_le_etvDist [OpensMeasurableSpace X] (μ ν : Measure X) :
    boundedLipschitzDist μ ν ≤ etvDist μ ν := by
  by_cases h : IsFiniteMeasure μ ∧ IsFiniteMeasure ν
  · obtain ⟨_, _⟩ := h
    refine boundedLipschitzDist_le_iff.2 fun f hf hb ↦ ?_
    rw [← ofReal_tvDist]
    refine ENNReal.ofReal_le_ofReal ?_
    have hm := hf.continuous.aestronglyMeasurable (μ := μ)
    simpa using norm_integral_sub_integral_le_mul_tvDist hm
      (hf.continuous.aestronglyMeasurable (μ := ν)) hb
  · rw [etvDist_of_not_isFiniteMeasure h]
    exact le_top

/-- The real-valued bounded Lipschitz distance is at most the total variation distance. -/
theorem toReal_boundedLipschitzDist_le_tvDist [OpensMeasurableSpace X]
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (boundedLipschitzDist μ ν).toReal ≤ tvDist μ ν := by
  simpa only [tvDist] using
    ENNReal.toReal_mono (etvDist_ne_top μ ν) (boundedLipschitzDist_le_etvDist μ ν)

/-- On a pseudometric space with its Borel σ-algebra, the bounded Lipschitz distance between
finite measures vanishes exactly when the measures are equal. -/
@[simp]
theorem boundedLipschitzDist_eq_zero_iff [BorelSpace X] [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    boundedLipschitzDist μ ν = 0 ↔ μ = ν := by
  refine ⟨fun h ↦ ext_of_forall_integral_eq_of_lipschitzWith fun f hf hb ↦ ?_,
    by rintro rfl; exact boundedLipschitzDist_self μ⟩
  have hle := ofReal_abs_integral_sub_integral_le_boundedLipschitzDist (μ := μ) (ν := ν) hf hb
  rwa [h, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero, abs_nonpos_iff, sub_eq_zero] at hle

end Basic

namespace ProbabilityMeasure

variable [PolishSpace X] [BorelSpace X] {ι : Type*} {l : Filter ι} {μs : ι → ProbabilityMeasure X}
  {μ : ProbabilityMeasure X}

/-- On a Polish space, probability measures converge weakly if and only if they converge in the
bounded Lipschitz distance. -/
theorem tendsto_boundedLipschitzDist_iff_tendsto :
    Tendsto (fun i ↦ boundedLipschitzDist (μs i : Measure X) μ) l (𝓝 0) ↔
      Tendsto μs l (𝓝 μ) :=
  (TauCeti.tendsto_probabilityMeasure_iff_iSup_abs_integral_sub_integral_boundedLipschitz
    one_pos).symm

end ProbabilityMeasure

end MeasureTheory
