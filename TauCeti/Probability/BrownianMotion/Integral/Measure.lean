/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.Predictable
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Trim
import Mathlib.MeasureTheory.Function.LpSeminorm.Trim
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The finite-horizon Brownian predictable measure

The measure `TauCeti.timeMeasure T` is Lebesgue time on `(0,T]` in nonnegative real time.
`MeasureTheory.Filtration.predictableMeasure` trims its product with the sample measure to the
predictable sigma-algebra. This is the measure whose native real `Lp` space at exponent two
is the domain for Brownian integral completion; no Brownian process or usual conditions are
needed to construct it.

Predictable rectangles have their interval-length times event-probability mass, the time-zero
slice is null, and restriction to a shorter horizon commutes with the construction. The
integral dictionary retains the predictable measurability hypothesis: trimming does not
preserve integrals of arbitrary ambient-product-measurable functions.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace TauCeti

/-- Lebesgue time restricted to `(0,T]`, using the real inclusion of nonnegative time. -/
def timeMeasure (T : ℝ≥0) : Measure ℝ≥0 :=
  (Measure.comap ((↑) : ℝ≥0 → ℝ) volume).restrict (Ioc 0 T)

/-- The concrete restriction defining finite-horizon Lebesgue time. -/
theorem timeMeasure_def (T : ℝ≥0) :
    timeMeasure T = (Measure.comap ((↑) : ℝ≥0 → ℝ) volume).restrict (Ioc 0 T) :=
  (rfl)

/-- The mass of a time interval contained in the horizon is its length. -/
@[simp]
theorem timeMeasure_Ioc {s t T : ℝ≥0} (ht : t ≤ T) :
    timeMeasure T (Ioc s t) = ENNReal.ofReal ((t : ℝ) - s) := by
  rw [timeMeasure_def, Measure.restrict_eq_self _ (Ioc_subset_Ioc (zero_le : (0 : ℝ≥0) ≤ s) ht),
    Measure.comap_apply _ NNReal.coe_injective
      (fun _ h => NNReal.isClosedEmbedding_coe.measurableEmbedding.measurableSet_image.mpr h)
      _ measurableSet_Ioc, NNReal.image_coe_Ioc, Real.volume_Ioc]

/-- Finite-horizon Lebesgue time has total mass `T`. -/
@[simp]
theorem timeMeasure_univ (T : ℝ≥0) : timeMeasure T univ = T := by
  rw [timeMeasure_def, Measure.restrict_apply_univ]
  simpa [timeMeasure_def] using timeMeasure_Ioc (s := 0) (T := T) le_rfl

/-- A zero horizon gives the zero measure. -/
@[simp]
theorem timeMeasure_zero : timeMeasure 0 = 0 := by simp [timeMeasure_def]

/-- Finite horizons have finite Lebesgue mass. -/
instance (T : ℝ≥0) : IsFiniteMeasure (timeMeasure T) where
  measure_univ_lt_top := by simp

/-- The time-zero slice carries no Lebesgue mass. -/
@[simp]
theorem timeMeasure_singleton_zero (T : ℝ≥0) : timeMeasure T {0} = 0 := by
  rw [timeMeasure_def, Measure.restrict_apply (measurableSet_singleton _)]
  simp

/-- Restricting to a shorter horizon recovers its time measure. -/
theorem timeMeasure_restrict {S T : ℝ≥0} (hST : S ≤ T) :
    (timeMeasure T).restrict (Ioc 0 S) = timeMeasure S := by
  simp only [timeMeasure_def]
  exact Measure.restrict_restrict_of_subset (Ioc_subset_Ioc le_rfl hST)

end TauCeti

namespace MeasureTheory.Filtration

open TauCeti

variable {Ω : Type*} {m : MeasurableSpace Ω} (ℱ : Filtration ℝ≥0 m) (P : Measure Ω)

/-- Brownian finite-horizon time-product measure on the predictable sigma-algebra.
Its real `Lp` space at exponent two is the predictable square-integrable integrand space. -/
def predictableMeasure (T : ℝ≥0) : @Measure (ℝ≥0 × Ω) ℱ.predictable :=
  ((timeMeasure T).prod P).trim ℱ.predictable_le_prod

/-- The predictable measure is the trim of the ambient time-product measure. -/
theorem predictableMeasure_def (T : ℝ≥0) :
    ℱ.predictableMeasure P T = ((timeMeasure T).prod P).trim ℱ.predictable_le_prod :=
  (rfl)

/-- On predictable sets trimming leaves the ambient time-product mass unchanged. -/
theorem predictableMeasure_apply {T : ℝ≥0} {A : Set (ℝ≥0 × Ω)}
    (hA : MeasurableSet[ℱ.predictable] A) :
    ℱ.predictableMeasure P T A = (timeMeasure T).prod P A :=
  trim_measurableSet_eq ℱ.predictable_le_prod hA

/-- With a finite sample measure the predictable measure is finite. -/
instance (T : ℝ≥0) [IsFiniteMeasure P] :
    @IsFiniteMeasure (ℝ≥0 × Ω) ℱ.predictable (ℱ.predictableMeasure P T) :=
  inferInstanceAs (IsFiniteMeasure (((timeMeasure T).prod P).trim ℱ.predictable_le_prod))

/-- A zero horizon gives the zero predictable measure. -/
@[simp]
theorem predictableMeasure_zero : ℱ.predictableMeasure P 0 = 0 := by
  simp [predictableMeasure_def]

variable [SFinite P]

/-- The total predictable mass is horizon length times sample-space mass. -/
@[simp]
theorem predictableMeasure_univ (T : ℝ≥0) :
    ℱ.predictableMeasure P T univ = T * P univ := by
  rw [ℱ.predictableMeasure_apply P MeasurableSet.univ, ← univ_prod_univ,
    Measure.prod_prod, timeMeasure_univ]

/-- A predictable rectangle has interval-length times event mass. The height event is
measurable at the left endpoint, not the right endpoint. -/
theorem predictableMeasure_Ioc_prod {s t T : ℝ≥0} {A : Set Ω}
    (hA : MeasurableSet[ℱ s] A) (ht : t ≤ T) :
    ℱ.predictableMeasure P T (Ioc s t ×ˢ A) = ENNReal.ofReal ((t : ℝ) - s) * P A := by
  rw [ℱ.predictableMeasure_apply P (measurableSet_predictable_Ioc_prod s t hA),
    Measure.prod_prod, timeMeasure_Ioc ht]

/-- The entire time-zero slice is null, regardless of the filtration at time zero. -/
@[simp]
theorem predictableMeasure_singleton_zero_prod (T : ℝ≥0) :
    ℱ.predictableMeasure P T ({0} ×ˢ univ) = 0 := by
  have h : MeasurableSet[ℱ.predictable] ({0} ×ˢ (univ : Set Ω)) :=
    measurableSet_predictable_singleton_bot_prod MeasurableSet.univ
  rw [ℱ.predictableMeasure_apply P h, Measure.prod_prod]
  simp

/-- Shorter-horizon restriction commutes with predictable trimming. -/
theorem predictableMeasure_restrict {S T : ℝ≥0} (hST : S ≤ T) :
    @Measure.restrict _ ℱ.predictable (ℱ.predictableMeasure P T) (Ioc 0 S ×ˢ univ) =
      ℱ.predictableMeasure P S := by
  rw [predictableMeasure_def, restrict_trim ℱ.predictable_le_prod _
    (measurableSet_predictable_Ioc_prod 0 S MeasurableSet.univ),
    ← Measure.prod_restrict, Measure.restrict_univ, timeMeasure_restrict hST,
    predictableMeasure_def]

omit [SFinite P] in
/-- The predictable integral is the ambient time-product integral for predictable functions. -/
theorem integral_predictableMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ≥0 × Ω → E} (hf : StronglyMeasurable[ℱ.predictable] f) (T : ℝ≥0) :
    ∫ p, f p ∂ℱ.predictableMeasure P T = ∫ p, f p ∂(timeMeasure T).prod P :=
  (integral_trim ℱ.predictable_le_prod hf).symm

/-- Nonnegative predictable integrals can be computed by ordinary time/sample integration.
Unlike a real Bochner energy, the lower integral records infinite square energy faithfully. -/
theorem lintegral_predictableMeasure {f : ℝ≥0 × Ω → ℝ≥0∞}
    (hf : Measurable[ℱ.predictable] f) (T : ℝ≥0) :
    ∫⁻ p, f p ∂ℱ.predictableMeasure P T = ∫⁻ t, ∫⁻ ω, f (t, ω) ∂P ∂timeMeasure T := by
  rw [predictableMeasure_def, lintegral_trim ℱ.predictable_le_prod hf]
  exact lintegral_prod _ (hf.mono ℱ.predictable_le_prod le_rfl).aemeasurable

omit [SFinite P] in
/-- Equality of predictable representatives almost everywhere is the same for the
predictable measure and the ambient time-product measure. -/
theorem ae_eq_predictableMeasure_iff {E : Type*} [MeasurableSpace E] [MeasurableEq E]
    {f g : ℝ≥0 × Ω → E} (hf : Measurable[ℱ.predictable] f)
    (hg : Measurable[ℱ.predictable] g) (T : ℝ≥0) :
    f =ᵐ[ℱ.predictableMeasure P T] g ↔ f =ᵐ[(timeMeasure T).prod P] g :=
  ⟨ae_eq_of_ae_eq_trim, ae_eq_trim_of_measurable ℱ.predictable_le_prod hf hg⟩

omit [SFinite P] in
/-- For predictable functions the native `MemLp` condition can be tested in the ambient
product measure, at every exponent (in particular exponent two). -/
theorem memLp_predictableMeasure_iff {E : Type*} [NormedAddCommGroup E]
    {f : ℝ≥0 × Ω → E} (hf : StronglyMeasurable[ℱ.predictable] f) (T : ℝ≥0) (p : ℝ≥0∞) :
    MemLp f p (ℱ.predictableMeasure P T) ↔ MemLp f p ((timeMeasure T).prod P) := by
  simp only [MemLp, predictableMeasure_def, eLpNorm_trim ℱ.predictable_le_prod hf]

end MeasureTheory.Filtration
