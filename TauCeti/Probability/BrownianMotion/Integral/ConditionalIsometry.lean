/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.L2
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import TauCeti.Probability.BrownianMotion.Integral.Locality

/-!
# Conditional isometry for elementary and completed Brownian integrals

The elementary Brownian isometry remains valid when both sides are integrated over an event
known before every trading interval. Equivalently, the conditional second moment of an
elementary integral, given information preceding its intervals, is the conditional expectation
of its square energy. The random heights need only belong to `L²`, not be bounded.

The interval family may have an arbitrary finite index type, and observation at `T` clips each
interval at `T`. Empty families, repeated endpoints and intervals not yet started are allowed.
Passing to the completed `L²` integral extends the event-wise and conditional increment energy
identities to any modification of `l2Integral` for a `BrownianIntegrable` integrand
(`setIntegral_sq_sub_of_ae_eq_l2Integral`, `condExp_sq_sub_of_ae_eq_l2Integral`), without
adaptedness, path continuity, or usual conditions on the filtration.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2, in particular Proposition 3.2.10.
-/

public section

open MeasureTheory ProbabilityTheory Finset Set
open scoped NNReal ENNReal

namespace TauCeti.Probability.IsFilteredPreBrownianReal

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {I : Finset ι} {s t : ι → ℝ≥0} {X : ι → Ω → ℝ}

/-- The elementary Brownian isometry on an event known at every left endpoint.
The interval lengths are clipped at the observation time, while the heights remain
measurable at their original left endpoints and need only be square-integrable on the event. -/
theorem setIntegral_sq_sum_mul_sub_min (hW : IsFilteredPreBrownianReal ℱ W P)
    (hst : ∀ i ∈ I, s i ≤ t i)
    (hdisj : (I : Set ι).Pairwise fun i j => t i ≤ s j ∨ t j ≤ s i)
    (hX : ∀ i ∈ I, StronglyMeasurable[ℱ (s i)] (X i))
    {A : Set Ω} (hXi : ∀ i ∈ I, MemLp (X i) 2 (P.restrict A))
    (hAs : ∀ i ∈ I, MeasurableSet[ℱ (s i)] A) (T : ℝ≥0) :
    ∫ ω in A, (∑ i ∈ I,
      X i ω * (W (min (t i) T) ω - W (min (s i) T) ω)) ^ 2 ∂P =
      ∑ i ∈ I, (∫ ω in A, X i ω ^ 2 ∂P) * (↑(min (t i) T) - ↑(min (s i) T)) := by
  rcases I.eq_empty_or_nonempty with rfl | ⟨i₀, hi₀⟩
  · simp
  have hA : MeasurableSet A := ℱ.le (s i₀) A (hAs i₀ hi₀)
  have h := hW.integral_sq_sum_mul_sub_min I hst hdisj
    (fun i hi => (hX i hi).indicator (hAs i hi))
    (fun i hi => (memLp_indicator_iff_restrict hA.nullMeasurableSet).mpr (hXi i hi)) T
  have hleft : (fun ω => (∑ i ∈ I, A.indicator (X i) ω *
      (W (min (t i) T) ω - W (min (s i) T) ω)) ^ 2) =
      A.indicator (fun ω => (∑ i ∈ I, X i ω *
        (W (min (t i) T) ω - W (min (s i) T) ω)) ^ 2) := by
    ext ω
    by_cases hω : ω ∈ A <;> simp [hω]
  have hright (i : ι) : (fun ω => (A.indicator (X i) ω) ^ 2) =
      A.indicator (fun ω => X i ω ^ 2) := by
    ext ω
    by_cases hω : ω ∈ A <;> simp [hω]
  simpa only [hleft, hright, integral_indicator hA] using h

/-- **Conditional elementary Brownian isometry.** Given information before all the
intervals, the conditional second moment of the elementary integral is the conditional
expectation of its square energy. No independence between the random heights is assumed. -/
theorem condExp_sq_sum_mul_sub_min (hW : IsFilteredPreBrownianReal ℱ W P)
    (hst : ∀ i ∈ I, s i ≤ t i)
    (hdisj : (I : Set ι).Pairwise fun i j => t i ≤ s j ∨ t j ≤ s i)
    (hX : ∀ i ∈ I, StronglyMeasurable[ℱ (s i)] (X i))
    (hXi : ∀ i ∈ I, MemLp (X i) 2 P) {r : ℝ≥0} (hrs : ∀ i ∈ I, r ≤ s i)
    (T : ℝ≥0) :
    P[fun ω => (∑ i ∈ I,
      X i ω * (W (min (t i) T) ω - W (min (s i) T) ω)) ^ 2 | ℱ r] =ᵐ[P]
      P[fun ω => ∑ i ∈ I,
        X i ω ^ 2 * (↑(min (t i) T) - ↑(min (s i) T)) | ℱ r] := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  have henergy : Integrable (fun ω => ∑ i ∈ I,
      X i ω ^ 2 * (↑(min (t i) T) - ↑(min (s i) T))) P :=
    integrable_finsetSum _ fun i hi => (hXi i hi).integrable_sq.mul_const _
  refine (ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le r)
    (hW.memLp_sum_mul_sub_min I hst hX hXi T).integrable_sq
    (fun _ _ _ => integrable_condExp.integrableOn) (fun A hA _ => ?_)
    stronglyMeasurable_condExp.aestronglyMeasurable).symm
  rw [setIntegral_condExp (ℱ.le r) henergy hA,
    hW.setIntegral_sq_sum_mul_sub_min hst hdisj hX (fun i hi => (hXi i hi).restrict A)
      (fun i hi => ℱ.mono (hrs i hi) A hA) T,
    integral_finsetSum _ (fun i hi => ((hXi i hi).integrable_sq.mul_const _).integrableOn)]
  exact sum_congr rfl fun i _ => integral_mul_const _ _

/-- For any process `I` agreeing almost surely at `s` and `t` (`s ≤ t`) with the predictable `L²`
integral of a `BrownianIntegrable` integrand `H`, the set integral of `(I t - I s)^2` over any
`ℱ s`-measurable event `A` equals the expected square energy of `H` over `(s, t] × A`.
No adaptedness assumption on `I` is needed. -/
theorem setIntegral_sq_sub_of_ae_eq_l2Integral (hW : IsFilteredPreBrownianReal ℱ W P)
    {H I : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H)
    {s t : ℝ≥0} (hst : s ≤ t)
    (hs : I s =ᵐ[P] hW.l2Integral s (hH.toPredictableLp s))
    (ht : I t =ᵐ[P] hW.l2Integral t (hH.toPredictableLp t))
    {A : Set Ω} (hA : MeasurableSet[ℱ s] A) :
    ∫ ω in A, (I t ω - I s ω) ^ 2 ∂P =
      ∫ p in Ioc s t ×ˢ A, H p.1 p.2 ^ 2 ∂(timeMeasure t).prod P := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  have hrect := hW.coeFn_l2Integral_indicator_Ioc_prod_eq_indicator_sub hH hst le_rfl hA
  have hsq : (fun ω ↦ A.indicator (fun ω ↦ (I t ω - I s ω) ^ 2) ω) =ᵐ[P]
      fun ω ↦ hW.l2Integral t ((hH.indicator_Ioc_prod s t hA).toPredictableLp t) ω ^ 2 := by
    filter_upwards [hrect, hs, ht] with ω hω hωs hωt
    rw [hω]; by_cases hωA : ω ∈ A <;> simp [hωA, hωs, hωt]
  have hint := hW.integral_sq_l2Integral_toPredictableLp (hH.indicator_Ioc_prod s t hA) t
  rw [← integral_indicator (ℱ.le s A hA), integral_congr_ae hsq, hint,
    ← integral_indicator ((measurableSet_Ioc (a := s) (b := t)).prod (ℱ.le s A hA))]
  refine integral_congr_ae (.of_forall fun ⟨u, ω⟩ ↦ ?_)
  by_cases hu : u ∈ Ioc s t <;> by_cases hω : ω ∈ A <;> simp [hu, hω]

/-- Conditional second moment of increments of a modification `I` of the predictable `L²` Brownian
integral: for `s ≤ t`, `E[(I t - I s)^2 | ℱ s] = E[∫_(s, t] H u ^ 2 du | ℱ s]` almost surely.
No adaptedness assumption on `I` is needed. -/
theorem condExp_sq_sub_of_ae_eq_l2Integral (hW : IsFilteredPreBrownianReal ℱ W P)
    {H I : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H)
    {s t : ℝ≥0} (hst : s ≤ t)
    (hs : I s =ᵐ[P] hW.l2Integral s (hH.toPredictableLp s))
    (ht : I t =ᵐ[P] hW.l2Integral t (hH.toPredictableLp t)) :
    P[fun ω ↦ (I t ω - I s ω) ^ 2 | ℱ s] =ᵐ[P]
      P[fun ω ↦ ∫ u in Ioc s t, H u ω ^ 2 ∂timeMeasure t | ℱ s] := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  have hI_mem : MemLp (fun ω ↦ I t ω - I s ω) 2 P :=
    (hW.memLp_of_ae_eq_l2Integral hH ht).sub (hW.memLp_of_ae_eq_l2Integral hH hs)
  have hprod_int : Integrable (fun p : ℝ≥0 × Ω ↦ H p.1 p.2 ^ 2)
      (((timeMeasure t).restrict (Ioc s t)).prod P) :=
    (hH.memLp_timeMeasure t).integrable_sq.mono_measure
      (Measure.prod_mono Measure.restrict_le_self le_rfl)
  refine (ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le s)
    hI_mem.integrable_sq (fun _ _ _ ↦ integrable_condExp.integrableOn)
    (fun A hA _ ↦ ?_) stronglyMeasurable_condExp.aestronglyMeasurable).symm
  have hA_int : Integrable (fun p : ℝ≥0 × Ω ↦ H p.1 p.2 ^ 2)
      (((timeMeasure t).restrict (Ioc s t)).prod (P.restrict A)) :=
    hprod_int.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
  rw [setIntegral_condExp (ℱ.le s) hprod_int.integral_prod_right hA,
    hW.setIntegral_sq_sub_of_ae_eq_l2Integral hH hst hs ht hA,
    ← Measure.prod_restrict (Ioc s t) A, integral_prod_symm _ hA_int]

end TauCeti.Probability.IsFilteredPreBrownianReal
