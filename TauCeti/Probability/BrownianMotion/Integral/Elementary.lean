/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Filtered
import TauCeti.MeasureTheory.Function.L2Space
import TauCeti.Probability.Independence.Integration

/-!
# The isometry for elementary Brownian integrals

For a Brownian motion relative to a filtration, an elementary integral on a deterministic
nondecreasing grid is the sum `∑ i < n, ξ i * (W (τ (i+1)) - W (τ i))`, where the height
`ξ i` is measurable at the left endpoint `τ i`. This file proves that these sums are square
integrable and that their second moments equal
`∑ i < n, E[(ξ i)²] * (τ (i+1) - τ i)`.

The heights need only be square integrable, not bounded or mutually independent. Distinct
weighted increments are orthogonal because the later Brownian increment is centered and
independent of the information at its left endpoint. Empty sums and repeated grid times
are allowed. Only finite-dimensional Brownian laws, adaptedness to the filtration, and
filtration-relative increment independence are used; neither path continuity nor usual
conditions are needed.

The isometry also holds for finite families of pairwise chronologically disjoint intervals,
without an order on their index type. Its arbitrary-observation-time version truncates both
endpoints at `T`, while keeping each height measurable at its original left endpoint. Intervals
not yet started contribute zero, so future heights need not be measurable at `T`.

These are the elementary isometry and orthogonality identities used to extend the Brownian
integral by completion and compute its second moment at each observation time. No integral for
general predictable processes is constructed here.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.
-/

public section

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal ENNReal

namespace TauCeti.Probability.IsFilteredPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {ξ η : Ω → ℝ}
  {s t u v : ℝ≥0}

/-- A square-integrable height known at the left endpoint times a Brownian increment
is square integrable. -/
theorem memLp_mul_sub (hW : IsFilteredPreBrownianReal ℱ W P) (hst : s ≤ t)
    (hξ : StronglyMeasurable[ℱ s] ξ) (hξ₂ : MemLp ξ 2 P) :
    MemLp (fun ω => ξ ω * (W t ω - W s ω)) 2 P := by
  have hΔ : MemLp (W t - W s) 2 P :=
    (hW.hasLaw_sub_of_le hst).memLp (memLp_id_gaussianReal 2)
  exact (hW.indepFun_sub hst hξ.measurable).memLp_two_mul hξ₂ hΔ

/-- A measurable height known at the left endpoint times a Brownian increment has mean zero.
No integrability is required: the Bochner integral is zero also in the nonintegrable case. -/
theorem integral_mul_sub_eq_zero (hW : IsFilteredPreBrownianReal ℱ W P) (hst : s ≤ t)
    (hξ : StronglyMeasurable[ℱ s] ξ) :
    ∫ ω, ξ ω * (W t ω - W s ω) ∂P = 0 := by
  have h := (hW.indepFun_sub hst hξ.measurable).integral_fun_mul_eq_mul_integral
    (hξ.mono (ℱ.le s)).aestronglyMeasurable
    (hW.adapted.measurable.sub hW.adapted.measurable).aestronglyMeasurable
  have hmean : ∫ ω, W t ω - W s ω ∂P = 0 := by
    simpa only [Pi.sub_apply] using
      (hW.hasLaw_sub_of_le hst).integral_eq.trans integral_id_gaussianReal
  simpa only [Pi.sub_apply, hmean, mul_zero] using h

/-- The one-interval Brownian second-moment identity for a measurable left-endpoint height.
No integrability is required; nonintegrable squares have Bochner integral zero. -/
theorem integral_sq_mul_sub (hW : IsFilteredPreBrownianReal ℱ W P) (hst : s ≤ t)
    (hξ : StronglyMeasurable[ℱ s] ξ) :
    ∫ ω, (ξ ω * (W t ω - W s ω)) ^ 2 ∂P =
      (∫ ω, ξ ω ^ 2 ∂P) * ((t : ℝ) - s) := by
  have hΔ := hW.toIsPreBrownianReal.integral_sq_sub_of_le hst
  simp_rw [mul_pow]
  have h := ((hW.indepFun_sub hst hξ.measurable).comp (measurable_id.pow_const 2)
    (measurable_id.pow_const 2)).integral_fun_mul_eq_mul_integral
      ((hξ.mono (ℱ.le s)).measurable.pow_const 2).aestronglyMeasurable
      ((hW.adapted.measurable.sub hW.adapted.measurable).pow_const 2).aestronglyMeasurable
  simpa only [Function.comp_apply, id_eq, Pi.sub_apply, hΔ] using h

/-- The product of weighted Brownian increments on ordered disjoint intervals has integral zero.
The heights need only be measurable at their respective left endpoints; in the square-integrable
case this is orthogonality in `L²`. -/
theorem integral_mul_sub_mul_mul_sub_eq_zero (hW : IsFilteredPreBrownianReal ℱ W P)
    (huv : u ≤ v) (hvs : v ≤ s) (hst : s ≤ t)
    (hξ : StronglyMeasurable[ℱ u] ξ) (hη : StronglyMeasurable[ℱ s] η) :
    ∫ ω, (ξ ω * (W v ω - W u ω)) * (η ω * (W t ω - W s ω)) ∂P = 0 := by
  have hknown : StronglyMeasurable[ℱ s] (fun ω => (ξ ω * (W v ω - W u ω)) * η ω) :=
    (((hξ.mono (ℱ.mono (huv.trans hvs))).mul
      ((hW.adapted.stronglyAdapted.stronglyMeasurable_le hvs).sub
        (hW.adapted.stronglyAdapted.stronglyMeasurable_le (huv.trans hvs)))).mul hη)
  simpa only [mul_assoc] using hW.integral_mul_sub_eq_zero hst hknown

/-- A finite sum of weighted Brownian increments with square-integrable left-endpoint
heights lies in `L²`. No disjointness of the intervals is required. -/
theorem memLp_sum_mul_sub_of_le (hW : IsFilteredPreBrownianReal ℱ W P)
    {ι : Type*} (I : Finset ι) {s t : ι → ℝ≥0} {X : ι → Ω → ℝ}
    (hst : ∀ i ∈ I, s i ≤ t i)
    (hX : ∀ i ∈ I, StronglyMeasurable[ℱ (s i)] (X i))
    (hXi : ∀ i ∈ I, MemLp (X i) 2 P) :
    MemLp (fun ω => ∑ i ∈ I, X i ω * (W (t i) ω - W (s i) ω)) 2 P :=
  memLp_finsetSum _ fun i hi => hW.memLp_mul_sub (hst i hi) (hX i hi) (hXi i hi)

/-- **The elementary Brownian isometry for disjoint interval families.** The second moment
of a finite sum of weighted increments equals the sum of the expected squared heights times
the interval lengths. The intervals are pairwise chronologically disjoint, but their index type
need not be ordered. Heights are known at their own left endpoints and belong to `L²`;
no independence between heights is assumed. Empty families and zero-length intervals are allowed. -/
theorem integral_sq_sum_mul_sub_of_pairwise_disjoint (hW : IsFilteredPreBrownianReal ℱ W P)
    {ι : Type*} (I : Finset ι) {s t : ι → ℝ≥0} {X : ι → Ω → ℝ}
    (hst : ∀ i ∈ I, s i ≤ t i)
    (hdisj : (I : Set ι).Pairwise fun i j => t i ≤ s j ∨ t j ≤ s i)
    (hX : ∀ i ∈ I, StronglyMeasurable[ℱ (s i)] (X i))
    (hXi : ∀ i ∈ I, MemLp (X i) 2 P) :
    ∫ ω, (∑ i ∈ I, X i ω * (W (t i) ω - W (s i) ω)) ^ 2 ∂P =
      ∑ i ∈ I, (∫ ω, X i ω ^ 2 ∂P) * (↑(t i) - ↑(s i)) := by
  let U (i : ι) (ω : Ω) := X i ω * (W (t i) ω - W (s i) ω)
  have hU i (hi : i ∈ I) : MemLp (U i) 2 P :=
    hW.memLp_mul_sub (hst i hi) (hX i hi) (hXi i hi)
  have hcross i (hi : i ∈ I) j (hj : j ∈ I) (hij : i ≠ j) :
      ∫ ω, U i ω * U j ω ∂P = 0 := by
    rcases hdisj hi hj hij with hij | hji
    · exact hW.integral_mul_sub_mul_mul_sub_eq_zero (hst i hi) hij
        (hst j hj) (hX i hi) (hX j hj)
    · simpa only [mul_comm] using
        hW.integral_mul_sub_mul_mul_sub_eq_zero (hst j hj) hji
          (hst i hi) (hX j hj) (hX i hi)
  rw [integral_sq_sum_of_pairwise_integral_mul_eq_zero hU hcross]
  exact sum_congr rfl fun i hi => hW.integral_sq_mul_sub (hst i hi) (hX i hi)

variable {τ : ℕ → ℝ≥0} {n : ℕ} {a : ℕ → Ω → ℝ}

/-- An elementary Brownian integral with square-integrable predictable heights lies in `L²`.
Grid monotonicity is required only through its last endpoint. -/
theorem memLp_sum_mul_sub (hW : IsFilteredPreBrownianReal ℱ W P)
    (hτ : MonotoneOn τ (Set.Iic n))
    (ha : ∀ i < n, StronglyMeasurable[ℱ (τ i)] (a i))
    (ha₂ : ∀ i < n, MemLp (a i) 2 P) :
    MemLp (fun ω => ∑ i ∈ range n, a i ω * (W (τ (i + 1)) ω - W (τ i) ω)) 2 P := by
  exact hW.memLp_sum_mul_sub_of_le (range n)
    (fun i hi => hτ (Set.mem_Iic.mpr (mem_range.mp hi).le)
      (Set.mem_Iic.mpr (Nat.succ_le_of_lt (mem_range.mp hi))) (Nat.le_succ i))
    (fun i hi => ha i (mem_range.mp hi)) (fun i hi => ha₂ i (mem_range.mp hi))

/-- **The elementary Brownian isometry.** The second moment of a finite predictable
increment sum is the sum of the expected squared heights times the interval lengths.
No independence between the heights and no strictness of the grid is assumed. -/
theorem integral_sq_sum_mul_sub (hW : IsFilteredPreBrownianReal ℱ W P)
    (hτ : MonotoneOn τ (Set.Iic n))
    (ha : ∀ i < n, StronglyMeasurable[ℱ (τ i)] (a i))
    (ha₂ : ∀ i < n, MemLp (a i) 2 P) :
    ∫ ω, (∑ i ∈ range n, a i ω * (W (τ (i + 1)) ω - W (τ i) ω)) ^ 2 ∂P =
      ∑ i ∈ range n, (∫ ω, a i ω ^ 2 ∂P) * ((τ (i + 1) : ℝ) - τ i) := by
  apply hW.integral_sq_sum_mul_sub_of_pairwise_disjoint (range n)
    (fun i hi => hτ (by simpa using (mem_range.mp hi).le)
      (by simpa using Nat.succ_le_of_lt (mem_range.mp hi)) (Nat.le_succ i))
    (hX := fun i hi => ha i (mem_range.mp hi)) (hXi := fun i hi => ha₂ i (mem_range.mp hi))
  intro i hi j hj hij
  rcases hij.lt_or_gt with hij | hji
  · exact Or.inl (hτ (by simpa using Nat.succ_le_of_lt (mem_range.mp hi))
      (by simpa using (mem_range.mp hj).le) (Nat.succ_le_of_lt hij))
  · exact Or.inr (hτ (by simpa using Nat.succ_le_of_lt (mem_range.mp hj))
      (by simpa using (mem_range.mp hi).le) (Nat.succ_le_of_lt hji))

/-- A finite sum of weighted Brownian increments truncated at an observation time lies in
`L²`. Heights need only be measurable at their original left endpoints: intervals not yet
started contribute zero. No disjointness of the intervals is required. -/
theorem memLp_sum_mul_sub_min (hW : IsFilteredPreBrownianReal ℱ W P)
    {ι : Type*} (I : Finset ι) {s t : ι → ℝ≥0} {X : ι → Ω → ℝ}
    (hst : ∀ i ∈ I, s i ≤ t i)
    (hX : ∀ i ∈ I, StronglyMeasurable[ℱ (s i)] (X i))
    (hXi : ∀ i ∈ I, MemLp (X i) 2 P) (T : ℝ≥0) :
    MemLp (fun ω => ∑ i ∈ I,
      X i ω * (W (min (t i) T) ω - W (min (s i) T) ω)) 2 P := by
  refine memLp_finsetSum _ fun i hi => ?_
  by_cases hs : s i ≤ T
  · simpa only [min_eq_left hs] using
      hW.memLp_mul_sub (le_min (hst i hi) hs) (hX i hi) (hXi i hi)
  · have hTs : T ≤ s i := (lt_of_not_ge hs).le
    simp only [min_eq_right hTs, min_eq_right (hTs.trans (hst i hi)), sub_self, mul_zero]
    exact MemLp.zero

/-- The elementary Brownian isometry at an arbitrary observation time. Intervals after `T`
contribute zero and an interval straddling `T` contributes only its elapsed length. The
heights remain measurable at their original left endpoints; no measurability at an
earlier, truncated time is assumed. -/
theorem integral_sq_sum_mul_sub_min (hW : IsFilteredPreBrownianReal ℱ W P)
    {ι : Type*} (I : Finset ι) {s t : ι → ℝ≥0} {X : ι → Ω → ℝ}
    (hst : ∀ i ∈ I, s i ≤ t i)
    (hdisj : (I : Set ι).Pairwise fun i j => t i ≤ s j ∨ t j ≤ s i)
    (hX : ∀ i ∈ I, StronglyMeasurable[ℱ (s i)] (X i))
    (hXi : ∀ i ∈ I, MemLp (X i) 2 P) (T : ℝ≥0) :
    ∫ ω, (∑ i ∈ I, X i ω * (W (min (t i) T) ω - W (min (s i) T) ω)) ^ 2 ∂P =
      ∑ i ∈ I, (∫ ω, X i ω ^ 2 ∂P) * (↑(min (t i) T) - ↑(min (s i) T)) := by
  classical
  -- Discard intervals not yet started before applying the disjoint-family isometry
  -- integral_sq_sum_mul_sub_of_pairwise_disjoint. Their heights need not be measurable
  -- at the observation time.
  have h := hW.integral_sq_sum_mul_sub_of_pairwise_disjoint (I.filter fun i => s i < T)
    (s := s) (t := fun i => min (t i) T) (X := X)
    (fun i hi => le_min (hst i (mem_filter.mp hi).1) (mem_filter.mp hi).2.le)
    (fun i hi j hj hij => (hdisj (mem_filter.mp hi).1 (mem_filter.mp hj).1 hij).imp
      (fun hij => (min_le_left _ _).trans hij) (fun hji => (min_le_left _ _).trans hji))
    (fun i hi => hX i (mem_filter.mp hi).1)
    (fun i hi => hXi i (mem_filter.mp hi).1)
  have hfilter (c : ι → ℝ) (f : ι → ℝ≥0 → ℝ) :
      (∑ i ∈ I, c i * (f i (min (t i) T) - f i (min (s i) T))) =
        ∑ i ∈ I.filter (fun i => s i < T), c i * (f i (min (t i) T) - f i (s i)) := by
    rw [sum_filter]
    refine sum_congr rfl fun i hi => ?_
    by_cases hs : s i < T
    · simp [hs, min_eq_left hs.le]
    · have hTs : T ≤ s i := le_of_not_gt hs
      simp [hs, min_eq_right hTs, min_eq_right (hTs.trans (hst i hi))]
  have hsum (ω : Ω) := hfilter (fun i => X i ω) (fun _ r => W r ω)
  simp_rw [hsum, hfilter]
  exact h

end TauCeti.Probability.IsFilteredPreBrownianReal
