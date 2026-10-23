/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ConstantSpeed
public import TauCeti.Topology.Connected.HausdorffMeasure

/-!
# Hausdorff measure and the length of curves

A continuous curve on a compact real interval `[a, b]` that is injective on the open interval
`(a, b)` has variation equal to the one-dimensional Hausdorff measure of its trace. This covers
injective arcs and simple closed curves, where `γ a = γ b`; the endpoints may also coincide
with other points of the trace. In particular, finite trace measure is equivalent to bounded
variation, without any Lipschitz or bounded-variation hypothesis on the parametrization.
The results include empty and singleton parameter intervals.

Both raw Hausdorff measure `μH[1]` and Euclidean-normalized measure `μHE[1]` are supported.
These results let one compute the length of such a curve from its trace using either convention.

For an arbitrary continuous curve, a partition argument bounds the variation by the Hausdorff
integral of the extended cardinality of the fibers. This is the lower half of the Banach
indicatrix formula, which counts repeated traversals. For a curve injective on `(a, b)`, almost
every fiber over the trace is a single point, which gives the bound by the trace measure.

## References

* H. Federer, *Geometric Measure Theory*, Theorem 2.10.13 (the Banach indicatrix formula for
  continuous curves).
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace ContinuousOn

variable {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {γ : ℝ → X} {a b : ℝ}

omit [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] in
/-- Given a partition of `[a, b]` and a point `y` that is not a value at a partition point, the
number of partition subarcs through `y` is at most the number of parameters over `y`. Each such
subarc meets the fiber in its open parameter interval, and these intervals are disjoint. -/
private theorem sum_indicator_image_Icc_le_encard {n : ℕ} {u : ℕ → ℝ}
    (hu : StrictMonoOn u (Iic n)) (hus : ∀ i ∈ Iic n, u i ∈ Icc a b) {y : X}
    (hy : y ∉ (fun i ↦ γ (u i)) '' Iic n) :
    ∑ i ∈ Finset.range n, (γ '' Icc (u i) (u (i + 1))).indicator 1 y ≤
      ((Icc a b ∩ γ ⁻¹' {y}).encard : ℝ≥0∞) := by
  classical
  let I := (Finset.range n).filter fun i ↦ y ∈ γ '' Icc (u i) (u (i + 1))
  have hmem (i : ℕ) : i ∈ I ↔ i < n ∧ y ∈ γ '' Icc (u i) (u (i + 1)) := by
    simp [I]
  have hsum : ∑ i ∈ Finset.range n, (γ '' Icc (u i) (u (i + 1))).indicator 1 y =
      ((I : Set ℕ).encard : ℝ≥0∞) := by
    rw [Set.encard_coe_eq_coe_finsetCard]
    simp only [I, Set.indicator_apply, Pi.one_apply, Finset.sum_boole]
    norm_cast
  have hpt (i : ℕ) (hi : i ∈ I) : ∃ t ∈ Ioo (u i) (u (i + 1)), γ t = y := by
    obtain ⟨hi, t, ht, rfl⟩ := (hmem i).mp hi
    refine ⟨t, ⟨ht.1.lt_of_ne ?_, ht.2.lt_of_ne ?_⟩, rfl⟩
    · rintro rfl
      exact hy ⟨i, by simp; omega, rfl⟩
    · rintro rfl
      exact hy ⟨i + 1, by simp; omega, rfl⟩
  choose! t ht hty using hpt
  have hlt (i : ℕ) (hi : i ∈ I) (j : ℕ) (hj : j ∈ I) (hij : i < j) : t i < t j := by
    have hj' := ((hmem j).mp hj).1
    calc
      t i < u (i + 1) := (ht i hi).2
      _ ≤ u j := hu.monotoneOn (by simp; omega) (by simp; omega) (by omega)
      _ < t j := (ht j hj).1
  rw [hsum, ENat.toENNReal_le]
  refine encard_le_encard_of_injOn (f := t) (fun i hi ↦ ?_) fun i hi j hj hij ↦ ?_
  · have hi' := ((hmem i).mp hi).1
    exact ⟨Icc_subset_Icc (hus i (by simp; omega)).1 (hus (i + 1) (by simp; omega)).2
      (Ioo_subset_Icc_self (ht i hi)), hty i hi⟩
  · by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact (hlt i hi j hj h).ne hij
    · exact (hlt j hj i hi h).ne hij.symm

/-- **Banach indicatrix inequality.** The variation of a continuous curve on `[a, b]` is at most
the raw one-dimensional Hausdorff integral of the extended cardinality of its fibers. No
injectivity or rectifiability hypothesis is needed; repeated traversals are counted by the
fiber cardinality. -/
theorem eVariationOn_le_lintegral_encard (hγ : ContinuousOn γ (Icc a b)) :
    eVariationOn γ (Icc a b) ≤ ∫⁻ y, ((Icc a b ∩ γ ⁻¹' {y}).encard : ℝ≥0∞) ∂μH[1] := by
  rw [eVariationOn.eVariationOn_eq_strictMonoOn]
  refine iSup_le ?_
  rintro ⟨n, u, hu, hus⟩
  have hsub (i : ℕ) (hi : i < n) : Icc (u i) (u (i + 1)) ⊆ Icc a b :=
    Icc_subset_Icc (hus i (by simp; omega)).1 (hus (i + 1) (by simp; omega)).2
  have hle (i : ℕ) (hi : i < n) : u i ≤ u (i + 1) :=
    (hu (by simp; omega) (by simp; omega) (by omega)).le
  have hK (i : ℕ) (hi : i < n) : MeasurableSet (γ '' Icc (u i) (u (i + 1))) :=
    (isCompact_Icc.image_of_continuousOn (hγ.mono (hsub i hi))).measurableSet
  -- The finitely many values at partition points have zero Hausdorff length.
  have hcount : ∀ᵐ y ∂μH[1], ∑ i ∈ Finset.range n, (γ '' Icc (u i) (u (i + 1))).indicator 1 y ≤
      ((Icc a b ∩ γ ⁻¹' {y}).encard : ℝ≥0∞) := by
    have := Measure.nullSingletonClass_hausdorff X (show (0 : ℝ) < 1 by norm_num)
    have hF : μH[1] ((fun i ↦ γ (u i)) '' Iic n) = 0 := ((finite_Iic n).image _).measure_zero _
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hF] with y hy
    exact sum_indicator_image_Icc_le_encard hu hus hy
  -- Bound each partition chord by its subarc measure, then count subarcs through each point.
  calc
    (∑ i ∈ Finset.range n, edist (γ (u (i + 1))) (γ (u i))) ≤
        ∑ i ∈ Finset.range n, μH[1] (γ '' Icc (u i) (u (i + 1))) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' := Finset.mem_range.mp hi
      exact (isPreconnected_Icc.image γ (hγ.mono (hsub i hi'))).edist_le_hausdorffMeasure
          (mem_image_of_mem γ (right_mem_Icc.mpr (hle i hi')))
          (mem_image_of_mem γ (left_mem_Icc.mpr (hle i hi')))
    _ = ∫⁻ y, ∑ i ∈ Finset.range n, (γ '' Icc (u i) (u (i + 1))).indicator 1 y ∂μH[1] := by
      rw [lintegral_finsetSum]
      · refine Finset.sum_congr rfl fun i hi ↦ ?_
        rw [lintegral_indicator_one (hK i (Finset.mem_range.mp hi))]
      · exact fun i hi ↦ measurable_const.indicator (hK i (Finset.mem_range.mp hi))
    _ ≤ _ := lintegral_mono_ae hcount

/-- The variation of a continuous curve on `[a, b]` that is injective on `(a, b)`, such as an
injective arc or a simple closed curve, is at most the raw one-dimensional Hausdorff measure of
its trace. No rectifiability hypothesis on the parametrization is needed. -/
theorem eVariationOn_le_hausdorffMeasure_image (hγ : ContinuousOn γ (Icc a b))
    (hinj : InjOn γ (Ioo a b)) : eVariationOn γ (Icc a b) ≤ μH[1] (γ '' Icc a b) := by
  have := Measure.nullSingletonClass_hausdorff X (show (0 : ℝ) < 1 by norm_num)
  -- Away from the two endpoint values, each fiber over the trace has at most one point.
  have hfib : ∀ᵐ y ∂μH[1],
      ((Icc a b ∩ γ ⁻¹' {y}).encard : ℝ≥0∞) ≤ (γ '' Icc a b).indicator 1 y := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp ((toFinite {γ a, γ b}).measure_zero μH[1])]
      with y hy
    by_cases hyI : y ∈ γ '' Icc a b
    · have hIoo (t : ℝ) (ht : t ∈ Icc a b ∩ γ ⁻¹' {y}) : t ∈ Ioo a b := by
        have hty : γ t = y := ht.2
        refine ⟨ht.1.1.lt_of_ne ?_, ht.1.2.lt_of_ne ?_⟩ <;> rintro rfl <;> simp [hty] at hy
      rw [indicator_of_mem hyI, Pi.one_apply, ← ENat.toENNReal_one, ENat.toENNReal_le,
        encard_le_one_iff]
      exact fun s t hs ht ↦ hinj (hIoo s hs) (hIoo t ht) (hs.2.trans ht.2.symm)
    · have hempty : Icc a b ∩ γ ⁻¹' {y} = ∅ :=
        eq_empty_of_forall_notMem fun t ht ↦ hyI ⟨t, ht.1, ht.2⟩
      simp [indicator_of_notMem hyI, hempty]
  calc
    eVariationOn γ (Icc a b) ≤ ∫⁻ y, ((Icc a b ∩ γ ⁻¹' {y}).encard : ℝ≥0∞) ∂μH[1] :=
      hγ.eVariationOn_le_lintegral_encard
    _ ≤ ∫⁻ y, (γ '' Icc a b).indicator 1 y ∂μH[1] := lintegral_mono_ae hfib
    _ = μH[1] (γ '' Icc a b) :=
      lintegral_indicator_one (isCompact_Icc.image_of_continuousOn hγ).measurableSet

/-- The variation of a continuous curve on `[a, b]` that is injective on `(a, b)`, such as an
injective arc or a simple closed curve, is at most the Euclidean-normalized one-dimensional
Hausdorff measure of its trace. This also covers empty and singleton intervals. -/
theorem eVariationOn_le_euclideanHausdorffMeasure_image (hγ : ContinuousOn γ (Icc a b))
    (hinj : InjOn γ (Ioo a b)) : eVariationOn γ (Icc a b) ≤ μHE[1] (γ '' Icc a b) := by
  rw [Measure.euclideanHausdorffMeasure_one]
  exact hγ.eVariationOn_le_hausdorffMeasure_image hinj

/-- A continuous curve on `[a, b]` that is injective on `(a, b)`, such as an injective arc or
a simple closed curve, has variation equal to the raw one-dimensional Hausdorff measure of its
trace. The equality also holds for infinite length and for empty or singleton intervals. -/
theorem eVariationOn_eq_hausdorffMeasure_image (hγ : ContinuousOn γ (Icc a b))
    (hinj : InjOn γ (Ioo a b)) : eVariationOn γ (Icc a b) = μH[1] (γ '' Icc a b) :=
  le_antisymm (hγ.eVariationOn_le_hausdorffMeasure_image hinj)
    (eVariationOn.hausdorffMeasure_image_le γ (Icc a b))

/-- A continuous curve on `[a, b]` that is injective on `(a, b)`, such as an injective arc or
a simple closed curve, has variation equal to the Euclidean-normalized one-dimensional
Hausdorff measure of its trace, including when the length is infinite. -/
theorem eVariationOn_eq_euclideanHausdorffMeasure_image (hγ : ContinuousOn γ (Icc a b))
    (hinj : InjOn γ (Ioo a b)) : eVariationOn γ (Icc a b) = μHE[1] (γ '' Icc a b) := by
  rw [Measure.euclideanHausdorffMeasure_one]
  exact hγ.eVariationOn_eq_hausdorffMeasure_image hinj

/-- Finite raw Hausdorff length of the trace is equivalent to bounded variation for a continuous
curve injective on the open interval. No Lipschitz hypothesis on its parametrization is needed. -/
theorem boundedVariationOn_iff_hausdorffMeasure_image_lt_top
    (hγ : ContinuousOn γ (Icc a b)) (hinj : InjOn γ (Ioo a b)) :
    BoundedVariationOn γ (Icc a b) ↔ μH[1] (γ '' Icc a b) < ∞ := by
  rw [BoundedVariationOn, hγ.eVariationOn_eq_hausdorffMeasure_image hinj, lt_top_iff_ne_top]

/-- Finite Euclidean Hausdorff length of the trace is equivalent to bounded variation for a
continuous curve injective on the open interval, including injective arcs and simple closed
curves. -/
theorem boundedVariationOn_iff_euclideanHausdorffMeasure_image_lt_top
    (hγ : ContinuousOn γ (Icc a b)) (hinj : InjOn γ (Ioo a b)) :
    BoundedVariationOn γ (Icc a b) ↔ μHE[1] (γ '' Icc a b) < ∞ := by
  rw [BoundedVariationOn, hγ.eVariationOn_eq_euclideanHausdorffMeasure_image hinj,
    lt_top_iff_ne_top]

end ContinuousOn
