/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Connected.HausdorffMeasure
public import TauCeti.Analysis.ConstantSpeed
import Mathlib.Order.Interval.Set.Union

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

For an arbitrary continuous curve, the variation is the Hausdorff integral of the extended
cardinality of the fibers: the Banach indicatrix formula, which counts repeated traversals. A
partition argument bounds the variation by the integral. Conversely, along uniform partitions the
number of subarcs through a point eventually reaches the number of parameters over it, and each
such count has integral at most the variation, so Fatou's lemma gives the reverse bound. For a
curve injective on `(a, b)`, almost every fiber over the trace is a single point, which gives the
bound by the trace measure.

## References

* H. Federer, *Geometric Measure Theory*, Theorem 2.10.13 (the Banach indicatrix formula for
  continuous curves).
-/

public section

open Filter MeasureTheory Set
open scoped ENNReal Topology

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

/-- For a partition `u` of `[u 0, u n]` into intervals with measurable images, the raw
one-dimensional Hausdorff integral of the number of subarcs through each point is at most the
variation. Each subarc has measure at most its variation, and variation adds over the partition. -/
private theorem lintegral_sum_indicator_image_Icc_le {n : ℕ} {u : ℕ → ℝ} (hu : Monotone u)
    (hK : ∀ i < n, MeasurableSet (γ '' Icc (u i) (u (i + 1)))) :
    ∫⁻ y, ∑ i ∈ Finset.range n, (γ '' Icc (u i) (u (i + 1))).indicator 1 y ∂μH[1] ≤
      eVariationOn γ (Icc (u 0) (u n)) := by
  have hK' (i : ℕ) (hi : i ∈ Finset.range n) := hK i (Finset.mem_range.mp hi)
  calc
    _ = ∑ i ∈ Finset.range n, μH[1] (γ '' Icc (u i) (u (i + 1))) := by
      rw [lintegral_finsetSum _ fun i hi ↦ measurable_one.indicator (hK' i hi)]
      exact Finset.sum_congr rfl fun i hi ↦ lintegral_indicator_one (hK' i hi)
    _ ≤ ∑ i ∈ Finset.range n, eVariationOn γ (Icc (u i) (u (i + 1))) :=
      Finset.sum_le_sum fun i _ ↦ eVariationOn.hausdorffMeasure_image_le γ _
    _ = _ := eVariationOn.sum' γ hu

omit [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] in
/-- Let `u` be a partition of `[u 0, u (n + 1)]` whose intervals have length at most `δ`. A finite
set of parameters over `y` whose distinct points are more than `δ` apart has at most as many points
as there are subarcs through `y`: each parameter lies in some partition interval, and no interval
holds two of them. -/
private theorem card_le_sum_indicator_image_Icc {n : ℕ} {u : ℕ → ℝ} (hu : Monotone u) {δ : ℝ}
    (hmesh : ∀ i, u (i + 1) - u i ≤ δ) {y : X} {F : Finset ℝ}
    (hF : (F : Set ℝ) ⊆ Icc (u 0) (u (n + 1)) ∩ γ ⁻¹' {y})
    (hsep : ∀ s ∈ F, ∀ t ∈ F, s ≠ t → δ < |s - t|) :
    (F.card : ℝ≥0∞) ≤ ∑ i ∈ Finset.range (n + 1), (γ '' Icc (u i) (u (i + 1))).indicator 1 y := by
  classical
  have hcov (t : ℝ) (ht : t ∈ Icc (u 0) (u (n + 1))) : ∃ i < n + 1, t ∈ Icc (u i) (u (i + 1)) := by
    rcases ht.1.eq_or_lt with rfl | h
    · exact ⟨0, n.succ_pos, le_rfl, hu (Nat.zero_le 1)⟩
    · obtain ⟨i, hi, hti⟩ := mem_iUnion₂.mp (Ioc_subset_biUnion_Ioc (n + 1) u ⟨h, ht.2⟩)
      exact ⟨i, Finset.mem_range.mp hi, Ioc_subset_Icc_self hti⟩
  choose! idx hidx hmem using hcov
  calc
    (F.card : ℝ≥0∞) ≤
        ((Finset.range (n + 1)).filter fun i ↦ y ∈ γ '' Icc (u i) (u (i + 1))).card := by
      refine Nat.cast_le.mpr (Finset.card_le_card_of_injOn idx (fun t ht ↦ ?_) ?_)
      · exact Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (hidx t (hF ht).1), t, hmem t (hF ht).1, (hF ht).2⟩
      · intro s hs t ht hst
        by_contra hne
        have hs' := hmem s (hF hs).1
        have ht' := hmem t (hF ht).1
        rw [hst] at hs'
        refine (hsep s hs t ht hne).not_ge ((abs_sub_le_iff.mpr ⟨?_, ?_⟩).trans (hmesh (idx t)))
        · linarith [hs'.2, ht'.1]
        · linarith [hs'.1, ht'.2]
    _ = _ := by simp [Set.indicator_apply, Finset.sum_boole]

omit [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] in
/-- Along partitions of `[a, b]` into `n + 1` intervals whose meshes tend to zero, the number of
parameters over `y`, finite or not, is at most the lower limit of the number of subarcs through
`y`: a finite set of parameters is eventually separated by the mesh. -/
private theorem encard_le_liminf_sum_indicator_image_Icc {u : ℕ → ℕ → ℝ}
    (hu : ∀ n, Monotone (u n)) (hu0 : ∀ n, u n 0 = a) (hun : ∀ n, u n (n + 1) = b)
    {δ : ℕ → ℝ} (hmesh : ∀ n i, u n (i + 1) - u n i ≤ δ n) (hδ : Tendsto δ atTop (𝓝 0))
    (y : X) :
    ((Icc a b ∩ γ ⁻¹' {y}).encard : ℝ≥0∞) ≤ liminf (fun n ↦
      ∑ i ∈ Finset.range (n + 1), (γ '' Icc (u n i) (u n (i + 1))).indicator 1 y) atTop := by
  have hfin (F : Finset ℝ) (hF : (F : Set ℝ) ⊆ Icc a b ∩ γ ⁻¹' {y}) : (F.card : ℝ≥0∞) ≤
      liminf (fun n ↦ ∑ i ∈ Finset.range (n + 1),
        (γ '' Icc (u n i) (u n (i + 1))).indicator 1 y) atTop := by
    have hsep : ∀ᶠ n in atTop, ∀ s ∈ F, ∀ t ∈ F, s ≠ t → δ n < |s - t| := by
      simp only [Finset.eventually_all]
      intro s _ t _
      by_cases hst : s = t
      · exact .of_forall fun _ h ↦ absurd hst h
      · exact (hδ.eventually (gt_mem_nhds (abs_pos.mpr (sub_ne_zero.mpr hst)))).mono
          fun _ h _ ↦ h
    refine le_liminf_of_le (by isBoundedDefault) (hsep.mono fun n hn ↦ ?_)
    exact card_le_sum_indicator_image_Icc (hu n) (hmesh n) (by rwa [hu0, hun]) hn
  rcases (Icc a b ∩ γ ⁻¹' {y}).finite_or_infinite with hS | hS
  · simpa [hS.encard_eq_coe_toFinset_card] using hfin hS.toFinset (by simp)
  · rw [hS.encard_eq, ENat.toENNReal_top, top_le_iff]
    refine ENNReal.eq_top_of_forall_nnreal_le fun r ↦ ?_
    obtain ⟨k, hk⟩ := exists_nat_ge (r : ℝ)
    obtain ⟨F, hF, rfl⟩ := hS.exists_subset_card_eq k
    exact le_trans (by exact_mod_cast hk) (hfin F hF)

/-- **Banach indicatrix formula.** The variation of a continuous curve on `[a, b]` is the raw
one-dimensional Hausdorff integral of the extended cardinality of its fibers. No Lipschitz or
bounded-variation hypothesis is needed: both sides are infinite together. Pauses and repeated
traversals are allowed, and infinite fibers have infinite multiplicity. -/
theorem eVariationOn_eq_lintegral_encard (hγ : ContinuousOn γ (Icc a b)) :
    eVariationOn γ (Icc a b) = ∫⁻ y, ((Icc a b ∩ γ ⁻¹' {y}).encard : ℝ≥0∞) ∂μH[1] := by
  refine le_antisymm hγ.eVariationOn_le_lintegral_encard ?_
  rcases lt_or_ge b a with hab | hab
  · simp [Icc_eq_empty_of_lt hab]
  -- Count the subarcs through each point for the uniform partitions into `n + 1` intervals; the
  -- count has integral at most the variation, and Fatou's lemma passes to the lower limit.
  let δ (n : ℕ) : ℝ := (b - a) / (n + 1 : ℕ)
  let u (n i : ℕ) : ℝ := a + i * δ n
  have hu (n : ℕ) : Monotone (u n) :=
    (Nat.mono_cast.mul_const (div_nonneg (sub_nonneg.mpr hab) (n + 1).cast_nonneg)).const_add a
  have hu0 (n : ℕ) : u n 0 = a := by simp [u]
  have hun (n : ℕ) : u n (n + 1) = b := by simp only [u, δ]; field_simp; ring
  have hmesh (n i : ℕ) : u n (i + 1) - u n i ≤ δ n := by simp only [u]; push_cast; linarith
  have hδ : Tendsto δ atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat (b - a)).comp (tendsto_add_atTop_nat 1)
  have hK (n i : ℕ) (hi : i < n + 1) : MeasurableSet (γ '' Icc (u n i) (u n (i + 1))) :=
    (isCompact_Icc.image_of_continuousOn (hγ.mono (Icc_subset_Icc
      ((hu0 n).symm.le.trans (hu n i.zero_le)) ((hu n hi).trans (hun n).le)))).measurableSet
  let N (n : ℕ) (y : X) : ℝ≥0∞ :=
    ∑ i ∈ Finset.range (n + 1), (γ '' Icc (u n i) (u n (i + 1))).indicator 1 y
  have hN (n : ℕ) : Measurable (N n) :=
    Finset.measurable_sum _ fun i hi ↦ measurable_one.indicator (hK n i (Finset.mem_range.mp hi))
  calc
    _ ≤ ∫⁻ y, liminf (N · y) atTop ∂μH[1] :=
      lintegral_mono (encard_le_liminf_sum_indicator_image_Icc hu hu0 hun hmesh hδ)
    _ ≤ liminf (fun n ↦ ∫⁻ y, N n y ∂μH[1]) atTop := lintegral_liminf_le hN
    _ ≤ _ := liminf_le_of_frequently_le' <| .of_forall fun n ↦ by
      simpa only [hu0, hun] using lintegral_sum_indicator_image_Icc_le (hu n) (hK n)

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
