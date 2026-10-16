/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Euclidean.Volume.Measure
public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import TauCeti.Topology.Connected.HausdorffMeasure

/-!
# Hausdorff lower bounds for the length of injective curves

A continuous injective curve on a compact real interval has variation at most the
one-dimensional Hausdorff measure of its trace. In particular, finite trace measure implies
bounded variation, without any Lipschitz or bounded-variation hypothesis on the parametrization.
The same conclusions hold for a simple closed curve, represented by a map injective on the
half-open parameter interval and taking equal values at its endpoints. All results include empty
and singleton parameter intervals.

Both raw Hausdorff measure `μH[1]` and Euclidean-normalized measure `μHE[1]` are supported.
The central formal input is `IsPreconnected.edist_le_hausdorffMeasure`: apply it to the
subarcs of a partition and add their measures. Injectivity ensures that distinct subarcs
overlap only at endpoints, which have zero one-dimensional Hausdorff measure.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace ContinuousOn

variable {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {γ : ℝ → X} {a b : ℝ}

private theorem sum_edist_le_hausdorffMeasure_image (hγ : ContinuousOn γ (Icc a b))
    (hinj : InjOn γ (Icc a b)) {n : ℕ} {u : ℕ → ℝ}
    (hu : StrictMonoOn u (Iic n)) (hus : ∀ i ∈ Iic n, u i ∈ Icc a b) :
    (∑ i ∈ Finset.range n, edist (γ (u (i + 1))) (γ (u i))) ≤
      μH[1] (γ '' Icc a b) := by
  have hsub (i : ℕ) (hi : i < n) : Icc (u i) (u (i + 1)) ⊆ Icc a b :=
    Icc_subset_Icc (hus i (by simp; omega)).1 (hus (i + 1) (by simp; omega)).2
  have hle (i : ℕ) (hi : i < n) : u i ≤ u (i + 1) :=
    (hu (by simp; omega) (by simp; omega) (by omega)).le
  -- Ordered subarcs can meet only at a common endpoint, whose Hausdorff length is zero.
  have hnull (i j : ℕ) (hi : i < n) (hj : j < n) (hij : i < j) :
      AEDisjoint μH[1] (γ '' Icc (u i) (u (i + 1)))
        (γ '' Icc (u j) (u (j + 1))) := by
    have huv : u (i + 1) ≤ u j :=
      hu.monotoneOn (by simp; omega) (by simp; omega) (by omega)
    have hinter : Icc (u i) (u (i + 1)) ∩ Icc (u j) (u (j + 1)) ⊆ {u j} := by
      intro t ht
      exact mem_singleton_iff.mpr (le_antisymm (ht.1.2.trans huv) ht.2.1)
    have := Measure.nullSingletonClass_hausdorff X (show (0 : ℝ) < 1 by norm_num)
    apply measure_mono_null (t := {γ (u j)}) _ (measure_singleton _)
    rw [← hinj.image_inter (hsub i hi) (hsub j hj)]
    simpa using image_mono (f := γ) hinter
  have hdisj : (↑(Finset.range n) : Set ℕ).Pairwise
      (fun i j ↦ AEDisjoint μH[1] (γ '' Icc (u i) (u (i + 1)))
        (γ '' Icc (u j) (u (j + 1)))) := by
    intro i hi j hj hij
    rcases lt_or_gt_of_ne hij with hij | hij
    · exact hnull i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hij
    · exact (hnull j i (Finset.mem_range.mp hj) (Finset.mem_range.mp hi) hij).symm
  -- Bound each partition chord by its subarc measure, then use finite additivity.
  calc
    (∑ i ∈ Finset.range n, edist (γ (u (i + 1))) (γ (u i))) ≤
        ∑ i ∈ Finset.range n, μH[1] (γ '' Icc (u i) (u (i + 1))) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' := Finset.mem_range.mp hi
      exact (isPreconnected_Icc.image γ (hγ.mono (hsub i hi'))).edist_le_hausdorffMeasure
          (mem_image_of_mem γ (right_mem_Icc.mpr (hle i hi')))
          (mem_image_of_mem γ (left_mem_Icc.mpr (hle i hi')))
    _ = μH[1] (⋃ i ∈ Finset.range n, γ '' Icc (u i) (u (i + 1))) := by
      symm
      apply measure_biUnion_finset₀ hdisj
      intro i hi
      exact (isCompact_Icc.image_of_continuousOn
        (hγ.mono (hsub i (Finset.mem_range.mp hi)))).measurableSet.nullMeasurableSet
    _ ≤ μH[1] (γ '' Icc a b) := by
      apply measure_mono
      exact iUnion₂_subset fun i hi ↦ image_mono (hsub i (Finset.mem_range.mp hi))

/-- The variation of a continuous injective arc is at most the raw one-dimensional
Hausdorff measure of its trace. No rectifiability hypothesis on the parametrization is needed. -/
theorem eVariationOn_le_hausdorffMeasure_image (hγ : ContinuousOn γ (Icc a b))
    (hinj : InjOn γ (Icc a b)) : eVariationOn γ (Icc a b) ≤ μH[1] (γ '' Icc a b) := by
  rw [eVariationOn.eVariationOn_eq_strictMonoOn]
  exact iSup_le fun p ↦ hγ.sum_edist_le_hausdorffMeasure_image hinj p.2.2.1 p.2.2.2

/-- The variation of a continuous injective arc is at most the Euclidean-normalized
one-dimensional Hausdorff measure of its trace. This also covers empty and singleton intervals. -/
theorem eVariationOn_le_euclideanHausdorffMeasure_image (hγ : ContinuousOn γ (Icc a b))
    (hinj : InjOn γ (Icc a b)) : eVariationOn γ (Icc a b) ≤ μHE[1] (γ '' Icc a b) := by
  have hreal : (μHE[1] : Measure ℝ) = volume := by
    simpa using (InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := ℝ))
  have hscalar :
      Measure.addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin 1)))
        μH[(1 : ℕ)] = 1 := by
    have h := congrArg (fun μ : Measure ℝ ↦ μ (Icc 0 1)) hreal
    simpa [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply,
      hausdorffMeasure_real, Real.volume_Icc] using h
  rw [Measure.euclideanHausdorffMeasure_def, hscalar, one_smul]
  simpa only [Nat.cast_one] using hγ.eVariationOn_le_hausdorffMeasure_image hinj

/-- A continuous injective arc with finite raw Hausdorff length has bounded variation. -/
theorem boundedVariationOn_of_hausdorffMeasure_image_lt_top (hγ : ContinuousOn γ (Icc a b))
    (hinj : InjOn γ (Icc a b)) (hfinite : μH[1] (γ '' Icc a b) < ∞) :
    BoundedVariationOn γ (Icc a b) :=
  ((hγ.eVariationOn_le_hausdorffMeasure_image hinj).trans_lt hfinite).ne

/-- A continuous injective arc with finite Euclidean Hausdorff length has bounded variation,
without a Lipschitz hypothesis on its input parametrization. -/
theorem boundedVariationOn_of_euclideanHausdorffMeasure_image_lt_top
    (hγ : ContinuousOn γ (Icc a b)) (hinj : InjOn γ (Icc a b))
    (hfinite : μHE[1] (γ '' Icc a b) < ∞) : BoundedVariationOn γ (Icc a b) :=
  ((hγ.eVariationOn_le_euclideanHausdorffMeasure_image hinj).trans_lt hfinite).ne

/-! ### Simple closed curves -/

/-- The variation of a continuous simple closed curve is at most the raw one-dimensional
Hausdorff measure of its trace. Simplicity is expressed by injectivity on the half-open parameter
interval; the only repetition on the closed interval is therefore the common endpoint value. The
singleton parameter interval is included. -/
theorem eVariationOn_le_hausdorffMeasure_image_of_injOn_Ico
    (hγ : ContinuousOn γ (Icc a b)) (hinj : InjOn γ (Ico a b))
    (hclosed : γ a = γ b) (hab : a ≤ b) :
    eVariationOn γ (Icc a b) ≤ μH[1] (γ '' Icc a b) := by
  rcases hab.eq_or_lt with rfl | hab
  · exact hγ.eVariationOn_le_hausdorffMeasure_image (Icc_self a ▸ injOn_singleton γ a)
  let c := (a + b) / 2
  have hac : a < c := by dsimp [c]; linarith
  have hcb : c < b := by dsimp [c]; linarith
  -- Half-open injectivity and endpoint equality characterize every possible repeated value.
  have hsimple {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hxy : γ x = γ y) :
      x = y ∨ (x = a ∧ y = b) ∨ (x = b ∧ y = a) := by
    by_cases hxb : x = b
    · subst x
      by_cases hyb : y = b
      · exact Or.inl hyb.symm
      · exact Or.inr <| Or.inr ⟨rfl, (hinj (left_mem_Ico.mpr hab)
          ⟨hy.1, lt_of_le_of_ne hy.2 hyb⟩ (hclosed.trans hxy)).symm⟩
    · by_cases hyb : y = b
      · subst y
        exact Or.inr <| Or.inl ⟨hinj ⟨hx.1, lt_of_le_of_ne hx.2 hxb⟩
          (left_mem_Ico.mpr hab) (hxy.trans hclosed.symm), rfl⟩
      · exact Or.inl <| hinj ⟨hx.1, lt_of_le_of_ne hx.2 hxb⟩
          ⟨hy.1, lt_of_le_of_ne hy.2 hyb⟩ hxy
  -- Splitting at the midpoint turns the closed curve into two injective compact arcs.
  have hleft : InjOn γ (Icc a c) := by
    intro x hx y hy hxy
    rcases hsimple ⟨hx.1, hx.2.trans hcb.le⟩ ⟨hy.1, hy.2.trans hcb.le⟩ hxy with
      h | h | h
    · exact h
    · exact absurd (h.2 ▸ hy.2) (not_le_of_gt hcb)
    · exact absurd (h.1 ▸ hx.2) (not_le_of_gt hcb)
  have hright : InjOn γ (Icc c b) := by
    intro x hx y hy hxy
    rcases hsimple ⟨hac.le.trans hx.1, hx.2⟩ ⟨hac.le.trans hy.1, hy.2⟩ hxy with
      h | h | h
    · exact h
    · exact absurd (h.1 ▸ hx.1) (not_le_of_gt hac)
    · exact absurd (h.2 ▸ hy.1) (not_le_of_gt hac)
  have := Measure.nullSingletonClass_hausdorff X (by norm_num : (0 : ℝ) < 1)
  -- The two arc traces meet only at the midpoint and the common endpoint, hence measurably add.
  have hdisj : AEDisjoint μH[1] (γ '' Icc a c) (γ '' Icc c b) := by
    apply measure_mono_null (t := {γ c, γ a})
    · rintro z ⟨⟨x, hx, rfl⟩, ⟨y, hy, hxy⟩⟩
      rcases hsimple ⟨hx.1, hx.2.trans hcb.le⟩ ⟨hac.le.trans hy.1, hy.2⟩ hxy.symm with
        h | h | h
      · have hcx : c ≤ x := h.symm ▸ hy.1
        exact Or.inl (congrArg γ (le_antisymm hx.2 hcx))
      · exact Or.inr (mem_singleton_iff.mpr (congrArg γ h.1))
      · exact Or.inr (mem_singleton_iff.mpr ((congrArg γ h.1).trans hclosed.symm))
    · exact ((finite_singleton (γ a)).insert (γ c)).measure_zero _
  have hmeasure :
      μH[1] (γ '' Icc a b) = μH[1] (γ '' Icc a c) + μH[1] (γ '' Icc c b) := by
    rw [← Icc_union_Icc_eq_Icc hac.le hcb.le, image_union]
    exact measure_union₀
      (isCompact_Icc.image_of_continuousOn
        (hγ.mono (Icc_subset_Icc hac.le le_rfl))).measurableSet.nullMeasurableSet hdisj
  -- Add the two arc inequalities using additivity of both variation and trace measure.
  have hvariation := eVariationOn.Icc_add_Icc γ (s := univ) hac.le hcb.le (mem_univ c)
  simp only [univ_inter] at hvariation
  have hle := add_le_add
    ((hγ.mono (Icc_subset_Icc le_rfl hcb.le)).eVariationOn_le_hausdorffMeasure_image hleft)
    ((hγ.mono (Icc_subset_Icc hac.le le_rfl)).eVariationOn_le_hausdorffMeasure_image hright)
  exact hvariation.symm.trans_le (hle.trans hmeasure.symm.le)

/-- The variation of a continuous simple closed curve is at most the Euclidean-normalized
one-dimensional Hausdorff measure of its trace. -/
theorem eVariationOn_le_euclideanHausdorffMeasure_image_of_injOn_Ico
    (hγ : ContinuousOn γ (Icc a b)) (hinj : InjOn γ (Ico a b))
    (hclosed : γ a = γ b) (hab : a ≤ b) :
    eVariationOn γ (Icc a b) ≤ μHE[1] (γ '' Icc a b) := by
  have hreal : (μHE[1] : Measure ℝ) = volume := by
    simpa using (InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := ℝ))
  have hscalar :
      Measure.addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin 1)))
        μH[(1 : ℕ)] = 1 := by
    have h := congrArg (fun μ : Measure ℝ ↦ μ (Icc 0 1)) hreal
    simpa [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply,
      hausdorffMeasure_real, Real.volume_Icc] using h
  rw [Measure.euclideanHausdorffMeasure_def, hscalar, one_smul]
  simpa only [Nat.cast_one] using
    hγ.eVariationOn_le_hausdorffMeasure_image_of_injOn_Ico hinj hclosed hab

/-- A continuous simple closed curve with finite raw Hausdorff length has bounded variation. -/
theorem boundedVariationOn_of_hausdorffMeasure_image_lt_top_of_injOn_Ico
    (hγ : ContinuousOn γ (Icc a b)) (hinj : InjOn γ (Ico a b))
    (hclosed : γ a = γ b) (hab : a ≤ b) (hfinite : μH[1] (γ '' Icc a b) < ∞) :
    BoundedVariationOn γ (Icc a b) :=
  ((hγ.eVariationOn_le_hausdorffMeasure_image_of_injOn_Ico hinj hclosed hab).trans_lt
    hfinite).ne

/-- A continuous simple closed curve with finite Euclidean Hausdorff length has bounded variation,
without a Lipschitz hypothesis on its input parametrization. -/
theorem boundedVariationOn_of_euclideanHausdorffMeasure_image_lt_top_of_injOn_Ico
    (hγ : ContinuousOn γ (Icc a b)) (hinj : InjOn γ (Ico a b))
    (hclosed : γ a = γ b) (hab : a ≤ b) (hfinite : μHE[1] (γ '' Icc a b) < ∞) :
    BoundedVariationOn γ (Icc a b) :=
  ((hγ.eVariationOn_le_euclideanHausdorffMeasure_image_of_injOn_Ico hinj hclosed hab).trans_lt
    hfinite).ne

end ContinuousOn
