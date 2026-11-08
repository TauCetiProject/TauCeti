/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.VectorMeasure.BoundedVariation
public import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic
public import Mathlib.Topology.Order.ProjIcc
public import TauCeti.Topology.EMetricSpace.BoundedVariation

/-!
# Finite-horizon Stieltjes vector measures

A bounded-variation path on a closed real interval is extended constantly at both ends before
forming its native derivative vector measure and restricting it to `(a,b]`.
This gives a finite-horizon Stieltjes measure without making assumptions on the path outside the
interval. In particular, a right-continuous path contributes no atom at the initial time, while a
jump at the terminal time is retained.
These are the endpoint conventions for pathwise finite-variation integration.

The construction uses Mathlib's `BoundedVariationOn.vectorMeasure` and `Set.IccExtend`.

## References

* P. E. Protter, *Stochastic Integration and Differential Equations*, second edition,
  Springer, 2005, Chapter I, finite-variation processes.
-/

public section

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

/-- Two vector measures carried by `(a,b]` agree if their cumulative increments agree. -/
theorem MeasureTheory.VectorMeasure.ext_of_restrict_Ioc
    {E : Type*} [NormedAddCommGroup E] {μ ν : VectorMeasure ℝ E} {a b : ℝ}
    (hab : a ≤ b) (hμ : μ.restrict (Ioc a b) = μ) (hν : ν.restrict (Ioc a b) = ν)
    (h : ∀ x ∈ Icc a b, μ (Ioc a x) = ν (Ioc a x)) : μ = ν := by
  have heval (x : ℝ) : μ (Iic x) = ν (Iic x) := by
    rw [← hμ, ← hν, VectorMeasure.restrict_apply _ measurableSet_Ioc measurableSet_Iic,
      VectorMeasure.restrict_apply _ measurableSet_Ioc measurableSet_Iic]
    by_cases hxa : x ≤ a
    · have hempty : Iic x ∩ Ioc a b = ∅ := by
        ext y
        simp only [mem_inter_iff, mem_Iic, mem_Ioc, mem_empty_iff_false]
        grind
      rw [hempty]
      simp
    · by_cases hbx : b ≤ x
      · rw [inter_eq_right.mpr (fun y (hy : y ∈ Ioc a b) ↦ hy.2.trans hbx)]
        exact h b (right_mem_Icc.mpr hab)
      · rw [Iic_inter_Ioc_of_le (le_of_not_ge hbx)]
        exact h x ⟨le_of_not_ge hxa, le_of_not_ge hbx⟩
  apply VectorMeasure.ext_of_generateFrom (range Iic)
    (fun s hs ↦ by obtain ⟨x, rfl⟩ := hs; exact heval x)
    (borel_eq_generateFrom_Iic (α := ℝ)) isPiSystem_Iic
  rw [← hμ, ← hν, VectorMeasure.restrict_apply_univ, VectorMeasure.restrict_apply_univ]
  exact h b (right_mem_Icc.mpr hab)

namespace BoundedVariationOn

variable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
  {f g : ℝ → E} {a b c d x : ℝ}

/-- The finite-horizon Stieltjes measure of a BV path: the derivative of its constant
extension restricted to `(a,b]`. Right continuity within the horizon is needed for its
increment formulas, not its definition. -/
def vectorMeasureIcc (hf : BoundedVariationOn f (Icc a b)) (hab : a ≤ b) :
    VectorMeasure ℝ E :=
  (hf.iccExtend hab).vectorMeasure.restrict (Ioc a b)

/-- Unfolding formula for the finite-horizon derivative measure. -/
theorem vectorMeasureIcc_def (hf : BoundedVariationOn f (Icc a b)) (hab : a ≤ b) :
    hf.vectorMeasureIcc hab = (hf.iccExtend hab).vectorMeasure.restrict (Ioc a b) :=
  (rfl)

omit [CompleteSpace E] in
private theorem rightLim_iccExtend (hab : a ≤ b)
    (hfr : ∀ x ∈ Icc a b, ContinuousWithinAt f (Icc x b) x) (x : ℝ) :
    (IccExtend hab (f ∘ Subtype.val)).rightLim x =
      IccExtend hab (f ∘ Subtype.val) x := by
  apply ContinuousWithinAt.rightLim_eq
  by_cases hxb : b ≤ x
  · have heq : EqOn (IccExtend hab (f ∘ Subtype.val)) (fun _ ↦ f b) (Ici x) := by
      intro y hy
      simp [IccExtend_of_right_le hab _ (hxb.trans hy)]
    exact continuousWithinAt_const.congr_of_mem heq (self_mem_Ici)
  · have hxb : x < b := lt_of_not_ge hxb
    by_cases hxa : x < a
    · have heq : IccExtend hab (f ∘ Subtype.val) =ᶠ[𝓝 x] fun _ ↦ f a := by
        filter_upwards [Iio_mem_nhds hxa] with y hy
        simp [IccExtend_of_le_left hab _ hy.le]
      exact (continuousAt_const.congr_of_eventuallyEq heq).continuousWithinAt
    · have hax : a ≤ x := le_of_not_gt hxa
      have hproj : (projIcc a b hab x : ℝ) = x := by
        simp [projIcc_of_mem hab ⟨hax, hxb.le⟩]
      have hc : Continuous (fun y : ℝ ↦ (projIcc a b hab y : ℝ)) :=
        continuous_subtype_val.comp continuous_projIcc
      exact (hfr x ⟨hax, hxb.le⟩).comp_of_eq hc.continuousAt.continuousWithinAt
        (fun y hy ↦ ⟨by simpa only [coe_projIcc] using
          (le_max_of_le_right (le_min hxb.le hy) : x ≤ max a (min b y)),
          (projIcc a b hab y).property.2⟩) hproj

/-- On subintervals of the horizon a right-continuous BV path has its usual Stieltjes increments. -/
@[simp]
theorem vectorMeasureIcc_Ioc (hf : BoundedVariationOn f (Icc a b)) (hab : a ≤ b)
    (hfr : ∀ x ∈ Icc a b, ContinuousWithinAt f (Icc x b) x)
    (hc : c ∈ Icc a b) (hd : d ∈ Icc a b) (hcd : c ≤ d) :
    hf.vectorMeasureIcc hab (Ioc c d) = f d - f c := by
  rw [vectorMeasureIcc_def,
    VectorMeasure.restrict_eq_self _ measurableSet_Ioc measurableSet_Ioc
      (Ioc_subset_Ioc hc.1 hd.2), (hf.iccExtend hab).vectorMeasure_Ioc hcd,
    rightLim_iccExtend hab hfr, rightLim_iccExtend hab hfr,
    IccExtend_of_mem hab _ hd, IccExtend_of_mem hab _ hc]
  rfl

/-- The variation of the finite-horizon measure is finite. -/
instance isFiniteMeasure_variation_vectorMeasureIcc
    (hf : BoundedVariationOn f (Icc a b)) (hab : a ≤ b) :
    IsFiniteMeasure (hf.vectorMeasureIcc hab).variation := by
  rw [vectorMeasureIcc_def]
  infer_instance

/-- At every time strictly after the initial time, including the terminal time, the atom
is the jump from the left. The unrestricted left limit is legitimate here because a left
neighborhood of this time lies inside the horizon. -/
theorem vectorMeasureIcc_singleton (hf : BoundedVariationOn f (Icc a b)) (hab : a ≤ b)
    (hfr : ∀ x ∈ Icc a b, ContinuousWithinAt f (Icc x b) x) (hx : x ∈ Ioc a b) :
    hf.vectorMeasureIcc hab {x} = f x - f.leftLim x := by
  have heq : IccExtend hab (f ∘ Subtype.val) =ᶠ[𝓝[<] x] f := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Ioi_mem_nhds hx.1)] with y hy hya
    simp [IccExtend_of_mem hab _ ⟨hya.le, hy.le.trans hx.2⟩]
  have hlim : (IccExtend hab (f ∘ Subtype.val)).leftLim x = f.leftLim x :=
    (leftLim_eq_of_tendsto (((hf.iccExtend hab).tendsto_leftLim x).congr' heq)).symm
  rw [vectorMeasureIcc_def,
    VectorMeasure.restrict_eq_self _ measurableSet_Ioc (measurableSet_singleton x)
      (singleton_subset_iff.mpr hx), (hf.iccExtend hab).vectorMeasure_singleton,
    rightLim_iccExtend hab hfr, hlim, IccExtend_of_mem hab _ ⟨hx.1.le, hx.2⟩]
  rfl

/-- The finite-horizon measure is carried by the half-open horizon. -/
@[simp]
theorem vectorMeasureIcc_restrict (hf : BoundedVariationOn f (Icc a b)) (hab : a ≤ b) :
    (hf.vectorMeasureIcc hab).restrict (Ioc a b) = hf.vectorMeasureIcc hab := by
  simp [vectorMeasureIcc_def, VectorMeasure.restrict_restrict, measurableSet_Ioc]

/-- There is no initial-time atom, even when the original path has a left jump there. -/
@[simp]
theorem vectorMeasureIcc_singleton_left (hf : BoundedVariationOn f (Icc a b)) (hab : a ≤ b) :
    hf.vectorMeasureIcc hab {a} = 0 := by
  simp [vectorMeasureIcc_def, VectorMeasure.restrict_apply, measurableSet_Ioc,
    Set.singleton_inter_eq_empty.mpr]

/-- The total mass is the path's net change over the horizon. -/
@[simp]
theorem vectorMeasureIcc_univ (hf : BoundedVariationOn f (Icc a b)) (hab : a ≤ b)
    (hfr : ∀ x ∈ Icc a b, ContinuousWithinAt f (Icc x b) x) :
    hf.vectorMeasureIcc hab univ = f b - f a := by
  have h := congrArg (fun μ : VectorMeasure ℝ E ↦ μ univ) (hf.vectorMeasureIcc_restrict hab)
  rw [VectorMeasure.restrict_apply_univ] at h
  rw [← h, hf.vectorMeasureIcc_Ioc hab hfr (left_mem_Icc.mpr hab)
    (right_mem_Icc.mpr hab) hab]

/-- The cumulative mass within the horizon is the change since the initial time. -/
@[simp]
theorem vectorMeasureIcc_Iic (hf : BoundedVariationOn f (Icc a b)) (hab : a ≤ b)
    (hfr : ∀ x ∈ Icc a b, ContinuousWithinAt f (Icc x b) x) (hx : x ∈ Icc a b) :
    hf.vectorMeasureIcc hab (Iic x) = f x - f a := by
  have h := congrArg (fun μ : VectorMeasure ℝ E ↦ μ (Iic x))
    (hf.vectorMeasureIcc_restrict hab)
  rw [VectorMeasure.restrict_apply _ measurableSet_Ioc measurableSet_Iic,
    Iic_inter_Ioc_of_le hx.2] at h
  rw [← h, hf.vectorMeasureIcc_Ioc hab hfr (left_mem_Icc.mpr hab) hx hx.1]

/-- Characterization and uniqueness of the finite-horizon Stieltjes measure by its carrier
and cumulative increments. No behavior of the path outside `[a,b]` enters this criterion. -/
theorem eq_vectorMeasureIcc_iff (hf : BoundedVariationOn f (Icc a b)) (hab : a ≤ b)
    (hfr : ∀ x ∈ Icc a b, ContinuousWithinAt f (Icc x b) x) (ν : VectorMeasure ℝ E) :
    ν = hf.vectorMeasureIcc hab ↔ ν.restrict (Ioc a b) = ν ∧
      ∀ x ∈ Icc a b, ν (Ioc a x) = f x - f a := by
  constructor
  · rintro rfl
    exact ⟨hf.vectorMeasureIcc_restrict hab, fun x hx ↦
      hf.vectorMeasureIcc_Ioc hab hfr (left_mem_Icc.mpr hab) hx hx.1⟩
  · rintro ⟨hν, hincr⟩
    exact VectorMeasure.ext_of_restrict_Ioc hab hν (hf.vectorMeasureIcc_restrict hab)
      (fun x hx ↦ (hincr x hx).trans
        (hf.vectorMeasureIcc_Ioc hab hfr (left_mem_Icc.mpr hab) hx hx.1).symm)

/-- Restriction to a shorter horizon agrees with the measure constructed on that horizon. -/
theorem vectorMeasureIcc_restrict_Ioc (hf : BoundedVariationOn f (Icc a b)) (hab : a ≤ b)
    (hfr : ∀ x ∈ Icc a b, ContinuousWithinAt f (Icc x b) x)
    (hc : c ∈ Icc a b) (hd : d ∈ Icc a b) (hcd : c ≤ d) :
    (hf.vectorMeasureIcc hab).restrict (Ioc c d) =
      (hf.mono (Icc_subset_Icc hc.1 hd.2)).vectorMeasureIcc hcd := by
  have hfr' : ∀ x ∈ Icc c d, ContinuousWithinAt f (Icc x d) x := fun x hx ↦
    (hfr x ⟨hc.1.trans hx.1, hx.2.trans hd.2⟩).mono (Icc_subset_Icc_right hd.2)
  apply ((hf.mono (Icc_subset_Icc hc.1 hd.2)).eq_vectorMeasureIcc_iff hcd hfr' _).mpr
  constructor
  · rw [VectorMeasure.restrict_restrict _ measurableSet_Ioc measurableSet_Ioc, inter_self]
  · intro x hx
    rw [VectorMeasure.restrict_eq_self _ measurableSet_Ioc measurableSet_Ioc
      (Ioc_subset_Ioc le_rfl hx.2)]
    exact hf.vectorMeasureIcc_Ioc hab hfr hc
      ⟨hc.1.trans hx.1, hx.2.trans hd.2⟩ hx.1

/-- On a zero-length horizon the measure is zero. -/
@[simp]
theorem vectorMeasureIcc_self (hf : BoundedVariationOn f (Icc a a)) :
    hf.vectorMeasureIcc le_rfl = 0 := by
  simp [vectorMeasureIcc_def]

/-- Paths agreeing on the horizon give the same finite-horizon measure. -/
theorem vectorMeasureIcc_congr (hf : BoundedVariationOn f (Icc a b))
    (hg : BoundedVariationOn g (Icc a b)) (hab : a ≤ b) (hfg : EqOn f g (Icc a b)) :
    hf.vectorMeasureIcc hab = hg.vectorMeasureIcc hab := by
  have hext : IccExtend hab (f ∘ Subtype.val) = IccExtend hab (g ∘ Subtype.val) :=
    funext fun x ↦ hfg (projIcc a b hab x).property
  simp only [vectorMeasureIcc_def]
  congr 2

end BoundedVariationOn
