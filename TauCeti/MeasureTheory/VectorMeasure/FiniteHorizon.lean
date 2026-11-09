/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.VectorMeasure.BoundedVariation
public import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic
public import TauCeti.Topology.Order.ProjIcc
public import TauCeti.Topology.EMetricSpace.BoundedVariation

/-!
# Finite-horizon Stieltjes vector measures

A bounded-variation path on a closed interval in a densely ordered space with compact intervals
is extended constantly at both ends before forming its native derivative vector measure and
restricting it to `(a,b]`.
This gives a finite-horizon Stieltjes measure without making assumptions on the path outside the
interval. The initial time never carries an atom because of the restriction to `(a,b]`, while a
jump at the terminal time is retained. Right continuity within the horizon yields the usual
increment formulas. These are the endpoint conventions for pathwise finite-variation integration.

The construction uses Mathlib's `BoundedVariationOn.vectorMeasure` and `Set.IccExtend`.

## References

* P. E. Protter, *Stochastic Integration and Differential Equations*, second edition,
  Springer, 2005, Chapter I, finite-variation processes.
-/

public section

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

variable {α : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
  [SecondCountableTopology α] [MeasurableSpace α] [BorelSpace α]

/-- Two vector measures carried by `(a,b]` agree if their cumulative increments agree. -/
theorem MeasureTheory.VectorMeasure.ext_of_restrict_Ioc
    {E : Type*} [AddCommGroup E] [TopologicalSpace E] [T2Space E]
    {μ ν : VectorMeasure α E} {a b : α}
    (hab : a ≤ b) (hμ : μ.restrict (Ioc a b) = μ) (hν : ν.restrict (Ioc a b) = ν)
    (h : ∀ x ∈ Icc a b, μ (Ioc a x) = ν (Ioc a x)) : μ = ν := by
  borelize α
  have heval (x : α) : μ (Iic x) = ν (Iic x) := by
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
    (borel_eq_generateFrom_Iic (α := α)) isPiSystem_Iic
  rw [← hμ, ← hν, VectorMeasure.restrict_apply_univ, VectorMeasure.restrict_apply_univ]
  exact h b (right_mem_Icc.mpr hab)

namespace BoundedVariationOn

variable [DenselyOrdered α] [CompactIccSpace α]
  {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
  {f g : α → E} {a b c d x : α}

/-- The finite-horizon Stieltjes measure of a BV path: the derivative of its constant
extension restricted to `(a,b]`. Right continuity within the horizon is needed for its
increment formulas, not its definition. -/
def vectorMeasureIcc (hf : BoundedVariationOn f (Icc a b)) (hab : a ≤ b) :
    VectorMeasure α E :=
  (hf.IccExtend hab).vectorMeasure.restrict (Ioc a b)

/-- Unfolding formula for the finite-horizon derivative measure. -/
theorem vectorMeasureIcc_def (hf : BoundedVariationOn f (Icc a b)) (hab : a ≤ b) :
    hf.vectorMeasureIcc hab = (hf.IccExtend hab).vectorMeasure.restrict (Ioc a b) :=
  (rfl)

/-- On subintervals of the horizon a right-continuous BV path has its usual Stieltjes increments. -/
@[simp]
theorem vectorMeasureIcc_Ioc (hf : BoundedVariationOn f (Icc a b)) (hab : a ≤ b)
    (hfc : ContinuousWithinAt f (Icc c b) c) (hfd : ContinuousWithinAt f (Icc d b) d)
    (hc : c ∈ Icc a b) (hd : d ∈ Icc a b) (hcd : c ≤ d) :
    hf.vectorMeasureIcc hab (Ioc c d) = f d - f c := by
  rw [vectorMeasureIcc_def,
    VectorMeasure.restrict_eq_self _ measurableSet_Ioc measurableSet_Ioc
      (Ioc_subset_Ioc hc.1 hd.2), (hf.IccExtend hab).vectorMeasure_Ioc hcd,
    (TauCeti.continuousWithinAt_IccExtend_Ici hab (fun _ ↦ hfd)).rightLim_eq,
    (TauCeti.continuousWithinAt_IccExtend_Ici hab (fun _ ↦ hfc)).rightLim_eq,
    IccExtend_of_mem hab _ hd, IccExtend_of_mem hab _ hc]
  rfl

/-- The variation of the finite-horizon measure is finite. -/
instance isFiniteMeasure_variation_vectorMeasureIcc
    (hf : BoundedVariationOn f (Icc a b)) (hab : a ≤ b) :
    IsFiniteMeasure (hf.vectorMeasureIcc hab).variation := by
  rw [vectorMeasureIcc_def]
  infer_instance

/-- At a time in `(a,b]` where the path is right-continuous within the horizon, the atom is
its jump from the left. This continuity is automatic at `b`. The unrestricted left limit is
legitimate because a left neighborhood of this time lies inside the horizon. -/
@[simp]
theorem vectorMeasureIcc_singleton (hf : BoundedVariationOn f (Icc a b)) (hab : a ≤ b)
    (hfr : ContinuousWithinAt f (Icc x b) x) (hx : x ∈ Ioc a b) :
    hf.vectorMeasureIcc hab {x} = f x - f.leftLim x := by
  have heq : Set.IccExtend hab (f ∘ Subtype.val) =ᶠ[𝓝[<] x] f := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Ioi_mem_nhds hx.1)] with y hy hya
    simp [IccExtend_of_mem hab _ ⟨hya.le, hy.le.trans hx.2⟩]
  have : (𝓝[<] x).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_Iio' ⟨a, hx.1⟩]
    exact self_mem_Iic
  have hlim : (Set.IccExtend hab (f ∘ Subtype.val)).leftLim x = f.leftLim x :=
    (leftLim_eq_of_tendsto (((hf.IccExtend hab).tendsto_leftLim x).congr' heq)).symm
  rw [vectorMeasureIcc_def,
    VectorMeasure.restrict_eq_self _ measurableSet_Ioc (measurableSet_singleton x)
      (singleton_subset_iff.mpr hx), (hf.IccExtend hab).vectorMeasure_singleton,
    (TauCeti.continuousWithinAt_IccExtend_Ici hab (fun _ ↦ hfr)).rightLim_eq, hlim,
    IccExtend_of_mem hab _ ⟨hx.1.le, hx.2⟩]
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

/-- For a path right-continuous at the initial time within the horizon, the total mass is
its net change over the horizon. -/
@[simp]
theorem vectorMeasureIcc_univ (hf : BoundedVariationOn f (Icc a b)) (hab : a ≤ b)
    (hfr : ContinuousWithinAt f (Icc a b) a) :
    hf.vectorMeasureIcc hab univ = f b - f a := by
  have h := congrArg (fun μ : VectorMeasure α E ↦ μ univ) (hf.vectorMeasureIcc_restrict hab)
  rw [VectorMeasure.restrict_apply_univ] at h
  rw [← h, hf.vectorMeasureIcc_Ioc hab hfr (by simp) (left_mem_Icc.mpr hab)
    (right_mem_Icc.mpr hab) hab]

/-- For a path right-continuous within the horizon at the initial time and at `x`, the
cumulative mass up to `x` is the change since the initial time. -/
@[simp]
theorem vectorMeasureIcc_Iic (hf : BoundedVariationOn f (Icc a b)) (hab : a ≤ b)
    (hfa : ContinuousWithinAt f (Icc a b) a) (hfx : ContinuousWithinAt f (Icc x b) x)
    (hx : x ∈ Icc a b) :
    hf.vectorMeasureIcc hab (Iic x) = f x - f a := by
  have h := congrArg (fun μ : VectorMeasure α E ↦ μ (Iic x))
    (hf.vectorMeasureIcc_restrict hab)
  rw [VectorMeasure.restrict_apply _ measurableSet_Ioc measurableSet_Iic,
    Iic_inter_Ioc_of_le hx.2] at h
  rw [← h, hf.vectorMeasureIcc_Ioc hab hfa hfx (left_mem_Icc.mpr hab) hx hx.1]

/-- For a path right-continuous within the horizon, its finite-horizon Stieltjes measure is
characterized by its carrier and cumulative increments. No behavior of the path outside `[a,b]`
enters this criterion. -/
theorem eq_vectorMeasureIcc_iff (hf : BoundedVariationOn f (Icc a b)) (hab : a ≤ b)
    (hfr : ∀ x ∈ Icc a b, ContinuousWithinAt f (Icc x b) x) (ν : VectorMeasure α E) :
    ν = hf.vectorMeasureIcc hab ↔ ν.restrict (Ioc a b) = ν ∧
      ∀ x ∈ Icc a b, ν (Ioc a x) = f x - f a := by
  constructor
  · rintro rfl
    exact ⟨hf.vectorMeasureIcc_restrict hab, fun x hx ↦
      hf.vectorMeasureIcc_Ioc hab (hfr a (left_mem_Icc.mpr hab)) (hfr x hx)
        (left_mem_Icc.mpr hab) hx hx.1⟩
  · rintro ⟨hν, hincr⟩
    exact VectorMeasure.ext_of_restrict_Ioc hab hν (hf.vectorMeasureIcc_restrict hab)
      (fun x hx ↦ (hincr x hx).trans
        (hf.vectorMeasureIcc_Ioc hab (hfr a (left_mem_Icc.mpr hab)) (hfr x hx)
          (left_mem_Icc.mpr hab) hx hx.1).symm)

/-- For a path right-continuous within the horizon, restriction to a shorter horizon agrees
with the measure constructed on that horizon. -/
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
    exact hf.vectorMeasureIcc_Ioc hab (hfr c hc)
      (hfr x ⟨hc.1.trans hx.1, hx.2.trans hd.2⟩) hc
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
  have hext : Set.IccExtend hab (f ∘ Subtype.val) = Set.IccExtend hab (g ∘ Subtype.val) :=
    funext fun x ↦ hfg (projIcc a b hab x).property
  simp only [vectorMeasureIcc_def]
  congr 2

end BoundedVariationOn
