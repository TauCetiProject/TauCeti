/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Topology.Order.Compact

/-!
# Planar cells between continuous graphs

The vertical region between two graphs includes both graphs and the two endpoint fibers. The
horizontal region swaps the two coordinates. Continuous graphs on the base interval suffice for
compactness and a null frontier; no differentiability or absolute continuity is required.

Degenerate fibers and empty fibers are allowed by the geometric API.
-/

public section

open MeasureTheory Set
open scoped Topology

namespace TauCeti.Green

/-- A closed vertical region between two real graphs over `[a,b]`. -/
def verticalRegion (a b : ℝ) (lower upper : ℝ → ℝ) : Set ℂ :=
  {z | z.re ∈ Icc a b ∧ z.im ∈ Icc (lower z.re) (upper z.re)}

/-- A closed horizontal region between two real graphs over `[a,b]`. -/
def horizontalRegion (a b : ℝ) (lower upper : ℝ → ℝ) : Set ℂ :=
  {z | z.im ∈ Icc a b ∧ z.re ∈ Icc (lower z.im) (upper z.im)}

variable {a b : ℝ} {lower upper : ℝ → ℝ} {z : ℂ}

/-- Membership in a vertical region in real coordinates. -/
@[simp]
theorem mem_verticalRegion : z ∈ verticalRegion a b lower upper ↔
    z.re ∈ Icc a b ∧ z.im ∈ Icc (lower z.re) (upper z.re) := Iff.rfl

/-- Membership in a horizontal region in real coordinates. -/
@[simp]
theorem mem_horizontalRegion : z ∈ horizontalRegion a b lower upper ↔
    z.im ∈ Icc a b ∧ z.re ∈ Icc (lower z.im) (upper z.im) := Iff.rfl

/-- In real product coordinates the vertical cell has the indicated interval fibers. -/
theorem preimage_measurableEquivRealProd_symm_verticalRegion :
    Complex.measurableEquivRealProd.symm ⁻¹' verticalRegion a b lower upper =
        {p : ℝ × ℝ | p.1 ∈ Icc a b ∧ p.2 ∈ Icc (lower p.1) (upper p.1)} := (rfl)

/-- A fiber over a point of the base interval is exactly the closed interval between the graphs. -/
theorem verticalRegion_fiber_of_mem {x : ℝ} (hx : x ∈ Icc a b) :
    (fun y : ℝ ↦ Complex.measurableEquivRealProd.symm (x, y)) ⁻¹'
      verticalRegion a b lower upper = Icc (lower x) (upper x) := by
  ext y
  simp [hx]

/-- A fiber outside the base interval is empty. -/
theorem verticalRegion_fiber_of_notMem {x : ℝ} (hx : x ∉ Icc a b) :
    (fun y : ℝ ↦ Complex.measurableEquivRealProd.symm (x, y)) ⁻¹'
      verticalRegion a b lower upper = ∅ := by
  ext y
  simp [hx]

/-- A vertical region with continuous graphs is closed. -/
theorem isClosed_verticalRegion (hl : ContinuousOn lower (Icc a b))
    (hu : ContinuousOn upper (Icc a b)) : IsClosed (verticalRegion a b lower upper) := by
  have hc : IsClosed {z : ℂ | z.re ∈ Icc a b} := isClosed_Icc.preimage Complex.continuous_re
  have hl' := hl.comp Complex.continuous_re.continuousOn (fun _ hx ↦ hx)
  have hu' := hu.comp Complex.continuous_re.continuousOn (fun _ hx ↦ hx)
  convert (hc.isClosed_le hl' Complex.continuous_im.continuousOn).inter
    (hc.isClosed_le Complex.continuous_im.continuousOn hu') using 1
  ext z
  simp only [mem_verticalRegion, mem_Icc, mem_inter_iff, mem_ofPred_eq, Function.comp_apply]
  tauto

/-- A vertical region with continuous graphs is compact, even if some fibers are empty. -/
theorem isCompact_verticalRegion (hl : ContinuousOn lower (Icc a b))
    (hu : ContinuousOn upper (Icc a b)) : IsCompact (verticalRegion a b lower upper) := by
  obtain ⟨L, hL⟩ := isCompact_Icc.bddBelow_image hl
  obtain ⟨U, hU⟩ := isCompact_Icc.bddAbove_image hu
  refine ((isCompact_Icc (a := a) (b := b)).reProdIm
    (isCompact_Icc (a := L) (b := U))).of_isClosed_subset
    (isClosed_verticalRegion hl hu) ?_
  intro z hz
  exact ⟨hz.1, (hL ⟨z.re, hz.1, rfl⟩).trans hz.2.1,
    hz.2.2.trans (hU ⟨z.re, hz.1, rfl⟩)⟩

/-- A vertical region with continuous graphs is measurable. -/
theorem measurableSet_verticalRegion (hl : ContinuousOn lower (Icc a b))
    (hu : ContinuousOn upper (Icc a b)) : MeasurableSet (verticalRegion a b lower upper) :=
  (isClosed_verticalRegion hl hu).measurableSet

/-- Points strictly between both endpoint fibers and the two graphs are interior points. -/
theorem mem_interior_verticalRegion (hl : ContinuousOn lower (Icc a b))
    (hu : ContinuousOn upper (Icc a b)) (hx : z.re ∈ Ioo a b)
    (hy : z.im ∈ Ioo (lower z.re) (upper z.re)) :
    z ∈ interior (verticalRegion a b lower upper) := by
  have hl' : ContinuousAt (fun w : ℂ ↦ lower w.re) z :=
    (hl z.re (Ioo_subset_Icc_self hx)).continuousAt (Icc_mem_nhds hx.1 hx.2)
      |>.comp Complex.continuous_re.continuousAt
  have hu' : ContinuousAt (fun w : ℂ ↦ upper w.re) z :=
    (hu z.re (Ioo_subset_Icc_self hx)).continuousAt (Icc_mem_nhds hx.1 hx.2)
      |>.comp Complex.continuous_re.continuousAt
  apply mem_interior_iff_mem_nhds.mpr
  filter_upwards [Complex.continuous_re.continuousAt.preimage_mem_nhds
      (isOpen_Ioo.mem_nhds hx),
    hl'.eventually_lt Complex.continuous_im.continuousAt hy.1,
    Complex.continuous_im.continuousAt.eventually_lt hu' hy.2] with w hw hwL hwU
  exact ⟨Ioo_subset_Icc_self hw, hwL.le, hwU.le⟩

/-- The frontier is contained in the two endpoint lines and the two graph traces. -/
theorem frontier_verticalRegion_subset (hl : ContinuousOn lower (Icc a b))
    (hu : ContinuousOn upper (Icc a b)) :
    frontier (verticalRegion a b lower upper) ⊆
      {z : ℂ | z.re = a} ∪ {z : ℂ | z.re = b} ∪
        {z : ℂ | z.re ∈ Icc a b ∧ z.im = lower z.re} ∪
        {z : ℂ | z.re ∈ Icc a b ∧ z.im = upper z.re} := by
  intro z hz
  have hmem : z ∈ verticalRegion a b lower upper :=
    (isClosed_verticalRegion hl hu).closure_eq ▸ frontier_subset_closure hz
  by_cases ha : z.re = a
  · exact Or.inl (Or.inl (Or.inl ha))
  by_cases hb : z.re = b
  · exact Or.inl (Or.inl (Or.inr hb))
  by_cases hL : z.im = lower z.re
  · exact Or.inl (Or.inr ⟨hmem.1, hL⟩)
  by_cases hU : z.im = upper z.re
  · exact Or.inr ⟨hmem.1, hU⟩
  exact False.elim (hz.2 (mem_interior_verticalRegion hl hu
    ⟨lt_of_le_of_ne hmem.1.1 (Ne.symm ha), lt_of_le_of_ne hmem.1.2 hb⟩
    ⟨lt_of_le_of_ne hmem.2.1 (Ne.symm hL), lt_of_le_of_ne hmem.2.2 hU⟩))

/-- The frontier of a vertical cell bounded by continuous graphs has zero planar area. -/
theorem volume_frontier_verticalRegion_eq_zero (hl : ContinuousOn lower (Icc a b))
    (hu : ContinuousOn upper (Icc a b)) :
    volume (frontier (verticalRegion a b lower upper)) = 0 := by
  apply measure_mono_null (frontier_verticalRegion_subset hl hu)
  exact measure_union_null
    (measure_union_null (measure_union_null (Complex.volume_setOf_re_eq a)
      (Complex.volume_setOf_re_eq b)) (Complex.volume_setOf_re_mem_Icc_im_eq hl))
        (Complex.volume_setOf_re_mem_Icc_im_eq hu)

/-- The horizontal region is the coordinate swap of the vertical region. -/
theorem preimage_coordinateSwap_verticalRegion :
    Complex.coordinateSwap ⁻¹' verticalRegion a b lower upper =
      horizontalRegion a b lower upper := by
  ext z
  simp

/-- The vertical region is the coordinate swap of the horizontal region. -/
theorem preimage_coordinateSwap_horizontalRegion :
    Complex.coordinateSwap ⁻¹' horizontalRegion a b lower upper =
      verticalRegion a b lower upper := by
  ext z
  simp

/-- A horizontal region with continuous graphs is compact. -/
theorem isCompact_horizontalRegion (hl : ContinuousOn lower (Icc a b))
    (hu : ContinuousOn upper (Icc a b)) : IsCompact (horizontalRegion a b lower upper) := by
  rw [← preimage_coordinateSwap_verticalRegion]
  exact Complex.coordinateSwap.isCompact_preimage.mpr (isCompact_verticalRegion hl hu)

/-- A horizontal region with continuous graphs is measurable. -/
theorem measurableSet_horizontalRegion (hl : ContinuousOn lower (Icc a b))
    (hu : ContinuousOn upper (Icc a b)) : MeasurableSet (horizontalRegion a b lower upper) :=
  (isCompact_horizontalRegion hl hu).measurableSet

/-- The frontier of a horizontal cell bounded by continuous graphs has zero planar area. -/
theorem volume_frontier_horizontalRegion_eq_zero (hl : ContinuousOn lower (Icc a b))
    (hu : ContinuousOn upper (Icc a b)) :
    volume (frontier (horizontalRegion a b lower upper)) = 0 := by
  rw [← preimage_coordinateSwap_verticalRegion, ← Complex.coordinateSwap.preimage_frontier]
  exact (Complex.measurePreserving_coordinateSwap.measure_preimage
    isClosed_frontier.measurableSet.nullMeasurableSet).trans
      (volume_frontier_verticalRegion_eq_zero hl hu)

end TauCeti.Green
