/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.CWComplex.Abstract.FiberwiseCell.Attachment
import TauCeti.Topology.Circle.Degree
import TauCeti.Topology.Homotopy.Homotopic.Rel

/-!
# Reattachment maps depend on the boundary homotopy

The fiberwise reattachment map of Milnor's Lemma 3.6 (`TauCeti.fiberwiseCellReattachment`)
compares two attachments `(P × A) ∪_{α₁} ⨆ᵢ (P × D^{k i})` and `(P × A) ∪_{α₀} ⨆ᵢ (P × D^{k i})`.
It is built from self-maps `h i` of the disc pairs and homotopies `K i : χ₁ i ≃ χ₀ i ∘ (p, h i)` of
characteristic maps into a space `Y ⊇ A`. On the `i`-th disc it is `x ↦ h i (p, 2x)` for
`‖x‖ ≤ 1/2` and `x ↦ K i (2 - 2‖x‖, (p, x/‖x‖))` for `1/2 ≤ ‖x‖`, so it reads `K i` only on the
boundary spheres, where it is a homotopy `H i` in `A` from `α₁ i` to `α₀ i ∘ h i`. This file makes
the two halves of that remark precise.

* The reattachment map depends on the homotopies only through their boundary restrictions `H i`
  (`TauCeti.fiberwiseCellReattachment_congr`): homotopies of possibly different characteristic maps
  that agree on the boundary spheres give the same map.
* Its class up to homotopy relative to `P × A` can depend on these boundary homotopies
  (`TauCeti.exists_not_homotopicRel_fiberwiseCellReattachment_fiberwiseCellReattachment`). Take `A`
  the unit circle in `Y = ℂ`, one `1`-cell attached at both ends to the point `1`, constant
  characteristic maps and `h` the identity, so that both attachments are the wedge of two circles.
  The homotopy `K'` constant at `1` gives a map homotopic relative to `A` to the identity of the
  wedge: it stretches the inner half of the new cell over the whole cell and sends the outer annulus
  to `1`. The homotopy `K` whose boundary restriction winds once around `A` at the end `-1` and
  stays at `1` at the end `+1` gives a map that, up to homotopy, sends the new circle to the loop of
  `A` followed by the new circle. Collapsing the new cell to the point `1` and following its
  diameter, the loop given by `K` has degree `1` in `A` and the loop given by `K'` has degree `0`; a
  homotopy relative to `A` would make these loops homotopic relative to their endpoints, which the
  degree forbids (`Circle.degree_eq_of_homotopic`).

So the independence of the reattachment class from the homotopies
(`TauCeti.exists_homotopyRel_fiberwiseCellReattachment_fiberwiseCellReattachment`) needs its
hypothesis that the comparison map `(P × A) ∪_{α₀} ⨆ᵢ (P × D^{k i}) → P × Y` has a left homotopy
inverse relative to `P × A`. In the example the comparison map goes to the contractible space `ℂ`,
so it has none. For Morse cells, Milnor's cell attachment theorem supplies such a left inverse,
and the reattachment class does not depend on the homotopies of the characteristic maps in the upper
sublevel (`TauCeti.homotopicRel_morseCellReattachment_morseCellReattachment`). Without such a left
inverse, as in the example, the boundary homotopy is part of the data that determines the class.

## Main results

* `TauCeti.fiberwiseCellReattachment_congr`: the reattachment map only depends on the restrictions
  of the homotopies to the boundary spheres.
* `TauCeti.exists_not_homotopicRel_fiberwiseCellReattachment_fiberwiseCellReattachment`: two
  reattachment maps between the same attachments, built from the same characteristic maps and disc
  self-maps but from homotopies with different boundary restrictions, need not be homotopic
  relative to the attached base.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Lemma 3.6.
-/

public section

noncomputable section

open CategoryTheory Set Metric unitInterval Real

universe u

namespace TauCeti

section Congr

variable {P Y : Type u} [TopologicalSpace P] [TopologicalSpace Y] {A : Set Y} {ι : Type u}
  {k : ι → ℕ} (α₀ α₁ : ∀ i, C(P × TopCat.diskBoundary.{u} (k i), A))
  {χ₀ χ₁ χ₀' χ₁' : ∀ i, C(P × TopCat.disk.{u} (k i), Y)}
  {hχ₀ : ∀ i p s, χ₀ i (p, TopCat.diskBoundaryInclusion (k i) s) = α₀ i (p, s)}
  {hχ₁ : ∀ i p s, χ₁ i (p, TopCat.diskBoundaryInclusion (k i) s) = α₁ i (p, s)}
  {hχ₀' : ∀ i p s, χ₀' i (p, TopCat.diskBoundaryInclusion (k i) s) = α₀ i (p, s)}
  {hχ₁' : ∀ i p s, χ₁' i (p, TopCat.diskBoundaryInclusion (k i) s) = α₁ i (p, s)}
  (h : ∀ i, C(P × TopCat.disk.{u} (k i), TopCat.disk.{u} (k i)))
  {hh : ∀ i p, MapsTo (fun w ↦ h i (p, w)) (range (TopCat.diskBoundaryInclusion (k i)))
    (range (TopCat.diskBoundaryInclusion (k i)))}
  {K : ∀ i, (χ₁ i).Homotopy ((χ₀ i).comp (ContinuousMap.fst.prodMk (h i)))}
  {hK : ∀ i t p s, K i (t, (p, TopCat.diskBoundaryInclusion (k i) s)) ∈ A}
  {K' : ∀ i, (χ₁' i).Homotopy ((χ₀' i).comp (ContinuousMap.fst.prodMk (h i)))}
  {hK' : ∀ i t p s, K' i (t, (p, TopCat.diskBoundaryInclusion (k i) s)) ∈ A}

/-- **The reattachment map only depends on the boundary homotopies.** Two fiberwise reattachment
maps with the same attaching maps and disc self-maps agree when their homotopies, possibly between
different characteristic maps, agree on the boundary spheres. -/
theorem fiberwiseCellReattachment_congr
    (hKK' : ∀ i t p s, K i (t, (p, TopCat.diskBoundaryInclusion (k i) s)) =
      K' i (t, (p, TopCat.diskBoundaryInclusion (k i) s))) :
    fiberwiseCellReattachment α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h hh K hK =
      fiberwiseCellReattachment α₀ α₁ χ₀' χ₁' hχ₀' hχ₁' h hh K' hK' := by
  refine fiberwiseCellAttachment_hom_ext α₁ (fun x ↦
    (fiberwiseCellReattachment_fiberwiseCellAttachmentIncl ..).trans
      (fiberwiseCellReattachment_fiberwiseCellAttachmentIncl ..).symm) fun i ⟨p, w⟩ ↦ ?_
  rcases le_total ‖w.down.val‖ (1 / 2) with hw | hw
  · have hv := TopCat.coe_reattachmentRadial_of_norm_le hw
    rw [fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_norm_le (hw := hw) (hv := hv),
      fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_norm_le (hw := hw) (hv := hv)]
  · have ht := TopCat.coe_reattachmentTime_of_le_norm hw
    have hs := TopCat.coe_annulusDir (by norm_num : (0 : ℝ) < 1 / 2) ⟨w, hw⟩
    rw [fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_le_norm (hw := hw) (ht := ht)
        (hs := hs),
      fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_le_norm (hw := hw) (ht := ht)
        (hs := hs)]
    exact congrArg (fun a ↦ fiberwiseCellAttachmentIncl α₀ (p, a)) (Subtype.ext (hKK' ..))

end Congr

section Example

/-! The example: one `1`-cell attached at both ends to the point `1` of the unit circle in `ℂ`. -/

/-- The coordinate of a point of the `1`-disk. -/
private def diskOneCoord (w : TopCat.disk.{0} 1) : ℝ :=
  ((w : ULift.{0} (closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1)).down :
    EuclideanSpace ℝ (Fin 1)) 0

private theorem continuous_diskOneCoord : Continuous diskOneCoord :=
  (EuclideanSpace.proj (0 : Fin 1)).continuous.comp
    (continuous_subtypeVal.comp continuous_uliftDown)

/-- The constant attaching map at the point `1` of the unit circle. -/
private def basepointAttachingMap :
    ∀ _ : PUnit.{1}, C(PUnit.{1} × TopCat.diskBoundary.{0} 1, sphere (0 : ℂ) 1) :=
  fun _ ↦ ContinuousMap.const _ ⟨1, by simp⟩

/-- The constant characteristic map at `1 ∈ ℂ`. -/
private def basepointCharMap : ∀ _ : PUnit.{1}, C(PUnit.{1} × TopCat.disk.{0} 1, ℂ) :=
  fun _ ↦ ContinuousMap.const _ 1

/-- The identity of the `1`-disk, as a family over a point. -/
private def diskOneId : ∀ _ : PUnit.{1}, C(PUnit.{1} × TopCat.disk.{0} 1, TopCat.disk.{0} 1) :=
  fun _ ↦ ContinuousMap.snd

private theorem basepointCharMap_diskBoundaryInclusion (i : PUnit.{1}) (p : PUnit.{1})
    (s : TopCat.diskBoundary.{0} 1) :
    basepointCharMap i (p, TopCat.diskBoundaryInclusion 1 s) = basepointAttachingMap i (p, s) :=
  (rfl)

private theorem mapsTo_diskOneId (i : PUnit.{1}) (p : PUnit.{1}) :
    MapsTo (fun w ↦ diskOneId i (p, w)) (range (TopCat.diskBoundaryInclusion 1))
      (range (TopCat.diskBoundaryInclusion 1)) :=
  fun _ hw ↦ hw

/-- The homotopy `(t, x) ↦ ((1 - x)/2) e^{2πit} + (1 + x)/2` from the constant map `1` to itself
on the `1`-disk. Its restriction to the end `-1` winds once around the unit circle, and to the end
`+1` it is constant at `1`. -/
private def windingHomotopy (i : PUnit.{1}) :
    (basepointCharMap i).Homotopy
      ((basepointCharMap i).comp (ContinuousMap.fst.prodMk (diskOneId i))) where
  toFun x := (1 - diskOneCoord x.2.2) / 2 * (Circle.exp (2 * π * x.1) : ℂ) +
    (1 + diskOneCoord x.2.2) / 2
  continuous_toFun := by
    have hc : Continuous fun x : I × (PUnit.{1} × TopCat.disk.{0} 1) ↦
        (diskOneCoord x.2.2 : ℂ) :=
      Complex.continuous_ofReal.comp (continuous_diskOneCoord.comp
        (continuous_snd.comp continuous_snd))
    have he : Continuous fun x : I × (PUnit.{1} × TopCat.disk.{0} 1) ↦
        (Circle.exp (2 * π * x.1) : ℂ) :=
      continuous_subtypeVal.comp (Circle.exp.continuous.comp
        (continuous_const.mul (continuous_subtypeVal.comp continuous_fst)))
    exact ((continuous_const.sub hc).div_const _).mul he |>.add
      ((continuous_const.add hc).div_const _)
  map_zero_left _ := by
    simp only [Icc.coe_zero, mul_zero, Circle.exp_zero, Circle.coe_one]
    simp only [basepointCharMap, ContinuousMap.const_apply]
    ring
  map_one_left _ := by
    simp only [Icc.coe_one, mul_one, Circle.exp_two_pi, Circle.coe_one]
    simp only [basepointCharMap, ContinuousMap.comp_apply, ContinuousMap.const_apply]
    ring

/-- The constant homotopy at `1`. -/
private def constHomotopy (i : PUnit.{1}) :
    (basepointCharMap i).Homotopy
      ((basepointCharMap i).comp (ContinuousMap.fst.prodMk (diskOneId i))) where
  toFun _ := 1
  map_zero_left _ := (rfl)
  map_one_left _ := (rfl)

private theorem constHomotopy_apply (i : PUnit.{1}) (x : I × (PUnit.{1} × TopCat.disk.{0} 1)) :
    constHomotopy i x = 1 :=
  (rfl)

private theorem windingHomotopy_apply (i : PUnit.{1}) (t : I) (p : PUnit.{1})
    (w : TopCat.disk.{0} 1) :
    windingHomotopy i (t, (p, w)) =
      (1 - diskOneCoord w) / 2 * (Circle.exp (2 * π * t) : ℂ) + (1 + diskOneCoord w) / 2 :=
  (rfl)

/-- At the end `-1` the winding homotopy runs once around the unit circle. -/
private theorem windingHomotopy_of_diskOneCoord_eq_neg_one (i : PUnit.{1}) (t : I)
    (p : PUnit.{1}) {w : TopCat.disk.{0} 1} (hw : diskOneCoord w = -1) :
    windingHomotopy i (t, (p, w)) = Circle.exp (2 * π * t) := by
  rw [windingHomotopy_apply, hw]
  push_cast
  ring

/-- At the end `+1` the winding homotopy is constant at `1`. -/
private theorem windingHomotopy_of_diskOneCoord_eq_one (i : PUnit.{1}) (t : I)
    (p : PUnit.{1}) {w : TopCat.disk.{0} 1} (hw : diskOneCoord w = 1) :
    windingHomotopy i (t, (p, w)) = 1 := by
  rw [windingHomotopy_apply, hw]
  push_cast
  ring

/-- The homotopies of the constant characteristic map `1` to itself on the `1`-disk. -/
private abbrev LoopHomotopy : Type :=
  ∀ i, (basepointCharMap i).Homotopy
    ((basepointCharMap i).comp (ContinuousMap.fst.prodMk (diskOneId i)))

/-- A homotopy in `LoopHomotopy` keeps the ends of the disc on the unit circle. -/
private abbrev BoundaryOnCircle (K : LoopHomotopy) : Prop :=
  ∀ (i : PUnit.{1}) (t : I) (p : PUnit.{1}) (s : TopCat.diskBoundary.{0} 1),
    K i (t, (p, TopCat.diskBoundaryInclusion 1 s)) ∈ sphere (0 : ℂ) 1

private theorem windingHomotopy_mem : BoundaryOnCircle windingHomotopy := by
  intro i t p s
  rcases eq_sphereMinus_or_eq_spherePlus s with rfl | rfl
  · rw [windingHomotopy_of_diskOneCoord_eq_neg_one i t p sphereMinus_coord]
    exact (Circle.exp _).property
  · rw [windingHomotopy_of_diskOneCoord_eq_one i t p spherePlus_coord]
    simp

private theorem constHomotopy_mem : BoundaryOnCircle constHomotopy := by
  intro i t p s
  simp [constHomotopy_apply]

/-- The retraction of the wedge of two circles onto the unit circle collapsing the new cell. -/
private def collapseCell : fiberwiseCellAttachment basepointAttachingMap ⟶ TopCat.of Circle :=
  fiberwiseCellAttachmentDesc basepointAttachingMap
    (TopCat.ofHom ⟨fun x ↦ ⟨x.2.val, x.2.property⟩, by fun_prop⟩)
    (fun _ ↦ TopCat.ofHom (ContinuousMap.const _ (1 : Circle))) fun _ _ _ ↦ (rfl)

private theorem coe_collapseCell_incl (x : PUnit.{1} × sphere (0 : ℂ) 1) :
    (collapseCell (fiberwiseCellAttachmentIncl basepointAttachingMap x) : ℂ) = x.2 :=
  congrArg Subtype.val (fiberwiseCellAttachmentDesc_fiberwiseCellAttachmentIncl _ _ _ _ x)

private theorem collapseCell_cell (x : PUnit.{1} × TopCat.disk.{0} 1) :
    collapseCell (fiberwiseCellAttachmentCell basepointAttachingMap PUnit.unit x) = (1 : Circle) :=
  fiberwiseCellAttachmentDesc_fiberwiseCellAttachmentCell basepointAttachingMap _ _ _ PUnit.unit x

/-- The base point `1` of the unit circle, over the point. -/
private def basepoint : PUnit.{1} × sphere (0 : ℂ) 1 :=
  (PUnit.unit, ⟨1, by simp⟩)

/-- The new cell, run along its diameter `TauCeti.diskSegment` from `-1` to `+1`. -/
private def cellDiameter : C(I, fiberwiseCellAttachment basepointAttachingMap) :=
  (fiberwiseCellAttachmentCell basepointAttachingMap PUnit.unit).hom.comp
    ((ContinuousMap.const I PUnit.unit).prodMk diskSegment.toContinuousMap)

private theorem cellDiameter_apply (t : I) :
    cellDiameter t = fiberwiseCellAttachmentCell basepointAttachingMap PUnit.unit
      (PUnit.unit, diskSegment.{0} t) :=
  (rfl)

private theorem cellDiameter_zero :
    cellDiameter 0 = fiberwiseCellAttachmentIncl basepointAttachingMap basepoint := by
  rw [cellDiameter_apply, diskSegment.source]
  exact fiberwiseCellAttachmentCell_diskBoundaryInclusion _ _ _ _

private theorem cellDiameter_one :
    cellDiameter 1 = fiberwiseCellAttachmentIncl basepointAttachingMap basepoint := by
  rw [cellDiameter_apply, diskSegment.target]
  exact fiberwiseCellAttachmentCell_diskBoundaryInclusion _ _ _ _

/-- The reattachment map of the example for a homotopy `K` keeping the ends of the disc on the unit
circle. -/
private def exampleReattachment (K : LoopHomotopy) (hK : BoundaryOnCircle K) :
    fiberwiseCellAttachment basepointAttachingMap ⟶ fiberwiseCellAttachment basepointAttachingMap :=
  fiberwiseCellReattachment basepointAttachingMap basepointAttachingMap basepointCharMap
    basepointCharMap basepointCharMap_diskBoundaryInclusion basepointCharMap_diskBoundaryInclusion
    diskOneId mapsTo_diskOneId K hK

/-- The reattachment map of the example fixes the attached circle. -/
private theorem exampleReattachment_incl (K : LoopHomotopy) (hK : BoundaryOnCircle K)
    (x : PUnit.{1} × sphere (0 : ℂ) 1) :
    exampleReattachment K hK (fiberwiseCellAttachmentIncl basepointAttachingMap x) =
      fiberwiseCellAttachmentIncl basepointAttachingMap x :=
  fiberwiseCellReattachment_fiberwiseCellAttachmentIncl basepointAttachingMap basepointAttachingMap
    basepointCharMap basepointCharMap basepointCharMap_diskBoundaryInclusion
    basepointCharMap_diskBoundaryInclusion diskOneId mapsTo_diskOneId K hK x

/-- On the inner half of the cell the reattachment map of the example stays in the cell. -/
private theorem exampleReattachment_cell_of_norm_le (K : LoopHomotopy) (hK : BoundaryOnCircle K)
    {w : TopCat.disk.{0} 1} (hw : ‖w.down.val‖ ≤ 1 / 2) :
    exampleReattachment K hK (fiberwiseCellAttachmentCell basepointAttachingMap PUnit.unit
        (PUnit.unit, w)) =
      fiberwiseCellAttachmentCell basepointAttachingMap PUnit.unit
        (PUnit.unit, TopCat.reattachmentRadial w) :=
  fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_norm_le basepointAttachingMap
    basepointAttachingMap basepointCharMap basepointCharMap basepointCharMap_diskBoundaryInclusion
    basepointCharMap_diskBoundaryInclusion diskOneId mapsTo_diskOneId K hK PUnit.unit PUnit.unit hw
    (TopCat.coe_reattachmentRadial_of_norm_le hw)

/-- On the outer annulus of the cell the reattachment map of the example reads `K` on the
boundary. -/
private theorem exampleReattachment_cell_of_le_norm (K : LoopHomotopy) (hK : BoundaryOnCircle K)
    {w : TopCat.disk.{0} 1} (hw : 1 / 2 ≤ ‖w.down.val‖) :
    exampleReattachment K hK (fiberwiseCellAttachmentCell basepointAttachingMap PUnit.unit
        (PUnit.unit, w)) =
      fiberwiseCellAttachmentIncl basepointAttachingMap (PUnit.unit,
        ⟨K PUnit.unit (TopCat.reattachmentTime w, (PUnit.unit, TopCat.diskBoundaryInclusion 1
          (TopCat.annulusDir (by norm_num : (0 : ℝ) < 1 / 2) ⟨w, hw⟩))), hK _ _ _ _⟩) :=
  fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_le_norm basepointAttachingMap
    basepointAttachingMap basepointCharMap basepointCharMap basepointCharMap_diskBoundaryInclusion
    basepointCharMap_diskBoundaryInclusion diskOneId mapsTo_diskOneId K hK PUnit.unit PUnit.unit hw
    (TopCat.coe_reattachmentTime_of_le_norm hw)
    (TopCat.coe_annulusDir (by norm_num : (0 : ℝ) < 1 / 2) ⟨w, hw⟩)

/-- The reattachment map fixes the base point of the attachment, which collapses to `1`. -/
private theorem collapseCell_exampleReattachment_incl (K : LoopHomotopy) (hK : BoundaryOnCircle K) :
    collapseCell (exampleReattachment K hK
      (fiberwiseCellAttachmentIncl basepointAttachingMap basepoint)) = (1 : Circle) := by
  rw [exampleReattachment_incl]
  exact Circle.ext (coe_collapseCell_incl basepoint)

/-- The loop in the unit circle traced by the collapsed image of the diameter of the new cell under
the reattachment map of `K`. -/
private def reattachmentLoop (K : LoopHomotopy) (hK : BoundaryOnCircle K) :
    Path (1 : Circle) 1 where
  toContinuousMap := collapseCell.hom.comp ((exampleReattachment K hK).hom.comp cellDiameter)
  source' := (congrArg (fun y ↦ collapseCell (exampleReattachment K hK y)) cellDiameter_zero).trans
    (collapseCell_exampleReattachment_incl K hK)
  target' := (congrArg (fun y ↦ collapseCell (exampleReattachment K hK y)) cellDiameter_one).trans
    (collapseCell_exampleReattachment_incl K hK)

private theorem reattachmentLoop_toContinuousMap (K : LoopHomotopy) (hK : BoundaryOnCircle K) :
    (reattachmentLoop K hK).toContinuousMap =
      collapseCell.hom.comp ((exampleReattachment K hK).hom.comp cellDiameter) :=
  (rfl)

private theorem reattachmentLoop_apply (K : LoopHomotopy) (hK : BoundaryOnCircle K) (t : I) :
    reattachmentLoop K hK t = collapseCell (exampleReattachment K hK (cellDiameter t)) :=
  (rfl)

/-- On the inner half of the diameter the collapsed reattachment map is `1`. -/
private theorem reattachmentLoop_of_norm_le (K : LoopHomotopy) (hK : BoundaryOnCircle K) {t : I}
    (ht : ‖(diskSegment.{0} t : TopCat.disk.{0} 1).down.val‖ ≤ 1 / 2) :
    reattachmentLoop K hK t = 1 := by
  rw [reattachmentLoop_apply, cellDiameter_apply, exampleReattachment_cell_of_norm_le K hK ht,
    collapseCell_cell]

/-- On the outer half of the diameter the collapsed reattachment map reads `K` on the boundary. -/
private theorem coe_reattachmentLoop_of_le_norm (K : LoopHomotopy) (hK : BoundaryOnCircle K) {t : I}
    (ht : 1 / 2 ≤ ‖(diskSegment.{0} t : TopCat.disk.{0} 1).down.val‖) :
    (reattachmentLoop K hK t : ℂ) = K PUnit.unit (TopCat.reattachmentTime (diskSegment.{0} t),
      (PUnit.unit, TopCat.diskBoundaryInclusion 1
        (TopCat.annulusDir (by norm_num : (0 : ℝ) < 1 / 2) ⟨diskSegment.{0} t, ht⟩))) := by
  rw [reattachmentLoop_apply, cellDiameter_apply, exampleReattachment_cell_of_le_norm K hK ht]
  exact coe_collapseCell_incl _

/-- The constant homotopy gives the constant loop. -/
private theorem degree_reattachmentLoop_constHomotopy :
    Circle.degree (reattachmentLoop constHomotopy constHomotopy_mem) = 0 := by
  refine (Circle.degree_congr _ (Path.refl 1) fun t ↦ ?_).trans (Circle.degree_refl 1)
  rcases le_total ‖(diskSegment.{0} t : TopCat.disk.{0} 1).down.val‖ (1 / 2) with ht | ht
  · exact reattachmentLoop_of_norm_le _ _ ht
  · exact Circle.ext ((coe_reattachmentLoop_of_le_norm _ _ ht).trans
      (constHomotopy_apply _ _))

/-- The winding homotopy gives a loop of degree `1`: it is `e^{2πi · 4t}` for `t ≤ 1/4` and `1`
afterwards. -/
private theorem degree_reattachmentLoop_windingHomotopy :
    Circle.degree (reattachmentLoop windingHomotopy windingHomotopy_mem) = 1 := by
  refine Circle.degree_eq_of_sub_eq _ (θ := fun t : I ↦ 2 * π * min (4 * (t : ℝ)) 1)
    (by fun_prop) (fun t ↦ ?_) (by simp)
  have hc : diskOneCoord (diskSegment.{0} t) = 2 * (t : ℝ) - 1 := diskSegment_coord t
  rcases le_total (t : ℝ) (1 / 4) with ht | ht
  · -- On the first quarter the diameter is in the outer half on the side of `-1`.
    have hn : 1 / 2 ≤ ‖(diskSegment.{0} t : TopCat.disk.{0} 1).down.val‖ := by
      rw [norm_diskSegment, abs_of_neg (by linarith)]
      linarith
    refine Circle.ext ((coe_reattachmentLoop_of_le_norm _ _ hn).trans ?_).symm
    have hneg : diskOneCoord (diskSegment.{0} t) < 0 := by rw [hc]; linarith
    rw [windingHomotopy_of_diskOneCoord_eq_neg_one (hw := by
      rw [diskOneCoord, TopCat.coe_diskBoundaryInclusion_apply_down,
        TopCat.annulusDir_down_apply_zero, diskSegment_coord, ← hc, abs_of_neg hneg, inv_neg,
        neg_mul, inv_mul_cancel₀ hneg.ne]),
      min_eq_left (by linarith)]
    congr 3
    rw [TopCat.coe_reattachmentTime_of_le_norm hn, norm_diskSegment, abs_of_neg (by linarith)]
    ring
  · rw [min_eq_right (by linarith), mul_one, Circle.exp_two_pi]
    rcases le_or_gt ‖(diskSegment.{0} t : TopCat.disk.{0} 1).down.val‖ (1 / 2) with hn | hn
    · exact (reattachmentLoop_of_norm_le _ _ hn).symm
    · -- Past the first quarter, the outer half lies on the side of `+1`.
      have hpos : 0 < diskOneCoord (diskSegment.{0} t) := by
        rw [norm_diskSegment] at hn
        rw [hc]
        rcases abs_cases (2 * (t : ℝ) - 1) with ⟨h, -⟩ | ⟨h, -⟩ <;> linarith
      refine Circle.ext ((coe_reattachmentLoop_of_le_norm _ _ hn.le).trans ?_).symm
      rw [windingHomotopy_of_diskOneCoord_eq_one (hw := by
        rw [diskOneCoord, TopCat.coe_diskBoundaryInclusion_apply_down,
          TopCat.annulusDir_down_apply_zero, diskSegment_coord, ← hc, abs_of_pos hpos,
          inv_mul_cancel₀ hpos.ne']),
        Circle.coe_one]

/-- **The reattachment class depends on the boundary homotopy.** Attach one `1`-cell at both ends
to the point `1` of the unit circle `A` in `Y = ℂ`, with constant characteristic maps and the
identity of the disc. The reattachment maps `E` and `E'` of the homotopy winding once around `A` at
the end `-1` and of the constant homotopy are self-maps of the same attachment, the wedge of two
circles, but they are not homotopic relative to `A`. Since the reattachment map depends on the
homotopies only through their restrictions to the boundary spheres
(`TauCeti.fiberwiseCellReattachment_congr`), this shows that the homotopy class of a reattachment
map is not determined by the attaching maps and the disc self-maps: it depends on the boundary
homotopy. -/
theorem exists_not_homotopicRel_fiberwiseCellReattachment_fiberwiseCellReattachment :
    ∃ (α : ∀ _ : PUnit.{1}, C(PUnit.{1} × TopCat.diskBoundary.{0} 1, sphere (0 : ℂ) 1))
      (χ : ∀ _ : PUnit.{1}, C(PUnit.{1} × TopCat.disk.{0} 1, ℂ))
      (hχ : ∀ i p s, χ i (p, TopCat.diskBoundaryInclusion 1 s) = α i (p, s))
      (h : ∀ _ : PUnit.{1}, C(PUnit.{1} × TopCat.disk.{0} 1, TopCat.disk.{0} 1))
      (hh : ∀ i p, MapsTo (fun w ↦ h i (p, w)) (range (TopCat.diskBoundaryInclusion 1))
        (range (TopCat.diskBoundaryInclusion 1)))
      (K K' : ∀ i, (χ i).Homotopy ((χ i).comp (ContinuousMap.fst.prodMk (h i))))
      (hK : ∀ i t p s, K i (t, (p, TopCat.diskBoundaryInclusion 1 s)) ∈ sphere (0 : ℂ) 1)
      (hK' : ∀ i t p s, K' i (t, (p, TopCat.diskBoundaryInclusion 1 s)) ∈ sphere (0 : ℂ) 1),
      ¬ (fiberwiseCellReattachment α α χ χ hχ hχ h hh K hK).hom.HomotopicRel
        (fiberwiseCellReattachment α α χ χ hχ hχ h hh K' hK').hom
        (range (fiberwiseCellAttachmentIncl α)) := by
  refine ⟨basepointAttachingMap, basepointCharMap, basepointCharMap_diskBoundaryInclusion,
    diskOneId, mapsTo_diskOneId, windingHomotopy, constHomotopy, windingHomotopy_mem,
    constHomotopy_mem, fun hG ↦ ?_⟩
  -- The diameter of the new cell has its ends in `A`, so a homotopy relative to `A` gives a
  -- homotopy of the collapsed loops relative to their endpoints.
  have hends : ({0, 1} : Set I) ⊆ cellDiameter ⁻¹' range (fiberwiseCellAttachmentIncl _) := by
    rintro t (rfl | rfl)
    · exact ⟨_, cellDiameter_zero.symm⟩
    · exact ⟨_, cellDiameter_one.symm⟩
  have hrel : (reattachmentLoop windingHomotopy windingHomotopy_mem).toContinuousMap.HomotopicRel
      (reattachmentLoop constHomotopy constHomotopy_mem).toContinuousMap {0, 1} := by
    rw [reattachmentLoop_toContinuousMap, reattachmentLoop_toContinuousMap]
    exact ((ContinuousMap.HomotopicRel.precomp hG cellDiameter).mono hends).comp_continuousMap
      collapseCell.hom
  -- A `Path.Homotopy` is by definition a homotopy of the underlying maps relative to `{0, 1}`, so
  -- a homotopy relative to `{0, 1}` of the underlying maps of two paths makes them homotopic.
  have hloop : (reattachmentLoop windingHomotopy windingHomotopy_mem).Homotopic
      (reattachmentLoop constHomotopy constHomotopy_mem) :=
    ⟨hrel.some⟩
  have := Circle.degree_eq_of_homotopic hloop
  rw [degree_reattachmentLoop_windingHomotopy, degree_reattachmentLoop_constHomotopy] at this
  exact one_ne_zero this

end Example

end TauCeti
