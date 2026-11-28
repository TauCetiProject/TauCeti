/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Topology.Homotopy.Path
public import TauCeti.AlgebraicTopology.Disk
public import TauCeti.Topology.CWComplex.Abstract.FiberwiseCell.Attachment
import TauCeti.Analysis.Complex.Circle.Basic
import TauCeti.Analysis.InnerProductSpace.PiL2
import TauCeti.Topology.Circle.Degree
import TauCeti.Topology.Homotopy.Homotopic.Rel

/-!
# Reattachment maps of boundary homotopies

Milnor's comparison of two cell attachments `A ∪_{α₁} D^k` and `A ∪_{α₀} D^k`
(`TauCeti.fiberwiseCellReattachment`) is built from a self-map `h` of the disc pair and a homotopy
`K : χ₁ ≃ χ₀ ∘ h` of characteristic maps keeping the boundary sphere in `A`. The map itself only
reads `K` on the boundary sphere, that is, it only depends on the *boundary homotopy*
`H = K|∂D^k : α₁ ≃ α₀ ∘ h` in `A` (`TauCeti.fiberwiseCellReattachment_eq_of_forall_eq`). When the
comparison map of the target attachment has a left homotopy inverse, as for the cells of a Morse
function, the relative homotopy class of the reattachment map does not depend on `K`
(`TauCeti.exists_homotopyRel_fiberwiseCellReattachment_fiberwiseCellReattachment`).

In general the class depends on the boundary homotopy `H` itself, and not only on its endpoints
`α₁` and `α₀ ∘ h`. Attach one arc `D¹` at both of its ends to a point `a` of `A`, and read a
homotopy `K` on the two ends `-1` and `1` of the arc: the tracks `H₋ = K(·, -1)` and
`H₊ = K(·, 1)` are loops at `a` in `A` (`TauCeti.arcBoundaryTrack`). Collapsing the arc to `a`
retracts the attachment onto `A`, and the retraction of the reattachment map, read along the arc,
is the loop `H₋ · H₊⁻¹` up to reparametrization. A homotopy relative to `A` between two
reattachment maps therefore gives a homotopy of loops between their loops `H₋ · H₊⁻¹`
(`TauCeti.homotopic_arcBoundaryTrack_trans_symm_of_homotopicRel_fiberwiseCellReattachment`).
So the independence of `K` rests on the left homotopy inverse of the comparison map, which for the
cells of a Morse function is Milnor's cell attachment theorem; without it the class can change
with the boundary homotopy, as the following example shows.

For `A` the unit circle in `ℂ`, characteristic maps constant at `1` and `h = id`, every boundary
homotopy extends to `ℂ` by the straight-line homotopy. The constant boundary homotopy and the one
whose end `1` runs once around the circle have the same endpoints, but their loops have degrees
`0` and `-1`, so their reattachment maps are not homotopic relative to the circle
(`TauCeti.exists_not_homotopicRel_fiberwiseCellReattachment_sphere`).

## Main results

* `TauCeti.fiberwiseCellReattachment_eq_of_forall_eq`: two reattachment maps whose homotopies
  agree on the boundary spheres are equal.
* `TauCeti.homotopic_arcBoundaryTrack_trans_symm_of_homotopicRel_fiberwiseCellReattachment`: for
  an arc attached at both ends to `a`, the reattachment class relative to `A` determines the
  homotopy class of the loop `H₋ · H₊⁻¹` of the boundary homotopy.
* `TauCeti.exists_not_homotopicRel_fiberwiseCellReattachment_sphere`: two homotopies of
  characteristic maps with the same endpoints whose reattachment maps are not homotopic relative to
  the lower space.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Lemma 3.6.
-/

public section

noncomputable section

open CategoryTheory Set Metric unitInterval

universe u

namespace TauCeti

section BoundaryHomotopy

variable {P Y : Type u} [TopologicalSpace P] [TopologicalSpace Y] {A : Set Y} {ι : Type u}
  {k : ι → ℕ} (α₀ α₁ : ∀ i, C(P × TopCat.diskBoundary.{u} (k i), A))
  {χ₀ χ₁ χ₀' χ₁' : ∀ i, C(P × TopCat.disk.{u} (k i), Y)}
  (hχ₀ : ∀ i p s, χ₀ i (p, TopCat.diskBoundaryInclusion (k i) s) = α₀ i (p, s))
  (hχ₁ : ∀ i p s, χ₁ i (p, TopCat.diskBoundaryInclusion (k i) s) = α₁ i (p, s))
  (hχ₀' : ∀ i p s, χ₀' i (p, TopCat.diskBoundaryInclusion (k i) s) = α₀ i (p, s))
  (hχ₁' : ∀ i p s, χ₁' i (p, TopCat.diskBoundaryInclusion (k i) s) = α₁ i (p, s))
  (h : ∀ i, C(P × TopCat.disk.{u} (k i), TopCat.disk.{u} (k i)))
  (hh : ∀ i p, MapsTo (fun w ↦ h i (p, w)) (range (TopCat.diskBoundaryInclusion (k i)))
    (range (TopCat.diskBoundaryInclusion (k i))))
  {K : ∀ i, (χ₁ i).Homotopy ((χ₀ i).comp (ContinuousMap.fst.prodMk (h i)))}
  {K' : ∀ i, (χ₁' i).Homotopy ((χ₀' i).comp (ContinuousMap.fst.prodMk (h i)))}
  (hK : ∀ i t p s, K i (t, (p, TopCat.diskBoundaryInclusion (k i) s)) ∈ A)
  (hK' : ∀ i t p s, K' i (t, (p, TopCat.diskBoundaryInclusion (k i) s)) ∈ A)

/-- **The reattachment map only depends on the boundary homotopy.** Two fiberwise reattachment maps
between the same attachments, with the same self-maps `h i` of the discs, are equal as soon as
their homotopies of characteristic maps agree on the boundary spheres; the characteristic maps
themselves may differ. -/
theorem fiberwiseCellReattachment_eq_of_forall_eq
    (hKK' : ∀ i t p s, K i (t, (p, TopCat.diskBoundaryInclusion (k i) s)) =
      K' i (t, (p, TopCat.diskBoundaryInclusion (k i) s))) :
    fiberwiseCellReattachment α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h hh K hK =
      fiberwiseCellReattachment α₀ α₁ χ₀' χ₁' hχ₀' hχ₁' h hh K' hK' := by
  refine fiberwiseCellAttachment_hom_ext α₁ (fun x ↦ by
    rw [fiberwiseCellReattachment_fiberwiseCellAttachmentIncl,
      fiberwiseCellReattachment_fiberwiseCellAttachmentIncl]) fun i ⟨p, w⟩ ↦ ?_
  rcases le_total ‖w.down.val‖ (1 / 2) with hw | hw
  · rw [fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_norm_le (hw := hw)
        (hv := TopCat.coe_reattachmentRadial_of_norm_le hw),
      fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_norm_le (hw := hw)
        (hv := TopCat.coe_reattachmentRadial_of_norm_le hw)]
  · rw [fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_le_norm (hw := hw)
        (ht := TopCat.coe_reattachmentTime_of_le_norm hw)
        (hs := TopCat.coe_annulusDir (by norm_num) ⟨w, hw⟩),
      fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_le_norm (hw := hw)
        (ht := TopCat.coe_reattachmentTime_of_le_norm hw)
        (hs := TopCat.coe_annulusDir (by norm_num) ⟨w, hw⟩)]
    exact congrArg _ (Prod.ext rfl (Subtype.ext (hKK' i _ p _)))

end BoundaryHomotopy

section Arc

variable {Y : Type u} [TopologicalSpace Y] {A : Set Y} (a : A)
  {χ₀ χ₁ : C(PUnit.{u + 1} × TopCat.disk.{u} 1, Y)}
  (hχ₀ : ∀ p s, χ₀ (p, TopCat.diskBoundaryInclusion 1 s) = a)
  (hχ₁ : ∀ p s, χ₁ (p, TopCat.diskBoundaryInclusion 1 s) = a)
  {h : C(PUnit.{u + 1} × TopCat.disk.{u} 1, TopCat.disk.{u} 1)}
  (hh : ∀ p, MapsTo (fun w ↦ h (p, w)) (range (TopCat.diskBoundaryInclusion 1))
    (range (TopCat.diskBoundaryInclusion 1)))
  {K : χ₁.Homotopy (χ₀.comp (ContinuousMap.fst.prodMk h))}
  (hK : ∀ t p s, K (t, (p, TopCat.diskBoundaryInclusion 1 s)) ∈ A)

/-- The **track** `t ↦ K (t, s)` in `A` of the point `s` of the boundary `S⁰` of an arc attached
at both ends to `a`, under a homotopy `K : χ₁ ≃ χ₀ ∘ h` of characteristic maps keeping `S⁰` in
`A`. It is a loop at `a`: it starts at `χ₁ s = a` and ends at `χ₀ (h s) = a`, because `h`
preserves `S⁰`. -/
def arcBoundaryTrack (s : TopCat.diskBoundary.{u} 1) : Path a a where
  toFun t := ⟨K (t, (PUnit.unit, TopCat.diskBoundaryInclusion 1 s)), hK t _ s⟩
  continuous_toFun := (K.continuous.comp (continuous_id.prodMk continuous_const)).subtype_mk _
  source' := Subtype.ext ((K.apply_zero _).trans (hχ₁ _ s))
  target' := by
    obtain ⟨s', hs'⟩ := hh PUnit.unit ⟨s, rfl⟩
    refine Subtype.ext ((K.apply_one _).trans ?_)
    rw [ContinuousMap.comp_apply, ContinuousMap.prod_eval, ContinuousMap.fst_apply]
    exact (congrArg (fun w ↦ χ₀ (PUnit.unit, w)) hs').symm.trans (hχ₀ _ s')

@[simp]
theorem coe_arcBoundaryTrack_apply (s : TopCat.diskBoundary.{u} 1) (t : I) :
    (arcBoundaryTrack a hχ₀ hχ₁ hh hK s t : Y) =
      K (t, (PUnit.unit, TopCat.diskBoundaryInclusion 1 s)) :=
  (rfl)

/-- The retraction of the attachment of an arc at both ends to `a` onto `A`, collapsing the arc to
`a`. -/
private def arcRetraction :
    fiberwiseCellAttachment (k := fun _ : PUnit.{u + 1} ↦ 1)
      (fun _ ↦ ContinuousMap.const (PUnit.{u + 1} × TopCat.diskBoundary.{u} 1) a) ⟶ TopCat.of A :=
  fiberwiseCellAttachmentDesc _ (TopCat.ofHom ContinuousMap.snd)
    (fun _ ↦ TopCat.ofHom (ContinuousMap.const _ a)) fun _ _ _ ↦ rfl

/-- The arc `t ↦ 2t - 1`, as a path in the attachment from its end `-1` to its end `1`. -/
private def arcPath :
    C(I, fiberwiseCellAttachment (k := fun _ : PUnit.{u + 1} ↦ 1)
      (fun _ ↦ ContinuousMap.const (PUnit.{u + 1} × TopCat.diskBoundary.{u} 1) a)) :=
  (fiberwiseCellAttachmentCell _ PUnit.unit).hom.comp
    ⟨fun t ↦ (PUnit.unit, diskSegment t), continuous_const.prodMk diskSegment.continuous⟩

/-- The reparametrization `t ↦ min (2t) (max (1/2) (2t - 1))` of the unit interval: it runs the
first half on `[0, 1/4]`, rests at `1/2` on `[1/4, 3/4]` and runs the second half on `[3/4, 1]`. -/
private def arcReparam (t : I) : I :=
  ⟨min (2 * t) (max (1 / 2) (2 * t - 1)),
    le_min (mul_nonneg zero_le_two t.property.1) (le_max_of_le_left (by norm_num)),
    min_le_of_right_le (max_le (by norm_num) (by linarith [t.property.2]))⟩

private theorem continuous_arcReparam : Continuous arcReparam :=
  Continuous.subtype_mk (by fun_prop) _

private theorem arcReparam_zero : arcReparam 0 = 0 :=
  Subtype.ext (by norm_num [arcReparam])

private theorem arcReparam_one : arcReparam 1 = 1 :=
  Subtype.ext (by norm_num [arcReparam])

private theorem arcRetraction_fiberwiseCellAttachmentCell (x) :
    arcRetraction a (fiberwiseCellAttachmentCell _ PUnit.unit x) = a :=
  ConcreteCategory.congr_hom (fiberwiseCellAttachmentCell_desc (k := fun _ : PUnit.{u + 1} ↦ 1)
    (fun _ ↦ ContinuousMap.const (PUnit.{u + 1} × TopCat.diskBoundary.{u} 1) a)
    (TopCat.ofHom ContinuousMap.snd)
    (fun _ ↦ TopCat.ofHom (ContinuousMap.const (PUnit.{u + 1} × TopCat.disk.{u} 1) a))
    (fun _ _ _ ↦ rfl) PUnit.unit) x

private theorem arcRetraction_fiberwiseCellAttachmentIncl (x : PUnit.{u + 1} × A) :
    arcRetraction a (fiberwiseCellAttachmentIncl _ x) = x.2 :=
  ConcreteCategory.congr_hom (fiberwiseCellAttachmentIncl_desc _ _ _ _) x

/-- On the disc of radius `1/2`, collapsing the arc after the reattachment map gives `a`. -/
private theorem arcRetraction_fiberwiseCellReattachment_of_norm_le {w : TopCat.disk.{u} 1}
    (hw : ‖w.down.val‖ ≤ 1 / 2) :
    arcRetraction a (fiberwiseCellReattachment (fun _ ↦ ContinuousMap.const _ a)
      (fun _ ↦ ContinuousMap.const _ a) (fun _ ↦ χ₀) (fun _ ↦ χ₁) (fun _ ↦ hχ₀) (fun _ ↦ hχ₁)
      (fun _ ↦ h) (fun _ ↦ hh) (fun _ ↦ K) (fun _ ↦ hK)
        (fiberwiseCellAttachmentCell _ PUnit.unit (PUnit.unit, w))) = a := by
  rw [fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_norm_le (fun _ ↦ .const _ a)
    (fun _ ↦ .const _ a) (fun _ ↦ χ₀) (fun _ ↦ χ₁) (fun _ ↦ hχ₀) (fun _ ↦ hχ₁) (fun _ ↦ h)
    (fun _ ↦ hh) (fun _ ↦ K) (fun _ ↦ hK) PUnit.unit PUnit.unit hw
    (TopCat.coe_reattachmentRadial_of_norm_le hw), arcRetraction_fiberwiseCellAttachmentCell]

/-- On the annulus `1/2 ≤ ‖w‖`, collapsing the arc after the reattachment map reads the boundary
homotopy at the time `2 - 2‖w‖` and the end `s = w / ‖w‖`. -/
private theorem coe_arcRetraction_fiberwiseCellReattachment_of_le_norm {w : TopCat.disk.{u} 1}
    (hw : 1 / 2 ≤ ‖w.down.val‖) {s : TopCat.diskBoundary.{u} 1}
    (hs : s.down.val = ‖w.down.val‖⁻¹ • w.down.val) :
    (arcRetraction a (fiberwiseCellReattachment (fun _ ↦ ContinuousMap.const _ a)
      (fun _ ↦ ContinuousMap.const _ a) (fun _ ↦ χ₀) (fun _ ↦ χ₁) (fun _ ↦ hχ₀) (fun _ ↦ hχ₁)
      (fun _ ↦ h) (fun _ ↦ hh) (fun _ ↦ K) (fun _ ↦ hK)
        (fiberwiseCellAttachmentCell _ PUnit.unit (PUnit.unit, w))) : Y) =
      K (TopCat.reattachmentTime w, (PUnit.unit, TopCat.diskBoundaryInclusion 1 s)) := by
  rw [fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_le_norm (fun _ ↦ .const _ a)
    (fun _ ↦ .const _ a) (fun _ ↦ χ₀) (fun _ ↦ χ₁) (fun _ ↦ hχ₀) (fun _ ↦ hχ₁) (fun _ ↦ h)
    (fun _ ↦ hh) (fun _ ↦ K) (fun _ ↦ hK) PUnit.unit PUnit.unit hw
    (TopCat.coe_reattachmentTime_of_le_norm hw) hs, arcRetraction_fiberwiseCellAttachmentIncl]

variable {a hχ₀ hχ₁ hh hK} in
/-- Collapsing the arc after the reattachment map, along the arc, is the loop `H₋ · H₊⁻¹` read
along `arcReparam`. -/
private theorem arcRetraction_comp_fiberwiseCellReattachment_comp_arcPath :
    ((arcRetraction a).hom.comp
        (fiberwiseCellReattachment (fun _ ↦ ContinuousMap.const _ a)
          (fun _ ↦ ContinuousMap.const _ a) (fun _ ↦ χ₀) (fun _ ↦ χ₁) (fun _ ↦ hχ₀)
          (fun _ ↦ hχ₁) (fun _ ↦ h) (fun _ ↦ hh) (fun _ ↦ K) (fun _ ↦ hK)).hom).comp
        (arcPath a) =
      (((arcBoundaryTrack a hχ₀ hχ₁ hh hK sphereMinus).trans
        (arcBoundaryTrack a hχ₀ hχ₁ hh hK spherePlus).symm).reparam arcReparam
          continuous_arcReparam arcReparam_zero arcReparam_one).toContinuousMap := by
  ext1 t
  have hw := norm_diskSegment.{u} t
  have hc := diskSegment_coord.{u} t
  simp only [ContinuousMap.comp_apply, arcPath, Path.coe_toContinuousMap, Path.coe_reparam,
    Function.comp_apply, ContinuousMap.coe_mk]
  rcases le_or_gt ‖(diskSegment.{u} t).down.val‖ (1 / 2) with hle | hlt
  · -- On `[1/4, 3/4]` the reattachment map stays in the cell, which collapses to `a`; there the
    -- loop rests at the end of `H₋`.
    have hg : (arcReparam t : ℝ) = 1 / 2 := by
      rw [hw, abs_le] at hle
      simp only [arcReparam]
      rw [max_eq_left (by linarith), min_eq_right (by linarith)]
    rw [arcRetraction_fiberwiseCellReattachment_of_norm_le a hχ₀ hχ₁ hh hK hle, Path.trans_apply,
      dite_eq_left hg.le]
    exact ((congrArg _ (Subtype.ext (by simp [hg]))).trans (Path.target _)).symm
  -- Near the ends of the arc the reattachment map runs along the boundary homotopy.
  have hne : (diskSegment.{u} t).down.val 0 ≠ 0 := fun h0 ↦ by
    rw [hw, ← hc, h0, abs_zero] at hlt
    norm_num at hlt
  have hle := hlt.le
  rw [hw] at hlt
  refine Subtype.ext ?_
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · -- On `[0, 1/4)` it runs along `H₋`.
    rw [hc] at hneg
    rw [abs_of_neg hneg] at hlt
    have hg : (arcReparam t : ℝ) = 2 * t := min_eq_left (le_max_of_le_left (by linarith))
    rw [coe_arcRetraction_fiberwiseCellReattachment_of_le_norm a hχ₀ hχ₁ hh hK hle
      (s := sphereMinus) (diskBoundary_one_eq_inv_norm_smul hne (by
        rw [sphereMinus_down_apply_zero, hc, abs_of_neg hneg]; ring)), Path.trans_apply,
      dite_eq_left (by rw [hg]; linarith)]
    refine congrArg (fun x ↦ K (x, _)) (Subtype.ext ?_)
    rw [TopCat.coe_reattachmentTime_of_le_norm hle, hw, abs_of_neg hneg]
    simp only [hg]
    ring
  · -- On `(3/4, 1]` it runs backwards along `H₊`.
    rw [hc] at hpos
    rw [abs_of_pos hpos] at hlt
    have hg : (arcReparam t : ℝ) = 2 * t - 1 :=
      (min_eq_right (max_le (by linarith) (by linarith))).trans (max_eq_right (by linarith))
    rw [coe_arcRetraction_fiberwiseCellReattachment_of_le_norm a hχ₀ hχ₁ hh hK hle
      (s := spherePlus) (diskBoundary_one_eq_inv_norm_smul hne (by
        rw [spherePlus_down_apply_zero, hc, abs_of_pos hpos]; ring)), Path.trans_apply,
      dite_eq_right (by rw [hg]; linarith), Path.symm_apply]
    refine congrArg (fun x ↦ K (x, _)) (Subtype.ext ?_)
    rw [TopCat.coe_reattachmentTime_of_le_norm hle, hw, abs_of_pos hpos, coe_symm_eq]
    simp only [hg]
    ring

/-- The ends of the arc lie in the lower space. -/
private theorem arcPath_mem_range_fiberwiseCellAttachmentIncl {t : I}
    (ht : t ∈ ({0, 1} : Set I)) :
    arcPath a t ∈ range (fiberwiseCellAttachmentIncl (k := fun _ : PUnit.{u + 1} ↦ 1)
      (fun _ ↦ ContinuousMap.const (PUnit.{u + 1} × TopCat.diskBoundary.{u} 1) a)) := by
  rcases ht with rfl | rfl
  · exact ⟨_, (fiberwiseCellAttachmentCell_diskBoundaryInclusion _ PUnit.unit PUnit.unit
      sphereMinus).symm.trans (congrArg (fun w ↦ fiberwiseCellAttachmentCell _ PUnit.unit
        (PUnit.unit, w)) diskSegment.source.symm)⟩
  · exact ⟨_, (fiberwiseCellAttachmentCell_diskBoundaryInclusion _ PUnit.unit PUnit.unit
      spherePlus).symm.trans (congrArg (fun w ↦ fiberwiseCellAttachmentCell _ PUnit.unit
        (PUnit.unit, w)) diskSegment.target.symm)⟩

/-- **The reattachment class of an arc determines the loop of its boundary homotopy.** Attach an
arc `D¹` at both of its ends to the point `a` of `A`, and let `K : χ₁ ≃ χ₀ ∘ h` and
`K' : χ₁' ≃ χ₀' ∘ h'` be homotopies of characteristic maps keeping the ends of the arc in `A`. If
their reattachment maps are homotopic relative to `A`, then the loops `H₋ · H₊⁻¹` read off their
boundary homotopies, the track of the end `-1` followed by the reversed track of the end `1`, are
homotopic loops at `a` in `A`. -/
theorem homotopic_arcBoundaryTrack_trans_symm_of_homotopicRel_fiberwiseCellReattachment
    {χ₀' χ₁' : C(PUnit.{u + 1} × TopCat.disk.{u} 1, Y)}
    (hχ₀' : ∀ p s, χ₀' (p, TopCat.diskBoundaryInclusion 1 s) = a)
    (hχ₁' : ∀ p s, χ₁' (p, TopCat.diskBoundaryInclusion 1 s) = a)
    {h' : C(PUnit.{u + 1} × TopCat.disk.{u} 1, TopCat.disk.{u} 1)}
    (hh' : ∀ p, MapsTo (fun w ↦ h' (p, w)) (range (TopCat.diskBoundaryInclusion 1))
      (range (TopCat.diskBoundaryInclusion 1)))
    {K' : χ₁'.Homotopy (χ₀'.comp (ContinuousMap.fst.prodMk h'))}
    (hK' : ∀ t p s, K' (t, (p, TopCat.diskBoundaryInclusion 1 s)) ∈ A)
    (hE : (fiberwiseCellReattachment (fun _ ↦ ContinuousMap.const _ a)
          (fun _ ↦ ContinuousMap.const _ a) (fun _ ↦ χ₀) (fun _ ↦ χ₁) (fun _ ↦ hχ₀)
          (fun _ ↦ hχ₁) (fun _ ↦ h) (fun _ ↦ hh) (fun _ ↦ K) (fun _ ↦ hK)).hom.HomotopicRel
        (fiberwiseCellReattachment (fun _ ↦ ContinuousMap.const _ a)
          (fun _ ↦ ContinuousMap.const _ a) (fun _ ↦ χ₀') (fun _ ↦ χ₁') (fun _ ↦ hχ₀')
          (fun _ ↦ hχ₁') (fun _ ↦ h') (fun _ ↦ hh') (fun _ ↦ K') (fun _ ↦ hK')).hom
        (range (fiberwiseCellAttachmentIncl (k := fun _ : PUnit.{u + 1} ↦ 1)
          (fun _ ↦ ContinuousMap.const (PUnit.{u + 1} × TopCat.diskBoundary.{u} 1) a)))) :
    ((arcBoundaryTrack a hχ₀ hχ₁ hh hK sphereMinus).trans
        (arcBoundaryTrack a hχ₀ hχ₁ hh hK spherePlus).symm).Homotopic
      ((arcBoundaryTrack a hχ₀' hχ₁' hh' hK' sphereMinus).trans
        (arcBoundaryTrack a hχ₀' hχ₁' hh' hK' spherePlus).symm) := by
  -- Collapse the arc and restrict to the arc itself: the two loops, read along `arcReparam`, are
  -- homotopic relative to the ends of the arc.
  have hF := ContinuousMap.HomotopicRel.mono (ContinuousMap.HomotopicRel.precomp
    (hE.comp_continuousMap (arcRetraction a).hom) (arcPath a))
    fun _ ↦ arcPath_mem_range_fiberwiseCellAttachmentIncl a
  rw [arcRetraction_comp_fiberwiseCellReattachment_comp_arcPath,
    arcRetraction_comp_fiberwiseCellReattachment_comp_arcPath] at hF
  exact (Path.Homotopic.trans ⟨Path.Homotopy.reparam _ _ continuous_arcReparam arcReparam_zero
    arcReparam_one⟩ hF).trans ⟨(Path.Homotopy.reparam _ _ continuous_arcReparam arcReparam_zero
      arcReparam_one).symm⟩

end Arc

section Circle

/-- The characteristic map of the arc that is constant at `1`. -/
private abbrev circleArcChar : C(PUnit.{1} × TopCat.disk.{0} 1, ℂ) := ContinuousMap.const _ 1

/-- The straight-line homotopy from the constant characteristic map to itself whose end `1` runs
along the loop `γ` and whose end `-1` stays at `1`: `(t, x) ↦ 1 + ((1 + x) / 2) (γ t - 1)`. -/
private def circleArcHomotopy (γ : Path (1 : sphere (0 : ℂ) 1) 1) :
    circleArcChar.Homotopy (circleArcChar.comp (ContinuousMap.fst.prodMk ContinuousMap.snd)) where
  toFun q := 1 + ((1 + q.2.2.down.val 0) / 2 : ℝ) • ((γ q.1 : ℂ) - 1)
  continuous_toFun := by fun_prop
  map_zero_left x := by simp [Metric.unitSphere.coe_one]
  map_one_left x := by simp [Metric.unitSphere.coe_one]

private theorem circleArcHomotopy_apply (γ : Path (1 : sphere (0 : ℂ) 1) 1)
    (q : I × (PUnit.{1} × TopCat.disk.{0} 1)) :
    circleArcHomotopy γ q = 1 + ((1 + q.2.2.down.val 0) / 2 : ℝ) • ((γ q.1 : ℂ) - 1) :=
  (rfl)

private theorem circleArcHomotopy_apply_sphereMinus (γ : Path (1 : sphere (0 : ℂ) 1) 1) (t : I)
    (p : PUnit.{1}) :
    circleArcHomotopy γ (t, (p, TopCat.diskBoundaryInclusion 1 sphereMinus)) = 1 := by
  rw [circleArcHomotopy_apply, sphereMinus_coord]
  norm_num

private theorem circleArcHomotopy_apply_spherePlus (γ : Path (1 : sphere (0 : ℂ) 1) 1) (t : I)
    (p : PUnit.{1}) :
    circleArcHomotopy γ (t, (p, TopCat.diskBoundaryInclusion 1 spherePlus)) = γ t := by
  rw [circleArcHomotopy_apply, spherePlus_coord]
  norm_num

private theorem circleArcHomotopy_mem (γ : Path (1 : sphere (0 : ℂ) 1) 1) (t : I) (p : PUnit.{1})
    (s : TopCat.diskBoundary.{0} 1) :
    circleArcHomotopy γ (t, (p, TopCat.diskBoundaryInclusion 1 s)) ∈ sphere (0 : ℂ) 1 := by
  rcases eq_sphereMinus_or_eq_spherePlus s with rfl | rfl
  · rw [circleArcHomotopy_apply_sphereMinus]
    simp
  · rw [circleArcHomotopy_apply_spherePlus]
    exact (γ t).property

/-- The degree of the loop `H₋ · H₊⁻¹` of the boundary homotopy `circleArcHomotopy γ`: the end `-1`
stays at `1`, so it is minus the degree of `γ`. -/
private theorem degree_circleArcHomotopy (γ : Path (1 : sphere (0 : ℂ) 1) 1) :
    Circle.degree (((arcBoundaryTrack (1 : sphere (0 : ℂ) 1) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
      (fun _ _ hw ↦ hw) (circleArcHomotopy_mem γ) sphereMinus).trans
        (arcBoundaryTrack (1 : sphere (0 : ℂ) 1) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ hw ↦ hw)
          (circleArcHomotopy_mem γ) spherePlus).symm).map
            Circle.homeomorphSphere.symm.continuous) =
      -Circle.degree (γ.map Circle.homeomorphSphere.symm.continuous) := by
  rw [Path.map_trans, ← Path.map_symm, Circle.degree_trans, Circle.degree_symm,
    Circle.degree_congr _ (Path.refl (Circle.homeomorphSphere.symm 1)) fun t ↦
      Circle.ext (by
        simp only [Path.map_coe, Function.comp_apply, Circle.coe_homeomorphSphere_symm_apply,
          Path.refl_apply]
        exact (coe_arcBoundaryTrack_apply ..).trans
          ((circleArcHomotopy_apply_sphereMinus γ t PUnit.unit).trans
            Metric.unitSphere.coe_one.symm)),
    Circle.degree_refl, zero_add, neg_inj]
  exact Circle.degree_congr _ _ fun t ↦ Circle.ext (by
    simp only [Path.map_coe, Function.comp_apply, Circle.coe_homeomorphSphere_symm_apply]
    exact (coe_arcBoundaryTrack_apply ..).trans (circleArcHomotopy_apply_spherePlus γ t PUnit.unit))

/-- **The endpoints of a boundary homotopy do not determine the reattachment class.** Attach an
arc at both of its ends to the point `1` of the unit circle `S¹ ⊆ ℂ`, with characteristic maps
constant at `1` and `h = id`. There are two homotopies `K, K' : χ ≃ χ` of the characteristic map,
both keeping the ends of the arc on `S¹`, whose reattachment maps are not homotopic relative to
`S¹`: for `K` both ends stay at `1`, while for `K'` the end `1` runs once around the circle. Their
boundary homotopies have the same endpoints, but their loops `H₋ · H₊⁻¹` have degrees `0` and
`-1`. -/
theorem exists_not_homotopicRel_fiberwiseCellReattachment_sphere :
    ∃ (K K' : (ContinuousMap.const (PUnit.{1} × TopCat.disk.{0} 1) (1 : ℂ)).Homotopy
        ((ContinuousMap.const (PUnit.{1} × TopCat.disk.{0} 1) (1 : ℂ)).comp
          (ContinuousMap.fst.prodMk ContinuousMap.snd)))
      (hK : ∀ t p s, K (t, (p, TopCat.diskBoundaryInclusion 1 s)) ∈ sphere (0 : ℂ) 1)
      (hK' : ∀ t p s, K' (t, (p, TopCat.diskBoundaryInclusion 1 s)) ∈ sphere (0 : ℂ) 1),
      ¬ (fiberwiseCellReattachment (k := fun _ : PUnit.{1} ↦ 1)
          (fun _ ↦ ContinuousMap.const _ 1) (fun _ ↦ ContinuousMap.const _ 1)
          (fun _ ↦ ContinuousMap.const _ 1) (fun _ ↦ ContinuousMap.const _ 1) (fun _ _ _ ↦ rfl)
          (fun _ _ _ ↦ rfl) (fun _ ↦ ContinuousMap.snd) (fun _ _ _ hw ↦ hw) (fun _ ↦ K)
          (fun _ ↦ hK)).hom.HomotopicRel
        (fiberwiseCellReattachment (k := fun _ : PUnit.{1} ↦ 1)
          (fun _ ↦ ContinuousMap.const _ 1) (fun _ ↦ ContinuousMap.const _ 1)
          (fun _ ↦ ContinuousMap.const _ 1) (fun _ ↦ ContinuousMap.const _ 1) (fun _ _ _ ↦ rfl)
          (fun _ _ _ ↦ rfl) (fun _ ↦ ContinuousMap.snd) (fun _ _ _ hw ↦ hw) (fun _ ↦ K')
          (fun _ ↦ hK')).hom
        (range (fiberwiseCellAttachmentIncl (k := fun _ : PUnit.{1} ↦ 1)
          (fun _ ↦ ContinuousMap.const (PUnit.{1} × TopCat.diskBoundary.{0} 1)
            (1 : sphere (0 : ℂ) 1)))) := by
  refine ⟨circleArcHomotopy (Path.refl (1 : sphere (0 : ℂ) 1)),
    circleArcHomotopy ((Circle.expLoop.map Circle.homeomorphSphere.continuous).cast
      Circle.homeomorphSphere_one.symm Circle.homeomorphSphere_one.symm),
    circleArcHomotopy_mem _, circleArcHomotopy_mem _, fun hE ↦ ?_⟩
  have hd := Circle.degree_eq_of_homotopic
    ((homotopic_arcBoundaryTrack_trans_symm_of_homotopicRel_fiberwiseCellReattachment
      (1 : sphere (0 : ℂ) 1) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ hw ↦ hw)
      (circleArcHomotopy_mem _) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ hw ↦ hw)
      (circleArcHomotopy_mem _) hE).map
        Circle.homeomorphSphere.symm)
  rw [degree_circleArcHomotopy, degree_circleArcHomotopy,
    Circle.degree_congr
      ((Path.refl (1 : sphere (0 : ℂ) 1)).map Circle.homeomorphSphere.symm.continuous)
      (Path.refl (Circle.homeomorphSphere.symm 1)) (fun _ ↦ Circle.ext (by simp)),
    Circle.degree_congr (((Circle.expLoop.map Circle.homeomorphSphere.continuous).cast
        Circle.homeomorphSphere_one.symm Circle.homeomorphSphere_one.symm).map
          Circle.homeomorphSphere.symm.continuous) Circle.expLoop (fun _ ↦ Circle.ext (by simp)),
    Circle.degree_refl, Circle.degree_expLoop] at hd
  norm_num at hd

end Circle

end TauCeti
