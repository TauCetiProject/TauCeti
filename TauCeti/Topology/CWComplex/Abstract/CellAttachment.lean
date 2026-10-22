/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.CWComplex.Abstract.Hausdorff

/-!
# Attaching a family of cells

For a family of maps `φ i : ∂𝔻 n ⟶ X`, this file constructs the space obtained by attaching
one `n`-disk along each `φ i`.  The construction is the pushout of the coproduct of the boundary
inclusions.  It comes with its inclusion of `X`, characteristic maps for the new cells, the
pushout universal property, and an `AttachCells` witness.

The inclusion of the old space is a closed embedding, and the attachment is Hausdorff when the
old space is.  Each attaching map becomes null-homotopic after inclusion, since it extends over
its characteristic disk.  These facts are the point-set input for killing chosen homotopy
classes by cell attachment.

## Main definitions

* `TauCeti.cellAttachment`: the space obtained by attaching the disks.
* `TauCeti.cellAttachmentIncl`: the inclusion of the old space.
* `TauCeti.cellAttachmentCell`: the characteristic map of an attached cell.
* `TauCeti.cellAttachmentAttachCells`: the categorical cell-attachment witness.
* `TauCeti.cellAttachmentLift`: the map induced by compatible maps from the old space and disks.

## References

* A. Hatcher, *Algebraic Topology*, Chapter 0 and Section 4.1.
* R. Fritsch and R. Piccinini, *Cellular Structures in Topology*, Cambridge University Press,
  1990.
-/

public section

noncomputable section

open CategoryTheory Limits HomotopicalAlgebra

universe u

namespace TauCeti

variable {X Y : TopCat.{u}} {n : ℕ} {ι : Type u}

/-- The space obtained from `X` by attaching one `n`-disk along each map
`φ i : ∂𝔻 n ⟶ X`. -/
abbrev cellAttachment (φ : ι → (TopCat.diskBoundary n ⟶ X)) : TopCat.{u} :=
  pushout (Sigma.desc φ) (Limits.Sigma.map fun _ ↦ TopCat.diskBoundaryInclusion n)

/-- The inclusion of the old space into a cell attachment. -/
abbrev cellAttachmentIncl (φ : ι → (TopCat.diskBoundary n ⟶ X)) : X ⟶ cellAttachment φ :=
  pushout.inl (Sigma.desc φ)
    (Limits.Sigma.map fun _ ↦ TopCat.diskBoundaryInclusion n)

/-- The characteristic map of the cell attached along `φ i`. -/
def cellAttachmentCell (φ : ι → (TopCat.diskBoundary n ⟶ X)) (i : ι) :
    TopCat.disk n ⟶ cellAttachment φ :=
  Sigma.ι (fun _ : ι ↦ TopCat.disk.{u} n) i ≫
    pushout.inr (Sigma.desc φ)
      (Limits.Sigma.map fun _ ↦ TopCat.diskBoundaryInclusion n)

/-- The characteristic map of an attached cell restricts on its boundary to the attaching map. -/
@[reassoc]
theorem cellAttachment_boundary (φ : ι → (TopCat.diskBoundary n ⟶ X)) (i : ι) :
    φ i ≫ cellAttachmentIncl φ =
      TopCat.diskBoundaryInclusion n ≫ cellAttachmentCell φ i := by
  have h := Sigma.ι (fun _ : ι ↦ TopCat.diskBoundary.{u} n) i ≫=
    (pushout.condition (f := Sigma.desc φ)
      (g := Limits.Sigma.map fun _ ↦ TopCat.diskBoundaryInclusion n))
  simpa [cellAttachmentIncl, cellAttachmentCell, Category.assoc] using h

/-- The inclusion into `cellAttachment φ` is obtained by attaching `n`-disks in the sense of
Mathlib's categorical `AttachCells` structure. -/
@[expose] def cellAttachmentAttachCells (φ : ι → (TopCat.diskBoundary n ⟶ X)) :
    AttachCells.{u} (TopCat.RelativeCWComplex.basicCell n) (cellAttachmentIncl φ) where
  ι := ι
  π _ := ()
  isColimit₁ := coproductIsCoproduct _
  isColimit₂ := coproductIsCoproduct _
  m := Limits.Sigma.map fun _ ↦ TopCat.diskBoundaryInclusion n
  g₁ := Sigma.desc φ
  g₂ := pushout.inr (Sigma.desc φ)
    (Limits.Sigma.map fun _ ↦ TopCat.diskBoundaryInclusion n)
  isPushout := IsPushout.of_hasPushout (Sigma.desc φ)
    (Limits.Sigma.map fun _ ↦ TopCat.diskBoundaryInclusion n)
  cofan₁ := _
  cofan₂ := _

/-- The cells in `cellAttachmentAttachCells` have the prescribed characteristic maps. -/
@[simp]
theorem cellAttachmentAttachCells_cell (φ : ι → (TopCat.diskBoundary n ⟶ X)) (i : ι) :
    (cellAttachmentAttachCells φ).cell i = cellAttachmentCell φ i := by
  rfl

/-- A compatible map on the old space and on every characteristic disk induces a map out of the
cell attachment. -/
def cellAttachmentLift (φ : ι → (TopCat.diskBoundary n ⟶ X)) (f : X ⟶ Y)
    (F : ι → (TopCat.disk n ⟶ Y))
    (h : ∀ i, φ i ≫ f = TopCat.diskBoundaryInclusion n ≫ F i) :
    cellAttachment φ ⟶ Y :=
  pushout.desc f (Sigma.desc F) (by
    apply Sigma.hom_ext
    intro i
    simpa [Category.assoc] using h i)

/-- The lift out of a cell attachment restricts to the prescribed map on the old space. -/
@[reassoc (attr := simp)]
theorem cellAttachmentIncl_lift (φ : ι → (TopCat.diskBoundary n ⟶ X)) (f : X ⟶ Y)
    (F : ι → (TopCat.disk n ⟶ Y))
    (h : ∀ i, φ i ≫ f = TopCat.diskBoundaryInclusion n ≫ F i) :
    cellAttachmentIncl φ ≫ cellAttachmentLift φ f F h = f := by
  rw [cellAttachmentIncl, cellAttachmentLift, pushout.inl_desc]

/-- The lift out of a cell attachment restricts to the prescribed map on each disk. -/
@[reassoc (attr := simp)]
theorem cellAttachmentCell_lift (φ : ι → (TopCat.diskBoundary n ⟶ X)) (f : X ⟶ Y)
    (F : ι → (TopCat.disk n ⟶ Y))
    (h : ∀ i, φ i ≫ f = TopCat.diskBoundaryInclusion n ≫ F i) (i : ι) :
    cellAttachmentCell φ i ≫ cellAttachmentLift φ f F h = F i := by
  rw [cellAttachmentCell, cellAttachmentLift, Category.assoc, pushout.inr_desc,
    Sigma.ι_comp_desc]

/-- The inclusion of the old space into a cell attachment is a closed embedding. -/
theorem isClosedEmbedding_cellAttachmentIncl (φ : ι → (TopCat.diskBoundary n ⟶ X)) :
    Topology.IsClosedEmbedding (cellAttachmentIncl φ) :=
  TauCeti.TopCat.isClosedEmbedding_of_isPushout
    (IsPushout.of_hasPushout (Sigma.desc φ)
      (Limits.Sigma.map fun _ ↦ TopCat.diskBoundaryInclusion n))
    (TauCeti.TopCat.isClosedEmbedding_sigmaMap _ fun _ ↦
      TauCeti.TopCat.isClosedEmbedding_diskBoundaryInclusion n)

/-- Attaching disks to a Hausdorff space produces a Hausdorff space. -/
instance instT2SpaceCellAttachment [T2Space X]
    (φ : ι → (TopCat.diskBoundary n ⟶ X)) : T2Space (cellAttachment φ) :=
  (cellAttachmentAttachCells φ).t2Space
    (fun _ ↦ TauCeti.TopCat.extendsDisjointOpens_diskBoundaryInclusion n)
    (fun _ ↦ TauCeti.TopCat.isClosedEmbedding_diskBoundaryInclusion n)

/-- Every prescribed attaching map becomes null-homotopic after inclusion into the cell
attachment: its characteristic disk gives an extension. -/
theorem cellAttachment_attachingMap_nullhomotopic
    (φ : ι → (TopCat.diskBoundary n ⟶ X)) (i : ι) :
    ((cellAttachmentIncl φ).hom.comp (φ i).hom).Nullhomotopic := by
  rw [← TopCat.hom_comp]
  exact (TopCat.Hom.nullhomotopic_iff_exists_diskBoundaryInclusion_comp_eq _).2
    ⟨_, (cellAttachment_boundary φ i).symm⟩

end TauCeti
