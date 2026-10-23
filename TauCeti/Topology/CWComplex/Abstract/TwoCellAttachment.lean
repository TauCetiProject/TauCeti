/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Disk
public import TauCeti.AlgebraicTopology.FundamentalGroup.TwoCellAttachment
public import TauCeti.Topology.CWComplex.Abstract.AttachCells
public import TauCeti.Topology.CWComplex.Abstract.CellAttachment
public import TauCeti.Topology.CWComplex.Abstract.Trans

import TauCeti.Topology.UnitInterval.OpenSquare

/-!
# Attaching 2-cells along loops is attaching disks

`TauCeti.TwoCellAttachment γ` attaches a square `I × I` to a space `X` along each loop `γ i` at a
point `x`: the edge `{0} × I` is glued to `X` along `γ i` and the other three edges are collapsed
to `x`. The square with its boundary is homeomorphic to the disk `𝔻 2` with its boundary circle
(`TauCeti.diskHomeomorphCube`), so this is an attachment of 2-disks in the sense of
`TauCeti.cellAttachment`, the pushout in `TopCat` of the boundary inclusions of the disks.

The attaching map `TauCeti.TwoCellAttachment.attachingMap γ i` of the `i`-th disk sends a point
of the boundary circle to the point of `X` to which the corresponding boundary point of the square
is glued. The isomorphism `TauCeti.TwoCellAttachment.isoCellAttachment γ` from the disk
attachment to `TwoCellAttachment γ` is the identity on `X` and is the characteristic map of the
`i`-th square on the `i`-th disk. Its inverse comes from the universal property of
`TwoCellAttachment`: each disk is a nullhomotopy of the image of the loop `γ i`.

The comparison transfers the point-set results proved for disk attachments. In particular,
attaching 2-cells along loops in a Hausdorff space gives a Hausdorff space. This is what lets the
presentation complex of a group presentation, built from squares, start the tower of
`TauCeti.killHomotopyGroups`.

Read through Mathlib's categorical `AttachCells` (`TauCeti.TwoCellAttachment.attachCells`), the
comparison also transfers CW structures: if `X` is a Hausdorff CW complex without cells of
dimension at least `2`, such as a wedge of circles, then `TwoCellAttachment γ` is a CW complex
(`TauCeti.TwoCellAttachment.cwComplex`) whose cells are those of `X` and the attached squares.

## Main definitions

* `TauCeti.TwoCellAttachment.diskCell`: the characteristic map of the `i`-th cell, on the disk.
* `TauCeti.TwoCellAttachment.attachingMap`: the attaching map of the `i`-th cell, on the boundary
  circle of the disk.
* `TauCeti.TwoCellAttachment.isoCellAttachment`: the isomorphism
  `cellAttachment (attachingMap γ) ≅ TwoCellAttachment γ`.
* `TauCeti.TwoCellAttachment.attachCells`: `TwoCellAttachment γ` is obtained from `X` by attaching
  2-disks, in the sense of `AttachCells`.
* `TauCeti.TwoCellAttachment.cwComplex`: the CW structure on `TwoCellAttachment γ` over a CW
  complex of dimension at most `1`, with its cells described by
  `TauCeti.TwoCellAttachment.cwComplexCellEquiv` and
  `TauCeti.TwoCellAttachment.cwComplexCellTwoEquiv`.

## Main results

* `TauCeti.TwoCellAttachment.incl_attachingMap_apply`: the characterization of the attaching map.
* `TauCeti.TwoCellAttachment.cellAttachmentIncl_isoCellAttachment_hom`,
  `TauCeti.TwoCellAttachment.cellAttachmentCell_isoCellAttachment_hom`: the isomorphism is the
  inclusion on `X` and the characteristic map of the square on each disk.
* `TauCeti.TwoCellAttachment.instT2Space`: attaching 2-cells along loops in a Hausdorff space gives
  a Hausdorff space.

## Implementation notes

`TauCeti.cellAttachment` takes a space in `TopCat.{u}` and cells indexed by a type in the same
universe `u`, so the comparison is stated for loops indexed by a type in the universe of `X`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0 for attaching cells, and Section 1.2, the construction of the space `X_G` before
  Corollary 1.28.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory Limits Set Topology unitInterval

universe u

namespace TwoCellAttachment

variable {X : Type u} [TopologicalSpace X] {x : X} {ι : Type u} (γ : ι → Path x x)

/-- The characteristic map of the `i`-th cell, on the disk `𝔻 2`: the characteristic map
`TauCeti.TwoCellAttachment.cell γ i` of the square, through the homeomorphism
`TauCeti.diskHomeomorphCube` of the disk with the square `I^(Fin 2) = I × I`. -/
def diskCell (i : ι) : TopCat.disk.{u} 2 ⟶ TopCat.of (TwoCellAttachment γ) :=
  TopCat.ofHom ⟨fun z ↦ cell γ i (Homeomorph.piFinTwo _ (diskHomeomorphCube 2 z)),
    (cell γ i).continuous.comp ((Homeomorph.piFinTwo _).continuous.comp
      (diskHomeomorphCube 2).continuous)⟩

/-- The characteristic map of the `i`-th cell on the disk, at a point of the disk. -/
@[simp]
lemma diskCell_apply (i : ι) (z : TopCat.disk.{u} 2) :
    diskCell γ i z = cell γ i (diskHomeomorphCube 2 z 0, diskHomeomorphCube 2 z 1) :=
  (rfl)

/-- The attaching map of the `i`-th cell, on the boundary circle of the disk `𝔻 2`: a point of the
circle goes to the point of `X` to which the corresponding boundary point of the square `I × I`
is glued, through the homeomorphism `TauCeti.diskHomeomorphCube` of the disk with the square. It
is characterized by `TauCeti.TwoCellAttachment.incl_attachingMap_apply`. -/
def attachingMap (i : ι) : TopCat.diskBoundary.{u} 2 ⟶ TopCat.of X :=
  TopCat.ofHom ⟨fun s ↦ isClosedEmbedding_incl.isEmbedding.toHomeomorph.symm
      ⟨cell γ i (Homeomorph.piFinTwo _ (diskHomeomorphCube 2 (TopCat.diskBoundaryInclusion 2 s))),
        cell_mem_range_incl ((piFinTwo_diskHomeomorphCube_notMem_iff _).2 ⟨s, rfl⟩)⟩,
    isClosedEmbedding_incl.isEmbedding.toHomeomorph.symm.continuous.comp
      (Continuous.subtype_mk (by fun_prop) _)⟩

/-- The attaching map of the `i`-th cell sends a point of the boundary circle to the point of `X`
to which the corresponding point of the square is glued. -/
theorem incl_attachingMap_apply (i : ι) (s : TopCat.diskBoundary.{u} 2) :
    incl γ (attachingMap γ i s) = diskCell γ i (TopCat.diskBoundaryInclusion 2 s) :=
  congrArg Subtype.val (isClosedEmbedding_incl.isEmbedding.toHomeomorph.apply_symm_apply _)

/-- A point of the boundary of the square, glued to the point `y` of `X`, lies in the `i`-th disk
of the disk attachment over the image of `y`. -/
private lemma cellAttachmentCell_eq_of_cell_eq_incl {i : ι} {q : I × I}
    (hq : q ∉ Ioo (0 : I) 1 ×ˢ Ioo (0 : I) 1) {y : X} (hy : cell γ i q = incl γ y) :
    cellAttachmentCell (attachingMap γ) i
        ((diskHomeomorphCube 2).symm ((Homeomorph.piFinTwo _).symm q)) =
      cellAttachmentIncl (attachingMap γ) y := by
  have hq' : Homeomorph.piFinTwo _
      (diskHomeomorphCube 2 ((diskHomeomorphCube 2).symm ((Homeomorph.piFinTwo _).symm q))) =
        q := by
    simp
  obtain ⟨s, hs⟩ := (piFinTwo_diskHomeomorphCube_notMem_iff _).1 (hq' ▸ hq)
  have hsy : attachingMap γ i s = y := by
    refine incl_injective (γ := γ) ?_
    rw [incl_attachingMap_apply, hs, ← hy, diskCell_apply]
    simp
  rw [← hs, ← hsy, ← ConcreteCategory.comp_apply, ← cellAttachment_boundary,
    ConcreteCategory.comp_apply]

/-- The `i`-th disk of the disk attachment, read on the square, is a nullhomotopy of the image of
the loop `γ i`. -/
private def cellAttachmentHomotopy (i : ι) :
    Path.Homotopy ((γ i).map (cellAttachmentIncl (attachingMap γ)).hom.continuous)
      (Path.refl (cellAttachmentIncl (attachingMap γ) x)) where
  toContinuousMap := (cellAttachmentCell (attachingMap γ) i).hom.comp
    ⟨fun q ↦ (diskHomeomorphCube 2).symm ((Homeomorph.piFinTwo _).symm q), by fun_prop⟩
  map_zero_left t := by
    simpa using cellAttachmentCell_eq_of_cell_eq_incl γ (q := (0, t)) (by simp)
      (cell_apply_zero i t)
  map_one_left t := by
    simpa using cellAttachmentCell_eq_of_cell_eq_incl γ (q := (1, t)) (by simp)
      (cell_apply_one i t)
  prop' s t ht := by
    rcases ht with rfl | rfl
    · simpa using cellAttachmentCell_eq_of_cell_eq_incl γ (q := (s, 0)) (by simp)
        (cell_source i s)
    · simpa using cellAttachmentCell_eq_of_cell_eq_incl γ (q := (s, 1)) (by simp)
        (cell_target i s)

private lemma cellAttachmentHomotopy_apply (i : ι) (q : I × I) :
    cellAttachmentHomotopy γ i q = cellAttachmentCell (attachingMap γ) i
      ((diskHomeomorphCube 2).symm ((Homeomorph.piFinTwo _).symm q)) :=
  (rfl)

/-- The map from the disk attachment to `TwoCellAttachment γ`: the inclusion on `X` and
`diskCell γ i` on the `i`-th disk. -/
private def toTwoCellAttachment :
    cellAttachment (attachingMap γ) ⟶ TopCat.of (TwoCellAttachment γ) :=
  cellAttachmentLift (attachingMap γ) (TopCat.ofHom (incl γ)) (diskCell γ) fun i ↦ by
    ext s
    exact incl_attachingMap_apply γ i s

private lemma cellAttachmentIncl_toTwoCellAttachment :
    cellAttachmentIncl (attachingMap γ) ≫ toTwoCellAttachment γ = TopCat.ofHom (incl γ) := by
  rw [toTwoCellAttachment, cellAttachmentIncl_lift]

private lemma cellAttachmentCell_toTwoCellAttachment (i : ι) :
    cellAttachmentCell (attachingMap γ) i ≫ toTwoCellAttachment γ = diskCell γ i := by
  rw [toTwoCellAttachment, cellAttachmentCell_lift]

/-- **Attaching 2-cells along loops is attaching disks.** The isomorphism from the space obtained
by attaching a disk `𝔻 2` along each `attachingMap γ i` to `TwoCellAttachment γ`: it is the
inclusion on `X`, and the characteristic map of the `i`-th square on the `i`-th disk, through the
homeomorphism `TauCeti.diskHomeomorphCube` of the disk with the square. -/
def isoCellAttachment : cellAttachment (attachingMap γ) ≅ TopCat.of (TwoCellAttachment γ) where
  hom := toTwoCellAttachment γ
  inv := TopCat.ofHom (lift (cellAttachmentIncl (attachingMap γ)).hom (cellAttachmentHomotopy γ))
  hom_inv_id := by
    refine (cellAttachmentAttachCells _).hom_ext ?_ fun (i : ι) ↦ ?_
    · rw [reassoc_of% cellAttachmentIncl_toTwoCellAttachment γ]
      ext y
      simp
    · have hi := cellAttachmentAttachCells_cell (attachingMap γ) i
      rw [hi, reassoc_of% cellAttachmentCell_toTwoCellAttachment γ i]
      ext z
      rw [ConcreteCategory.comp_apply, diskCell_apply]
      simp only [TopCat.hom_ofHom, lift_cell]
      have hz : (diskHomeomorphCube 2 z 0, diskHomeomorphCube 2 z 1) =
          Homeomorph.piFinTwo (fun _ ↦ I) (diskHomeomorphCube 2 z) := rfl
      rw [cellAttachmentHomotopy_apply, hz, Homeomorph.symm_apply_apply,
        Homeomorph.symm_apply_apply, Category.comp_id]
  inv_hom_id := by
    refine TopCat.hom_ext (hom_ext ?_ fun i ↦ ?_)
    · ext y
      have h := ConcreteCategory.congr_hom (cellAttachmentIncl_toTwoCellAttachment γ) y
      simp only [TopCat.hom_comp, ContinuousMap.comp_apply, TopCat.hom_id, ContinuousMap.id_apply,
        TopCat.hom_ofHom, lift_incl] at h ⊢
      exact h
    · ext q
      simp only [TopCat.hom_comp, ContinuousMap.comp_apply, TopCat.hom_id, ContinuousMap.id_apply,
        TopCat.hom_ofHom, lift_cell]
      rw [cellAttachmentHomotopy_apply]
      refine (ConcreteCategory.congr_hom (cellAttachmentCell_toTwoCellAttachment γ i) _).trans ?_
      rw [diskCell_apply]
      simp

/-- The isomorphism `isoCellAttachment γ` is the inclusion on `X`. -/
@[reassoc (attr := simp)]
theorem cellAttachmentIncl_isoCellAttachment_hom :
    cellAttachmentIncl (attachingMap γ) ≫ (isoCellAttachment γ).hom = TopCat.ofHom (incl γ) :=
  cellAttachmentIncl_toTwoCellAttachment γ

/-- The isomorphism `isoCellAttachment γ` is the characteristic map of the `i`-th square on the
`i`-th disk. -/
@[reassoc (attr := simp)]
theorem cellAttachmentCell_isoCellAttachment_hom (i : ι) :
    cellAttachmentCell (attachingMap γ) i ≫ (isoCellAttachment γ).hom =
      diskCell γ i :=
  cellAttachmentCell_toTwoCellAttachment γ i

/-- **Attaching 2-cells along loops in a Hausdorff space gives a Hausdorff space**, since it is an
attachment of disks (`TauCeti.instT2SpaceCellAttachment`). -/
instance instT2Space [T2Space X] : T2Space (TwoCellAttachment γ) :=
  (TopCat.homeoOfIso (isoCellAttachment γ)).t2Space

/-! ### The CW structure -/

/-- `TwoCellAttachment γ` is obtained from `X` by attaching 2-disks, in the sense of Mathlib's
categorical `AttachCells` structure, along the inclusion of `X`. The cells are the characteristic
maps `TauCeti.TwoCellAttachment.diskCell γ i` (`TauCeti.TwoCellAttachment.attachCells_cell`). The
body is exposed so that its cells are indexed by `ι` by definition, which the statement of
`TauCeti.TwoCellAttachment.attachCells_cell` needs in order to typecheck. -/
@[expose] def attachCells :
    HomotopicalAlgebra.AttachCells.{u} (TopCat.RelativeCWComplex.basicCell 2)
      (TopCat.ofHom (incl γ)) :=
  (cellAttachmentAttachCells (attachingMap γ)).ofArrowIso
    (Arrow.isoMk (Iso.refl _) (isoCellAttachment γ) (by simp))

/-- The cells of `TauCeti.TwoCellAttachment.attachCells γ` are the characteristic maps of the
squares, read on the disk. -/
@[simp]
lemma attachCells_cell (i : ι) : (attachCells γ).cell i = diskCell γ i :=
  (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ (isoCellAttachment γ).hom) (cellAttachmentAttachCells_cell _ i)).trans
      (cellAttachmentCell_isoCellAttachment_hom γ i)

section CWComplex

open Topology.RelCWComplex (map)

variable [T2Space X] [Topology.CWComplex (univ : Set X)]
  (hX : ∀ m, 2 ≤ m → IsEmpty (RelCWComplex.cell (univ : Set X) m))

/-- **Attaching 2-cells to a CW complex of dimension at most one gives a CW complex.** If `X` is
a Hausdorff CW complex with no cells of dimension at least `2`, then `TwoCellAttachment γ` is a CW
complex. Its cells of dimension other than `2` are the cells of `X`, included by `incl γ`
(`TauCeti.TwoCellAttachment.cwComplexCellEquiv`), and its `2`-cells are the attached squares,
indexed by `ι` (`TauCeti.TwoCellAttachment.cwComplexCellTwoEquiv`). -/
@[instance_reducible]
def cwComplex : Topology.CWComplex (univ : Set (TwoCellAttachment γ)) :=
  (attachCells γ).toRelativeCWComplex.cwComplexTrans hX fun _ hm ↦
    (attachCells γ).isEmpty_toRelativeCWComplex_attachCells_ι hm.ne _

/-- The `m`-cells of `TauCeti.TwoCellAttachment.cwComplex` are the `m`-cells of `X` and the cells
of `TauCeti.TwoCellAttachment.attachCells γ` attached in dimension `m`. -/
private abbrev cwComplexCellEquiv' (m : ℕ) :
    @RelCWComplex.cell _ _ (univ : Set (TwoCellAttachment γ)) ∅
      (cwComplex γ hX).instRelCWComplex m ≃
      RelCWComplex.cell (univ : Set X) m ⊕
        ((attachCells γ).toRelativeCWComplex.attachCells m (not_isMax m)).ι :=
  TopCat.RelativeCWComplex.cwComplexTransCellEquiv _ _ _ m

/-- The cells of `TauCeti.TwoCellAttachment.cwComplex` of dimension `m ≠ 2` are the cells of
`X`. -/
def cwComplexCellEquiv {m : ℕ} (hm : m ≠ 2) :
    @RelCWComplex.cell _ _ (univ : Set (TwoCellAttachment γ)) ∅
      (cwComplex γ hX).instRelCWComplex m ≃
      RelCWComplex.cell (univ : Set X) m :=
  haveI := (attachCells γ).isEmpty_toRelativeCWComplex_attachCells_ι hm (not_isMax m)
  (cwComplexCellEquiv' γ hX m).trans (Equiv.sumEmpty _ _)

/-- The `2`-cells of `TauCeti.TwoCellAttachment.cwComplex` are indexed by `ι`. -/
def cwComplexCellTwoEquiv :
    @RelCWComplex.cell _ _ (univ : Set (TwoCellAttachment γ)) ∅
      (cwComplex γ hX).instRelCWComplex 2 ≃ ι :=
  haveI := hX 2 le_rfl
  ((cwComplexCellEquiv' γ hX 2).trans (Equiv.emptySum _ _)).trans
    (attachCells γ).toRelativeCWComplexAttachCellsEquiv

/-- The characteristic map of a cell of `X` of dimension `m ≠ 2`, as a cell of
`TauCeti.TwoCellAttachment.cwComplex`, is its characteristic map in `X` followed by `incl γ`. -/
@[simp]
lemma coe_map_cwComplexCellEquiv_symm {m : ℕ} (hm : m ≠ 2)
    (i : RelCWComplex.cell (univ : Set X) m) :
    ⇑(@map _ _ (univ : Set (TwoCellAttachment γ)) ∅ (cwComplex γ hX).instRelCWComplex m
        ((cwComplexCellEquiv γ hX hm).symm i)) = incl γ ∘ map m i :=
  TopCat.RelativeCWComplex.coe_map_cwComplexTransCellEquiv_symm_inl (X := TopCat.of X) _ _ _ m i

/-- The characteristic map of the `2`-cell indexed by `i` is the characteristic map
`TauCeti.TwoCellAttachment.diskCell γ i` of the `i`-th square, read on the closed unit ball of the
sup norm through the radial homeomorphism `TauCeti.diskHomeomorphClosedBall`. -/
@[simp]
lemma map_cwComplexCellTwoEquiv_symm (i : ι) (y : Metric.closedBall (0 : Fin 2 → ℝ) 1) :
    @map _ _ (univ : Set (TwoCellAttachment γ)) ∅ (cwComplex γ hX).instRelCWComplex 2
        ((cwComplexCellTwoEquiv γ hX).symm i) y =
      diskCell γ i ((diskHomeomorphClosedBall 2).symm y) := by
  have := hX 2 le_rfl
  refine (TopCat.RelativeCWComplex.map_cwComplexTransCellEquiv_symm_inr _ _ _ 2
    ((attachCells γ).toRelativeCWComplexAttachCellsEquiv.symm i) y).trans ?_
  rw [HomotopicalAlgebra.AttachCells.toRelativeCWComplex_cells_ι]
  -- The cells of `attachCells γ` are indexed by `ι` only up to unfolding `attachCells`, which
  -- `rw` does not do, so the last two steps are congruences.
  exact (congrArg (fun k ↦ (attachCells γ).cell k ((diskHomeomorphClosedBall 2).symm y))
    ((attachCells γ).toRelativeCWComplexAttachCellsEquiv.apply_symm_apply i)).trans
    (congrArg (fun g ↦ g ((diskHomeomorphClosedBall 2).symm y)) (attachCells_cell γ i))

end CWComplex

end TwoCellAttachment

end TauCeti
