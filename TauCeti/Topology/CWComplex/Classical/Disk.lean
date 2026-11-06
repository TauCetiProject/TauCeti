/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.CWComplex.Classical.Finite
public import TauCeti.AlgebraicTopology.Disk
public import TauCeti.Topology.CWComplex.Classical.Pushout
public import TauCeti.Topology.CWComplex.Classical.Sigma

/-!
# The disk relative to its boundary sphere, and disjoint unions of disks

The Euclidean disk `TopCat.disk n` is a classical relative CW complex over its boundary sphere,
the range of `TopCat.diskBoundaryInclusion n`, with a single cell, of dimension `n`
(`TauCeti.diskRelCWComplex`). Its characteristic map is the inverse of the radial comparison
`TauCeti.diskHomeomorphClosedBall` of the disk with the closed unit ball of the sup norm on
`Fin n → ℝ`, the domain of characteristic maps in Mathlib's `Topology.RelCWComplex`. For `n = 0`
the boundary is empty and the disk is a single `0`-cell.

For a family of dimensions `n : ι → ℕ`, the disjoint union `Σ i, TopCat.disk (n i)` is then a
relative CW complex over the disjoint union of the boundary spheres
(`TauCeti.sigmaDiskRelCWComplex`), with one cell for each index `i`, of dimension `n i`, and
characteristic map the characteristic map of the `i`-th disk followed by the summand inclusion.
The base is homeomorphic to `Σ i, TopCat.diskBoundary (n i)`
(`TauCeti.sigmaDiskBoundaryHomeomorph`), so a family of attaching maps
`a i : TopCat.diskBoundary (n i) → Z` becomes a single continuous map from the base to `Z`
(`TauCeti.sigmaDiskAttachingMap`).

This is the input of `TauCeti.relativeCWPushout`: gluing the disjoint union of disks to a space
`Z` along `TauCeti.sigmaDiskAttachingMap a` attaches one `n i`-cell to `Z` along each `a i`, and
the adjunction space is a relative CW complex over `Z` with these cells
(`TauCeti.sigmaDiskAdjunctionSpaceCellEquiv`). This is the form of a cell attachment along a
family of maps, such as the attachment of one cell to a sublevel of a Morse function for each
critical point of a critical level, of dimension its index.

## Main definitions

* `TauCeti.diskRelCWComplex n`: the disk `TopCat.disk n` as a relative CW complex over its
  boundary sphere, with one `n`-cell.
* `TauCeti.sigmaDiskRelCWComplex n`: the disjoint union of the disks `TopCat.disk (n i)` as a
  relative CW complex over the disjoint union of their boundaries.
* `TauCeti.sigmaDiskBoundaryHomeomorph n`: the base of `TauCeti.sigmaDiskRelCWComplex n` is the
  disjoint union of the boundary spheres `TopCat.diskBoundary (n i)`.
* `TauCeti.sigmaDiskAttachingMap a`: a family of maps out of the boundary spheres, as a map out of
  the base of `TauCeti.sigmaDiskRelCWComplex n`.

## Main results

* `TauCeti.diskRelCWComplexCellEquiv` and `TauCeti.sigmaDiskRelCWComplexCellEquiv`: the disk has
  one cell, of dimension `n`, and the `m`-cells of the disjoint union are the indices `i` with
  `n i = m`.
* `TauCeti.diskRelCWComplex_map_apply` and `TauCeti.sigmaDiskRelCWComplex_map_apply`: the
  characteristic maps.
* `TauCeti.finite_diskRelCWComplex`: the disk is a finite relative CW complex.
* `TauCeti.sigmaDiskAdjunctionSpaceCellEquiv`: gluing the disjoint union of disks to a space along
  a family of attaching maps attaches one `n i`-cell for each `i`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Chapter 0, cell
  attachments.
-/

public section

noncomputable section

universe u

open Metric Set Topology Topology.RelCWComplex

namespace TauCeti

variable (n : ℕ)

open Classical in
/-- The inverse of the radial comparison `TauCeti.diskHomeomorphClosedBall` on the closed unit
ball of the sup norm, extended by the centre outside it. -/
private def diskCellFun (x : Fin n → ℝ) : TopCat.disk.{u} n :=
  if hx : x ∈ closedBall 0 1 then (diskHomeomorphClosedBall n).symm ⟨x, hx⟩ else diskCenter n

private theorem diskCellFun_of_mem {x : Fin n → ℝ} (hx : x ∈ closedBall 0 1) :
    diskCellFun n x = (diskHomeomorphClosedBall n).symm ⟨x, hx⟩ := by
  unfold diskCellFun
  exact dite_eq_left hx

/-- The characteristic map of the top cell of the disk: `TauCeti.diskCellFun` with source the open
unit ball. -/
private def diskCellMap : PartialEquiv (Fin n → ℝ) (TopCat.disk.{u} n) where
  toFun := diskCellFun n
  invFun z := diskHomeomorphClosedBall n z
  source := ball 0 1
  target := {z | (diskHomeomorphClosedBall n z : Fin n → ℝ) ∈ ball 0 1}
  map_source' x hx := by
    rw [mem_ofPred_eq, diskCellFun_of_mem n (ball_subset_closedBall hx),
      Homeomorph.apply_symm_apply]
    exact hx
  map_target' _ hz := hz
  left_inv' x hx := by
    rw [diskCellFun_of_mem n (ball_subset_closedBall hx), Homeomorph.apply_symm_apply]
  right_inv' z _ := by
    rw [diskCellFun_of_mem n (diskHomeomorphClosedBall n z).2, Subtype.coe_eta,
      Homeomorph.symm_apply_apply]

private theorem diskCellMap_apply {x : Fin n → ℝ} (hx : x ∈ closedBall 0 1) :
    diskCellMap n x = (diskHomeomorphClosedBall n).symm ⟨x, hx⟩ :=
  diskCellFun_of_mem n hx

/-- The cells of dimension `m` of the disk `TopCat.disk n`: one if `m = n`, none otherwise. -/
private abbrev DiskCell (m : ℕ) : Type u := ULift.{u} (PLift (m = n))

/-- The characteristic maps of the cells of the disk. -/
private def diskCellMapOfCell :
    (m : ℕ) → DiskCell.{u} n m → PartialEquiv (Fin m → ℝ) (TopCat.disk.{u} n)
  | _, ⟨⟨rfl⟩⟩ => diskCellMap n

private theorem diskCellMapOfCell_self (c : DiskCell.{u} n n) :
    diskCellMapOfCell n n c = diskCellMap n := by
  rcases c with ⟨⟨h⟩⟩
  rfl

/-- **The disk relative to its boundary sphere.** The Euclidean disk `TopCat.disk n` is a finite
relative CW complex over its boundary sphere with exactly one cell, of dimension `n`, whose
characteristic map is the inverse of `TauCeti.diskHomeomorphClosedBall`
(`TauCeti.diskRelCWComplex_map_apply`). -/
@[instance_reducible]
def diskRelCWComplex :
    RelCWComplex (univ : Set (TopCat.disk.{u} n)) (range (TopCat.diskBoundaryInclusion.{u} n)) :=
  RelCWComplex.mkFinite _ _ (DiskCell.{u} n) (diskCellMapOfCell n)
    (Filter.eventually_atTop.2 ⟨n + 1, fun m hm ↦ ⟨fun i ↦ by have := i.down.down; omega⟩⟩)
    (fun _ ↦ inferInstance)
    (by rintro m ⟨⟨hm⟩⟩; subst m; rfl)
    (by
      rintro m ⟨⟨hm⟩⟩
      subst m
      rw [diskCellMapOfCell_self]
      refine continuousOn_iff_continuous_domRestrict.2 ?_
      convert (diskHomeomorphClosedBall n).symm.continuous using 1
      funext x
      exact diskCellMap_apply n x.2)
    (by
      rintro m ⟨⟨hm⟩⟩
      subst m
      rw [diskCellMapOfCell_self]
      exact (continuous_subtype_val.comp (diskHomeomorphClosedBall n).continuous).continuousOn)
    (by
      rintro ⟨m, ⟨⟨hm⟩⟩⟩ - ⟨m', ⟨⟨hm'⟩⟩⟩ - hne
      subst m m'
      exact absurd rfl hne)
    (by
      rintro m ⟨⟨hm⟩⟩
      subst m
      rw [diskCellMapOfCell_self]
      refine disjoint_left.2 ?_
      rintro _ ⟨x, hx, rfl⟩ hb
      refine (diskHomeomorphClosedBall_mem_ball_iff _).1 ?_ hb
      rw [diskCellMap_apply n (ball_subset_closedBall hx), Homeomorph.apply_symm_apply]
      exact hx)
    (by
      rintro m ⟨⟨hm⟩⟩ x hx
      subst m
      left
      rw [diskCellMapOfCell_self, ← norm_diskHomeomorphClosedBall_eq_one_iff,
        diskCellMap_apply n (sphere_subset_closedBall hx), Homeomorph.apply_symm_apply]
      exact mem_sphere_zero_iff_norm.1 hx)
    (TopCat.isClosedEmbedding_diskBoundaryInclusion n).isClosed_range
    (by
      refine eq_univ_of_forall fun z ↦ Or.inr (mem_iUnion₂.2 ⟨n, ⟨⟨rfl⟩⟩, ?_⟩)
      refine ⟨diskHomeomorphClosedBall n z, (diskHomeomorphClosedBall n z).2, ?_⟩
      rw [diskCellMapOfCell_self, diskCellMap_apply n (diskHomeomorphClosedBall n z).2,
        Subtype.coe_eta, Homeomorph.symm_apply_apply])

/-- The disk is a finite relative CW complex over its boundary sphere. -/
theorem finite_diskRelCWComplex :
    letI := diskRelCWComplex n
    RelCWComplex.Finite (univ : Set (TopCat.disk.{u} n)) :=
  RelCWComplex.finite_mkFinite ..

/-- The disk has exactly one cell, of dimension `n`: its `m`-cells are the proofs of `m = n`. -/
def diskRelCWComplexCellEquiv (m : ℕ) :
    letI := diskRelCWComplex n
    cell (univ : Set (TopCat.disk.{u} n)) m ≃ PLift (m = n) :=
  Equiv.ulift

/-- The top cell of the disk. -/
def diskRelCWComplexTopCell :
    letI := diskRelCWComplex n
    cell (univ : Set (TopCat.disk.{u} n)) n :=
  (diskRelCWComplexCellEquiv n n).symm ⟨rfl⟩

/-- The characteristic map of the top cell of the disk is the inverse of the radial comparison
`TauCeti.diskHomeomorphClosedBall` on the closed unit ball of the sup norm. -/
theorem diskRelCWComplex_map_apply (x : closedBall (0 : Fin n → ℝ) 1) :
    letI := diskRelCWComplex n
    map n (diskRelCWComplexTopCell n) x = (diskHomeomorphClosedBall n).symm x :=
  -- `RelCWComplex.mkFinite` takes the supplied family as its `map` field, so the characteristic
  -- map of the top cell is `diskCellMap n` by definition.
  diskCellMap_apply n x.2

section Sigma

variable {ι : Type u} (n : ι → ℕ)

/-- **Disjoint unions of disks relative to their boundaries.** For a family of dimensions
`n : ι → ℕ`, the disjoint union of the disks `TopCat.disk (n i)` is a relative CW complex over the
disjoint union of their boundary spheres, with one cell for each `i`, of dimension `n i`
(`TauCeti.sigmaDiskRelCWComplexCellEquiv`), whose characteristic map is that of the `i`-th disk
followed by the summand inclusion (`TauCeti.sigmaDiskRelCWComplex_map_apply`). -/
@[instance_reducible]
def sigmaDiskRelCWComplex :
    RelCWComplex (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i))))
      (univ.sigma fun i ↦ range (TopCat.diskBoundaryInclusion.{u} (n i))) :=
  letI := fun i ↦ diskRelCWComplex (n i)
  RelCWComplex.sigma _ _

/-- The `m`-cells of the disjoint union of the disks `TopCat.disk (n i)` are the indices `i` with
`n i = m`. -/
def sigmaDiskRelCWComplexCellEquiv (m : ℕ) :
    letI := sigmaDiskRelCWComplex n
    cell (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i)))) m ≃ {i // n i = m} :=
  letI := fun i ↦ diskRelCWComplex (n i)
  (RelCWComplex.sigmaCellEquiv _ _ m).trans
    { toFun c := ⟨c.1, (diskRelCWComplexCellEquiv (n c.1) m c.2).down.symm⟩
      invFun i := ⟨i.1, (diskRelCWComplexCellEquiv (n i.1) m).symm ⟨i.2.symm⟩⟩
      left_inv c := Sigma.ext rfl (heq_of_eq ((diskRelCWComplexCellEquiv (n c.1) m).injective
        (Subsingleton.elim _ _)))
      right_inv _ := rfl }

/-- The cell of the disjoint union of disks given by the `i`-th disk, of dimension `n i`. -/
def sigmaDiskRelCWComplexCell (i : ι) :
    letI := sigmaDiskRelCWComplex n
    cell (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i)))) (n i) :=
  letI := fun i ↦ diskRelCWComplex (n i)
  (RelCWComplex.sigmaCellEquiv _ _ (n i)).symm ⟨i, diskRelCWComplexTopCell (n i)⟩

/-- Under `TauCeti.sigmaDiskRelCWComplexCellEquiv`, the cell of the `i`-th disk is the index
`i`. -/
@[simp]
theorem sigmaDiskRelCWComplexCellEquiv_cell (i : ι) :
    sigmaDiskRelCWComplexCellEquiv n (n i) (sigmaDiskRelCWComplexCell n i) = ⟨i, rfl⟩ := by
  rw [sigmaDiskRelCWComplexCellEquiv, sigmaDiskRelCWComplexCell, Equiv.trans_apply,
    Equiv.apply_symm_apply]
  rfl

/-- The characteristic map of the cell of the `i`-th disk in the disjoint union is the
characteristic map of that disk followed by the summand inclusion. -/
theorem sigmaDiskRelCWComplex_map_apply (i : ι) (x : closedBall (0 : Fin (n i) → ℝ) 1) :
    letI := sigmaDiskRelCWComplex n
    map (n i) (sigmaDiskRelCWComplexCell n i) x =
      ⟨i, (diskHomeomorphClosedBall (n i)).symm x⟩ := by
  let := fun i ↦ diskRelCWComplex.{u} (n i)
  rw [sigmaDiskRelCWComplexCell, RelCWComplex.coe_map_sigma, Function.comp_apply,
    diskRelCWComplex_map_apply]

/-- The inclusion of the disjoint union of the boundary spheres into the disjoint union of the
disks. -/
private def sigmaDiskBoundaryInclusion (s : Σ i, TopCat.diskBoundary.{u} (n i)) :
    Σ i, TopCat.disk.{u} (n i) :=
  ⟨s.1, TopCat.diskBoundaryInclusion (n s.1) s.2⟩

private theorem isEmbedding_sigmaDiskBoundaryInclusion :
    IsEmbedding (sigmaDiskBoundaryInclusion.{u} n) :=
  (isEmbedding_sigmaMap (σ := fun i ↦ TopCat.diskBoundary.{u} (n i))
    (τ := fun i ↦ TopCat.disk.{u} (n i)) (f₁ := id)
    (f₂ := fun i ↦ ⇑(TopCat.diskBoundaryInclusion.{u} (n i))) Function.injective_id).2 fun i ↦
      (TopCat.isClosedEmbedding_diskBoundaryInclusion (n i)).isEmbedding

/-- The base of the disjoint union of disks, the disjoint union of their boundary spheres as a
subset of `Σ i, TopCat.disk (n i)`, is homeomorphic to `Σ i, TopCat.diskBoundary (n i)`. -/
def sigmaDiskBoundaryHomeomorph :
    (univ.sigma fun i ↦ range (TopCat.diskBoundaryInclusion.{u} (n i))) ≃ₜ
      Σ i, TopCat.diskBoundary.{u} (n i) :=
  ((isEmbedding_sigmaDiskBoundaryInclusion n).toHomeomorph.trans
    (Homeomorph.setCongr
      (sigma_univ_range_eq (f := fun i ↦ ⇑(TopCat.diskBoundaryInclusion.{u} (n i)))).symm)).symm

/-- The point of the base of the disjoint union of disks corresponding to a point `s` of the
boundary of the `i`-th disk is the image of `s` in that disk. -/
@[simp]
theorem coe_sigmaDiskBoundaryHomeomorph_symm_apply (s : Σ i, TopCat.diskBoundary.{u} (n i)) :
    ((sigmaDiskBoundaryHomeomorph n).symm s : Σ i, TopCat.disk.{u} (n i)) =
      ⟨s.1, TopCat.diskBoundaryInclusion (n s.1) s.2⟩ :=
  (rfl)

variable {n} {Z : Type*} [TopologicalSpace Z]

/-- A family of attaching maps `a i` out of the boundary spheres of the disks `TopCat.disk (n i)`,
as a single map out of the base of `TauCeti.sigmaDiskRelCWComplex n`. Gluing the disjoint union
of disks to `Z` along it attaches one `n i`-cell to `Z` along each `a i`. -/
def sigmaDiskAttachingMap (a : ∀ i, C(TopCat.diskBoundary.{u} (n i), Z)) :
    C(univ.sigma fun i ↦ range (TopCat.diskBoundaryInclusion.{u} (n i)), Z) :=
  (ContinuousMap.sigma a).comp (sigmaDiskBoundaryHomeomorph n)

/-- The attaching map of the disjoint union of disks is `a i` on the boundary of the `i`-th
disk. -/
@[simp]
theorem sigmaDiskAttachingMap_apply (a : ∀ i, C(TopCat.diskBoundary.{u} (n i), Z)) (i : ι)
    (s : TopCat.diskBoundary.{u} (n i)) :
    sigmaDiskAttachingMap a ((sigmaDiskBoundaryHomeomorph n).symm ⟨i, s⟩) = a i s := by
  simp [sigmaDiskAttachingMap]

/-- **Attaching cells along a family of maps.** Gluing the disjoint union of the disks
`TopCat.disk (n i)` to a space `Y` along `TauCeti.sigmaDiskAttachingMap b` gives a relative CW
complex over `Y` (`TauCeti.relativeCWPushout`) whose `m`-cells are the indices `i` with
`n i = m`: one `n i`-cell is attached along each `b i`. -/
def sigmaDiskAdjunctionSpaceCellEquiv {Y : Type u} [TopologicalSpace Y]
    (b : ∀ i, C(TopCat.diskBoundary.{u} (n i), Y)) (m : ℕ) :
    letI := sigmaDiskRelCWComplex n
    letI := relativeCWPushout (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i))))
      (sigmaDiskAttachingMap b)
    cell (univ : Set (relCWAdjunctionSpace
      (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n i)))) (sigmaDiskAttachingMap b))) m ≃
        {i // n i = m} :=
  letI := sigmaDiskRelCWComplex n
  (relativeCWPushoutCellEquiv _ _ m).trans (sigmaDiskRelCWComplexCellEquiv n m)

end Sigma

end TauCeti
