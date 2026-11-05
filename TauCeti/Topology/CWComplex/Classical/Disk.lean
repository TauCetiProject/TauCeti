/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.CWComplex.Classical.Finite
public import TauCeti.Topology.CWComplex.Abstract.AttachCells
public import TauCeti.Topology.CWComplex.Classical.Sigma

/-!
# The disk relative to its boundary sphere

The Euclidean disk `𝔻 n` is obtained from its boundary sphere `∂𝔻 n` by attaching a single
`n`-cell along the identity of the sphere (`TauCeti.diskAttachCells`). Read through the comparison
`TopCat.RelativeCWComplex.toRelCWComplex`, this makes the whole disk a classical relative CW
complex relative to its boundary sphere (`TauCeti.diskBoundaryRelCW`), with exactly one cell, in
dimension `n`, whose characteristic map is the inverse of the radial identification
`TauCeti.diskHomeomorphClosedBall` of the disk with the closed unit ball of the sup norm
(`TauCeti.map_diskBoundaryRelCW`). For `n = 0` the boundary sphere is empty and the cell is the
single point of the disk.

An arbitrary disjoint union of disks `Σ i, 𝔻 (n i)` is then a relative CW complex relative to the
disjoint union of the boundary spheres (`TauCeti.diskSigmaRelCW`), with one `n i`-cell for each
summand `i` (`TauCeti.diskSigmaRelCWCellEquiv`). Its base is homeomorphic to the disjoint union
`Σ i, ∂𝔻 (n i)` of the boundary spheres themselves (`TauCeti.diskSigmaBoundaryHomeomorph`), so a
family of attaching maps `∂𝔻 (n i) → Z` is a single map out of the base. These disk pairs are the
cells attached in a relative CW pushout, for instance at each critical level of a Morse function.

## Main definitions

* `TauCeti.diskAttachCells n`: the boundary inclusion `∂𝔻 n ⟶ 𝔻 n` attaches one `n`-cell.
* `TauCeti.diskBoundaryRelCW n`: the relative CW structure on `𝔻 n` relative to its boundary.
* `TauCeti.diskBoundaryRangeHomeomorph n`: the base of `TauCeti.diskBoundaryRelCW n` is
  homeomorphic to `∂𝔻 n`.
* `TauCeti.diskSigmaRelCW n`: the relative CW structure on a disjoint union of disks.
* `TauCeti.diskSigmaRelCWCellEquiv n m`: its `m`-cells are the summands of dimension `m`.
* `TauCeti.diskSigmaBoundaryHomeomorph n`: its base is homeomorphic to `Σ i, ∂𝔻 (n i)`.

## Main results

* `TauCeti.isEmpty_cell_diskBoundaryRelCW` and the `Unique` instance on its `n`-cells:
  `TauCeti.diskBoundaryRelCW n` has a single cell, of dimension `n`.
* `TauCeti.map_diskBoundaryRelCW`: its characteristic map is `(diskHomeomorphClosedBall n).symm`.
* `TauCeti.map_diskSigmaRelCW`: the characteristic map of the cell of the summand `i` of
  `TauCeti.diskSigmaRelCW n` is that of the disk `𝔻 (n i)` followed by the summand inclusion.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0 (cell complexes) and the Appendix (CW complexes).
-/

public section

noncomputable section

open CategoryTheory Limits Topology Metric Set HomotopicalAlgebra Topology.RelCWComplex

universe u

namespace TauCeti

section Disk

/-- **The disk is its boundary sphere with one cell attached.** The boundary inclusion
`∂𝔻 n ⟶ 𝔻 n` attaches a single `n`-cell, along the identity of the sphere: the square with the
boundary inclusion on both vertical sides and identities on both horizontal sides is a pushout. -/
def diskAttachCells (n : ℕ) :
    AttachCells.{u} (TopCat.RelativeCWComplex.basicCell n)
      (TopCat.diskBoundaryInclusion.{u} n) where
  ι := PUnit.{u + 1}
  π _ := ()
  cofan₁ := Cofan.mk (TopCat.diskBoundary n) fun _ ↦ 𝟙 _
  cofan₂ := Cofan.mk (TopCat.disk n) fun _ ↦ 𝟙 _
  isColimit₁ := Cofan.isColimitMkOfUnique (Iso.refl _) _
  isColimit₂ := Cofan.isColimitMkOfUnique (Iso.refl _) _
  m := TopCat.diskBoundaryInclusion n
  g₁ := 𝟙 _
  g₂ := 𝟙 _
  isPushout := IsPushout.of_horiz_isIso ⟨by simp⟩

/-- The single cell of `TauCeti.diskAttachCells n` is the identity of the disk. -/
@[simp]
theorem diskAttachCells_cell (n : ℕ) (i : (diskAttachCells.{u} n).ι) :
    (diskAttachCells.{u} n).cell i = 𝟙 _ := by
  rw [AttachCells.cell_def]
  simp [diskAttachCells]

/-- **The disk relative to its boundary sphere is a relative CW complex.** The whole disk `𝔻 n`
is a classical relative CW complex relative to the image of its boundary sphere, with a single
cell, of dimension `n` (`TauCeti.isEmpty_cell_diskBoundaryRelCW`), whose characteristic map is
the inverse of the radial identification `TauCeti.diskHomeomorphClosedBall n` of the disk with
the closed unit ball of the sup norm (`TauCeti.map_diskBoundaryRelCW`). This is not an instance,
since the base of a relative CW structure is an output parameter. -/
@[instance_reducible]
def diskBoundaryRelCW (n : ℕ) :
    RelCWComplex (univ : Set (TopCat.disk.{u} n)) (range (TopCat.diskBoundaryInclusion.{u} n)) :=
  (diskAttachCells n).toRelativeCWComplex.toRelCWComplex

/-- `TauCeti.diskBoundaryRelCW n` has no cells outside dimension `n`. -/
theorem isEmpty_cell_diskBoundaryRelCW {n m : ℕ} (hm : m ≠ n) :
    IsEmpty (@cell _ _ (univ : Set (TopCat.disk.{u} n)) _ (diskBoundaryRelCW n) m) :=
  (diskAttachCells n).isEmpty_cell_toRelCWComplex hm

/-- The cells of `TauCeti.diskBoundaryRelCW k` of dimension `m`: there is one if `k = m`, and
none otherwise. -/
def diskBoundaryRelCWCellEquiv (k m : ℕ) :
    @cell _ _ (univ : Set (TopCat.disk.{u} k)) _ (diskBoundaryRelCW k) m ≃ PLift (k = m) :=
  have : Subsingleton (@cell _ _ (univ : Set (TopCat.disk.{u} k)) _ (diskBoundaryRelCW k) m) := by
    obtain rfl | hm := eq_or_ne m k
    · exact Equiv.subsingleton (β := PUnit.{u + 1}) (diskAttachCells m).cellToRelCWComplexEquiv
    · have := isEmpty_cell_diskBoundaryRelCW.{u} hm
      infer_instance
  equivOfSubsingletonOfSubsingleton
    (fun j ↦ ⟨by_contra fun h ↦ (isEmpty_cell_diskBoundaryRelCW.{u} (Ne.symm h)).false j⟩)
    (fun h ↦ by
      obtain ⟨rfl⟩ := h
      exact (diskAttachCells k).cellToRelCWComplexEquiv.symm PUnit.unit)

/-- `TauCeti.diskBoundaryRelCW n` has exactly one cell of dimension `n`. -/
instance uniqueCellDiskBoundaryRelCW (n : ℕ) :
    Unique (@cell _ _ (univ : Set (TopCat.disk.{u} n)) _ (diskBoundaryRelCW n) n) where
  default := (diskBoundaryRelCWCellEquiv n n).symm ⟨rfl⟩
  uniq _ := (diskBoundaryRelCWCellEquiv n n).injective (Subsingleton.elim _ _)

/-- `TauCeti.diskBoundaryRelCW n` is a finite relative CW complex. -/
instance finiteDiskBoundaryRelCW (n : ℕ) :
    @RelCWComplex.Finite _ _ (univ : Set (TopCat.disk.{u} n)) _ (diskBoundaryRelCW n) :=
  letI := diskBoundaryRelCW.{u} n
  { eventually_isEmpty_cell := Filter.eventually_atTop.2
      ⟨n + 1, fun _ hm ↦ isEmpty_cell_diskBoundaryRelCW (by omega)⟩
    finite_cell m := by
      obtain rfl | hm := eq_or_ne m n
      · infer_instance
      · have := isEmpty_cell_diskBoundaryRelCW.{u} hm
        infer_instance }

/-- The characteristic map of the cell of `TauCeti.diskBoundaryRelCW n` is the inverse of the
radial identification `TauCeti.diskHomeomorphClosedBall n` of the disk with the closed unit ball
of the sup norm. -/
theorem map_diskBoundaryRelCW (n : ℕ)
    (j : @cell _ _ (univ : Set (TopCat.disk.{u} n)) _ (diskBoundaryRelCW n) n)
    (x : closedBall (0 : Fin n → ℝ) 1) :
    @map _ _ _ _ (diskBoundaryRelCW n) n j x = (diskHomeomorphClosedBall n).symm x := by
  have h := (diskAttachCells n).map_cellToRelCWComplexEquiv_symm
    ((diskAttachCells n).cellToRelCWComplexEquiv j) x
  rw [Equiv.symm_apply_apply, diskAttachCells_cell] at h
  exact h.trans rfl

/-- The base of `TauCeti.diskBoundaryRelCW n`, the image of the boundary sphere in the disk, is
homeomorphic to the boundary sphere `∂𝔻 n` by the boundary inclusion. -/
def diskBoundaryRangeHomeomorph (n : ℕ) :
    range (TopCat.diskBoundaryInclusion.{u} n) ≃ₜ TopCat.diskBoundary.{u} n :=
  (TopCat.isClosedEmbedding_diskBoundaryInclusion n).isEmbedding.toHomeomorph.symm

@[simp]
theorem coe_diskBoundaryRangeHomeomorph_symm_apply (n : ℕ) (s : TopCat.diskBoundary.{u} n) :
    ((diskBoundaryRangeHomeomorph n).symm s : TopCat.disk.{u} n) =
      TopCat.diskBoundaryInclusion n s :=
  (rfl)

@[simp]
theorem diskBoundaryInclusion_diskBoundaryRangeHomeomorph_apply (n : ℕ)
    (z : range (TopCat.diskBoundaryInclusion.{u} n)) :
    TopCat.diskBoundaryInclusion n (diskBoundaryRangeHomeomorph n z) = z := by
  rw [← coe_diskBoundaryRangeHomeomorph_symm_apply, Homeomorph.symm_apply_apply]

end Disk

section Sigma

variable {ι : Type u} (n : ι → ℕ)

/-- **A disjoint union of disks relative to their boundary spheres is a relative CW complex.**
The whole of `Σ i, 𝔻 (n i)` is a relative CW complex relative to the disjoint union of the
images of the boundary spheres, with one `n i`-cell for each summand `i`
(`TauCeti.diskSigmaRelCWCellEquiv`), whose characteristic map is that of
`TauCeti.diskBoundaryRelCW (n i)` followed by the summand inclusion
(`TauCeti.map_diskSigmaRelCW`). This is not an instance, since the base of a relative CW
structure is an output parameter. -/
@[instance_reducible]
def diskSigmaRelCW :
    RelCWComplex (univ : Set (Σ i, TopCat.disk.{u} (n i)))
      (univ.sigma fun i ↦ range (TopCat.diskBoundaryInclusion.{u} (n i))) :=
  letI (i : ι) := diskBoundaryRelCW.{u} (n i)
  RelCWComplex.sigmaUniv _

/-- The `m`-cells of `TauCeti.diskSigmaRelCW n` are the summands `i` with `n i = m`: each disk
`𝔻 (n i)` contributes its single cell. -/
def diskSigmaRelCWCellEquiv (m : ℕ) :
    @cell _ _ (univ : Set (Σ i, TopCat.disk.{u} (n i))) _ (diskSigmaRelCW n) m ≃
      {i // n i = m} :=
  letI (i : ι) := diskBoundaryRelCW.{u} (n i)
  (RelCWComplex.sigmaUnivCellEquiv _ m).trans
    ((Equiv.sigmaCongrRight fun i ↦ diskBoundaryRelCWCellEquiv (n i) m).trans
      (Equiv.sigmaPLiftEquivSubtype _))

/-- A disjoint union of finitely many disks is a finite relative CW complex relative to the
boundary spheres. -/
instance finiteDiskSigmaRelCW [Finite ι] :
    @RelCWComplex.Finite _ _ (univ : Set (Σ i, TopCat.disk.{u} (n i))) _ (diskSigmaRelCW n) :=
  letI := diskSigmaRelCW n
  { eventually_isEmpty_cell := by
      obtain ⟨N, hN⟩ := (finite_range n).bddAbove
      refine Filter.eventually_atTop.2 ⟨N + 1, fun m hm ↦
        (diskSigmaRelCWCellEquiv n m).isEmpty_congr.2 ⟨fun i ↦ ?_⟩⟩
      have := hN ⟨i.1, rfl⟩
      have := i.2
      omega
    finite_cell m := (diskSigmaRelCWCellEquiv n m).finite_iff.2 inferInstance }

/-- The characteristic map of the cell of the summand `i` of `TauCeti.diskSigmaRelCW n` is the
inverse of the radial identification `TauCeti.diskHomeomorphClosedBall (n i)` followed by the
inclusion of the summand. -/
theorem map_diskSigmaRelCW (i : ι) (x : closedBall (0 : Fin (n i) → ℝ) 1) :
    @map _ _ _ _ (diskSigmaRelCW n) (n i) ((diskSigmaRelCWCellEquiv n (n i)).symm ⟨i, rfl⟩) x =
      ⟨i, (diskHomeomorphClosedBall (n i)).symm x⟩ := by
  let (i : ι) := diskBoundaryRelCW.{u} (n i)
  -- The cell of the summand `i` is the summand's unique cell, with its summand index.
  have h : (diskSigmaRelCWCellEquiv n (n i)).symm ⟨i, rfl⟩ =
      (RelCWComplex.sigmaUnivCellEquiv _ (n i)).symm ⟨i, default⟩ :=
    (diskSigmaRelCWCellEquiv n (n i)).symm_apply_eq.2 <| Subtype.ext <| by
      simp [diskSigmaRelCWCellEquiv, Equiv.sigmaPLiftEquivSubtype]
      rfl
  rw [h]
  exact (congrFun (RelCWComplex.coe_map_sigmaUniv (X := fun i ↦ TopCat.disk.{u} (n i)) _ (n i) i
    default) x).trans (congrArg (Sigma.mk i) (map_diskBoundaryRelCW (n i) default x))

/-- The base of `TauCeti.diskSigmaRelCW n` is homeomorphic to the disjoint union
`Σ i, ∂𝔻 (n i)` of the boundary spheres, by the boundary inclusions of the summands. A family of
attaching maps `∂𝔻 (n i) → Z` thus becomes a single map out of the base, by composition with
`ContinuousMap.sigma`. -/
def diskSigmaBoundaryHomeomorph :
    (univ.sigma fun i ↦ range (TopCat.diskBoundaryInclusion.{u} (n i))) ≃ₜ
      Σ i, TopCat.diskBoundary.{u} (n i) :=
  (((isEmbedding_sigmaMap (f₁ := id) Function.injective_id).2 fun i ↦
    (TopCat.isClosedEmbedding_diskBoundaryInclusion (n i)).isEmbedding).toHomeomorph.trans
      (Homeomorph.setCongr sigma_univ_range_eq.symm)).symm

@[simp]
theorem coe_diskSigmaBoundaryHomeomorph_symm_apply (s : Σ i, TopCat.diskBoundary.{u} (n i)) :
    ((diskSigmaBoundaryHomeomorph n).symm s : Σ i, TopCat.disk.{u} (n i)) =
      ⟨s.1, TopCat.diskBoundaryInclusion (n s.1) s.2⟩ :=
  (rfl)

/-- `TauCeti.diskSigmaBoundaryHomeomorph n` keeps the summand index. -/
@[simp]
theorem fst_diskSigmaBoundaryHomeomorph_apply
    (z : univ.sigma fun i ↦ range (TopCat.diskBoundaryInclusion.{u} (n i))) :
    (diskSigmaBoundaryHomeomorph n z).1 = (z : Σ i, TopCat.disk.{u} (n i)).1 := by
  conv_rhs => rw [← (diskSigmaBoundaryHomeomorph n).symm_apply_apply z]
  rw [coe_diskSigmaBoundaryHomeomorph_symm_apply]

/-- Including the boundary point given by `TauCeti.diskSigmaBoundaryHomeomorph n` into its disk
recovers the original point. -/
@[simp]
theorem sigmaMk_diskBoundaryInclusion_diskSigmaBoundaryHomeomorph_apply
    (z : univ.sigma fun i ↦ range (TopCat.diskBoundaryInclusion.{u} (n i))) :
    (⟨(diskSigmaBoundaryHomeomorph n z).1,
      TopCat.diskBoundaryInclusion _ (diskSigmaBoundaryHomeomorph n z).2⟩ :
        Σ i, TopCat.disk.{u} (n i)) = z := by
  rw [← coe_diskSigmaBoundaryHomeomorph_symm_apply, Homeomorph.symm_apply_apply]

end Sigma

end TauCeti
