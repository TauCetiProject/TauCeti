/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Disk

/-!
# The image of the boundary sphere in the disk

The boundary inclusion `∂𝔻 n ⟶ 𝔻 n` is a closed embedding, so its image, as a subspace of the disk,
is homeomorphic to the boundary sphere itself (`TauCeti.diskBoundaryRangeHomeomorph`). Likewise,
in a disjoint union of disks `Σ i, 𝔻 (n i)`, the disjoint union of the images of the boundary
spheres is homeomorphic to the disjoint union `Σ i, ∂𝔻 (n i)` of the boundary spheres
(`TauCeti.diskSigmaBoundaryHomeomorph`). These images are the bases of the relative CW structures
on disks relative to their boundaries, so these homeomorphisms turn a family of attaching maps
`∂𝔻 (n i) → Z` into a single map out of such a base.

## Main definitions

* `TauCeti.diskBoundaryRangeHomeomorph n`: the image of `∂𝔻 n` in `𝔻 n` is homeomorphic to `∂𝔻 n`.
* `TauCeti.diskSigmaBoundaryHomeomorph n`: the disjoint union of the images of the boundary spheres
  in `Σ i, 𝔻 (n i)` is homeomorphic to `Σ i, ∂𝔻 (n i)`.
-/

public section

noncomputable section

open Set Topology

universe u

namespace TauCeti

/-- The image of the boundary sphere in the disk is homeomorphic to the boundary sphere `∂𝔻 n` by
the boundary inclusion. -/
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

section Sigma

variable {ι : Type u} (n : ι → ℕ)

/-- The disjoint union of the images of the boundary spheres in `Σ i, 𝔻 (n i)` is homeomorphic to
the disjoint union `Σ i, ∂𝔻 (n i)` of the boundary spheres, by the boundary inclusions of the
summands. A family of attaching maps `∂𝔻 (n i) → Z` thus becomes a single map out of this subspace,
by composition with `ContinuousMap.sigma`. -/
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
