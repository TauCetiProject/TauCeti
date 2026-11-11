/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Disk
public import TauCeti.Topology.Category.TopCat.ClosedEmbedding
public import TauCeti.Topology.Category.TopCat.DisjointOpens
public import TauCeti.Topology.Separation.Sigma

/-!
# Products of disks and handle attachments

A handle of index `k` is a product `𝔻 k × Y` of the closed disk `𝔻 k` with a second factor `Y`,
in Morse theory the disk `𝔻 l` of the complementary dimension. It is attached to a space along
its attaching region `∂𝔻 k × Y`. This file supplies the point-set topology of handles and of the
spaces obtained by attaching them.

* The product `𝔻 k × 𝔻 l` of two disks is homeomorphic to the disk `𝔻 (k + l)`
  (`TauCeti.TopCat.diskProdHomeomorph`): both factors are read as cubes by
  `TauCeti.TopCat.diskHomeomorphCube` and their coordinates are concatenated by `Fin.append`. The
  boundary sphere of `𝔻 (k + l)` corresponds to the boundary `∂𝔻 k × 𝔻 l ∪ 𝔻 k × ∂𝔻 l` of the
  product (`TauCeti.TopCat.diskProdHomeomorph_mem_range_diskBoundaryInclusion_iff`). The handle
  `𝔻 k × 𝔻 l` is also compact, Hausdorff and contractible, by the instances on each factor
  (`TauCeti.TopCat.compactSpace_disk`, `TauCeti.TopCat.t3Space_disk`,
  `TauCeti.TopCat.contractibleSpace_disk`). Its attaching region `∂𝔻 k × 𝔻 l` is empty for
  `k = 0` (`TauCeti.isEmpty_diskBoundary_zero`), so a handle of index `0` is attached
  along nothing, and compact and nonempty for `k ≥ 1`
  (`TauCeti.nonempty_diskBoundary_succ`).
* The inclusion `∂𝔻 k × Y ⟶ 𝔻 k × Y` of the attaching region is a closed embedding
  (`TauCeti.TopCat.isClosedEmbedding_diskBoundaryInclusion_prodMap`) which extends disjoint open
  sets (`TauCeti.TopCat.extendsDisjointOpens_diskBoundaryInclusion_prodMap`): an open subset `U`
  of `∂𝔻 k × Y` is the trace of the open set of the points `(x, y)` with `1 / 2 < ‖x‖` and
  `(x / ‖x‖, y) ∈ U`. Taking `Y` to be a point, so does the inclusion `∂𝔻 k ⟶ 𝔻 k` of the
  boundary sphere (`TauCeti.TopCat.extendsDisjointOpens_diskBoundaryInclusion`).
* Consequently, in a pushout square in `TopCat` attaching a family of handles `𝔻 (k i) × Y i` to a
  space `X` along any map out of their attaching regions, the inclusion of `X` is a closed
  embedding (`TauCeti.TopCat.isClosedEmbedding_of_isPushout_handles`), and the resulting space is
  Hausdorff when `X` is Hausdorff and each `Y i` is regular and Hausdorff
  (`TauCeti.TopCat.t2Space_of_isPushout_handles`). The family need not be finite.

The handle attachment across a critical level of a Morse function,
`TauCeti.IsMorse.exists_isPushout_sublevel_handles`, is a pushout square of exactly this form, with
`Y i = 𝔻 (n - k i)` in dimension `n`.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §3.
* L. I. Nicolaescu, *An Invitation to Morse Theory*, author version of the 2nd edition, §2.2,
  pp. 34–35, for handles and their attaching regions.
-/

public section

noncomputable section

open CategoryTheory Limits Topology

universe u

namespace TauCeti.TopCat

/-! ### Products of disks -/

section Prod

variable (k l : ℕ)

/-- The product `𝔻 k × 𝔻 l` of two Euclidean disks is homeomorphic to the disk `𝔻 (k + l)`: both
factors are read as cubes by `TauCeti.TopCat.diskHomeomorphCube`, and the coordinates of the two
cubes are concatenated by `Fin.append`. -/
def diskProdHomeomorph : TopCat.disk.{u} k × TopCat.disk.{u} l ≃ₜ TopCat.disk.{u} (k + l) :=
  ((diskHomeomorphCube k).prodCongr (diskHomeomorphCube l)).trans
    ((Fin.appendHomeomorph k l).trans (diskHomeomorphCube (k + l)).symm)

variable {k l}

/-- Read in the cube, `TauCeti.TopCat.diskProdHomeomorph` concatenates the coordinates of the two
factors. -/
@[simp]
theorem diskHomeomorphCube_diskProdHomeomorph (z : TopCat.disk.{u} k × TopCat.disk.{u} l) :
    diskHomeomorphCube (k + l) (diskProdHomeomorph k l z) =
      Fin.append (diskHomeomorphCube k z.1) (diskHomeomorphCube l z.2) := by
  ext i
  simp [diskProdHomeomorph]

/-- Read in the cube, the first factor of the inverse of `TauCeti.TopCat.diskProdHomeomorph`
consists of the first `k` coordinates. -/
@[simp]
theorem diskHomeomorphCube_diskProdHomeomorph_symm_fst (w : TopCat.disk.{u} (k + l)) :
    diskHomeomorphCube k ((diskProdHomeomorph k l).symm w).1 =
      fun i ↦ diskHomeomorphCube (k + l) w (Fin.castAdd l i) := by
  conv_rhs => rw [← (diskProdHomeomorph k l).apply_symm_apply w]
  ext i
  rw [diskHomeomorphCube_diskProdHomeomorph, Fin.append_left]

/-- Read in the cube, the second factor of the inverse of `TauCeti.TopCat.diskProdHomeomorph`
consists of the last `l` coordinates. -/
@[simp]
theorem diskHomeomorphCube_diskProdHomeomorph_symm_snd (w : TopCat.disk.{u} (k + l)) :
    diskHomeomorphCube l ((diskProdHomeomorph k l).symm w).2 =
      fun i ↦ diskHomeomorphCube (k + l) w (Fin.natAdd k i) := by
  conv_rhs => rw [← (diskProdHomeomorph k l).apply_symm_apply w]
  ext i
  rw [diskHomeomorphCube_diskProdHomeomorph, Fin.append_right]

/-- `TauCeti.TopCat.diskProdHomeomorph` carries the boundary `∂𝔻 k × 𝔻 l ∪ 𝔻 k × ∂𝔻 l` of the
product of two disks onto the boundary sphere of `𝔻 (k + l)`. -/
theorem diskProdHomeomorph_mem_range_diskBoundaryInclusion_iff
    (z : TopCat.disk.{u} k × TopCat.disk.{u} l) :
    diskProdHomeomorph k l z ∈ Set.range (TopCat.diskBoundaryInclusion.{u} (k + l)) ↔
      z.1 ∈ Set.range (TopCat.diskBoundaryInclusion.{u} k) ∨
        z.2 ∈ Set.range (TopCat.diskBoundaryInclusion.{u} l) := by
  simp only [← diskHomeomorphCube_mem_boundary_iff, diskHomeomorphCube_diskProdHomeomorph,
    Cube.boundary, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨i, hi⟩
    induction i using Fin.addCases with
    | left i => exact .inl ⟨i, by simpa using hi⟩
    | right i => exact .inr ⟨i, by simpa using hi⟩
  · rintro (⟨i, hi⟩ | ⟨i, hi⟩)
    · exact ⟨Fin.castAdd l i, by simpa using hi⟩
    · exact ⟨Fin.natAdd k i, by simpa using hi⟩

end Prod

/-! ### The attaching region of a handle -/

section AttachingRegion

variable (k : ℕ) (Y : Type u) [TopologicalSpace Y]

/-- The inclusion `∂𝔻 k × Y → 𝔻 k × Y` of the attaching region of a handle `𝔻 k × Y` is a closed
embedding. -/
theorem isClosedEmbedding_diskBoundaryInclusion_prodMap :
    IsClosedEmbedding ((TopCat.diskBoundaryInclusion.{u} k).hom.prodMap (ContinuousMap.id Y)) :=
  (isClosedEmbedding_diskBoundaryInclusion k).prodMap .id

/-- The inclusion `∂𝔻 k × Y ⟶ 𝔻 k × Y` of the attaching region of a handle `𝔻 k × Y` extends
disjoint open sets: an open subset `U` of `∂𝔻 k × Y` is the trace of the open set of the points
`(x, y)` with `1 / 2 < ‖x‖` and `(x / ‖x‖, y) ∈ U`, and these sets are disjoint over disjoint
sets. -/
theorem extendsDisjointOpens_diskBoundaryInclusion_prodMap :
    extendsDisjointOpens
      (TopCat.ofHom ((TopCat.diskBoundaryInclusion.{u} k).hom.prodMap (ContinuousMap.id Y))) := by
  -- The points of the disk and of its boundary as vectors of `E`. The carriers of `TopCat.disk k`
  -- and `TopCat.diskBoundary k` are, by definition, the lifts of the closed unit ball and of the
  -- unit sphere; the ascriptions expose these carriers, which the `TopCat` wrappers hide.
  let ν (z : TopCat.disk.{u} k) : EuclideanSpace ℝ (Fin k) :=
    ((z : ULift.{u} (Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1)).down :
      EuclideanSpace ℝ (Fin k))
  let μ (s : TopCat.diskBoundary.{u} k) : EuclideanSpace ℝ (Fin k) :=
    ((s : ULift.{u} (Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1)).down :
      EuclideanSpace ℝ (Fin k))
  have hμ : IsEmbedding μ := IsEmbedding.subtypeVal.comp IsEmbedding.uliftDown
  have hνμ (s : TopCat.diskBoundary.{u} k) : ν (TopCat.diskBoundaryInclusion k s) = μ s :=
    coe_diskBoundaryInclusion_apply_down k s
  have hμ₁ (s : TopCat.diskBoundary.{u} k) : ‖μ s‖ = 1 := mem_sphere_zero_iff_norm.1
    (s : ULift.{u} (Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1)).down.2
  have hν : Continuous ν := continuous_subtype_val.comp continuous_uliftDown
  -- The radial projection in the first factor, continuous away from the centre of the disk,
  -- retracts a neighbourhood of the attaching region onto it.
  refine extendsDisjointOpens_of_continuousOn _ (hμ.isInducing.prodMap IsInducing.id)
    (N := {z | 1 / 2 < ‖ν z.1‖}) (ρ := fun z ↦ (‖ν z.1‖⁻¹ • ν z.1, z.2))
    (isOpen_lt continuous_const (hν.norm.comp continuous_fst))
    ((((ContinuousOn.inv₀ (hν.norm.comp continuous_fst).continuousOn fun z hz ↦
      (lt_trans (by norm_num) hz).ne').smul (hν.comp continuous_fst).continuousOn).prodMk
        continuous_snd.continuousOn)) (fun s ↦ ?_) (fun z hz ↦ ?_) (fun s ↦ ?_)
  · simp [hνμ, hμ₁, show (2 : ℝ)⁻¹ < 1 by norm_num]
  · have h₁ : ‖‖ν z.1‖⁻¹ • ν z.1‖ = 1 :=
      norm_smul_inv_norm (𝕜 := ℝ) (norm_pos_iff.1 (lt_trans (by norm_num) hz))
    exact ⟨(ULift.up ⟨_, mem_sphere_zero_iff_norm.2 h₁⟩, z.2), rfl⟩
  · simp [hνμ, hμ₁, Prod.map]

/-- The inclusion `∂𝔻 k ⟶ 𝔻 k` of the boundary sphere of the disk extends disjoint open sets: an
open subset `U` of the sphere is the trace of the open cone `{x | 1 / 2 < ‖x‖ ∧ x / ‖x‖ ∈ U}`,
and the cones over disjoint sets are disjoint. This is the attaching region of a handle whose
second factor is a point (`TauCeti.TopCat.extendsDisjointOpens_diskBoundaryInclusion_prodMap`). -/
theorem extendsDisjointOpens_diskBoundaryInclusion :
    extendsDisjointOpens (TopCat.diskBoundaryInclusion.{u} k) :=
  (extendsDisjointOpens.arrow_mk_iso_iff (Arrow.isoMk (TopCat.isoOfHomeo (Homeomorph.prodPUnit _))
    -- Both composites of the square send `(s, ⋆)` to the boundary point `s` of the disk.
    (TopCat.isoOfHomeo (Homeomorph.prodPUnit _)) (by ext; rfl))).1
      (extendsDisjointOpens_diskBoundaryInclusion_prodMap k PUnit)

end AttachingRegion

/-! ### Attaching handles -/

section Pushout

variable {ι : Type u} {k : ι → ℕ} {Y : ι → TopCat.{u}} {X P : TopCat.{u}}
  {g : (∐ fun i ↦ TopCat.of (TopCat.diskBoundary.{u} (k i) × Y i)) ⟶ X} {j : X ⟶ P}
  {χ : (∐ fun i ↦ TopCat.of (TopCat.disk.{u} (k i) × Y i)) ⟶ P}

/-- **Attaching handles embeds the old space as a closed subspace.** In a pushout square in
`TopCat` attaching handles `𝔻 (k i) × Y i` to `X` along any map `g` out of their attaching regions
`∂𝔻 (k i) × Y i`, the inclusion `j` of `X` is a closed embedding. -/
theorem isClosedEmbedding_of_isPushout_handles
    (sq : IsPushout g (Limits.Sigma.map fun i ↦ TopCat.ofHom
      ((TopCat.diskBoundaryInclusion (k i)).hom.prodMap (ContinuousMap.id (Y i)))) j χ) :
    IsClosedEmbedding j :=
  isClosedEmbedding_of_isPushout sq (isClosedEmbedding_sigmaMap _ fun i ↦
    isClosedEmbedding_diskBoundaryInclusion_prodMap (k i) (Y i))

/-- **Attaching handles to a Hausdorff space gives a Hausdorff space.** In a pushout square in
`TopCat` attaching handles `𝔻 (k i) × Y i` to a Hausdorff space `X` along any map `g` out of their
attaching regions `∂𝔻 (k i) × Y i`, the resulting space `P` is Hausdorff, provided each `Y i` is
regular and Hausdorff, for instance a disk. The family of handles need not be finite. -/
theorem t2Space_of_isPushout_handles [T2Space X] [∀ i, T2Space (Y i)] [∀ i, RegularSpace (Y i)]
    (sq : IsPushout g (Limits.Sigma.map fun i ↦ TopCat.ofHom
      ((TopCat.diskBoundaryInclusion (k i)).hom.prodMap (ContinuousMap.id (Y i)))) j χ) :
    T2Space P := by
  -- The coproduct of the handles is their disjoint union, a regular Hausdorff space.
  let e := TopCat.homeoOfIso
    (TopCat.sigmaIsoSigma.{u, u} fun i ↦ TopCat.of (TopCat.disk.{u} (k i) × Y i))
  -- The carrier of `TopCat.of` of the sigma type is the sigma type, which instance search does
  -- not see through the wrapper.
  have : T2Space (TopCat.of (Σ i, TopCat.disk.{u} (k i) × Y i)) :=
    inferInstanceAs (T2Space (Σ i, TopCat.disk.{u} (k i) × Y i))
  have : RegularSpace (TopCat.of (Σ i, TopCat.disk.{u} (k i) × Y i)) :=
    inferInstanceAs (RegularSpace (Σ i, TopCat.disk.{u} (k i) × Y i))
  have : T2Space ((∐ fun i ↦ TopCat.of (TopCat.disk.{u} (k i) × Y i) : TopCat.{u})) :=
    e.isEmbedding.t2Space
  have : RegularSpace ((∐ fun i ↦ TopCat.of (TopCat.disk.{u} (k i) × Y i) : TopCat.{u})) :=
    e.isEmbedding.isInducing.regularSpace
  exact t2Space_of_isPushout sq
    (MorphismProperty.colimMap _ fun ⟨i⟩ ↦ extendsDisjointOpens_diskBoundaryInclusion_prodMap
      (k i) (Y i))
    (isClosedEmbedding_sigmaMap _ fun i ↦
      isClosedEmbedding_diskBoundaryInclusion_prodMap (k i) (Y i)).isClosed_range

end Pushout

end TauCeti.TopCat
