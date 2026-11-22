/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.CWComplex.Classical.DiscBundle
public import TauCeti.Topology.CWComplex.Classical.Pushout
public import TauCeti.Topology.FiberBundle.Separation
public import TauCeti.Topology.VectorBundle.Thom.Space
import TauCeti.Topology.CWComplex.Classical.FiniteCWType

/-!
# Cell structures of disc-bundle attachments and Thom spaces

Let `E → B` be a real vector bundle of rank `r` over a Hausdorff CW complex `B`, with
finite-dimensional model fibre and fibre inner products whose norm is continuous on the total
space. The unit disc bundle `D(E)` is a CW complex relative to the unit sphere bundle `S(E)`, with
one `(m + r)`-cell for each `m`-cell of `B` (`TauCeti.relCWComplexDiscBundleSphereBundle`, the
case of an absolute CW complex in `TauCeti.relCWComplexDiscBundle`). This file draws the two
consequences for spaces built by gluing `D(E)` along `S(E)`.

* **Attaching a disc bundle.** For any continuous map `g : S(E) → Z`, the space `Z ∪_g D(E)`, or
  more precisely any pushout `P` of `S(E) → D(E)` along `g`, is a CW complex relative to the image
  of `Z` (`CategoryTheory.IsPushout.relCWComplex`), whose `n`-cells are the `m`-cells of `B` with
  `m + r = n` (`TauCeti.discBundleAttachmentCellEquiv`). The characteristic map of each is that of
  the corresponding cell of `D(E)`, followed by `D(E) → P`
  (`TauCeti.map_discBundleAttachmentCellEquiv_symm`). No CW structure on `Z` is needed. This is
  how crossing a critical level of a Morse–Bott function, which attaches the negative disc bundle
  of each critical submanifold to the sublevel below it, acquires cells: one for each cell of the
  critical submanifold, raised in dimension by its index.
* **The Thom space.** The Thom space `Th(E) = D(E)/S(E)` (`TauCeti.thomSpace`) is a CW complex
  with one `0`-cell, the basepoint, and one `(m + r)`-cell for each `m`-cell of `B`
  (`TauCeti.thomSpaceCWComplex`, `TauCeti.thomSpaceCWComplexCellEquiv`). It is finite when `B` is
  (`TauCeti.finite_thomSpaceCWComplex`). Here `S(E)` is glued to a point, whose skeleta contain
  everything in positive dimensions, so the attaching map is cellular
  (`CategoryTheory.IsPushout.cwComplexOfMapsToSkeletonLT`). In rank zero the cells are those of
  `B` together with the basepoint, matching `TauCeti.thomSpaceHomeomorphOfSubsingleton`.

No orientation of `E` is used.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press, 1974, §18 (the cell structure of the Thom space of a bundle over a
  CW complex).
* A. Hatcher, *Vector Bundles and K-Theory*, §4.D (disc bundles and Thom spaces).
-/

public section

noncomputable section

open Bundle CategoryTheory Limits Metric Set Topology Topology.RelCWComplex

universe u

namespace TauCeti

variable {B : Type u} [TopologicalSpace B] [T2Space B] (F : Type*) [NormedAddCommGroup F]
  [NormedSpace ℝ F] [FiniteDimensional ℝ F] (E : B → Type u) [∀ b, NormedAddCommGroup (E b)]
  [∀ b, InnerProductSpace ℝ (E b)] [TopologicalSpace (TotalSpace F E)] [FiberBundle F E]
  [VectorBundle ℝ F E] [ContinuousFiberNorm F E] [CWComplex (univ : Set B)]

section Attachment

variable {Z P : TopCat.{u}} {g : TopCat.of (sphereBundle F E) ⟶ Z}
  {i : TopCat.of (discBundle F E) ⟶ P} {j : Z ⟶ P}

/-- **Attaching a disc bundle.** Let `P` be a pushout of the inclusion `S(E) → D(E)` along a map
`g : S(E) → Z`, for instance the space obtained from `Z` by attaching `D(E)` along `g`. If `B` is a
CW complex, then `P` is a CW complex relative to the image of `Z`
(`CategoryTheory.IsPushout.relCWComplex`) whose `n`-cells are the `m`-cells of `B` with
`m + r = n`, where `r` is the rank of the bundle. The characteristic maps are those of
`TauCeti.relCWComplexDiscBundleSphereBundle` followed by the map `D(E) → P`
(`CategoryTheory.IsPushout.relCWComplex_map_apply`). -/
def discBundleAttachmentCellEquiv
    (h : IsPushout (TopCat.ofHom (ContinuousMap.inclusion (sphereBundle_subset_discBundle F E)))
      g i j) (n : ℕ) :
    letI := relCWComplexDiscBundleSphereBundle F E
    letI := h.relCWComplex
    cell (univ : Set P) n ≃ Σ m : {m : ℕ // m + Module.finrank ℝ F = n}, cell (univ : Set B) m :=
  letI := relCWComplexDiscBundleSphereBundle F E
  (h.relCWComplexCellEquiv n).trans (relCWComplexDiscBundleSphereBundleCellEquiv F E n)

variable {F E}
  (h : IsPushout (TopCat.ofHom (ContinuousMap.inclusion (sphereBundle_subset_discBundle F E)))
    g i j)
  {n : ℕ} (c : Σ m : {m : ℕ // m + Module.finrank ℝ F = n}, cell (univ : Set B) m)

/-- The cell of a disc-bundle attachment over an `m`-cell of `B` is the cell of the pushout coming
from the corresponding cell of the disc bundle. -/
theorem discBundleAttachmentCellEquiv_symm_apply :
    letI := relCWComplexDiscBundleSphereBundle F E
    letI := h.relCWComplex
    (discBundleAttachmentCellEquiv F E h n).symm c =
      (h.relCWComplexCellEquiv n).symm
        ((relCWComplexDiscBundleSphereBundleCellEquiv F E n).symm c) := by
  rw [discBundleAttachmentCellEquiv, Equiv.symm_trans_apply]

/-- The characteristic map of the cell of a disc-bundle attachment over an `m`-cell of `B` is the
characteristic map of the corresponding cell of the disc bundle, followed by the map `D(E) → P`. -/
@[simp]
theorem map_discBundleAttachmentCellEquiv_symm (x : closedBall (0 : Fin n → ℝ) 1) :
    letI := relCWComplexDiscBundleSphereBundle F E
    letI := h.relCWComplex
    map n ((discBundleAttachmentCellEquiv F E h n).symm c) x =
      i ⟨map n ((relCWComplexDiscBundleSphereBundleCellEquiv F E n).symm c) x,
        closedCell_subset_complex n _ (mem_image_of_mem _ x.property)⟩ := by
  let := relCWComplexDiscBundleSphereBundle F E
  let := h.relCWComplex
  rw [h.relCWComplex_map_apply, discBundleAttachmentCellEquiv_symm_apply, Equiv.apply_symm_apply]

/-- Below the rank of the bundle, a disc-bundle attachment has no cells. -/
theorem isEmpty_cell_discBundleAttachment_of_lt {k : ℕ} (hk : k < Module.finrank ℝ F) :
    letI := relCWComplexDiscBundleSphereBundle F E
    letI := h.relCWComplex
    IsEmpty (cell (univ : Set P) k) :=
  letI := relCWComplexDiscBundleSphereBundle F E
  let := h.relCWComplex
  have := isEmpty_cell_relCWComplexDiscBundleSphereBundle_of_lt (F := F) (E := E) hk
  (h.relCWComplexCellEquiv k).isEmpty_congr.2 inferInstance

private theorem image_map_discBundleAttachment (S : Set (Fin n → ℝ)) (hS : S ⊆ closedBall 0 1) :
    letI := relCWComplexDiscBundleSphereBundle F E
    letI := h.relCWComplex
    map n ((discBundleAttachmentCellEquiv F E h n).symm c) '' S =
      i '' (Subtype.val ⁻¹'
        (map n ((relCWComplexDiscBundleSphereBundleCellEquiv F E n).symm c) '' S)) := by
  let := relCWComplexDiscBundleSphereBundle F E
  let := h.relCWComplex
  ext p
  simp only [mem_image, mem_preimage]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨_, closedCell_subset_complex n _ (mem_image_of_mem _ (hS hx))⟩,
      ⟨x, hx, rfl⟩, (map_discBundleAttachmentCellEquiv_symm h c ⟨x, hS hx⟩).symm⟩
  · rintro ⟨v, ⟨x, hx, hxv⟩, rfl⟩
    refine ⟨x, hx, ?_⟩
    rw [map_discBundleAttachmentCellEquiv_symm h c ⟨x, hS hx⟩]
    congr 1
    exact Subtype.ext hxv

/-- The open cell of a disc-bundle attachment over an `m`-cell `j` of `B` is the image under
`i : D(E) → P` of the vectors of norm less than one in `D(E)` over `openCell m j`. -/
theorem openCell_discBundleAttachment :
    letI := relCWComplexDiscBundleSphereBundle F E
    letI := h.relCWComplex
    openCell n ((discBundleAttachmentCellEquiv F E h n).symm c) =
      i '' {v : discBundle F E |
        (v : TotalSpace F E).proj ∈ openCell c.1.val c.2 ∧ ‖(v : TotalSpace F E).snd‖ < 1} := by
  let := relCWComplexDiscBundleSphereBundle F E
  let := h.relCWComplex
  rw [openCell, image_map_discBundleAttachment h c (ball 0 1) ball_subset_closedBall,
    ← openCell, openCell_relCWComplexDiscBundleSphereBundle]
  congr 1
  ext v
  simp [and_comm]

/-- The closed cell of a disc-bundle attachment over an `m`-cell `j` of `B` is the image under
`i : D(E) → P` of `D(E)` over `closedCell m j`. -/
theorem closedCell_discBundleAttachment :
    letI := relCWComplexDiscBundleSphereBundle F E
    letI := h.relCWComplex
    closedCell n ((discBundleAttachmentCellEquiv F E h n).symm c) =
      i '' (discBundleProj F E ⁻¹' closedCell c.1.val c.2) := by
  let := relCWComplexDiscBundleSphereBundle F E
  let := h.relCWComplex
  rw [closedCell, image_map_discBundleAttachment h c (closedBall 0 1) Subset.rfl,
    ← closedCell, closedCell_relCWComplexDiscBundleSphereBundle]
  congr 1
  ext v
  simp

/-- The boundary of the cell of a disc-bundle attachment over an `m`-cell `j` of `B` is the
image under `i : D(E) → P` of `S(E)` over `closedCell m j` together with `D(E)` over
`cellFrontier m j`. -/
theorem cellFrontier_discBundleAttachment :
    letI := relCWComplexDiscBundleSphereBundle F E
    letI := h.relCWComplex
    cellFrontier n ((discBundleAttachmentCellEquiv F E h n).symm c) =
      i '' (Subtype.val ⁻¹' sphereBundle F E ∩ discBundleProj F E ⁻¹' closedCell c.1.val c.2 ∪
        discBundleProj F E ⁻¹' cellFrontier c.1.val c.2) := by
  let := relCWComplexDiscBundleSphereBundle F E
  let := h.relCWComplex
  rw [cellFrontier, image_map_discBundleAttachment h c (sphere 0 1) sphere_subset_closedBall,
    ← cellFrontier, cellFrontier_relCWComplexDiscBundleSphereBundle]
  congr 1
  ext v
  simp

/-- A disc-bundle attachment over a finite-dimensional CW complex is finite-dimensional relative to
the image of `Z`. -/
theorem finiteDimensional_discBundleAttachment [RelCWComplex.FiniteDimensional (univ : Set B)] :
    letI := relCWComplexDiscBundleSphereBundle F E
    letI := h.relCWComplex
    RelCWComplex.FiniteDimensional (univ : Set P) := by
  let := relCWComplexDiscBundleSphereBundle F E
  let := h.relCWComplex
  have hfd := finiteDimensional_relCWComplexDiscBundleSphereBundle F E
  refine ⟨?_⟩
  filter_upwards [hfd.eventually_isEmpty_cell] with k _
  exact (h.relCWComplexCellEquiv k).isEmpty_congr.2 inferInstance

/-- A disc-bundle attachment over a CW complex of finite type has finite type relative to the
image of `Z`. -/
theorem finiteType_discBundleAttachment [RelCWComplex.FiniteType (univ : Set B)] :
    letI := relCWComplexDiscBundleSphereBundle F E
    letI := h.relCWComplex
    RelCWComplex.FiniteType (univ : Set P) :=
  let := relCWComplexDiscBundleSphereBundle F E
  let := h.relCWComplex
  have hft := finiteType_relCWComplexDiscBundleSphereBundle F E
  ⟨fun k ↦
    have := hft.finite_cell k
    (h.relCWComplexCellEquiv k).finite_iff.2 inferInstance⟩

/-- A disc-bundle attachment over a finite CW complex is a finite relative CW complex relative to
the image of `Z`. -/
theorem finite_discBundleAttachment [RelCWComplex.Finite (univ : Set B)] :
    letI := relCWComplexDiscBundleSphereBundle F E
    letI := h.relCWComplex
    RelCWComplex.Finite (univ : Set P) :=
  let := relCWComplexDiscBundleSphereBundle F E
  let := h.relCWComplex
  have := finiteDimensional_discBundleAttachment h
  have := finiteType_discBundleAttachment h
  finite_of_finiteDimensional_finiteType _

end Attachment

section ThomSpace

/-- Collapsing the sphere bundle to a point is cellular: the part in `S(E)` of the boundary of an
`n`-cell of `D(E)` is mapped into the skeleton of dimension `n` of the point. -/
private theorem const_mem_skeletonLT_of_mem_cellFrontier (n : ℕ)
    (c : letI := relCWComplexDiscBundleSphereBundle F E; cell (discBundle F E) n)
    (x : sphereBundle F E)
    (hx : letI := relCWComplexDiscBundleSphereBundle F E;
      (x : TotalSpace F E) ∈ cellFrontier n c) :
    TopCat.ofHom (ContinuousMap.const (sphereBundle F E) PUnit.unit) x ∈
      (skeletonLT (univ : Set PUnit.{u + 1}) n : Set PUnit.{u + 1}) := by
  let := relCWComplexDiscBundleSphereBundle F E
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [cellFrontier_zero_eq_empty] at hx
    exact hx.elim
  · rw [skeletonLT_univ_eq_univ_of_ne_zero hn.ne']
    exact mem_univ _

/-- **The Thom space of a bundle over a CW complex is a CW complex.** If `B` is a CW complex, the
Thom space `Th(E) = D(E)/S(E)` is a CW complex with one `0`-cell, the basepoint, and one
`(m + r)`-cell for each `m`-cell of `B`, where `r` is the rank of the bundle
(`TauCeti.thomSpaceCWComplexCellEquiv`). -/
@[instance_reducible]
def thomSpaceCWComplex : CWComplex (univ : Set (thomSpace F E)) :=
  letI := relCWComplexDiscBundleSphereBundle F E
  (isPushout_thomSpace F E).cwComplexOfMapsToSkeletonLT
    (const_mem_skeletonLT_of_mem_cellFrontier F E)

/-- The `n`-cells of the Thom space are the `n`-cells of the point, a single `0`-cell for the
basepoint, together with the `m`-cells of `B` with `m + r = n`, where `r` is the rank of the
bundle. -/
def thomSpaceCWComplexCellEquiv (n : ℕ) :
    letI := thomSpaceCWComplex F E
    cell (univ : Set (thomSpace F E)) n ≃
      cell (univ : Set PUnit.{u + 1}) n ⊕
        Σ m : {m : ℕ // m + Module.finrank ℝ F = n}, cell (univ : Set B) m :=
  letI := relCWComplexDiscBundleSphereBundle F E
  ((isPushout_thomSpace F E).cwComplexOfMapsToSkeletonLTCellEquiv
    (const_mem_skeletonLT_of_mem_cellFrontier F E) n).trans
      (Equiv.sumCongr (.refl _) (relCWComplexDiscBundleSphereBundleCellEquiv F E n))

/-- The cell of the point in the Thom space is the basepoint. -/
@[simp]
theorem thomSpaceCWComplex_map_inl {n : ℕ} (c : cell (univ : Set PUnit.{u + 1}) n)
    (x : Fin n → ℝ) :
    letI := thomSpaceCWComplex F E
    map n ((thomSpaceCWComplexCellEquiv F E n).symm (.inl c)) x = thomSpaceBasepoint F E :=
  letI := relCWComplexDiscBundleSphereBundle F E
  (isPushout_thomSpace F E).cwComplexOfMapsToSkeletonLT_map_inl
    (const_mem_skeletonLT_of_mem_cellFrontier F E) n c x

/-- The characteristic map of the cell of the Thom space over an `m`-cell of `B` is the
characteristic map of the corresponding cell of the disc bundle, followed by the collapse map
`D(E) → Th(E)`. -/
@[simp]
theorem thomSpaceCWComplex_map_inr {n : ℕ}
    (c : Σ m : {m : ℕ // m + Module.finrank ℝ F = n}, cell (univ : Set B) m)
    (x : closedBall (0 : Fin n → ℝ) 1) :
    letI := thomSpaceCWComplex F E
    letI := relCWComplexDiscBundleSphereBundle F E
    map n ((thomSpaceCWComplexCellEquiv F E n).symm (.inr c)) x =
      thomSpaceπ F E ⟨map n ((relCWComplexDiscBundleSphereBundleCellEquiv F E n).symm c) x,
        closedCell_subset_complex n _ (mem_image_of_mem _ x.property)⟩ :=
  letI := relCWComplexDiscBundleSphereBundle F E
  (isPushout_thomSpace F E).cwComplexOfMapsToSkeletonLT_map_inr
    (const_mem_skeletonLT_of_mem_cellFrontier F E) n _ x

/-- The Thom space of a bundle over a finite CW complex is a finite CW complex. -/
theorem finite_thomSpaceCWComplex [RelCWComplex.Finite (univ : Set B)] :
    letI := thomSpaceCWComplex F E
    RelCWComplex.Finite (univ : Set (thomSpace F E)) :=
  letI := relCWComplexDiscBundleSphereBundle F E
  haveI := finite_relCWComplexDiscBundleSphereBundle F E
  (isPushout_thomSpace F E).finite_cwComplexOfMapsToSkeletonLT
    (const_mem_skeletonLT_of_mem_cellFrontier F E)

end ThomSpace

end TauCeti
