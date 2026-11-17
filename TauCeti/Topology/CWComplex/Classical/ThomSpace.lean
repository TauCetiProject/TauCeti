/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.CWComplex.Classical.AdjunctionModel
public import TauCeti.Topology.CWComplex.Classical.DiscBundle
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
  `m + r = n` (`TauCeti.discBundleAttachmentCellEquiv`). No CW structure on `Z` is needed. This is
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

section Sets

variable {B : Type u} (F : Type*) (E : B → Type u) [∀ b, NormedAddCommGroup (E b)]

/-- The part of the disc bundle over all of `B` is the disc bundle. -/
private theorem image_id_discBundle_inter_preimage_univ :
    id '' (discBundle F E ∩ TotalSpace.proj ⁻¹' (univ : Set B)) = discBundle F E := by
  simp

/-- The base of the relative CW structure of the disc bundle over all of `B` is the sphere
bundle. -/
private theorem image_id_sphereBundle_union :
    id '' (sphereBundle F E ∩ TotalSpace.proj ⁻¹' (univ : Set B) ∪
      discBundle F E ∩ TotalSpace.proj ⁻¹' (∅ : Set B)) = sphereBundle F E := by
  simp

end Sets

variable {B : Type u} [TopologicalSpace B] [T2Space B] (F : Type*) [NormedAddCommGroup F]
  [NormedSpace ℝ F] [FiniteDimensional ℝ F] (E : B → Type u) [∀ b, NormedAddCommGroup (E b)]
  [∀ b, InnerProductSpace ℝ (E b)] [TopologicalSpace (TotalSpace F E)] [FiberBundle F E]
  [VectorBundle ℝ F E] [ContinuousFiberNorm F E] [CWComplex (univ : Set B)]

section DiscBundle

/-- **The disc bundle over a CW complex, relative to the sphere bundle.** If `B` is a CW complex,
the unit disc bundle `D(E)` is a CW complex relative to the unit sphere bundle `S(E)`, with one
`(m + r)`-cell for each `m`-cell of `B`, `r` the rank
(`TauCeti.relCWComplexDiscBundleSphereBundleCellEquiv`). It is `TauCeti.relCWComplexDiscBundle`
for the whole of `B`. -/
@[instance_reducible]
def relCWComplexDiscBundleSphereBundle : RelCWComplex (discBundle F E) (sphereBundle F E) :=
  letI := relCWComplexDiscBundle F E (univ : Set B)
  IsClosedEmbedding.id.relCWComplex (image_id_discBundle_inter_preimage_univ F E)
    (image_id_sphereBundle_union F E)

/-- The `n`-cells of the disc bundle relative to the sphere bundle are the `m`-cells of `B` with
`m + r = n`, where `r` is the rank of the bundle. -/
def relCWComplexDiscBundleSphereBundleCellEquiv (n : ℕ) :
    letI := relCWComplexDiscBundleSphereBundle F E
    cell (discBundle F E) n ≃
      Σ m : {m : ℕ // m + Module.finrank ℝ F = n}, cell (univ : Set B) m :=
  letI := relCWComplexDiscBundle F E (univ : Set B)
  (IsClosedEmbedding.id.relCWComplexCellEquiv (image_id_discBundle_inter_preimage_univ F E)
    (image_id_sphereBundle_union F E) n).trans (cellDiscBundleEquiv F E univ n)

variable {F E} {n : ℕ} (c : Σ m : {m : ℕ // m + Module.finrank ℝ F = n}, cell (univ : Set B) m)

/-- The characteristic maps of `TauCeti.relCWComplexDiscBundleSphereBundle` are those of
`TauCeti.relCWComplexDiscBundle` for the whole of `B`. -/
private theorem map_relCWComplexDiscBundleSphereBundle :
    letI := relCWComplexDiscBundleSphereBundle F E
    letI := relCWComplexDiscBundle F E (univ : Set B)
    ⇑(map n ((relCWComplexDiscBundleSphereBundleCellEquiv F E n).symm c)) =
      ⇑(map n ((cellDiscBundleEquiv F E univ n).symm c)) := by
  let := relCWComplexDiscBundle F E (univ : Set B)
  rw [IsClosedEmbedding.coe_map_relCWComplex, relCWComplexDiscBundleSphereBundleCellEquiv,
    Equiv.symm_trans_apply, Equiv.apply_symm_apply, Function.id_comp]

/-- The characteristic map of the cell of the disc bundle over an `m`-cell of `B` lies over the
characteristic map of that cell, applied to the first `m` coordinates. -/
theorem proj_map_relCWComplexDiscBundleSphereBundle {x : Fin n → ℝ} (hx : x ∈ closedBall 0 1) :
    letI := relCWComplexDiscBundleSphereBundle F E
    (map n ((relCWComplexDiscBundleSphereBundleCellEquiv F E n).symm c) x).proj =
      map c.1.1 c.2 ((Fin.appendIsometryOfEq c.1.2).symm x).1 := by
  let := relCWComplexDiscBundle F E (univ : Set B)
  rw [map_relCWComplexDiscBundleSphereBundle]
  exact proj_map_relCWComplexDiscBundle c hx

/-- The closed cell of the disc bundle over an `m`-cell `j` of `B` is the part of the disc bundle
over the closed cell of `j`. -/
theorem closedCell_relCWComplexDiscBundleSphereBundle :
    letI := relCWComplexDiscBundleSphereBundle F E
    closedCell n ((relCWComplexDiscBundleSphereBundleCellEquiv F E n).symm c) =
      discBundle F E ∩ TotalSpace.proj ⁻¹' closedCell c.1.1 c.2 := by
  let := relCWComplexDiscBundle F E (univ : Set B)
  rw [IsClosedEmbedding.closedCell_relCWComplex, image_id,
    relCWComplexDiscBundleSphereBundleCellEquiv, Equiv.symm_trans_apply, Equiv.apply_symm_apply]
  exact closedCell_relCWComplexDiscBundle (E := E) c

/-- The open cell of the disc bundle over an `m`-cell `j` of `B` consists of the vectors of norm
less than one over the open cell of `j`. -/
theorem openCell_relCWComplexDiscBundleSphereBundle :
    letI := relCWComplexDiscBundleSphereBundle F E
    openCell n ((relCWComplexDiscBundleSphereBundleCellEquiv F E n).symm c) =
      {v : TotalSpace F E | ‖v.2‖ < 1} ∩ TotalSpace.proj ⁻¹' openCell c.1.1 c.2 := by
  let := relCWComplexDiscBundle F E (univ : Set B)
  rw [IsClosedEmbedding.openCell_relCWComplex, image_id,
    relCWComplexDiscBundleSphereBundleCellEquiv, Equiv.symm_trans_apply, Equiv.apply_symm_apply]
  exact openCell_relCWComplexDiscBundle (E := E) c

/-- The boundary of the cell of the disc bundle over an `m`-cell `j` of `B` is the part of the
sphere bundle over the closed cell of `j` together with the part of the disc bundle over the
boundary of `j`. -/
theorem cellFrontier_relCWComplexDiscBundleSphereBundle :
    letI := relCWComplexDiscBundleSphereBundle F E
    cellFrontier n ((relCWComplexDiscBundleSphereBundleCellEquiv F E n).symm c) =
      sphereBundle F E ∩ TotalSpace.proj ⁻¹' closedCell c.1.1 c.2 ∪
        discBundle F E ∩ TotalSpace.proj ⁻¹' cellFrontier c.1.1 c.2 := by
  let := relCWComplexDiscBundle F E (univ : Set B)
  rw [IsClosedEmbedding.cellFrontier_relCWComplex, image_id,
    relCWComplexDiscBundleSphereBundleCellEquiv, Equiv.symm_trans_apply, Equiv.apply_symm_apply]
  exact cellFrontier_relCWComplexDiscBundle (E := E) c

variable (F E) in
/-- The disc bundle over a finite CW complex is a finite CW complex relative to the sphere
bundle. -/
theorem finite_relCWComplexDiscBundleSphereBundle [RelCWComplex.Finite (univ : Set B)] :
    letI := relCWComplexDiscBundleSphereBundle F E
    RelCWComplex.Finite (discBundle F E) :=
  letI := relCWComplexDiscBundleSphereBundle F E
  letI := relCWComplexDiscBundle F E (univ : Set B)
  have := finite_relCWComplexDiscBundle (F := F) (E := E) (C := (univ : Set B))
  have := RelCWComplex.finite_cells_of_finite (C := discBundle F E ∩ TotalSpace.proj ⁻¹' univ)
  -- The cells are those of the disc bundle over the whole of `B`.
  RelCWComplex.finite_of_finite_cells (.of_equiv _
    (Equiv.sigmaCongrRight fun n ↦ (IsClosedEmbedding.id.relCWComplexCellEquiv
      (image_id_discBundle_inter_preimage_univ F E) (image_id_sphereBundle_union F E) n).symm))

end DiscBundle

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

end Attachment

section ThomSpace

/-- Every point of a one-point space lies in its skeleta of positive dimension, for the discrete
CW structure. -/
private theorem mem_skeletonLT_punit {n : ℕ} (hn : n ≠ 0) (x : PUnit.{u + 1}) :
    x ∈ (skeletonLT (univ : Set PUnit.{u + 1}) n : Set PUnit.{u + 1}) := by
  obtain ⟨m, k, hx⟩ : ∃ m, ∃ k : cell (univ : Set PUnit.{u + 1}) m, x ∈ openCell m k := by
    simpa using
      (CWComplex.iUnion_openCell_eq_complex (C := (univ : Set PUnit.{u + 1}))).symm.subset
        (mem_univ x)
  cases m with
  | zero =>
    exact RelCWComplex.mem_skeletonLT_iff.2
      (.inr ⟨0, by exact_mod_cast Nat.pos_of_ne_zero hn, k, hx⟩)
  | succ m => exact isEmptyElim k

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
  · exact mem_skeletonLT_punit hn.ne' _

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
theorem thomSpaceCWComplex_map_inr {n : ℕ}
    (c : Σ m : {m : ℕ // m + Module.finrank ℝ F = n}, cell (univ : Set B) m)
    (x : closedBall (0 : Fin n → ℝ) 1) :
    letI := thomSpaceCWComplex F E
    letI := relCWComplexDiscBundleSphereBundle F E
    map n ((thomSpaceCWComplexCellEquiv F E n).symm (.inr c)) x =
      thomSpaceπ F E ⟨map n ((relCWComplexDiscBundleSphereBundleCellEquiv F E n).symm c) x,
        closedCell_subset_complex n _ (mem_image_of_mem _ x.2)⟩ :=
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
