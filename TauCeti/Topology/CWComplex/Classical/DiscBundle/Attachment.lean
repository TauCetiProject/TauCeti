/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.CWComplex.Classical.DiscBundle.Subtype
public import TauCeti.Topology.CWComplex.Classical.Pushout
public import TauCeti.Topology.FiberBundle.Separation

/-!
# Cell structures of disc-bundle attachments

Let `E → B` be a real vector bundle of rank `r` over a Hausdorff space `B : Type u`, with
finite-dimensional model fibre `F` and fibre inner products whose norm is continuous on the total
space (`TauCeti.ContinuousFiberNorm`). Given a topological space `Z`, attaching the unit disc
bundle `D(E)` along `S(E)` (or more generally along `S(E) ∪ D(E)|_A` over a classical relative CW
pair `(B, A)`) yields the adjunction space `Z ∪_g D(E)`, equipped with its classical relative CW
structure over the image of `Z`:

* **Same-universe pushouts.** For any continuous map `g : S(E) → Z` in `Type u` and any pushout `P`
  of `S(E) → D(E)` along `g`, `P` is a CW complex relative to the image of `Z`
  (`CategoryTheory.IsPushout.relCWComplex`), whose `n`-cells are the `m`-cells of `B` with
  `m + r = n` (`TauCeti.discBundleAttachmentCellEquiv`). The characteristic map of each is that of
  the corresponding cell of `D(E)`, followed by `D(E) → P`
  (`TauCeti.map_discBundleAttachmentCellEquiv_symm`). No CW structure on `Z` is needed.
* **Universe-polymorphic relative attachments.** For `Z : Type v` in an independent universe `v`,
  `TauCeti.relCWComplexDiscBundleSubtypeRel` and `TauCeti.uliftAdjunctionSpace` construct
  `TauCeti.discBundleRelAttachmentSpace` for any continuous attaching map
  `g : S(E) ∪ D(E)|_A → Z` over a relative CW pair `(B, A)`, together with its pushout universal
  property (`TauCeti.discBundleRelAttachmentDesc`), closed base embedding
  (`TauCeti.isClosedEmbedding_discBundleRelAttachmentInr`), Hausdorffness, relative CW model
  (`TauCeti.discBundleRelAttachmentCWModel`), characteristic-map and cell-set formulas, finiteness
  preservation, and universe-polymorphic homotopy invariance in `Z`
  (`TauCeti.exists_homotopyEquiv_discBundleRelAttachmentSpace`).
* **Universe-polymorphic sphere-bundle attachments.** Specializing via
  `TauCeti.relCWComplexDiscBundleSubtypeSphereBundle` to a Hausdorff CW complex `B` and
  `g : S(E) → Z` gives `TauCeti.discBundleAttachmentSpace`, its universal property
  (`TauCeti.discBundleAttachmentDesc`), relative CW model (`TauCeti.discBundleAttachmentCWModel`),
  cell formulas, finiteness preservation, and homotopy invariance in `Z`
  (`TauCeti.exists_homotopyEquiv_discBundleAttachmentSpace`).

No orientation of `E` is used.

## References

* J. W. Milnor and J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press, 1974, §18 (the cell structure of the Thom space of a bundle over a
  CW complex).
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), Chapter 0 and
  §4.D (disc bundles, cell attachments, and Thom spaces).
* R. Brown, *Topology and Groupoids*, 2006, Section 7.5 (gluing theorem for homotopy equivalences).
-/

public section

noncomputable section

open Bundle CategoryTheory ContinuousMap Limits Metric Set Topology Topology.RelCWComplex

universe u v w

namespace TauCeti

section Attachment

variable {B : Type u} [TopologicalSpace B] [T2Space B] (F : Type*) [NormedAddCommGroup F]
  [NormedSpace ℝ F] [FiniteDimensional ℝ F] (E : B → Type u) [∀ b, NormedAddCommGroup (E b)]
  [∀ b, InnerProductSpace ℝ (E b)] [TopologicalSpace (TotalSpace F E)] [FiberBundle F E]
  [VectorBundle ℝ F E] [ContinuousFiberNorm F E] [CWComplex (univ : Set B)]
  {Z P : TopCat.{u}} {g : TopCat.of (sphereBundle F E) ⟶ Z}
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
    RelCWComplex.FiniteDimensional (univ : Set P) :=
  letI := relCWComplexDiscBundleSphereBundle F E
  haveI := finiteDimensional_relCWComplexDiscBundleSphereBundle F E
  RelCWComplex.finiteDimensional_of_cellEquiv (relCWComplexDiscBundleSphereBundle F E)
    h.relCWComplex h.relCWComplexCellEquiv

/-- A disc-bundle attachment over a CW complex of finite type has finite type relative to the
image of `Z`. -/
theorem finiteType_discBundleAttachment [RelCWComplex.FiniteType (univ : Set B)] :
    letI := relCWComplexDiscBundleSphereBundle F E
    letI := h.relCWComplex
    RelCWComplex.FiniteType (univ : Set P) :=
  letI := relCWComplexDiscBundleSphereBundle F E
  haveI := finiteType_relCWComplexDiscBundleSphereBundle F E
  RelCWComplex.finiteType_of_cellEquiv (relCWComplexDiscBundleSphereBundle F E)
    h.relCWComplex h.relCWComplexCellEquiv

/-- A disc-bundle attachment over a finite CW complex is a finite relative CW complex relative to
the image of `Z`. -/
theorem finite_discBundleAttachment [RelCWComplex.Finite (univ : Set B)] :
    letI := relCWComplexDiscBundleSphereBundle F E
    letI := h.relCWComplex
    RelCWComplex.Finite (univ : Set P) :=
  letI := relCWComplexDiscBundleSphereBundle F E
  haveI := finite_relCWComplexDiscBundleSphereBundle F E
  RelCWComplex.finite_of_cellEquiv (relCWComplexDiscBundleSphereBundle F E)
    h.relCWComplex h.relCWComplexCellEquiv

end Attachment

/-! ### Relative disc-bundle attachment along `S(E) ∪ D(E)|_A` -/

section RelAttachment

section Helpers

variable {B : Type u} [TopologicalSpace B] (F : Type*) [NormedAddCommGroup F]
  (E : B → Type u) [∀ b, NormedAddCommGroup (E b)] [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E]

/-- Canonical homeomorphism between the relative base inside `discBundle F E` and
`S(E) ∪ D(E)|_A` in `TotalSpace F E`. -/
private def discRelBaseHomeo (A : Set B) :
    ↥(Subtype.val ⁻¹' sphereBundle F E ∪ discBundleProj F E ⁻¹' A : Set (discBundle F E)) ≃ₜ
      ↥(sphereBundle F E ∪ discBundle F E ∩ TotalSpace.proj ⁻¹' A) where
  toFun v := ⟨v.val.val,
    v.property.elim Or.inl fun hv ↦
      Or.inr ⟨v.val.property, Eq.mp (congrArg (· ∈ A) (discBundleProj_apply F E v.val)) hv⟩⟩
  invFun v := ⟨⟨v.val, v.property.elim (fun h ↦ mem_discBundle.2 (mem_sphereBundle.1 h).le)
    And.left⟩,
    v.property.elim Or.inl fun hv ↦
      Or.inr (Eq.mpr (congrArg (· ∈ A) (discBundleProj_apply F E _)) hv.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtypeVal.comp continuous_subtypeVal).subtype_mk _
  continuous_invFun := (continuous_subtypeVal.subtype_mk _).subtype_mk _

private def discRelBaseMap (A : Set B) {Z : Type v} [TopologicalSpace Z]
    (g : C(↥(sphereBundle F E ∪ discBundle F E ∩ TotalSpace.proj ⁻¹' A), Z)) :
    C(↥(Subtype.val ⁻¹' sphereBundle F E ∪ discBundleProj F E ⁻¹' A : Set (discBundle F E)),
      Z) :=
  g.comp ⟨discRelBaseHomeo F E A, (discRelBaseHomeo F E A).continuous⟩

end Helpers

variable {B : Type u} [TopologicalSpace B] [T2Space B] (F : Type*) [NormedAddCommGroup F]
  [NormedSpace ℝ F] [FiniteDimensional ℝ F] (E : B → Type u) [∀ b, NormedAddCommGroup (E b)]
  [∀ b, InnerProductSpace ℝ (E b)] [TopologicalSpace (TotalSpace F E)] [FiberBundle F E]
  [VectorBundle ℝ F E] [ContinuousFiberNorm F E] (A : Set B) [RelCWComplex (univ : Set B) A]
  {Z : Type v} [TopologicalSpace Z]
  (g : C(↥(sphereBundle F E ∪ discBundle F E ∩ TotalSpace.proj ⁻¹' A), Z))

/-- **Relative disc-bundle attachment space `Z ∪_g D(E)`.** The adjunction space obtained by
attaching the unit disc bundle `D(E)` to `Z` along a continuous map `g : S(E) ∪ D(E)|_A → Z`
over a relative CW pair `(B, A)`, constructed in the common universe `max u v`. -/
def discBundleRelAttachmentSpace : TopCat.{max u v} :=
  letI := relCWComplexDiscBundleSubtypeRel F E A
  uliftAdjunctionSpace (univ : Set (discBundle F E)) (discRelBaseMap F E A g)

/-- The canonical inclusion `Z → Z ∪_g D(E)` into the relative disc-bundle attachment. -/
def discBundleRelAttachmentInr : C(Z, discBundleRelAttachmentSpace F E A g) :=
  letI := relCWComplexDiscBundleSubtypeRel F E A
  uliftAdjunctionInr (univ : Set (discBundle F E)) (discRelBaseMap F E A g)

/-- The canonical characteristic-side map `D(E) → Z ∪_g D(E)` into the relative disc-bundle
attachment. -/
def discBundleRelAttachmentInl : C(discBundle F E, discBundleRelAttachmentSpace F E A g) :=
  letI := relCWComplexDiscBundleSubtypeRel F E A
  (uliftAdjunctionInl (univ : Set (discBundle F E)) (discRelBaseMap F E A g)).comp
    ⟨(Homeomorph.Set.univ (discBundle F E)).symm,
      (Homeomorph.Set.univ (discBundle F E)).symm.continuous⟩

/-- On the relative base `S(E) ∪ D(E)|_A`, `discBundleRelAttachmentInl` agrees with
`discBundleRelAttachmentInr ∘ g`. -/
theorem discBundleRelAttachmentInl_eq_inr
    (b : ↥(sphereBundle F E ∪ discBundle F E ∩ TotalSpace.proj ⁻¹' A)) :
    discBundleRelAttachmentInl F E A g
        ⟨b.val, b.property.elim (fun h ↦ mem_discBundle.2 (mem_sphereBundle.1 h).le) And.left⟩ =
      discBundleRelAttachmentInr F E A g (g b) :=
  letI := relCWComplexDiscBundleSubtypeRel F E A
  uliftAdjunctionInl_eq_inr (univ : Set (discBundle F E)) (discRelBaseMap F E A g)
    ((discRelBaseHomeo F E A).symm b)

/-- **Pushout eliminator for `discBundleRelAttachmentSpace`.** Compatible continuous maps out of
`D(E)` and `Z` into a space `W` in an arbitrary universe descend uniquely to a continuous map
`Z ∪_g D(E) → W`. -/
def discBundleRelAttachmentDesc {W : Type w} [TopologicalSpace W]
    (f : C(discBundle F E, W)) (h : C(Z, W))
    (hfg : ∀ b : ↥(sphereBundle F E ∪ discBundle F E ∩ TotalSpace.proj ⁻¹' A),
      f ⟨b.val, b.property.elim (fun h ↦ mem_discBundle.2 (mem_sphereBundle.1 h).le) And.left⟩ =
        h (g b)) :
    C(discBundleRelAttachmentSpace F E A g, W) :=
  letI := relCWComplexDiscBundleSubtypeRel F E A
  uliftAdjunctionDesc (univ : Set (discBundle F E)) (discRelBaseMap F E A g)
    (f.comp ⟨Homeomorph.Set.univ (discBundle F E),
      (Homeomorph.Set.univ (discBundle F E)).continuous⟩)
    h fun d ↦ hfg (discRelBaseHomeo F E A d)

@[simp]
theorem discBundleRelAttachmentDesc_inl {W : Type w} [TopologicalSpace W]
    (f : C(discBundle F E, W)) (h : C(Z, W))
    (hfg : ∀ b : ↥(sphereBundle F E ∪ discBundle F E ∩ TotalSpace.proj ⁻¹' A),
      f ⟨b.val, b.property.elim (fun h ↦ mem_discBundle.2 (mem_sphereBundle.1 h).le) And.left⟩ =
        h (g b))
    (v : discBundle F E) :
    discBundleRelAttachmentDesc F E A g f h hfg (discBundleRelAttachmentInl F E A g v) = f v :=
  letI := relCWComplexDiscBundleSubtypeRel F E A
  uliftAdjunctionDesc_inl (univ : Set (discBundle F E)) (discRelBaseMap F E A g)
    (f.comp ⟨Homeomorph.Set.univ (discBundle F E),
      (Homeomorph.Set.univ (discBundle F E)).continuous⟩)
    h (fun d ↦ hfg (discRelBaseHomeo F E A d)) ⟨v, mem_univ v⟩

@[simp]
theorem discBundleRelAttachmentDesc_inr {W : Type w} [TopologicalSpace W]
    (f : C(discBundle F E, W)) (h : C(Z, W))
    (hfg : ∀ b : ↥(sphereBundle F E ∪ discBundle F E ∩ TotalSpace.proj ⁻¹' A),
      f ⟨b.val, b.property.elim (fun h ↦ mem_discBundle.2 (mem_sphereBundle.1 h).le) And.left⟩ =
        h (g b))
    (z : Z) :
    discBundleRelAttachmentDesc F E A g f h hfg (discBundleRelAttachmentInr F E A g z) = h z :=
  letI := relCWComplexDiscBundleSubtypeRel F E A
  uliftAdjunctionDesc_inr (univ : Set (discBundle F E)) (discRelBaseMap F E A g)
    (f.comp ⟨Homeomorph.Set.univ (discBundle F E),
      (Homeomorph.Set.univ (discBundle F E)).continuous⟩)
    h (fun d ↦ hfg (discRelBaseHomeo F E A d)) z

@[simp]
theorem discBundleRelAttachmentDesc_comp_inl {W : Type w} [TopologicalSpace W]
    (f : C(discBundle F E, W)) (h : C(Z, W))
    (hfg : ∀ b : ↥(sphereBundle F E ∪ discBundle F E ∩ TotalSpace.proj ⁻¹' A),
      f ⟨b.val, b.property.elim (fun h ↦ mem_discBundle.2 (mem_sphereBundle.1 h).le) And.left⟩ =
        h (g b)) :
    (discBundleRelAttachmentDesc F E A g f h hfg).comp (discBundleRelAttachmentInl F E A g) = f :=
  ContinuousMap.ext (discBundleRelAttachmentDesc_inl F E A g f h hfg)

@[simp]
theorem discBundleRelAttachmentDesc_comp_inr {W : Type w} [TopologicalSpace W]
    (f : C(discBundle F E, W)) (h : C(Z, W))
    (hfg : ∀ b : ↥(sphereBundle F E ∪ discBundle F E ∩ TotalSpace.proj ⁻¹' A),
      f ⟨b.val, b.property.elim (fun h ↦ mem_discBundle.2 (mem_sphereBundle.1 h).le) And.left⟩ =
        h (g b)) :
    (discBundleRelAttachmentDesc F E A g f h hfg).comp (discBundleRelAttachmentInr F E A g) = h :=
  ContinuousMap.ext (discBundleRelAttachmentDesc_inr F E A g f h hfg)

/-- Every point of `Z ∪_g D(E)` lies in the image of `D(E)` or in the image of `Z`. -/
theorem exists_discBundleRelAttachmentInl_or_inr (p : discBundleRelAttachmentSpace F E A g) :
    (∃ v : discBundle F E, discBundleRelAttachmentInl F E A g v = p) ∨
      ∃ z : Z, discBundleRelAttachmentInr F E A g z = p := by
  let _ := relCWComplexDiscBundleSubtypeRel F E A
  rcases exists_uliftAdjunctionInl_or_inr (univ : Set (discBundle F E))
      (discRelBaseMap F E A g) p with ⟨v, hv⟩ | ⟨z, hz⟩
  · exact Or.inl ⟨v.val, hv⟩
  · exact Or.inr ⟨z, hz⟩

/-- Induction principle on points of `Z ∪_g D(E)` by splitting into the images of `D(E)` and
`Z`. -/
@[elab_as_elim]
theorem discBundleRelAttachmentSpace_induction_on
    {P : discBundleRelAttachmentSpace F E A g → Prop}
    (p : discBundleRelAttachmentSpace F E A g)
    (hl : ∀ v, P (discBundleRelAttachmentInl F E A g v))
    (hr : ∀ z, P (discBundleRelAttachmentInr F E A g z)) : P p := by
  rcases exists_discBundleRelAttachmentInl_or_inr F E A g p with ⟨v, rfl⟩ | ⟨z, rfl⟩
  · exact hl v
  · exact hr z

/-- The ranges of `discBundleRelAttachmentInl` and `discBundleRelAttachmentInr` cover
`Z ∪_g D(E)`. -/
theorem range_discBundleRelAttachmentInl_union_range_inr :
    range (discBundleRelAttachmentInl F E A g) ∪ range (discBundleRelAttachmentInr F E A g) =
      univ :=
  eq_univ_of_forall fun p ↦ exists_discBundleRelAttachmentInl_or_inr F E A g p

/-- Two continuous maps out of `Z ∪_g D(E)` agree as soon as they agree on the images of `D(E)`
and `Z`. -/
theorem discBundleRelAttachmentSpace_continuousMap_ext {W : Type w} [TopologicalSpace W]
    {f₁ f₂ : C(discBundleRelAttachmentSpace F E A g, W)}
    (hl : ∀ v, f₁ (discBundleRelAttachmentInl F E A g v) =
      f₂ (discBundleRelAttachmentInl F E A g v))
    (hr : ∀ z, f₁ (discBundleRelAttachmentInr F E A g z) =
      f₂ (discBundleRelAttachmentInr F E A g z)) : f₁ = f₂ :=
  ContinuousMap.ext fun p ↦ discBundleRelAttachmentSpace_induction_on F E A g p hl hr

/-- A subset of `Z ∪_g D(E)` is closed if and only if its preimages in `D(E)` and in `Z` are both
closed. -/
theorem isClosed_iff_discBundleRelAttachmentSpace
    (s : Set (discBundleRelAttachmentSpace F E A g)) :
    IsClosed s ↔
      IsClosed (discBundleRelAttachmentInl F E A g ⁻¹' s) ∧
        IsClosed (discBundleRelAttachmentInr F E A g ⁻¹' s) := by
  let _ := relCWComplexDiscBundleSubtypeRel F E A
  refine (isClosed_iff_uliftAdjunctionSpace (univ : Set (discBundle F E))
    (discRelBaseMap F E A g) s).trans ?_
  rw [← (Homeomorph.Set.univ (discBundle F E)).symm.isClosed_preimage]
  rfl

/-- The canonical map `Z → Z ∪_g D(E)` is a closed embedding. -/
theorem isClosedEmbedding_discBundleRelAttachmentInr :
    IsClosedEmbedding (discBundleRelAttachmentInr F E A g) :=
  let _ := relCWComplexDiscBundleSubtypeRel F E A
  isClosedEmbedding_uliftAdjunctionInr (univ : Set (discBundle F E)) (discRelBaseMap F E A g)

/-- When `Z` is Hausdorff, the relative disc-bundle attachment `Z ∪_g D(E)` is Hausdorff. -/
instance t2Space_discBundleRelAttachmentSpace [T2Space Z] :
    T2Space (discBundleRelAttachmentSpace F E A g) :=
  letI := relCWComplexDiscBundleSubtypeRel F E A
  t2Space_uliftAdjunctionSpace (univ : Set (discBundle F E)) (discRelBaseMap F E A g)

/-- **Classical relative CW model of a relative disc-bundle attachment.** Attaching `D(E)` to `Z`
along `g : S(E) ∪ D(E)|_A → Z` equips `Z ∪_g D(E)` with a classical relative CW structure relative
to the image of `Z`, with one `(m + r)`-cell for each relative `m`-cell of `(B, A)`. -/
@[instance_reducible]
def discBundleRelAttachmentCWModel :
    RelCWComplex (univ : Set (discBundleRelAttachmentSpace F E A g))
      (range (discBundleRelAttachmentInr F E A g)) :=
  letI := relCWComplexDiscBundleSubtypeRel F E A
  uliftAdjunctionCWModel (univ : Set (discBundle F E)) (discRelBaseMap F E A g)

/-- The `n`-cells of `Z ∪_g D(E)` correspond bijectively to the relative `m`-cells of `(B, A)`
with `m + r = n`, where `r` is the rank of the bundle. -/
def discBundleRelAttachmentCWModelCellEquiv (n : ℕ) :
    letI := discBundleRelAttachmentCWModel F E A g
    cell (univ : Set (discBundleRelAttachmentSpace F E A g)) n ≃
      Σ m : {m : ℕ // m + Module.finrank ℝ F = n}, cell (univ : Set B) m :=
  letI := relCWComplexDiscBundleSubtypeRel F E A
  (uliftAdjunctionCellEquiv (univ : Set (discBundle F E)) (discRelBaseMap F E A g) n).trans
    (relCWComplexDiscBundleSubtypeRelCellEquiv F E A n)

/-- Below the fibre rank `r`, `discBundleRelAttachmentCWModel` has no `n`-cells. -/
theorem isEmpty_cell_discBundleRelAttachmentCWModel_of_lt {n : ℕ} (hn : n < Module.finrank ℝ F) :
    letI := discBundleRelAttachmentCWModel F E A g
    IsEmpty (cell (univ : Set (discBundleRelAttachmentSpace F E A g)) n) :=
  let := discBundleRelAttachmentCWModel F E A g
  letI := relCWComplexDiscBundleSubtypeRel F E A
  have := isEmpty_cell_relCWComplexDiscBundleSubtypeRel_of_lt (F := F) (E := E) (A := A) hn
  (uliftAdjunctionCellEquiv (univ : Set (discBundle F E))
    (discRelBaseMap F E A g) n).isEmpty_congr.2 inferInstance

private lemma uliftAdjunctionCellEquiv_discBundleRelAttachmentCWModel_symm {n : ℕ}
    (c : Σ m : {m : ℕ // m + Module.finrank ℝ F = n}, cell (univ : Set B) m) :
    letI := discBundleRelAttachmentCWModel F E A g
    letI := relCWComplexDiscBundleSubtypeRel F E A
    uliftAdjunctionCellEquiv (univ : Set (discBundle F E)) (discRelBaseMap F E A g) n
      ((discBundleRelAttachmentCWModelCellEquiv F E A g n).symm c) =
      (relCWComplexDiscBundleSubtypeRelCellEquiv F E A n).symm c := by
  let _ := relCWComplexDiscBundleSubtypeRel F E A
  exact (uliftAdjunctionCellEquiv (univ : Set (discBundle F E))
    (discRelBaseMap F E A g) n).apply_symm_apply _

/-- Each characteristic map of `discBundleRelAttachmentCWModel` is the corresponding characteristic
map of `TauCeti.relCWComplexDiscBundleSubtypeRel` in `D(E)` followed by
`discBundleRelAttachmentInl`. -/
theorem discBundleRelAttachmentCWModel_map_apply {n : ℕ}
    (c : Σ m : {m : ℕ // m + Module.finrank ℝ F = n}, cell (univ : Set B) m)
    {x : Fin n → ℝ} (hx : x ∈ closedBall 0 1) :
    letI := discBundleRelAttachmentCWModel F E A g
    letI := relCWComplexDiscBundleSubtypeRel F E A
    map n ((discBundleRelAttachmentCWModelCellEquiv F E A g n).symm c) x =
      discBundleRelAttachmentInl F E A g
        (map n ((relCWComplexDiscBundleSubtypeRelCellEquiv F E A n).symm c) x) := by
  let _ := relCWComplexDiscBundleSubtypeRel F E A
  refine (uliftAdjunctionCWModel_map_apply (univ : Set (discBundle F E)) (discRelBaseMap F E A g)
    n _ hx).trans ?_
  rw [uliftAdjunctionCellEquiv_discBundleRelAttachmentCWModel_symm]
  rfl

private theorem image_map_discBundleRelAttachmentCWModel {n : ℕ}
    (c : Σ m : {m : ℕ // m + Module.finrank ℝ F = n}, cell (univ : Set B) m)
    (S : Set (Fin n → ℝ)) (hS : S ⊆ closedBall 0 1) :
    letI := discBundleRelAttachmentCWModel F E A g
    letI := relCWComplexDiscBundleSubtypeRel F E A
    map n ((discBundleRelAttachmentCWModelCellEquiv F E A g n).symm c) '' S =
      discBundleRelAttachmentInl F E A g ''
        (map n ((relCWComplexDiscBundleSubtypeRelCellEquiv F E A n).symm c) '' S) := by
  let _ := relCWComplexDiscBundleSubtypeRel F E A
  refine (image_map_uliftAdjunctionCWModel (univ : Set (discBundle F E)) (discRelBaseMap F E A g)
    n _ S hS).trans ?_
  rw [uliftAdjunctionCellEquiv_discBundleRelAttachmentCWModel_symm]
  ext p
  simp only [mem_image, mem_preimage]
  exact ⟨fun ⟨v, hvS, hvp⟩ ↦ ⟨v.val, hvS, hvp⟩, fun ⟨v, hvS, hvp⟩ ↦ ⟨⟨v, mem_univ v⟩, hvS, hvp⟩⟩

/-- The open cell of `discBundleRelAttachmentCWModel` over a relative `m`-cell `j` of `(B, A)` is
the image under `discBundleRelAttachmentInl` of the vectors of norm less than one in `D(E)` over
`openCell m j`. -/
@[simp]
theorem openCell_discBundleRelAttachmentCWModel {n : ℕ}
    (c : Σ m : {m : ℕ // m + Module.finrank ℝ F = n}, cell (univ : Set B) m) :
    letI := discBundleRelAttachmentCWModel F E A g
    openCell n ((discBundleRelAttachmentCWModelCellEquiv F E A g n).symm c) =
      discBundleRelAttachmentInl F E A g '' {v : discBundle F E |
        (v : TotalSpace F E).proj ∈ openCell c.1.val c.2 ∧ ‖(v : TotalSpace F E).snd‖ < 1} := by
  let _ := discBundleRelAttachmentCWModel F E A g
  let _ := relCWComplexDiscBundleSubtypeRel F E A
  rw [openCell,
    image_map_discBundleRelAttachmentCWModel F E A g c (ball 0 1) ball_subset_closedBall,
    ← openCell, openCell_relCWComplexDiscBundleSubtypeRel]
  congr 1; ext v; simp [discBundleProj_apply, and_comm]

/-- The closed cell of `discBundleRelAttachmentCWModel` over a relative `m`-cell `j` of `(B, A)`
is the image under `discBundleRelAttachmentInl` of `D(E)` over `closedCell m j`. -/
@[simp]
theorem closedCell_discBundleRelAttachmentCWModel {n : ℕ}
    (c : Σ m : {m : ℕ // m + Module.finrank ℝ F = n}, cell (univ : Set B) m) :
    letI := discBundleRelAttachmentCWModel F E A g
    closedCell n ((discBundleRelAttachmentCWModelCellEquiv F E A g n).symm c) =
      discBundleRelAttachmentInl F E A g '' (discBundleProj F E ⁻¹' closedCell c.1.val c.2) := by
  let _ := discBundleRelAttachmentCWModel F E A g
  let _ := relCWComplexDiscBundleSubtypeRel F E A
  rw [closedCell,
    image_map_discBundleRelAttachmentCWModel F E A g c (closedBall 0 1) Subset.rfl,
    ← closedCell, closedCell_relCWComplexDiscBundleSubtypeRel]

/-- The boundary of the cell of `discBundleRelAttachmentCWModel` over a relative `m`-cell `j` of
`(B, A)` is the image under `discBundleRelAttachmentInl` of `S(E)` over `closedCell m j` together
with `D(E)` over `cellFrontier m j`. -/
@[simp]
theorem cellFrontier_discBundleRelAttachmentCWModel {n : ℕ}
    (c : Σ m : {m : ℕ // m + Module.finrank ℝ F = n}, cell (univ : Set B) m) :
    letI := discBundleRelAttachmentCWModel F E A g
    cellFrontier n ((discBundleRelAttachmentCWModelCellEquiv F E A g n).symm c) =
      discBundleRelAttachmentInl F E A g ''
        (Subtype.val ⁻¹' sphereBundle F E ∩ discBundleProj F E ⁻¹' closedCell c.1.val c.2 ∪
          discBundleProj F E ⁻¹' cellFrontier c.1.val c.2) := by
  let _ := discBundleRelAttachmentCWModel F E A g
  let _ := relCWComplexDiscBundleSubtypeRel F E A
  rw [cellFrontier,
    image_map_discBundleRelAttachmentCWModel F E A g c (sphere 0 1) sphere_subset_closedBall,
    ← cellFrontier, cellFrontier_relCWComplexDiscBundleSubtypeRel]

/-- `discBundleRelAttachmentCWModel` is finite-dimensional when `(B, A)` is finite-dimensional. -/
theorem finiteDimensional_discBundleRelAttachmentCWModel
    [RelCWComplex.FiniteDimensional (univ : Set B)] :
    letI := discBundleRelAttachmentCWModel F E A g
    RelCWComplex.FiniteDimensional (univ : Set (discBundleRelAttachmentSpace F E A g)) :=
  let _ := discBundleRelAttachmentCWModel F E A g
  let _ := relCWComplexDiscBundleSubtypeRel F E A
  have := finiteDimensional_relCWComplexDiscBundleSubtypeRel F E A
  finiteDimensional_uliftAdjunctionCWModel (univ : Set (discBundle F E)) (discRelBaseMap F E A g)

/-- `discBundleRelAttachmentCWModel` has finite type when `(B, A)` has finite type. -/
theorem finiteType_discBundleRelAttachmentCWModel [RelCWComplex.FiniteType (univ : Set B)] :
    letI := discBundleRelAttachmentCWModel F E A g
    RelCWComplex.FiniteType (univ : Set (discBundleRelAttachmentSpace F E A g)) :=
  let _ := discBundleRelAttachmentCWModel F E A g
  let _ := relCWComplexDiscBundleSubtypeRel F E A
  have := finiteType_relCWComplexDiscBundleSubtypeRel F E A
  finiteType_uliftAdjunctionCWModel (univ : Set (discBundle F E)) (discRelBaseMap F E A g)

/-- `discBundleRelAttachmentCWModel` is finite when `(B, A)` is finite. -/
theorem finite_discBundleRelAttachmentCWModel [RelCWComplex.Finite (univ : Set B)] :
    letI := discBundleRelAttachmentCWModel F E A g
    RelCWComplex.Finite (univ : Set (discBundleRelAttachmentSpace F E A g)) :=
  let _ := discBundleRelAttachmentCWModel F E A g
  let _ := relCWComplexDiscBundleSubtypeRel F E A
  have := finite_relCWComplexDiscBundleSubtypeRel F E A
  finite_uliftAdjunctionCWModel (univ : Set (discBundle F E)) (discRelBaseMap F E A g)

/-- **Base homotopy invariance of relative disc-bundle attachments.** A homotopy equivalence
`e : Z ≃ₕ Z'` (with `Z` and `Z'` in independent universes) induces a homotopy equivalence
`Z ∪_g D(E) ≃ₕ Z' ∪_{e ∘ g} D(E)` compatible with the inclusions of `Z` and `Z'`. -/
theorem exists_homotopyEquiv_discBundleRelAttachmentSpace {Z' : Type w} [TopologicalSpace Z']
    (e : Z ≃ₕ Z') :
    ∃ H : discBundleRelAttachmentSpace.{u, v} F E A g ≃ₕ
        discBundleRelAttachmentSpace.{u, w} F E A (e.toFun.comp g),
      (∀ z, H (discBundleRelAttachmentInr F E A g z) =
        discBundleRelAttachmentInr F E A (e.toFun.comp g) (e z)) ∧
      ∀ z', H.symm (discBundleRelAttachmentInr F E A (e.toFun.comp g) z') =
        discBundleRelAttachmentInr F E A g (e.symm z') :=
  let _ := relCWComplexDiscBundleSubtypeRel F E A
  exists_homotopyEquiv_uliftAdjunctionSpace (univ : Set (discBundle F E))
    (discRelBaseMap F E A g) e

end RelAttachment

/-! ### Disc-bundle attachment `Z ∪_g D(E)` along `g : S(E) → Z` -/

section SphereAttachment

section Helpers

variable {B : Type u} [TopologicalSpace B] (F : Type*) [NormedAddCommGroup F]
  (E : B → Type u) [∀ b, NormedAddCommGroup (E b)] [TopologicalSpace (TotalSpace F E)]

/-- Canonical homeomorphism between `Subtype.val ⁻¹' sphereBundle F E` in `discBundle F E` and
`sphereBundle F E`. -/
private def discSphereBaseHomeo :
    ↥(Subtype.val ⁻¹' sphereBundle F E : Set (discBundle F E)) ≃ₜ sphereBundle F E where
  toFun s := ⟨s.val.val, s.property⟩
  invFun s := ⟨⟨s.val, mem_discBundle.2 (mem_sphereBundle.1 s.property).le⟩, s.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtypeVal.comp continuous_subtypeVal).subtype_mk _
  continuous_invFun := (continuous_subtypeVal.subtype_mk _).subtype_mk _

private def discSphereBaseMap {Z : Type v} [TopologicalSpace Z] (g : C(sphereBundle F E, Z)) :
    C(↥(Subtype.val ⁻¹' sphereBundle F E : Set (discBundle F E)), Z) :=
  g.comp ⟨discSphereBaseHomeo F E, (discSphereBaseHomeo F E).continuous⟩

end Helpers

variable {B : Type u} [TopologicalSpace B] [T2Space B] [Topology.CWComplex (univ : Set B)]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (E : B → Type u) [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace ℝ (E b)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]
  [ContinuousFiberNorm F E] {Z : Type v} [TopologicalSpace Z] (g : C(sphereBundle F E, Z))

/-- **Disc-bundle attachment space `Z ∪_g D(E)`.** The adjunction space obtained by attaching the
unit disc bundle `D(E)` to `Z` along `g : S(E) → Z`, constructed in `TopCat.{max u v}` for `B`
and `Z` in independent universes. -/
def discBundleAttachmentSpace : TopCat.{max u v} :=
  letI := relCWComplexDiscBundleSubtypeSphereBundle F E
  uliftAdjunctionSpace (univ : Set (discBundle F E)) (discSphereBaseMap F E g)

/-- The canonical closed embedding `Z → Z ∪_g D(E)`. -/
def discBundleAttachmentInr : C(Z, discBundleAttachmentSpace F E g) :=
  letI := relCWComplexDiscBundleSubtypeSphereBundle F E
  uliftAdjunctionInr (univ : Set (discBundle F E)) (discSphereBaseMap F E g)

/-- The canonical characteristic-side map `D(E) → Z ∪_g D(E)`. -/
def discBundleAttachmentInl : C(discBundle F E, discBundleAttachmentSpace F E g) :=
  letI := relCWComplexDiscBundleSubtypeSphereBundle F E
  (uliftAdjunctionInl (univ : Set (discBundle F E)) (discSphereBaseMap F E g)).comp
    ⟨(Homeomorph.Set.univ (discBundle F E)).symm,
      (Homeomorph.Set.univ (discBundle F E)).symm.continuous⟩

/-- On the unit sphere bundle `S(E)`, `discBundleAttachmentInl` glues each vector `s` to `g s` in
`Z`. -/
theorem discBundleAttachmentInl_sphere (s : sphereBundle F E) :
    discBundleAttachmentInl F E g ⟨s.val, mem_discBundle.2 (mem_sphereBundle.1 s.property).le⟩ =
      discBundleAttachmentInr F E g (g s) :=
  letI := relCWComplexDiscBundleSubtypeSphereBundle F E
  uliftAdjunctionInl_eq_inr (univ : Set (discBundle F E)) (discSphereBaseMap F E g)
    ((discSphereBaseHomeo F E).symm s)

/-- **Pushout eliminator for `discBundleAttachmentSpace`.** Continuous maps `f : D(E) → W` and
`h : Z → W` into a space `W` in an arbitrary universe that agree along `g : S(E) → Z` descend
uniquely to a continuous map `Z ∪_g D(E) → W`. -/
def discBundleAttachmentDesc {W : Type w} [TopologicalSpace W]
    (f : C(discBundle F E, W)) (h : C(Z, W))
    (hfg : ∀ s : sphereBundle F E,
      f ⟨s.val, mem_discBundle.2 (mem_sphereBundle.1 s.property).le⟩ = h (g s)) :
    C(discBundleAttachmentSpace F E g, W) :=
  letI := relCWComplexDiscBundleSubtypeSphereBundle F E
  uliftAdjunctionDesc (univ : Set (discBundle F E)) (discSphereBaseMap F E g)
    (f.comp ⟨Homeomorph.Set.univ (discBundle F E),
      (Homeomorph.Set.univ (discBundle F E)).continuous⟩)
    h fun s ↦ hfg (discSphereBaseHomeo F E s)

@[simp]
theorem discBundleAttachmentDesc_inl {W : Type w} [TopologicalSpace W]
    (f : C(discBundle F E, W)) (h : C(Z, W))
    (hfg : ∀ s : sphereBundle F E,
      f ⟨s.val, mem_discBundle.2 (mem_sphereBundle.1 s.property).le⟩ = h (g s))
    (v : discBundle F E) :
    discBundleAttachmentDesc F E g f h hfg (discBundleAttachmentInl F E g v) = f v :=
  letI := relCWComplexDiscBundleSubtypeSphereBundle F E
  uliftAdjunctionDesc_inl (univ : Set (discBundle F E)) (discSphereBaseMap F E g)
    (f.comp ⟨Homeomorph.Set.univ (discBundle F E),
      (Homeomorph.Set.univ (discBundle F E)).continuous⟩)
    h (fun s ↦ hfg (discSphereBaseHomeo F E s)) ⟨v, mem_univ v⟩

@[simp]
theorem discBundleAttachmentDesc_inr {W : Type w} [TopologicalSpace W]
    (f : C(discBundle F E, W)) (h : C(Z, W))
    (hfg : ∀ s : sphereBundle F E,
      f ⟨s.val, mem_discBundle.2 (mem_sphereBundle.1 s.property).le⟩ = h (g s))
    (z : Z) :
    discBundleAttachmentDesc F E g f h hfg (discBundleAttachmentInr F E g z) = h z :=
  letI := relCWComplexDiscBundleSubtypeSphereBundle F E
  uliftAdjunctionDesc_inr (univ : Set (discBundle F E)) (discSphereBaseMap F E g)
    (f.comp ⟨Homeomorph.Set.univ (discBundle F E),
      (Homeomorph.Set.univ (discBundle F E)).continuous⟩)
    h (fun s ↦ hfg (discSphereBaseHomeo F E s)) z

@[simp]
theorem discBundleAttachmentDesc_comp_inl {W : Type w} [TopologicalSpace W]
    (f : C(discBundle F E, W)) (h : C(Z, W))
    (hfg : ∀ s : sphereBundle F E,
      f ⟨s.val, mem_discBundle.2 (mem_sphereBundle.1 s.property).le⟩ = h (g s)) :
    (discBundleAttachmentDesc F E g f h hfg).comp (discBundleAttachmentInl F E g) = f :=
  ContinuousMap.ext (discBundleAttachmentDesc_inl F E g f h hfg)

@[simp]
theorem discBundleAttachmentDesc_comp_inr {W : Type w} [TopologicalSpace W]
    (f : C(discBundle F E, W)) (h : C(Z, W))
    (hfg : ∀ s : sphereBundle F E,
      f ⟨s.val, mem_discBundle.2 (mem_sphereBundle.1 s.property).le⟩ = h (g s)) :
    (discBundleAttachmentDesc F E g f h hfg).comp (discBundleAttachmentInr F E g) = h :=
  ContinuousMap.ext (discBundleAttachmentDesc_inr F E g f h hfg)

/-- Every point of `Z ∪_g D(E)` lies in the image of `D(E)` or in the image of `Z`. -/
theorem exists_discBundleAttachmentInl_or_inr (p : discBundleAttachmentSpace F E g) :
    (∃ v : discBundle F E, discBundleAttachmentInl F E g v = p) ∨
      ∃ z : Z, discBundleAttachmentInr F E g z = p := by
  let _ := relCWComplexDiscBundleSubtypeSphereBundle F E
  rcases exists_uliftAdjunctionInl_or_inr (univ : Set (discBundle F E))
      (discSphereBaseMap F E g) p with ⟨v, hv⟩ | ⟨z, hz⟩
  · exact Or.inl ⟨v.val, hv⟩
  · exact Or.inr ⟨z, hz⟩

/-- Induction principle on points of `Z ∪_g D(E)` by splitting into the images of `D(E)` and
`Z`. -/
@[elab_as_elim]
theorem discBundleAttachmentSpace_induction_on
    {P : discBundleAttachmentSpace F E g → Prop} (p : discBundleAttachmentSpace F E g)
    (hl : ∀ v, P (discBundleAttachmentInl F E g v))
    (hr : ∀ z, P (discBundleAttachmentInr F E g z)) : P p := by
  rcases exists_discBundleAttachmentInl_or_inr F E g p with ⟨v, rfl⟩ | ⟨z, rfl⟩
  · exact hl v
  · exact hr z

/-- The ranges of `discBundleAttachmentInl` and `discBundleAttachmentInr` cover `Z ∪_g D(E)`. -/
theorem range_discBundleAttachmentInl_union_range_inr :
    range (discBundleAttachmentInl F E g) ∪ range (discBundleAttachmentInr F E g) = univ :=
  eq_univ_of_forall fun p ↦ exists_discBundleAttachmentInl_or_inr F E g p

/-- Two continuous maps out of `Z ∪_g D(E)` agree as soon as they agree on the images of `D(E)`
and `Z`. -/
theorem discBundleAttachmentSpace_continuousMap_ext {W : Type w} [TopologicalSpace W]
    {f₁ f₂ : C(discBundleAttachmentSpace F E g, W)}
    (hl : ∀ v, f₁ (discBundleAttachmentInl F E g v) = f₂ (discBundleAttachmentInl F E g v))
    (hr : ∀ z, f₁ (discBundleAttachmentInr F E g z) = f₂ (discBundleAttachmentInr F E g z)) :
    f₁ = f₂ :=
  ContinuousMap.ext fun p ↦ discBundleAttachmentSpace_induction_on F E g p hl hr

/-- A subset of `Z ∪_g D(E)` is closed if and only if its preimages in `D(E)` and in `Z` are both
closed. -/
theorem isClosed_iff_discBundleAttachmentSpace (s : Set (discBundleAttachmentSpace F E g)) :
    IsClosed s ↔
      IsClosed (discBundleAttachmentInl F E g ⁻¹' s) ∧
        IsClosed (discBundleAttachmentInr F E g ⁻¹' s) := by
  let _ := relCWComplexDiscBundleSubtypeSphereBundle F E
  refine (isClosed_iff_uliftAdjunctionSpace (univ : Set (discBundle F E))
    (discSphereBaseMap F E g) s).trans ?_
  rw [← (Homeomorph.Set.univ (discBundle F E)).symm.isClosed_preimage]
  rfl

/-- The inclusion `Z → Z ∪_g D(E)` is a closed embedding. -/
theorem isClosedEmbedding_discBundleAttachmentInr :
    IsClosedEmbedding (discBundleAttachmentInr F E g) :=
  let _ := relCWComplexDiscBundleSubtypeSphereBundle F E
  isClosedEmbedding_uliftAdjunctionInr (univ : Set (discBundle F E)) (discSphereBaseMap F E g)

/-- When `Z` is Hausdorff, the disc-bundle attachment `Z ∪_g D(E)` is Hausdorff. -/
instance t2Space_discBundleAttachmentSpace [T2Space Z] :
    T2Space (discBundleAttachmentSpace F E g) :=
  letI := relCWComplexDiscBundleSubtypeSphereBundle F E
  t2Space_uliftAdjunctionSpace (univ : Set (discBundle F E)) (discSphereBaseMap F E g)

/-- **Classical relative CW model of a disc-bundle attachment `Z ∪_g D(E)`.** For a finite-rank
vector bundle `E → B` with continuous fibre norm over a Hausdorff CW complex `B` and any continuous
attaching map `g : S(E) → Z`, the adjunction space `Z ∪_g D(E)` carries a classical relative CW
structure relative to `range (discBundleAttachmentInr F E g)`, whose `(m + r)`-cells correspond to
the `m`-cells of `B`. -/
@[instance_reducible]
def discBundleAttachmentCWModel :
    RelCWComplex (univ : Set (discBundleAttachmentSpace F E g))
      (range (discBundleAttachmentInr F E g)) :=
  letI := relCWComplexDiscBundleSubtypeSphereBundle F E
  uliftAdjunctionCWModel (univ : Set (discBundle F E)) (discSphereBaseMap F E g)

/-- The `n`-cells of `discBundleAttachmentCWModel` correspond bijectively to the `m`-cells of `B`
with `m + r = n`, where `r` is the rank of the bundle. -/
def discBundleAttachmentCWModelCellEquiv (n : ℕ) :
    letI := discBundleAttachmentCWModel F E g
    cell (univ : Set (discBundleAttachmentSpace F E g)) n ≃
      Σ m : {m : ℕ // m + Module.finrank ℝ F = n}, cell (univ : Set B) m :=
  letI := relCWComplexDiscBundleSubtypeSphereBundle F E
  (uliftAdjunctionCellEquiv (univ : Set (discBundle F E)) (discSphereBaseMap F E g) n).trans
    (relCWComplexDiscBundleSubtypeSphereBundleCellEquiv F E n)

/-- Below the fibre rank `r`, `discBundleAttachmentCWModel` has no `n`-cells. -/
theorem isEmpty_cell_discBundleAttachmentCWModel_of_lt {n : ℕ} (hn : n < Module.finrank ℝ F) :
    letI := discBundleAttachmentCWModel F E g
    IsEmpty (cell (univ : Set (discBundleAttachmentSpace F E g)) n) :=
  let := discBundleAttachmentCWModel F E g
  letI := relCWComplexDiscBundleSubtypeSphereBundle F E
  have := isEmpty_cell_relCWComplexDiscBundleSubtypeSphereBundle_of_lt (F := F) (E := E) hn
  (uliftAdjunctionCellEquiv (univ : Set (discBundle F E))
    (discSphereBaseMap F E g) n).isEmpty_congr.2 inferInstance

private lemma uliftAdjunctionCellEquiv_discBundleAttachmentCWModel_symm {n : ℕ}
    (c : Σ m : {m : ℕ // m + Module.finrank ℝ F = n}, cell (univ : Set B) m) :
    letI := discBundleAttachmentCWModel F E g
    letI := relCWComplexDiscBundleSubtypeSphereBundle F E
    uliftAdjunctionCellEquiv (univ : Set (discBundle F E)) (discSphereBaseMap F E g) n
      ((discBundleAttachmentCWModelCellEquiv F E g n).symm c) =
      (relCWComplexDiscBundleSubtypeSphereBundleCellEquiv F E n).symm c := by
  let _ := relCWComplexDiscBundleSubtypeSphereBundle F E
  exact (uliftAdjunctionCellEquiv (univ : Set (discBundle F E))
    (discSphereBaseMap F E g) n).apply_symm_apply _

/-- Each characteristic map of `discBundleAttachmentCWModel` is the characteristic map of the
corresponding cell of `TauCeti.relCWComplexDiscBundleSubtypeSphereBundle` in `D(E)` followed by
`discBundleAttachmentInl`. -/
theorem discBundleAttachmentCWModel_map_apply {n : ℕ}
    (c : Σ m : {m : ℕ // m + Module.finrank ℝ F = n}, cell (univ : Set B) m)
    {x : Fin n → ℝ} (hx : x ∈ closedBall 0 1) :
    letI := discBundleAttachmentCWModel F E g
    letI := relCWComplexDiscBundleSubtypeSphereBundle F E
    map n ((discBundleAttachmentCWModelCellEquiv F E g n).symm c) x =
      discBundleAttachmentInl F E g
        (map n ((relCWComplexDiscBundleSubtypeSphereBundleCellEquiv F E n).symm c) x) := by
  let _ := relCWComplexDiscBundleSubtypeSphereBundle F E
  refine (uliftAdjunctionCWModel_map_apply (univ : Set (discBundle F E)) (discSphereBaseMap F E g)
    n _ hx).trans ?_
  rw [uliftAdjunctionCellEquiv_discBundleAttachmentCWModel_symm]
  rfl

private theorem image_map_discBundleAttachmentCWModel {n : ℕ}
    (c : Σ m : {m : ℕ // m + Module.finrank ℝ F = n}, cell (univ : Set B) m)
    (S : Set (Fin n → ℝ)) (hS : S ⊆ closedBall 0 1) :
    letI := discBundleAttachmentCWModel F E g
    letI := relCWComplexDiscBundleSubtypeSphereBundle F E
    map n ((discBundleAttachmentCWModelCellEquiv F E g n).symm c) '' S =
      discBundleAttachmentInl F E g ''
        (map n ((relCWComplexDiscBundleSubtypeSphereBundleCellEquiv F E n).symm c) '' S) := by
  let _ := relCWComplexDiscBundleSubtypeSphereBundle F E
  refine (image_map_uliftAdjunctionCWModel (univ : Set (discBundle F E)) (discSphereBaseMap F E g)
    n _ S hS).trans ?_
  rw [uliftAdjunctionCellEquiv_discBundleAttachmentCWModel_symm]
  ext p
  simp only [mem_image, mem_preimage]
  exact ⟨fun ⟨v, hvS, hvp⟩ ↦ ⟨v.val, hvS, hvp⟩, fun ⟨v, hvS, hvp⟩ ↦ ⟨⟨v, mem_univ v⟩, hvS, hvp⟩⟩

/-- The open cell of `discBundleAttachmentCWModel` over an `m`-cell `j` of `B` is the image under
`discBundleAttachmentInl` of the vectors of norm less than one in `D(E)` over `openCell m j`. -/
@[simp]
theorem openCell_discBundleAttachmentCWModel {n : ℕ}
    (c : Σ m : {m : ℕ // m + Module.finrank ℝ F = n}, cell (univ : Set B) m) :
    letI := discBundleAttachmentCWModel F E g
    openCell n ((discBundleAttachmentCWModelCellEquiv F E g n).symm c) =
      discBundleAttachmentInl F E g '' {v : discBundle F E |
        (v : TotalSpace F E).proj ∈ openCell c.1.val c.2 ∧ ‖(v : TotalSpace F E).snd‖ < 1} := by
  let _ := discBundleAttachmentCWModel F E g
  let _ := relCWComplexDiscBundleSubtypeSphereBundle F E
  rw [openCell, image_map_discBundleAttachmentCWModel F E g c (ball 0 1) ball_subset_closedBall,
    ← openCell, openCell_relCWComplexDiscBundleSubtypeSphereBundle]
  congr 1; ext v; simp [discBundleProj_apply, and_comm]

/-- The closed cell of `discBundleAttachmentCWModel` over an `m`-cell `j` of `B` is the image under
`discBundleAttachmentInl` of `D(E)` over `closedCell m j`. -/
@[simp]
theorem closedCell_discBundleAttachmentCWModel {n : ℕ}
    (c : Σ m : {m : ℕ // m + Module.finrank ℝ F = n}, cell (univ : Set B) m) :
    letI := discBundleAttachmentCWModel F E g
    closedCell n ((discBundleAttachmentCWModelCellEquiv F E g n).symm c) =
      discBundleAttachmentInl F E g '' (discBundleProj F E ⁻¹' closedCell c.1.val c.2) := by
  let _ := discBundleAttachmentCWModel F E g
  let _ := relCWComplexDiscBundleSubtypeSphereBundle F E
  rw [closedCell, image_map_discBundleAttachmentCWModel F E g c (closedBall 0 1) Subset.rfl,
    ← closedCell, closedCell_relCWComplexDiscBundleSubtypeSphereBundle]

/-- The boundary of the cell of `discBundleAttachmentCWModel` over an `m`-cell `j` of `B` is the
image under `discBundleAttachmentInl` of `S(E)` over `closedCell m j` together with `D(E)` over
`cellFrontier m j`. -/
@[simp]
theorem cellFrontier_discBundleAttachmentCWModel {n : ℕ}
    (c : Σ m : {m : ℕ // m + Module.finrank ℝ F = n}, cell (univ : Set B) m) :
    letI := discBundleAttachmentCWModel F E g
    cellFrontier n ((discBundleAttachmentCWModelCellEquiv F E g n).symm c) =
      discBundleAttachmentInl F E g ''
        (Subtype.val ⁻¹' sphereBundle F E ∩ discBundleProj F E ⁻¹' closedCell c.1.val c.2 ∪
          discBundleProj F E ⁻¹' cellFrontier c.1.val c.2) := by
  let _ := discBundleAttachmentCWModel F E g
  let _ := relCWComplexDiscBundleSubtypeSphereBundle F E
  rw [cellFrontier, image_map_discBundleAttachmentCWModel F E g c (sphere 0 1)
    sphere_subset_closedBall, ← cellFrontier,
    cellFrontier_relCWComplexDiscBundleSubtypeSphereBundle]

/-- `discBundleAttachmentCWModel` is finite-dimensional when `B` is finite-dimensional. -/
theorem finiteDimensional_discBundleAttachmentCWModel
    [RelCWComplex.FiniteDimensional (univ : Set B)] :
    letI := discBundleAttachmentCWModel F E g
    RelCWComplex.FiniteDimensional (univ : Set (discBundleAttachmentSpace F E g)) :=
  let _ := discBundleAttachmentCWModel F E g
  let _ := relCWComplexDiscBundleSubtypeSphereBundle F E
  have := finiteDimensional_relCWComplexDiscBundleSubtypeSphereBundle F E
  finiteDimensional_uliftAdjunctionCWModel (univ : Set (discBundle F E)) (discSphereBaseMap F E g)

/-- `discBundleAttachmentCWModel` has finite type when `B` has finite type. -/
theorem finiteType_discBundleAttachmentCWModel [RelCWComplex.FiniteType (univ : Set B)] :
    letI := discBundleAttachmentCWModel F E g
    RelCWComplex.FiniteType (univ : Set (discBundleAttachmentSpace F E g)) :=
  let _ := discBundleAttachmentCWModel F E g
  let _ := relCWComplexDiscBundleSubtypeSphereBundle F E
  have := finiteType_relCWComplexDiscBundleSubtypeSphereBundle F E
  finiteType_uliftAdjunctionCWModel (univ : Set (discBundle F E)) (discSphereBaseMap F E g)

/-- `discBundleAttachmentCWModel` is finite when `B` is finite. -/
theorem finite_discBundleAttachmentCWModel [RelCWComplex.Finite (univ : Set B)] :
    letI := discBundleAttachmentCWModel F E g
    RelCWComplex.Finite (univ : Set (discBundleAttachmentSpace F E g)) :=
  let _ := discBundleAttachmentCWModel F E g
  let _ := relCWComplexDiscBundleSubtypeSphereBundle F E
  have := finite_relCWComplexDiscBundleSubtypeSphereBundle F E
  finite_uliftAdjunctionCWModel (univ : Set (discBundle F E)) (discSphereBaseMap F E g)

/-- **Base homotopy invariance of disc-bundle attachments.** A homotopy equivalence `e : Z ≃ₕ Z'`
(with `Z` and `Z'` in independent universes) induces a homotopy equivalence
`Z ∪_g D(E) ≃ₕ Z' ∪_{e ∘ g} D(E)` restricting to `e` on `Z` and to `e.symm` on `Z'`. -/
theorem exists_homotopyEquiv_discBundleAttachmentSpace {Z' : Type w} [TopologicalSpace Z']
    (e : Z ≃ₕ Z') :
    ∃ H : discBundleAttachmentSpace.{u, v} F E g ≃ₕ
        discBundleAttachmentSpace.{u, w} F E (e.toFun.comp g),
      (∀ z, H (discBundleAttachmentInr F E g z) =
        discBundleAttachmentInr F E (e.toFun.comp g) (e z)) ∧
      ∀ z', H.symm (discBundleAttachmentInr F E (e.toFun.comp g) z') =
        discBundleAttachmentInr F E g (e.symm z') :=
  let _ := relCWComplexDiscBundleSubtypeSphereBundle F E
  exists_homotopyEquiv_uliftAdjunctionSpace (univ : Set (discBundle F E))
    (discSphereBaseMap F E g) e

end SphereAttachment

end TauCeti
