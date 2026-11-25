/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.RelativeCellComplex.Pushout
public import TauCeti.Topology.CWComplex.Abstract.Classical
public import TauCeti.Topology.CWComplex.Abstract.ClosedEmbedding
public import TauCeti.Topology.CWComplex.Abstract.Hausdorff
public import TauCeti.Topology.CWComplex.Classical.Image
public import TauCeti.Topology.CWComplex.Classical.RelativeCWComplex
public import TauCeti.Topology.CWComplex.Classical.Trans
public import TauCeti.Topology.Homotopy.Extension.Pushout
import TauCeti.Topology.Homotopy.Extension.CWComplex

/-!
# Gluing a relative CW complex to a space

Let `C` be a classical relative CW complex with base `D` in a Hausdorff space, and let
`a : D → Z` be a continuous map to a space `Z`. The adjunction space `Z ∪_a C`
(`TauCeti.relCWAdjunctionSpace`) is the pushout in `TopCat` of the inclusion `D → C` and `a`, with
its quotient topology. This file shows:

* the inclusion `D → C` is an embedding whose image has the homotopy extension property
  (`TauCeti.isEmbedding_relCWBaseInclusion`,
  `TauCeti.hasHomotopyExtensionProperty_range_relCWBaseInclusion`);
* the map `Z → Z ∪_a C` is a closed embedding
  (`TauCeti.isClosedEmbedding_pushout_inr_relCWBaseInclusion`);
* `Z ∪_a C` is Hausdorff when `Z` is (`TauCeti.t2Space_relCWAdjunctionSpace`);
* `Z ∪_a C` is a classical relative CW complex relative to the image of `Z`
  (`TauCeti.relativeCWPushout`), whose `n`-cells are the `n`-cells of `C`
  (`TauCeti.relativeCWPushoutCellEquiv`) and whose characteristic maps are those of `C` followed
  by the map `C → Z ∪_a C` (`TauCeti.relativeCWPushout_map_apply`);
* the same holds for any pushout `P` of `D → C` along a map to `Z`, not only the chosen one: the
  map `Z → P` is a closed embedding (`CategoryTheory.IsPushout.isClosedEmbedding_inr`), `P`
  is Hausdorff when `Z` is (`CategoryTheory.IsPushout.t2Space`), and it is a relative CW complex
  over the image of `Z` (`CategoryTheory.IsPushout.relCWComplex`) with the cells of `C`
  (`CategoryTheory.IsPushout.relCWComplexCellEquiv`), whose characteristic maps are those of `C`
  followed by `C → P` (`CategoryTheory.IsPushout.relCWComplex_map_apply`);
* if moreover `Z` is a CW complex `W` relative to a base `A`, and the map `D → W` sends the part
  in `D` of the boundary of every `n`-cell of `C` into the skeleton `skeletonLT W n`, then `P` is a
  CW complex relative to the image of `A`
  (`CategoryTheory.IsPushout.relCWComplexOfMapsToSkeletonLT`, and
  `CategoryTheory.IsPushout.cwComplexOfMapsToSkeletonLT` for an absolute CW complex `W`), whose
  `n`-cells are those of `W` and those of `C`
  (`CategoryTheory.IsPushout.relCWComplexOfMapsToSkeletonLTCellEquiv`) with their characteristic
  maps followed by `j : W → P` and by `i : C → P`;
* up to homotopy equivalence, `Z ∪_a C` depends only on the homotopy type of `Z`: a homotopy
  equivalence `e : Z ≃ₕ Z'` induces a homotopy equivalence `Z ∪_a C ≃ₕ Z' ∪_{e ∘ a} C` which is
  `e` on `Z` and whose inverse is the inverse of `e` on `Z'`
  (`ContinuousMap.HomotopyEquiv.exists_homotopyEquiv_relCWAdjunctionSpace`).

Except for the gluing along a cellular map, the space `Z` needs no CW structure. The proof passes
through the categorical relative CW complexes of Mathlib: `C` is a categorical relative CW complex
on the inclusion of `D` (`TauCeti.toRelativeCWComplex`), its cobase change along `a` is a
categorical relative CW complex with the same cells
(`HomotopicalAlgebra.RelativeCellComplex.pushout`), and categorical relative CW complexes are
closed embeddings, are Hausdorff over a Hausdorff base, and carry classical structures
(`TopCat.RelativeCWComplex.toRelCWComplex`). The CW structure on a pushout along a cellular map is
the composite (`TauCeti.relCWComplexTrans`) of the relative CW structure of `P` over the image of
`W` with the structure of `W` over `A`, carried to `P` along the closed embedding of `W`. A point
of the boundary of a cell of `C` glued to a point of `W` comes from `D`, so the part in `W` of the
boundary of an `n`-cell of `P` lies in the image of `skeletonLT W n`: this is the compatibility
condition of the composite.

These are the cell attachments of Morse theory and of cellular approximation: attaching cells to a
space along maps of their boundary spheres keeps the cells and their characteristic maps.

## Main definitions

* `TauCeti.relCWAdjunctionSpace`: the adjunction space `Z ∪_a C`.
* `TauCeti.relativeCWPushout`: the classical relative CW structure on `Z ∪_a C` relative to `Z`.
* `TauCeti.relativeCWPushoutCellEquiv`: its `n`-cells are the `n`-cells of `C`.
* `CategoryTheory.IsPushout.relCWComplex`: the relative CW structure on any pushout of `D → C`.
* `CategoryTheory.IsPushout.relCWComplexOfMapsToSkeletonLT` and
  `CategoryTheory.IsPushout.cwComplexOfMapsToSkeletonLT`: the CW structure on a pushout of a
  relative CW complex along a cellular map, with cells
  `CategoryTheory.IsPushout.relCWComplexOfMapsToSkeletonLTCellEquiv` and
  `CategoryTheory.IsPushout.cwComplexOfMapsToSkeletonLTCellEquiv`.

## Main results

* `TauCeti.isEmbedding_relCWBaseInclusion` and
  `TauCeti.hasHomotopyExtensionProperty_range_relCWBaseInclusion`: the inclusion `D → C` is an
  embedding whose image has the homotopy extension property.
* `TauCeti.isClosedEmbedding_pushout_inr_relCWBaseInclusion`: `Z → Z ∪_a C` is a closed embedding.
* `TauCeti.t2Space_relCWAdjunctionSpace`: `Z ∪_a C` is Hausdorff when `Z` is.
* `TauCeti.relativeCWPushout_map_apply`: the characteristic maps of `Z ∪_a C` are those of `C`,
  followed by `C → Z ∪_a C`.
* `CategoryTheory.IsPushout.finite_cwComplexOfMapsToSkeletonLT`: gluing a finite relative CW
  complex to a finite CW complex along a cellular map gives a finite CW complex.
* `ContinuousMap.HomotopyEquiv.exists_homotopyEquiv_relCWAdjunctionSpace`: a homotopy equivalence
  of `Z` with `Z'` induces one of `Z ∪_a C` with `Z' ∪_{e ∘ a} C`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Chapter 0 and the Appendix.
* R. Fritsch and R. Piccinini, *Cellular Structures in Topology*, Cambridge University Press,
  1990, Chapter 2.
* R. Brown, *Topology and Groupoids*, 2006, Section 7.5, the gluing theorem for homotopy
  equivalences, for the change of base.
-/

public section

noncomputable section

universe u

open CategoryTheory Limits Topology Set Metric

namespace TauCeti

open Topology.RelCWComplex

variable {X : Type u} [TopologicalSpace X] [T2Space X] {C D : Set X} [RelCWComplex C D]
  {Z : Type u} [TopologicalSpace Z] (a : C(D, Z))

/-- The inclusion of the base `D` of a classical relative CW complex into the complex `C`, as a
morphism of `TopCat`. -/
abbrev relCWBaseInclusion (C : Set X) {D : Set X} [RelCWComplex C D] :
    TopCat.of D ⟶ TopCat.of C :=
  TopCat.ofHom (ContinuousMap.inclusion (base_subset_complex (C := C)))

omit [T2Space X] in
variable (C) in
/-- The inclusion of the base `D` of a classical relative CW complex into the complex `C` is an
embedding. -/
theorem isEmbedding_relCWBaseInclusion : IsEmbedding (relCWBaseInclusion C) :=
  IsEmbedding.inclusion base_subset_complex

variable (C) in
/-- **The base of a relative CW complex is a cofibration.** The image of the inclusion of the base
`D` into the relative CW complex `C` has the homotopy extension property. -/
theorem hasHomotopyExtensionProperty_range_relCWBaseInclusion :
    HasHomotopyExtensionProperty (range (relCWBaseInclusion C)) := by
  have hr : range (relCWBaseInclusion C) = Subtype.val ⁻¹' D :=
    range_inclusion base_subset_complex
  rw [hr]
  exact hasHomotopyExtensionProperty_base

variable (C) in
/-- The adjunction space `Z ∪_a C` of a relative CW complex `C` with base `D` and a map
`a : D → Z`: the pushout in `TopCat` of the inclusion `D → C` and `a`. -/
abbrev relCWAdjunctionSpace : TopCat.{u} :=
  pushout (relCWBaseInclusion C) (TopCat.ofHom a)

variable (C) in
/-- The categorical relative CW complex `Z ⟶ Z ∪_a C` obtained by gluing `C` to `Z` along `a`. -/
abbrev relCWAdjunctionSpaceRelativeCWComplex :
    TopCat.RelativeCWComplex (pushout.inr (relCWBaseInclusion C) (TopCat.ofHom a)) :=
  (toRelativeCWComplex C).pushout (TopCat.ofHom a)

/-- **Gluing along a relative CW complex is a closed embedding.** The map from `Z` to the space
`Z ∪_a C` obtained by gluing a relative CW complex `C` with base `D` along `a : D → Z` is a
closed embedding. -/
theorem isClosedEmbedding_pushout_inr_relCWBaseInclusion :
    IsClosedEmbedding (pushout.inr (relCWBaseInclusion C) (TopCat.ofHom a)) :=
  (relCWAdjunctionSpaceRelativeCWComplex C a).isClosedEmbedding

/-- **Gluing a relative CW complex to a Hausdorff space gives a Hausdorff space.** -/
instance t2Space_relCWAdjunctionSpace [T2Space Z] :
    T2Space (relCWAdjunctionSpace C a) :=
  have : T2Space (TopCat.of Z) := ‹_›
  (relCWAdjunctionSpaceRelativeCWComplex C a).t2Space

variable (C) in
/-- **Gluing a relative CW complex to a space.** If `C` is a classical relative CW complex with
base `D` in a Hausdorff space and `a : D → Z` is continuous, the adjunction space `Z ∪_a C`, the
pushout of the inclusion `D → C` and `a`, is a classical relative CW complex relative to the image
of `Z`. Its cells are those of `C` (`TauCeti.relativeCWPushoutCellEquiv`), with the characteristic
maps of `C` followed by `C → Z ∪_a C` (`TauCeti.relativeCWPushout_map_apply`). -/
@[instance_reducible] def relativeCWPushout :
    RelCWComplex (univ : Set (relCWAdjunctionSpace C a))
      (range (pushout.inr (relCWBaseInclusion C) (TopCat.ofHom a))) :=
  (relCWAdjunctionSpaceRelativeCWComplex C a).toRelCWComplex

attribute [local instance] relativeCWPushout

variable (C) in
/-- The `n`-cells of `Z ∪_a C` are the `n`-cells of `C`. -/
def relativeCWPushoutCellEquiv (n : ℕ) :
    cell (univ : Set (relCWAdjunctionSpace C a)) n ≃ cell C n :=
  (relCWAdjunctionSpaceRelativeCWComplex C a).toRelCWComplexCellEquiv n

/-- The characteristic map of an `n`-cell of `Z ∪_a C` is the characteristic map of the
corresponding cell of `C`, followed by the map `C → Z ∪_a C`. -/
theorem relativeCWPushout_map_apply (n : ℕ) (i : cell (univ : Set (relCWAdjunctionSpace C a)) n)
    (x : closedBall (0 : Fin n → ℝ) 1) :
    map n i x = pushout.inl (relCWBaseInclusion C) (TopCat.ofHom a)
      ⟨map n (relativeCWPushoutCellEquiv C a n i) x,
        mem_of_subset_of_mem (closedCell_subset_complex n _) (mem_image_of_mem _ x.property)⟩ := by
  rw [TopCat.RelativeCWComplex.toRelCWComplex_map_apply]
  refine (ConcreteCategory.congr_hom ((toRelativeCWComplex C).pushout_cells_ι (TopCat.ofHom a) n
    (not_isMax n) (relativeCWPushoutCellEquiv C a n i)) _).trans ?_
  rw [ConcreteCategory.comp_apply]
  congr 1
  apply Subtype.ext
  rw [coe_toRelativeCWComplex_cells_ι_apply, Homeomorph.apply_symm_apply]

end TauCeti

namespace CategoryTheory.IsPushout

open TauCeti Limits Set Topology Topology.RelCWComplex

variable {X : Type u} [TopologicalSpace X] [T2Space X] {C D : Set X} [RelCWComplex C D]
  {Z P : TopCat.{u}} {g : TopCat.of D ⟶ Z} {i : TopCat.of C ⟶ P} {j : Z ⟶ P}
  (h : IsPushout (relCWBaseInclusion C) g i j)

omit [T2Space X] in
include h in
/-- In a pushout of the inclusion of the base of a relative CW complex, the comparison map from
`TauCeti.relCWAdjunctionSpace` is a closed embedding. -/
private theorem isClosedEmbedding_isoPushout_inv : IsClosedEmbedding h.isoPushout.inv :=
  (TopCat.homeoOfIso h.isoPushout.symm).isClosedEmbedding

omit [T2Space X] in
include h in
private theorem image_range_pushout_inr :
    h.isoPushout.inv '' range (pushout.inr (relCWBaseInclusion C) g) = range j := by
  rw [← range_comp]
  exact congrArg (fun f : Z ⟶ P ↦ range f) h.inr_isoPushout_inv

omit [T2Space X] in
include h in
/-- **Gluing along a relative CW complex is a closed embedding, for any pushout square.** In a
pushout `P` of the inclusion `D → C` of the base of a relative CW complex along a map `g : D → Z`,
the map `j : Z → P` is a closed embedding. For the canonical pushout this is
`TauCeti.isClosedEmbedding_pushout_inr_relCWBaseInclusion`. -/
theorem isClosedEmbedding_inr : IsClosedEmbedding j :=
  TopCat.isClosedEmbedding_of_isPushout h.flip
    (IsClosedEmbedding.inclusion base_subset_complex
      ((isClosedBase C).preimage continuous_subtypeVal))

include h in
/-- A pushout of the inclusion `D → C` of the base of a relative CW complex is Hausdorff when the
space `Z` it is glued to is. -/
theorem t2Space [T2Space Z] : T2Space P :=
  haveI := t2Space_relCWAdjunctionSpace (C := C) g.hom
  (TopCat.homeoOfIso h.isoPushout).isEmbedding.t2Space

/-- **Gluing a relative CW complex to a space, for any pushout square.** If `C` is a relative CW
complex with base `D` in a Hausdorff space and `P` is a pushout of the inclusion `D → C` and of a
map `g : D → Z`, with maps `i : C → P` and `j : Z → P`, then `P` is a CW complex relative to the
image of `j`. Its cells are those of `C` (`CategoryTheory.IsPushout.relCWComplexCellEquiv`), with
the characteristic maps of `C` followed by `i` (`CategoryTheory.IsPushout.relCWComplex_map_apply`).
For the canonical pushout this is `TauCeti.relativeCWPushout`. -/
@[instance_reducible]
def relCWComplex : RelCWComplex (univ : Set P) (range j) :=
  letI := relativeCWPushout C g.hom
  (isClosedEmbedding_isoPushout_inv h).relCWComplex
    (image_univ_of_surjective (TopCat.homeoOfIso h.isoPushout.symm).surjective)
    (image_range_pushout_inr h)

/-- The `n`-cells of the relative CW structure on a pushout `P` of `D → C` are the `n`-cells
of `C`. -/
def relCWComplexCellEquiv (n : ℕ) :
    letI := h.relCWComplex
    cell (univ : Set P) n ≃ cell C n :=
  letI := relativeCWPushout C g.hom
  ((isClosedEmbedding_isoPushout_inv h).relCWComplexCellEquiv _ _ n).trans
    (relativeCWPushoutCellEquiv C g.hom n)

/-- The characteristic map of an `n`-cell of a pushout `P` of `D → C` is the characteristic map of
the corresponding cell of `C`, followed by `i : C → P`. -/
theorem relCWComplex_map_apply (n : ℕ)
    (c : letI := h.relCWComplex; cell (univ : Set P) n) (x : closedBall (0 : Fin n → ℝ) 1) :
    letI := h.relCWComplex
    RelCWComplex.map n c x = i ⟨RelCWComplex.map n (h.relCWComplexCellEquiv n c) x,
      closedCell_subset_complex n _ (mem_image_of_mem _ x.property)⟩ := by
  let := relativeCWPushout C g.hom
  let := h.relCWComplex
  have hc := (isClosedEmbedding_isoPushout_inv h).coe_map_relCWComplex
    (image_univ_of_surjective (TopCat.homeoOfIso h.isoPushout.symm).surjective)
    (image_range_pushout_inr h) n c
  rw [hc, Function.comp_apply, relativeCWPushout_map_apply g.hom]
  exact ConcreteCategory.congr_hom h.inl_isoPushout_inv _

end CategoryTheory.IsPushout

namespace CategoryTheory.IsPushout

open TauCeti Topology.RelCWComplex

variable {X : Type u} [TopologicalSpace X] [T2Space X] {C D : Set X} [RelCWComplex C D]
  {W : Type u} [TopologicalSpace W] [T2Space W]
  {P : TopCat.{u}} {g : TopCat.of D ⟶ TopCat.of W} {i : TopCat.of C ⟶ P}
  {j : TopCat.of W ⟶ P} (h : IsPushout (relCWBaseInclusion C) g i j)

section Relative

variable {A : Set W} [RelCWComplex (univ : Set W) A]
  (hg : ∀ n (c : cell C n) (x : D), (x : X) ∈ cellFrontier n c →
    g x ∈ (skeletonLT (univ : Set W) n : Set W))

include h

/-- The relative CW structure of `W` over `A`, carried to its image in `P`, with base any set `A'`
equal to the image of `A`. -/
private abbrev rangeRelCWComplex {A' : Set P} (hA : j '' A = A') : RelCWComplex (range j) A' :=
  h.isClosedEmbedding_inr.relCWComplex (C := univ) (D := A) image_univ hA

include hg

/-- In a pushout `P` of `D → C` along `g : D → W`, the part in the image of `W` of the boundary of
an `n`-cell lies in the image of the skeleton `skeletonLT W n`, if `g` maps the part in `D` of the
boundary of every `n`-cell of `C` into that skeleton. -/
private theorem cellFrontier_inter_range_subset_image_skeletonLT (n : ℕ)
    (c : letI := h.relCWComplex; cell (univ : Set P) n) :
    letI := h.relCWComplex
    cellFrontier n c ∩ range j ⊆ j '' (skeletonLT (univ : Set W) n : Set W) := by
  let := h.relCWComplex
  rintro _ ⟨⟨x, hx, rfl⟩, w, hw⟩
  have hmap := h.relCWComplex_map_apply n c ⟨x, sphere_subset_closedBall hx⟩
  -- A point of `C` glued to a point of `W` comes from a point `s` of the base `D`.
  obtain ⟨s, hs, rfl⟩ := (Types.pushoutCocone_inl_eq_inr_iff_of_isColimit
    ((forget TopCat).map_isPushout h).isColimit (isEmbedding_relCWBaseInclusion C).injective
      _ w).1 (hmap.symm.trans hw.symm)
  refine ⟨g s, hg n (h.relCWComplexCellEquiv n c) s ?_, hw⟩
  have hsx : (s : X) = RelCWComplex.map n (h.relCWComplexCellEquiv n c) x :=
    congrArg Subtype.val hs
  rw [hsx]
  exact mem_image_of_mem _ hx

/-- The compatibility condition for composing the relative CW structure of a pushout `P` of
`D → C` over the image of `W` with the relative CW structure of `W` over `A`. -/
private theorem cellFrontier_inter_range_subset_skeletonLT [T2Space P] {A' : Set P}
    (hA : j '' A = A') (n : ℕ)
    (c : letI := h.relCWComplex; cell (univ : Set P) n) :
    letI := h.relCWComplex
    letI := rangeRelCWComplex h hA
    cellFrontier n c ∩ range j ⊆ skeletonLT (range j) n := by
  let := h.relCWComplex
  let := rangeRelCWComplex h hA
  rw [h.isClosedEmbedding_inr.coe_skeletonLT_relCWComplex image_univ hA]
  exact cellFrontier_inter_range_subset_image_skeletonLT h hg n c

/-- The relative CW structure on a pushout `P` of `D → C` along a cellular map, over any set `A'`
equal to the image of `A`. -/
private abbrev relCWComplexOfMapsToSkeletonLTAux [T2Space P] {A' : Set P} (hA : j '' A = A') :
    RelCWComplex (univ : Set P) A' :=
  letI := h.relCWComplex
  letI := rangeRelCWComplex h hA
  relCWComplexTrans _ _ A' (cellFrontier_inter_range_subset_skeletonLT h hg hA)

/-- The cells of `CategoryTheory.IsPushout.relCWComplexOfMapsToSkeletonLTAux`. -/
private def relCWComplexOfMapsToSkeletonLTAuxCellEquiv [T2Space P] {A' : Set P}
    (hA : j '' A = A') (n : ℕ) :
    letI := relCWComplexOfMapsToSkeletonLTAux h hg hA
    cell (univ : Set P) n ≃ cell (univ : Set W) n ⊕ cell C n :=
  letI := h.relCWComplex
  letI := rangeRelCWComplex h hA
  (relCWComplexTransCellEquiv (cellFrontier_inter_range_subset_skeletonLT h hg hA) n).trans
    (Equiv.sumCongr (h.isClosedEmbedding_inr.relCWComplexCellEquiv image_univ hA n)
      (h.relCWComplexCellEquiv n))

private theorem relCWComplexOfMapsToSkeletonLTAux_map_inl [T2Space P] {A' : Set P}
    (hA : j '' A = A')
    (n : ℕ) (c : cell (univ : Set W) n) (x : Fin n → ℝ) :
    letI := relCWComplexOfMapsToSkeletonLTAux h hg hA
    RelCWComplex.map n ((relCWComplexOfMapsToSkeletonLTAuxCellEquiv h hg hA n).symm (.inl c)) x =
      j (RelCWComplex.map n c x) := by
  let := h.relCWComplex
  let := rangeRelCWComplex h hA
  set k := (h.isClosedEmbedding_inr.relCWComplexCellEquiv image_univ hA n).symm c
  have h₁ := map_relCWComplexTrans_inl (cellFrontier_inter_range_subset_skeletonLT h hg hA) n k
  have h₂ := h.isClosedEmbedding_inr.coe_map_relCWComplex image_univ hA n k
  exact (congrArg (fun e : PartialEquiv _ _ ↦ e x) h₁).trans
    ((congrFun h₂ x).trans (by simp [k]))

private theorem relCWComplexOfMapsToSkeletonLTAux_map_inr [T2Space P] {A' : Set P}
    (hA : j '' A = A')
    (n : ℕ) (c : cell C n) (x : closedBall (0 : Fin n → ℝ) 1) :
    letI := relCWComplexOfMapsToSkeletonLTAux h hg hA
    RelCWComplex.map n ((relCWComplexOfMapsToSkeletonLTAuxCellEquiv h hg hA n).symm (.inr c)) x =
      i ⟨RelCWComplex.map n c x,
        closedCell_subset_complex n _ (mem_image_of_mem _ x.property)⟩ := by
  let := h.relCWComplex
  let := rangeRelCWComplex h hA
  set k := (h.relCWComplexCellEquiv n).symm c
  have h₁ := map_relCWComplexTrans_inr (cellFrontier_inter_range_subset_skeletonLT h hg hA) n k
  refine (congrArg (fun e : PartialEquiv (Fin n → ℝ) _ ↦ e x) h₁).trans
    ((h.relCWComplex_map_apply n k x).trans ?_)
  simp only [k, Equiv.apply_symm_apply]

/-- **Gluing a relative CW complex to a CW complex along a cellular map.** Let `C` be a CW complex
relative to `D`, let `W` be a CW complex relative to `A`, and let `P` be a pushout of the inclusion
`D → C` along `g : D → W`, with maps `i : C → P` and `j : W → P`. If `g` maps the part in `D` of
the boundary of every `n`-cell of `C` into the skeleton `skeletonLT W n`, then `P` is a CW complex
relative to the image of `A`. Its `n`-cells are those of `W` and those of `C`
(`CategoryTheory.IsPushout.relCWComplexOfMapsToSkeletonLTCellEquiv`), with their characteristic
maps followed by `j` and by `i`. -/
@[instance_reducible]
def relCWComplexOfMapsToSkeletonLT : RelCWComplex (univ : Set P) (j '' A) :=
  haveI := h.t2Space
  relCWComplexOfMapsToSkeletonLTAux h hg rfl

/-- The `n`-cells of a pushout `P` of `D → C` along a cellular map to a relative CW complex `W` are
the `n`-cells of `W` together with those of `C`. -/
def relCWComplexOfMapsToSkeletonLTCellEquiv (n : ℕ) :
    letI := h.relCWComplexOfMapsToSkeletonLT hg
    cell (univ : Set P) n ≃ cell (univ : Set W) n ⊕ cell C n :=
  haveI := h.t2Space
  relCWComplexOfMapsToSkeletonLTAuxCellEquiv h hg rfl n

/-- The characteristic map of a cell of `W`, as a cell of the pushout `P`, is its characteristic
map in `W` followed by `j`. -/
@[simp]
theorem relCWComplexOfMapsToSkeletonLT_map_inl (n : ℕ) (c : cell (univ : Set W) n)
    (x : Fin n → ℝ) :
    letI := h.relCWComplexOfMapsToSkeletonLT hg
    RelCWComplex.map n ((h.relCWComplexOfMapsToSkeletonLTCellEquiv hg n).symm (.inl c)) x =
      j (RelCWComplex.map n c x) :=
  have := h.t2Space
  relCWComplexOfMapsToSkeletonLTAux_map_inl h hg rfl n c x

/-- The characteristic map of a cell of `C`, as a cell of the pushout `P`, is its characteristic
map in `C` followed by `i`. -/
@[simp]
theorem relCWComplexOfMapsToSkeletonLT_map_inr (n : ℕ) (c : cell C n)
    (x : closedBall (0 : Fin n → ℝ) 1) :
    letI := h.relCWComplexOfMapsToSkeletonLT hg
    RelCWComplex.map n ((h.relCWComplexOfMapsToSkeletonLTCellEquiv hg n).symm (.inr c)) x =
      i ⟨RelCWComplex.map n c x, closedCell_subset_complex n _ (mem_image_of_mem _ x.property)⟩ :=
  have := h.t2Space
  relCWComplexOfMapsToSkeletonLTAux_map_inr h hg rfl n c x

end Relative

section Absolute

variable [CWComplex (univ : Set W)]
  (hg : ∀ n (c : cell C n) (x : D), (x : X) ∈ cellFrontier n c →
    g x ∈ (skeletonLT (univ : Set W) n : Set W))

include h hg

/-- **Gluing a CW complex relative to `D` to a CW complex along a cellular map.** Let `C` be a CW
complex relative to `D`, let `W` be a CW complex, and let `P` be a pushout of the inclusion
`D → C` along `g : D → W`. If `g` maps the part in `D` of the boundary of every `n`-cell of `C`
into the skeleton `skeletonLT W n`, then `P` is a CW complex, whose `n`-cells are those of `W` and
those of `C` (`CategoryTheory.IsPushout.cwComplexOfMapsToSkeletonLTCellEquiv`). -/
@[instance_reducible]
def cwComplexOfMapsToSkeletonLT : CWComplex (univ : Set P) :=
  haveI := h.t2Space
  @RelCWComplex.toCWComplex _ _ _ (relCWComplexOfMapsToSkeletonLTAux h hg (image_empty _))

/-- The `n`-cells of a pushout `P` of `D → C` along a cellular map to a CW complex `W` are the
`n`-cells of `W` together with those of `C`. -/
def cwComplexOfMapsToSkeletonLTCellEquiv (n : ℕ) :
    letI := h.cwComplexOfMapsToSkeletonLT hg
    cell (univ : Set P) n ≃ cell (univ : Set W) n ⊕ cell C n :=
  haveI := h.t2Space
  relCWComplexOfMapsToSkeletonLTAuxCellEquiv h hg (image_empty _) n

/-- The characteristic map of a cell of `W`, as a cell of the CW complex `P`, is its characteristic
map in `W` followed by `j`. -/
@[simp]
theorem cwComplexOfMapsToSkeletonLT_map_inl (n : ℕ) (c : cell (univ : Set W) n)
    (x : Fin n → ℝ) :
    letI := h.cwComplexOfMapsToSkeletonLT hg
    RelCWComplex.map n ((h.cwComplexOfMapsToSkeletonLTCellEquiv hg n).symm (.inl c)) x =
      j (RelCWComplex.map n c x) :=
  have := h.t2Space
  relCWComplexOfMapsToSkeletonLTAux_map_inl h hg (image_empty _) n c x

/-- The characteristic map of a cell of `C`, as a cell of the CW complex `P`, is its characteristic
map in `C` followed by `i`. -/
@[simp]
theorem cwComplexOfMapsToSkeletonLT_map_inr (n : ℕ) (c : cell C n)
    (x : closedBall (0 : Fin n → ℝ) 1) :
    letI := h.cwComplexOfMapsToSkeletonLT hg
    RelCWComplex.map n ((h.cwComplexOfMapsToSkeletonLTCellEquiv hg n).symm (.inr c)) x =
      i ⟨RelCWComplex.map n c x, closedCell_subset_complex n _ (mem_image_of_mem _ x.property)⟩ :=
  have := h.t2Space
  relCWComplexOfMapsToSkeletonLTAux_map_inr h hg (image_empty _) n c x

/-- Gluing a finite CW complex relative to `D` to a finite CW complex along a cellular map gives a
finite CW complex. -/
theorem finite_cwComplexOfMapsToSkeletonLT [RelCWComplex.Finite C]
    [RelCWComplex.Finite (univ : Set W)] :
    letI := h.cwComplexOfMapsToSkeletonLT hg
    RelCWComplex.Finite (univ : Set P) :=
  letI := h.cwComplexOfMapsToSkeletonLT hg
  have := RelCWComplex.finite_cells_of_finite (C := (univ : Set W))
  have := RelCWComplex.finite_cells_of_finite (C := C)
  RelCWComplex.finite_of_finite_cells (.of_equiv ((Σ n, cell (univ : Set W) n) ⊕ Σ n, cell C n)
    ((Equiv.sigmaSumDistrib _ _).symm.trans
      (Equiv.sigmaCongrRight fun n ↦ (h.cwComplexOfMapsToSkeletonLTCellEquiv hg n).symm)))

end Absolute

end CategoryTheory.IsPushout

namespace ContinuousMap.HomotopyEquiv

open CategoryTheory Limits Set TauCeti Topology.RelCWComplex

variable {X : Type u} [TopologicalSpace X] [T2Space X] {D : Set X} {Z Z' : Type u}
  [TopologicalSpace Z] [TopologicalSpace Z']

/-- **Changing the base of a cell attachment by a homotopy equivalence.** Let `C` be a relative
CW complex with base `D` in a Hausdorff space, and `a : D → Z` an attaching map. A homotopy
equivalence `e : Z ≃ₕ Z'` induces a homotopy equivalence `Z ∪_a C ≃ₕ Z' ∪_{e ∘ a} C` which is
`e` on `Z`, and whose homotopy inverse is the homotopy inverse of `e` on `Z'`. -/
theorem exists_homotopyEquiv_relCWAdjunctionSpace (e : Z ≃ₕ Z') (C : Set X) [RelCWComplex C D]
    (a : C(D, Z)) :
    ∃ E : relCWAdjunctionSpace C a ≃ₕ relCWAdjunctionSpace C (e.toFun.comp a),
      (∀ z, E (pushout.inr (relCWBaseInclusion C) (TopCat.ofHom a) z) =
        pushout.inr (relCWBaseInclusion C) (TopCat.ofHom (e.toFun.comp a)) (e z)) ∧
      ∀ z, E.symm (pushout.inr (relCWBaseInclusion C) (TopCat.ofHom (e.toFun.comp a)) z) =
        pushout.inr (relCWBaseInclusion C) (TopCat.ofHom a) (e.symm z) := by
  have h := e.exists_homotopyEquiv_pushout _ (isEmbedding_relCWBaseInclusion C)
    (hasHomotopyExtensionProperty_range_relCWBaseInclusion C) (TopCat.ofHom a)
  rwa [← TopCat.ofHom_comp] at h

end ContinuousMap.HomotopyEquiv
