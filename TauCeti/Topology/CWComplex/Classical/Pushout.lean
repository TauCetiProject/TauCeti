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
public import TauCeti.Topology.CWComplex.Classical.Finite
public import TauCeti.Topology.CWComplex.Classical.Image
public import TauCeti.Topology.CWComplex.Classical.RelativeCWComplex
public import TauCeti.Topology.CWComplex.Classical.Trans
public import TauCeti.Topology.CWComplex.Classical.ULift
public import TauCeti.Topology.Homotopy.Extension.Pushout
import Mathlib.Topology.Category.TopCat.ULift
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
  (`ContinuousMap.HomotopyEquiv.exists_homotopyEquiv_relCWAdjunctionSpace`);
* when `C` lives in `Type u` and `Z` lives in an independent universe `Type v`, lifting to
  `Type (max u v)` gives the universe-polymorphic adjunction space `TauCeti.uliftAdjunctionSpace`
  with inclusions `TauCeti.uliftAdjunctionInl` and `TauCeti.uliftAdjunctionInr`, universal
  eliminator `TauCeti.uliftAdjunctionDesc`, relative CW model `TauCeti.uliftAdjunctionCWModel`,
  universe-change homeomorphism `TauCeti.exists_homeomorph_uliftAdjunctionSpace_ulift`, and
  universe-polymorphic homotopy invariance `TauCeti.exists_homotopyEquiv_uliftAdjunctionSpace`.

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
* `TauCeti.uliftAdjunctionSpace`, `TauCeti.uliftAdjunctionDesc`, and
  `TauCeti.uliftAdjunctionCWModel`: the universe-polymorphic adjunction space, its eliminator, and
  its relative CW structure for `C` in `Type u` and `Z` in `Type v`.
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
* `TauCeti.isClosedEmbedding_uliftAdjunctionInr`,
  `TauCeti.exists_homeomorph_uliftAdjunctionSpace_ulift`, and
  `TauCeti.exists_homotopyEquiv_uliftAdjunctionSpace`: closed base embedding, universe-change
  comparison, and homotopy invariance for `TauCeti.uliftAdjunctionSpace`.
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

namespace TauCeti

/-! ### Universe-polymorphic adjunction space of a relative CW complex -/

section ULiftAdjunction

open CategoryTheory ContinuousMap Limits Set Topology Topology.RelCWComplex

universe v w

/-- Convert a homeomorphism to a bundled continuous map without requiring a coercion instance. -/
private abbrev homC {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (e : α ≃ₜ β) : C(α, β) :=
  ⟨e, e.continuous⟩

/-- Canonical homeomorphism between a subset `S : Set X` and its universe-lifted preimage
`ULift.down ⁻¹' S` in `ULift.{v, u} X`. -/
private def uliftSubsetHomeo {X : Type u} [TopologicalSpace X] (S : Set X) :
    ↥S ≃ₜ ↥(ULift.down ⁻¹' S : Set (ULift.{v, u} X)) :=
  (Homeomorph.ulift.{v, u} (X := X)).symm.subtype fun _ ↦ Iff.rfl

/-- Transport `a : C(D, Z)` to the universe-lifted pair `(ULift.down ⁻¹' D, ULift.{u, v} Z)`. -/
private def liftedBaseMap {X : Type u} [TopologicalSpace X] {D : Set X}
    {Z : Type v} [TopologicalSpace Z] (a : C(D, Z)) :
    C(↥(ULift.down ⁻¹' D : Set (ULift.{v, u} X)), ULift.{u, v} Z) :=
  (homC Homeomorph.ulift.{u, v}.symm).comp
    (a.comp (homC (uliftSubsetHomeo.{u, v} D).symm))

variable {X : Type u} [TopologicalSpace X] (C : Set X) {D : Set X} [RelCWComplex C D]
  {Z : Type v} [TopologicalSpace Z] (a : C(D, Z))

/-- **Universe-polymorphic adjunction space `Z ∪_a C`.** The adjunction space obtained by gluing a
classical relative CW complex `(C, D)` in `Type u` to an arbitrary topological space `Z` in an
independent universe `Type v` along `a : D → Z`, formed in `TopCat.{max u v}` via
`RelCWComplex.ulift`. -/
def uliftAdjunctionSpace : TopCat.{max u v} :=
  letI := RelCWComplex.ulift.{v, u} C
  relCWAdjunctionSpace (ULift.down ⁻¹' C : Set (ULift.{v, u} X)) (liftedBaseMap a)

/-- The canonical base inclusion `Z → Z ∪_a C` into the universe-polymorphic adjunction space. -/
def uliftAdjunctionInr : C(Z, uliftAdjunctionSpace C a) :=
  letI := RelCWComplex.ulift.{v, u} C
  (pushout.inr (relCWBaseInclusion (ULift.down ⁻¹' C : Set (ULift.{v, u} X)))
    (TopCat.ofHom (liftedBaseMap a))).hom.comp (homC Homeomorph.ulift.{u, v}.symm)

/-- The canonical complex-side map `C → Z ∪_a C` into the universe-polymorphic adjunction space. -/
def uliftAdjunctionInl : C(C, uliftAdjunctionSpace C a) :=
  letI := RelCWComplex.ulift.{v, u} C
  (pushout.inl (relCWBaseInclusion (ULift.down ⁻¹' C : Set (ULift.{v, u} X)))
    (TopCat.ofHom (liftedBaseMap a))).hom.comp (homC (uliftSubsetHomeo.{u, v} C))

private lemma uliftAdjunctionInl_apply (x : C) :
    uliftAdjunctionInl C a x =
      letI := RelCWComplex.ulift.{v, u} C
      pushout.inl (relCWBaseInclusion (ULift.down ⁻¹' C : Set (ULift.{v, u} X)))
        (TopCat.ofHom (liftedBaseMap a)) (uliftSubsetHomeo.{u, v} C x) :=
  rfl

/-- On the base `D`, `uliftAdjunctionInl` agrees with `uliftAdjunctionInr ∘ a`. -/
theorem uliftAdjunctionInl_eq_inr (d : D) :
    uliftAdjunctionInl C a ⟨d.val, base_subset_complex d.property⟩ =
      uliftAdjunctionInr C a (a d) :=
  letI := RelCWComplex.ulift.{v, u} C
  ConcreteCategory.congr_hom (pushout.condition
    (f := relCWBaseInclusion (ULift.down ⁻¹' C : Set (ULift.{v, u} X)))
    (g := TopCat.ofHom (liftedBaseMap a))) (uliftSubsetHomeo.{u, v} D d)

private def uliftDescLeft {W : Type w} [TopologicalSpace W] (f : C(C, W)) :
    TopCat.uliftFunctor.{w, max u v}.obj
        (TopCat.of ↥(ULift.down ⁻¹' C : Set (ULift.{v, u} X))) ⟶
      TopCat.of (ULift.{max u v, w} W) :=
  TopCat.ofHom <| (homC Homeomorph.ulift.{max u v, w}.symm).comp
    (f.comp ((homC (uliftSubsetHomeo.{u, v} C).symm).comp
      (homC (TopCat.uliftFunctorObjHomeo.{w} _).symm)))

private lemma uliftDescLeft_apply {W : Type w} [TopologicalSpace W] (f : C(C, W))
    (x : TopCat.uliftFunctor.{w, max u v}.obj
      (TopCat.of ↥(ULift.down ⁻¹' C : Set (ULift.{v, u} X)))) :
    uliftDescLeft.{u, v, w} C f x =
      ULift.up (f ((uliftSubsetHomeo.{u, v} C).symm
        ((TopCat.uliftFunctorObjHomeo.{w} _).symm x))) :=
  rfl

private def uliftDescRight {W : Type w} [TopologicalSpace W] (h : C(Z, W)) :
    TopCat.uliftFunctor.{w, max u v}.obj (TopCat.of (ULift.{u, v} Z)) ⟶
      TopCat.of (ULift.{max u v, w} W) :=
  TopCat.ofHom <| (homC Homeomorph.ulift.{max u v, w}.symm).comp
    (h.comp ((homC Homeomorph.ulift.{u, v}).comp (homC (TopCat.uliftFunctorObjHomeo.{w} _).symm)))

private lemma uliftDescRight_apply {W : Type w} [TopologicalSpace W] (h : C(Z, W))
    (x : TopCat.uliftFunctor.{w, max u v}.obj (TopCat.of (ULift.{u, v} Z))) :
    uliftDescRight.{u, v, w} h x =
      ULift.up (h (Homeomorph.ulift.{u, v} ((TopCat.uliftFunctorObjHomeo.{w} _).symm x))) :=
  rfl

private lemma uliftDesc_compat {W : Type w} [TopologicalSpace W]
    (f : C(C, W)) (h : C(Z, W))
    (hfa : ∀ d : D, f ⟨d.val, base_subset_complex d.property⟩ = h (a d)) :
    letI := RelCWComplex.ulift.{v, u} C
    TopCat.uliftFunctor.{w, max u v}.map
        (relCWBaseInclusion (ULift.down ⁻¹' C : Set (ULift.{v, u} X))) ≫
        uliftDescLeft.{u, v, w} C f =
      TopCat.uliftFunctor.{w, max u v}.map (TopCat.ofHom (liftedBaseMap a)) ≫
        uliftDescRight.{u, v, w} h := by
  let _ := RelCWComplex.ulift.{v, u} C
  ext x
  let y := (TopCat.uliftFunctorObjHomeo.{w} _).symm x
  have h1 := TopCat.uliftFunctorObjHomeo_symm_naturality_apply.{w}
    (relCWBaseInclusion (ULift.down ⁻¹' C : Set (ULift.{v, u} X))) x
  have h2 := TopCat.uliftFunctorObjHomeo_symm_naturality_apply.{w}
    (TopCat.ofHom (liftedBaseMap a)) x
  have hL :
      (TopCat.uliftFunctor.{w, max u v}.map (relCWBaseInclusion _) ≫
          uliftDescLeft.{u, v, w} C f) x =
        ULift.up (f ⟨y.val.down, base_subset_complex y.property⟩) := by
    rw [ConcreteCategory.comp_apply, uliftDescLeft_apply]
    exact congrArg (fun p : ↥(ULift.down ⁻¹' C : Set (ULift.{v, u} X)) ↦
      ULift.up (f ((uliftSubsetHomeo.{u, v} C).symm p))) h1
  have hR :
      (TopCat.uliftFunctor.{w, max u v}.map (TopCat.ofHom (liftedBaseMap a)) ≫
          uliftDescRight.{u, v, w} h) x = ULift.up (h (a ⟨y.val.down, y.property⟩)) := by
    rw [ConcreteCategory.comp_apply, uliftDescRight_apply]
    exact congrArg (fun z : ULift.{u, v} Z ↦ ULift.up (h z.down)) h2
  exact congrArg ULift.down
    (hL.trans <| (congrArg ULift.up (hfa ⟨y.val.down, y.property⟩)).trans hR.symm)

/-- **Universal eliminator for `uliftAdjunctionSpace`.** Compatible continuous maps `f : C → W`
and `h : Z → W` into an arbitrary universe `W` descend to a continuous map `Z ∪_a C → W`. -/
def uliftAdjunctionDesc {W : Type w} [TopologicalSpace W]
    (f : C(C, W)) (h : C(Z, W))
    (hfa : ∀ d : D, f ⟨d.val, base_subset_complex d.property⟩ = h (a d)) :
    C(uliftAdjunctionSpace C a, W) :=
  letI := RelCWComplex.ulift.{v, u} C
  let ι := relCWBaseInclusion (ULift.down ⁻¹' C : Set (ULift.{v, u} X))
  let sq := IsPushout.of_hasPushout ι (TopCat.ofHom (liftedBaseMap a))
  let dW := (sq.map TopCat.uliftFunctor.{w, max u v}).desc
    (uliftDescLeft.{u, v, w} C f) (uliftDescRight.{u, v, w} h)
    (uliftDesc_compat.{u, v, w} C a f h hfa)
  let eP := TopCat.uliftFunctorObjHomeo.{w} (pushout ι (TopCat.ofHom (liftedBaseMap a)))
  (homC Homeomorph.ulift.{max u v, w}).comp (dW.hom.comp (homC eP))

/-- Shared evaluation helper for `uliftAdjunctionDesc_inl` and `uliftAdjunctionDesc_inr`. -/
private lemma uliftDescAux_apply {W : Type w} [TopologicalSpace W]
    {P A : TopCat.{u}} (k : A ⟶ P)
    (dW : TopCat.uliftFunctor.{w, u}.obj P ⟶ TopCat.of (ULift.{u, w} W))
    (l : TopCat.uliftFunctor.{w, u}.obj A ⟶ TopCat.of (ULift.{u, w} W))
    (hkl : TopCat.uliftFunctor.{w, u}.map k ≫ dW = l) (y : A) :
    (dW (TopCat.uliftFunctorObjHomeo.{w} P (k y))).down =
      (l (TopCat.uliftFunctorObjHomeo.{w} A y)).down := by
  have hcomp := ConcreteCategory.congr_hom hkl (TopCat.uliftFunctorObjHomeo.{w} A y)
  rw [ConcreteCategory.comp_apply, TopCat.uliftFunctorObjHomeo_naturality_apply.{w} k y] at hcomp
  exact congrArg ULift.down hcomp

@[simp]
theorem uliftAdjunctionDesc_inl {W : Type w} [TopologicalSpace W]
    (f : C(C, W)) (h : C(Z, W))
    (hfa : ∀ d : D, f ⟨d.val, base_subset_complex d.property⟩ = h (a d)) (x : C) :
    uliftAdjunctionDesc C a f h hfa (uliftAdjunctionInl C a x) = f x := by
  let _ := RelCWComplex.ulift.{v, u} C
  let ι := relCWBaseInclusion (ULift.down ⁻¹' C : Set (ULift.{v, u} X))
  let sq := IsPushout.of_hasPushout ι (TopCat.ofHom (liftedBaseMap a))
  have hval := uliftDescAux_apply (pushout.inl ι (TopCat.ofHom (liftedBaseMap a))) _
    (uliftDescLeft.{u, v, w} C f)
    ((sq.map TopCat.uliftFunctor.{w, max u v}).inl_desc (uliftDescLeft.{u, v, w} C f)
      (uliftDescRight.{u, v, w} h) (uliftDesc_compat.{u, v, w} C a f h hfa))
    (uliftSubsetHomeo.{u, v} C x)
  rw [uliftDescLeft_apply, Homeomorph.symm_apply_apply, Homeomorph.symm_apply_apply] at hval
  exact hval

@[simp]
theorem uliftAdjunctionDesc_inr {W : Type w} [TopologicalSpace W]
    (f : C(C, W)) (h : C(Z, W))
    (hfa : ∀ d : D, f ⟨d.val, base_subset_complex d.property⟩ = h (a d)) (z : Z) :
    uliftAdjunctionDesc C a f h hfa (uliftAdjunctionInr C a z) = h z := by
  let _ := RelCWComplex.ulift.{v, u} C
  let ι := relCWBaseInclusion (ULift.down ⁻¹' C : Set (ULift.{v, u} X))
  let sq := IsPushout.of_hasPushout ι (TopCat.ofHom (liftedBaseMap a))
  have hval := uliftDescAux_apply (pushout.inr ι (TopCat.ofHom (liftedBaseMap a))) _
    (uliftDescRight.{u, v, w} h)
    ((sq.map TopCat.uliftFunctor.{w, max u v}).inr_desc (uliftDescLeft.{u, v, w} C f)
      (uliftDescRight.{u, v, w} h) (uliftDesc_compat.{u, v, w} C a f h hfa))
    (ULift.up z)
  rw [uliftDescRight_apply, Homeomorph.symm_apply_apply] at hval
  exact hval

@[simp]
theorem uliftAdjunctionDesc_comp_inl {W : Type w} [TopologicalSpace W]
    (f : C(C, W)) (h : C(Z, W))
    (hfa : ∀ d : D, f ⟨d.val, base_subset_complex d.property⟩ = h (a d)) :
    (uliftAdjunctionDesc C a f h hfa).comp (uliftAdjunctionInl C a) = f :=
  ContinuousMap.ext (uliftAdjunctionDesc_inl C a f h hfa)

@[simp]
theorem uliftAdjunctionDesc_comp_inr {W : Type w} [TopologicalSpace W]
    (f : C(C, W)) (h : C(Z, W))
    (hfa : ∀ d : D, f ⟨d.val, base_subset_complex d.property⟩ = h (a d)) :
    (uliftAdjunctionDesc C a f h hfa).comp (uliftAdjunctionInr C a) = h :=
  ContinuousMap.ext (uliftAdjunctionDesc_inr C a f h hfa)

/-- Every point of `uliftAdjunctionSpace` lies in the image of `C` or of `Z`. -/
theorem exists_uliftAdjunctionInl_or_inr (p : uliftAdjunctionSpace C a) :
    (∃ x : C, uliftAdjunctionInl C a x = p) ∨ ∃ z : Z, uliftAdjunctionInr C a z = p := by
  let _ := RelCWComplex.ulift.{v, u} C
  dsimp only [uliftAdjunctionSpace] at p
  rcases Types.eq_or_eq_of_isPushout ((forget TopCat).map_isPushout (IsPushout.of_hasPushout
    (relCWBaseInclusion (ULift.down ⁻¹' C : Set (ULift.{v, u} X)))
    (TopCat.ofHom (liftedBaseMap a)))) p with ⟨⟨⟨x⟩, hx⟩, rfl⟩ | ⟨⟨z⟩, rfl⟩
  · exact Or.inl ⟨⟨x, hx⟩, rfl⟩
  · exact Or.inr ⟨z, rfl⟩

/-- Induction principle on points of `uliftAdjunctionSpace` by splitting into the images of `C` and
`Z`. -/
@[elab_as_elim]
theorem uliftAdjunctionSpace_induction_on
    {P : uliftAdjunctionSpace C a → Prop} (p : uliftAdjunctionSpace C a)
    (hl : ∀ x : C, P (uliftAdjunctionInl C a x))
    (hr : ∀ z : Z, P (uliftAdjunctionInr C a z)) : P p := by
  rcases exists_uliftAdjunctionInl_or_inr C a p with ⟨x, rfl⟩ | ⟨z, rfl⟩
  · exact hl x
  · exact hr z

/-- The ranges of `uliftAdjunctionInl` and `uliftAdjunctionInr` cover `uliftAdjunctionSpace`. -/
theorem range_uliftAdjunctionInl_union_range_inr :
    range (uliftAdjunctionInl C a) ∪ range (uliftAdjunctionInr C a) = univ :=
  eq_univ_of_forall fun p ↦ exists_uliftAdjunctionInl_or_inr C a p

/-- Two continuous maps out of `uliftAdjunctionSpace` agree as soon as they agree on the images of
`C` and `Z`. -/
theorem uliftAdjunctionSpace_continuousMap_ext {W : Type w} [TopologicalSpace W]
    {f₁ f₂ : C(uliftAdjunctionSpace C a, W)}
    (hl : ∀ x, f₁ (uliftAdjunctionInl C a x) = f₂ (uliftAdjunctionInl C a x))
    (hr : ∀ z, f₁ (uliftAdjunctionInr C a z) = f₂ (uliftAdjunctionInr C a z)) : f₁ = f₂ :=
  ContinuousMap.ext fun p ↦ uliftAdjunctionSpace_induction_on C a p hl hr

/-- A subset of `uliftAdjunctionSpace` is closed if and only if its preimages in `C` and `Z` are
both closed. -/
theorem isClosed_iff_uliftAdjunctionSpace (s : Set (uliftAdjunctionSpace C a)) :
    IsClosed s ↔
      IsClosed (uliftAdjunctionInl C a ⁻¹' s) ∧ IsClosed (uliftAdjunctionInr C a ⁻¹' s) := by
  let _ := RelCWComplex.ulift.{v, u} C
  let sq := IsPushout.of_hasPushout
    (relCWBaseInclusion (ULift.down ⁻¹' C : Set (ULift.{v, u} X)))
    (TopCat.ofHom (liftedBaseMap a))
  refine (TauCeti.TopCat.isClosed_iff_of_isPushout sq s).trans ?_
  rw [← (uliftSubsetHomeo.{u, v} C).isClosed_preimage,
    ← (Homeomorph.ulift.{u, v} (X := Z)).symm.isClosed_preimage]
  rfl

/-- The canonical map `Z → uliftAdjunctionSpace C a` is a closed embedding. -/
theorem isClosedEmbedding_uliftAdjunctionInr [T2Space X] :
    IsClosedEmbedding (uliftAdjunctionInr C a) :=
  letI := RelCWComplex.ulift.{v, u} C
  (isClosedEmbedding_pushout_inr_relCWBaseInclusion
    (C := (ULift.down ⁻¹' C : Set (ULift.{v, u} X))) (liftedBaseMap a)).comp
    (Homeomorph.ulift.{u, v} (X := Z)).symm.isClosedEmbedding

/-- When `X` and `Z` are Hausdorff, `uliftAdjunctionSpace C a` is Hausdorff. -/
instance t2Space_uliftAdjunctionSpace [T2Space X] [T2Space Z] :
    T2Space (uliftAdjunctionSpace C a) :=
  letI := RelCWComplex.ulift.{v, u} C
  t2Space_relCWAdjunctionSpace (C := (ULift.down ⁻¹' C : Set (ULift.{v, u} X)))
    (liftedBaseMap a)

private lemma range_uliftAdjunctionInr :
    letI := RelCWComplex.ulift.{v, u} C
    range (pushout.inr (relCWBaseInclusion (ULift.down ⁻¹' C : Set (ULift.{v, u} X)))
        (TopCat.ofHom (liftedBaseMap a))) = range (uliftAdjunctionInr C a) := by
  ext p
  simp only [mem_range, uliftAdjunctionInr]
  exact ⟨fun ⟨⟨z⟩, hz⟩ ↦ ⟨z, hz⟩, fun ⟨z, hz⟩ ↦ ⟨⟨z⟩, hz⟩⟩

/-- **Relative CW structure on the universe-polymorphic adjunction space.**
`uliftAdjunctionSpace C a` is a classical relative CW complex relative to
`range (uliftAdjunctionInr C a)`, with the cells of `C`. -/
@[instance_reducible]
def uliftAdjunctionCWModel [T2Space X] :
    RelCWComplex (univ : Set (uliftAdjunctionSpace C a)) (range (uliftAdjunctionInr C a)) :=
  letI := RelCWComplex.ulift.{v, u} C
  (relativeCWPushout (ULift.down ⁻¹' C : Set (ULift.{v, u} X)) (liftedBaseMap a)).copy univ
    (range (uliftAdjunctionInr C a)) rfl (range_uliftAdjunctionInr C a)

/-- The `n`-cells of `uliftAdjunctionCWModel` correspond bijectively to the `n`-cells of `C`. -/
def uliftAdjunctionCellEquiv [T2Space X] (n : ℕ) :
    letI := uliftAdjunctionCWModel C a
    cell (univ : Set (uliftAdjunctionSpace C a)) n ≃ cell C n :=
  letI := RelCWComplex.ulift.{v, u} C
  (((relativeCWPushout (ULift.down ⁻¹' C : Set (ULift.{v, u} X))
    (liftedBaseMap a)).copyCellEquiv univ (range (uliftAdjunctionInr C a)) rfl
      (range_uliftAdjunctionInr C a) n).trans
    (relativeCWPushoutCellEquiv (ULift.down ⁻¹' C : Set (ULift.{v, u} X))
      (liftedBaseMap a) n)).trans (RelCWComplex.uliftCellEquiv.{v, u} C n)

/-- Each characteristic map of `uliftAdjunctionCWModel` is the characteristic map of the
corresponding cell of `C` followed by `uliftAdjunctionInl`. -/
theorem uliftAdjunctionCWModel_map_apply [T2Space X] (n : ℕ)
    (i : letI := uliftAdjunctionCWModel C a; cell (univ : Set (uliftAdjunctionSpace C a)) n)
    {x : Fin n → ℝ} (hx : x ∈ closedBall 0 1) :
    letI := uliftAdjunctionCWModel C a
    map n i x = uliftAdjunctionInl C a ⟨map n (uliftAdjunctionCellEquiv C a n i) x,
      closedCell_subset_complex n _ (mem_image_of_mem _ hx)⟩ := by
  let _ := RelCWComplex.ulift.{v, u} C
  let P := relativeCWPushout (ULift.down ⁻¹' C : Set (ULift.{v, u} X)) (liftedBaseMap a)
  have hcopy := P.map_copy univ (range (uliftAdjunctionInr C a)) rfl
    (range_uliftAdjunctionInr C a) n i
  refine (congrArg (fun f : PartialEquiv _ _ ↦ f x) hcopy).trans ?_
  refine (relativeCWPushout_map_apply (C := (ULift.down ⁻¹' C : Set (ULift.{v, u} X)))
    (a := liftedBaseMap a) n _ ⟨x, hx⟩).trans ?_
  rw [uliftAdjunctionInl_apply]
  congr 1
  exact Subtype.ext (congrFun (RelCWComplex.coe_map_ulift.{v, u} C n _) x)

/-- The image of a subset of the closed unit ball under a characteristic map of
`uliftAdjunctionCWModel` is the image under `uliftAdjunctionInl` of the corresponding image in
`C`. -/
theorem image_map_uliftAdjunctionCWModel [T2Space X] (n : ℕ)
    (i : letI := uliftAdjunctionCWModel C a; cell (univ : Set (uliftAdjunctionSpace C a)) n)
    (S : Set (Fin n → ℝ)) (hS : S ⊆ closedBall 0 1) :
    letI := uliftAdjunctionCWModel C a
    map n i '' S =
      uliftAdjunctionInl C a ''
        (Subtype.val ⁻¹' (map n (uliftAdjunctionCellEquiv C a n i) '' S)) := by
  let _ := uliftAdjunctionCWModel C a
  ext p
  simp only [mem_image, mem_preimage]
  refine ⟨fun ⟨x, hx, hp⟩ ↦ ?_, fun ⟨y, ⟨x, hx, hxy⟩, hp⟩ ↦ ?_⟩
  · exact ⟨⟨_, closedCell_subset_complex n _ (mem_image_of_mem _ (hS hx))⟩,
      ⟨x, hx, rfl⟩, hp ▸ (uliftAdjunctionCWModel_map_apply C a n i (hS hx)).symm⟩
  · refine ⟨x, hx, ?_⟩
    rw [← hp, uliftAdjunctionCWModel_map_apply C a n i (hS hx)]
    exact congrArg (uliftAdjunctionInl C a) (Subtype.ext hxy)

@[simp]
theorem openCell_uliftAdjunctionCWModel [T2Space X] (n : ℕ)
    (i : letI := uliftAdjunctionCWModel C a; cell (univ : Set (uliftAdjunctionSpace C a)) n) :
    letI := uliftAdjunctionCWModel C a
    openCell n i = uliftAdjunctionInl C a ''
      (Subtype.val ⁻¹' openCell n (uliftAdjunctionCellEquiv C a n i)) :=
  image_map_uliftAdjunctionCWModel C a n i (ball 0 1) ball_subset_closedBall

@[simp]
theorem closedCell_uliftAdjunctionCWModel [T2Space X] (n : ℕ)
    (i : letI := uliftAdjunctionCWModel C a; cell (univ : Set (uliftAdjunctionSpace C a)) n) :
    letI := uliftAdjunctionCWModel C a
    closedCell n i = uliftAdjunctionInl C a ''
      (Subtype.val ⁻¹' closedCell n (uliftAdjunctionCellEquiv C a n i)) :=
  image_map_uliftAdjunctionCWModel C a n i (closedBall 0 1) Subset.rfl

@[simp]
theorem cellFrontier_uliftAdjunctionCWModel [T2Space X] (n : ℕ)
    (i : letI := uliftAdjunctionCWModel C a; cell (univ : Set (uliftAdjunctionSpace C a)) n) :
    letI := uliftAdjunctionCWModel C a
    cellFrontier n i = uliftAdjunctionInl C a ''
      (Subtype.val ⁻¹' cellFrontier n (uliftAdjunctionCellEquiv C a n i)) :=
  image_map_uliftAdjunctionCWModel C a n i (sphere 0 1) sphere_subset_closedBall

/-- `uliftAdjunctionCWModel` is finite-dimensional when `C` is finite-dimensional. -/
theorem finiteDimensional_uliftAdjunctionCWModel [T2Space X]
    [RelCWComplex.FiniteDimensional C] :
    letI := uliftAdjunctionCWModel C a
    RelCWComplex.FiniteDimensional (univ : Set (uliftAdjunctionSpace C a)) :=
  RelCWComplex.finiteDimensional_of_cellEquiv inferInstance (uliftAdjunctionCWModel C a)
    (uliftAdjunctionCellEquiv C a)

/-- `uliftAdjunctionCWModel` has finite type when `C` has finite type. -/
theorem finiteType_uliftAdjunctionCWModel [T2Space X] [RelCWComplex.FiniteType C] :
    letI := uliftAdjunctionCWModel C a
    RelCWComplex.FiniteType (univ : Set (uliftAdjunctionSpace C a)) :=
  RelCWComplex.finiteType_of_cellEquiv inferInstance (uliftAdjunctionCWModel C a)
    (uliftAdjunctionCellEquiv C a)

/-- `uliftAdjunctionCWModel` is finite when `C` is finite. -/
theorem finite_uliftAdjunctionCWModel [T2Space X] [RelCWComplex.Finite C] :
    letI := uliftAdjunctionCWModel C a
    RelCWComplex.Finite (univ : Set (uliftAdjunctionSpace C a)) :=
  RelCWComplex.finite_of_cellEquiv inferInstance (uliftAdjunctionCWModel C a)
    (uliftAdjunctionCellEquiv C a)

private def uliftChangeUnivInvL :
    TopCat.of ↥(ULift.down ⁻¹' C : Set (ULift.{max v w, u} X)) ⟶
      TopCat.of (ULift.{w, max u v} (uliftAdjunctionSpace C a)) :=
  TopCat.ofHom <| (homC Homeomorph.ulift.{w, max u v}.symm).comp
    ((uliftAdjunctionInl C a).comp (homC (uliftSubsetHomeo.{u, max v w} C).symm))

private def uliftChangeUnivInvR :
    TopCat.of (ULift.{max u w, v} Z) ⟶
      TopCat.of (ULift.{w, max u v} (uliftAdjunctionSpace C a)) :=
  TopCat.ofHom <| (homC Homeomorph.ulift.{w, max u v}.symm).comp
    ((uliftAdjunctionInr C a).comp (homC Homeomorph.ulift.{max u w, v}))

private lemma uliftChangeUnivInv_compat
    (b : C(↥(ULift.down ⁻¹' D : Set (ULift.{max v w, u} X)), ULift.{max u w, v} Z))
    (hb : ∀ x, b x = ULift.up (a ((uliftSubsetHomeo.{u, max v w} D).symm x))) :
    letI := RelCWComplex.ulift.{max v w, u} C
    relCWBaseInclusion (ULift.down ⁻¹' C : Set (ULift.{max v w, u} X)) ≫
        uliftChangeUnivInvL.{u, v, w} C a =
      TopCat.ofHom b ≫ uliftChangeUnivInvR.{u, v, w} C a := by
  ext x
  simp only [ConcreteCategory.comp_apply, TopCat.hom_ofHom, ContinuousMap.coe_comp,
    uliftChangeUnivInvL, uliftChangeUnivInvR, ContinuousMap.coe_mk, hb]
  exact uliftAdjunctionInl_eq_inr C a ((uliftSubsetHomeo.{u, max v w} D).symm x)

private def uliftAdjunctionChangeUnivInv
    (b : C(↥(ULift.down ⁻¹' D : Set (ULift.{max v w, u} X)), ULift.{max u w, v} Z))
    (hb : ∀ x, b x = ULift.up (a ((uliftSubsetHomeo.{u, max v w} D).symm x))) :
    letI := RelCWComplex.ulift.{max v w, u} C
    C(relCWAdjunctionSpace (ULift.down ⁻¹' C : Set (ULift.{max v w, u} X)) b,
      uliftAdjunctionSpace C a) :=
  letI := RelCWComplex.ulift.{max v w, u} C
  (homC Homeomorph.ulift.{w, max u v}).comp
    (pushout.desc (uliftChangeUnivInvL.{u, v, w} C a) (uliftChangeUnivInvR.{u, v, w} C a)
      (uliftChangeUnivInv_compat.{u, v, w} C a b hb)).hom

private lemma uliftAdjunctionChangeUnivInv_inl
    (b : C(↥(ULift.down ⁻¹' D : Set (ULift.{max v w, u} X)), ULift.{max u w, v} Z))
    (hb : ∀ x, b x = ULift.up (a ((uliftSubsetHomeo.{u, max v w} D).symm x))) (x : C) :
    letI := RelCWComplex.ulift.{max v w, u} C
    uliftAdjunctionChangeUnivInv.{u, v, w} C a b hb
      (pushout.inl (relCWBaseInclusion (ULift.down ⁻¹' C : Set (ULift.{max v w, u} X)))
        (TopCat.ofHom b) (uliftSubsetHomeo.{u, max v w} C x)) = uliftAdjunctionInl C a x := by
  let _ := RelCWComplex.ulift.{max v w, u} C
  have h := congrArg ULift.down <| ConcreteCategory.congr_hom
    (pushout.inl_desc (uliftChangeUnivInvL.{u, v, w} C a) (uliftChangeUnivInvR.{u, v, w} C a)
      (uliftChangeUnivInv_compat.{u, v, w} C a b hb))
    (uliftSubsetHomeo.{u, max v w} C x)
  exact h.trans (congrArg (uliftAdjunctionInl C a) (Homeomorph.symm_apply_apply _ x))

private lemma uliftAdjunctionChangeUnivInv_inr
    (b : C(↥(ULift.down ⁻¹' D : Set (ULift.{max v w, u} X)), ULift.{max u w, v} Z))
    (hb : ∀ x, b x = ULift.up (a ((uliftSubsetHomeo.{u, max v w} D).symm x))) (z : Z) :
    letI := RelCWComplex.ulift.{max v w, u} C
    uliftAdjunctionChangeUnivInv.{u, v, w} C a b hb
      (pushout.inr (relCWBaseInclusion (ULift.down ⁻¹' C : Set (ULift.{max v w, u} X)))
        (TopCat.ofHom b) (ULift.up z)) = uliftAdjunctionInr C a z := by
  let _ := RelCWComplex.ulift.{max v w, u} C
  exact congrArg ULift.down <| ConcreteCategory.congr_hom
    (pushout.inr_desc (uliftChangeUnivInvL.{u, v, w} C a) (uliftChangeUnivInvR.{u, v, w} C a)
      (uliftChangeUnivInv_compat.{u, v, w} C a b hb)) (ULift.up z)

/-- **Universe-change comparison for `uliftAdjunctionSpace`.** The adjunction space
`uliftAdjunctionSpace C a` in `Type (max u v)` is homeomorphic (compatibly with the inclusions of
`Z`) to the same-universe adjunction space `relCWAdjunctionSpace` formed in `Type (max u v w)`. -/
theorem exists_homeomorph_uliftAdjunctionSpace_ulift
    (b : C(↥(ULift.down ⁻¹' D : Set (ULift.{max v w, u} X)), ULift.{max u w, v} Z))
    (hb : ∀ x, b x = ULift.up (a ⟨x.val.down, x.property⟩)) :
    letI := RelCWComplex.ulift.{max v w, u} C
    ∃ Φ : uliftAdjunctionSpace.{u, v} C a ≃ₜ
        relCWAdjunctionSpace (ULift.down ⁻¹' C : Set (ULift.{max v w, u} X)) b,
      (∀ z, Φ (uliftAdjunctionInr C a z) =
        pushout.inr (relCWBaseInclusion (ULift.down ⁻¹' C : Set (ULift.{max v w, u} X)))
          (TopCat.ofHom b) (ULift.up z)) ∧
      ∀ z, Φ.symm (pushout.inr
          (relCWBaseInclusion (ULift.down ⁻¹' C : Set (ULift.{max v w, u} X)))
          (TopCat.ofHom b) (ULift.up z)) = uliftAdjunctionInr C a z := by
  let _ := RelCWComplex.ulift.{max v w, u} C
  let ι := relCWBaseInclusion (ULift.down ⁻¹' C : Set (ULift.{max v w, u} X))
  -- Stage 1: build the forward map from `uliftAdjunctionSpace` into the larger-universe pushout.
  let inlBig : C(C, relCWAdjunctionSpace (ULift.down ⁻¹' C : Set (ULift.{max v w, u} X)) b) :=
    (pushout.inl ι (TopCat.ofHom b)).hom.comp (homC (uliftSubsetHomeo.{u, max v w} C))
  let inrBig : C(Z, relCWAdjunctionSpace (ULift.down ⁻¹' C : Set (ULift.{max v w, u} X)) b) :=
    (pushout.inr ι (TopCat.ofHom b)).hom.comp (homC Homeomorph.ulift.{max u w, v}.symm)
  have hcompat :
      ∀ d : D, inlBig ⟨d.val, base_subset_complex d.property⟩ = inrBig (a d) := fun d ↦ by
    have hc := ConcreteCategory.congr_hom (pushout.condition (f := ι) (g := TopCat.ofHom b))
      (uliftSubsetHomeo.{u, max v w} D d)
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hc
    exact hc.trans
      (congrArg (pushout.inr ι (TopCat.ofHom b)) (hb (uliftSubsetHomeo.{u, max v w} D d)))
  let toF := uliftAdjunctionDesc C a inlBig inrBig hcompat
  -- Stage 2: use the extracted inverse map `uliftAdjunctionChangeUnivInv` and verify inverses.
  let invF := uliftAdjunctionChangeUnivInv.{u, v, w} C a b hb
  refine ⟨{
    toFun := toF, invFun := invF
    left_inv := fun p ↦ uliftAdjunctionSpace_induction_on (P := fun q ↦ invF (toF q) = q) C a p
      (fun x ↦ (congrArg invF (uliftAdjunctionDesc_inl C a inlBig inrBig hcompat x)).trans
        (uliftAdjunctionChangeUnivInv_inl C a b hb x))
      (fun z ↦ (congrArg invF (uliftAdjunctionDesc_inr C a inlBig inrBig hcompat z)).trans
        (uliftAdjunctionChangeUnivInv_inr C a b hb z))
    right_inv := fun q ↦ by
      rcases Types.eq_or_eq_of_isPushout
        ((forget TopCat).map_isPushout (IsPushout.of_hasPushout ι (TopCat.ofHom b))) q with
        ⟨⟨⟨x⟩, hx⟩, rfl⟩ | ⟨⟨z⟩, rfl⟩
      · exact (congrArg toF (uliftAdjunctionChangeUnivInv_inl C a b hb ⟨x, hx⟩)).trans
          (uliftAdjunctionDesc_inl C a inlBig inrBig hcompat ⟨x, hx⟩)
      · exact (congrArg toF (uliftAdjunctionChangeUnivInv_inr C a b hb z)).trans
          (uliftAdjunctionDesc_inr C a inlBig inrBig hcompat z)
    continuous_toFun := toF.continuous, continuous_invFun := invF.continuous },
    fun z ↦ uliftAdjunctionDesc_inr C a inlBig inrBig hcompat z,
    uliftAdjunctionChangeUnivInv_inr C a b hb⟩

/-- **Base homotopy invariance of `uliftAdjunctionSpace`.** A homotopy equivalence `e : Z ≃ₕ Z'`
(with `Z` and `Z'` in independent universes) induces a homotopy equivalence
`uliftAdjunctionSpace C a ≃ₕ uliftAdjunctionSpace C (e ∘ a)` compatible with
`uliftAdjunctionInr`. -/
theorem exists_homotopyEquiv_uliftAdjunctionSpace [T2Space X]
    {Z' : Type w} [TopologicalSpace Z'] (e : Z ≃ₕ Z') :
    ∃ H : uliftAdjunctionSpace.{u, v} C a ≃ₕ
        uliftAdjunctionSpace.{u, w} C (e.toFun.comp a),
      (∀ z, H (uliftAdjunctionInr C a z) = uliftAdjunctionInr C (e.toFun.comp a) (e z)) ∧
      ∀ z', H.symm (uliftAdjunctionInr C (e.toFun.comp a) z') =
        uliftAdjunctionInr C a (e.symm z') := by
  let _ := RelCWComplex.ulift.{max v w, u} C
  let b : C(↥(ULift.down ⁻¹' D : Set (ULift.{max v w, u} X)), ULift.{max u w, v} Z) :=
    (homC Homeomorph.ulift.{max u w, v}.symm).comp
      (a.comp (homC (uliftSubsetHomeo.{u, max v w} D).symm))
  have hb : ∀ x : ↥(ULift.down ⁻¹' D : Set (ULift.{max v w, u} X)),
      b x = ULift.up (a ⟨x.val.down, x.property⟩) := fun _ ↦ rfl
  have heb : ∀ x : ↥(ULift.down ⁻¹' D : Set (ULift.{max v w, u} X)),
      ((e.uliftCongr.{max u w, max u v}).toFun.comp b) x =
        ULift.up ((e.toFun.comp a) ⟨x.val.down, x.property⟩) :=
    fun x ↦ e.uliftCongr_apply.{max u w, max u v} _
  obtain ⟨Hw, hHw, hHwsymm⟩ :=
    (e.uliftCongr.{max u w, max u v}).exists_homotopyEquiv_relCWAdjunctionSpace
      (ULift.down ⁻¹' C : Set (ULift.{max v w, u} X)) b
  obtain ⟨Φ₁, hΦ₁, hΦ₁s⟩ :=
    exists_homeomorph_uliftAdjunctionSpace_ulift.{u, v, w} C a b hb
  obtain ⟨Φ₂, hΦ₂, hΦ₂s⟩ := exists_homeomorph_uliftAdjunctionSpace_ulift.{u, w, v} C
    (e.toFun.comp a) ((e.uliftCongr.{max u w, max u v}).toFun.comp b) heb
  refine ⟨(Φ₁.toHomotopyEquiv.trans Hw).trans Φ₂.symm.toHomotopyEquiv,
    fun z ↦ ?_, fun z' ↦ ?_⟩
  · simp only [ContinuousMap.HomotopyEquiv.trans_apply, Homeomorph.coe_toHomotopyEquiv,
      hΦ₁, hHw, ContinuousMap.HomotopyEquiv.uliftCongr_apply, hΦ₂s]
  · simp only [ContinuousMap.HomotopyEquiv.trans_symm_apply, ← Homeomorph.symm_toHomotopyEquiv,
      Homeomorph.symm_symm, Homeomorph.coe_toHomotopyEquiv,
      hΦ₂, hHwsymm, ContinuousMap.HomotopyEquiv.uliftCongr_symm_apply, hΦ₁s]

end ULiftAdjunction

end TauCeti
