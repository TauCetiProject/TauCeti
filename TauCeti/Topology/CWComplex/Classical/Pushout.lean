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
public import TauCeti.Topology.CWComplex.Classical.RelativeCWComplex

/-!
# Gluing a relative CW complex to a space

Let `C` be a classical relative CW complex with base `D` in a Hausdorff space, and let
`a : D → Z` be a continuous map to a space `Z`. The adjunction space `Z ∪_a C`
(`TauCeti.relCWAdjunctionSpace`) is the pushout in `TopCat` of the inclusion `D → C` and `a`, with
its quotient topology. This file shows:

* the map `Z → Z ∪_a C` is a closed embedding
  (`TauCeti.isClosedEmbedding_pushout_inr_relCWBaseInclusion`);
* `Z ∪_a C` is Hausdorff when `Z` is (`TauCeti.t2Space_relCWAdjunctionSpace`);
* `Z ∪_a C` is a classical relative CW complex relative to the image of `Z`
  (`TauCeti.relativeCWPushout`), whose `n`-cells are the `n`-cells of `C`
  (`TauCeti.relativeCWPushoutCellEquiv`) and whose characteristic maps are those of `C` followed
  by the map `C → Z ∪_a C` (`TauCeti.relativeCWPushout_map_apply`).

The space `Z` needs no CW structure. The proof passes through the categorical relative CW
complexes of Mathlib: `C` is a categorical relative CW complex on the inclusion of `D`
(`TauCeti.toRelativeCWComplex`), its cobase change along `a` is a categorical relative CW complex
with the same cells (`HomotopicalAlgebra.RelativeCellComplex.pushout`), and categorical relative
CW complexes are closed embeddings, are Hausdorff over a Hausdorff base, and carry classical
structures (`TopCat.RelativeCWComplex.toRelCWComplex`).

These are the cell attachments of Morse theory and of cellular approximation: attaching cells to a
space along maps of their boundary spheres keeps the cells and their characteristic maps.

## Main definitions

* `TauCeti.relCWAdjunctionSpace`: the adjunction space `Z ∪_a C`.
* `TauCeti.relativeCWPushout`: the classical relative CW structure on `Z ∪_a C` relative to `Z`.
* `TauCeti.relativeCWPushoutCellEquiv`: its `n`-cells are the `n`-cells of `C`.

## Main results

* `TauCeti.isClosedEmbedding_pushout_inr_relCWBaseInclusion`: `Z → Z ∪_a C` is a closed embedding.
* `TauCeti.t2Space_relCWAdjunctionSpace`: `Z ∪_a C` is Hausdorff when `Z` is.
* `TauCeti.relativeCWPushout_map_apply`: the characteristic maps of `Z ∪_a C` are those of `C`,
  followed by `C → Z ∪_a C`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Chapter 0 and the Appendix.
* R. Fritsch and R. Piccinini, *Cellular Structures in Topology*, Cambridge University Press,
  1990, Chapter 2.
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

variable (C) in
/-- The `n`-cells of `Z ∪_a C` are the `n`-cells of `C`. -/
def relativeCWPushoutCellEquiv (n : ℕ) :
    letI := relativeCWPushout C a
    cell (univ : Set (relCWAdjunctionSpace C a)) n ≃ cell C n :=
  (relCWAdjunctionSpaceRelativeCWComplex C a).toRelCWComplexCellEquiv n

/-- The characteristic map of an `n`-cell of `Z ∪_a C` is the characteristic map of the
corresponding cell of `C`, followed by the map `C → Z ∪_a C`. -/
theorem relativeCWPushout_map_apply (n : ℕ)
    (i : letI := relativeCWPushout C a
      cell (univ : Set (relCWAdjunctionSpace C a)) n)
    (x : closedBall (0 : Fin n → ℝ) 1) :
    letI := relativeCWPushout C a
    map n i x = pushout.inl (relCWBaseInclusion C) (TopCat.ofHom a)
      ⟨map n (relativeCWPushoutCellEquiv C a n i) x,
        mem_of_subset_of_mem (closedCell_subset_complex n _) (mem_image_of_mem _ x.2)⟩ := by
  rw [TopCat.RelativeCWComplex.toRelCWComplex_map_apply]
  refine (ConcreteCategory.congr_hom ((toRelativeCWComplex C).pushout_cells_ι (TopCat.ofHom a) n
    (not_isMax n) (relativeCWPushoutCellEquiv C a n i)) _).trans ?_
  rw [ConcreteCategory.comp_apply]
  congr 1
  apply Subtype.ext
  rw [coe_toRelativeCWComplex_cells_ι_apply, Homeomorph.apply_symm_apply]

end TauCeti
