/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.Homology
public import TauCeti.AlgebraicTopology.Cellular.Incidence
public import TauCeti.Topology.CWComplex.Abstract.AttachCells
public import TauCeti.Topology.CWComplex.Abstract.CellAttachment

/-!
# The homology of a cell attachment in the dimension of the cells and the one below

Let `Y` be obtained from a Hausdorff space `X` by attaching `(n + 1)`-cells along maps
`φ i : Sⁿ → X`, and let `f : X → Y` be the inclusion. With coefficients in a ring `R`, the map
`f_* : Hₙ(X; R) → Hₙ(Y; R)` is surjective
(`TauCeti.surjective_singularHomologyMap_cellAttachmentIncl`), and its kernel is the submodule
spanned by the classes `(φ i)_*[Sⁿ]` of the attaching spheres
(`TauCeti.ker_singularHomologyMap_cellAttachmentIncl`). Here `[Sⁿ]` is the standard generator of
the reduced homology of the sphere, included in its ordinary homology. So
`Hₙ(Y; R) ≅ Hₙ(X; R) ⧸ ⟨(φ i)_*[Sⁿ]⟩`: attaching cells kills exactly the homology classes of their
attaching spheres.

In the dimension `n + 1` of the cells, if `Hₙ₊₁(X; R)` and `Hₙ(X; R)` vanish, then `Hₙ₊₁(Y; R)` is
free on the attached cells (`TauCeti.nonempty_singularHomology_cellAttachment_iso_sigma`).

The proof reads the attachment as a relative CW complex whose cells all have dimension `n + 1`.
Its `n`-skeleton is `X` and its `(n + 1)`-skeleton is `Y`, so the long exact sequence of the pair
`(Y, X)` is the one of the skeletal pair. The relative homology `Hₙ(Y, X)` vanishes, and the image
of the connecting morphism `Hₙ₊₁(Y, X) → Hₙ(X)` is spanned by the attaching spheres
(`TauCeti.range_skeletonPairδ`). In degree `n + 1`, the same sequence identifies `Hₙ₊₁(Y)` with
the relative homology `Hₙ₊₁(Y, X)`, the cellular chain group of the cells.

## Main results

* `TauCeti.surjective_singularHomologyMap_cellAttachmentIncl`: `Hₙ(X) → Hₙ(Y)` is onto.
* `TauCeti.ker_singularHomologyMap_cellAttachmentIncl`: its kernel is spanned by the classes of
  the attaching spheres.
* `TauCeti.nonempty_singularHomology_cellAttachment_iso_sigma`: if `Hₙ₊₁(X)` and `Hₙ(X)` vanish,
  `Hₙ₊₁(Y)` is free on the cells.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2, Lemma 2.34 and the cellular boundary formula.
-/

public section

noncomputable section

open CategoryTheory Limits Topology Topology.RelCWComplex HomotopicalAlgebra Set

universe w

namespace TauCeti

variable {X : TopCat.{w}} [T2Space X] {ι : Type w} {n : ℕ}
  (φ : ι → (TopCat.diskBoundary.{w} (n + 1) ⟶ X)) (R : Type w) [Ring R]

namespace CellAttachment

/-! ### The cell attachment as a skeletal pair -/

/-- The classical relative CW structure of a cell attachment, relative to the old space. -/
@[instance_reducible]
private def relCWComplex :
    RelCWComplex (univ : Set (cellAttachment φ)) (range (cellAttachmentIncl φ)) :=
  (cellAttachmentAttachCells φ).toRelativeCWComplex.toRelCWComplex

attribute [local instance] relCWComplex

/-- The `n`-skeleton of the cell attachment is the old space. -/
private lemma skeletonLT_eq_range :
    (skeletonLT (univ : Set (cellAttachment φ)) ((n + 1 : ℕ) : ℕ∞) : Set (cellAttachment φ)) =
      range (cellAttachmentIncl φ) :=
  (cellAttachmentAttachCells φ).skeletonLT_toRelCWComplex le_rfl

/-- The `(n + 1)`-skeleton of the cell attachment is the whole space. -/
private lemma skeletonLT_eq_univ :
    (skeletonLT (univ : Set (cellAttachment φ)) ((n + 2 : ℕ) : ℕ∞) : Set (cellAttachment φ)) =
      univ :=
  skeletonLT_eq_complex_of_isEmpty_cell _ (n + 2) fun _ hm ↦
    (cellAttachmentAttachCells φ).isEmpty_cell_toRelCWComplex (by omega)

/-- The old space is homeomorphic to the `n`-skeleton of the cell attachment, through the
inclusion. -/
private def toSkeletonIso : X ≅ skeletonObj (univ : Set (cellAttachment φ)) (n + 1) :=
  TopCat.isoOfHomeo ((isClosedEmbedding_cellAttachmentIncl φ).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (skeletonLT_eq_range φ).symm))

private lemma coe_toSkeletonIso_hom_apply (x : X) :
    ((toSkeletonIso φ).hom x : cellAttachment φ) = cellAttachmentIncl φ x :=
  (rfl)

/-- The `(n + 1)`-skeleton of the cell attachment is homeomorphic to the whole space, through the
inclusion. -/
private def skeletonIso : skeletonObj (univ : Set (cellAttachment φ)) (n + 2) ≅ cellAttachment φ :=
  TopCat.isoOfHomeo ((Homeomorph.setCongr (skeletonLT_eq_univ φ)).trans (Homeomorph.Set.univ _))

/-- Through the two identifications, the inclusion of the `n`-skeleton into the `(n + 1)`-skeleton
is the inclusion of the old space. -/
@[reassoc]
private lemma toSkeletonIso_hom_comp_map_comp_skeletonIso_hom :
    (toSkeletonIso φ).hom ≫ (skeletonPair (univ : Set (cellAttachment φ)) (n + 1)).map ≫
      (skeletonIso φ).hom = cellAttachmentIncl φ :=
  (rfl)

/-- The `(n + 1)`-cells of the classical structure are the attached cells. -/
private def cellEquiv : cell (univ : Set (cellAttachment φ)) (n + 1) ≃ ι :=
  (cellAttachmentAttachCells φ).cellToRelCWComplexEquiv

/-- The attaching map of an `(n + 1)`-cell of the classical structure is the prescribed attaching
map, followed by the identification of the old space with the `n`-skeleton. -/
private lemma cellAttachingMap_eq (j : cell (univ : Set (cellAttachment φ)) (n + 1)) :
    cellAttachingMap j = φ (cellEquiv φ j) ≫ (toSkeletonIso φ).hom := by
  ext z
  obtain ⟨i, rfl⟩ := (cellEquiv φ).symm.surjective j
  rw [coe_cellAttachingMap_apply, Equiv.apply_symm_apply, ConcreteCategory.comp_apply,
    coe_toSkeletonIso_hom_apply]
  -- The cells of `cellAttachmentAttachCells φ` are indexed by `ι` by definition, which the
  -- characteristic-map formula states with the index type of the `AttachCells` structure.
  refine ((cellAttachmentAttachCells φ).map_cellToRelCWComplexEquiv_symm i _).trans ?_
  rw [Homeomorph.symm_apply_apply, cellAttachmentAttachCells_cell]
  exact (ConcreteCategory.congr_hom (cellAttachment_boundary φ i) z).symm

end CellAttachment

/-! ### Homology in the dimension below the cells -/

open AlgebraicTopology CellAttachment

attribute [local instance] CellAttachment.relCWComplex

/-- **Attaching `(n + 1)`-cells is onto on `Hₙ`.** The inclusion `X → Y` of a Hausdorff space into
the space obtained by attaching `(n + 1)`-cells induces a surjection on `Hₙ(-; R)`. -/
theorem surjective_singularHomologyMap_cellAttachmentIncl :
    Function.Surjective
      (((singularHomologyFunctor (ModuleCat.{w} R) n).obj (ModuleCat.of R R)).map
        (cellAttachmentIncl φ)).hom := by
  let H := (singularHomologyFunctor (ModuleCat.{w} R) n).obj (ModuleCat.of R R)
  -- The relative homology `Hₙ(Y, X)` of the skeletal pair vanishes.
  have : Epi (H.map (skeletonPair (univ : Set (cellAttachment φ)) (n + 1)).map) :=
    TopPair.epi_homologyMap_map_of_isZero _ _
      (isZero_singularHomology_skeletonPair_of_ne _ _ (by omega))
  rw [← toSkeletonIso_hom_comp_map_comp_skeletonIso_hom]
  -- The skeletal pair presents the `n`- and `(n + 1)`-skeleta as `TopPair.snd` and `TopPair.fst`,
  -- equal to `skeletonObj` only up to unfolding, so `erw` is needed to split the composite.
  erw [Functor.map_comp, Functor.map_comp]
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.coe_comp, LinearMap.coe_comp]
  exact (H.mapIso (skeletonIso φ)).toLinearEquiv.surjective.comp
    (((ModuleCat.epi_iff_surjective _).1 this).comp
      (H.mapIso (toSkeletonIso φ)).toLinearEquiv.surjective)

/-- **Attaching `(n + 1)`-cells kills exactly the attaching spheres in `Hₙ`.** The kernel of the
map `Hₙ(X; R) → Hₙ(Y; R)` induced by attaching `(n + 1)`-cells along the maps `φ i` to a
Hausdorff space `X` is the submodule spanned by the images `(φ i)_*[Sⁿ]` of the standard generator
of the homology of the sphere. -/
theorem ker_singularHomologyMap_cellAttachmentIncl :
    LinearMap.ker (((singularHomologyFunctor (ModuleCat.{w} R) n).obj (ModuleCat.of R R)).map
        (cellAttachmentIncl φ)).hom =
      Submodule.span R (Set.range fun i ↦
        (((singularHomologyFunctor (ModuleCat.{w} R) n).obj (ModuleCat.of R R)).map (φ i)).hom
          ((reducedSingularHomologyι (ModuleCat.of R R) n).app (TopCat.diskBoundary.{w} (n + 1))
            ((reducedSingularHomologyTopCatSphereIso (ModuleCat.of R R) n).inv 1))) := by
  let H := (singularHomologyFunctor (ModuleCat.{w} R) n).obj (ModuleCat.of R R)
  let σ := (reducedSingularHomologyι (ModuleCat.of R R) n).app (TopCat.diskBoundary.{w} (n + 1))
    ((reducedSingularHomologyTopCatSphereIso (ModuleCat.of R R) n).inv 1)
  let P := skeletonPair (univ : Set (cellAttachment φ)) (n + 1)
  -- Exactness of the skeletal pair at the homology of the `n`-skeleton.
  have hexact :=
    (P.singularHomology_exact_subspace (ModuleCat.of R R) (n + 1) n).moduleCat_range_eq_ker
  -- The attaching spheres of the classical structure are the prescribed ones, read in the
  -- `n`-skeleton.
  have hspan : Submodule.span R (Set.range fun j : cell (univ : Set (cellAttachment φ)) (n + 1) ↦
      (H.map (cellAttachingMap j)).hom σ) =
      (Submodule.span R (Set.range fun i ↦ (H.map (φ i)).hom σ)).map
        (H.map (toSkeletonIso φ).hom).hom := by
    rw [Submodule.map_span, ← Set.range_comp, ← (cellEquiv φ).surjective.range_comp]
    congr 2
    funext j
    rw [Function.comp_apply, Function.comp_apply, cellAttachingMap_eq, Functor.map_comp,
      ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [← toSkeletonIso_hom_comp_map_comp_skeletonIso_hom]
  -- As in `surjective_singularHomologyMap_cellAttachmentIncl`, the skeleta of the pair appear as
  -- `TopPair.snd` and `TopPair.fst`, so the composite is split and the exactness and span
  -- identities are applied with `erw`.
  erw [Functor.map_comp, Functor.map_comp]
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.ker_comp]
  erw [LinearMap.ker_comp_of_ker_eq_bot _
      (LinearMap.ker_eq_bot.2 (H.mapIso (skeletonIso φ)).toLinearEquiv.injective),
    ← hexact, range_skeletonPairδ, hspan]
  exact Submodule.comap_map_eq_of_injective (H.mapIso (toSkeletonIso φ)).toLinearEquiv.injective _

/-! ### Homology in the dimension of the cells -/

/-- **Attaching `(n + 1)`-cells to a space without homology in degrees `n` and `n + 1`.** If
`Hₙ₊₁(X; R)` and `Hₙ(X; R)` vanish, for instance if `X` is a point and `n ≥ 1`, then
`Hₙ₊₁(Y; R)` is free on the attached cells: it is the coproduct of one copy of `R` for each
cell. -/
theorem nonempty_singularHomology_cellAttachment_iso_sigma
    (h₁ : IsZero (((singularHomologyFunctor (ModuleCat.{w} R) (n + 1)).obj
      (ModuleCat.of R R)).obj X))
    (h₀ : IsZero (((singularHomologyFunctor (ModuleCat.{w} R) n).obj (ModuleCat.of R R)).obj X)) :
    Nonempty (((singularHomologyFunctor (ModuleCat.{w} R) (n + 1)).obj (ModuleCat.of R R)).obj
      (cellAttachment φ) ≅ ∐ fun _ : ι ↦ ModuleCat.of R R) := by
  let P := skeletonPair (univ : Set (cellAttachment φ)) (n + 1)
  let H := fun k ↦ (singularHomologyFunctor (ModuleCat.{w} R) k).obj (ModuleCat.of R R)
  -- The homology of the `n`-skeleton vanishes in degrees `n` and `n + 1`.
  have h₁' := h₁.of_iso ((H (n + 1)).mapIso (toSkeletonIso φ)).symm
  have h₀' := h₀.of_iso ((H n).mapIso (toSkeletonIso φ)).symm
  -- So the map from the homology of the `(n + 1)`-skeleton to that of the pair is bijective.
  have hmono : Mono (P.singularHomologyπ (ModuleCat.of R R) (n + 1)) :=
    (P.singularHomology_exact_space (ModuleCat.of R R) (n + 1)).mono_g (h₁'.eq_of_src _ _)
  have hepi : Epi (P.singularHomologyπ (ModuleCat.of R R) (n + 1)) :=
    (P.singularHomology_exact_relative (ModuleCat.of R R) (n + 1) n).epi_f (h₀'.eq_of_tgt _ _)
  have hiso : IsIso (P.singularHomologyπ (ModuleCat.of R R) (n + 1)) := isIso_of_mono_of_epi _
  exact ⟨((H (n + 1)).mapIso (skeletonIso φ)).symm ≪≫
    @asIso _ _ _ _ (P.singularHomologyπ (ModuleCat.of R R) (n + 1)) hiso ≪≫
      cellularChainGroupIso (univ : Set (cellAttachment φ)) (ModuleCat.of R R) (n + 1) ≪≫
        Sigma.reindex (cellEquiv φ) (fun _ : ι ↦ ModuleCat.of R R)⟩

end TauCeti
