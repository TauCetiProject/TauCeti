/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Products
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

In the dimension `n + 1` of the cells, for a module `N` of coefficients, if `Hₙ₊₁(X; N)` and
`Hₙ(X; N)` vanish, then `Hₙ₊₁(Y; N)` is the coproduct of one copy of `N` for each attached cell
(`TauCeti.nonempty_singularHomology_cellAttachment_iso_sigma`); for `N = R` it is free on the
cells. If only `Hₙ₊₁(X; N)` vanishes, `Hₙ₊₁(Y; N)` still embeds into that coproduct
(`TauCeti.exists_mono_singularHomology_cellAttachment_sigma`). So, still assuming that
`Hₙ₊₁(X; N)` vanishes, for finitely many cells and Noetherian `N` the module `Hₙ₊₁(Y; N)` is
Noetherian (`TauCeti.isNoetherian_singularHomology_cellAttachment`). Under the same vanishing
hypothesis, for a free module `N` over a ring `R` with the strong rank condition, the rank of
`Hₙ₊₁(Y; N)` is at most the cardinality of the set of cells times the rank of `N`
(`TauCeti.rank_singularHomology_cellAttachment_le`), and for finitely many cells and finite free
`N` its `finrank` is at most their number times the `finrank` of `N`
(`TauCeti.finrank_singularHomology_cellAttachment_le`).

The proof reads the attachment as a relative CW complex whose cells all have dimension `n + 1`.
Its `n`-skeleton is `X` and its `(n + 1)`-skeleton is `Y`, so the long exact sequence of the pair
`(Y, X)` is the one of the skeletal pair. The relative homology `Hₙ(Y, X)` vanishes, and the image
of the connecting morphism `Hₙ₊₁(Y, X) → Hₙ(X)` is spanned by the attaching spheres
(`TauCeti.range_skeletonPairδ`). In degree `n + 1`, the same sequence maps `Hₙ₊₁(Y)` to the
relative homology `Hₙ₊₁(Y, X)`, the cellular chain group of the cells: vanishing of `Hₙ₊₁(X)`
makes this map an embedding, and vanishing of `Hₙ(X)` as well makes it an isomorphism.

## Main results

* `TauCeti.surjective_singularHomologyMap_cellAttachmentIncl`: `Hₙ(X) → Hₙ(Y)` is onto.
* `TauCeti.ker_singularHomologyMap_cellAttachmentIncl`: its kernel is spanned by the classes of
  the attaching spheres.
* `TauCeti.nonempty_singularHomology_cellAttachment_iso_sigma`: if `Hₙ₊₁(X; N)` and `Hₙ(X; N)`
  vanish, `Hₙ₊₁(Y; N)` is the coproduct of one copy of `N` for each cell.
* `TauCeti.exists_mono_singularHomology_cellAttachment_sigma`: if `Hₙ₊₁(X; N)` vanishes,
  `Hₙ₊₁(Y; N)` embeds into the coproduct of one copy of `N` for each cell.
* `TauCeti.isNoetherian_singularHomology_cellAttachment`: for finitely many attached cells and
  Noetherian coefficients `N`, if `Hₙ₊₁(X; N)` vanishes, `Hₙ₊₁(Y; N)` is a Noetherian module.
* `TauCeti.rank_singularHomology_cellAttachment_le`: for a free module `N` over a ring with the
  strong rank condition, if `Hₙ₊₁(X; N)` vanishes, the rank of `Hₙ₊₁(Y; N)` is at most the
  cardinality of the set of cells times the rank of `N`.
* `TauCeti.finrank_singularHomology_cellAttachment_le`: for finitely many attached cells and a
  finite free module `N` over a ring with the strong rank condition, if `Hₙ₊₁(X; N)` vanishes,
  the `finrank` of `Hₙ₊₁(Y; N)` is at most the number of cells times the `finrank` of `N`.

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

/-- The old space as the `n`-skeleton of the cell attachment, through the inclusion. -/
private abbrev toSkeletonIso : X ≅ skeletonObj (univ : Set (cellAttachment φ)) (n + 1) :=
  skeletonObjIsoOfRangeEq (f := (cellAttachmentIncl φ).hom)
    (isClosedEmbedding_cellAttachmentIncl φ).isEmbedding (skeletonLT_eq_range φ).symm

/-- The `(n + 1)`-skeleton of the cell attachment as the whole space. -/
private abbrev skeletonIso :
    skeletonObj (univ : Set (cellAttachment φ)) (n + 2) ≅ cellAttachment φ :=
  skeletonObjIsoOfEqUniv (skeletonLT_eq_univ φ)

/-- Through the two identifications, the inclusion of the old space is the inclusion of the
`n`-skeleton into the `(n + 1)`-skeleton. -/
private lemma cellAttachmentIncl_eq_comp :
    cellAttachmentIncl φ = (toSkeletonIso φ).hom ≫
      (skeletonPair (univ : Set (cellAttachment φ)) (n + 1)).map ≫ (skeletonIso φ).hom :=
  -- `TopCat.ofHom (cellAttachmentIncl φ).hom` is `cellAttachmentIncl φ` (`TopCat.ofHom_hom`).
  (skeletonObjIsoOfRangeEq_hom_comp_map_comp (isClosedEmbedding_cellAttachmentIncl φ).isEmbedding
    (skeletonLT_eq_range φ).symm (skeletonLT_eq_univ φ)).symm

/-- The `(n + 1)`-cells of the classical structure are the attached cells. -/
private def cellEquiv : cell (univ : Set (cellAttachment φ)) (n + 1) ≃ ι :=
  (cellAttachmentAttachCells φ).cellToRelCWComplexEquiv

/-- The attaching map of an `(n + 1)`-cell of the classical structure is the prescribed attaching
map, followed by the identification of the old space with the `n`-skeleton. -/
private lemma cellAttachingMap_eq (j : cell (univ : Set (cellAttachment φ)) (n + 1)) :
    cellAttachingMap j = φ (cellEquiv φ j) ≫
      (toSkeletonIso φ).hom := by
  ext z
  obtain ⟨i, rfl⟩ := (cellEquiv φ).symm.surjective j
  rw [coe_cellAttachingMap_apply, Equiv.apply_symm_apply, ConcreteCategory.comp_apply,
    coe_skeletonObjIsoOfRangeEq_hom_apply]
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
  rw [cellAttachmentIncl_eq_comp]
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
  rw [cellAttachmentIncl_eq_comp]
  -- As in `surjective_singularHomologyMap_cellAttachmentIncl`, the skeleta of the pair appear as
  -- `TopPair.snd` and `TopPair.fst`, so the composite is split and the exactness and span
  -- identities are applied with `erw`.
  erw [Functor.map_comp, Functor.map_comp]
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.ker_comp]
  erw [LinearMap.ker_comp_of_ker_eq_bot _
      (LinearMap.ker_eq_bot.2
        (H.mapIso (skeletonIso φ)).toLinearEquiv.injective),
    ← hexact, range_skeletonPairδ, hspan]
  exact Submodule.comap_map_eq_of_injective
    (H.mapIso (toSkeletonIso φ)).toLinearEquiv.injective _

/-! ### Homology in the dimension of the cells -/

/-- The comparison morphism from `Hₙ₊₁(Y; N)` to the relative homology `Hₙ₊₁(Y, X; N)` of the
cell attachment, read as the coproduct of one copy of `N` for each attached cell. -/
private def singularHomologyToSigma (N : ModuleCat.{w} R) :
    ((singularHomologyFunctor (ModuleCat.{w} R) (n + 1)).obj N).obj (cellAttachment φ) ⟶
      ∐ fun _ : ι ↦ N :=
  (((singularHomologyFunctor (ModuleCat.{w} R) (n + 1)).obj N).mapIso (skeletonIso φ)).inv ≫
    (skeletonPair (univ : Set (cellAttachment φ)) (n + 1)).singularHomologyπ N (n + 1) ≫
      (cellularChainGroupIso (univ : Set (cellAttachment φ)) N (n + 1) ≪≫
        Sigma.reindex (cellEquiv φ) (fun _ : ι ↦ N)).hom

/-- If `Hₙ₊₁(X; N)` vanishes, the comparison morphism from `Hₙ₊₁(Y; N)` to the coproduct of one
copy of `N` for each cell is a monomorphism. -/
private lemma mono_singularHomologyToSigma (N : ModuleCat.{w} R)
    (h₁ : IsZero (((singularHomologyFunctor (ModuleCat.{w} R) (n + 1)).obj N).obj X)) :
    Mono (singularHomologyToSigma φ R N) := by
  -- The homology of the `n`-skeleton, which is `X`, vanishes in degree `n + 1`, so the map from
  -- the homology of the `(n + 1)`-skeleton to that of the pair is injective.
  have h₁' :=
    h₁.of_iso (((singularHomologyFunctor (ModuleCat.{w} R) (n + 1)).obj N).mapIso
      (toSkeletonIso φ)).symm
  have hmono : Mono ((skeletonPair (univ : Set (cellAttachment φ)) (n + 1)).singularHomologyπ N
      (n + 1)) :=
    ((skeletonPair _ (n + 1)).singularHomology_exact_space N (n + 1)).mono_g (h₁'.eq_of_src _ _)
  -- The two outer factors are isomorphisms.
  exact mono_comp' inferInstance (mono_comp' hmono inferInstance)

/-- **Attaching `(n + 1)`-cells to a space without homology in degrees `n` and `n + 1`.** For
every module `N` of coefficients, if `Hₙ₊₁(X; N)` and `Hₙ(X; N)` vanish, for instance if `X` is a
point and `n ≥ 1`, then `Hₙ₊₁(Y; N)` is the coproduct of one copy of `N` for each attached cell.
For `N = R` this says that `Hₙ₊₁(Y; R)` is free on the attached cells. -/
theorem nonempty_singularHomology_cellAttachment_iso_sigma (N : ModuleCat.{w} R)
    (h₁ : IsZero (((singularHomologyFunctor (ModuleCat.{w} R) (n + 1)).obj N).obj X))
    (h₀ : IsZero (((singularHomologyFunctor (ModuleCat.{w} R) n).obj N).obj X)) :
    Nonempty (((singularHomologyFunctor (ModuleCat.{w} R) (n + 1)).obj N).obj
      (cellAttachment φ) ≅ ∐ fun _ : ι ↦ N) := by
  -- The homology of the `n`-skeleton vanishes in degree `n`, so the map from the homology of the
  -- `(n + 1)`-skeleton to that of the pair is onto; it is injective as `Hₙ₊₁(X; N)` vanishes.
  have h₀' := h₀.of_iso
    (((singularHomologyFunctor (ModuleCat.{w} R) n).obj N).mapIso (toSkeletonIso φ)).symm
  have hepi : Epi ((skeletonPair (univ : Set (cellAttachment φ)) (n + 1)).singularHomologyπ N
      (n + 1)) :=
    ((skeletonPair _ (n + 1)).singularHomology_exact_relative N (n + 1) n).epi_f
      (h₀'.eq_of_tgt _ _)
  have : Epi (singularHomologyToSigma φ R N) :=
    epi_comp' inferInstance (epi_comp' hepi inferInstance)
  have := mono_singularHomologyToSigma φ R N h₁
  have : IsIso (singularHomologyToSigma φ R N) := isIso_of_mono_of_epi _
  exact ⟨asIso (singularHomologyToSigma φ R N)⟩

/-- **Attaching `(n + 1)`-cells to a space without homology in degree `n + 1`.** For every module
`N` of coefficients, if `Hₙ₊₁(X; N)` vanishes, then `Hₙ₊₁(Y; N)` embeds into the coproduct of one
copy of `N` for each attached cell: its map to the relative homology `Hₙ₊₁(Y, X; N)`, which is
that coproduct, is a monomorphism. -/
theorem exists_mono_singularHomology_cellAttachment_sigma (N : ModuleCat.{w} R)
    (h₁ : IsZero (((singularHomologyFunctor (ModuleCat.{w} R) (n + 1)).obj N).obj X)) :
    ∃ f : ((singularHomologyFunctor (ModuleCat.{w} R) (n + 1)).obj N).obj (cellAttachment φ) ⟶
      ∐ fun _ : ι ↦ N, Mono f :=
  ⟨_, mono_singularHomologyToSigma φ R N h₁⟩

/-- The comparison morphism from `Hₙ₊₁(Y; N)` to the relative homology of the cell attachment,
read as the module `ι →₀ N` of finitely supported families indexed by the attached cells. -/
private def singularHomologyToFinsupp (N : ModuleCat.{w} R) :
    ((singularHomologyFunctor (ModuleCat.{w} R) (n + 1)).obj N).obj (cellAttachment φ) →ₗ[R]
      (ι →₀ N) :=
  (ModuleCat.coprodLinearEquivFinsupp.{w, w, w} N ι).toLinearMap ∘ₗ
    (singularHomologyToSigma φ R N).hom

/-- If `Hₙ₊₁(X; N)` vanishes, then `Hₙ₊₁(Y; N)` embeds linearly into `ι →₀ N`. -/
private lemma injective_singularHomologyToFinsupp (N : ModuleCat.{w} R)
    (h₁ : IsZero (((singularHomologyFunctor (ModuleCat.{w} R) (n + 1)).obj N).obj X)) :
    Function.Injective (singularHomologyToFinsupp φ R N) := by
  have := mono_singularHomologyToSigma φ R N h₁
  exact (ModuleCat.coprodLinearEquivFinsupp.{w, w, w} N ι).injective.comp
    ((ModuleCat.mono_iff_injective _).1 inferInstance)

/-- **Attaching finitely many `(n + 1)`-cells to a space without homology in degree `n + 1`.**
With coefficients in a Noetherian module `N`, for instance a Noetherian ring such as `ℤ` or a
field, if `Hₙ₊₁(X; N)` vanishes, then `Hₙ₊₁(Y; N)` is a Noetherian `R`-module; in particular it
is finitely generated, and so are all its submodules. -/
theorem isNoetherian_singularHomology_cellAttachment [Finite ι] (N : ModuleCat.{w} R)
    [IsNoetherian R N]
    (h₁ : IsZero (((singularHomologyFunctor (ModuleCat.{w} R) (n + 1)).obj N).obj X)) :
    IsNoetherian R (((singularHomologyFunctor (ModuleCat.{w} R) (n + 1)).obj N).obj
      (cellAttachment φ)) :=
  isNoetherian_of_injective ((Finsupp.linearEquivFunOnFinite R N ι).toLinearMap ∘ₗ
      singularHomologyToFinsupp φ R N)
    ((Finsupp.linearEquivFunOnFinite R N ι).injective.comp
      (injective_singularHomologyToFinsupp φ R N h₁))

/-- **Attaching `(n + 1)`-cells to a space without homology in degree `n + 1`.** With coefficients
in a free module `N` over a ring `R` with the strong rank condition, for instance `R` itself for
`R = ℤ` or a division ring, if `Hₙ₊₁(X; N)` vanishes, then the rank of `Hₙ₊₁(Y; N)` is at most
the cardinality of the set of attached cells times the rank of `N`. -/
theorem rank_singularHomology_cellAttachment_le [StrongRankCondition R] (N : ModuleCat.{w} R)
    [Module.Free R N]
    (h₁ : IsZero (((singularHomologyFunctor (ModuleCat.{w} R) (n + 1)).obj N).obj X)) :
    Module.rank R (((singularHomologyFunctor (ModuleCat.{w} R) (n + 1)).obj N).obj
      (cellAttachment φ)) ≤ Cardinal.mk ι * Module.rank R N :=
  (LinearMap.rank_le_of_injective _ (injective_singularHomologyToFinsupp φ R N h₁)).trans_eq
    (rank_finsupp' R N ι)

/-- **Attaching finitely many `(n + 1)`-cells to a space without homology in degree `n + 1`.**
With coefficients in a finite free module `N` over a ring `R` with the strong rank condition, for
instance `R` itself for `R = ℤ` or a division ring, if `Hₙ₊₁(X; N)` vanishes, then the `finrank`
of `Hₙ₊₁(Y; N)` is at most the number of attached cells times the `finrank` of `N`. -/
theorem finrank_singularHomology_cellAttachment_le [Finite ι] [StrongRankCondition R]
    (N : ModuleCat.{w} R) [Module.Free R N] [Module.Finite R N]
    (h₁ : IsZero (((singularHomologyFunctor (ModuleCat.{w} R) (n + 1)).obj N).obj X)) :
    Module.finrank R (((singularHomologyFunctor (ModuleCat.{w} R) (n + 1)).obj N).obj
      (cellAttachment φ)) ≤ Nat.card ι * Module.finrank R N :=
  Module.finrank_le_of_rank_le <| (rank_singularHomology_cellAttachment_le φ R N h₁).trans_eq <| by
    rw [Nat.cast_mul, Nat.cast_card, Module.finrank_eq_rank]

end TauCeti
