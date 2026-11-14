/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Relative.Basic
public import TauCeti.AlgebraicTopology.Singular.FilteredSpace.Basic

/-!
# The cubical spectral sequence of a filtered space

Let `X : ℤ → Set Y` be an increasing family of subsets of a topological space `Y`, for instance
the preimages of the skeleta of a CW complex under a fibration. Since the push-forward along a
subspace inclusion is injective on normalized cubical chains, the normalized cubical chains of the
`X q` form an increasing filtration of the normalized cubical chains of `Y`: this is
`TauCeti.subspaceChainFiltration` for the functor `TauCeti.normalizedCubicalChainComplex`, and its
spectral sequence is `TauCeti.subspaceChainSpectralSequence`. Its graded pieces are the relative
normalized cubical chain complexes `TopPair.cubicalChainComplex`, which are defined as cokernels,
so the general results of `TauCeti.AlgebraicTopology.Singular.FilteredSpace.ChainFunctor` describe
its first page as relative cubical homology and its abutment as cubical homology. Normalized
cubical chains vanish on empty spaces (`TauCeti.isZero_normalizedCubicalChainComplex_obj`), which
gives strong convergence for finite filtrations
(`TauCeti.subspaceChainSpectralSequencePageXIsoGradedOfFinite`).

This file compares that spectral sequence with the spectral sequence
`TauCeti.filteredSpaceSpectralSequence` of the filtration of simplicial singular chains.

* **Comparison.** The natural comparison map `TauCeti.cubicalToSingular` from normalized cubical
  to simplicial singular chains is a quasi-isomorphism on every space, so it induces an
  isomorphism between the cubical and the simplicial spectral sequences of the filtered space, on
  every page (`TauCeti.filteredSpaceCubicalSpectralSequenceIso`). No boundedness or
  exhaustiveness assumption on the filtration is needed.
* **First page and abutment.** Under the identifications of the first pages with relative
  homology, this isomorphism is the map in homology of the relative comparison map
  `TopPair.cubicalToSingularRel` (`TauCeti.filteredSpaceCubicalSpectralSequenceIso_hom_two_f_comp`),
  and on the abutments the comparison is the map in homology of `TauCeti.cubicalToSingular`
  (`TauCeti.spectralObjectMap_cubicalToSingular_abutment_comp`).

Applied to the filtration of the total space of a fibration by the preimages of the skeleta of the
base, this transports the Serre spectral sequence of simplicial singular chains to normalized
cubical chains, the chains on which twisted complexes with coefficients in DG local systems are
built.

## References

* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapters II and VII.
* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  425–505, Chapter II, where the spectral sequence of a fibration is built on cubical chains.
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Section 2.2.
-/

public section

noncomputable section

open CategoryTheory Limits HomologicalComplex Abelian.SpectralObject

universe u

namespace TauCeti

variable (k : Type u) [Ring k]

/-- The normalized cubical chains of an empty space vanish, since it has no singular cubes. -/
lemma isZero_normalizedCubicalChainComplex_obj (Z : TopCat.{u}) [IsEmpty Z] :
    IsZero ((normalizedCubicalChainComplex k).obj Z) := by
  rw [IsZero.iff_id_eq_zero]
  ext n : 1
  have : IsEmpty (SingularCube Z n) := ⟨fun c ↦ isEmptyElim (c fun _ ↦ 0)⟩
  have : Subsingleton (((normalizedCubicalChainComplex k).obj Z).X n) :=
    (normalizedCubicalChainComplexXEquiv (R := k) _ n).toEquiv.subsingleton_congr.2
      (Submodule.Quotient.mk_surjective _).subsingleton
  exact (ModuleCat.isZero_of_subsingleton _).eq_of_src _ _

variable {Y : TopCat.{u}} {X : ℤ → Set Y} (hX : Monotone X)

/-- **The cubical and simplicial spectral sequences of a filtered space are isomorphic.** The
natural comparison map `TauCeti.cubicalToSingular` from normalized cubical to simplicial singular
chains induces an isomorphism, on every page, between the spectral sequence of the filtration of
the normalized cubical chains of `Y` by those of the `X q` and the spectral sequence of the
filtration of the simplicial singular chains of `Y` by those of the `X q`. -/
def filteredSpaceCubicalSpectralSequenceIso :
    subspaceChainSpectralSequence (normalizedCubicalChainComplex k) hX ≅
      filteredSpaceSpectralSequence (ModuleCat.of k k) hX :=
  subspaceChainSpectralSequenceIso hX (cubicalToSingular k)

/-- The isomorphism between the cubical and simplicial spectral sequences of a filtered space is
the morphism of spectral sequences induced by the comparison of the filtrations along
`TauCeti.cubicalToSingular`. -/
@[simp]
lemma filteredSpaceCubicalSpectralSequenceIso_hom :
    (filteredSpaceCubicalSpectralSequenceIso k hX).hom =
      spectralSequenceMap coreE₂Cohomological
        (CochainComplex.spectralObjectMap (subspaceChainFiltrationMap hX (cubicalToSingular k))) :=
  subspaceChainSpectralSequenceIso_hom hX (cubicalToSingular k)

/-- On the cokernel of the map of chains of a pair, the map induced by `TauCeti.cubicalToSingular`
is the relative comparison map `TopPair.cubicalToSingularRel`, under the identification of that
cokernel with the relative singular chains. -/
private lemma cokernel_map_cubicalToSingular_comp (P : TopPair.{u}) :
    cokernel.map _ _ ((cubicalToSingular k).app _) ((cubicalToSingular k).app _)
        ((cubicalToSingular k).naturality P.map) ≫
        (P.cokernelSingularChainComplexIso (ModuleCat.of k k)).hom =
      TopPair.cubicalToSingularRel k P := by
  -- The cokernel of the map of singular chains is written through `TauCeti.singularChains` on one
  -- side and through simplicial chains on the other, so the composites are formed with terms.
  exact (cancel_epi (cokernel.π _)).1 <| (cokernel.π_desc_assoc _ _ _ _).trans <|
    (Category.assoc _ _ _).trans <|
      ((congrArg (_ ≫ ·) (TopPair.π_cokernelSingularChainComplexIso_hom _ P)).trans <|
        congrArg (_ ≫ ·) (TopPair.singularRelπ_eq k P).symm).trans
          (TopPair.π_cubicalToSingularRel k P).symm

/-- **The comparison of the cubical and simplicial spectral sequences on the first page.** Under
the identifications of the objects of the first pages with relative cubical and relative
simplicial homology, the isomorphism `TauCeti.filteredSpaceCubicalSpectralSequenceIso` is the map
in homology of the relative comparison map `TopPair.cubicalToSingularRel`, an isomorphism by
`TopPair.quasiIso_cubicalToSingularRel`. -/
@[reassoc]
lemma filteredSpaceCubicalSpectralSequenceIso_hom_two_f_comp (pq : ℤ × ℤ) (a b : ℤ)
    (ha : a = pq.2) (hb : b = pq.2 + 1) (m : ℤ) (hm : m = pq.1 + pq.2) (n : ℕ) (hn : m = -n) :
    ((filteredSpaceCubicalSpectralSequenceIso k hX).hom.hom 2 le_rfl).f pq ≫
        (filteredSpaceSpectralSequenceFirstPageXIso (ModuleCat.of k k) hX pq a b ha hb m hm n
          hn).hom =
      (subspaceChainSpectralSequenceFirstPageXIso (normalizedCubicalChainComplex k) hX pq a b ha hb
          m hm n hn).hom ≫
        homologyMap (TopPair.cubicalToSingularRel k (TopPair.ofInclusion (hX (by lia : a ≤ b))))
          n := by
  rw [filteredSpaceCubicalSpectralSequenceIso_hom, filteredSpaceSpectralSequenceFirstPageXIso_hom,
    ← cokernel_map_cubicalToSingular_comp, homologyMap_comp]
  exact spectralSequenceMap_subspaceChainFiltrationMap_two_f_comp_assoc hX (cubicalToSingular k)
    pq a b ha hb m hm n hn _

/-- **The comparison of the cubical and simplicial abutments.** Under the identifications of the
abutments in degree `-n` with the cubical and the simplicial homology `Hₙ(Y)`, the morphism of
spectral objects induced by the comparison of the filtrations is the map in homology of the
comparison map `TauCeti.cubicalToSingular` of `Y`. -/
@[reassoc]
lemma spectralObjectMap_cubicalToSingular_abutment_comp (n : ℕ) :
    ((CochainComplex.spectralObjectMap (subspaceChainFiltrationMap hX (cubicalToSingular k))).hom
        (-n)).app (ComposableArrows.mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤))) ≫
        (filteredSpaceAbutmentIso (ModuleCat.of k k) hX n).hom =
      (subspaceChainAbutmentIso (normalizedCubicalChainComplex k) hX n).hom ≫
        homologyMap ((cubicalToSingular k).app Y) n :=
  spectralObjectMap_subspaceChainFiltrationMap_abutment_comp hX (cubicalToSingular k) n

end TauCeti
