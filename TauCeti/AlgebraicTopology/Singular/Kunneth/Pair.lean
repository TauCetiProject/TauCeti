/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Excision
public import TauCeti.AlgebraicTopology.Singular.Kunneth.Relative

/-!
# The shuffle map of a product of two pairs

Let `A ⊆ X` and `B ⊆ Y` be subsets of topological spaces, and write `A × Y` and `X × B` for the
preimages of `A` and `B` under the projections of `X × Y`. The shuffle map
`C(X; R) ⊗ C(Y; S) ⟶ C(X × Y; R ⊗ S)` (`TopCat.shuffle`) carries `C(A; R) ⊗ C(Y; S)` into the chains
of `A × Y` and `C(X; R) ⊗ C(B; S)` into the chains of `X × B`. So it descends to the **shuffle map
of the product of the pairs** `(X, A)` and `(Y, B)` (`TopCat.shufflePair`)

`C(X, A; R) ⊗ C(Y, B; S) ⟶ C(X × Y, A × Y ∪ X × B; R ⊗ S)`,

characterized by `(π ⊗ π) ≫ shufflePair = shuffle ≫ π`
(`TopCat.singularChainComplexπ_tensorHom_singularChainComplexπ_shufflePair`). It is built from the
relative shuffle map `TopCat.shuffleRel` of `(X, A)` and `Y`: tensoring on the left with
`C(X, A; R)` preserves the short exact sequence `C(B) ⟶ C(Y) ⟶ C(Y, B)`, since the inclusion of
the singular chains of `B` splits in each degree, and the relative shuffle map followed by the
quotient modulo the chains of `A × Y ∪ X × B` vanishes on `C(X, A; R) ⊗ C(B; S)`.

It is natural in maps of pairs (`TopCat.shufflePair_naturality`). When the interiors of `A × Y`
and `X × B` cover their union, in particular when `A` and `B` are open, it is a quasi-isomorphism
(`TopCat.quasiIso_shufflePair`, `TopCat.quasiIso_shufflePair_of_isOpen`): this is the **relative
Eilenberg–Zilber theorem for a product of pairs**. The tensored sequence maps to the singular
chain sequence of the triple `(X × Y, A × Y ∪ X × B, A × Y)`, by the relative shuffle maps of
`(X, A)` with `B` and with `Y` on the first two terms and by `shufflePair` on the third. The
relative shuffle maps are quasi-isomorphisms (`TopCat.quasiIso_shuffleRel`), and the first is
followed by the inclusion of pairs `(X × B, A × B) ⟶ (A × Y ∪ X × B, A × Y)`, an excision since
the interiors of `A × Y` and `X × B` cover the union
(`TopPair.isIso_singularHomologyMap_prodExcisionFst`). The five lemma concludes
(`TopCat.quasiIso_shufflePair_of_isIso`). The cover is used only through this excision.

The map lives on simplicial singular chains, the chain model of the shuffle and
Alexander–Whitney maps (`TopCat.shuffle`, `TopCat.alexanderWhitney`). The relative homology of
`(X × Y, A × Y ∪ X × B)` is also reached through cubical chains, by the comparison
`TauCeti.cubicalChainComplexProdToSingular` behind `TauCeti.singularHomologyKunnethPair`; the two
chain-level constructions are not compared here.

## Main definitions

* `TopCat.shufflePair`: the shuffle map
  `C(X, A; R) ⊗ C(Y, B; S) ⟶ C(X × Y, A × Y ∪ X × B; R ⊗ S)` of a product of two pairs.

## Main results

* `TopCat.quasiIso_shufflePair_of_isIso`: the relative Eilenberg–Zilber theorem for a product of
  pairs whose excision map `TopPair.prodExcisionFst` is a homology isomorphism.
* `TopCat.quasiIso_shufflePair`: the same when the interiors of `A × Y` and `X × B` cover their
  union, and `TopCat.quasiIso_shufflePair_of_isOpen` when `A` and `B` are open.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.B, the relative cross product `Hₚ(X, A) ⊗ H_q(Y, B) ⟶ Hₙ(X × Y, A × Y ∪ X × B)`.
* E. H. Spanier, *Algebraic Topology*, Chapter 5, Section 3, excisive couples and the relative
  Eilenberg–Zilber theorem.
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory HomologicalComplex Limits
  AlgebraicTopology

universe w v u

namespace TopCat

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCoproducts.{w} C]
  [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft T)]
  [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight T)]
  (X Y : TopCat.{w}) (A : Set X) (B : Set Y) (R S : C)

section QuasiIso

/-- On `C(X; R) ⊗ C(Y; S)`, the relative shuffle map of `(X, A)` and `Y` followed by a map of pairs
`f` out of `(X × Y, A × Y)` is the shuffle map followed by the map of ambient chains induced by `f`
and the projection to the relative chains of the target. -/
private theorem singularChainComplexπ_tensorHom_id_shuffleRel_singularChainComplexMap
    {P : TopPair.{w}} (f : TopPair.ofSubset (fst X Y ⁻¹' A) ⟶ P) :
    ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
        𝟙 ((toSSet.obj Y).chainComplex S)) ≫ shuffleRel X Y A R S ≫
          TopPair.singularChainComplexMap f (R ⊗ S) =
      shuffle X Y R S ≫ SSet.chainComplexMap (toSSet.map (TopPair.Hom.fst f)) (R ⊗ S) ≫
        P.singularChainComplexπ (R ⊗ S) :=
  (singularChainComplexπ_tensorHom_id_shuffleRel_assoc X Y A R S _).trans
    ((Category.assoc _ _ _).trans (congrArg (shuffle X Y R S ≫ ·)
      (TopPair.singularChainComplexπ_pair_naturality f (R ⊗ S)).symm))

/-- The excision map, followed by the inclusion of pairs `(A × Y ∪ X × B, A × Y) ⟶ (X × Y, A × Y)`,
is the product of the identity of `X` with the inclusion of `B` on ambient spaces. -/
private theorem fst_prodExcisionFst_comp_innerToTotal :
    TopPair.Hom.fst (TopPair.prodExcisionFst A B ≫
        TauCeti.TopTriple.innerToTotal.app (TopPair.prodUnionTripleFst A B)) =
      𝟙 X ⊗ₘ ((TopPair.ofSubset B).map : (TopPair.ofSubset B).snd ⟶ Y) := by
  rw [TopPair.Hom.fst_comp, TopPair.prodExcisionFst_fst, TauCeti.TopTriple.innerToTotal_app_fst]
  ext; rfl

/-- The comparison on the first terms: the relative shuffle map of `(X, A)` and `B`, followed by
the excision map. -/
private def shufflePairτ₁ :
    (TopPair.ofSubset A).singularChainComplex R ⊗
        (toSSet.obj (TopPair.ofSubset B).snd).chainComplex S ⟶
      (TauCeti.TopTriple.innerPair.obj
        (TopPair.prodUnionTripleFst A B)).singularChainComplex (R ⊗ S) :=
  shuffleRel X (TopPair.ofSubset B).snd A R S ≫
    TopPair.singularChainComplexMap (TopPair.prodExcisionFst A B) (R ⊗ S)

/-- The comparison on the middle terms: the relative shuffle map of `(X, A)` and `Y`, read in the
total pair of the triple. -/
private def shufflePairτ₂ :
    (TopPair.ofSubset A).singularChainComplex R ⊗ (toSSet.obj Y).chainComplex S ⟶
      (TauCeti.TopTriple.totalPair.obj
        (TopPair.prodUnionTripleFst A B)).singularChainComplex (R ⊗ S) :=
  shuffleRel X Y A R S

/-- The comparison maps commute with the maps of the sequences on the first two terms. -/
private theorem shufflePair_comm₁₂ :
    (𝟙 ((TopPair.ofSubset A).singularChainComplex R) ⊗ₘ
        (SSet.chainComplexMap (toSSet.map (TopPair.ofSubset B).map) S :
          (toSSet.obj (TopPair.ofSubset B).snd).chainComplex S ⟶ (toSSet.obj Y).chainComplex S)) ≫
        shufflePairτ₂ X Y A B R S =
      shufflePairτ₁ X Y A B R S ≫ TopPair.singularChainComplexMap
        (TauCeti.TopTriple.innerToTotal.app (TopPair.prodUnionTripleFst A B)) (R ⊗ S) := by
  have := (shortExact_tensorRightShortComplex_singularChainComplexShortComplex X
    (TopPair.ofSubset B).snd A R S).epi_g
  refine (cancel_epi ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
      𝟙 ((toSSet.obj (TopPair.ofSubset B).snd).chainComplex S))).1 ?_
  have h₂ := shuffle_naturality (𝟙 X) ((TopPair.ofSubset B).map : (TopPair.ofSubset B).snd ⟶ Y)
    R S
  simp only [CategoryTheory.Functor.map_id] at h₂
  have hx := singularChainComplexπ_tensorHom_id_comp_id_tensorHom_chainComplexMap X Y A B R S
  rw [TopPair.toSSetPair_obj_hom] at hx
  have e₂ := singularChainComplexπ_tensorHom_id_shuffleRel X Y A R S
  have e₁ := singularChainComplexπ_tensorHom_id_shuffleRel_singularChainComplexMap X
    (TopPair.ofSubset B).snd A R S (TopPair.prodExcisionFst A B ≫
      TauCeti.TopTriple.innerToTotal.app (TopPair.prodUnionTripleFst A B))
  rw [fst_prodExcisionFst_comp_innerToTotal, TopPair.singularChainComplexMap_comp] at e₁
  -- Both sides are the shuffle map of `X` and `B`, followed by the map induced by `X × B ⟶ X × Y`
  -- and the projection to the relative chains of `(X × Y, A × Y)`. The chain complexes appear in
  -- several forms that agree only up to unfolding, so the composites are reassociated by hand.
  exact ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hx).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) e₂).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h₂).trans
        (Category.assoc _ _ _))))))).trans
    ((congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans e₁).symm

/-- The morphism from the sequence `C(X, A) ⊗ (C(B) ⟶ C(Y) ⟶ C(Y, B))` to the singular chain
sequence of the triple `(X × Y, A × Y ∪ X × B, A × Y)` given by the relative shuffle maps and the
shuffle map of the product of pairs. -/
private def shufflePairShortComplexMap :
    tensorLeftShortComplex ((TopPair.ofSubset A).singularChainComplex R)
        ((TopPair.ofSubset B).singularChainComplexShortComplex S) ⟶
      (TopPair.prodUnionTripleFst A B).singularChainComplexShortComplex (R ⊗ S) where
  τ₁ := shufflePairτ₁ X Y A B R S
  τ₂ := shufflePairτ₂ X Y A B R S
  τ₃ := shufflePair X Y A B R S
  comm₁₂ := (shufflePair_comm₁₂ X Y A B R S).symm
  comm₂₃ := ((id_tensorHom_singularChainComplexπ_shufflePair X Y A B R S).trans <| by
    dsimp only
    rw [TauCeti.TopTriple.totalToOuter_app_ofSubset]
    rfl).symm

variable {A B}

/-- **The relative Eilenberg–Zilber theorem for an excisive product of pairs**: if the inclusion of
pairs `(X × B, A × B) ⟶ (A × Y ∪ X × B, A × Y)` (`TopPair.prodExcisionFst`) induces isomorphisms on
relative singular homology, then the shuffle map
`C(X, A; R) ⊗ C(Y, B; S) ⟶ C(X × Y, A × Y ∪ X × B; R ⊗ S)` is a quasi-isomorphism. -/
theorem quasiIso_shufflePair_of_isIso
    (h : ∀ n, IsIso (TopPair.singularHomologyMap (TopPair.prodExcisionFst A B) (R ⊗ S) n)) :
    QuasiIso (shufflePair X Y A B R S) := by
  have : QuasiIso (TopPair.singularChainComplexMap (TopPair.prodExcisionFst A B) (R ⊗ S)) :=
    (quasiIso_iff _).2 fun n ↦ (quasiIsoAt_iff_isIso_homologyMap _ n).2 (h n)
  have : QuasiIso (shufflePairτ₁ X Y A B R S) := by
    rw [shufflePairτ₁]
    infer_instance
  have : QuasiIso (shufflePairτ₂ X Y A B R S) := quasiIso_shuffleRel X Y A R S
  exact HomologySequence.quasiIso_τ₃ (shufflePairShortComplexMap X Y A B R S)
    (shortExact_tensorLeftShortComplex_singularChainComplexShortComplex X Y A B R S)
    ((TopPair.prodUnionTripleFst A B).shortExact_singularChainComplexShortComplex (R ⊗ S)) ‹_› ‹_›

/-- **The relative Eilenberg–Zilber theorem for a product of pairs with covering interiors**: if
the interiors of `A × Y` and `X × B` in `A × Y ∪ X × B` cover it, then the shuffle map
`C(X, A; R) ⊗ C(Y, B; S) ⟶ C(X × Y, A × Y ∪ X × B; R ⊗ S)` is a quasi-isomorphism. -/
theorem quasiIso_shufflePair
    (h : interior ((↑) ⁻¹' (fst X Y ⁻¹' A) : Set ↥(fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)) ∪
      interior ((↑) ⁻¹' (snd X Y ⁻¹' B) : Set ↥(fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)) = Set.univ) :
    QuasiIso (shufflePair X Y A B R S) :=
  quasiIso_shufflePair_of_isIso X Y R S
    (TopPair.isIso_singularHomologyMap_prodExcisionFst (R ⊗ S) h)

/-- **The relative Eilenberg–Zilber theorem for a product of open pairs**: for open `A ⊆ X` and
`B ⊆ Y`, the shuffle map `C(X, A; R) ⊗ C(Y, B; S) ⟶ C(X × Y, A × Y ∪ X × B; R ⊗ S)` is a
quasi-isomorphism. -/
theorem quasiIso_shufflePair_of_isOpen (hA : IsOpen A) (hB : IsOpen B) :
    QuasiIso (shufflePair X Y A B R S) :=
  quasiIso_shufflePair_of_isIso X Y R S
    (TopPair.isIso_singularHomologyMap_prodExcisionFst_of_isOpen (R ⊗ S) hA hB)

end QuasiIso

end TopCat
