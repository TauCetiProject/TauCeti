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

On homology, the relative cross product `Hₚ(X, A; R) ⊗ H_q(Y; S) ⟶ Hₙ(X × Y, A × Y; R ⊗ S)`
followed by the restriction to `(X × Y, A × Y ∪ X × B)` is the cross product with the image in
`H_q(Y, B; S)`, through `shufflePair` (`TopCat.singularHomologyCrossRel_comp_singularHomologyMap`).

The map lives on simplicial singular chains, the chain model of the shuffle and
Alexander–Whitney maps (`TopCat.shuffle`, `TopCat.alexanderWhitney`). The relative homology of
`(X × Y, A × Y ∪ X × B)` is also reached through cubical chains, by the comparison
`TauCeti.cubicalChainComplexProdToSingular` behind `TauCeti.singularHomologyKunnethPair`; the two
chain-level constructions are not compared here.

## Main definitions

* `TopCat.shufflePair`: the shuffle map
  `C(X, A; R) ⊗ C(Y, B; S) ⟶ C(X × Y, A × Y ∪ X × B; R ⊗ S)` of a product of two pairs.

## Main results

* `TopCat.singularChainComplexπ_tensorHom_singularChainComplexπ_shufflePair`: the shuffle map of a
  product of pairs is induced by the absolute shuffle map.
* `TopCat.shufflePair_naturality`: naturality in maps of both pairs.
* `TopCat.singularHomologyCrossRel_comp_singularHomologyMap`: the relative cross product restricts
  to the product of pairs through `shufflePair`.
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

section Construction

omit [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft T)]
  [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight T)] in
/-- Tensoring on the left with `C(X, A; R)` preserves the short exact sequence
`C(B; S) ⟶ C(Y; S) ⟶ C(Y, B; S)` of singular chains of the pair `(Y, B)`, since the inclusion of
the singular chains of `B` splits in each degree. -/
theorem shortExact_tensorLeftShortComplex_singularChainComplexShortComplex :
    (tensorLeftShortComplex ((TopPair.ofSubset A).singularChainComplex R)
      ((TopPair.ofSubset B).singularChainComplexShortComplex S)).ShortExact :=
  shortExact_tensorLeftShortComplex _
    ((TopPair.ofSubset B).shortExact_singularChainComplexShortComplex S)

omit [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft T)]
  [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight T)] in
/-- The projection `C(X; R) ⟶ C(X, A; R)` and the inclusion `C(B; S) ⟶ C(Y; S)`, tensored in the
two variables, commute. -/
private theorem singularChainComplexπ_tensorHom_comp_tensorHom_chainComplexMap :
    ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
        𝟙 ((toSSet.obj (TopPair.ofSubset B).snd).chainComplex S)) ≫
      (𝟙 ((TopPair.ofSubset A).singularChainComplex R) ⊗ₘ
        (SSet.chainComplexMap (toSSet.map (TopPair.ofSubset B).map) S :
          (toSSet.obj (TopPair.ofSubset B).snd).chainComplex S ⟶ (toSSet.obj Y).chainComplex S)) =
    (𝟙 ((toSSet.obj X).chainComplex R) ⊗ₘ
        (SSet.chainComplexMap (toSSet.map (TopPair.ofSubset B).map) S :
          (toSSet.obj (TopPair.ofSubset B).snd).chainComplex S ⟶ (toSSet.obj Y).chainComplex S)) ≫
      ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ 𝟙 ((toSSet.obj Y).chainComplex S)) := by
  -- This is the naturality of the map of fixed-left totalizations induced by the projection.
  have h := ((curriedTensor C).mapBifunctorLeftMap (ComplexShape.down ℕ) (ComplexShape.down ℕ)
    ((TopPair.ofSubset A).singularChainComplexπ R)).naturality
      (SSet.chainComplexMap (toSSet.map (TopPair.ofSubset B).map) S)
  rw [Functor.mapBifunctorLeftMap_app, Functor.mapBifunctorLeftMap_app,
    Functor.mapBifunctorLeft_map, Functor.mapBifunctorLeft_map] at h
  exact h.symm

omit [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft T)]
  [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight T)] in
/-- The projection `C(X; R) ⊗ C(Y; S) ⟶ C(X, A; R) ⊗ C(Y, B; S)` is the projection in the first
variable followed by the projection in the second. -/
private theorem singularChainComplexπ_tensorHom_singularChainComplexπ_eq :
    (TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ (TopPair.ofSubset B).singularChainComplexπ S =
      ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ 𝟙 ((toSSet.obj Y).chainComplex S)) ≫
        (𝟙 ((TopPair.ofSubset A).singularChainComplex R) ⊗ₘ
          (TopPair.ofSubset B).singularChainComplexπ S) :=
  (congrArg₂ (· ⊗ₘ ·) (Category.comp_id _).symm (Category.id_comp _).symm).trans
    (mapBifunctorMap_comp _ _ _ _ _ _)

omit [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft T)]
  [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight T)] in
/-- The projection `C(X; R) ⊗ C(Y; S) ⟶ C(X, A; R) ⊗ C(Y, B; S)` is an epimorphism, so a map out of
`C(X, A; R) ⊗ C(Y, B; S)`, such as `TopCat.shufflePair`, is determined by its composite with it. -/
instance epi_singularChainComplexπ_tensorHom_singularChainComplexπ :
    Epi ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
      (TopPair.ofSubset B).singularChainComplexπ S) := by
  have h₁ := (shortExact_tensorRightShortComplex_singularChainComplexShortComplex X Y A R S).epi_g
  have h₂ := (shortExact_tensorLeftShortComplex_singularChainComplexShortComplex X Y A B R S).epi_g
  rw [singularChainComplexπ_tensorHom_singularChainComplexπ_eq X Y A B R S]
  exact epi_comp' h₁ h₂

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

/-- On `C(X; R) ⊗ C(Y; S)`, the relative shuffle map of `(X, A)` and `Y` followed by a map of pairs
out of `(X × Y, A × Y)` that is the identity of `X × Y` is the shuffle map followed by the
projection to the relative chains of the target. -/
private theorem singularChainComplexπ_tensorHom_id_shuffleRel_singularChainComplexMap_of_fst_eq_id
    {Z : TopCat.{w}} {j : Z ⟶ X ⊗ Y} {hj : Topology.IsEmbedding j}
    (f : TopPair.ofSubset (fst X Y ⁻¹' A) ⟶ TopPair.of j hj)
    (hf : TopPair.Hom.fst f = 𝟙 (X ⊗ Y)) :
    ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
        𝟙 ((toSSet.obj Y).chainComplex S)) ≫ shuffleRel X Y A R S ≫
          TopPair.singularChainComplexMap f (R ⊗ S) =
      shuffle X Y R S ≫ (TopPair.of j hj).singularChainComplexπ (R ⊗ S) :=
  (singularChainComplexπ_tensorHom_id_shuffleRel_singularChainComplexMap X Y A R S f).trans
    (congrArg (shuffle X Y R S ≫ ·) ((TopPair.singularChainComplexπ_pair_naturality f (R ⊗ S)).trans
      (TopPair.singularChainComplexπ_comp_singularChainComplexMap_of_fst_eq_id (R ⊗ S) f hf)))

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
  have hx := singularChainComplexπ_tensorHom_comp_tensorHom_chainComplexMap X Y A B R S
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

/-- The relative shuffle map of `(X, A)` and `Y`, followed by the quotient modulo the chains of
`A × Y ∪ X × B`, vanishes on `C(X, A; R) ⊗ C(B; S)`: through the triple
`(X × Y, A × Y ∪ X × B, A × Y)` it factors through the composite of the inclusions of the inner
pair into the total pair and of the total pair into the outer pair, which is zero. -/
private theorem shuffleRel_cokernel_condition :
    (𝟙 ((TopPair.ofSubset A).singularChainComplex R) ⊗ₘ
        (SSet.chainComplexMap (toSSet.map (TopPair.ofSubset B).map) S :
          (toSSet.obj (TopPair.ofSubset B).snd).chainComplex S ⟶ (toSSet.obj Y).chainComplex S)) ≫
      shufflePairτ₂ X Y A B R S ≫ TopPair.singularChainComplexMap
        (TauCeti.TopTriple.totalToOuter.app (TopPair.prodUnionTripleFst A B)) (R ⊗ S) = 0 := by
  -- `rw` does not apply: the chains of `Y` appear both as those of `Y` and as the ambient chains
  -- of the pair `(Y, B)`, which agree only up to unfolding, so the composite is reassociated by
  -- hand.
  exact (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ _) (shufflePair_comm₁₂ X Y A B R S)).trans <| (Category.assoc _ _ _).trans <|
      (congrArg (_ ≫ ·)
        ((TopPair.prodUnionTripleFst A B).singularChainComplexMap_innerToTotal_comp_totalToOuter
          (R ⊗ S))).trans comp_zero

/-- **The shuffle map of a product of two pairs**,
`C(X, A; R) ⊗ C(Y, B; S) ⟶ C(X × Y, A × Y ∪ X × B; R ⊗ S)`, induced by the shuffle map
`C(X; R) ⊗ C(Y; S) ⟶ C(X × Y; R ⊗ S)` on the quotients. It is characterized by
`TopCat.singularChainComplexπ_tensorHom_singularChainComplexπ_shufflePair`, and is a
quasi-isomorphism when `A` and `B` are open (`TopCat.quasiIso_shufflePair_of_isOpen`). -/
def shufflePair :
    (TopPair.ofSubset A).singularChainComplex R ⊗ (TopPair.ofSubset B).singularChainComplex S ⟶
      (TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)).singularChainComplex (R ⊗ S) :=
  have hS := shortExact_tensorLeftShortComplex_singularChainComplexShortComplex X Y A B R S
  have := hS.epi_g
  hS.exact.gIsCokernel.desc (CokernelCofork.ofπ _ (shuffleRel_cokernel_condition X Y A B R S))

/-- The comparison maps commute with the maps of the sequences on the last two terms. -/
private theorem shufflePair_comm₂₃ :
    (𝟙 ((TopPair.ofSubset A).singularChainComplex R) ⊗ₘ
        (TopPair.ofSubset B).singularChainComplexπ S) ≫ shufflePair X Y A B R S =
      shufflePairτ₂ X Y A B R S ≫ TopPair.singularChainComplexMap
        (TauCeti.TopTriple.totalToOuter.app (TopPair.prodUnionTripleFst A B)) (R ⊗ S) :=
  have hS := shortExact_tensorLeftShortComplex_singularChainComplexShortComplex X Y A B R S
  have := hS.epi_g
  hS.exact.gIsCokernel.fac _ WalkingParallelPair.one

/-- On `C(X, A; R) ⊗ C(Y; S)` the shuffle map of the product of pairs is the relative shuffle map
of `(X, A)` and `Y`, followed by the quotient modulo the chains of `A × Y ∪ X × B`. -/
@[reassoc (attr := simp)]
theorem id_tensorHom_singularChainComplexπ_shufflePair :
    (𝟙 ((TopPair.ofSubset A).singularChainComplex R) ⊗ₘ
        (TopPair.ofSubset B).singularChainComplexπ S) ≫ shufflePair X Y A B R S =
      shuffleRel X Y A R S ≫ TopPair.singularChainComplexMap
        (TopPair.ofSubsetMap (𝟙 _) fun _ hz ↦ Or.inl hz) (R ⊗ S) := by
  rw [shufflePair_comm₂₃, shufflePairτ₂, TauCeti.TopTriple.totalToOuter_app_ofSubset]
  -- The two sides differ only in how the pairs `(X × Y, A × Y)` and `(X × Y, A × Y ∪ X × B)` are
  -- presented: as the total and outer pairs of the triple, or as `TopPair.ofSubset`.
  rfl

/-- **The shuffle map of a product of pairs is induced by the shuffle map**: on
`C(X; R) ⊗ C(Y; S)` it is the shuffle map followed by the projection to the relative chains of
`(X × Y, A × Y ∪ X × B)`. -/
@[reassoc (attr := simp)]
theorem singularChainComplexπ_tensorHom_singularChainComplexπ_shufflePair :
    ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
        (TopPair.ofSubset B).singularChainComplexπ S) ≫ shufflePair X Y A B R S =
      shuffle X Y R S ≫
        (TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)).singularChainComplexπ (R ⊗ S) := by
  have h := singularChainComplexπ_tensorHom_singularChainComplexπ_eq X Y A B R S
  -- `rw [Category.assoc]` does not apply: the chains of `Y` appear both as those of `Y` and as the
  -- ambient chains of the pair `(Y, B)`, which agree only up to unfolding `TopPair.ofSubset`.
  exact (congrArg (· ≫ shufflePair X Y A B R S) h).trans ((Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) (id_tensorHom_singularChainComplexπ_shufflePair X Y A B R S)).trans
      (singularChainComplexπ_tensorHom_id_shuffleRel_singularChainComplexMap_of_fst_eq_id X Y A R S
        (TopPair.ofSubsetMap (𝟙 _) fun _ hz ↦ Or.inl hz) (TopPair.ofSubsetMap_fst _ _))))

end Construction

section Naturality

/-- **Naturality of the shuffle map of a product of pairs** in maps of pairs `(X, A) ⟶ (X', A')`
and `(Y, B) ⟶ (Y', B')`. -/
@[reassoc]
theorem shufflePair_naturality {X' Y' : TopCat.{w}} {A' : Set X'} {B' : Set Y'} (f : X ⟶ X')
    (hf : Set.MapsTo f A A') (g : Y ⟶ Y') (hg : Set.MapsTo g B B') :
    (TopPair.singularChainComplexMap (TopPair.ofSubsetMap f hf) R ⊗ₘ
        TopPair.singularChainComplexMap (TopPair.ofSubsetMap g hg) S) ≫
          shufflePair X' Y' A' B' R S =
      shufflePair X Y A B R S ≫ TopPair.singularChainComplexMap
        (TopPair.ofSubsetMap (f ⊗ₘ g) (mapsTo_tensorHom_preimage_union f g hf hg)) (R ⊗ S) := by
  refine (cancel_epi ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
      (TopPair.ofSubset B).singularChainComplexπ S)).1 ?_
  have hπf := TopPair.singularChainComplexπ_pair_naturality (TopPair.ofSubsetMap f hf) R
  have hπg := TopPair.singularChainComplexπ_pair_naturality (TopPair.ofSubsetMap g hg) S
  simp only [TopPair.ofSubsetMap_fst] at hπf hπg
  have h₁ : ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
        (TopPair.ofSubset B).singularChainComplexπ S) ≫
          (TopPair.singularChainComplexMap (TopPair.ofSubsetMap f hf) R ⊗ₘ
            TopPair.singularChainComplexMap (TopPair.ofSubsetMap g hg) S) =
      (SSet.chainComplexMap (toSSet.map f) R ⊗ₘ SSet.chainComplexMap (toSSet.map g) S) ≫
        ((TopPair.ofSubset A').singularChainComplexπ R ⊗ₘ
          (TopPair.ofSubset B').singularChainComplexπ S) :=
    (mapBifunctorMap_comp _ _ _ _ _ _).symm.trans <|
      (congrArg₂ (· ⊗ₘ ·) hπf.symm hπg.symm).trans (mapBifunctorMap_comp _ _ _ _ _ _)
  have h₂ := TopPair.singularChainComplexπ_pair_naturality
    (TopPair.ofSubsetMap (f ⊗ₘ g) (mapsTo_tensorHom_preimage_union f g hf hg)) (R ⊗ S)
  have hfst := TopPair.ofSubsetMap_fst (B := fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)
    (B' := fst X' Y' ⁻¹' A' ∪ snd X' Y' ⁻¹' B') (f ⊗ₘ g) (mapsTo_tensorHom_preimage_union f g hf hg)
  -- Both sides are the shuffle map followed by the map of pairs induced by `f × g`. The chain
  -- complexes of the pairs appear both as relative chains and as the chains of their ambient
  -- spaces, which agree only up to unfolding, so the composites are reassociated by `calc`.
  calc _ = (SSet.chainComplexMap (toSSet.map f) R ⊗ₘ SSet.chainComplexMap (toSSet.map g) S) ≫
        ((TopPair.ofSubset A').singularChainComplexπ R ⊗ₘ
          (TopPair.ofSubset B').singularChainComplexπ S) ≫ shufflePair X' Y' A' B' R S :=
        (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h₁).trans (Category.assoc _ _ _))
    _ = shuffle X Y R S ≫ SSet.chainComplexMap (toSSet.map (f ⊗ₘ g)) (R ⊗ S) ≫
        (TopPair.ofSubset (fst X' Y' ⁻¹' A' ∪ snd X' Y' ⁻¹' B')).singularChainComplexπ (R ⊗ S) :=
        (congrArg (_ ≫ ·)
          (singularChainComplexπ_tensorHom_singularChainComplexπ_shufflePair X' Y' A' B' R S)).trans
          ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _)
            (shuffle_naturality f g R S)).trans (Category.assoc _ _ _)))
    _ = _ := (congrArg (fun φ ↦ shuffle X Y R S ≫ SSet.chainComplexMap (toSSet.map φ) (R ⊗ S) ≫
        (TopPair.ofSubset (fst X' Y' ⁻¹' A' ∪ snd X' Y' ⁻¹' B')).singularChainComplexπ (R ⊗ S))
          hfst.symm).trans <|
      (congrArg (_ ≫ ·) h₂).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ _)
          (singularChainComplexπ_tensorHom_singularChainComplexπ_shufflePair X Y A B R S).symm
            ).trans (Category.assoc _ _ _)))

end Naturality

section Cross

variable (p q n : ℕ) (h : p + q = n)
  [PreservesColimitsOfShape WalkingParallelPair
    (tensorLeft (((TopPair.ofSubset A).singularChainComplex R).homology p))]
  [PreservesColimitsOfShape WalkingParallelPair
    (tensorRight (((toSSet.obj Y).chainComplex S).cycles q))]
  [PreservesColimitsOfShape WalkingParallelPair
    (tensorRight (((toSSet.obj Y).chainComplex S).X ((ComplexShape.down ℕ).prev q)))]
  [PreservesColimitsOfShape WalkingParallelPair
    (tensorRight (((TopPair.ofSubset B).singularChainComplex S).cycles q))]
  [PreservesColimitsOfShape WalkingParallelPair
    (tensorRight (((TopPair.ofSubset B).singularChainComplex S).X ((ComplexShape.down ℕ).prev q)))]

/-- **The relative cross product restricts to the product of pairs.** The image of
`a × b ∈ Hₙ(X × Y, A × Y; R ⊗ S)` in `Hₙ(X × Y, A × Y ∪ X × B; R ⊗ S)` is the cross product of `a`
with the image of `b` in `H_q(Y, B; S)`, through the shuffle map of the product of pairs. -/
theorem singularHomologyCrossRel_comp_singularHomologyMap :
    singularHomologyCrossRel X Y A R S p q n h ≫
      TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 _) fun _ hz ↦ Or.inl hz :
        TopPair.ofSubset (fst X Y ⁻¹' A) ⟶ TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B))
        (R ⊗ S) n =
      (𝟙 _ ⊗ₘ (TopPair.ofSubset B).singularHomologyπ S q) ≫
        homologyCross ((TopPair.ofSubset A).singularChainComplex R)
          ((TopPair.ofSubset B).singularChainComplex S) p q n h ≫
        homologyMap (shufflePair X Y A B R S) n := by
  have hcross : (𝟙 _ ⊗ₘ (TopPair.ofSubset B).singularHomologyπ S q) ≫
      homologyCross ((TopPair.ofSubset A).singularChainComplex R)
        ((TopPair.ofSubset B).singularChainComplex S) p q n h =
      homologyCross ((TopPair.ofSubset A).singularChainComplex R) ((toSSet.obj Y).chainComplex S)
        p q n h ≫
        homologyMap (𝟙 _ ⊗ₘ (TopPair.ofSubset B).singularChainComplexπ S) n := by
    have hn := homologyCross_naturality (L := (toSSet.obj Y).chainComplex S)
      (𝟙 ((TopPair.ofSubset A).singularChainComplex R))
      ((TopPair.ofSubset B).singularChainComplexπ S) p q n h
    rw [homologyMap_id] at hn
    -- `singularHomologyπ` is the map induced by `singularChainComplexπ`, and
    -- `HomologicalComplex.tensorHom` is the tensor product `⊗ₘ` of chain maps.
    exact hn
  rw [singularHomologyCrossRel_def]
  -- Relative singular homology and its maps are by definition the homology of the singular
  -- chain complexes and the maps induced by chain maps.
  change (homologyCross _ _ p q n h ≫ homologyMap (shuffleRel X Y A R S) n) ≫
      homologyMap (TopPair.singularChainComplexMap _ _) n = _
  rw [Category.assoc, ← homologyMap_comp, ← id_tensorHom_singularChainComplexπ_shufflePair,
    reassoc_of% hcross]
  -- The two sides differ only in the bracketing of `homologyMap ((𝟙 ⊗ π) ≫ shufflePair)`, which
  -- `rw` cannot reach in the target produced by `change`.
  exact (_ ≫= homologyMap_comp _ _ n).trans (Category.assoc _ _ _).symm

end Cross

section QuasiIso

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
  comm₂₃ := (shufflePair_comm₂₃ X Y A B R S).symm

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
