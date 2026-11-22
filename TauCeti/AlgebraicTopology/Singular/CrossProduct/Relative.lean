/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.Homology.Connecting
public import TauCeti.AlgebraicTopology.Singular.AlexanderWhitney.RelativeCup
public import TauCeti.AlgebraicTopology.Singular.CrossProduct.Basic
public import TauCeti.AlgebraicTopology.Singular.Kunneth.Pair
import TauCeti.AlgebraicTopology.Singular.Subdivision.Small.Relative
import TauCeti.CategoryTheory.Monoidal.Category

/-!
# The relative cross product in singular homology

For subsets `A ⊆ X` and `B ⊆ Y` and coefficient objects `R` and `S` in an abelian monoidal
category, `TopCat.singularRelativeHomologyCross` is the relative homology cross product

`Hₚ(X, A; R) ⊗ H_q(Y, B; S) ⟶ Hₙ(X × Y, A × Y ∪ X × B; R ⊗ S)` (`p + q = n`),

obtained by composing the algebraic cross product `HomologicalComplex.homologyCross` with the
shuffle map of a product of pairs `TopCat.shufflePair`. On the small-chain side, the relative
Eilenberg–Mac Lane shuffle map `TopCat.relativeShuffle` followed by
`TopCat.smallSingularSubcomplexPairToUnion` agrees with `TopCat.shufflePair`
(`TopCat.relativeShuffle_comp_smallSingularSubcomplexPairToUnion`). Because the short exact sequence
`0 ⟶ C(A) ⟶ C(X) ⟶ C(X, A) ⟶ 0` splits in each degree, tensoring it with any chain complex stays
short exact (`HomologicalComplex.shortExact_tensorLeftShortComplex`,
`HomologicalComplex.shortExact_tensorRightShortComplex`), so both the shuffle map and the
Eilenberg–Zilber homotopies `AW ∘ shuffle ≃ id` and `shuffle ∘ AW ≃ id` descend to relative chains
without openness, flatness, or Künneth assumptions.

This chain-level homotopy equivalence and relative homology cross product feed the Kronecker
duality formulas for relative cross and cup products in
`TauCeti.AlgebraicTopology.Cohomology.Cup.Kronecker` and the local homology cross product in
`TauCeti.AlgebraicTopology.Singular.LocalHomology.Cross`, which in turn establish generator
preservation and reflection for local cohomology cross products and Thom classes over arbitrary
commutative rings without flatness or Künneth hypotheses.

Every construction assumes discrete colimit preservation for `tensorLeft` and `tensorRight`.
For the `WalkingParallelPair` colimit-preservation hypotheses:
* `TopCat.homologyMap_relativeShuffle_comp_homologyMap_relativeAlexanderWhitney` and
  `TopCat.homologyMap_relativeAlexanderWhitney_comp_homologyMap_relativeShuffle` require none;
* `TopCat.singularRelativeHomologyCross` and
  `TopCat.homologyπ_tensorHom_singularRelativeHomologyCross` assume `WalkingParallelPair` colimit
  preservation for `tensorLeft` of `Hₚ(X, A; R)` and `tensorRight` of `Z_q(Y, B; S)` and
  `C_{q+1}(Y, B; S)`;
* `TopCat.singularHomologyπ_tensorHom_singularRelativeHomologyCross`,
  `TopCat.singularRelativeHomologyCross_naturality`, and
  `TopCat.singularRelativeHomologyCross_coefficient_naturality` also require the corresponding
  `WalkingParallelPair` instances on the ambient chains, target pairs, or target coefficients.

## Main definitions and results

* `TopCat.relativeShuffle`: the relative Eilenberg–Mac Lane shuffle map
  `C(X, A; R) ⊗ C(Y, B; S) ⟶ C(X × Y; A × Y + X × B; R ⊗ S)`, characterized by
  `TopCat.singularChainComplexπ_tensorHom_relativeShuffle`, agreeing with `TopCat.shufflePair`
  after `TopCat.smallSingularSubcomplexPairToUnion`
  (`TopCat.relativeShuffle_comp_smallSingularSubcomplexPairToUnion`), and natural in pairs
  (`TopCat.relativeShuffle_naturality`) and coefficients
  (`TopCat.relativeShuffle_coefficient_naturality`).
* `TopCat.relativeShuffleAlexanderWhitneyHomotopy` and
  `TopCat.relativeAlexanderWhitneyShuffleHomotopy`: the relative Eilenberg–Zilber chain homotopies
  `AW ∘ shuffle ≃ id` and `shuffle ∘ AW ≃ id`, assembled into
  `TopCat.relativeEilenbergZilberHomotopyEquiv`, giving
  `TopCat.homologyMap_relativeShuffle_comp_homologyMap_relativeAlexanderWhitney`,
  `TopCat.homologyMap_relativeAlexanderWhitney_comp_homologyMap_relativeShuffle`, and
  `TopCat.quasiIso_relativeShuffle`.
* `TopCat.singularRelativeHomologyCross`: the relative homology cross product, with cycle
  evaluation (`TopCat.homologyπ_tensorHom_singularRelativeHomologyCross`), compatibility with the
  absolute cross product (`TopCat.singularHomologyπ_tensorHom_singularRelativeHomologyCross`), and
  naturality in pairs (`TopCat.singularRelativeHomologyCross_naturality`) and coefficients
  (`TopCat.singularRelativeHomologyCross_coefficient_naturality`).

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), Section 3.B.
* S. Eilenberg and J. A. Zilber, *On products of complexes*, Amer. J. Math. 75 (1953).
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicTopology
  HomologicalComplex

universe w v u

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
  [MonoidalCategory C] [MonoidalPreadditive C]

namespace TopCat

variable [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft T)]
  [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight T)]

section Fixed

variable (X Y : TopCat.{w}) (A : Set X) (B : Set Y) (R S : C)

private def leftRelativeShuffle :
    (TopPair.ofSubset A).singularChainComplex R ⊗ (toSSet.obj Y).chainComplex S ⟶
      ((X ⊗ Y).smallSingularSubcomplex ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.chainComplex
        (R ⊗ S) :=
  shuffleRel X Y A R S ≫
    SSetPair.chainComplexMap
      (toSmallPair (fst X Y ⁻¹' A) (snd X Y ⁻¹' B) (i := 0) (Matrix.cons_val_zero _ _).superset)
      (R ⊗ S)

@[reassoc]
private lemma singularChainComplexπ_tensorHom_id_leftRelativeShuffle :
    ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ 𝟙 ((toSSet.obj Y).chainComplex S)) ≫
        leftRelativeShuffle X Y A B R S =
      shuffle X Y R S ≫
        ((X ⊗ Y).smallSingularSubcomplex ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.chainComplexπ
          (R ⊗ S) := by
  have hπ' :
      (TopPair.ofSubset (fst X Y ⁻¹' A)).singularChainComplexπ (R ⊗ S) ≫
          SSetPair.chainComplexMap
            (toSmallPair (fst X Y ⁻¹' A) (snd X Y ⁻¹' B) (i := 0)
              (Matrix.cons_val_zero _ _).superset) (R ⊗ S) =
        ((X ⊗ Y).smallSingularSubcomplex ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.chainComplexπ
          (R ⊗ S) := by
    have h := (SSetPair.chainComplexπ_naturality (R ⊗ S)
      (toSmallPair (fst X Y ⁻¹' A) (snd X Y ⁻¹' B) (i := 0)
        (Matrix.cons_val_zero _ _).superset)).symm
    change _ = SSet.chainComplexMap (𝟙 _) (R ⊗ S) ≫ _ at h
    rw [SSet.chainComplexMap, CategoryTheory.Functor.map_id] at h
    exact h.trans (Category.id_comp _)
  rw [leftRelativeShuffle, ← Category.assoc, singularChainComplexπ_tensorHom_id_shuffleRel]
  exact (Category.assoc _ _ _).trans (whisker_eq _ hπ')

private lemma id_tensorHom_chainComplexMap_comp_leftRelativeShuffle :
    (𝟙 ((TopPair.ofSubset A).singularChainComplex R) ⊗ₘ
        SSet.chainComplexMap (TopPair.toSSetPair.obj (TopPair.ofSubset B)).hom S) ≫
      leftRelativeShuffle X Y A B R S = 0 := by
  let : MonoidalCategory (ChainComplex C ℕ) := monoidalCategory C (ComplexShape.down ℕ)
  let pA := (TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
    𝟙 ((TopPair.toSSetPair.obj (TopPair.ofSubset B)).left.chainComplex S)
  rw [← cancel_epi pA, comp_zero]
  have hcomm : pA ≫ (𝟙 ((TopPair.ofSubset A).singularChainComplex R) ⊗ₘ
      SSet.chainComplexMap (TopPair.toSSetPair.obj (TopPair.ofSubset B)).hom S) =
      (𝟙 ((toSSet.obj X).chainComplex R) ⊗ₘ
          SSet.chainComplexMap (toSSet.map (TopPair.ofSubset B).map) S) ≫
        ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ 𝟙 ((toSSet.obj Y).chainComplex S)) :=
    (tensor_id_comp_id_tensor _ _).trans (id_tensor_comp_tensor_id _ _).symm
  have hnat := shuffle_naturality (𝟙 X) (TopPair.ofSubset B).map R S
  simp only [CategoryTheory.Functor.map_id] at hnat
  have hf (z) : (𝟙 X ⊗ₘ (TopPair.ofSubset B).map) z ∈ ![fst X Y ⁻¹' A, snd X Y ⁻¹' B] 1 :=
    Set.mem_preimage.2 ((ConcreteCategory.congr_hom
      (tensorHom_snd (𝟙 X) (TopPair.ofSubset B).map) z).symm ▸ (snd X (of ↥B) z).property)
  calc _ = (𝟙 ((toSSet.obj X).chainComplex R) ⊗ₘ
            SSet.chainComplexMap (toSSet.map (TopPair.ofSubset B).map) S) ≫
          ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ 𝟙 ((toSSet.obj Y).chainComplex S)) ≫
          leftRelativeShuffle X Y A B R S :=
        (Category.assoc _ _ _).symm.trans <| (eq_whisker hcomm _).trans (Category.assoc _ _ _)
    _ = (𝟙 ((toSSet.obj X).chainComplex R) ⊗ₘ
            SSet.chainComplexMap (toSSet.map (TopPair.ofSubset B).map) S) ≫
          shuffle X Y R S ≫
          ((X ⊗ Y).smallSingularSubcomplex ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.chainComplexπ
            (R ⊗ S) :=
        whisker_eq _ (singularChainComplexπ_tensorHom_id_leftRelativeShuffle X Y A B R S)
    _ = 0 :=
        (Category.assoc _ _ _).symm.trans <| (eq_whisker hnat _).trans <|
          (Category.assoc _ _ _).trans <|
            (whisker_eq _
              (TauCeti.chainComplexMap_comp_smallSingularSubcomplex_chainComplexπ_eq_zero
                _ _ hf (R ⊗ S))).trans comp_zero

/-- **The relative shuffle map** `C(X, A; R) ⊗ C(Y, B; S) ⟶ C(X × Y; A × Y + X × B; R ⊗ S)`,
descending `TopCat.shuffle X Y R S` to chains relative to `fst⁻¹(A)` and `snd⁻¹(B)`. -/
def relativeShuffle :
    (TopPair.ofSubset A).singularChainComplex R ⊗ (TopPair.ofSubset B).singularChainComplex S ⟶
      ((X ⊗ Y).smallSingularSubcomplex ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.chainComplex
        (R ⊗ S) :=
  (CokernelCofork.IsColimit.desc'
    (shortExact_tensorLeftShortComplex ((TopPair.ofSubset A).singularChainComplex R)
      ((TopPair.ofSubset B).shortExact_singularChainComplexShortComplex S)).gIsCokernel
    (leftRelativeShuffle X Y A B R S)
    (id_tensorHom_chainComplexMap_comp_leftRelativeShuffle X Y A B R S)).val

/-- `relativeShuffle` is characterized by precomposing with `π_A ⊗ π_B`. -/
@[reassoc (attr := simp)]
lemma singularChainComplexπ_tensorHom_relativeShuffle :
    ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
        (TopPair.ofSubset B).singularChainComplexπ S) ≫ relativeShuffle X Y A B R S =
      shuffle X Y R S ≫
        ((X ⊗ Y).smallSingularSubcomplex ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.chainComplexπ
          (R ⊗ S) := by
  let : MonoidalCategory (ChainComplex C ℕ) := monoidalCategory C (ComplexShape.down ℕ)
  have hdesc : (𝟙 ((TopPair.ofSubset A).singularChainComplex R) ⊗ₘ
      (TopPair.ofSubset B).singularChainComplexπ S) ≫ relativeShuffle X Y A B R S =
      leftRelativeShuffle X Y A B R S :=
    (CokernelCofork.IsColimit.desc'
      (shortExact_tensorLeftShortComplex ((TopPair.ofSubset A).singularChainComplex R)
        ((TopPair.ofSubset B).shortExact_singularChainComplexShortComplex S)).gIsCokernel _
      (id_tensorHom_chainComplexMap_comp_leftRelativeShuffle X Y A B R S)).property
  rw [← tensor_id_comp_id_tensor ((TopPair.ofSubset B).singularChainComplexπ S)
      ((TopPair.ofSubset A).singularChainComplexπ R),
    Category.assoc, hdesc]
  exact singularChainComplexπ_tensorHom_id_leftRelativeShuffle X Y A B R S

end Fixed

/-- **Naturality of `relativeShuffle`** in maps carrying `A` into `A'` and `B` into `B'`. -/
@[reassoc]
lemma relativeShuffle_naturality {X Y X' Y' : TopCat.{w}} {A : Set X} {B : Set Y}
    {A' : Set X'} {B' : Set Y'} (f : X ⟶ X') (g : Y ⟶ Y')
    (hf : Set.MapsTo f A A') (hg : Set.MapsTo g B B') (R S : C) :
    (TopPair.singularChainComplexMap (TopPair.ofSubsetMap f hf) R ⊗ₘ
        TopPair.singularChainComplexMap (TopPair.ofSubsetMap g hg) S) ≫
        relativeShuffle X' Y' A' B' R S =
      relativeShuffle X Y A B R S ≫
        SSetPair.chainComplexMap (smallSingularSubcomplexPairMap (f ⊗ₘ g)
          (mapsTo_tensorHom_preimage_fst f g hf) (mapsTo_tensorHom_preimage_snd f g hg))
          (R ⊗ S) := by
  let : MonoidalCategory (ChainComplex C ℕ) := monoidalCategory C (ComplexShape.down ℕ)
  rw [← cancel_epi ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
    (TopPair.ofSubset B).singularChainComplexπ S)]
  have hπ := SSetPair.chainComplexπ_naturality (R ⊗ S) (smallSingularSubcomplexPairMap (f ⊗ₘ g)
    (mapsTo_tensorHom_preimage_fst f g hf) (mapsTo_tensorHom_preimage_snd f g hg))
  have hA := TopPair.singularChainComplexπ_pair_naturality (TopPair.ofSubsetMap f hf) R
  have hB := TopPair.singularChainComplexπ_pair_naturality (TopPair.ofSubsetMap g hg) S
  rw [smallSingularSubcomplexPairMap_right] at hπ
  rw [TopPair.ofSubsetMap_fst] at hA hB
  refine (Category.assoc _ _ _).symm.trans <|
    (eq_whisker (TauCeti.tensorHom_comp_tensorHom_eq hA.symm hB.symm) _).trans <|
      (Category.assoc _ _ _).trans <| Eq.trans ?_
        ((Category.assoc _ _ _).symm.trans
          (singularChainComplexπ_tensorHom_relativeShuffle_assoc X Y A B R S _).symm)
  calc (SSet.chainComplexMap (toSSet.map f) R ⊗ₘ SSet.chainComplexMap (toSSet.map g) S) ≫
          ((TopPair.ofSubset A').singularChainComplexπ R ⊗ₘ
            (TopPair.ofSubset B').singularChainComplexπ S) ≫
          relativeShuffle X' Y' A' B' R S
      = (SSet.chainComplexMap (toSSet.map f) R ⊗ₘ SSet.chainComplexMap (toSSet.map g) S) ≫
          shuffle X' Y' R S ≫
          ((X' ⊗ Y').smallSingularSubcomplex
              ![fst X' Y' ⁻¹' A', snd X' Y' ⁻¹' B']).pair.chainComplexπ (R ⊗ S) :=
        whisker_eq _ (singularChainComplexπ_tensorHom_relativeShuffle X' Y' A' B' R S)
    _ = shuffle X Y R S ≫ SSet.chainComplexMap (toSSet.map (f ⊗ₘ g)) (R ⊗ S) ≫
          ((X' ⊗ Y').smallSingularSubcomplex
              ![fst X' Y' ⁻¹' A', snd X' Y' ⁻¹' B']).pair.chainComplexπ (R ⊗ S) :=
        shuffle_naturality_assoc f g R S _
    _ = shuffle X Y R S ≫
          ((X ⊗ Y).smallSingularSubcomplex
              ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.chainComplexπ (R ⊗ S) ≫
          SSetPair.chainComplexMap (smallSingularSubcomplexPairMap (f ⊗ₘ g)
            (mapsTo_tensorHom_preimage_fst f g hf) (mapsTo_tensorHom_preimage_snd f g hg))
            (R ⊗ S) :=
        whisker_eq _ hπ

/-- **Naturality of the relative shuffle map** in both coefficient objects. -/
@[reassoc]
lemma relativeShuffle_coefficient_naturality (X Y : TopCat.{w}) (A : Set X) (B : Set Y)
    {R S R' S' : C} (φ : R ⟶ R') (ψ : S ⟶ S') :
    (((SSetPair.chainComplexFunctor C).map φ).app (TopPair.toSSetPair.obj (TopPair.ofSubset A)) ⊗ₘ
        ((SSetPair.chainComplexFunctor C).map ψ).app
          (TopPair.toSSetPair.obj (TopPair.ofSubset B))) ≫
        relativeShuffle X Y A B R' S' =
      relativeShuffle X Y A B R S ≫
        ((SSetPair.chainComplexFunctor C).map (φ ⊗ₘ ψ)).app
          ((X ⊗ Y).smallSingularSubcomplex ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair := by
  let : MonoidalCategory (ChainComplex C ℕ) := monoidalCategory C (ComplexShape.down ℕ)
  rw [← cancel_epi ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
    (TopPair.ofSubset B).singularChainComplexπ S)]
  have hπ := NatTrans.congr_app ((SSetPair.chainComplexFunctorπ C).naturality (φ ⊗ₘ ψ))
    ((X ⊗ Y).smallSingularSubcomplex ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair
  have hA := NatTrans.congr_app ((SSetPair.chainComplexFunctorπ C).naturality φ).symm
    (TopPair.toSSetPair.obj (TopPair.ofSubset A))
  have hB := NatTrans.congr_app ((SSetPair.chainComplexFunctorπ C).naturality ψ).symm
    (TopPair.toSSetPair.obj (TopPair.ofSubset B))
  refine (Category.assoc _ _ _).symm.trans <|
    (eq_whisker (TauCeti.tensorHom_comp_tensorHom_eq hA hB) _).trans <|
      (Category.assoc _ _ _).trans <| Eq.trans ?_
        ((Category.assoc _ _ _).symm.trans
          (singularChainComplexπ_tensorHom_relativeShuffle_assoc X Y A B R S _).symm)
  calc (((SSet.chainComplexFunctor C).map φ).app (toSSet.obj X) ⊗ₘ
            ((SSet.chainComplexFunctor C).map ψ).app (toSSet.obj Y)) ≫
          ((TopPair.ofSubset A).singularChainComplexπ R' ⊗ₘ
            (TopPair.ofSubset B).singularChainComplexπ S') ≫
          relativeShuffle X Y A B R' S'
      = (((SSet.chainComplexFunctor C).map φ).app (toSSet.obj X) ⊗ₘ
            ((SSet.chainComplexFunctor C).map ψ).app (toSSet.obj Y)) ≫
          shuffle X Y R' S' ≫
          ((X ⊗ Y).smallSingularSubcomplex
              ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.chainComplexπ (R' ⊗ S') :=
        whisker_eq _ (singularChainComplexπ_tensorHom_relativeShuffle X Y A B R' S')
    _ = shuffle X Y R S ≫ ((SSet.chainComplexFunctor C).map (φ ⊗ₘ ψ)).app (toSSet.obj (X ⊗ Y)) ≫
          ((X ⊗ Y).smallSingularSubcomplex
              ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.chainComplexπ (R' ⊗ S') :=
        shuffle_coefficient_naturality_assoc X Y φ ψ _
    _ = shuffle X Y R S ≫
          ((X ⊗ Y).smallSingularSubcomplex
              ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.chainComplexπ (R ⊗ S) ≫
          ((SSetPair.chainComplexFunctor C).map (φ ⊗ₘ ψ)).app
            ((X ⊗ Y).smallSingularSubcomplex ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair :=
        whisker_eq _ hπ

section Homotopy

variable (X Y : TopCat.{w}) (A : Set X) (B : Set Y) (R S : C)

private lemma tensorHom_f_comp_shuffleAlexanderWhitneyHomotopy_hom_comp_eq_zero
    {K' K L' L : SSet.{w}} (f : K' ⟶ K) (g : L' ⟶ L) {Z : ChainComplex C ℕ}
    (p : K.chainComplex R ⊗ L.chainComplex S ⟶ Z)
    (hp : (SSet.chainComplexMap f R ⊗ₘ SSet.chainComplexMap g S) ≫ p = 0) (i j : ℕ) :
    (SSet.chainComplexMap f R ⊗ₘ SSet.chainComplexMap g S).f i ≫
        (SSet.shuffleAlexanderWhitneyHomotopy K L R S).hom i j ≫ p.f j = 0 := by
  rw [SSet.shuffleAlexanderWhitneyHomotopy_hom_naturality_assoc R S f g i j,
    ← HomologicalComplex.comp_f, hp, HomologicalComplex.zero_f, comp_zero]

private lemma chainComplexMap_tensorHom_id_comp_shuffleAlexanderWhitneyHomotopy_hom_comp
    (i j : ℕ) :
    (SSet.chainComplexMap (toSSet.map (TopPair.ofSubset A).map) R ⊗ₘ
          𝟙 ((toSSet.obj Y).chainComplex S)).f i ≫
        (SSet.shuffleAlexanderWhitneyHomotopy (toSSet.obj X) (toSSet.obj Y) R S).hom i j ≫
        ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
          (TopPair.ofSubset B).singularChainComplexπ S).f j = 0 := by
  let : MonoidalCategory (ChainComplex C ℕ) := monoidalCategory C (ComplexShape.down ℕ)
  have h := tensorHom_f_comp_shuffleAlexanderWhitneyHomotopy_hom_comp_eq_zero R S
    (toSSet.map (TopPair.ofSubset A).map) (𝟙 (toSSet.obj Y))
    ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
      (TopPair.ofSubset B).singularChainComplexπ S)
    ((tensorHom_comp_tensorHom _ _ _ _).trans <| by
      rw [TopPair.chainComplexMap_comp_singularChainComplexπ]
      exact zero_tensorHom _) i j
  simp only [CategoryTheory.Functor.map_id] at h
  exact h

private lemma id_tensorHom_chainComplexMap_comp_shuffleAlexanderWhitneyHomotopy_hom_comp
    (i j : ℕ) :
    (𝟙 ((toSSet.obj X).chainComplex R) ⊗ₘ
          SSet.chainComplexMap (toSSet.map (TopPair.ofSubset B).map) S).f i ≫
        (SSet.shuffleAlexanderWhitneyHomotopy (toSSet.obj X) (toSSet.obj Y) R S).hom i j ≫
        ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
          (TopPair.ofSubset B).singularChainComplexπ S).f j = 0 := by
  let : MonoidalCategory (ChainComplex C ℕ) := monoidalCategory C (ComplexShape.down ℕ)
  have h := tensorHom_f_comp_shuffleAlexanderWhitneyHomotopy_hom_comp_eq_zero R S
    (𝟙 (toSSet.obj X)) (toSSet.map (TopPair.ofSubset B).map)
    ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
      (TopPair.ofSubset B).singularChainComplexπ S)
    ((tensorHom_comp_tensorHom _ _ _ _).trans <| by
      rw [TopPair.chainComplexMap_comp_singularChainComplexπ]
      exact tensorHom_zero _) i j
  simp only [CategoryTheory.Functor.map_id] at h
  exact h

private def leftRelativeShuffleAlexanderWhitneyHomotopy :
    _root_.Homotopy
      ((tensorLeftShortComplex ((TopPair.ofSubset A).singularChainComplex R)
          ((TopPair.ofSubset B).singularChainComplexShortComplex S)).g ≫
        (relativeShuffle X Y A B R S ≫ relativeAlexanderWhitney X Y A B R S))
      (tensorLeftShortComplex ((TopPair.ofSubset A).singularChainComplex R)
        ((TopPair.ofSubset B).singularChainComplexShortComplex S)).g := by
  let S₁ := tensorRightShortComplex ((toSSet.obj Y).chainComplex S)
    ((TopPair.ofSubset A).singularChainComplexShortComplex R)
  have hfac : S₁.g ≫ (tensorLeftShortComplex ((TopPair.ofSubset A).singularChainComplex R)
      ((TopPair.ofSubset B).singularChainComplexShortComplex S)).g =
      ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
        (TopPair.ofSubset B).singularChainComplexπ S) := by
    let : MonoidalCategory (ChainComplex C ℕ) := monoidalCategory C (ComplexShape.down ℕ)
    exact tensor_id_comp_id_tensor ((TopPair.ofSubset B).singularChainComplexπ S)
      ((TopPair.ofSubset A).singularChainComplexπ R)
  refine _root_.Homotopy.descCokernel
    (SSet.shuffleAlexanderWhitneyHomotopy (toSSet.obj X) (toSSet.obj Y) R S) S₁.f S₁.g
    ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ (TopPair.ofSubset B).singularChainComplexπ S)
    (fun i ↦ (comp_f _ _ i).symm.trans ((congr_hom S₁.zero i).trans (zero_f _ _ i)))
    (fun i ↦ ((shortExact_iff_degreewise_shortExact S₁).1
      (shortExact_tensorRightShortComplex ((toSSet.obj Y).chainComplex S) _
        ((TopPair.ofSubset A).shortExact_singularChainComplexShortComplex R)) i).gIsCokernel)
    (chainComplexMap_tensorHom_id_comp_shuffleAlexanderWhitneyHomotopy_hom_comp X Y A B R S)
    ?_ (hfac.trans (Category.id_comp _).symm)
  exact (Category.assoc _ _ _).symm.trans <| (eq_whisker hfac _).trans <|
    (singularChainComplexπ_tensorHom_relativeShuffle_assoc X Y A B R S _).trans <|
      (Category.assoc _ _ _).trans <|
        (whisker_eq _ (chainComplexπ_relativeAlexanderWhitney X Y A B R S)).trans <|
          (Category.assoc _ _ _).symm.trans <| eq_whisker (shuffle_alexanderWhitney X Y R S) _

private lemma π_leftRelativeShuffleAlexanderWhitneyHomotopy_hom (i j : ℕ) :
    ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ 𝟙 ((toSSet.obj Y).chainComplex S)).f i ≫
        (leftRelativeShuffleAlexanderWhitneyHomotopy X Y A B R S).hom i j =
      (SSet.shuffleAlexanderWhitneyHomotopy (toSSet.obj X) (toSSet.obj Y) R S).hom i j ≫
        ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
          (TopPair.ofSubset B).singularChainComplexπ S).f j := by
  unfold leftRelativeShuffleAlexanderWhitneyHomotopy
  exact _root_.Homotopy.π_descCokernel_hom _ _ _ _ _ _ _ _ _ i j

/-- **The relative Eilenberg–Zilber chain homotopy** `AW ∘ shuffle ≃ id` on
`C(X, A; R) ⊗ C(Y, B; S)`. -/
def relativeShuffleAlexanderWhitneyHomotopy :
    _root_.Homotopy
      (relativeShuffle X Y A B R S ≫ relativeAlexanderWhitney X Y A B R S) (𝟙 _) :=
  let S₂ := tensorLeftShortComplex ((TopPair.ofSubset A).singularChainComplex R)
    ((TopPair.ofSubset B).singularChainComplexShortComplex S)
  _root_.Homotopy.descCokernel
    (leftRelativeShuffleAlexanderWhitneyHomotopy X Y A B R S) S₂.f S₂.g (𝟙 _)
    (fun i ↦ (comp_f _ _ i).symm.trans ((congr_hom S₂.zero i).trans (zero_f _ _ i)))
    (fun i ↦ ((shortExact_iff_degreewise_shortExact S₂).1
      (shortExact_tensorLeftShortComplex ((TopPair.ofSubset A).singularChainComplex R)
        ((TopPair.ofSubset B).shortExact_singularChainComplexShortComplex S)) i).gIsCokernel)
    (fun i j ↦ by
      let : MonoidalCategory (ChainComplex C ℕ) := monoidalCategory C (ComplexShape.down ℕ)
      let pA := (TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
        𝟙 ((toSSet.obj (TopPair.ofSubset B).snd).chainComplex S)
      have hcomm : pA ≫ S₂.f =
          (𝟙 ((toSSet.obj X).chainComplex R) ⊗ₘ
            SSet.chainComplexMap (toSSet.map (TopPair.ofSubset B).map) S) ≫
            ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
              𝟙 ((toSSet.obj Y).chainComplex S)) := by
        change ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ 𝟙 _) ≫ (𝟙 _ ⊗ₘ _) =
          (𝟙 _ ⊗ₘ _) ≫ ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ 𝟙 _)
        exact (tensor_id_comp_id_tensor _ _).trans (id_tensor_comp_tensor_id _ _).symm
      rw [HomologicalComplex.id_f, Category.comp_id]
      have hcomm_i := congrArg (HomologicalComplex.Hom.f · i) hcomm
      have hpA : pA.f i ≫ S₂.f.f i ≫
          (leftRelativeShuffleAlexanderWhitneyHomotopy X Y A B R S).hom i j = 0 :=
        (Category.assoc _ _ _).symm.trans <| (eq_whisker hcomm_i _).trans <|
          (Category.assoc _ _ _).trans <|
            (whisker_eq _ (π_leftRelativeShuffleAlexanderWhitneyHomotopy_hom X Y A B R S i j)).trans
              (id_tensorHom_chainComplexMap_comp_shuffleAlexanderWhitneyHomotopy_hom_comp
                X Y A B R S i j)
      exact (cancel_epi (pA.f i)).1 (hpA.trans comp_zero.symm))
    (Category.comp_id _).symm rfl

/-- Precomposing `(relativeShuffleAlexanderWhitneyHomotopy ...).hom i j` with `π_A ⊗ π_B`
intertwines it with `SSet.shuffleAlexanderWhitneyHomotopy`. -/
@[reassoc (attr := simp)]
lemma singularChainComplexπ_tensorHom_f_relativeShuffleAlexanderWhitneyHomotopy_hom (i j : ℕ) :
    ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
        (TopPair.ofSubset B).singularChainComplexπ S).f i ≫
      (relativeShuffleAlexanderWhitneyHomotopy X Y A B R S).hom i j =
      (SSet.shuffleAlexanderWhitneyHomotopy (toSSet.obj X) (toSSet.obj Y) R S).hom i j ≫
        ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
          (TopPair.ofSubset B).singularChainComplexπ S).f j := by
  let : MonoidalCategory (ChainComplex C ℕ) := monoidalCategory C (ComplexShape.down ℕ)
  have hdesc : (𝟙 ((TopPair.ofSubset A).singularChainComplex R) ⊗ₘ
      (TopPair.ofSubset B).singularChainComplexπ S).f i ≫
      (relativeShuffleAlexanderWhitneyHomotopy X Y A B R S).hom i j =
      (leftRelativeShuffleAlexanderWhitneyHomotopy X Y A B R S).hom i j := by
    unfold relativeShuffleAlexanderWhitneyHomotopy
    exact (_root_.Homotopy.π_descCokernel_hom _ _ _ _ _ _ _ _ _ i j).trans (Category.comp_id _)
  conv_lhs =>
    rw [← tensor_id_comp_id_tensor ((TopPair.ofSubset B).singularChainComplexπ S)
        ((TopPair.ofSubset A).singularChainComplexπ R),
      HomologicalComplex.comp_f, Category.assoc, hdesc]
  exact π_leftRelativeShuffleAlexanderWhitneyHomotopy_hom X Y A B R S i j

/-- On homology, `relativeShuffle` followed by `relativeAlexanderWhitney` is the identity. -/
@[reassoc (attr := simp)]
lemma homologyMap_relativeShuffle_comp_homologyMap_relativeAlexanderWhitney (n : ℕ) :
    homologyMap (relativeShuffle X Y A B R S) n ≫
        homologyMap (relativeAlexanderWhitney X Y A B R S) n = 𝟙 _ := by
  rw [← homologyMap_comp, (relativeShuffleAlexanderWhitneyHomotopy X Y A B R S).homologyMap_eq n,
    homologyMap_id]

private lemma chainComplexMap_smallSingularSubcomplex_ι_comp_ambientHomotopy_hom_comp
    (i j : ℕ) :
    (SSet.chainComplexMap ((X ⊗ Y).smallSingularSubcomplex
        ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).ι (R ⊗ S)).f i ≫
      (alexanderWhitneyShuffleHomotopy X Y R S).hom i j ≫
      (((X ⊗ Y).smallSingularSubcomplex ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.chainComplexπ
        (R ⊗ S)).f j = 0 := by
  ext σ
  simp only [comp_zero, SSet.ι_chainComplexMap_f_assoc]
  obtain ⟨k, hk⟩ := (mem_smallSingularSubcomplex_iff _ _ _).1 σ.property
  have hcomp {X' Y' : TopCat.{w}} (f : X' ⟶ X) (g : Y' ⟶ Y)
      (τ : (toSSet.obj (X' ⊗ Y')).obj (Opposite.op ⟨i⟩))
      (hτ : (toSSet.map (f ⊗ₘ g)).app _ τ = σ.val)
      (hzero : SSet.chainComplexMap (toSSet.map (f ⊗ₘ g)) (R ⊗ S) ≫
        ((X ⊗ Y).smallSingularSubcomplex ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.chainComplexπ
          (R ⊗ S) = 0) :
      (toSSet.obj (X ⊗ Y)).ιChainComplex σ.val ≫
        (alexanderWhitneyShuffleHomotopy X Y R S).hom i j ≫
        (((X ⊗ Y).smallSingularSubcomplex ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.chainComplexπ
          (R ⊗ S)).f j = 0 := by
    have hnat := alexanderWhitneyShuffleHomotopy_hom_naturality f g (R := R) (S := S) i j
    have hz : (SSet.chainComplexMap (toSSet.map (f ⊗ₘ g)) (R ⊗ S)).f j ≫
        (((X ⊗ Y).smallSingularSubcomplex ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.chainComplexπ
          (R ⊗ S)).f j = 0 := by
      have hz₀ := congrArg (HomologicalComplex.Hom.f · j) hzero
      rwa [HomologicalComplex.zero_f] at hz₀
    rw [← hτ, ← SSet.ι_chainComplexMap_f_assoc]
    exact (whisker_eq _ ((Category.assoc _ _ _).symm.trans <| (eq_whisker hnat _).trans <|
      (Category.assoc _ _ _).trans <| (whisker_eq _ hz).trans comp_zero)).trans comp_zero
  fin_cases k
  · have hind : Topology.IsInducing ((TopPair.ofSubset A).map ⊗ₘ 𝟙 Y) :=
      (TopPair.ofSubset A).isEmbedding_map.isInducing.prodMap Topology.IsInducing.id
    obtain ⟨τ, hτ⟩ := (hind.mem_range_toSSet_map_app_iff _ σ.val).2
      (hk.trans fun x hx ↦ ⟨(⟨fst X Y x, hx⟩, snd X Y x), rfl⟩)
    exact hcomp (TopPair.ofSubset A).map (𝟙 Y) τ hτ
      (TauCeti.chainComplexMap_comp_smallSingularSubcomplex_chainComplexπ_eq_zero
        ![fst X Y ⁻¹' A, snd X Y ⁻¹' B] ((TopPair.ofSubset A).map ⊗ₘ 𝟙 Y) (i := 0)
        (fun z ↦ mapsTo_tensorHom_preimage_fst (A := Set.univ) (TopPair.ofSubset A).map (𝟙 Y)
          (fun w _ ↦ w.property) (Set.mem_preimage.2 (Set.mem_univ _))) (R ⊗ S))
  · have hind : Topology.IsInducing (𝟙 X ⊗ₘ (TopPair.ofSubset B).map) :=
      Topology.IsInducing.id.prodMap (TopPair.ofSubset B).isEmbedding_map.isInducing
    obtain ⟨τ, hτ⟩ := (hind.mem_range_toSSet_map_app_iff _ σ.val).2
      (hk.trans fun x hx ↦ ⟨(fst X Y x, ⟨snd X Y x, hx⟩), rfl⟩)
    exact hcomp (𝟙 X) (TopPair.ofSubset B).map τ hτ
      (TauCeti.chainComplexMap_comp_smallSingularSubcomplex_chainComplexπ_eq_zero
        ![fst X Y ⁻¹' A, snd X Y ⁻¹' B] (𝟙 X ⊗ₘ (TopPair.ofSubset B).map) (i := 1)
        (fun z ↦ mapsTo_tensorHom_preimage_snd (B := Set.univ) (𝟙 X) (TopPair.ofSubset B).map
          (fun w _ ↦ w.property) (Set.mem_preimage.2 (Set.mem_univ _))) (R ⊗ S))

/-- **The relative Eilenberg–Zilber chain homotopy** `shuffle ∘ AW ≃ id` on
`C(X × Y; A × Y + X × B; R ⊗ S)`. -/
def relativeAlexanderWhitneyShuffleHomotopy :
    _root_.Homotopy
      (relativeAlexanderWhitney X Y A B R S ≫ relativeShuffle X Y A B R S) (𝟙 _) :=
  _root_.Homotopy.descCokernel
    (alexanderWhitneyShuffleHomotopy X Y R S)
    (SSet.chainComplexMap
      ((X ⊗ Y).smallSingularSubcomplex ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.hom (R ⊗ S))
    (((X ⊗ Y).smallSingularSubcomplex ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.chainComplexπ (R ⊗ S))
    (((X ⊗ Y).smallSingularSubcomplex ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.chainComplexπ (R ⊗ S))
    (fun i ↦ ((X ⊗ Y).smallSingularSubcomplex
      ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.chainComplex_condition_f (R ⊗ S) i)
    (fun i ↦ ((X ⊗ Y).smallSingularSubcomplex
      ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.isColimitCokernelCoforkChainComplexX (R ⊗ S) i)
    (chainComplexMap_smallSingularSubcomplex_ι_comp_ambientHomotopy_hom_comp X Y A B R S)
    ((Category.assoc _ _ _).symm.trans <|
      (eq_whisker (chainComplexπ_relativeAlexanderWhitney X Y A B R S) _).trans <|
      (Category.assoc _ _ _).trans <|
      (whisker_eq _ (singularChainComplexπ_tensorHom_relativeShuffle X Y A B R S)).trans
      (Category.assoc _ _ _).symm)
    ((Category.comp_id _).trans (Category.id_comp _).symm)

/-- **The relative Eilenberg–Zilber theorem**: `TopCat.relativeAlexanderWhitney` and
`TopCat.relativeShuffle` form a chain homotopy equivalence between `C(X × Y; A × Y + X × B; R ⊗ S)`
and `C(X, A; R) ⊗ C(Y, B; S)`. -/
def relativeEilenbergZilberHomotopyEquiv :
    _root_.HomotopyEquiv
      (((X ⊗ Y).smallSingularSubcomplex ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.chainComplex (R ⊗ S))
      ((TopPair.ofSubset A).singularChainComplex R ⊗
        (TopPair.ofSubset B).singularChainComplex S) where
  hom := relativeAlexanderWhitney X Y A B R S
  inv := relativeShuffle X Y A B R S
  homotopyHomInvId := relativeAlexanderWhitneyShuffleHomotopy X Y A B R S
  homotopyInvHomId := relativeShuffleAlexanderWhitneyHomotopy X Y A B R S

@[simp]
lemma relativeEilenbergZilberHomotopyEquiv_hom :
    (relativeEilenbergZilberHomotopyEquiv X Y A B R S).hom = relativeAlexanderWhitney X Y A B R S :=
  (rfl)

@[simp]
lemma relativeEilenbergZilberHomotopyEquiv_inv :
    (relativeEilenbergZilberHomotopyEquiv X Y A B R S).inv = relativeShuffle X Y A B R S :=
  (rfl)

/-- `TopCat.relativeShuffle` is a quasi-isomorphism, being the inverse of
`TopCat.relativeEilenbergZilberHomotopyEquiv`. -/
instance quasiIso_relativeShuffle [CategoryWithHomology C] :
    QuasiIso (relativeShuffle X Y A B R S) := by
  rw [← relativeEilenbergZilberHomotopyEquiv_inv]
  infer_instance

/-- On homology, `relativeAlexanderWhitney` followed by `relativeShuffle` is the identity. -/
@[reassoc (attr := simp)]
lemma homologyMap_relativeAlexanderWhitney_comp_homologyMap_relativeShuffle (n : ℕ) :
    homologyMap (relativeAlexanderWhitney X Y A B R S) n ≫
        homologyMap (relativeShuffle X Y A B R S) n = 𝟙 _ := by
  rw [← homologyMap_comp,
    (relativeAlexanderWhitneyShuffleHomotopy X Y A B R S).homologyMap_eq n, homologyMap_id]

end Homotopy

/-- `relativeShuffle` followed by `smallSingularSubcomplexPairToUnion` agrees with
`TopCat.shufflePair`. -/
@[reassoc]
lemma relativeShuffle_comp_smallSingularSubcomplexPairToUnion
    (X Y : TopCat.{w}) (A : Set X) (B : Set Y) (R S : C) :
    relativeShuffle X Y A B R S ≫
      SSetPair.chainComplexMap
        (smallSingularSubcomplexPairToUnion (fst X Y ⁻¹' A) (snd X Y ⁻¹' B)) (R ⊗ S) =
      shufflePair X Y A B R S := by
  rw [← cancel_epi ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
      (TopPair.ofSubset B).singularChainComplexπ S)]
  exact (singularChainComplexπ_tensorHom_relativeShuffle_assoc X Y A B R S _).trans <|
    (Category.assoc _ _ _).trans <|
      (whisker_eq _ (chainComplexπ_smallSingularSubcomplexPairToUnion (R ⊗ S)
        (fst X Y ⁻¹' A) (snd X Y ⁻¹' B))).trans
        (singularChainComplexπ_tensorHom_singularChainComplexπ_shufflePair X Y A B R S).symm

section Basic

variable (X Y : TopCat.{w}) (R S : C) (A : Set X) (B : Set Y) (p q n : ℕ) (h : p + q = n)
  [PreservesColimitsOfShape WalkingParallelPair
    (tensorLeft (((TopPair.ofSubset A).singularChainComplex R).homology p))]
  [PreservesColimitsOfShape WalkingParallelPair
    (tensorRight (((TopPair.ofSubset B).singularChainComplex S).cycles q))]
  [PreservesColimitsOfShape WalkingParallelPair
    (tensorRight (((TopPair.ofSubset B).singularChainComplex S).X ((ComplexShape.down ℕ).prev q)))]

/-- **The relative homology cross product**
`Hₚ(X, A; R) ⊗ H_q(Y, B; S) ⟶ Hₙ(X × Y, A × Y ∪ X × B; R ⊗ S)` (`p + q = n`). -/
def singularRelativeHomologyCross :
    (TopPair.ofSubset A).singularHomology R p ⊗ (TopPair.ofSubset B).singularHomology S q ⟶
      (TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)).singularHomology (R ⊗ S) n :=
  homologyCross ((TopPair.ofSubset A).singularChainComplex R)
      ((TopPair.ofSubset B).singularChainComplex S) p q n h ≫
    homologyMap (shufflePair X Y A B R S) n

/-- Definitional unfolding of `TopCat.singularRelativeHomologyCross`. -/
lemma singularRelativeHomologyCross_def :
    singularRelativeHomologyCross X Y R S A B p q n h =
      homologyCross ((TopPair.ofSubset A).singularChainComplex R)
          ((TopPair.ofSubset B).singularChainComplex S) p q n h ≫
        homologyMap (shufflePair X Y A B R S) n :=
  (rfl)

/-- Cycle evaluation of `TopCat.singularRelativeHomologyCross` in `(X × Y, A × Y ∪ X × B)`. -/
@[reassoc (attr := simp)]
lemma homologyπ_tensorHom_singularRelativeHomologyCross :
    (((TopPair.ofSubset A).singularChainComplex R).homologyπ p ⊗ₘ
        ((TopPair.ofSubset B).singularChainComplex S).homologyπ q) ≫
        singularRelativeHomologyCross X Y R S A B p q n h =
      cyclesCross ((TopPair.ofSubset A).singularChainComplex R)
          ((TopPair.ofSubset B).singularChainComplex S) p q n h ≫
        cyclesMap (shufflePair X Y A B R S) n ≫
          ((TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)).singularChainComplex
            (R ⊗ S)).homologyπ n :=
  (homologyπ_tensorHom_homologyCross_assoc _ _ p q n h _).trans
    (cyclesCross _ _ p q n h ≫= homologyπ_naturality (shufflePair X Y A B R S) n)

/-- **Compatibility with the absolute homology cross product** along `singularHomologyπ`. -/
@[reassoc (attr := simp)]
lemma singularHomologyπ_tensorHom_singularRelativeHomologyCross
    [PreservesColimitsOfShape WalkingParallelPair (tensorLeft
      (((toSSet.obj X).chainComplex R).homology p))]
    [PreservesColimitsOfShape WalkingParallelPair (tensorRight
      (((toSSet.obj Y).chainComplex S).cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair (tensorRight
      (((toSSet.obj Y).chainComplex S).X ((ComplexShape.down ℕ).prev q)))] :
    ((TopPair.ofSubset A).singularHomologyπ R p ⊗ₘ (TopPair.ofSubset B).singularHomologyπ S q) ≫
        singularRelativeHomologyCross X Y R S A B p q n h =
      singularHomologyCross X Y R S p q n h ≫
        (TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)).singularHomologyπ (R ⊗ S) n := by
  rw [singularRelativeHomologyCross_def]
  exact (homologyCross_comp_homologyMap_naturality
    (K := (toSSet.obj X).chainComplex R) (L := (toSSet.obj Y).chainComplex S)
    ((TopPair.ofSubset A).singularChainComplexπ R) ((TopPair.ofSubset B).singularChainComplexπ S)
    p q n h (shufflePair X Y A B R S) (shuffle X Y R S)
    ((TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)).singularChainComplexπ (R ⊗ S))
    (singularChainComplexπ_tensorHom_singularChainComplexπ_shufflePair X Y A B R S)).trans
    ((Category.assoc _ _ _).symm.trans
      (eq_whisker (singularHomologyCross_def X Y R S p q n h).symm _))

end Basic

/-- **Naturality of `singularRelativeHomologyCross`** in pair maps `(f, g)`. -/
@[reassoc]
lemma singularRelativeHomologyCross_naturality
    {X Y X' Y' : TopCat.{w}} {A : Set X} {B : Set Y} {A' : Set X'} {B' : Set Y'}
    (f : X ⟶ X') (g : Y ⟶ Y') (hf : Set.MapsTo f A A') (hg : Set.MapsTo g B B')
    (R S : C) (p q n : ℕ) (h : p + q = n)
    [PreservesColimitsOfShape WalkingParallelPair (tensorLeft
      (((TopPair.ofSubset A).singularChainComplex R).homology p))]
    [PreservesColimitsOfShape WalkingParallelPair (tensorRight
      (((TopPair.ofSubset B).singularChainComplex S).cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair (tensorRight
      (((TopPair.ofSubset B).singularChainComplex S).X ((ComplexShape.down ℕ).prev q)))]
    [PreservesColimitsOfShape WalkingParallelPair (tensorLeft
      (((TopPair.ofSubset A').singularChainComplex R).homology p))]
    [PreservesColimitsOfShape WalkingParallelPair (tensorRight
      (((TopPair.ofSubset B').singularChainComplex S).cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair (tensorRight
      (((TopPair.ofSubset B').singularChainComplex S).X ((ComplexShape.down ℕ).prev q)))] :
    (TopPair.singularHomologyMap (TopPair.ofSubsetMap f hf) R p ⊗ₘ
        TopPair.singularHomologyMap (TopPair.ofSubsetMap g hg) S q) ≫
        singularRelativeHomologyCross X' Y' R S A' B' p q n h =
      singularRelativeHomologyCross X Y R S A B p q n h ≫
        TopPair.singularHomologyMap
          (TopPair.ofSubsetMap (f ⊗ₘ g) (mapsTo_tensorHom_preimage_union f g hf hg)) (R ⊗ S) n := by
  rw [singularRelativeHomologyCross_def, singularRelativeHomologyCross_def]
  exact (homologyCross_comp_homologyMap_naturality
    (TopPair.singularChainComplexMap (TopPair.ofSubsetMap f hf) R)
    (TopPair.singularChainComplexMap (TopPair.ofSubsetMap g hg) S) p q n h
    (shufflePair X' Y' A' B' R S) (shufflePair X Y A B R S)
    (TopPair.singularChainComplexMap
      (TopPair.ofSubsetMap (f ⊗ₘ g) (mapsTo_tensorHom_preimage_union f g hf hg)) (R ⊗ S))
    (shufflePair_naturality X Y A B R S f hf g hg)).trans (Category.assoc _ _ _).symm

/-- **Naturality of `singularRelativeHomologyCross`** in both coefficient objects. -/
@[reassoc]
lemma singularRelativeHomologyCross_coefficient_naturality
    (X Y : TopCat.{w}) (A : Set X) (B : Set Y) {R S R' S' : C} (φ : R ⟶ R') (ψ : S ⟶ S')
    (p q n : ℕ) (h : p + q = n)
    [PreservesColimitsOfShape WalkingParallelPair (tensorLeft
      (((TopPair.ofSubset A).singularChainComplex R).homology p))]
    [PreservesColimitsOfShape WalkingParallelPair (tensorRight
      (((TopPair.ofSubset B).singularChainComplex S).cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair (tensorRight
      (((TopPair.ofSubset B).singularChainComplex S).X ((ComplexShape.down ℕ).prev q)))]
    [PreservesColimitsOfShape WalkingParallelPair (tensorLeft
      (((TopPair.ofSubset A).singularChainComplex R').homology p))]
    [PreservesColimitsOfShape WalkingParallelPair (tensorRight
      (((TopPair.ofSubset B).singularChainComplex S').cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair (tensorRight
      (((TopPair.ofSubset B).singularChainComplex S').X ((ComplexShape.down ℕ).prev q)))] :
    (homologyMap (((SSetPair.chainComplexFunctor C).map φ).app
        (TopPair.toSSetPair.obj (TopPair.ofSubset A))) p ⊗ₘ
      homologyMap (((SSetPair.chainComplexFunctor C).map ψ).app
        (TopPair.toSSetPair.obj (TopPair.ofSubset B))) q) ≫
        singularRelativeHomologyCross X Y R' S' A B p q n h =
      singularRelativeHomologyCross X Y R S A B p q n h ≫
        homologyMap (((SSetPair.chainComplexFunctor C).map (φ ⊗ₘ ψ)).app
          (TopPair.toSSetPair.obj (TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)))) n := by
  let u := SSetPair.chainComplexMap
    (smallSingularSubcomplexPairToUnion (fst X Y ⁻¹' A) (snd X Y ⁻¹' B)) (R ⊗ S)
  let u' := SSetPair.chainComplexMap
    (smallSingularSubcomplexPairToUnion (fst X Y ⁻¹' A) (snd X Y ⁻¹' B)) (R' ⊗ S')
  rw [singularRelativeHomologyCross_def, singularRelativeHomologyCross_def,
    ← relativeShuffle_comp_smallSingularSubcomplexPairToUnion X Y A B R' S',
    ← relativeShuffle_comp_smallSingularSubcomplexPairToUnion X Y A B R S]
  exact (homologyCross_comp_homologyMap_naturality
    (((SSetPair.chainComplexFunctor C).map φ).app (TopPair.toSSetPair.obj (TopPair.ofSubset A)))
    (((SSetPair.chainComplexFunctor C).map ψ).app (TopPair.toSSetPair.obj (TopPair.ofSubset B)))
    p q n h (relativeShuffle X Y A B R' S' ≫ u') (relativeShuffle X Y A B R S ≫ u)
    (((SSetPair.chainComplexFunctor C).map (φ ⊗ₘ ψ)).app
      (TopPair.toSSetPair.obj (TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B))))
    ((relativeShuffle_coefficient_naturality_assoc X Y A B φ ψ _).trans
      ((whisker_eq _ (((SSetPair.chainComplexFunctor C).map (φ ⊗ₘ ψ)).naturality
        (smallSingularSubcomplexPairToUnion (fst X Y ⁻¹' A) (snd X Y ⁻¹' B))).symm).trans
        (Category.assoc _ _ _).symm))).trans (Category.assoc _ _ _).symm

end TopCat
