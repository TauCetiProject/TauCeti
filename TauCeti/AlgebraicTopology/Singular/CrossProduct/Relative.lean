/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.Homology.Connecting
public import TauCeti.AlgebraicTopology.Singular.AlexanderWhitney.RelativeCup
public import TauCeti.AlgebraicTopology.Singular.CrossProduct.Basic
import TauCeti.AlgebraicTopology.Singular.Subdivision.Small.Relative
import TauCeti.CategoryTheory.Monoidal.Category

/-!
# The relative cross product in singular homology

For subsets `A ⊆ X` and `B ⊆ Y` and coefficient objects `R` and `S` in an abelian monoidal
category, `TopCat.singularRelativeHomologyCross` is the relative homology cross product

`Hₚ(X, A; R) ⊗ H_q(Y, B; S) ⟶ Hₙ(X × Y, A × Y ∪ X × B; R ⊗ S)` (`p + q = n`),

obtained by composing the algebraic cross product `HomologicalComplex.homologyCross` with the
relative Eilenberg–Mac Lane shuffle map `TopCat.relativeShuffle` and the map
`TopCat.smallSingularSubcomplexPairToUnion` from small chains to chains relative to the union.
Because the short exact sequence `0 ⟶ C(A) ⟶ C(X) ⟶ C(X, A) ⟶ 0` splits in each degree, tensoring
it with any chain complex stays short exact (`HomologicalComplex.shortExact_tensorLeftShortComplex`,
`HomologicalComplex.shortExact_tensorRightShortComplex`), so both the shuffle map and the
Eilenberg–Zilber homotopy `AW ∘ shuffle ≃ id` descend to relative chains without openness,
flatness, or Künneth assumptions.

This chain-level homotopy and relative homology cross product feed the Kronecker duality formulas
for relative cross and cup products in `TauCeti.AlgebraicTopology.Cohomology.Cup.Kronecker` and the
local homology cross product in `TauCeti.AlgebraicTopology.Singular.LocalHomology.Cross`, which in
turn establish generator preservation and reflection for local cohomology cross products and Thom
classes over arbitrary commutative rings without flatness or Künneth hypotheses.

Every construction assumes discrete colimit preservation for `tensorLeft` and `tensorRight`.
For the `WalkingParallelPair` colimit-preservation hypotheses:
* `TopCat.homologyMap_relativeShuffle_comp_homologyMap_relativeAlexanderWhitney` requires none;
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
  `TopCat.singularChainComplexπ_tensorHom_relativeShuffle` and natural in pairs
  (`TopCat.relativeShuffle_naturality`) and coefficients
  (`TopCat.relativeShuffle_coefficient_naturality`).
* `TopCat.relativeShuffleAlexanderWhitneyHomotopy`: the relative Eilenberg–Zilber chain homotopy
  `AW ∘ shuffle ≃ id` on `C(X, A; R) ⊗ C(Y, B; S)`, characterized by
  `TopCat.singularChainComplexπ_tensorHom_f_relativeShuffleAlexanderWhitneyHomotopy_hom`, giving
  `TopCat.homologyMap_relativeShuffle_comp_homologyMap_relativeAlexanderWhitney` on homology.
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

private lemma chainComplexMap_tensorHom_id_comp_shuffle_comp_chainComplexπ :
    (SSet.chainComplexMap (TopPair.toSSetPair.obj (TopPair.ofSubset A)).hom R ⊗ₘ
        𝟙 ((toSSet.obj Y).chainComplex S)) ≫ shuffle X Y R S ≫
      ((X ⊗ Y).smallSingularSubcomplex ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.chainComplexπ
        (R ⊗ S) = 0 := by
  have hnat := shuffle_naturality (TopPair.ofSubset A).map (𝟙 Y) R S
  simp only [CategoryTheory.Functor.map_id] at hnat
  have hf (z) : ((TopPair.ofSubset A).map ⊗ₘ 𝟙 Y) z ∈ ![fst X Y ⁻¹' A, snd X Y ⁻¹' B] 0 :=
    Set.mem_preimage.2 ((ConcreteCategory.congr_hom
      (tensorHom_fst (TopPair.ofSubset A).map (𝟙 Y)) z).symm ▸ (fst (of ↥A) Y z).property)
  exact (Category.assoc _ _ _).symm.trans <| (eq_whisker hnat _).trans <|
    (Category.assoc _ _ _).trans <|
      (whisker_eq _ (TauCeti.chainComplexMap_comp_smallSingularSubcomplex_chainComplexπ_eq_zero _ _
        hf _)).trans comp_zero

private def leftRelativeShuffle :
    (TopPair.ofSubset A).singularChainComplex R ⊗ (toSSet.obj Y).chainComplex S ⟶
      ((X ⊗ Y).smallSingularSubcomplex ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.chainComplex
        (R ⊗ S) :=
  (CokernelCofork.IsColimit.desc'
    (shortExact_tensorRightShortComplex ((toSSet.obj Y).chainComplex S) _
      ((TopPair.ofSubset A).shortExact_singularChainComplexShortComplex R)).gIsCokernel
    (shuffle X Y R S ≫
      ((X ⊗ Y).smallSingularSubcomplex ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.chainComplexπ (R ⊗ S))
    (chainComplexMap_tensorHom_id_comp_shuffle_comp_chainComplexπ X Y A B R S)).val

@[reassoc]
private lemma singularChainComplexπ_tensorHom_id_leftRelativeShuffle :
    ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ 𝟙 ((toSSet.obj Y).chainComplex S)) ≫
        leftRelativeShuffle X Y A B R S =
      shuffle X Y R S ≫
        ((X ⊗ Y).smallSingularSubcomplex ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.chainComplexπ
          (R ⊗ S) :=
  (CokernelCofork.IsColimit.desc'
    (shortExact_tensorRightShortComplex ((toSSet.obj Y).chainComplex S) _
      ((TopPair.ofSubset A).shortExact_singularChainComplexShortComplex R)).gIsCokernel _
    (chainComplexMap_tensorHom_id_comp_shuffle_comp_chainComplexπ X Y A B R S)).property

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
    (fun i j ↦ ?_) ?_ (hfac.trans (Category.id_comp _).symm)
  · let : MonoidalCategory (ChainComplex C ℕ) := monoidalCategory C (ComplexShape.down ℕ)
    have hnat := SSet.shuffleAlexanderWhitneyHomotopy_hom_naturality
      (R := R) (S := S) (toSSet.map (TopPair.ofSubset A).map) (𝟙 (toSSet.obj Y)) i j
    simp only [CategoryTheory.Functor.map_id] at hnat
    have hzero : S₁.f ≫ ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
        (TopPair.ofSubset B).singularChainComplexπ S) = 0 :=
      (tensorHom_comp_tensorHom _ _ _ _).trans <| by
        rw [(TopPair.toSSetPair.obj (TopPair.ofSubset A)).chainComplex_condition R]
        exact zero_tensorHom _
    exact (Category.assoc _ _ _).symm.trans <| (eq_whisker hnat _).trans <|
      (Category.assoc _ _ _).trans <|
        (whisker_eq _ ((comp_f _ _ j).symm.trans ((congr_hom hzero j).trans (zero_f _ _ j)))).trans
          comp_zero
  · exact (Category.assoc _ _ _).symm.trans <| (eq_whisker hfac _).trans <|
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
        𝟙 ((TopPair.toSSetPair.obj (TopPair.ofSubset B)).left.chainComplex S)
      let iB := SSet.chainComplexMap (TopPair.toSSetPair.obj (TopPair.ofSubset B)).hom S
      rw [← cancel_epi (pA.f i), comp_zero, HomologicalComplex.id_f, Category.comp_id]
      have hcomm : pA ≫ S₂.f =
          (𝟙 ((TopPair.toSSetPair.obj (TopPair.ofSubset A)).right.chainComplex R) ⊗ₘ iB) ≫
            ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
              𝟙 ((TopPair.toSSetPair.obj (TopPair.ofSubset B)).right.chainComplex S)) :=
        (tensor_id_comp_id_tensor _ _).trans (id_tensor_comp_tensor_id _ _).symm
      have hnat := SSet.shuffleAlexanderWhitneyHomotopy_hom_naturality
        (R := R) (S := S) (𝟙 (toSSet.obj X)) (toSSet.map (TopPair.ofSubset B).map) i j
      simp only [CategoryTheory.Functor.map_id] at hnat
      have hzero : (𝟙 ((TopPair.toSSetPair.obj (TopPair.ofSubset A)).right.chainComplex R) ⊗ₘ iB) ≫
          ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
            (TopPair.ofSubset B).singularChainComplexπ S) = 0 := by
        rw [tensorHom_comp_tensorHom,
          (TopPair.toSSetPair.obj (TopPair.ofSubset B)).chainComplex_condition S]
        exact tensorHom_zero _
      rw [← Category.assoc, ← HomologicalComplex.comp_f, hcomm, HomologicalComplex.comp_f,
        Category.assoc]
      exact (whisker_eq _ (π_leftRelativeShuffleAlexanderWhitneyHomotopy_hom X Y A B R S i j)).trans
        <| (Category.assoc _ _ _).symm.trans <| (eq_whisker hnat _).trans <|
          (Category.assoc _ _ _).trans <|
            (whisker_eq _
              ((comp_f _ _ j).symm.trans ((congr_hom hzero j).trans (zero_f _ _ j)))).trans
              comp_zero)
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

end Homotopy

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
    homologyMap (relativeShuffle X Y A B R S) n ≫
      SSetPair.homologyMap (smallSingularSubcomplexPairToUnion (fst X Y ⁻¹' A) (snd X Y ⁻¹' B))
        (R ⊗ S) n

/-- Definitional unfolding of `TopCat.singularRelativeHomologyCross`. -/
lemma singularRelativeHomologyCross_def :
    singularRelativeHomologyCross X Y R S A B p q n h =
      homologyCross ((TopPair.ofSubset A).singularChainComplex R)
          ((TopPair.ofSubset B).singularChainComplex S) p q n h ≫
        homologyMap (relativeShuffle X Y A B R S) n ≫
          SSetPair.homologyMap (smallSingularSubcomplexPairToUnion (fst X Y ⁻¹' A) (snd X Y ⁻¹' B))
            (R ⊗ S) n :=
  (rfl)

/-- Cycle evaluation of `TopCat.singularRelativeHomologyCross` in `(X × Y, A × Y ∪ X × B)`. -/
@[reassoc (attr := simp)]
lemma homologyπ_tensorHom_singularRelativeHomologyCross :
    (((TopPair.ofSubset A).singularChainComplex R).homologyπ p ⊗ₘ
        ((TopPair.ofSubset B).singularChainComplex S).homologyπ q) ≫
        singularRelativeHomologyCross X Y R S A B p q n h =
      cyclesCross ((TopPair.ofSubset A).singularChainComplex R)
          ((TopPair.ofSubset B).singularChainComplex S) p q n h ≫
        cyclesMap (relativeShuffle X Y A B R S) n ≫
          cyclesMap (SSetPair.chainComplexMap
            (smallSingularSubcomplexPairToUnion (fst X Y ⁻¹' A) (snd X Y ⁻¹' B)) (R ⊗ S)) n ≫
            ((TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)).singularChainComplex
              (R ⊗ S)).homologyπ n :=
  (homologyπ_tensorHom_homologyCross_assoc _ _ p q n h _).trans <|
    (cyclesCross _ _ p q n h ≫= homologyπ_naturality_assoc (relativeShuffle X Y A B R S) n _).trans
      (cyclesCross _ _ p q n h ≫= cyclesMap (relativeShuffle X Y A B R S) n ≫=
        homologyπ_naturality _ n)

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
  rw [singularRelativeHomologyCross_def, ← homologyMap_comp (relativeShuffle X Y A B R S)]
  exact (homologyCross_comp_homologyMap_naturality
    (K := (toSSet.obj X).chainComplex R) (L := (toSSet.obj Y).chainComplex S)
    ((TopPair.ofSubset A).singularChainComplexπ R) ((TopPair.ofSubset B).singularChainComplexπ S)
    p q n h
    (relativeShuffle X Y A B R S ≫ SSetPair.chainComplexMap
      (smallSingularSubcomplexPairToUnion (fst X Y ⁻¹' A) (snd X Y ⁻¹' B)) (R ⊗ S))
    (shuffle X Y R S)
    ((TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)).singularChainComplexπ (R ⊗ S))
    ((singularChainComplexπ_tensorHom_relativeShuffle_assoc X Y A B R S _).trans <|
      (Category.assoc _ _ _).trans <| whisker_eq _
        (chainComplexπ_smallSingularSubcomplexPairToUnion (R := R ⊗ S)
          (U := fst X Y ⁻¹' A) (V := snd X Y ⁻¹' B)))).trans
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
        TopPair.singularHomologyMap (TopPair.ofSubsetMap (f ⊗ₘ g)
          ((mapsTo_tensorHom_preimage_fst f g hf).union_union
            (mapsTo_tensorHom_preimage_snd f g hg))) (R ⊗ S) n := by
  let ψ := SSetPair.chainComplexMap
    (smallSingularSubcomplexPairToUnion (fst X Y ⁻¹' A) (snd X Y ⁻¹' B)) (R ⊗ S)
  let ψ' := SSetPair.chainComplexMap
    (smallSingularSubcomplexPairToUnion (fst X' Y' ⁻¹' A') (snd X' Y' ⁻¹' B')) (R ⊗ S)
  have hsmall := (((SSetPair.chainComplexFunctor C).obj (R ⊗ S)).map_comp _ _).symm.trans <|
    (congrArg (SSetPair.chainComplexMap · (R ⊗ S))
      (smallSingularSubcomplexPairToUnion_comp_ofSubsetMap (f ⊗ₘ g)
        (mapsTo_tensorHom_preimage_fst f g hf) (mapsTo_tensorHom_preimage_snd f g hg)).symm).trans
      (((SSetPair.chainComplexFunctor C).obj (R ⊗ S)).map_comp _ _)
  rw [singularRelativeHomologyCross_def, singularRelativeHomologyCross_def,
    ← homologyMap_comp (relativeShuffle X' Y' A' B' R S) ψ' n,
    ← homologyMap_comp (relativeShuffle X Y A B R S) ψ n, Category.assoc]
  exact homologyCross_comp_homologyMap_naturality
    (TopPair.singularChainComplexMap (TopPair.ofSubsetMap f hf) R)
    (TopPair.singularChainComplexMap (TopPair.ofSubsetMap g hg) S) p q n h
    (relativeShuffle X' Y' A' B' R S ≫ ψ') (relativeShuffle X Y A B R S ≫ ψ)
    (TopPair.singularChainComplexMap (TopPair.ofSubsetMap (f ⊗ₘ g)
      ((mapsTo_tensorHom_preimage_fst f g hf).union_union
        (mapsTo_tensorHom_preimage_snd f g hg))) (R ⊗ S))
    ((relativeShuffle_naturality_assoc f g hf hg R S _).trans
      ((whisker_eq _ hsmall).trans (Category.assoc _ _ _).symm))

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
    ← homologyMap_comp (relativeShuffle X Y A B R' S') u' n,
    ← homologyMap_comp (relativeShuffle X Y A B R S) u n, Category.assoc]
  exact homologyCross_comp_homologyMap_naturality
    (((SSetPair.chainComplexFunctor C).map φ).app (TopPair.toSSetPair.obj (TopPair.ofSubset A)))
    (((SSetPair.chainComplexFunctor C).map ψ).app (TopPair.toSSetPair.obj (TopPair.ofSubset B)))
    p q n h (relativeShuffle X Y A B R' S' ≫ u') (relativeShuffle X Y A B R S ≫ u)
    (((SSetPair.chainComplexFunctor C).map (φ ⊗ₘ ψ)).app
      (TopPair.toSSetPair.obj (TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B))))
    ((relativeShuffle_coefficient_naturality_assoc X Y A B φ ψ _).trans
      ((whisker_eq _ (((SSetPair.chainComplexFunctor C).map (φ ⊗ₘ ψ)).naturality
        (smallSingularSubcomplexPairToUnion (fst X Y ⁻¹' A) (snd X Y ⁻¹' B))).symm).trans
        (Category.assoc _ _ _).symm))

end TopCat
