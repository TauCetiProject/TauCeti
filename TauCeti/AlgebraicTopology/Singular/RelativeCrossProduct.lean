/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.Homology.Connecting
public import TauCeti.AlgebraicTopology.Singular.AlexanderWhitney.RelativeCup
public import TauCeti.AlgebraicTopology.Singular.CrossProduct
import TauCeti.AlgebraicTopology.Singular.Subdivision.Small.Relative

/-!
# The relative cross product in singular homology

For subsets `A ⊆ X` and `B ⊆ Y` and coefficient objects `R, S`, tensoring preserves the degreewise
split chain short exact sequences of `(X, A)` and `(Y, B)`, so `TopCat.shuffle` descends to
`TopCat.relativeShuffle : C(X, A; R) ⊗ C(Y, B; S) ⟶ C(X × Y; A × Y + X × B; R ⊗ S)`
(`TopCat.singularChainComplexπ_tensorHom_relativeShuffle`), and two applications of
`Homotopy.descCokernel` to `SSet.shuffleAlexanderWhitneyHomotopy` give
`TopCat.relativeShuffleAlexanderWhitneyHomotopy` from `relativeShuffle ≫ relativeAlexanderWhitney`
to `𝟙 _`. Composing `HomologicalComplex.homologyCross` with `TopCat.relativeShuffle` and
`TopCat.smallSingularSubcomplexPairToUnion` defines `TopCat.singularRelativeHomologyCross` without
openness hypotheses, evaluated on cycles by
`TopCat.homologyπ_tensorHom_singularRelativeHomologyCross` and compatible with
`TopCat.singularHomologyCross`
(`TopCat.singularHomologyπ_tensorHom_singularRelativeHomologyCross`).

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), Section 3.B.
* S. Eilenberg and J. A. Zilber, *On products of complexes*, Amer. J. Math. 75 (1953).
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicTopology
  HomologicalComplex

universe w v u

namespace TopCat

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

/-- Cache `MonoidalCategory (ChainComplex C ℕ)` under `[Preadditive C]` before `[Abelian C]` enters
scope so `[Abelian C]` does not push the synthesis term size past `synthInstance.maxSize`. -/
local instance instMonoidalCategoryChainComplex {C : Type u} [Category.{v} C] [Preadditive C]
    [HasCoproducts.{w} C] [MonoidalCategory C] [MonoidalPreadditive C] :
    MonoidalCategory (ChainComplex C ℕ) :=
  inferInstance

section ChainLevel

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
  [MonoidalCategory C] [MonoidalPreadditive C]

/-- Short exact sequence `0 ⟶ C(A; R) ⊗ C(Y; S) ⟶ C(X; R) ⊗ C(Y; S) ⟶ C(X, A; R) ⊗ C(Y; S) ⟶ 0`. -/
private lemma shortExact_leftFactor (X Y : TopCat.{w}) (A : Set X) (R S : C) :
    (tensorRightShortComplex ((toSSet.obj Y).chainComplex S)
      ((TopPair.toSSetPair.obj (TopPair.ofSubset A)).chainComplexShortComplex R)).ShortExact :=
  shortExact_tensorRightShortComplex ((toSSet.obj Y).chainComplex S) _
    ((TopPair.toSSetPair.obj (TopPair.ofSubset A)).shortExact_chainComplexShortComplex R)

/-- Exactness of `0 ⟶ C(X, A; R) ⊗ C(B; S) ⟶ C(X, A; R) ⊗ C(Y; S) ⟶ C(X, A; R) ⊗ C(Y, B; S) ⟶ 0`. -/
private lemma shortExact_rightFactor (X Y : TopCat.{w}) (A : Set X) (B : Set Y) (R S : C) :
    (tensorLeftShortComplex ((TopPair.ofSubset A).singularChainComplex R)
      ((TopPair.toSSetPair.obj (TopPair.ofSubset B)).chainComplexShortComplex S)).ShortExact :=
  shortExact_tensorLeftShortComplex ((TopPair.ofSubset A).singularChainComplex R)
    ((TopPair.toSSetPair.obj (TopPair.ofSubset B)).shortExact_chainComplexShortComplex S)

/-- Epimorphism `C(X; R) ⊗ C(Y; S) ↠ C(X, A; R) ⊗ C(Y, B; S)`. -/
private instance epi_singularChainComplexπ_tensorHom
    (X Y : TopCat.{w}) (A : Set X) (B : Set Y) (R S : C) :
    Epi ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
      (TopPair.ofSubset B).singularChainComplexπ S) := by
  have : Epi ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
      𝟙 ((TopPair.toSSetPair.obj (TopPair.ofSubset B)).right.chainComplex S)) :=
    (shortExact_leftFactor X Y A R S).epi_g
  have : Epi (𝟙 ((TopPair.ofSubset A).singularChainComplex R) ⊗ₘ
      (TopPair.ofSubset B).singularChainComplexπ S) := (shortExact_rightFactor X Y A B R S).epi_g
  have hfac : ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
      (TopPair.ofSubset B).singularChainComplexπ S) =
      ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
        𝟙 ((TopPair.toSSetPair.obj (TopPair.ofSubset B)).right.chainComplex S)) ≫
      (𝟙 ((TopPair.ofSubset A).singularChainComplex R) ⊗ₘ
        (TopPair.ofSubset B).singularChainComplexπ S) := by
    simp only [tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]
  exact hfac ▸ epi_comp _ _

section Shuffle

variable [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft T)]
  [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight T)]

/-- `shuffle X Y R S` vanishes on `C(A; R) ⊗ C(Y; S)` modulo `A × Y + X × B`. -/
private lemma chainComplexMap_tensorHom_id_comp_shuffle_comp_chainComplexπ
    (X Y : TopCat.{w}) (A : Set X) (B : Set Y) (R S : C) :
    (SSet.chainComplexMap (TopPair.toSSetPair.obj (TopPair.ofSubset A)).hom R ⊗ₘ
        𝟙 ((toSSet.obj Y).chainComplex S)) ≫ shuffle X Y R S ≫
      ((X ⊗ Y).smallSingularSubcomplex ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.chainComplexπ
        (R ⊗ S) = 0 := by
  let ιA : of ↥A ⟶ X := (TopPair.ofSubset A).map
  have hid : 𝟙 ((toSSet.obj Y).chainComplex S) = SSet.chainComplexMap (toSSet.map (𝟙 Y)) S :=
    (((SSet.chainComplexFunctor C).obj S).map_id _).symm.trans
      (congrArg (SSet.chainComplexMap · S) (toSSet.map_id Y).symm)
  have hsh := (eq_whisker (congrArg (SSet.chainComplexMap (toSSet.map ιA) R ⊗ₘ ·) hid)
      (shuffle X Y R S)).trans (shuffle_naturality ιA (𝟙 Y) R S)
  refine (Category.assoc _ _ _).symm.trans
    ((eq_whisker hsh _).trans ((Category.assoc _ _ _).trans ?_))
  have hf (z) : (ιA ⊗ₘ 𝟙 Y) z ∈ ![fst X Y ⁻¹' A, snd X Y ⁻¹' B] 0 := by
    rw [Matrix.cons_val_zero]
    exact Set.mem_preimage.2
      ((ConcreteCategory.congr_hom (tensorHom_fst ιA (𝟙 Y)) z).symm ▸ (fst (of ↥A) Y z).2)
  exact (whisker_eq _
    (TauCeti.chainComplexMap_comp_smallSingularSubcomplex_chainComplexπ_eq_zero _ _ hf _)).trans
    comp_zero

/-- Intermediate descent of the shuffle map to `C(X, A; R) ⊗ C(Y; S)`. -/
private def leftRelativeShuffle (X Y : TopCat.{w}) (A : Set X) (B : Set Y) (R S : C) :
    (TopPair.ofSubset A).singularChainComplex R ⊗ (toSSet.obj Y).chainComplex S ⟶
      ((X ⊗ Y).smallSingularSubcomplex ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.chainComplex
        (R ⊗ S) :=
  (CokernelCofork.IsColimit.desc' (shortExact_leftFactor X Y A R S).gIsCokernel
    (shuffle X Y R S ≫
      ((X ⊗ Y).smallSingularSubcomplex ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.chainComplexπ (R ⊗ S))
    (chainComplexMap_tensorHom_id_comp_shuffle_comp_chainComplexπ X Y A B R S)).1

@[reassoc]
private lemma singularChainComplexπ_tensorHom_id_leftRelativeShuffle
    (X Y : TopCat.{w}) (A : Set X) (B : Set Y) (R S : C) :
    ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ 𝟙 ((toSSet.obj Y).chainComplex S)) ≫
        leftRelativeShuffle X Y A B R S =
      shuffle X Y R S ≫
        ((X ⊗ Y).smallSingularSubcomplex ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.chainComplexπ
          (R ⊗ S) :=
  (CokernelCofork.IsColimit.desc' (shortExact_leftFactor X Y A R S).gIsCokernel _
    (chainComplexMap_tensorHom_id_comp_shuffle_comp_chainComplexπ X Y A B R S)).2

/-- On `C(X, A; R) ⊗ C(B; S)`, the intermediate shuffle map vanishes because `C(X; R) ⊗ C(B; S)`
lands in the singular chains of `X × B`. -/
private lemma id_tensorHom_chainComplexMap_comp_leftRelativeShuffle
    (X Y : TopCat.{w}) (A : Set X) (B : Set Y) (R S : C) :
    (𝟙 ((TopPair.ofSubset A).singularChainComplex R) ⊗ₘ
        SSet.chainComplexMap (TopPair.toSSetPair.obj (TopPair.ofSubset B)).hom S) ≫
      leftRelativeShuffle X Y A B R S = 0 := by
  let ιB : of ↥B ⟶ Y := (TopPair.ofSubset B).map
  let pA := (TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
    𝟙 ((TopPair.toSSetPair.obj (TopPair.ofSubset B)).left.chainComplex S)
  have : Epi pA := (shortExact_leftFactor X (of ↥B) A R S).epi_g
  rw [← cancel_epi pA, comp_zero]
  have hcomm : pA ≫ (𝟙 ((TopPair.ofSubset A).singularChainComplex R) ⊗ₘ
      SSet.chainComplexMap (TopPair.toSSetPair.obj (TopPair.ofSubset B)).hom S) =
      (𝟙 ((toSSet.obj X).chainComplex R) ⊗ₘ SSet.chainComplexMap (toSSet.map ιB) S) ≫
        ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ 𝟙 ((toSSet.obj Y).chainComplex S)) :=
    (tensorHom_comp_tensorHom _ _ _ _).trans <|
      (congrArg₂ (· ⊗ₘ ·) (Category.comp_id _) (Category.id_comp _)).trans <|
      (congrArg₂ (· ⊗ₘ ·) (Category.id_comp _).symm (Category.comp_id _).symm).trans
        (tensorHom_comp_tensorHom _ _ _ _).symm
  refine (Category.assoc _ _ _).symm.trans ((eq_whisker hcomm _).trans <|
    (Category.assoc _ _ _).trans <|
    (whisker_eq _ (singularChainComplexπ_tensorHom_id_leftRelativeShuffle X Y A B R S)).trans ?_)
  have hid : 𝟙 ((toSSet.obj X).chainComplex R) = SSet.chainComplexMap (toSSet.map (𝟙 X)) R :=
    (((SSet.chainComplexFunctor C).obj R).map_id _).symm.trans
      (congrArg (SSet.chainComplexMap · R) (toSSet.map_id X).symm)
  have hsh := (eq_whisker (congrArg (· ⊗ₘ SSet.chainComplexMap (toSSet.map ιB) S) hid)
      (shuffle X Y R S)).trans (shuffle_naturality (𝟙 X) ιB R S)
  refine (Category.assoc _ _ _).symm.trans
    ((eq_whisker hsh _).trans ((Category.assoc _ _ _).trans ?_))
  have hf (z) : (𝟙 X ⊗ₘ ιB) z ∈ ![fst X Y ⁻¹' A, snd X Y ⁻¹' B] 1 := by
    rw [Matrix.cons_val_one, Matrix.cons_val_zero]
    exact Set.mem_preimage.2
      ((ConcreteCategory.congr_hom (tensorHom_snd (𝟙 X) ιB) z).symm ▸ (snd X (of ↥B) z).2)
  exact (whisker_eq _
    (TauCeti.chainComplexMap_comp_smallSingularSubcomplex_chainComplexπ_eq_zero _ _ hf _)).trans
    comp_zero

/-- **The relative shuffle map**
`C(X, A; R) ⊗ C(Y, B; S) ⟶ C(X × Y; A × Y + X × B; R ⊗ S)` for subsets `A ⊆ X` and `B ⊆ Y`: the
descent of `TopCat.shuffle X Y R S` followed by the quotient map from `C(X × Y; R ⊗ S)` to the
chains relative to singular simplices lying in `fst⁻¹(A)` or in `snd⁻¹(B)`. -/
def relativeShuffle (X Y : TopCat.{w}) (A : Set X) (B : Set Y) (R S : C) :
    (TopPair.ofSubset A).singularChainComplex R ⊗ (TopPair.ofSubset B).singularChainComplex S ⟶
      ((X ⊗ Y).smallSingularSubcomplex ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.chainComplex
        (R ⊗ S) :=
  (CokernelCofork.IsColimit.desc' (shortExact_rightFactor X Y A B R S).gIsCokernel
    (leftRelativeShuffle X Y A B R S)
    (id_tensorHom_chainComplexMap_comp_leftRelativeShuffle X Y A B R S)).1

/-- The relative shuffle map is characterized by precomposition with the tensor product of the
quotient maps `C(X; R) ⟶ C(X, A; R)` and `C(Y; S) ⟶ C(Y, B; S)`. -/
@[reassoc (attr := simp)]
lemma singularChainComplexπ_tensorHom_relativeShuffle
    (X Y : TopCat.{w}) (A : Set X) (B : Set Y) (R S : C) :
    ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
        (TopPair.ofSubset B).singularChainComplexπ S) ≫ relativeShuffle X Y A B R S =
      shuffle X Y R S ≫
        ((X ⊗ Y).smallSingularSubcomplex ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.chainComplexπ
          (R ⊗ S) := by
  have hdesc : (𝟙 ((TopPair.ofSubset A).singularChainComplex R) ⊗ₘ
      (TopPair.ofSubset B).singularChainComplexπ S) ≫ relativeShuffle X Y A B R S =
      leftRelativeShuffle X Y A B R S :=
    (CokernelCofork.IsColimit.desc' (shortExact_rightFactor X Y A B R S).gIsCokernel _
      (id_tensorHom_chainComplexMap_comp_leftRelativeShuffle X Y A B R S)).2
  have hfac : ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
      (TopPair.ofSubset B).singularChainComplexπ S) =
      ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ 𝟙 ((toSSet.obj Y).chainComplex S)) ≫
        (𝟙 ((TopPair.ofSubset A).singularChainComplex R) ⊗ₘ
          (TopPair.ofSubset B).singularChainComplexπ S) :=
    (congrArg₂ (· ⊗ₘ ·) (Category.comp_id _).symm (Category.id_comp _).symm).trans
      (tensorHom_comp_tensorHom _ _ _ _).symm
  exact (congrArg (· ≫ _) hfac).trans ((Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) hdesc).trans
      (singularChainComplexπ_tensorHom_id_leftRelativeShuffle X Y A B R S)))

/-- **Naturality of the relative shuffle map** in continuous maps `f : X ⟶ X'` carrying `A` into
`A'` and `g : Y ⟶ Y'` carrying `B` into `B'`. -/
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
  rw [← cancel_epi ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
    (TopPair.ofSubset B).singularChainComplexπ S)]
  have hπ := SSetPair.chainComplexπ_naturality (R ⊗ S) (smallSingularSubcomplexPairMap (f ⊗ₘ g)
    (mapsTo_tensorHom_preimage_fst f g hf) (mapsTo_tensorHom_preimage_snd f g hg))
  have hA := TopPair.singularChainComplexπ_pair_naturality (TopPair.ofSubsetMap f hf) R
  have hB := TopPair.singularChainComplexπ_pair_naturality (TopPair.ofSubsetMap g hg) S
  rw [smallSingularSubcomplexPairMap_right] at hπ
  rw [TopPair.ofSubsetMap_fst] at hA hB
  exact (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ _) ((tensorHom_comp_tensorHom _ _ _ _).trans
      ((congrArg₂ (· ⊗ₘ ·) hA.symm hB.symm).trans
        (tensorHom_comp_tensorHom _ _ _ _).symm))).trans <|
    (Category.assoc _ _ _).trans <|
    (whisker_eq _ (singularChainComplexπ_tensorHom_relativeShuffle X' Y' A' B' R S)).trans <|
    ((singularChainComplexπ_tensorHom_relativeShuffle_assoc X Y A B R S _).trans <|
      (Category.assoc _ _ _).trans <|
      (congrArg (_ ≫ ·) hπ.symm).trans (shuffle_naturality_assoc f g R S _).symm).symm

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
  rw [← cancel_epi ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
    (TopPair.ofSubset B).singularChainComplexπ S)]
  have hπ := NatTrans.congr_app ((SSetPair.chainComplexFunctorπ C).naturality (φ ⊗ₘ ψ)).symm
    ((X ⊗ Y).smallSingularSubcomplex ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair
  have hA := NatTrans.congr_app ((SSetPair.chainComplexFunctorπ C).naturality φ).symm
    (TopPair.toSSetPair.obj (TopPair.ofSubset A))
  have hB := NatTrans.congr_app ((SSetPair.chainComplexFunctorπ C).naturality ψ).symm
    (TopPair.toSSetPair.obj (TopPair.ofSubset B))
  exact (Category.assoc _ _ _).symm.trans <|
    (eq_whisker ((tensorHom_comp_tensorHom _ _ _ _).trans
      ((congrArg₂ (· ⊗ₘ ·) hA hB).trans (tensorHom_comp_tensorHom _ _ _ _).symm)) _).trans <|
    (Category.assoc _ _ _).trans <|
    (whisker_eq _ (singularChainComplexπ_tensorHom_relativeShuffle X Y A B R' S')).trans <|
    ((singularChainComplexπ_tensorHom_relativeShuffle_assoc X Y A B R S _).trans <|
      (Category.assoc _ _ _).trans <|
      (whisker_eq _ hπ).trans (shuffle_coefficient_naturality_assoc X Y φ ψ _).symm).symm

/-- On `C(A; R) ⊗ C(Y; S)`, the simplicial Eilenberg–Zilber homotopy followed by `π_A ⊗ π_B`
vanishes in every bidegree. -/
private lemma leftFactor_comp_shuffleAlexanderWhitneyHomotopy_hom
    (X Y : TopCat.{w}) (A : Set X) (B : Set Y) (R S : C) (i j : ℕ) :
    (tensorRightShortComplex ((toSSet.obj Y).chainComplex S)
        ((TopPair.toSSetPair.obj (TopPair.ofSubset A)).chainComplexShortComplex R)).f.f i ≫
      (SSet.shuffleAlexanderWhitneyHomotopy (toSSet.obj X) (toSSet.obj Y) R S).hom i j ≫
      ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
        (TopPair.ofSubset B).singularChainComplexπ S).f j = 0 := by
  have hid : 𝟙 ((toSSet.obj Y).chainComplex S) = SSet.chainComplexMap (𝟙 (toSSet.obj Y)) S :=
    (((SSet.chainComplexFunctor C).obj S).map_id _).symm
  have hnat := SSet.shuffleAlexanderWhitneyHomotopy_hom_naturality_assoc
    (R := R) (S := S) (toSSet.map (TopPair.ofSubset A).map) (𝟙 (toSSet.obj Y)) i j
    (((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
      (TopPair.ofSubset B).singularChainComplexπ S).f j)
  have hzero : (SSet.chainComplexMap (toSSet.map (TopPair.ofSubset A).map) R ⊗ₘ
      𝟙 ((toSSet.obj Y).chainComplex S)) ≫ ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
        (TopPair.ofSubset B).singularChainComplexπ S) = 0 :=
    (tensorHom_comp_tensorHom _ _ _ _).trans <|
      (congrArg (· ⊗ₘ _)
        ((TopPair.toSSetPair.obj (TopPair.ofSubset A)).chainComplex_condition R)).trans
        (zero_tensorHom _)
  refine (eq_whisker (congrArg (fun g ↦
    (SSet.chainComplexMap (toSSet.map (TopPair.ofSubset A).map) R ⊗ₘ g).f i) hid) _).trans
    (hnat.trans ((whisker_eq _ (eq_whisker (congrArg (fun g ↦
      (SSet.chainComplexMap (toSSet.map (TopPair.ofSubset A).map) R ⊗ₘ g).f j) hid.symm) _)).trans
      ?_))
  exact (whisker_eq _ ((HomologicalComplex.comp_f _ _ j).symm.trans
    ((HomologicalComplex.congr_hom hzero j).trans (HomologicalComplex.zero_f _ _ j)))).trans
    comp_zero

/-- Intermediate descent of the Eilenberg–Zilber chain homotopy along the first quotient
`C(X; R) ⊗ C(Y; S) ↠ C(X, A; R) ⊗ C(Y; S)`. -/
private def leftRelativeShuffleAlexanderWhitneyHomotopy
    (X Y : TopCat.{w}) (A : Set X) (B : Set Y) (R S : C) :
    _root_.Homotopy
      ((tensorLeftShortComplex ((TopPair.ofSubset A).singularChainComplex R)
          ((TopPair.toSSetPair.obj (TopPair.ofSubset B)).chainComplexShortComplex S)).g ≫
        (relativeShuffle X Y A B R S ≫ relativeAlexanderWhitney X Y A B R S))
      (tensorLeftShortComplex ((TopPair.ofSubset A).singularChainComplex R)
        ((TopPair.toSSetPair.obj (TopPair.ofSubset B)).chainComplexShortComplex S)).g := by
  let S₁ := tensorRightShortComplex ((toSSet.obj Y).chainComplex S)
    ((TopPair.toSSetPair.obj (TopPair.ofSubset A)).chainComplexShortComplex R)
  have hfac : S₁.g ≫ (tensorLeftShortComplex ((TopPair.ofSubset A).singularChainComplex R)
      ((TopPair.toSSetPair.obj (TopPair.ofSubset B)).chainComplexShortComplex S)).g =
      ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
        (TopPair.ofSubset B).singularChainComplexπ S) :=
    (tensorHom_comp_tensorHom ((TopPair.toSSetPair.obj (TopPair.ofSubset A)).chainComplexπ R)
      (𝟙 ((toSSet.obj Y).chainComplex S)) (𝟙 ((TopPair.ofSubset A).singularChainComplex R))
      ((TopPair.toSSetPair.obj (TopPair.ofSubset B)).chainComplexπ S)).trans
      (congrArg₂ (· ⊗ₘ ·) (Category.comp_id _) (Category.id_comp _))
  refine _root_.Homotopy.descCokernel
    (SSet.shuffleAlexanderWhitneyHomotopy (toSSet.obj X) (toSSet.obj Y) R S) S₁.f S₁.g
    ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ (TopPair.ofSubset B).singularChainComplexπ S)
    (fun i ↦ (HomologicalComplex.comp_f S₁.f S₁.g i).symm.trans
      ((HomologicalComplex.congr_hom S₁.zero i).trans (HomologicalComplex.zero_f _ _ i)))
    (fun i ↦ ((shortExact_iff_degreewise_shortExact S₁).1
      (shortExact_leftFactor X Y A R S) i).gIsCokernel)
    (leftFactor_comp_shuffleAlexanderWhitneyHomotopy_hom X Y A B R S) ?_
    (hfac.trans (Category.id_comp _).symm)
  exact (Category.assoc _ _ _).symm.trans <| (eq_whisker hfac _).trans <|
    (singularChainComplexπ_tensorHom_relativeShuffle_assoc X Y A B R S _).trans <|
    (Category.assoc _ _ _).trans <|
    (whisker_eq _ (chainComplexπ_relativeAlexanderWhitney X Y A B R S)).trans <|
    (Category.assoc _ _ _).symm.trans (eq_whisker (shuffle_alexanderWhitney X Y R S) _)

private lemma π_leftRelativeShuffleAlexanderWhitneyHomotopy_hom
    (X Y : TopCat.{w}) (A : Set X) (B : Set Y) (R S : C) (i j : ℕ) :
    ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ 𝟙 ((toSSet.obj Y).chainComplex S)).f i ≫
        (leftRelativeShuffleAlexanderWhitneyHomotopy X Y A B R S).hom i j =
      (SSet.shuffleAlexanderWhitneyHomotopy (toSSet.obj X) (toSSet.obj Y) R S).hom i j ≫
        ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
          (TopPair.ofSubset B).singularChainComplexπ S).f j := by
  unfold leftRelativeShuffleAlexanderWhitneyHomotopy
  exact _root_.Homotopy.π_descCokernel_hom _ _ _ _ _ _ _ _ _ i j

/-- On `C(X, A; R) ⊗ C(B; S)`, the intermediate homotopy vanishes in every bidegree. -/
private lemma rightFactor_comp_leftRelativeShuffleAlexanderWhitneyHomotopy_hom
    (X Y : TopCat.{w}) (A : Set X) (B : Set Y) (R S : C) (i j : ℕ) :
    (tensorLeftShortComplex ((TopPair.ofSubset A).singularChainComplex R)
        ((TopPair.toSSetPair.obj (TopPair.ofSubset B)).chainComplexShortComplex S)).f.f i ≫
      (leftRelativeShuffleAlexanderWhitneyHomotopy X Y A B R S).hom i j ≫
      HomologicalComplex.Hom.f (𝟙 ((TopPair.ofSubset A).singularChainComplex R ⊗
        (TopPair.ofSubset B).singularChainComplex S)) j = 0 := by
  let pA := (TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
    𝟙 ((TopPair.toSSetPair.obj (TopPair.ofSubset B)).left.chainComplex S)
  have : Epi (pA.f i) :=
    ((shortExact_iff_degreewise_shortExact _).1 (shortExact_leftFactor X (of ↥B) A R S) i).epi_g
  rw [← cancel_epi (pA.f i), comp_zero, HomologicalComplex.id_f, Category.comp_id]
  have hcomm : pA ≫ (tensorLeftShortComplex ((TopPair.ofSubset A).singularChainComplex R)
        ((TopPair.toSSetPair.obj (TopPair.ofSubset B)).chainComplexShortComplex S)).f =
      (𝟙 ((toSSet.obj X).chainComplex R) ⊗ₘ
        SSet.chainComplexMap (toSSet.map (TopPair.ofSubset B).map) S) ≫
        ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ 𝟙 ((toSSet.obj Y).chainComplex S)) :=
    (tensorHom_comp_tensorHom ((TopPair.ofSubset A).singularChainComplexπ R)
      (𝟙 ((TopPair.toSSetPair.obj (TopPair.ofSubset B)).left.chainComplex S))
      (𝟙 ((TopPair.ofSubset A).singularChainComplex R))
      (SSet.chainComplexMap (TopPair.toSSetPair.obj (TopPair.ofSubset B)).hom S)).trans <|
      (congrArg₂ (· ⊗ₘ ·) (Category.comp_id _) (Category.id_comp _)).trans <|
      (congrArg₂ (· ⊗ₘ ·) (Category.id_comp _).symm (Category.comp_id _).symm).trans
        (tensorHom_comp_tensorHom _ _ _ _).symm
  have hid : 𝟙 ((toSSet.obj X).chainComplex R) = SSet.chainComplexMap (𝟙 (toSSet.obj X)) R :=
    (((SSet.chainComplexFunctor C).obj R).map_id _).symm
  have hnat := SSet.shuffleAlexanderWhitneyHomotopy_hom_naturality_assoc
    (R := R) (S := S) (𝟙 (toSSet.obj X)) (toSSet.map (TopPair.ofSubset B).map) i j
    (((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
      (TopPair.ofSubset B).singularChainComplexπ S).f j)
  have hzero : (𝟙 ((toSSet.obj X).chainComplex R) ⊗ₘ
      SSet.chainComplexMap (toSSet.map (TopPair.ofSubset B).map) S) ≫
      ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
        (TopPair.ofSubset B).singularChainComplexπ S) = 0 :=
    (tensorHom_comp_tensorHom _ _ _ _).trans <|
      (congrArg (_ ⊗ₘ ·)
        ((TopPair.toSSetPair.obj (TopPair.ofSubset B)).chainComplex_condition S)).trans
        (tensorHom_zero _)
  refine (Category.assoc _ _ _).symm.trans <|
    (eq_whisker ((HomologicalComplex.comp_f _ _ i).symm.trans
      ((HomologicalComplex.congr_hom hcomm i).trans (HomologicalComplex.comp_f _ _ i))) _).trans <|
    (Category.assoc _ _ _).trans <|
    (whisker_eq _ (π_leftRelativeShuffleAlexanderWhitneyHomotopy_hom X Y A B R S i j)).trans <|
    (eq_whisker (congrArg (fun g ↦
      (g ⊗ₘ SSet.chainComplexMap (toSSet.map (TopPair.ofSubset B).map) S).f i) hid) _).trans
      (hnat.trans ((whisker_eq _ (eq_whisker (congrArg (fun g ↦
        (g ⊗ₘ SSet.chainComplexMap (toSSet.map (TopPair.ofSubset B).map) S).f j) hid.symm) _)).trans
        ?_))
  exact (whisker_eq _ ((HomologicalComplex.comp_f _ _ j).symm.trans
    ((HomologicalComplex.congr_hom hzero j).trans (HomologicalComplex.zero_f _ _ j)))).trans
    comp_zero

/-- **The relative Eilenberg–Zilber chain homotopy** `AW ∘ shuffle ≃ id`: for subsets `A ⊆ X` and
`B ⊆ Y`, `TopCat.relativeShuffle` followed by `TopCat.relativeAlexanderWhitney` is chain homotopic
to the identity of `C(X, A; R) ⊗ C(Y, B; S)`. -/
def relativeShuffleAlexanderWhitneyHomotopy
    (X Y : TopCat.{w}) (A : Set X) (B : Set Y) (R S : C) :
    _root_.Homotopy
      (relativeShuffle X Y A B R S ≫ relativeAlexanderWhitney X Y A B R S) (𝟙 _) :=
  let S₂ := tensorLeftShortComplex ((TopPair.ofSubset A).singularChainComplex R)
    ((TopPair.toSSetPair.obj (TopPair.ofSubset B)).chainComplexShortComplex S)
  _root_.Homotopy.descCokernel
    (leftRelativeShuffleAlexanderWhitneyHomotopy X Y A B R S) S₂.f S₂.g (𝟙 _)
    (fun i ↦ (HomologicalComplex.comp_f S₂.f S₂.g i).symm.trans
      ((HomologicalComplex.congr_hom S₂.zero i).trans (HomologicalComplex.zero_f _ _ i)))
    (fun i ↦ ((shortExact_iff_degreewise_shortExact S₂).1
      (shortExact_rightFactor X Y A B R S) i).gIsCokernel)
    (rightFactor_comp_leftRelativeShuffleAlexanderWhitneyHomotopy_hom X Y A B R S)
    (Category.comp_id _).symm rfl

/-- On homology, the relative shuffle map followed by the relative Alexander–Whitney map is the
identity of `Hₙ(C(X, A; R) ⊗ C(Y, B; S))`. -/
@[reassoc (attr := simp)]
lemma homologyMap_relativeShuffle_comp_homologyMap_relativeAlexanderWhitney
    (X Y : TopCat.{w}) (A : Set X) (B : Set Y) (R S : C) (n : ℕ) :
    homologyMap (relativeShuffle X Y A B R S) n ≫
        homologyMap (relativeAlexanderWhitney X Y A B R S) n = 𝟙 _ := by
  rw [← homologyMap_comp, (relativeShuffleAlexanderWhitneyHomotopy X Y A B R S).homologyMap_eq n,
    homologyMap_id]

end Shuffle

end ChainLevel

section HomologyCross

variable {C : Type u} [Category.{v} C] [Abelian C]
  [MonoidalCategory C] [MonoidalPreadditive C] [HasCoproducts.{w} C]
  [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft T)]
  [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight T)]

/-- **The relative homology cross product**
`Hₚ(X, A; R) ⊗ H_q(Y, B; S) ⟶ Hₙ(X × Y, A × Y ∪ X × B; R ⊗ S)` for arbitrary subsets `A ⊆ X` and
`B ⊆ Y` (`p + q = n`): `HomologicalComplex.homologyCross` followed by `TopCat.relativeShuffle` and
`TopCat.smallSingularSubcomplexPairToUnion`. -/
def singularRelativeHomologyCross (X Y : TopCat.{w}) (R S : C) (A : Set X) (B : Set Y)
    (p q n : ℕ) (h : p + q = n)
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorLeft (((TopPair.ofSubset A).singularChainComplex R).homology p))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((TopPair.ofSubset B).singularChainComplex S).cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((TopPair.ofSubset B).singularChainComplex S).X
        ((ComplexShape.down ℕ).prev q)))] :
    (TopPair.ofSubset A).singularHomology R p ⊗ (TopPair.ofSubset B).singularHomology S q ⟶
      (TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)).singularHomology (R ⊗ S) n :=
  homologyCross ((TopPair.ofSubset A).singularChainComplex R)
      ((TopPair.ofSubset B).singularChainComplex S) p q n h ≫
    homologyMap (relativeShuffle X Y A B R S) n ≫
      SSetPair.homologyMap (smallSingularSubcomplexPairToUnion (fst X Y ⁻¹' A) (snd X Y ⁻¹' B))
        (R ⊗ S) n

/-- Definitional unfolding of `TopCat.singularRelativeHomologyCross`. -/
lemma singularRelativeHomologyCross_def (X Y : TopCat.{w}) (R S : C) (A : Set X) (B : Set Y)
    (p q n : ℕ) (h : p + q = n)
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorLeft (((TopPair.ofSubset A).singularChainComplex R).homology p))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((TopPair.ofSubset B).singularChainComplex S).cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((TopPair.ofSubset B).singularChainComplex S).X
        ((ComplexShape.down ℕ).prev q)))] :
    singularRelativeHomologyCross X Y R S A B p q n h =
      homologyCross ((TopPair.ofSubset A).singularChainComplex R)
          ((TopPair.ofSubset B).singularChainComplex S) p q n h ≫
        homologyMap (relativeShuffle X Y A B R S) n ≫
          SSetPair.homologyMap (smallSingularSubcomplexPairToUnion (fst X Y ⁻¹' A) (snd X Y ⁻¹' B))
            (R ⊗ S) n :=
  (rfl)

/-- The relative cross product of the classes of two relative singular cycles is the class of their
relative shuffle product in `(X × Y, A × Y ∪ X × B)`. -/
@[simp, reassoc]
lemma homologyπ_tensorHom_singularRelativeHomologyCross
    (X Y : TopCat.{w}) (R S : C) (A : Set X) (B : Set Y) (p q n : ℕ) (h : p + q = n)
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorLeft (((TopPair.ofSubset A).singularChainComplex R).homology p))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((TopPair.ofSubset B).singularChainComplex S).cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((TopPair.ofSubset B).singularChainComplex S).X
        ((ComplexShape.down ℕ).prev q)))] :
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
        homologyπ_naturality (SSetPair.chainComplexMap
          (smallSingularSubcomplexPairToUnion (fst X Y ⁻¹' A) (snd X Y ⁻¹' B)) (R ⊗ S)) n)

/-- **Compatibility with the absolute homology cross product**: the quotient maps from absolute to
relative singular homology intertwine `TopCat.singularHomologyCross` and
`TopCat.singularRelativeHomologyCross`. -/
@[reassoc]
lemma singularHomologyπ_tensorHom_singularRelativeHomologyCross
    (X Y : TopCat.{w}) (R S : C) (A : Set X) (B : Set Y) (p q n : ℕ) (h : p + q = n)
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorLeft (((toSSet.obj X).chainComplex R).homology p))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((toSSet.obj Y).chainComplex S).cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((toSSet.obj Y).chainComplex S).X ((ComplexShape.down ℕ).prev q)))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorLeft (((TopPair.ofSubset A).singularChainComplex R).homology p))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((TopPair.ofSubset B).singularChainComplex S).cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((TopPair.ofSubset B).singularChainComplex S).X
        ((ComplexShape.down ℕ).prev q)))] :
    ((TopPair.ofSubset A).singularHomologyπ R p ⊗ₘ (TopPair.ofSubset B).singularHomologyπ S q) ≫
        singularRelativeHomologyCross X Y R S A B p q n h =
      singularHomologyCross X Y R S p q n h ≫
        (TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)).singularHomologyπ (R ⊗ S) n := by
  let πA : (toSSet.obj X).chainComplex R ⟶ _ := (TopPair.ofSubset A).singularChainComplexπ R
  let πB : (toSSet.obj Y).chainComplex S ⟶ _ := (TopPair.ofSubset B).singularChainComplexπ S
  let πU : (toSSet.obj (X ⊗ Y)).chainComplex (R ⊗ S) ⟶ _ :=
    (TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)).singularChainComplexπ (R ⊗ S)
  let φ := relativeShuffle X Y A B R S
  let ψ := SSetPair.chainComplexMap
    (smallSingularSubcomplexPairToUnion (fst X Y ⁻¹' A) (snd X Y ⁻¹' B)) (R ⊗ S)
  have hsh : HomologicalComplex.tensorHom πA πB ≫ (φ ≫ ψ) = shuffle X Y R S ≫ πU :=
    (singularChainComplexπ_tensorHom_relativeShuffle_assoc X Y A B R S _).trans <|
      (Category.assoc _ _ _).trans <| whisker_eq _
      (chainComplexπ_smallSingularSubcomplexPairToUnion (R := R ⊗ S)
        (U := fst X Y ⁻¹' A) (V := snd X Y ⁻¹' B))
  exact (whisker_eq _ (whisker_eq _ (homologyMap_comp φ ψ n).symm)).trans <|
    (homologyCross_naturality_assoc πA πB p q n h (homologyMap (φ ≫ ψ) n)).trans <|
    (whisker_eq _ ((homologyMap_comp (HomologicalComplex.tensorHom πA πB) (φ ≫ ψ) n).symm.trans
      ((congrArg (homologyMap · n) hsh).trans (homologyMap_comp (shuffle X Y R S) πU n)))).trans <|
      (Category.assoc _ _ _).symm.trans
        (eq_whisker (singularHomologyCross_def X Y R S p q n h).symm _)

/-- **Naturality of `singularRelativeHomologyCross`** in pair maps `(f, g)`. -/
@[reassoc]
lemma singularRelativeHomologyCross_naturality
    {X Y X' Y' : TopCat.{w}} {A : Set X} {B : Set Y} {A' : Set X'} {B' : Set Y'}
    (f : X ⟶ X') (g : Y ⟶ Y') (hf : Set.MapsTo f A A') (hg : Set.MapsTo g B B')
    (R S : C) (p q n : ℕ) (h : p + q = n)
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorLeft (((TopPair.ofSubset A).singularChainComplex R).homology p))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((TopPair.ofSubset B).singularChainComplex S).cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((TopPair.ofSubset B).singularChainComplex S).X
        ((ComplexShape.down ℕ).prev q)))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorLeft (((TopPair.ofSubset A').singularChainComplex R).homology p))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((TopPair.ofSubset B').singularChainComplex S).cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((TopPair.ofSubset B').singularChainComplex S).X
        ((ComplexShape.down ℕ).prev q)))] :
    (TopPair.singularHomologyMap (TopPair.ofSubsetMap f hf) R p ⊗ₘ
        TopPair.singularHomologyMap (TopPair.ofSubsetMap g hg) S q) ≫
        singularRelativeHomologyCross X' Y' R S A' B' p q n h =
      singularRelativeHomologyCross X Y R S A B p q n h ≫
        TopPair.singularHomologyMap (TopPair.ofSubsetMap (f ⊗ₘ g)
          ((mapsTo_tensorHom_preimage_fst f g hf).union_union
            (mapsTo_tensorHom_preimage_snd f g hg))) (R ⊗ S) n := by
  let fA := TopPair.singularChainComplexMap (TopPair.ofSubsetMap f hf) R
  let fB := TopPair.singularChainComplexMap (TopPair.ofSubsetMap g hg) S
  let e := TopPair.singularChainComplexMap (TopPair.ofSubsetMap (f ⊗ₘ g)
    ((mapsTo_tensorHom_preimage_fst f g hf).union_union
      (mapsTo_tensorHom_preimage_snd f g hg))) (R ⊗ S)
  let φ := relativeShuffle X Y A B R S
  let ψ := SSetPair.chainComplexMap
    (smallSingularSubcomplexPairToUnion (fst X Y ⁻¹' A) (snd X Y ⁻¹' B)) (R ⊗ S)
  let φ' := relativeShuffle X' Y' A' B' R S
  let ψ' := SSetPair.chainComplexMap
    (smallSingularSubcomplexPairToUnion (fst X' Y' ⁻¹' A') (snd X' Y' ⁻¹' B')) (R ⊗ S)
  have hsmall : SSetPair.chainComplexMap (smallSingularSubcomplexPairMap (f ⊗ₘ g)
        (mapsTo_tensorHom_preimage_fst f g hf) (mapsTo_tensorHom_preimage_snd f g hg)) (R ⊗ S) ≫
      ψ' = ψ ≫ e :=
    (((SSetPair.chainComplexFunctor C).obj (R ⊗ S)).map_comp _ _).symm.trans <|
      (congrArg (SSetPair.chainComplexMap · (R ⊗ S))
        (smallSingularSubcomplexPairToUnion_comp_ofSubsetMap (f ⊗ₘ g)
          (mapsTo_tensorHom_preimage_fst f g hf)
          (mapsTo_tensorHom_preimage_snd f g hg)).symm).trans
        (((SSetPair.chainComplexFunctor C).obj (R ⊗ S)).map_comp _ _)
  have hsh : HomologicalComplex.tensorHom fA fB ≫ (φ' ≫ ψ') = (φ ≫ ψ) ≫ e :=
    (relativeShuffle_naturality_assoc f g hf hg R S _).trans
      ((whisker_eq _ hsmall).trans (Category.assoc _ _ _).symm)
  exact (whisker_eq _ (whisker_eq _ (homologyMap_comp φ' ψ' n).symm)).trans <|
    (homologyCross_naturality_assoc fA fB p q n h (homologyMap (φ' ≫ ψ') n)).trans <|
    (whisker_eq _ ((homologyMap_comp (HomologicalComplex.tensorHom fA fB) (φ' ≫ ψ') n).symm.trans
      ((congrArg (homologyMap · n) hsh).trans
        ((homologyMap_comp (φ ≫ ψ) e n).trans (eq_whisker (homologyMap_comp φ ψ n) _))))).trans
      (Category.assoc _ _ _).symm

/-- **Naturality of `singularRelativeHomologyCross`** in both coefficient objects. -/
@[reassoc]
lemma singularRelativeHomologyCross_coefficient_naturality
    (X Y : TopCat.{w}) (A : Set X) (B : Set Y) {R S R' S' : C} (φ : R ⟶ R') (ψ : S ⟶ S')
    (p q n : ℕ) (h : p + q = n)
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorLeft (((TopPair.ofSubset A).singularChainComplex R).homology p))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((TopPair.ofSubset B).singularChainComplex S).cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((TopPair.ofSubset B).singularChainComplex S).X
        ((ComplexShape.down ℕ).prev q)))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorLeft (((TopPair.ofSubset A).singularChainComplex R').homology p))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((TopPair.ofSubset B).singularChainComplex S').cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((TopPair.ofSubset B).singularChainComplex S').X
        ((ComplexShape.down ℕ).prev q)))] :
    (homologyMap (((SSetPair.chainComplexFunctor C).map φ).app
        (TopPair.toSSetPair.obj (TopPair.ofSubset A))) p ⊗ₘ
      homologyMap (((SSetPair.chainComplexFunctor C).map ψ).app
        (TopPair.toSSetPair.obj (TopPair.ofSubset B))) q) ≫
        singularRelativeHomologyCross X Y R' S' A B p q n h =
      singularRelativeHomologyCross X Y R S A B p q n h ≫
        homologyMap (((SSetPair.chainComplexFunctor C).map (φ ⊗ₘ ψ)).app
          (TopPair.toSSetPair.obj (TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)))) n := by
  let fA : (TopPair.ofSubset A).singularChainComplex R ⟶ _ :=
    ((SSetPair.chainComplexFunctor C).map φ).app (TopPair.toSSetPair.obj (TopPair.ofSubset A))
  let fB : (TopPair.ofSubset B).singularChainComplex S ⟶ _ :=
    ((SSetPair.chainComplexFunctor C).map ψ).app (TopPair.toSSetPair.obj (TopPair.ofSubset B))
  let e : (TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)).singularChainComplex (R ⊗ S) ⟶ _ :=
    ((SSetPair.chainComplexFunctor C).map (φ ⊗ₘ ψ)).app
      (TopPair.toSSetPair.obj (TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)))
  let s := relativeShuffle X Y A B R S
  let u := SSetPair.chainComplexMap
    (smallSingularSubcomplexPairToUnion (fst X Y ⁻¹' A) (snd X Y ⁻¹' B)) (R ⊗ S)
  let s' := relativeShuffle X Y A B R' S'
  let u' := SSetPair.chainComplexMap
    (smallSingularSubcomplexPairToUnion (fst X Y ⁻¹' A) (snd X Y ⁻¹' B)) (R' ⊗ S')
  have hsmall : ((SSetPair.chainComplexFunctor C).map (φ ⊗ₘ ψ)).app
      ((X ⊗ Y).smallSingularSubcomplex ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair ≫ u' = u ≫ e :=
    (((SSetPair.chainComplexFunctor C).map (φ ⊗ₘ ψ)).naturality
      (smallSingularSubcomplexPairToUnion (fst X Y ⁻¹' A) (snd X Y ⁻¹' B))).symm
  have hsh : HomologicalComplex.tensorHom fA fB ≫ (s' ≫ u') = (s ≫ u) ≫ e :=
    (relativeShuffle_coefficient_naturality_assoc X Y A B φ ψ _).trans
      ((whisker_eq _ hsmall).trans (Category.assoc _ _ _).symm)
  exact (whisker_eq _ (whisker_eq _ (homologyMap_comp s' u' n).symm)).trans <|
    (homologyCross_naturality_assoc fA fB p q n h (homologyMap (s' ≫ u') n)).trans <|
    (whisker_eq _ ((homologyMap_comp (HomologicalComplex.tensorHom fA fB) (s' ≫ u') n).symm.trans
      ((congrArg (homologyMap · n) hsh).trans
        ((homologyMap_comp (s ≫ u) e n).trans (eq_whisker (homologyMap_comp s u n) _))))).trans
      (Category.assoc _ _ _).symm

end HomologyCross

end TopCat
