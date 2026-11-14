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

For subsets `A ⊆ X` and `B ⊆ Y` and coefficient objects `R` and `S`, the relative homology cross
product is the morphism

`Hₚ(X, A; R) ⊗ H_q(Y, B; S) ⟶ Hₙ(X × Y, A × Y ∪ X × B; R ⊗ S)`, for `p + q = n`

(`TopCat.singularRelativeHomologyCross`), defined with no openness hypotheses on `A` or `B` by
composing `HomologicalComplex.homologyCross` with the relative shuffle map
`TopCat.relativeShuffle : C(X, A; R) ⊗ C(Y, B; S) ⟶ C(X × Y; A × Y + X × B; R ⊗ S)` and the
inclusion `TopCat.smallSingularSubcomplexPairToUnion` into `C(X × Y, A × Y ∪ X × B; R ⊗ S)`. As in
`TauCeti.AlgebraicTopology.Singular.CrossProduct`, each homology-level declaration assumes only that
`tensorLeft` of `Hₚ(X, A; R)` and `tensorRight` of `Z_q(Y, B; S)` and `C_{q+1}(Y, B; S)` preserve
cokernels (`PreservesColimitsOfShape WalkingParallelPair`), along with discrete colimit preservation
for `tensorLeft` and `tensorRight`; in `ModuleCat` these are found automatically.

At chain level, `TopCat.relativeShuffleAlexanderWhitneyHomotopy` shows that `TopCat.relativeShuffle`
is a chain-homotopy right inverse to `TopCat.relativeAlexanderWhitney`. That homotopy feeds the
Kronecker multiplicativity of relative cross products in
`TauCeti.AlgebraicTopology.Cohomology.Cup.Kronecker`, which in turn detects local-cohomology and
Thom-class cross-product generators without flatness or Künneth hypotheses.

## Main definitions and results

* `SSetPair.shortExact_tensorLeftShortComplex_chainComplexShortComplex`,
  `SSetPair.shortExact_tensorRightShortComplex_chainComplexShortComplex`,
  `TopPair.shortExact_tensorLeftShortComplex_singularChainComplexShortComplex`,
  `TopPair.shortExact_tensorRightShortComplex_singularChainComplexShortComplex`,
  `SSetPair.isSplitEpi_chainComplexπ_tensorHom_f`, and `SSetPair.epi_chainComplexπ_tensorHom`:
  tensoring preserves the relative chain short exact sequence of any simplicial or topological pair,
  and `chainComplexπ ⊗ₘ chainComplexπ` (hence `singularChainComplexπ ⊗ₘ singularChainComplexπ`) is a
  degreewise split epimorphism and chain-complex epimorphism.
* `TopCat.relativeShuffle`: the relative shuffle chain map, characterized by
  `TopCat.singularChainComplexπ_tensorHom_relativeShuffle` and natural in pairs and coefficients.
* `TopCat.relativeShuffleAlexanderWhitneyHomotopy`: the relative Eilenberg–Zilber chain homotopy
  from `relativeShuffle ≫ relativeAlexanderWhitney` to `𝟙 _`, characterized degreewise by
  `TopCat.singularChainComplexπ_tensorHom_f_relativeShuffleAlexanderWhitneyHomotopy_hom`.
* `TopCat.singularRelativeHomologyCross`: the relative homology cross product, evaluated on classes
  of cycles by `TopCat.homologyπ_tensorHom_singularRelativeHomologyCross`, compatible with
  `TopCat.singularHomologyCross`
  (`TopCat.singularHomologyπ_tensorHom_singularRelativeHomologyCross`), and natural in pairs
  (`TopCat.singularRelativeHomologyCross_naturality`) and coefficients
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

/-- Cache `MonoidalCategory (ChainComplex C ℕ)` under `[Preadditive C]` before `[Abelian C]` enters
scope so `[Abelian C]` does not push the synthesis term size past `synthInstance.maxSize`. -/
local instance instMonoidalCategoryChainComplex {C : Type u} [Category.{v} C] [Preadditive C]
    [HasCoproducts.{w} C] [MonoidalCategory C] [MonoidalPreadditive C] :
    MonoidalCategory (ChainComplex C ℕ) :=
  inferInstance

namespace SSetPair

section ShortExact

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
  [MonoidalCategory C] [MonoidalPreadditive C]

/-- The tensor product `P.chainComplexπ R ⊗ₘ Q.chainComplexπ S` of relative chain quotient maps of
simplicial (or topological) pairs is a split epimorphism in each degree. -/
instance isSplitEpi_chainComplexπ_tensorHom_f (P Q : SSetPair.{w}) (R S : C) (i : ℕ) :
    IsSplitEpi ((P.chainComplexπ R ⊗ₘ Q.chainComplexπ S).f i) :=
  inferInstance

/-- The tensor product `P.chainComplexπ R ⊗ₘ Q.chainComplexπ S` of relative chain quotient maps of
simplicial (or topological) pairs is an epimorphism of chain complexes. -/
instance epi_chainComplexπ_tensorHom (P Q : SSetPair.{w}) (R S : C) :
    Epi (P.chainComplexπ R ⊗ₘ Q.chainComplexπ S) :=
  inferInstance

/-- Tensoring on the left with `K` preserves the relative chain short exact sequence
`0 ⟶ C(A; R) ⟶ C(X; R) ⟶ C(X, A; R) ⟶ 0` of a simplicial pair `P = (X, A)`. -/
theorem shortExact_tensorLeftShortComplex_chainComplexShortComplex
    (K : ChainComplex C ℕ) (P : SSetPair.{w}) (R : C) :
    (tensorLeftShortComplex K (P.chainComplexShortComplex R)).ShortExact :=
  shortExact_tensorLeftShortComplex K (P.shortExact_chainComplexShortComplex R)

/-- Tensoring on the right with `K` preserves the relative chain short exact sequence
`0 ⟶ C(A; R) ⟶ C(X; R) ⟶ C(X, A; R) ⟶ 0` of a simplicial pair `P = (X, A)`. -/
theorem shortExact_tensorRightShortComplex_chainComplexShortComplex
    (K : ChainComplex C ℕ) (P : SSetPair.{w}) (R : C) :
    (tensorRightShortComplex K (P.chainComplexShortComplex R)).ShortExact :=
  shortExact_tensorRightShortComplex K _ (P.shortExact_chainComplexShortComplex R)

end ShortExact

end SSetPair

namespace TopPair

section ShortExact

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
  [MonoidalCategory C] [MonoidalPreadditive C]

/-- Tensoring on the left with `K` preserves the singular chain short exact sequence
`0 ⟶ C(A; R) ⟶ C(X; R) ⟶ C(X, A; R) ⟶ 0` of a topological pair `P = (X, A)`. -/
theorem shortExact_tensorLeftShortComplex_singularChainComplexShortComplex
    (K : ChainComplex C ℕ) (P : TopPair.{w}) (R : C) :
    (tensorLeftShortComplex K (P.singularChainComplexShortComplex R)).ShortExact :=
  (toSSetPair.obj P).shortExact_tensorLeftShortComplex_chainComplexShortComplex K R

/-- Tensoring on the right with `K` preserves the singular chain short exact sequence
`0 ⟶ C(A; R) ⟶ C(X; R) ⟶ C(X, A; R) ⟶ 0` of a topological pair `P = (X, A)`. -/
theorem shortExact_tensorRightShortComplex_singularChainComplexShortComplex
    (K : ChainComplex C ℕ) (P : TopPair.{w}) (R : C) :
    (tensorRightShortComplex K (P.singularChainComplexShortComplex R)).ShortExact :=
  (toSSetPair.obj P).shortExact_tensorRightShortComplex_chainComplexShortComplex K R

end ShortExact

end TopPair

namespace TopCat

section ChainLevel

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
  [MonoidalCategory C] [MonoidalPreadditive C]

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
  (CokernelCofork.IsColimit.desc'
    (TopPair.shortExact_tensorRightShortComplex_singularChainComplexShortComplex
      ((toSSet.obj Y).chainComplex S) (TopPair.ofSubset A) R).gIsCokernel
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
  (CokernelCofork.IsColimit.desc'
    (TopPair.shortExact_tensorRightShortComplex_singularChainComplexShortComplex
      ((toSSet.obj Y).chainComplex S) (TopPair.ofSubset A) R).gIsCokernel _
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
  (CokernelCofork.IsColimit.desc'
    (TopPair.shortExact_tensorLeftShortComplex_singularChainComplexShortComplex
      ((TopPair.ofSubset A).singularChainComplex R) (TopPair.ofSubset B) S).gIsCokernel
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
    (CokernelCofork.IsColimit.desc'
      (TopPair.shortExact_tensorLeftShortComplex_singularChainComplexShortComplex
        ((TopPair.ofSubset A).singularChainComplex R) (TopPair.ofSubset B) S).gIsCokernel _
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
        ((TopPair.ofSubset A).singularChainComplexShortComplex R)).f.f i ≫
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
          ((TopPair.ofSubset B).singularChainComplexShortComplex S)).g ≫
        (relativeShuffle X Y A B R S ≫ relativeAlexanderWhitney X Y A B R S))
      (tensorLeftShortComplex ((TopPair.ofSubset A).singularChainComplex R)
        ((TopPair.ofSubset B).singularChainComplexShortComplex S)).g := by
  let S₁ := tensorRightShortComplex ((toSSet.obj Y).chainComplex S)
    ((TopPair.ofSubset A).singularChainComplexShortComplex R)
  have hfac : S₁.g ≫ (tensorLeftShortComplex ((TopPair.ofSubset A).singularChainComplex R)
      ((TopPair.ofSubset B).singularChainComplexShortComplex S)).g =
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
      (TopPair.shortExact_tensorRightShortComplex_singularChainComplexShortComplex
        ((toSSet.obj Y).chainComplex S) (TopPair.ofSubset A) R) i).gIsCokernel)
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
        ((TopPair.ofSubset B).singularChainComplexShortComplex S)).f.f i ≫
      (leftRelativeShuffleAlexanderWhitneyHomotopy X Y A B R S).hom i j ≫
      HomologicalComplex.Hom.f (𝟙 ((TopPair.ofSubset A).singularChainComplex R ⊗
        (TopPair.ofSubset B).singularChainComplex S)) j = 0 := by
  let pA := (TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
    𝟙 ((TopPair.toSSetPair.obj (TopPair.ofSubset B)).left.chainComplex S)
  rw [← cancel_epi (pA.f i), comp_zero, HomologicalComplex.id_f, Category.comp_id]
  have hcomm : pA ≫ (tensorLeftShortComplex ((TopPair.ofSubset A).singularChainComplex R)
        ((TopPair.ofSubset B).singularChainComplexShortComplex S)).f =
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
    ((TopPair.ofSubset B).singularChainComplexShortComplex S)
  _root_.Homotopy.descCokernel
    (leftRelativeShuffleAlexanderWhitneyHomotopy X Y A B R S) S₂.f S₂.g (𝟙 _)
    (fun i ↦ (HomologicalComplex.comp_f S₂.f S₂.g i).symm.trans
      ((HomologicalComplex.congr_hom S₂.zero i).trans (HomologicalComplex.zero_f _ _ i)))
    (fun i ↦ ((shortExact_iff_degreewise_shortExact S₂).1
      (TopPair.shortExact_tensorLeftShortComplex_singularChainComplexShortComplex
        ((TopPair.ofSubset A).singularChainComplex R) (TopPair.ofSubset B) S) i).gIsCokernel)
    (rightFactor_comp_leftRelativeShuffleAlexanderWhitneyHomotopy_hom X Y A B R S)
    (Category.comp_id _).symm rfl

/-- Precomposing the degree-`(i, j)` component of `TopCat.relativeShuffleAlexanderWhitneyHomotopy`
with the tensor product of the chain quotient maps intertwines it with the simplicial
Eilenberg–Zilber homotopy `SSet.shuffleAlexanderWhitneyHomotopy`. -/
@[reassoc (attr := simp)]
lemma singularChainComplexπ_tensorHom_f_relativeShuffleAlexanderWhitneyHomotopy_hom
    (X Y : TopCat.{w}) (A : Set X) (B : Set Y) (R S : C) (i j : ℕ) :
    ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
        (TopPair.ofSubset B).singularChainComplexπ S).f i ≫
      (relativeShuffleAlexanderWhitneyHomotopy X Y A B R S).hom i j =
      (SSet.shuffleAlexanderWhitneyHomotopy (toSSet.obj X) (toSSet.obj Y) R S).hom i j ≫
        ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
          (TopPair.ofSubset B).singularChainComplexπ S).f j := by
  have hdesc : (𝟙 ((TopPair.ofSubset A).singularChainComplex R) ⊗ₘ
      (TopPair.ofSubset B).singularChainComplexπ S).f i ≫
      (relativeShuffleAlexanderWhitneyHomotopy X Y A B R S).hom i j =
      (leftRelativeShuffleAlexanderWhitneyHomotopy X Y A B R S).hom i j := by
    unfold relativeShuffleAlexanderWhitneyHomotopy
    exact (_root_.Homotopy.π_descCokernel_hom _ _ _ _ _ _ _ _ _ i j).trans (Category.comp_id _)
  have hfac : ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
      (TopPair.ofSubset B).singularChainComplexπ S) =
      ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ 𝟙 ((toSSet.obj Y).chainComplex S)) ≫
        (𝟙 ((TopPair.ofSubset A).singularChainComplex R) ⊗ₘ
          (TopPair.ofSubset B).singularChainComplexπ S) :=
    ((tensorHom_comp_tensorHom ((TopPair.toSSetPair.obj (TopPair.ofSubset A)).chainComplexπ R)
      (𝟙 ((toSSet.obj Y).chainComplex S)) (𝟙 ((TopPair.ofSubset A).singularChainComplex R))
      ((TopPair.toSSetPair.obj (TopPair.ofSubset B)).chainComplexπ S)).trans
      (congrArg₂ (· ⊗ₘ ·) (Category.comp_id _) (Category.id_comp _))).symm
  exact (eq_whisker ((HomologicalComplex.congr_hom hfac i).trans
      (HomologicalComplex.comp_f _ _ i)) _).trans <|
    (Category.assoc _ _ _).trans <|
      (whisker_eq _ hdesc).trans
        (π_leftRelativeShuffleAlexanderWhitneyHomotopy_hom X Y A B R S i j)

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

/-- Transport a chain-level commutative square `tensorHom fA fB ≫ (φ' ≫ ψ') = g ≫ e` across
`HomologicalComplex.homologyCross` and `HomologicalComplex.homologyMap`. -/
private lemma homologyMap_tensorHom_homologyCross_comp
    {K₁ K₂ L₁ L₂ M' N N' : ChainComplex C ℕ}
    (fA : K₁ ⟶ L₁) (fB : K₂ ⟶ L₂) (φ' : L₁ ⊗ L₂ ⟶ M') (ψ' : M' ⟶ N')
    (g : K₁ ⊗ K₂ ⟶ N) (e : N ⟶ N') (p q n : ℕ) (h : p + q = n)
    [PreservesColimitsOfShape WalkingParallelPair (tensorLeft (K₁.homology p))]
    [PreservesColimitsOfShape WalkingParallelPair (tensorRight (K₂.cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (K₂.X ((ComplexShape.down ℕ).prev q)))]
    [PreservesColimitsOfShape WalkingParallelPair (tensorLeft (L₁.homology p))]
    [PreservesColimitsOfShape WalkingParallelPair (tensorRight (L₂.cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (L₂.X ((ComplexShape.down ℕ).prev q)))]
    (hsh : HomologicalComplex.tensorHom fA fB ≫ (φ' ≫ ψ') = g ≫ e) :
    (homologyMap fA p ⊗ₘ homologyMap fB q) ≫
        homologyCross L₁ L₂ p q n h ≫ homologyMap φ' n ≫ homologyMap ψ' n =
      (homologyCross K₁ K₂ p q n h ≫ homologyMap g n) ≫ homologyMap e n := by
  rw [← homologyMap_comp φ' ψ' n, homologyCross_naturality_assoc, ← homologyMap_comp, hsh,
    homologyMap_comp, ← Category.assoc]

variable [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft T)]
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
@[reassoc (attr := simp)]
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
@[reassoc (attr := simp)]
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
  exact (homologyMap_tensorHom_homologyCross_comp πA πB φ ψ (shuffle X Y R S) πU p q n h hsh).trans
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
  rw [singularRelativeHomologyCross_def, singularRelativeHomologyCross_def,
    homologyMap_tensorHom_homologyCross_comp fA fB φ' ψ' (φ ≫ ψ) e p q n h hsh,
    homologyMap_comp φ ψ n, Category.assoc]

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
  rw [singularRelativeHomologyCross_def, singularRelativeHomologyCross_def,
    homologyMap_tensorHom_homologyCross_comp fA fB s' u' (s ≫ u) e p q n h hsh,
    homologyMap_comp s u n, Category.assoc]

end HomologyCross

end TopCat
