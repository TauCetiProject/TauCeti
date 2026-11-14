/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.Homology.Kronecker
public import TauCeti.AlgebraicTopology.Cohomology.Kronecker
public import TauCeti.AlgebraicTopology.Cohomology.Cup.Relative
public import TauCeti.AlgebraicTopology.Singular.RelativeCrossProduct

/-!
# The Kronecker pairing of relative cross and cup products

For open subsets `A ⊆ X` and `B ⊆ Y`, the relative cohomology cross product
`TauCeti.singularRelativeCross` pairs `Hᵖ(X, A; R, M)` and `H^q(Y, B; S, N)` into
`Hⁿ(X × Y, A × Y ∪ X × B; R ⊗ S, L)` (`p + q = n`), while `TopCat.singularRelativeHomologyCross`
maps `Hₚ(X, A; R) ⊗ H_q(Y, B; S)` into `Hₙ(X × Y, A × Y ∪ X × B; R ⊗ S)`. Under the small-chain
isomorphism (`TauCeti.homologyMap_cochainComplexMap_singularRelativeCross`) and the relative
Eilenberg–Zilber homotopy (`TopCat.relativeShuffleAlexanderWhitneyHomotopy`), their Kronecker
pairing reduces to `ChainComplex.homologyCross_comp_kronecker_cup`: `⟨a × b, x × y⟩ =
μ (⟨a, x⟩ ⊗ ⟨b, y⟩)` with no sign
(`TopCat.singularRelativeHomologyCross_comp_singularKronecker_singularRelativeCross`), and `0` when
degrees differ
(`TopCat.singularRelativeHomologyCross_comp_singularKronecker_singularRelativeCross_of_ne`).

Via `TauCeti.singularRelativeCup_eq_homologyMap_singularRelativeCup`, when `v ≫ u = 𝟙 (R ⊗ S)` and
`Z` agrees with `fst⁻¹(A) ∪ snd⁻¹(B)`, pushing `TopCat.singularRelativeHomologyCross` forward along
`v` pairs multiplicatively with `TopCat.singularRelativeCupPullback` along `fst` and `snd`
(`TopCat.singularRelativeHomologyCross_comp_singularKronecker_singularRelativeCupPullback`,
`TopCat.singularRelativeHomologyCross_comp_singularKronecker_singularRelativeCupPullback_of_ne`).

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), §§3.2, 3.B.
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

section KroneckerPairing

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
  [MonoidalCategory C] [MonoidalPreadditive C]
  {k : Type*} [CommRing k] [Linear k C] [MonoidalLinear k C]
  {R S T M N L : C}

/-- Reduction of Kronecker evaluation of `TopCat.singularRelativeCupPullback` along `fst` and `snd`
to `TauCeti.singularRelativeCross` when `v ≫ u = 𝟙 (R ⊗ S)` and `Z` agrees with
`fst⁻¹(A) ∪ snd⁻¹(B)`. -/
private lemma homologyMap_comp_singularKronecker_singularRelativeCupPullback
    (X Y : TopCat.{w}) {A : Set X} {B : Set Y} (hA : IsOpen A) (hB : IsOpen B)
    {Z : Set ↥(X ⊗ Y)} (hZ : Z ⊆ fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)
    (hZ' : fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B ⊆ Z)
    {v : R ⊗ S ⟶ T} {u : T ⟶ R ⊗ S} (hu : v ≫ u = 𝟙 (R ⊗ S)) (μ : M ⊗ N ⟶ L)
    (p q n : ℕ) (h : p + q = n)
    (a : (TopPair.ofSubset A).singularCohomology R k M p)
    (b : (TopPair.ofSubset B).singularCohomology S k N q) :
    homologyMap
        (K := (TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)).singularChainComplex (R ⊗ S))
        (L := (TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)).singularChainComplex T)
        (((SSetPair.chainComplexFunctor C).map v).app
          (TopPair.toSSetPair.obj (TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)))) n ≫
      TopPair.singularHomologyMap
        (TopPair.ofSubsetMap (B := fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B) (B' := Z)
          (𝟙 (X ⊗ Y)) fun _ hx ↦ hZ' hx) T n ≫
      (TopPair.ofSubset Z).singularKronecker (R := T) (M := L) k n
        (singularRelativeCupPullback k u μ (fst X Y) (snd X Y) hA hB hZ p q n h a b) =
      (TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)).singularKronecker (R := R ⊗ S) (M := L)
        k n (TauCeti.singularRelativeCross k X Y hA hB μ p q n h a b) := by
  let i₁ := TopPair.ofSubsetMap (B := fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B) (B' := Z)
    (𝟙 (X ⊗ Y)) fun _ hx ↦ hZ' hx
  let i₂ := TopPair.ofSubsetMap (B := Z) (B' := fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)
    (𝟙 (X ⊗ Y)) fun _ hx ↦ hZ hx
  have hpair : i₁ ≫ i₂ = 𝟙 (TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)) :=
    (TopPair.ofSubsetMap_comp_ofSubsetMap_of_comp_eq _ _ (fun _ hx ↦ hx)
      (Category.comp_id _)).trans (TopPair.ofSubsetMap_id fun _ hx ↦ hx)
  have hidZ : TopPair.singularHomologyMap i₁ T n ≫ TopPair.singularHomologyMap i₂ T n = 𝟙 _ := by
    rw [← TopPair.singularHomologyMap_comp, hpair, TopPair.singularHomologyMap_id]
  let P := TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)
  let ev : P.singularChainComplex (R ⊗ S) ⟶ P.singularChainComplex T :=
    ((SSetPair.chainComplexFunctor C).map v).app (TopPair.toSSetPair.obj P)
  let eu : P.singularChainComplex T ⟶ P.singularChainComplex (R ⊗ S) :=
    ((SSetPair.chainComplexFunctor C).map u).app (TopPair.toSSetPair.obj P)
  have hvu : homologyMap ev n ≫ homologyMap eu n = 𝟙 _ := by
    have hchain : ev ≫ eu = 𝟙 (P.singularChainComplex (R ⊗ S)) := by
      simp only [ev, eu, ← NatTrans.comp_app, ← (SSetPair.chainComplexFunctor C).map_comp, hu,
        (SSetPair.chainComplexFunctor C).map_id, NatTrans.id_app]
    rw [← homologyMap_comp, hchain, homologyMap_id]
  rw [singularRelativeCupPullback_apply, TopPair.singularKronecker_naturality,
    ← Category.assoc (TopPair.singularHomologyMap i₁ T n), hidZ, Category.id_comp,
    TauCeti.singularRelativeCup_eq_homologyMap_singularRelativeCup,
    ← TauCeti.singularRelativeCross_apply k X Y hA hB, TopPair.singularKronecker_def,
    TopPair.singularKronecker_def]
  exact (whisker_eq _ (TauCeti.ChainComplex.kronecker_naturality eu n _)).trans
    ((Category.assoc _ _ _).symm.trans ((eq_whisker hvu _).trans (Category.id_comp _)))

variable [∀ (Z : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft Z)]
  [∀ (Z : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight Z)]

/-- Along `relativeShuffle` and `smallSingularSubcomplexPairToUnion`, the Kronecker pairing of
`TauCeti.singularRelativeCross` reduces to `ChainComplex.cup` along `𝟙 _`. -/
private lemma homologyMap_relativeShuffle_comp_singularKronecker_singularRelativeCross
    (X Y : TopCat.{w}) {A : Set X} {B : Set Y} (hA : IsOpen A) (hB : IsOpen B)
    (μ : M ⊗ N ⟶ L) (p q n : ℕ) (h : p + q = n)
    (a : (TopPair.ofSubset A).singularCohomology R k M p)
    (b : (TopPair.ofSubset B).singularCohomology S k N q) :
    homologyMap (relativeShuffle X Y A B R S) n ≫
        SSetPair.homologyMap
          (smallSingularSubcomplexPairToUnion (fst X Y ⁻¹' A) (snd X Y ⁻¹' B)) (R ⊗ S) n ≫
        TauCeti.ChainComplex.kronecker k
          ((TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)).singularChainComplex (R ⊗ S)) L n
          (TauCeti.singularRelativeCross k X Y hA hB μ p q n h a b) =
      TauCeti.ChainComplex.kronecker k
        (HomologicalComplex.tensorObj ((TopPair.ofSubset A).singularChainComplex R)
          ((TopPair.ofSubset B).singularChainComplex S)) L n
        (TauCeti.ChainComplex.cup k
          (𝟙 (HomologicalComplex.tensorObj ((TopPair.ofSubset A).singularChainComplex R)
            ((TopPair.ofSubset B).singularChainComplex S))) μ p q n h a b) := by
  have hk₁ : SSetPair.homologyMap
        (smallSingularSubcomplexPairToUnion (fst X Y ⁻¹' A) (snd X Y ⁻¹' B)) (R ⊗ S) n ≫
      TauCeti.ChainComplex.kronecker k
        ((TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)).singularChainComplex (R ⊗ S)) L n
        (TauCeti.singularRelativeCross k X Y hA hB μ p q n h a b) =
      TauCeti.ChainComplex.kronecker k
        (((X ⊗ Y).smallSingularSubcomplex ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.chainComplex
          (R ⊗ S)) L n
        (TauCeti.ChainComplex.cup k (relativeAlexanderWhitney X Y A B R S) μ p q n h a b) := by
    rw [← TauCeti.homologyMap_cochainComplexMap_singularRelativeCross k X Y hA hB μ p q n h a b]
    exact (TauCeti.ChainComplex.kronecker_naturality (k := k)
      (SSetPair.chainComplexMap
        (smallSingularSubcomplexPairToUnion (fst X Y ⁻¹' A) (snd X Y ⁻¹' B)) (R ⊗ S)) n _).symm
  have hcup := (TauCeti.ChainComplex.cup_precomp (relativeAlexanderWhitney X Y A B R S) μ
      (relativeShuffle X Y A B R S) p q n h a b).symm.trans
    (TauCeti.ChainComplex.cup_eq_of_homotopy _ μ
      (relativeShuffleAlexanderWhitneyHomotopy X Y A B R S) p q n h a b)
  exact (whisker_eq _ hk₁).trans <|
    (TauCeti.ChainComplex.kronecker_naturality (k := k)
        (relativeShuffle X Y A B R S) n _).symm.trans
      (congrArg (TauCeti.ChainComplex.kronecker k
        (HomologicalComplex.tensorObj ((TopPair.ofSubset A).singularChainComplex R)
          ((TopPair.ofSubset B).singularChainComplex S)) L n) hcup)

/-- **The Kronecker pairing of relative cross products**, `⟨a × b, x × y⟩ = μ (⟨a, x⟩ ⊗ ⟨b, y⟩)`
for open `A ⊆ X` and `B ⊆ Y`. -/
theorem singularRelativeHomologyCross_comp_singularKronecker_singularRelativeCross
    (X Y : TopCat.{w}) {A : Set X} {B : Set Y} (hA : IsOpen A) (hB : IsOpen B)
    (μ : M ⊗ N ⟶ L) (p q n : ℕ) (h : p + q = n)
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorLeft (((TopPair.ofSubset A).singularChainComplex R).homology p))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((TopPair.ofSubset B).singularChainComplex S).cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((TopPair.ofSubset B).singularChainComplex S).X
        ((ComplexShape.down ℕ).prev q)))]
    (a : (TopPair.ofSubset A).singularCohomology R k M p)
    (b : (TopPair.ofSubset B).singularCohomology S k N q) :
    singularRelativeHomologyCross X Y R S A B p q n h ≫
        (TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)).singularKronecker (R := R ⊗ S) (M := L)
          k n (TauCeti.singularRelativeCross k X Y hA hB μ p q n h a b) =
      ((TopPair.ofSubset A).singularKronecker (R := R) (M := M) k p a ⊗ₘ
        (TopPair.ofSubset B).singularKronecker (R := S) (M := N) k q b) ≫ μ := by
  simp only [singularRelativeHomologyCross_def, TopPair.singularKronecker_def]
  exact (Category.assoc _ _ _).trans <|
    (whisker_eq _ ((Category.assoc _ _ _).trans
      (homologyMap_relativeShuffle_comp_singularKronecker_singularRelativeCross
        X Y hA hB μ p q n h a b))).trans
    (ChainComplex.homologyCross_comp_kronecker_cup _ _ μ p q n h a b)

/-- **Off-diagonal vanishing for relative cross products** when `p ≠ p'`. -/
theorem singularRelativeHomologyCross_comp_singularKronecker_singularRelativeCross_of_ne
    (X Y : TopCat.{w}) {A : Set X} {B : Set Y} (hA : IsOpen A) (hB : IsOpen B)
    (μ : M ⊗ N ⟶ L) {p q p' q' n : ℕ} (h : p + q = n) (h' : p' + q' = n) (hp : p ≠ p')
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorLeft (((TopPair.ofSubset A).singularChainComplex R).homology p))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((TopPair.ofSubset B).singularChainComplex S).cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((TopPair.ofSubset B).singularChainComplex S).X
        ((ComplexShape.down ℕ).prev q)))]
    (a : (TopPair.ofSubset A).singularCohomology R k M p')
    (b : (TopPair.ofSubset B).singularCohomology S k N q') :
    singularRelativeHomologyCross X Y R S A B p q n h ≫
        (TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)).singularKronecker (R := R ⊗ S) (M := L)
          k n (TauCeti.singularRelativeCross k X Y hA hB μ p' q' n h' a b) = 0 := by
  simp only [singularRelativeHomologyCross_def, TopPair.singularKronecker_def]
  exact (Category.assoc _ _ _).trans <|
    (whisker_eq _ ((Category.assoc _ _ _).trans
      (homologyMap_relativeShuffle_comp_singularKronecker_singularRelativeCross
        X Y hA hB μ p' q' n h' a b))).trans
    (ChainComplex.homologyCross_comp_kronecker_cup_of_ne _ _ μ p q h h' hp a b)

/-- **The Kronecker pairing of `TopCat.singularRelativeCupPullback` along `fst` and `snd`** when
`v ≫ u = 𝟙 (R ⊗ S)` and `Z` agrees with `fst⁻¹(A) ∪ snd⁻¹(B)`. -/
theorem singularRelativeHomologyCross_comp_singularKronecker_singularRelativeCupPullback
    (X Y : TopCat.{w}) {A : Set X} {B : Set Y} (hA : IsOpen A) (hB : IsOpen B)
    {Z : Set ↥(X ⊗ Y)} (hZ : Z ⊆ fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)
    (hZ' : fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B ⊆ Z)
    {v : R ⊗ S ⟶ T} {u : T ⟶ R ⊗ S} (hu : v ≫ u = 𝟙 (R ⊗ S)) (μ : M ⊗ N ⟶ L)
    (p q n : ℕ) (h : p + q = n)
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorLeft (((TopPair.ofSubset A).singularChainComplex R).homology p))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((TopPair.ofSubset B).singularChainComplex S).cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((TopPair.ofSubset B).singularChainComplex S).X
        ((ComplexShape.down ℕ).prev q)))]
    (a : (TopPair.ofSubset A).singularCohomology R k M p)
    (b : (TopPair.ofSubset B).singularCohomology S k N q) :
    singularRelativeHomologyCross X Y R S A B p q n h ≫
        homologyMap
          (K := (TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)).singularChainComplex (R ⊗ S))
          (L := (TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)).singularChainComplex T)
          (((SSetPair.chainComplexFunctor C).map v).app
            (TopPair.toSSetPair.obj (TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)))) n ≫
        TopPair.singularHomologyMap
          (TopPair.ofSubsetMap (B := fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B) (B' := Z)
            (𝟙 (X ⊗ Y)) fun _ hx ↦ hZ' hx) T n ≫
        (TopPair.ofSubset Z).singularKronecker (R := T) (M := L) k n
          (singularRelativeCupPullback k u μ (fst X Y) (snd X Y) hA hB hZ p q n h a b) =
      ((TopPair.ofSubset A).singularKronecker (R := R) (M := M) k p a ⊗ₘ
        (TopPair.ofSubset B).singularKronecker (R := S) (M := N) k q b) ≫ μ :=
  (whisker_eq _ (homologyMap_comp_singularKronecker_singularRelativeCupPullback
    X Y hA hB hZ hZ' hu μ p q n h a b)).trans
    (singularRelativeHomologyCross_comp_singularKronecker_singularRelativeCross
      X Y hA hB μ p q n h a b)

/-- **Off-diagonal vanishing for `TopCat.singularRelativeCupPullback` along `fst` and `snd`** when
`p ≠ p'`, `v ≫ u = 𝟙 (R ⊗ S)`, and `Z` agrees with `fst⁻¹(A) ∪ snd⁻¹(B)`. -/
theorem singularRelativeHomologyCross_comp_singularKronecker_singularRelativeCupPullback_of_ne
    (X Y : TopCat.{w}) {A : Set X} {B : Set Y} (hA : IsOpen A) (hB : IsOpen B)
    {Z : Set ↥(X ⊗ Y)} (hZ : Z ⊆ fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)
    (hZ' : fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B ⊆ Z)
    {v : R ⊗ S ⟶ T} {u : T ⟶ R ⊗ S} (hu : v ≫ u = 𝟙 (R ⊗ S)) (μ : M ⊗ N ⟶ L)
    {p q p' q' n : ℕ} (h : p + q = n) (h' : p' + q' = n) (hp : p ≠ p')
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorLeft (((TopPair.ofSubset A).singularChainComplex R).homology p))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((TopPair.ofSubset B).singularChainComplex S).cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((TopPair.ofSubset B).singularChainComplex S).X
        ((ComplexShape.down ℕ).prev q)))]
    (a : (TopPair.ofSubset A).singularCohomology R k M p')
    (b : (TopPair.ofSubset B).singularCohomology S k N q') :
    singularRelativeHomologyCross X Y R S A B p q n h ≫
        homologyMap
          (K := (TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)).singularChainComplex (R ⊗ S))
          (L := (TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)).singularChainComplex T)
          (((SSetPair.chainComplexFunctor C).map v).app
            (TopPair.toSSetPair.obj (TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)))) n ≫
        TopPair.singularHomologyMap
          (TopPair.ofSubsetMap (B := fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B) (B' := Z)
            (𝟙 (X ⊗ Y)) fun _ hx ↦ hZ' hx) T n ≫
        (TopPair.ofSubset Z).singularKronecker (R := T) (M := L) k n
          (singularRelativeCupPullback k u μ (fst X Y) (snd X Y) hA hB hZ p' q' n h' a b) = 0 :=
  (whisker_eq _ (homologyMap_comp_singularKronecker_singularRelativeCupPullback
    X Y hA hB hZ hZ' hu μ p' q' n h' a b)).trans
    (singularRelativeHomologyCross_comp_singularKronecker_singularRelativeCross_of_ne
      X Y hA hB μ h h' hp a b)

end KroneckerPairing

end TopCat
