/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cup.Relative
public import TauCeti.AlgebraicTopology.Singular.CrossProduct.Relative

/-!
# The Kronecker pairing of relative cross products and pulled-back cup products

For open `A ⊆ X` and `B ⊆ Y`, `TauCeti.singularRelativeCross` and
`TopCat.singularRelativeHomologyCross` are dual under `TopPair.singularKronecker` with no sign
(`⟨a × b, x × y⟩ = μ (⟨a, x⟩ ⊗ ⟨b, y⟩)` in matching bidegrees, `0` when `p ≠ p'`), extending to
`TopCat.singularRelativeCupPullback` along `fst` and `snd` when `Z = fst⁻¹(A) ∪ snd⁻¹(B)` and
`v ≫ u = 𝟙 (R ⊗ S)`. This Kronecker multiplicativity detects local-cohomology and Thom-pair
cross-product generators in `TauCeti.AlgebraicTopology.Cohomology.Local.Cross` and
`TauCeti.Topology.VectorBundle.Thom.Prod` over arbitrary commutative rings without flatness or
Künneth hypotheses. Each theorem assumes discrete colimit preservation for
`tensorLeft`/`tensorRight` and `WalkingParallelPair` colimit preservation for `tensorLeft` of
`Hₚ(X, A; R)` and `tensorRight` of `Z_q(Y, B; S)` and `C_{q+1}(Y, B; S)`.

## Main results

* `TopCat.singularRelativeHomologyCross_comp_singularKronecker_singularRelativeCross` and
  `TopCat.singularRelativeHomologyCross_comp_singularKronecker_singularRelativeCross_of_ne`:
  Kronecker multiplicativity `⟨a × b, x × y⟩ = μ (⟨a, x⟩ ⊗ ⟨b, y⟩)` in matching bidegrees and
  off-diagonal vanishing (`p ≠ p'`) for relative cross products.
* `TopCat.singularRelativeHomologyCross_comp_singularKronecker_singularRelativeCupPullback` and
  `TopCat.singularRelativeHomologyCross_comp_singularKronecker_singularRelativeCupPullback_of_ne`:
  the corresponding diagonal and off-diagonal Kronecker pairings for
  `TopCat.singularRelativeCupPullback` along `fst` and `snd` with split chain-coefficient pairing
  `v ≫ u = 𝟙 (R ⊗ S)`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), §§3.2, 3.B.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicTopology
  HomologicalComplex

universe w v u

namespace TopCat

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
  [MonoidalCategory C] [MonoidalPreadditive C]
  {k : Type*} [CommRing k] [Linear k C] [MonoidalLinear k C] {R S T M N L : C}

private lemma homologyMap_comp_singularKronecker_singularRelativeCupPullback
    (X Y : TopCat.{w}) {A : Set X} {B : Set Y} (hA : IsOpen A) (hB : IsOpen B)
    {Z : Set ↥(X ⊗ Y)} (hZ : Z ⊆ fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)
    (hZ' : fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B ⊆ Z)
    {v : R ⊗ S ⟶ T} {u : T ⟶ R ⊗ S} (hu : v ≫ u = 𝟙 (R ⊗ S)) (μ : M ⊗ N ⟶ L)
    (p q n : ℕ) (h : p + q = n) (a : (TopPair.ofSubset A).singularCohomology R k M p)
    (b : (TopPair.ofSubset B).singularCohomology S k N q) :
    homologyMap (K := (TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)).singularChainComplex
          (R ⊗ S)) (L := (TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)).singularChainComplex T)
        (((SSetPair.chainComplexFunctor C).map v).app
          (TopPair.toSSetPair.obj (TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)))) n ≫
      TopPair.singularHomologyMap (TopPair.ofSubsetMap (B := fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)
        (B' := Z) (𝟙 (X ⊗ Y)) fun _ hx ↦ hZ' hx) T n ≫
      (TopPair.ofSubset Z).singularKronecker (R := T) (M := L) k n
        (singularRelativeCupPullback k u μ (fst X Y) (snd X Y) hA hB hZ p q n h a b) =
      (TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)).singularKronecker (R := R ⊗ S) (M := L)
        k n (TauCeti.singularRelativeCross k X Y hA hB μ p q n h a b) := by
  let P := TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)
  let i₁ := TopPair.ofSubsetMap (B := fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B) (B' := Z) (𝟙 _) fun _ h ↦ hZ' h
  let i₂ := TopPair.ofSubsetMap (B := Z) (B' := fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B) (𝟙 _) fun _ h ↦ hZ h
  have hpair : i₁ ≫ i₂ = 𝟙 P := (TopPair.ofSubsetMap_comp_ofSubsetMap_of_comp_eq _ _ (fun _ hx ↦ hx)
    (Category.comp_id _)).trans (TopPair.ofSubsetMap_id fun _ hx ↦ hx)
  have hidZ : TopPair.singularHomologyMap i₁ T n ≫ TopPair.singularHomologyMap i₂ T n = 𝟙 _ := by
    rw [← TopPair.singularHomologyMap_comp, hpair, TopPair.singularHomologyMap_id]
  let ev := ((SSetPair.chainComplexFunctor C).map v).app (TopPair.toSSetPair.obj P)
  let eu := ((SSetPair.chainComplexFunctor C).map u).app (TopPair.toSSetPair.obj P)
  have hvu : homologyMap ev n ≫ homologyMap eu n = 𝟙 _ := by
    rw [← homologyMap_comp]
    simp [ev, eu, ← NatTrans.comp_app, ← (SSetPair.chainComplexFunctor C).map_comp, hu]
  rw [singularRelativeCupPullback_apply, TopPair.singularKronecker_naturality,
    ← Category.assoc (TopPair.singularHomologyMap i₁ T n), hidZ, Category.id_comp,
    singularRelativeCup_eq_homologyMap_singularRelativeCup,
    ← TauCeti.singularRelativeCross_apply k X Y hA hB, TopPair.singularKronecker_def,
    TopPair.singularKronecker_def]
  exact (whisker_eq _ (TauCeti.ChainComplex.kronecker_naturality eu n _)).trans
    ((Category.assoc _ _ _).symm.trans ((eq_whisker hvu _).trans (Category.id_comp _)))

variable [∀ (Z : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft Z)]
  [∀ (Z : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight Z)]
  (X Y : TopCat.{w}) {A : Set X} {B : Set Y} (hA : IsOpen A) (hB : IsOpen B)

private lemma homologyMap_relativeShuffle_comp_singularKronecker_singularRelativeCross
    (μ : M ⊗ N ⟶ L) (p q n : ℕ) (h : p + q = n)
    (a : (TopPair.ofSubset A).singularCohomology R k M p)
    (b : (TopPair.ofSubset B).singularCohomology S k N q) :
    homologyMap (relativeShuffle X Y A B R S) n ≫
        SSetPair.homologyMap (smallSingularSubcomplexPairToUnion (fst X Y ⁻¹' A) (snd X Y ⁻¹' B))
          (R ⊗ S) n ≫
        TauCeti.ChainComplex.kronecker k
          ((TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)).singularChainComplex (R ⊗ S)) L n
          (TauCeti.singularRelativeCross k X Y hA hB μ p q n h a b) =
      TauCeti.ChainComplex.kronecker k
        (HomologicalComplex.tensorObj ((TopPair.ofSubset A).singularChainComplex R)
          ((TopPair.ofSubset B).singularChainComplex S)) L n
        (TauCeti.ChainComplex.cup k
          (𝟙 (HomologicalComplex.tensorObj ((TopPair.ofSubset A).singularChainComplex R)
            ((TopPair.ofSubset B).singularChainComplex S))) μ p q n h a b) := by
  rw [← TauCeti.ChainComplex.kronecker_naturality,
    TauCeti.homologyMap_cochainComplexMap_singularRelativeCross,
    ← TauCeti.ChainComplex.kronecker_naturality, ← TauCeti.ChainComplex.cup_precomp]
  exact congrArg _ (TauCeti.ChainComplex.cup_eq_of_homotopy _ μ
    (relativeShuffleAlexanderWhitneyHomotopy X Y A B R S) p q n h a b)

/-- **The Kronecker pairing of relative cross products**, `⟨a × b, x × y⟩ = μ (⟨a, x⟩ ⊗ ⟨b, y⟩)`
for open `A ⊆ X` and `B ⊆ Y`. -/
theorem singularRelativeHomologyCross_comp_singularKronecker_singularRelativeCross
    (μ : M ⊗ N ⟶ L) (p q n : ℕ) (h : p + q = n)
    [PreservesColimitsOfShape WalkingParallelPair (tensorLeft
      (((TopPair.ofSubset A).singularChainComplex R).homology p))]
    [PreservesColimitsOfShape WalkingParallelPair (tensorRight
      (((TopPair.ofSubset B).singularChainComplex S).cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair (tensorRight
      (((TopPair.ofSubset B).singularChainComplex S).X ((ComplexShape.down ℕ).prev q)))]
    (a : (TopPair.ofSubset A).singularCohomology R k M p)
    (b : (TopPair.ofSubset B).singularCohomology S k N q) :
    singularRelativeHomologyCross X Y R S A B p q n h ≫
        (TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)).singularKronecker (R := R ⊗ S) (M := L)
          k n (TauCeti.singularRelativeCross k X Y hA hB μ p q n h a b) =
      ((TopPair.ofSubset A).singularKronecker (R := R) (M := M) k p a ⊗ₘ
        (TopPair.ofSubset B).singularKronecker (R := S) (M := N) k q b) ≫ μ := by
  rw [singularRelativeHomologyCross_def, ← relativeShuffle_comp_smallSingularSubcomplexPairToUnion,
    homologyMap_comp]
  simp only [TopPair.singularKronecker_def]
  exact (Category.assoc _ _ _).trans <|
    (whisker_eq _ ((Category.assoc _ _ _).trans
      (homologyMap_relativeShuffle_comp_singularKronecker_singularRelativeCross
        X Y hA hB μ p q n h a b))).trans
    (ChainComplex.homologyCross_comp_kronecker_cup _ _ μ p q n h a b)

/-- **Off-diagonal vanishing for the Kronecker pairing of relative cross products** (`p ≠ p'`). -/
theorem singularRelativeHomologyCross_comp_singularKronecker_singularRelativeCross_of_ne
    (μ : M ⊗ N ⟶ L) {p q p' q' n : ℕ} (h : p + q = n) (h' : p' + q' = n) (hp : p ≠ p')
    [PreservesColimitsOfShape WalkingParallelPair (tensorLeft
      (((TopPair.ofSubset A).singularChainComplex R).homology p))]
    [PreservesColimitsOfShape WalkingParallelPair (tensorRight
      (((TopPair.ofSubset B).singularChainComplex S).cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair (tensorRight
      (((TopPair.ofSubset B).singularChainComplex S).X ((ComplexShape.down ℕ).prev q)))]
    (a : (TopPair.ofSubset A).singularCohomology R k M p')
    (b : (TopPair.ofSubset B).singularCohomology S k N q') :
    singularRelativeHomologyCross X Y R S A B p q n h ≫
        (TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)).singularKronecker (R := R ⊗ S) (M := L)
          k n (TauCeti.singularRelativeCross k X Y hA hB μ p' q' n h' a b) = 0 := by
  rw [singularRelativeHomologyCross_def, ← relativeShuffle_comp_smallSingularSubcomplexPairToUnion,
    homologyMap_comp, TopPair.singularKronecker_def]
  exact (Category.assoc _ _ _).trans <|
    (whisker_eq _ ((Category.assoc _ _ _).trans
      (homologyMap_relativeShuffle_comp_singularKronecker_singularRelativeCross
        X Y hA hB μ p' q' n h' a b))).trans
    (ChainComplex.homologyCross_comp_kronecker_cup_of_ne _ _ μ p q h h' hp a b)

/-- **The Kronecker pairing of `TopCat.singularRelativeCupPullback` along `fst` and `snd`** when
`v ≫ u = 𝟙 (R ⊗ S)` and `Z` agrees with `fst⁻¹(A) ∪ snd⁻¹(B)`. -/
theorem singularRelativeHomologyCross_comp_singularKronecker_singularRelativeCupPullback
    {Z : Set ↥(X ⊗ Y)} (hZ : Z ⊆ fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)
    (hZ' : fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B ⊆ Z)
    {v : R ⊗ S ⟶ T} {u : T ⟶ R ⊗ S} (hu : v ≫ u = 𝟙 (R ⊗ S)) (μ : M ⊗ N ⟶ L)
    (p q n : ℕ) (h : p + q = n)
    [PreservesColimitsOfShape WalkingParallelPair (tensorLeft
      (((TopPair.ofSubset A).singularChainComplex R).homology p))]
    [PreservesColimitsOfShape WalkingParallelPair (tensorRight
      (((TopPair.ofSubset B).singularChainComplex S).cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair (tensorRight
      (((TopPair.ofSubset B).singularChainComplex S).X ((ComplexShape.down ℕ).prev q)))]
    (a : (TopPair.ofSubset A).singularCohomology R k M p)
    (b : (TopPair.ofSubset B).singularCohomology S k N q) :
    singularRelativeHomologyCross X Y R S A B p q n h ≫
        homologyMap (K := (TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)).singularChainComplex
            (R ⊗ S))
          (L := (TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)).singularChainComplex T)
          (((SSetPair.chainComplexFunctor C).map v).app
            (TopPair.toSSetPair.obj (TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)))) n ≫
        TopPair.singularHomologyMap (TopPair.ofSubsetMap (B := fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)
          (B' := Z) (𝟙 (X ⊗ Y)) fun _ hx ↦ hZ' hx) T n ≫
        (TopPair.ofSubset Z).singularKronecker (R := T) (M := L) k n
          (singularRelativeCupPullback k u μ (fst X Y) (snd X Y) hA hB hZ p q n h a b) =
      ((TopPair.ofSubset A).singularKronecker (R := R) (M := M) k p a ⊗ₘ
        (TopPair.ofSubset B).singularKronecker (R := S) (M := N) k q b) ≫ μ :=
  (whisker_eq _ (homologyMap_comp_singularKronecker_singularRelativeCupPullback
    X Y hA hB hZ hZ' hu μ p q n h a b)).trans
    (singularRelativeHomologyCross_comp_singularKronecker_singularRelativeCross
      X Y hA hB μ p q n h a b)

/-- **Off-diagonal vanishing for the Kronecker pairing of `TopCat.singularRelativeCupPullback` along
`fst` and `snd`** (`p ≠ p'`, `v ≫ u = 𝟙 (R ⊗ S)`, `Z = fst⁻¹(A) ∪ snd⁻¹(B)`). -/
theorem singularRelativeHomologyCross_comp_singularKronecker_singularRelativeCupPullback_of_ne
    {Z : Set ↥(X ⊗ Y)} (hZ : Z ⊆ fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)
    (hZ' : fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B ⊆ Z)
    {v : R ⊗ S ⟶ T} {u : T ⟶ R ⊗ S} (hu : v ≫ u = 𝟙 (R ⊗ S)) (μ : M ⊗ N ⟶ L)
    {p q p' q' n : ℕ} (h : p + q = n) (h' : p' + q' = n) (hp : p ≠ p')
    [PreservesColimitsOfShape WalkingParallelPair (tensorLeft
      (((TopPair.ofSubset A).singularChainComplex R).homology p))]
    [PreservesColimitsOfShape WalkingParallelPair (tensorRight
      (((TopPair.ofSubset B).singularChainComplex S).cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair (tensorRight
      (((TopPair.ofSubset B).singularChainComplex S).X ((ComplexShape.down ℕ).prev q)))]
    (a : (TopPair.ofSubset A).singularCohomology R k M p')
    (b : (TopPair.ofSubset B).singularCohomology S k N q') :
    singularRelativeHomologyCross X Y R S A B p q n h ≫
        homologyMap (K := (TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)).singularChainComplex
            (R ⊗ S))
          (L := (TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)).singularChainComplex T)
          (((SSetPair.chainComplexFunctor C).map v).app
            (TopPair.toSSetPair.obj (TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)))) n ≫
        TopPair.singularHomologyMap (TopPair.ofSubsetMap (B := fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)
          (B' := Z) (𝟙 (X ⊗ Y)) fun _ hx ↦ hZ' hx) T n ≫
        (TopPair.ofSubset Z).singularKronecker (R := T) (M := L) k n
          (singularRelativeCupPullback k u μ (fst X Y) (snd X Y) hA hB hZ p' q' n h' a b) = 0 :=
  (whisker_eq _ (homologyMap_comp_singularKronecker_singularRelativeCupPullback
    X Y hA hB hZ hZ' hu μ p' q' n h' a b)).trans
    (singularRelativeHomologyCross_comp_singularKronecker_singularRelativeCross_of_ne
      X Y hA hB μ h h' hp a b)

end TopCat
