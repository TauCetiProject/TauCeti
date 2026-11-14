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
`Hⁿ(X × Y, A × Y ∪ X × B; R ⊗ S, L)` (`p + q = n`) via the small-chain isomorphism from the
quotient of `C(X × Y)` by `C(A × Y) + C(X × B)`
(`TauCeti.AlgebraicTopology.Cohomology.Cup.Relative`), while the relative homology cross
product `TopCat.singularRelativeHomologyCross` maps `Hₚ(X, A; R) ⊗ H_q(Y, B; S)` into
`Hₙ(X × Y, A × Y ∪ X × B; R ⊗ S)` via the relative shuffle map into that same small-chain quotient
followed by its map to `C(X × Y, A × Y ∪ X × B)`
(`TauCeti.AlgebraicTopology.Singular.RelativeCrossProduct`).

Under the small-chain isomorphism, `TauCeti.singularRelativeCross` corresponds to the cohomological
cup product along `TopCat.relativeAlexanderWhitney`
(`TopCat.homologyMap_cochainComplexMap_singularRelativeCross`), and pulling back further along
`TopCat.relativeShuffle` turns it, via the relative Eilenberg–Zilber chain homotopy
`TopCat.relativeShuffleAlexanderWhitneyHomotopy`, into the algebraic cup product along the identity
diagonal of `C(X, A; R) ⊗ C(Y, B; S)`. Consequently, the Kronecker pairing of the relative
cohomology cross product with the relative homology cross product reduces to the purely algebraic
identity `ChainComplex.homologyCross_comp_kronecker_cup`:

`⟨a × b, x × y⟩ = μ (⟨a, x⟩ ⊗ ⟨b, y⟩)`

with no sign (`TopCat.singularRelativeHomologyCross_comp_singularKronecker_singularRelativeCross`),
and `⟨a × b, x × y⟩ = 0` when the degrees of `a` and `x` differ
(`TopCat.singularRelativeHomologyCross_comp_singularKronecker_singularRelativeCross_of_ne`).

Changing chain coefficients along a morphism `u : T ⟶ R ⊗ S` expresses `TopCat.singularRelativeCup`
along `u` in terms of `TopCat.singularRelativeCup` along `𝟙 (R ⊗ S)`
(`TopCat.singularRelativeCup_eq_homologyMap_singularRelativeCup`). When `v : R ⊗ S ⟶ T` satisfies
`v ≫ u = 𝟙 (R ⊗ S)` (for instance `v = (λ_ _).hom` and `u = (λ_ _).inv` on the monoidal unit of
`ModuleCat K`) and `Z = fst⁻¹(A) ∪ snd⁻¹(B)`, pushing the relative homology cross product forward
along `v` pairs multiplicatively with `TopCat.singularRelativeCupPullback` along `fst` and `snd`
(`TopCat.singularRelativeHomologyCross_comp_singularKronecker_singularRelativeCupPullback`). Over
any commutative ring, this detects unit generators of local cohomology groups of product pairs
`(F₁ × F₂, (F₁ × F₂) \ {0})` without any field or Künneth flatness hypothesis.

## Main definitions and results

* `TopCat.singularRelativeCup_eq_homologyMap_singularRelativeCup`: the relative cup product along
  `u : T ⟶ R ⊗ S` is the relative cup product along `𝟙 (R ⊗ S)` followed by the change of chain
  coefficients along `u`.
* `TopCat.homologyMap_cochainComplexMap_singularRelativeCross`: under the small-chain isomorphism,
  `TauCeti.singularRelativeCross` is the cup product along `TopCat.relativeAlexanderWhitney`.
* `TopCat.singularRelativeHomologyCross_comp_singularKronecker_singularRelativeCross` and
  `TopCat.singularRelativeHomologyCross_comp_singularKronecker_singularRelativeCross_of_ne`: the
  Kronecker pairing of relative cohomology and homology cross products in matching and differing
  bidegrees.
* `TopCat.singularRelativeHomologyCross_comp_singularKronecker_singularRelativeCupPullback` and
  `TopCat.singularRelativeHomologyCross_comp_singularKronecker_singularRelativeCupPullback_of_ne`:
  the corresponding Kronecker pairing formulas for `TopCat.singularRelativeCupPullback` along the
  two projections when `v ≫ u = 𝟙 (R ⊗ S)` and `Z` agrees with `fst⁻¹(A) ∪ snd⁻¹(B)`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.2 and Section 3.B.
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

section CoefficientChange

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
  [MonoidalCategory C] [MonoidalPreadditive C]
  {R S T M N L : C}

/-- Changing chain coefficients along `u : T ⟶ R ⊗ S` on the small-chain quotient complex relates
`TopCat.relativeAlexanderWhitneyDiagonal U V u` to the diagonal along `𝟙 (R ⊗ S)`. -/
private lemma relativeAlexanderWhitneyDiagonal_eq_comp {W : TopCat.{w}} (U V : Set W)
    (u : T ⟶ R ⊗ S) :
    relativeAlexanderWhitneyDiagonal U V u =
      ((SSetPair.chainComplexFunctor C).map u).app (W.smallSingularSubcomplex ![U, V]).pair ≫
        relativeAlexanderWhitneyDiagonal U V (𝟙 (R ⊗ S)) := by
  apply (cancel_epi ((W.smallSingularSubcomplex ![U, V]).pair.chainComplexπ T)).1
  have hπ : (W.smallSingularSubcomplex ![U, V]).pair.chainComplexπ T ≫
      ((SSetPair.chainComplexFunctor C).map u).app (W.smallSingularSubcomplex ![U, V]).pair =
      ((SSet.chainComplexFunctor C).map u).app (toSSet.obj W) ≫
        (W.smallSingularSubcomplex ![U, V]).pair.chainComplexπ (R ⊗ S) :=
    NatTrans.congr_app ((SSetPair.chainComplexFunctorπ C).naturality u).symm
      (W.smallSingularSubcomplex ![U, V]).pair
  have hD : W.alexanderWhitneyDiagonal u =
      ((SSet.chainComplexFunctor C).map u).app (toSSet.obj W) ≫
        W.alexanderWhitneyDiagonal (𝟙 (R ⊗ S)) := by
    simp [TauCeti.alexanderWhitneyDiagonal_def]
  exact (chainComplexπ_relativeAlexanderWhitneyDiagonal U V u).trans <|
    (eq_whisker hD _).trans <|
    (Category.assoc _ _ _).trans <|
    (whisker_eq _ (chainComplexπ_relativeAlexanderWhitneyDiagonal U V (𝟙 (R ⊗ S))).symm).trans <|
    (Category.assoc _ _ _).symm.trans <|
    (eq_whisker hπ.symm _).trans (Category.assoc _ _ _)

/-- **The relative cup product changes chain coefficients along its coefficient morphism**: for
`u : T ⟶ R ⊗ S`, the relative cup product along `u` is the relative cup product along `𝟙 (R ⊗ S)`
followed by the cohomology map precomposing relative cochains with the chain map induced by `u`. -/
lemma singularRelativeCup_eq_homologyMap_singularRelativeCup {W : TopCat.{w}} (k : Type*)
    [CommRing k] [Linear k C] [MonoidalLinear k C] (u : T ⟶ R ⊗ S) (μ : M ⊗ N ⟶ L) (U V : Set W)
    (hU : IsOpen ((↑) ⁻¹' U : Set ↥(U ∪ V))) (hV : IsOpen ((↑) ⁻¹' V : Set ↥(U ∪ V)))
    (p q n : ℕ) (h : p + q = n)
    (a : (TopPair.ofSubset U).singularCohomology R k M p)
    (b : (TopPair.ofSubset V).singularCohomology S k N q) :
    singularRelativeCup k u μ U V hU hV p q n h a b =
      homologyMap
        (K := (TopPair.ofSubset (U ∪ V)).singularCochainComplex (R ⊗ S) k L)
        (L := (TopPair.ofSubset (U ∪ V)).singularCochainComplex T k L)
        ((TauCeti.ChainComplex.linearYonedaFunctor k L).map
          (((SSetPair.chainComplexFunctor C).map u).app
            (TopPair.toSSetPair.obj (TopPair.ofSubset (U ∪ V)))).op) n
        (singularRelativeCup k (𝟙 (R ⊗ S)) μ U V hU hV p q n h a b) := by
  have := isIso_homologyMap_cochainComplexMap_smallSingularSubcomplexPairToUnion T k L U V hU hV n
  apply (ModuleCat.mono_iff_injective (homologyMap (SSetPair.cochainComplexMap (R := T) (k := k)
    (M := L) (smallSingularSubcomplexPairToUnion U V)) n)).1 inferInstance
  let e₁ : (W.smallSingularSubcomplex ![U, V]).pair.chainComplex T ⟶
      (W.smallSingularSubcomplex ![U, V]).pair.chainComplex (R ⊗ S) :=
    ((SSetPair.chainComplexFunctor C).map u).app (W.smallSingularSubcomplex ![U, V]).pair
  let e₂ : (TopPair.ofSubset (U ∪ V)).singularChainComplex T ⟶
      (TopPair.ofSubset (U ∪ V)).singularChainComplex (R ⊗ S) :=
    ((SSetPair.chainComplexFunctor C).map u).app
      (TopPair.toSSetPair.obj (TopPair.ofSubset (U ∪ V)))
  let sT : (W.smallSingularSubcomplex ![U, V]).pair.chainComplex T ⟶
      (TopPair.ofSubset (U ∪ V)).singularChainComplex T :=
    SSetPair.chainComplexMap (smallSingularSubcomplexPairToUnion U V) T
  let sRS : (W.smallSingularSubcomplex ![U, V]).pair.chainComplex (R ⊗ S) ⟶
      (TopPair.ofSubset (U ∪ V)).singularChainComplex (R ⊗ S) :=
    SSetPair.chainComplexMap (smallSingularSubcomplexPairToUnion U V) (R ⊗ S)
  have hsq : sT ≫ e₂ = e₁ ≫ sRS :=
    ((SSetPair.chainComplexFunctor C).map u).naturality
      (smallSingularSubcomplexPairToUnion U V)
  let c := singularRelativeCup k (𝟙 (R ⊗ S)) μ U V hU hV p q n h a b
  have hcomp : homologyMap
        (K := ((W.smallSingularSubcomplex ![U, V]).pair.chainComplex (R ⊗ S)).linearYonedaObj k L)
        (L := ((W.smallSingularSubcomplex ![U, V]).pair.chainComplex T).linearYonedaObj k L)
        ((TauCeti.ChainComplex.linearYonedaFunctor k L).map e₁.op) n
        (homologyMap (SSetPair.cochainComplexMap (R := R ⊗ S) (k := k) (M := L)
          (smallSingularSubcomplexPairToUnion U V)) n c) =
      homologyMap (SSetPair.cochainComplexMap (R := T) (k := k) (M := L)
          (smallSingularSubcomplexPairToUnion U V)) n
        (homologyMap
          (K := (TopPair.ofSubset (U ∪ V)).singularCochainComplex (R ⊗ S) k L)
          (L := (TopPair.ofSubset (U ∪ V)).singularCochainComplex T k L)
          ((TauCeti.ChainComplex.linearYonedaFunctor k L).map e₂.op) n c) := by
    refine (TauCeti.ChainComplex.homologyMap_linearYonedaFunctor_map_comp_apply
      e₁ sRS n c).symm.trans ?_
    rw [← hsq]
    exact TauCeti.ChainComplex.homologyMap_linearYonedaFunctor_map_comp_apply sT e₂ n c
  rw [homologyMap_cochainComplexMap_singularRelativeCup]
  refine Eq.trans ?_ hcomp
  rw [homologyMap_cochainComplexMap_singularRelativeCup,
    relativeAlexanderWhitneyDiagonal_eq_comp U V u]
  exact TauCeti.ChainComplex.cup_precomp
    (relativeAlexanderWhitneyDiagonal U V (𝟙 (R ⊗ S))) μ e₁ p q n h a b

/-- On `X × Y`, the relative Alexander–Whitney diagonal for `fst⁻¹(A)` and `snd⁻¹(B)` followed by
the projections onto `C(X, A; R)` and `C(Y, B; S)` is `TopCat.relativeAlexanderWhitney`. -/
private lemma relativeAlexanderWhitneyDiagonal_id_comp_tensorHom_fst_snd
    (X Y : TopCat.{w}) (A : Set X) (B : Set Y) :
    relativeAlexanderWhitneyDiagonal (fst X Y ⁻¹' A) (snd X Y ⁻¹' B) (𝟙 (R ⊗ S)) ≫
        HomologicalComplex.tensorHom
          (TopPair.singularChainComplexMap
            (TopPair.ofSubsetMap (fst X Y) (Set.mapsTo_preimage _ _)) R)
          (TopPair.singularChainComplexMap
            (TopPair.ofSubsetMap (snd X Y) (Set.mapsTo_preimage _ _)) S) =
      relativeAlexanderWhitney X Y A B R S := by
  apply (cancel_epi (((X ⊗ Y).smallSingularSubcomplex
    ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.chainComplexπ (R ⊗ S))).1
  have hdiag : lift (𝟙 (X ⊗ Y)) (𝟙 (X ⊗ Y)) ≫ (fst X Y ⊗ₘ snd X Y) = 𝟙 (X ⊗ Y) := by
    ext <;> simp
  have hAW : alexanderWhitney X Y R S =
      (X ⊗ Y).alexanderWhitneyDiagonal (𝟙 (R ⊗ S)) ≫
        HomologicalComplex.tensorHom
          (SSet.chainComplexMap (toSSet.map (fst X Y)) R)
          (SSet.chainComplexMap (toSSet.map (snd X Y)) S) := by
    rw [TauCeti.alexanderWhitneyDiagonal_def, (SSet.chainComplexFunctor C).map_id]
    simp only [NatTrans.id_app, Category.id_comp, Category.assoc]
    have hD : SSet.chainComplexMap (toSSet.map (fst X Y ⊗ₘ snd X Y)) (R ⊗ S) ≫
        alexanderWhitney X Y R S =
      alexanderWhitney (X ⊗ Y) (X ⊗ Y) R S ≫
        HomologicalComplex.tensorHom
          (SSet.chainComplexMap (toSSet.map (fst X Y)) R)
          (SSet.chainComplexMap (toSSet.map (snd X Y)) S) :=
      alexanderWhitney_naturality (fst X Y) (snd X Y) R S
    rw [← hD, ← Category.assoc, ← ((SSet.chainComplexFunctor C).obj (R ⊗ S)).map_comp,
      ← toSSet.map_comp, hdiag, toSSet.map_id,
      ((SSet.chainComplexFunctor C).obj (R ⊗ S)).map_id, Category.id_comp]
  have hA := TopPair.singularChainComplexπ_pair_naturality
    (TopPair.ofSubsetMap (fst X Y) (Set.mapsTo_preimage _ A)) R
  have hB := TopPair.singularChainComplexπ_pair_naturality
    (TopPair.ofSubsetMap (snd X Y) (Set.mapsTo_preimage _ B)) S
  rw [TopPair.ofSubsetMap_fst] at hA hB
  have htensor : HomologicalComplex.tensorHom
        ((TopPair.ofSubset (fst X Y ⁻¹' A)).singularChainComplexπ R)
        ((TopPair.ofSubset (snd X Y ⁻¹' B)).singularChainComplexπ S) ≫
      HomologicalComplex.tensorHom
        (TopPair.singularChainComplexMap
          (TopPair.ofSubsetMap (fst X Y) (Set.mapsTo_preimage _ _)) R)
        (TopPair.singularChainComplexMap
          (TopPair.ofSubsetMap (snd X Y) (Set.mapsTo_preimage _ _)) S) =
      HomologicalComplex.tensorHom
          (SSet.chainComplexMap (toSSet.map (fst X Y)) R)
          (SSet.chainComplexMap (toSSet.map (snd X Y)) S) ≫
        HomologicalComplex.tensorHom
          ((TopPair.ofSubset A).singularChainComplexπ R)
          ((TopPair.ofSubset B).singularChainComplexπ S) :=
    (mapBifunctorMap_comp (curriedTensor C) (ComplexShape.down ℕ) _ _ _ _).symm.trans <|
      (congrArg₂ (HomologicalComplex.tensorHom · ·) hA.symm hB.symm).trans
        (mapBifunctorMap_comp (curriedTensor C) (ComplexShape.down ℕ) _ _ _ _)
  exact (chainComplexπ_relativeAlexanderWhitneyDiagonal_assoc
      (fst X Y ⁻¹' A) (snd X Y ⁻¹' B) (𝟙 (R ⊗ S)) _).trans <|
    (Category.assoc _ _ _).trans <|
    (whisker_eq _ htensor).trans <|
    (Category.assoc _ _ _).symm.trans <|
    (eq_whisker hAW.symm _).trans (chainComplexπ_relativeAlexanderWhitney X Y A B R S).symm

/-- **Characterization of the relative cohomology cross product on small chains**: under the
small-chain isomorphism for `fst⁻¹(A)` and `snd⁻¹(B)`, `TauCeti.singularRelativeCross` is the
cohomological cup product along `TopCat.relativeAlexanderWhitney`. -/
lemma homologyMap_cochainComplexMap_singularRelativeCross
    (k : Type*) [CommRing k] [Linear k C] [MonoidalLinear k C]
    (X Y : TopCat.{w}) {A : Set X} {B : Set Y} (hA : IsOpen A) (hB : IsOpen B)
    (μ : M ⊗ N ⟶ L) (p q n : ℕ) (h : p + q = n)
    (a : (TopPair.ofSubset A).singularCohomology R k M p)
    (b : (TopPair.ofSubset B).singularCohomology S k N q) :
    homologyMap (SSetPair.cochainComplexMap (R := R ⊗ S) (k := k) (M := L)
        (smallSingularSubcomplexPairToUnion (fst X Y ⁻¹' A) (snd X Y ⁻¹' B))) n
        (TauCeti.singularRelativeCross k X Y hA hB μ p q n h a b) =
      TauCeti.ChainComplex.cup k (relativeAlexanderWhitney X Y A B R S) μ p q n h a b := by
  rw [TauCeti.singularRelativeCross_apply, homologyMap_cochainComplexMap_singularRelativeCup]
  have hcup := TauCeti.ChainComplex.cup_naturality (k := k)
    (relativeAlexanderWhitney X Y A B R S) μ
    (relativeAlexanderWhitneyDiagonal (fst X Y ⁻¹' A) (snd X Y ⁻¹' B) (𝟙 (R ⊗ S)))
    (𝟙 _)
    (TopPair.singularChainComplexMap
      (TopPair.ofSubsetMap (fst X Y) (Set.mapsTo_preimage _ _)) R)
    (TopPair.singularChainComplexMap
      (TopPair.ofSubsetMap (snd X Y) (Set.mapsTo_preimage _ _)) S)
    ((Category.id_comp _).trans
      (relativeAlexanderWhitneyDiagonal_id_comp_tensorHom_fst_snd X Y A B).symm)
    p q n h a b
  have hid : (TauCeti.ChainComplex.linearYonedaFunctor k L).map
      (𝟙 (((X ⊗ Y).smallSingularSubcomplex
        ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.chainComplex (R ⊗ S))).op =
      𝟙 ((((X ⊗ Y).smallSingularSubcomplex
        ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.chainComplex (R ⊗ S)).linearYonedaObj k L) := by
    rw [op_id]
    exact (TauCeti.ChainComplex.linearYonedaFunctor k L).map_id _
  rw [hid, homologyMap_id, ModuleCat.id_apply] at hcup
  exact hcup

end CoefficientChange

section KroneckerPairing

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
  [MonoidalCategory C] [MonoidalPreadditive C]
  {k : Type*} [CommRing k] [Linear k C] [MonoidalLinear k C]
  {R S T M N L : C}

/-- Reduction of the Kronecker evaluation of `TopCat.singularRelativeCupPullback` along `fst` and
`snd` to that of `TauCeti.singularRelativeCross`, when `v ≫ u = 𝟙 (R ⊗ S)` and `Z` agrees with
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
    singularRelativeCup_eq_homologyMap_singularRelativeCup,
    ← TauCeti.singularRelativeCross_apply k X Y hA hB, TopPair.singularKronecker_def,
    TopPair.singularKronecker_def]
  exact (whisker_eq _ (TauCeti.ChainComplex.kronecker_naturality eu n _)).trans
    ((Category.assoc _ _ _).symm.trans ((eq_whisker hvu _).trans (Category.id_comp _)))

variable [∀ (Z : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft Z)]
  [∀ (Z : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight Z)]

/-- Restricted along `relativeShuffle` and `smallSingularSubcomplexPairToUnion`, the relative
Kronecker image of `TauCeti.singularRelativeCross` is the algebraic Kronecker image of the cup
product along the identity diagonal of `C(X, A; R) ⊗ C(Y, B; S)`. -/
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
    rw [← homologyMap_cochainComplexMap_singularRelativeCross k X Y hA hB μ p q n h a b]
    exact (TauCeti.ChainComplex.kronecker_naturality (k := k)
      (SSetPair.chainComplexMap
        (smallSingularSubcomplexPairToUnion (fst X Y ⁻¹' A) (snd X Y ⁻¹' B)) (R ⊗ S)) n _).symm
  have hcup : homologyMap
        (K := (((X ⊗ Y).smallSingularSubcomplex
          ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.chainComplex (R ⊗ S)).linearYonedaObj k L)
        (L := _root_.ChainComplex.linearYonedaObj
          (HomologicalComplex.tensorObj ((TopPair.ofSubset A).singularChainComplex R)
            ((TopPair.ofSubset B).singularChainComplex S)) k L)
        ((TauCeti.ChainComplex.linearYonedaFunctor k L).map
          (relativeShuffle X Y A B R S).op) n
        (TauCeti.ChainComplex.cup k (relativeAlexanderWhitney X Y A B R S) μ p q n h a b) =
      TauCeti.ChainComplex.cup k
        (𝟙 (HomologicalComplex.tensorObj ((TopPair.ofSubset A).singularChainComplex R)
          ((TopPair.ofSubset B).singularChainComplex S))) μ p q n h a b :=
    (TauCeti.ChainComplex.cup_precomp (relativeAlexanderWhitney X Y A B R S) μ
      (relativeShuffle X Y A B R S) p q n h a b).symm.trans
      (TauCeti.ChainComplex.cup_eq_of_homotopy _ μ
        (relativeShuffleAlexanderWhitneyHomotopy X Y A B R S) p q n h a b)
  refine (whisker_eq _ hk₁).trans ?_
  rw [← hcup]
  exact (TauCeti.ChainComplex.kronecker_naturality (k := k) (relativeShuffle X Y A B R S) n _).symm

/-- **The Kronecker pairing of relative cross products**, `⟨a × b, x × y⟩ = μ (⟨a, x⟩ ⊗ ⟨b, y⟩)`:
for open `A ⊆ X` and `B ⊆ Y`, evaluating the relative cohomology cross product
`a × b ∈ Hⁿ(X × Y, A × Y ∪ X × B; R ⊗ S, L)` on the image of the relative homology cross product
`Hₚ(X, A; R) ⊗ H_q(Y, B; S) ⟶ Hₙ(X × Y, A × Y ∪ X × B; R ⊗ S)` is the tensor product of the
relative Kronecker evaluations of `a` and `b` followed by `μ`. -/
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

/-- **The Kronecker pairing of relative cross products of different degrees vanishes**: for
`p ≠ p'`, the relative cohomology cross product of classes of degrees `p'` and `q'` evaluates to
zero on the image of the relative homology cross product in bidegree `(p, q)`. -/
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

/-- **The Kronecker pairing of `TopCat.singularRelativeCupPullback` along the two projections**:
when `v ≫ u = 𝟙 (R ⊗ S)` and `Z` agrees with `fst⁻¹(A) ∪ snd⁻¹(B)`, pushing the relative homology
cross product forward along `v` and into `(X × Y, Z)` pairs with the pulled-back relative cup
product as the tensor product of the relative Kronecker evaluations followed by `μ`. -/
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

/-- **Off-diagonal vanishing for `TopCat.singularRelativeCupPullback` along the two projections**:
when `p ≠ p'`, `v ≫ u = 𝟙 (R ⊗ S)`, and `Z` agrees with `fst⁻¹(A) ∪ snd⁻¹(B)`, the pulled-back
relative cup product in bidegree `(p', q')` evaluates to zero on the pushed-forward relative
homology cross product in bidegree `(p, q)`. -/
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
