/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.Homology.Connecting
public import TauCeti.AlgebraicTopology.Singular.AlexanderWhitney.RelativeCup
public import TauCeti.AlgebraicTopology.Singular.CrossProduct

/-!
# The relative cross product in singular homology

For topological pairs `(X, A)` and `(Y, B)` given by subsets `A ⊆ X` and `B ⊆ Y`, and coefficient
objects `R` and `S` in an abelian monoidal category, the **relative homology cross product** is the
morphism

`Hₚ(X, A; R) ⊗ H_q(Y, B; S) ⟶ Hₙ(X × Y, A × Y ∪ X × B; R ⊗ S)`, for `p + q = n`,

where `A × Y` and `X × B` are the preimages `fst⁻¹(A)` and `snd⁻¹(B)`.

At the chain level, the singular shuffle map `C(X; R) ⊗ C(Y; S) ⟶ C(X × Y; R ⊗ S)` carries
`C(A; R) ⊗ C(Y; S)` into the singular chains of `A × Y` and `C(X; R) ⊗ C(B; S)` into the singular
chains of `X × B`. Since the short exact sequences of singular chains of `(X, A)` and `(Y, B)`
split in each degree, tensoring preserves their cokernels
(`HomologicalComplex.shortExact_tensorRightShortComplex`,
`HomologicalComplex.shortExact_tensorLeftShortComplex`), so the shuffle map followed by the
quotient to the chains `C(X × Y; A × Y + X × B; R ⊗ S)` relative to simplices small for
`{A × Y, X × B}` descends to a chain map

`TopCat.relativeShuffle : C(X, A; R) ⊗ C(Y, B; S) ⟶ C(X × Y; A × Y + X × B; R ⊗ S)`.

In the opposite direction, the relative Alexander–Whitney diagonal
`TopCat.relativeAlexanderWhitneyDiagonal` followed by the projections onto `(X, A)` and `(Y, B)`
defines

`TopCat.relativeAlexanderWhitney : C(X × Y; A × Y + X × B; R ⊗ S) ⟶ C(X, A; R) ⊗ C(Y, B; S)`.

Because the simplicial Eilenberg–Zilber chain homotopy `SSet.shuffleAlexanderWhitneyHomotopy` is
natural in both simplicial sets, it carries the subcomplexes `C(A; R) ⊗ C(Y; S)` and
`C(X; R) ⊗ C(B; S)` into the kernel of the quotient map `π_A ⊗ π_B`, and two applications of
`Homotopy.descCokernel` produce the relative Eilenberg–Zilber chain homotopy

`TopCat.relativeShuffleAlexanderWhitneyHomotopy :
  Homotopy (relativeShuffle X Y A B R S ≫ relativeAlexanderWhitney X Y A B R S) (𝟙 _)`.

Composing the algebraic homology cross product `HomologicalComplex.homologyCross` with
`TopCat.relativeShuffle` and the inclusion `TopCat.smallSingularSubcomplexPairToUnion` of small
simplices into `A × Y ∪ X × B` defines `TopCat.singularRelativeHomologyCross` for arbitrary subsets
`A ⊆ X` and `B ⊆ Y`, without any openness hypothesis. It is natural in maps of pairs and in both
coefficient objects, and compatible with `TopCat.singularHomologyCross` under the quotient maps
from absolute to relative homology.

## Main definitions and results

* `TopCat.relativeShuffle`: the relative shuffle chain map
  `C(X, A; R) ⊗ C(Y, B; S) ⟶ C(X × Y; A × Y + X × B; R ⊗ S)`, characterized by
  `TopCat.singularChainComplexπ_tensorHom_relativeShuffle` and natural in maps of pairs
  (`TopCat.relativeShuffle_naturality`).
* `TopCat.relativeAlexanderWhitney`: the relative Alexander–Whitney chain map
  `C(X × Y; A × Y + X × B; R ⊗ S) ⟶ C(X, A; R) ⊗ C(Y, B; S)`, characterized by
  `TopCat.chainComplexπ_relativeAlexanderWhitney` and natural in maps of pairs
  (`TopCat.relativeAlexanderWhitney_naturality`).
* `TopCat.relativeShuffleAlexanderWhitneyHomotopy`: the chain homotopy from
  `relativeShuffle ≫ relativeAlexanderWhitney` to the identity of `C(X, A; R) ⊗ C(Y, B; S)`.
* `TopCat.singularRelativeHomologyCross`: the relative homology cross product
  `Hₚ(X, A; R) ⊗ H_q(Y, B; S) ⟶ Hₙ(X × Y, A × Y ∪ X × B; R ⊗ S)`, natural in maps of pairs
  (`TopCat.singularRelativeHomologyCross_naturality`) and compatible with
  `TopCat.singularHomologyCross`
  (`TopCat.singularHomologyπ_tensorHom_singularRelativeHomologyCross`).

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.B, the relative cross product in homology.
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

section ChainLevel

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]

/-- A continuous map `f : Z ⟶ W` taking values in a single member `U i` of a family of subsets
induces the zero map into the singular chains of `W` relative to the simplices small for `U`. -/
private lemma chainComplexMap_comp_smallSingularSubcomplex_chainComplexπ_eq_zero
    {Z W : TopCat.{w}} {ι : Type*} (U : ι → Set W) (f : Z ⟶ W) {i : ι} (hf : ∀ z, f z ∈ U i)
    (T : C) :
    SSet.chainComplexMap (toSSet.map f) T ≫ (W.smallSingularSubcomplex U).pair.chainComplexπ T =
      0 := by
  have hι : SSet.chainComplexMap (W.smallSingularSubcomplex U).ι T ≫
      (W.smallSingularSubcomplex U).pair.chainComplexπ T = 0 :=
    (W.smallSingularSubcomplex U).pair.chainComplex_condition T
  have hmap : SSet.chainComplexMap (toSSet.map f) T =
      SSet.chainComplexMap
        (toSSet.map (ofHom ⟨fun z ↦ ⟨f z, hf z⟩, f.hom.continuous.subtype_mk hf⟩) ≫
          toSmallSingularSubcomplex U (subset_refl (U i))) T ≫
      SSet.chainComplexMap (W.smallSingularSubcomplex U).ι T := by
    refine Eq.trans ?_ (((SSet.chainComplexFunctor C).obj T).map_comp _ _)
    congr 2
    rw [Category.assoc, toSmallSingularSubcomplex_ι, ← toSSet.map_comp]
    rfl
  exact (eq_whisker hmap _).trans ((Category.assoc _ _ _).trans ((whisker_eq _ hι).trans comp_zero))

variable [MonoidalCategory C] [MonoidalPreadditive C]

/-- Functoriality of `⊗ₘ` on `ℕ`-indexed chain complexes without requiring the full
`MonoidalCategory (ChainComplex C ℕ)` instance. -/
private lemma chainComplex_tensorHom_comp {K₁ L₁ M₁ K₂ L₂ M₂ : ChainComplex C ℕ}
    (f₁ : K₁ ⟶ L₁) (g₁ : L₁ ⟶ M₁) (f₂ : K₂ ⟶ L₂) (g₂ : L₂ ⟶ M₂) :
    (f₁ ≫ g₁) ⊗ₘ (f₂ ≫ g₂) = (f₁ ⊗ₘ f₂) ≫ (g₁ ⊗ₘ g₂) :=
  mapBifunctorMap_comp (curriedTensor C) (ComplexShape.down ℕ) f₁ g₁ f₂ g₂

/-- The short exact sequence `0 ⟶ C(A; R) ⊗ C(Y; S) ⟶ C(X; R) ⊗ C(Y; S) ⟶ C(X, A; R) ⊗ C(Y; S) ⟶ 0`
obtained by tensoring the chain short exact sequence of `(X, A)` on the right with `C(Y; S)`. -/
private lemma shortExact_leftFactor (X Y : TopCat.{w}) (A : Set X) (R S : C) :
    (tensorRightShortComplex ((toSSet.obj Y).chainComplex S)
      ((TopPair.toSSetPair.obj (TopPair.ofSubset A)).chainComplexShortComplex R)).ShortExact :=
  shortExact_tensorRightShortComplex ((toSSet.obj Y).chainComplex S)
    ((TopPair.toSSetPair.obj (TopPair.ofSubset A)).chainComplexShortComplex R)
    ((TopPair.toSSetPair.obj (TopPair.ofSubset A)).shortExact_chainComplexShortComplex R)

/-- The short exact sequence
`0 ⟶ C(X, A; R) ⊗ C(B; S) ⟶ C(X, A; R) ⊗ C(Y; S) ⟶ C(X, A; R) ⊗ C(Y, B; S) ⟶ 0`
obtained by tensoring the chain short exact sequence of `(Y, B)` on the left with `C(X, A; R)`. -/
private lemma shortExact_rightFactor (X Y : TopCat.{w}) (A : Set X) (B : Set Y) (R S : C) :
    (tensorLeftShortComplex ((TopPair.ofSubset A).singularChainComplex R)
      ((TopPair.toSSetPair.obj (TopPair.ofSubset B)).chainComplexShortComplex S)).ShortExact :=
  shortExact_tensorLeftShortComplex ((TopPair.ofSubset A).singularChainComplex R)
    ((TopPair.toSSetPair.obj (TopPair.ofSubset B)).shortExact_chainComplexShortComplex S)

/-- The tensor product of the quotient maps `C(X; R) ⟶ C(X, A; R)` and `C(Y; S) ⟶ C(Y, B; S)` is an
epimorphism of chain complexes. -/
private instance epi_singularChainComplexπ_tensorHom
    (X Y : TopCat.{w}) (A : Set X) (B : Set Y) (R S : C) :
    Epi ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
      (TopPair.ofSubset B).singularChainComplexπ S) := by
  let f₁ : ((TopPair.toSSetPair.obj (TopPair.ofSubset A)).right.chainComplex R) ⊗
      ((TopPair.toSSetPair.obj (TopPair.ofSubset B)).right.chainComplex S) ⟶
      (TopPair.ofSubset A).singularChainComplex R ⊗
        ((TopPair.toSSetPair.obj (TopPair.ofSubset B)).right.chainComplex S) :=
    (TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
      𝟙 ((TopPair.toSSetPair.obj (TopPair.ofSubset B)).right.chainComplex S)
  let f₂ : (TopPair.ofSubset A).singularChainComplex R ⊗
      ((TopPair.toSSetPair.obj (TopPair.ofSubset B)).right.chainComplex S) ⟶
      (TopPair.ofSubset A).singularChainComplex R ⊗
        (TopPair.ofSubset B).singularChainComplex S :=
    𝟙 ((TopPair.ofSubset A).singularChainComplex R) ⊗ₘ
      (TopPair.ofSubset B).singularChainComplexπ S
  have : Epi f₁ := (shortExact_leftFactor X Y A R S).epi_g
  have : Epi f₂ := (shortExact_rightFactor X Y A B R S).epi_g
  have hfac : ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
      (TopPair.ofSubset B).singularChainComplexπ S) = f₁ ≫ f₂ :=
    (congrArg₂ (· ⊗ₘ ·) (Category.comp_id _).symm (Category.id_comp _).symm).trans
      (chainComplex_tensorHom_comp _ _ _ _)
  rw [hfac]
  exact epi_comp f₁ f₂

/-- **The relative Alexander–Whitney map**
`C(X × Y; A × Y + X × B; R ⊗ S) ⟶ C(X, A; R) ⊗ C(Y, B; S)` for subsets `A ⊆ X` and `B ⊆ Y`: the
relative Alexander–Whitney diagonal `TopCat.relativeAlexanderWhitneyDiagonal` of `fst⁻¹(A)` and
`snd⁻¹(B)`, followed by the projections to `(X, A)` and `(Y, B)`. -/
def relativeAlexanderWhitney (X Y : TopCat.{w}) (A : Set X) (B : Set Y) (R S : C) :
    ((X ⊗ Y).smallSingularSubcomplex ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.chainComplex (R ⊗ S) ⟶
      (TopPair.ofSubset A).singularChainComplex R ⊗ (TopPair.ofSubset B).singularChainComplex S :=
  relativeAlexanderWhitneyDiagonal (fst X Y ⁻¹' A) (snd X Y ⁻¹' B) (𝟙 (R ⊗ S)) ≫
    (TopPair.singularChainComplexMap (TopPair.ofSubsetMap (fst X Y) (Set.mapsTo_preimage _ _)) R ⊗ₘ
      TopPair.singularChainComplexMap (TopPair.ofSubsetMap (snd X Y) (Set.mapsTo_preimage _ _)) S)

/-- Precomposing the relative Alexander–Whitney map with the quotient from `C(X × Y; R ⊗ S)` gives
the absolute Alexander–Whitney map followed by `π_A ⊗ π_B`. -/
@[reassoc (attr := simp)]
lemma chainComplexπ_relativeAlexanderWhitney
    (X Y : TopCat.{w}) (A : Set X) (B : Set Y) (R S : C) :
    ((X ⊗ Y).smallSingularSubcomplex ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.chainComplexπ (R ⊗ S) ≫
        relativeAlexanderWhitney X Y A B R S =
      alexanderWhitney X Y R S ≫
        ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
          (TopPair.ofSubset B).singularChainComplexπ S) := by
  have hdiag : lift (𝟙 (X ⊗ Y)) (𝟙 (X ⊗ Y)) ≫ (fst X Y ⊗ₘ snd X Y) = 𝟙 (X ⊗ Y) := by
    ext <;> simp
  have hAW : alexanderWhitney X Y R S =
      (X ⊗ Y).alexanderWhitneyDiagonal (𝟙 (R ⊗ S)) ≫
        (SSet.chainComplexMap (toSSet.map (fst X Y)) R ⊗ₘ
          SSet.chainComplexMap (toSSet.map (snd X Y)) S) := by
    rw [TauCeti.alexanderWhitneyDiagonal_def, (SSet.chainComplexFunctor C).map_id]
    simp only [NatTrans.id_app, Category.id_comp, Category.assoc]
    rw [← alexanderWhitney_naturality (fst X Y) (snd X Y) R S, ← Category.assoc,
      ← ((SSet.chainComplexFunctor C).obj (R ⊗ S)).map_comp, ← toSSet.map_comp, hdiag,
      toSSet.map_id, ((SSet.chainComplexFunctor C).obj (R ⊗ S)).map_id, Category.id_comp]
  have hA := TopPair.singularChainComplexπ_pair_naturality
    (TopPair.ofSubsetMap (fst X Y) (Set.mapsTo_preimage _ A)) R
  have hB := TopPair.singularChainComplexπ_pair_naturality
    (TopPair.ofSubsetMap (snd X Y) (Set.mapsTo_preimage _ B)) S
  rw [TopPair.ofSubsetMap_fst] at hA hB
  have htensor : ((TopPair.ofSubset (fst X Y ⁻¹' A)).singularChainComplexπ R ⊗ₘ
      (TopPair.ofSubset (snd X Y ⁻¹' B)).singularChainComplexπ S) ≫
      (TopPair.singularChainComplexMap
          (TopPair.ofSubsetMap (fst X Y) (Set.mapsTo_preimage _ _)) R ⊗ₘ
        TopPair.singularChainComplexMap
          (TopPair.ofSubsetMap (snd X Y) (Set.mapsTo_preimage _ _)) S) =
      (SSet.chainComplexMap (toSSet.map (fst X Y)) R ⊗ₘ
        SSet.chainComplexMap (toSSet.map (snd X Y)) S) ≫
        ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
          (TopPair.ofSubset B).singularChainComplexπ S) :=
    (chainComplex_tensorHom_comp _ _ _ _).symm.trans
      ((congrArg₂ (· ⊗ₘ ·) hA.symm hB.symm).trans (chainComplex_tensorHom_comp _ _ _ _))
  exact (chainComplexπ_relativeAlexanderWhitneyDiagonal_assoc
      (fst X Y ⁻¹' A) (snd X Y ⁻¹' B) (𝟙 (R ⊗ S)) _).trans <|
    (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·) htensor).trans <|
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hAW.symm)

/-- **Naturality of the relative Alexander–Whitney map** in continuous maps `f : X ⟶ X'` carrying
`A` into `A'` and `g : Y ⟶ Y'` carrying `B` into `B'`. -/
@[reassoc]
lemma relativeAlexanderWhitney_naturality {X Y X' Y' : TopCat.{w}} {A : Set X} {B : Set Y}
    {A' : Set X'} {B' : Set Y'} (f : X ⟶ X') (g : Y ⟶ Y')
    (hf : Set.MapsTo f A A') (hg : Set.MapsTo g B B') (R S : C) :
    SSetPair.chainComplexMap (smallSingularSubcomplexPairMap (f ⊗ₘ g)
        (mapsTo_tensorHom_preimage_fst f g hf) (mapsTo_tensorHom_preimage_snd f g hg)) (R ⊗ S) ≫
        relativeAlexanderWhitney X' Y' A' B' R S =
      relativeAlexanderWhitney X Y A B R S ≫
        (TopPair.singularChainComplexMap (TopPair.ofSubsetMap f hf) R ⊗ₘ
          TopPair.singularChainComplexMap (TopPair.ofSubsetMap g hg) S) := by
  apply (cancel_epi
    (((X ⊗ Y).smallSingularSubcomplex ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.chainComplexπ
      (R ⊗ S))).1
  have hπ := SSetPair.chainComplexπ_naturality (R ⊗ S) (smallSingularSubcomplexPairMap (f ⊗ₘ g)
    (mapsTo_tensorHom_preimage_fst f g hf) (mapsTo_tensorHom_preimage_snd f g hg))
  rw [smallSingularSubcomplexPairMap_right] at hπ
  have hLHS : ((X ⊗ Y).smallSingularSubcomplex ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.chainComplexπ
      (R ⊗ S) ≫
      (SSetPair.chainComplexMap (smallSingularSubcomplexPairMap (f ⊗ₘ g)
          (mapsTo_tensorHom_preimage_fst f g hf) (mapsTo_tensorHom_preimage_snd f g hg)) (R ⊗ S) ≫
        relativeAlexanderWhitney X' Y' A' B' R S) =
      alexanderWhitney X Y R S ≫
        (SSet.chainComplexMap (toSSet.map f) R ⊗ₘ SSet.chainComplexMap (toSSet.map g) S) ≫
          ((TopPair.ofSubset A').singularChainComplexπ R ⊗ₘ
            (TopPair.ofSubset B').singularChainComplexπ S) :=
    (Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ _) hπ.symm).trans <|
      (Category.assoc _ _ _).trans <|
      (congrArg (_ ≫ ·) (chainComplexπ_relativeAlexanderWhitney X' Y' A' B' R S)).trans
        (alexanderWhitney_naturality_assoc f g R S _)
  have hA := TopPair.singularChainComplexπ_pair_naturality (TopPair.ofSubsetMap f hf) R
  have hB := TopPair.singularChainComplexπ_pair_naturality (TopPair.ofSubsetMap g hg) S
  rw [TopPair.ofSubsetMap_fst] at hA hB
  have hRHS : ((X ⊗ Y).smallSingularSubcomplex ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.chainComplexπ
      (R ⊗ S) ≫
      (relativeAlexanderWhitney X Y A B R S ≫
        (TopPair.singularChainComplexMap (TopPair.ofSubsetMap f hf) R ⊗ₘ
          TopPair.singularChainComplexMap (TopPair.ofSubsetMap g hg) S)) =
      alexanderWhitney X Y R S ≫
        (SSet.chainComplexMap (toSSet.map f) R ⊗ₘ SSet.chainComplexMap (toSSet.map g) S) ≫
          ((TopPair.ofSubset A').singularChainComplexπ R ⊗ₘ
            (TopPair.ofSubset B').singularChainComplexπ S) :=
    (chainComplexπ_relativeAlexanderWhitney_assoc X Y A B R S _).trans <|
      (Category.assoc _ _ _).trans <|
      whisker_eq _ ((chainComplex_tensorHom_comp _ _ _ _).symm.trans
        ((congrArg₂ (· ⊗ₘ ·) hA.symm hB.symm).trans (chainComplex_tensorHom_comp _ _ _ _)))
  exact hLHS.trans hRHS.symm

section Shuffle

variable [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft T)]
  [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight T)]

/-- On `C(A; R) ⊗ C(Y; S)`, the singular shuffle map of `X` and `Y` lands in the singular chains of
`A × Y`, so it vanishes in `C(X × Y; A × Y + X × B; R ⊗ S)`. -/
private lemma chainComplexMap_tensorHom_id_comp_shuffle_comp_chainComplexπ
    (X Y : TopCat.{w}) (A : Set X) (B : Set Y) (R S : C) :
    (SSet.chainComplexMap (TopPair.toSSetPair.obj (TopPair.ofSubset A)).hom R ⊗ₘ
        𝟙 ((toSSet.obj Y).chainComplex S)) ≫
      shuffle X Y R S ≫
        ((X ⊗ Y).smallSingularSubcomplex ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.chainComplexπ
          (R ⊗ S) = 0 := by
  let ιA : of ↥A ⟶ X := (TopPair.ofSubset A).map
  have hid : 𝟙 ((toSSet.obj Y).chainComplex S) = SSet.chainComplexMap (toSSet.map (𝟙 Y)) S :=
    (((SSet.chainComplexFunctor C).obj S).map_id (toSSet.obj Y)).symm.trans
      (congrArg (SSet.chainComplexMap · S) (toSSet.map_id Y).symm)
  have hsh : (SSet.chainComplexMap (TopPair.toSSetPair.obj (TopPair.ofSubset A)).hom R ⊗ₘ
      𝟙 ((toSSet.obj Y).chainComplex S)) ≫ shuffle X Y R S =
      shuffle (of ↥A) Y R S ≫ SSet.chainComplexMap (toSSet.map (ιA ⊗ₘ 𝟙 Y)) (R ⊗ S) :=
    (eq_whisker (congrArg (SSet.chainComplexMap (toSSet.map ιA) R ⊗ₘ ·) hid)
      (shuffle X Y R S)).trans (shuffle_naturality ιA (𝟙 Y) R S)
  refine (Category.assoc _ _ _).symm.trans
    ((eq_whisker hsh _).trans ((Category.assoc _ _ _).trans ?_))
  have hf (z) : (ιA ⊗ₘ 𝟙 Y) z ∈ ![fst X Y ⁻¹' A, snd X Y ⁻¹' B] 0 := by
    have hz : fst X Y ((ιA ⊗ₘ 𝟙 Y) z) = ιA (fst (of ↥A) Y z) :=
      ConcreteCategory.congr_hom (tensorHom_fst ιA (𝟙 Y)) z
    rw [Matrix.cons_val_zero]
    exact Set.mem_preimage.2 (hz.symm ▸ (fst (of ↥A) Y z).2)
  exact (whisker_eq _
    (chainComplexMap_comp_smallSingularSubcomplex_chainComplexπ_eq_zero _ _ hf _)).trans comp_zero

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
  let pA : ((TopPair.toSSetPair.obj (TopPair.ofSubset A)).right.chainComplex R) ⊗
      ((TopPair.toSSetPair.obj (TopPair.ofSubset B)).left.chainComplex S) ⟶
      (TopPair.ofSubset A).singularChainComplex R ⊗
        ((TopPair.toSSetPair.obj (TopPair.ofSubset B)).left.chainComplex S) :=
    (TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
      𝟙 ((TopPair.toSSetPair.obj (TopPair.ofSubset B)).left.chainComplex S)
  have : Epi pA := (shortExact_tensorRightShortComplex
    ((TopPair.toSSetPair.obj (TopPair.ofSubset B)).left.chainComplex S)
    ((TopPair.toSSetPair.obj (TopPair.ofSubset A)).chainComplexShortComplex R)
    ((TopPair.toSSetPair.obj (TopPair.ofSubset A)).shortExact_chainComplexShortComplex R)).epi_g
  apply (cancel_epi pA).1
  rw [comp_zero]
  have hcomm : pA ≫ (𝟙 ((TopPair.ofSubset A).singularChainComplex R) ⊗ₘ
      SSet.chainComplexMap (TopPair.toSSetPair.obj (TopPair.ofSubset B)).hom S) =
      (𝟙 ((toSSet.obj X).chainComplex R) ⊗ₘ SSet.chainComplexMap (toSSet.map ιB) S) ≫
        ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
          𝟙 ((toSSet.obj Y).chainComplex S)) := by
    refine (chainComplex_tensorHom_comp _ _ _ _).symm.trans ?_
    rw [Category.comp_id, Category.id_comp]
    exact (congrArg₂ (· ⊗ₘ ·) (Category.id_comp _).symm (Category.comp_id _).symm).trans
      (chainComplex_tensorHom_comp _ _ _ _)
  refine (Category.assoc _ _ _).symm.trans ((eq_whisker hcomm _).trans <|
    (Category.assoc _ _ _).trans <|
    (whisker_eq _ (singularChainComplexπ_tensorHom_id_leftRelativeShuffle X Y A B R S)).trans ?_)
  have hid : 𝟙 ((toSSet.obj X).chainComplex R) = SSet.chainComplexMap (toSSet.map (𝟙 X)) R :=
    (((SSet.chainComplexFunctor C).obj R).map_id (toSSet.obj X)).symm.trans
      (congrArg (SSet.chainComplexMap · R) (toSSet.map_id X).symm)
  have hsh : (𝟙 ((toSSet.obj X).chainComplex R) ⊗ₘ
      SSet.chainComplexMap (toSSet.map ιB) S) ≫ shuffle X Y R S =
      shuffle X (of ↥B) R S ≫ SSet.chainComplexMap (toSSet.map (𝟙 X ⊗ₘ ιB)) (R ⊗ S) :=
    (eq_whisker (congrArg (· ⊗ₘ SSet.chainComplexMap (toSSet.map ιB) S) hid)
      (shuffle X Y R S)).trans (shuffle_naturality (𝟙 X) ιB R S)
  refine (Category.assoc _ _ _).symm.trans
    ((eq_whisker hsh _).trans ((Category.assoc _ _ _).trans ?_))
  have hf (z) : (𝟙 X ⊗ₘ ιB) z ∈ ![fst X Y ⁻¹' A, snd X Y ⁻¹' B] 1 := by
    have hz : snd X Y ((𝟙 X ⊗ₘ ιB) z) = ιB (snd X (of ↥B) z) :=
      ConcreteCategory.congr_hom (tensorHom_snd (𝟙 X) ιB) z
    rw [Matrix.cons_val_one, Matrix.cons_val_zero]
    exact Set.mem_preimage.2 (hz.symm ▸ (snd X (of ↥B) z).2)
  exact (whisker_eq _
    (chainComplexMap_comp_smallSingularSubcomplex_chainComplexπ_eq_zero _ _ hf _)).trans comp_zero

/-- **The relative shuffle map**
`C(X, A; R) ⊗ C(Y, B; S) ⟶ C(X × Y; A × Y + X × B; R ⊗ S)` for subsets `A ⊆ X` and `B ⊆ Y`: the
descent of the singular shuffle map `TopCat.shuffle X Y R S`, followed by the quotient map from
`C(X × Y; R ⊗ S)` to the chains relative to singular simplices lying in `fst⁻¹(A)` or in
`snd⁻¹(B)`. -/
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
      (chainComplex_tensorHom_comp _ _ _ _)
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
  apply (cancel_epi ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
    (TopPair.ofSubset B).singularChainComplexπ S)).1
  have hπ := SSetPair.chainComplexπ_naturality (R ⊗ S) (smallSingularSubcomplexPairMap (f ⊗ₘ g)
    (mapsTo_tensorHom_preimage_fst f g hf) (mapsTo_tensorHom_preimage_snd f g hg))
  rw [smallSingularSubcomplexPairMap_right] at hπ
  have hRHS : ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
      (TopPair.ofSubset B).singularChainComplexπ S) ≫
      (relativeShuffle X Y A B R S ≫
        SSetPair.chainComplexMap (smallSingularSubcomplexPairMap (f ⊗ₘ g)
          (mapsTo_tensorHom_preimage_fst f g hf) (mapsTo_tensorHom_preimage_snd f g hg))
          (R ⊗ S)) =
      (SSet.chainComplexMap (toSSet.map f) R ⊗ₘ SSet.chainComplexMap (toSSet.map g) S) ≫
        shuffle X' Y' R S ≫
          ((X' ⊗ Y').smallSingularSubcomplex
            ![fst X' Y' ⁻¹' A', snd X' Y' ⁻¹' B']).pair.chainComplexπ (R ⊗ S) :=
    (singularChainComplexπ_tensorHom_relativeShuffle_assoc X Y A B R S _).trans <|
      (Category.assoc _ _ _).trans <|
      (congrArg (_ ≫ ·) hπ.symm).trans (shuffle_naturality_assoc f g R S _).symm
  have hA := TopPair.singularChainComplexπ_pair_naturality (TopPair.ofSubsetMap f hf) R
  have hB := TopPair.singularChainComplexπ_pair_naturality (TopPair.ofSubsetMap g hg) S
  rw [TopPair.ofSubsetMap_fst] at hA hB
  have hLHS : ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
      (TopPair.ofSubset B).singularChainComplexπ S) ≫
      ((TopPair.singularChainComplexMap (TopPair.ofSubsetMap f hf) R ⊗ₘ
        TopPair.singularChainComplexMap (TopPair.ofSubsetMap g hg) S) ≫
        relativeShuffle X' Y' A' B' R S) =
      (SSet.chainComplexMap (toSSet.map f) R ⊗ₘ SSet.chainComplexMap (toSSet.map g) S) ≫
        shuffle X' Y' R S ≫
          ((X' ⊗ Y').smallSingularSubcomplex
            ![fst X' Y' ⁻¹' A', snd X' Y' ⁻¹' B']).pair.chainComplexπ (R ⊗ S) :=
    (Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ _) ((chainComplex_tensorHom_comp _ _ _ _).symm.trans
        ((congrArg₂ (· ⊗ₘ ·) hA.symm hB.symm).trans
          (chainComplex_tensorHom_comp _ _ _ _)))).trans <|
      (Category.assoc _ _ _).trans
        (whisker_eq _ (singularChainComplexπ_tensorHom_relativeShuffle X' Y' A' B' R S))
  exact hLHS.trans hRHS.symm

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
  apply (cancel_epi ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
    (TopPair.ofSubset B).singularChainComplexπ S)).1
  have hπ : ((X ⊗ Y).smallSingularSubcomplex ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.chainComplexπ
        (R ⊗ S) ≫
      ((SSetPair.chainComplexFunctor C).map (φ ⊗ₘ ψ)).app
        ((X ⊗ Y).smallSingularSubcomplex ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair =
      ((SSet.chainComplexFunctor C).map (φ ⊗ₘ ψ)).app (toSSet.obj (X ⊗ Y)) ≫
        ((X ⊗ Y).smallSingularSubcomplex ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.chainComplexπ
          (R' ⊗ S') :=
    NatTrans.congr_app ((SSetPair.chainComplexFunctorπ C).naturality (φ ⊗ₘ ψ)).symm
      ((X ⊗ Y).smallSingularSubcomplex ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair
  have hRHS : ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
      (TopPair.ofSubset B).singularChainComplexπ S) ≫
      (relativeShuffle X Y A B R S ≫
        ((SSetPair.chainComplexFunctor C).map (φ ⊗ₘ ψ)).app
          ((X ⊗ Y).smallSingularSubcomplex ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair) =
      (((SSet.chainComplexFunctor C).map φ).app (toSSet.obj X) ⊗ₘ
        ((SSet.chainComplexFunctor C).map ψ).app (toSSet.obj Y)) ≫
        shuffle X Y R' S' ≫
          ((X ⊗ Y).smallSingularSubcomplex ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.chainComplexπ
            (R' ⊗ S') :=
    (singularChainComplexπ_tensorHom_relativeShuffle_assoc X Y A B R S _).trans <|
      (Category.assoc _ _ _).trans <|
      (whisker_eq _ hπ).trans (shuffle_coefficient_naturality_assoc X Y φ ψ _).symm
  have hA : (TopPair.ofSubset A).singularChainComplexπ R ≫
      ((SSetPair.chainComplexFunctor C).map φ).app (TopPair.toSSetPair.obj (TopPair.ofSubset A)) =
      ((SSet.chainComplexFunctor C).map φ).app (toSSet.obj X) ≫
        (TopPair.ofSubset A).singularChainComplexπ R' :=
    NatTrans.congr_app ((SSetPair.chainComplexFunctorπ C).naturality φ).symm
      (TopPair.toSSetPair.obj (TopPair.ofSubset A))
  have hB : (TopPair.ofSubset B).singularChainComplexπ S ≫
      ((SSetPair.chainComplexFunctor C).map ψ).app (TopPair.toSSetPair.obj (TopPair.ofSubset B)) =
      ((SSet.chainComplexFunctor C).map ψ).app (toSSet.obj Y) ≫
        (TopPair.ofSubset B).singularChainComplexπ S' :=
    NatTrans.congr_app ((SSetPair.chainComplexFunctorπ C).naturality ψ).symm
      (TopPair.toSSetPair.obj (TopPair.ofSubset B))
  have hLHS : ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
      (TopPair.ofSubset B).singularChainComplexπ S) ≫
      ((((SSetPair.chainComplexFunctor C).map φ).app
          (TopPair.toSSetPair.obj (TopPair.ofSubset A)) ⊗ₘ
        ((SSetPair.chainComplexFunctor C).map ψ).app
          (TopPair.toSSetPair.obj (TopPair.ofSubset B))) ≫
        relativeShuffle X Y A B R' S') =
      (((SSet.chainComplexFunctor C).map φ).app (toSSet.obj X) ⊗ₘ
        ((SSet.chainComplexFunctor C).map ψ).app (toSSet.obj Y)) ≫
        shuffle X Y R' S' ≫
          ((X ⊗ Y).smallSingularSubcomplex ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.chainComplexπ
            (R' ⊗ S') :=
    (Category.assoc _ _ _).symm.trans <|
      (eq_whisker ((chainComplex_tensorHom_comp _ _ _ _).symm.trans
        ((congrArg₂ (· ⊗ₘ ·) hA hB).trans (chainComplex_tensorHom_comp _ _ _ _))) _).trans <|
      (Category.assoc _ _ _).trans
        (whisker_eq _ (singularChainComplexπ_tensorHom_relativeShuffle X Y A B R' S'))
  exact hLHS.trans hRHS.symm

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
  have hS₁ := shortExact_leftFactor X Y A R S
  let hH : _root_.Homotopy (shuffle X Y R S ≫ alexanderWhitney X Y R S) (𝟙 _) :=
    (_root_.Homotopy.ofEq (shuffle_alexanderWhitney X Y R S)).trans
      (SSet.shuffleAlexanderWhitneyHomotopy (toSSet.obj X) (toSSet.obj Y) R S)
  have hH_hom (i j : ℕ) : hH.hom i j =
      (SSet.shuffleAlexanderWhitneyHomotopy (toSSet.obj X) (toSSet.obj Y) R S).hom i j := by
    simp [hH]
  have hfac : S₁.g ≫
      (tensorLeftShortComplex ((TopPair.ofSubset A).singularChainComplex R)
        ((TopPair.toSSetPair.obj (TopPair.ofSubset B)).chainComplexShortComplex S)).g =
      ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
        (TopPair.ofSubset B).singularChainComplexπ S) :=
    (chainComplex_tensorHom_comp _ _ _ _).symm.trans
      (congrArg₂ (· ⊗ₘ ·) (Category.comp_id _) (Category.id_comp _))
  refine _root_.Homotopy.descCokernel hH S₁.f S₁.g
    ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
      (TopPair.ofSubset B).singularChainComplexπ S)
    (fun i ↦ (HomologicalComplex.comp_f S₁.f S₁.g i).symm.trans
      ((HomologicalComplex.congr_hom S₁.zero i).trans (HomologicalComplex.zero_f _ _ i)))
    (fun i ↦ ((shortExact_iff_degreewise_shortExact S₁).1 hS₁ i).gIsCokernel)
    (fun i j ↦ ?_) ?_ ?_
  · rw [hH_hom]
    have hid : 𝟙 ((toSSet.obj Y).chainComplex S) = SSet.chainComplexMap (𝟙 (toSSet.obj Y)) S :=
      (((SSet.chainComplexFunctor C).obj S).map_id _).symm
    have hnat := SSet.shuffleAlexanderWhitneyHomotopy_hom_naturality_assoc
      (R := R) (S := S) (toSSet.map (TopPair.ofSubset A).map) (𝟙 (toSSet.obj Y)) i j
      (((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
        (TopPair.ofSubset B).singularChainComplexπ S).f j)
    have hzero : (SSet.chainComplexMap (toSSet.map (TopPair.ofSubset A).map) R ⊗ₘ
        𝟙 ((toSSet.obj Y).chainComplex S)) ≫
        ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
          (TopPair.ofSubset B).singularChainComplexπ S) = 0 :=
      (chainComplex_tensorHom_comp _ _ _ _).symm.trans <|
        (congrArg (· ⊗ₘ _)
          ((TopPair.toSSetPair.obj (TopPair.ofSubset A)).chainComplex_condition R)).trans
          (zero_tensorHom _)
    refine (eq_whisker (congrArg (fun g ↦
      (SSet.chainComplexMap (toSSet.map (TopPair.ofSubset A).map) R ⊗ₘ g).f i) hid) _).trans
      (hnat.trans ?_)
    refine (whisker_eq _ (eq_whisker (congrArg (fun g ↦
      (SSet.chainComplexMap (toSSet.map (TopPair.ofSubset A).map) R ⊗ₘ g).f j)
        hid.symm) _)).trans ?_
    exact (whisker_eq _ ((HomologicalComplex.comp_f _ _ j).symm.trans
      ((HomologicalComplex.congr_hom hzero j).trans (HomologicalComplex.zero_f _ _ j)))).trans
      comp_zero
  · exact (Category.assoc _ _ _).symm.trans <|
      (eq_whisker hfac _).trans <|
      (singularChainComplexπ_tensorHom_relativeShuffle_assoc X Y A B R S _).trans <|
      (Category.assoc _ _ _).trans <|
      (whisker_eq _ (chainComplexπ_relativeAlexanderWhitney X Y A B R S)).trans
        (Category.assoc _ _ _).symm
  · exact hfac.trans (Category.id_comp _).symm

private lemma π_leftRelativeShuffleAlexanderWhitneyHomotopy_hom
    (X Y : TopCat.{w}) (A : Set X) (B : Set Y) (R S : C) (i j : ℕ) :
    ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ 𝟙 ((toSSet.obj Y).chainComplex S)).f i ≫
        (leftRelativeShuffleAlexanderWhitneyHomotopy X Y A B R S).hom i j =
      (SSet.shuffleAlexanderWhitneyHomotopy (toSSet.obj X) (toSSet.obj Y) R S).hom i j ≫
        ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
          (TopPair.ofSubset B).singularChainComplexπ S).f j := by
  unfold leftRelativeShuffleAlexanderWhitneyHomotopy
  refine (_root_.Homotopy.π_descCokernel_hom _ _ _ _ _ _ _ _ _ i j).trans (eq_whisker ?_ _)
  simp only [_root_.Homotopy.trans_hom, _root_.Homotopy.ofEq_hom, Pi.zero_apply, zero_add]
  rfl

/-- **The relative Eilenberg–Zilber chain homotopy** `AW ∘ shuffle ≃ id`: for subsets `A ⊆ X` and
`B ⊆ Y`, the relative shuffle map `TopCat.relativeShuffle` followed by the relative
Alexander–Whitney map `TopCat.relativeAlexanderWhitney` is chain homotopic to the identity of
`C(X, A; R) ⊗ C(Y, B; S)`. -/
def relativeShuffleAlexanderWhitneyHomotopy
    (X Y : TopCat.{w}) (A : Set X) (B : Set Y) (R S : C) :
    _root_.Homotopy
      (relativeShuffle X Y A B R S ≫ relativeAlexanderWhitney X Y A B R S) (𝟙 _) := by
  let S₂ := tensorLeftShortComplex ((TopPair.ofSubset A).singularChainComplex R)
    ((TopPair.toSSetPair.obj (TopPair.ofSubset B)).chainComplexShortComplex S)
  have hS₂ := shortExact_rightFactor X Y A B R S
  let H₁ := leftRelativeShuffleAlexanderWhitneyHomotopy X Y A B R S
  refine _root_.Homotopy.descCokernel H₁ S₂.f S₂.g (𝟙 _)
    (fun i ↦ (HomologicalComplex.comp_f S₂.f S₂.g i).symm.trans
      ((HomologicalComplex.congr_hom S₂.zero i).trans (HomologicalComplex.zero_f _ _ i)))
    (fun i ↦ ((shortExact_iff_degreewise_shortExact S₂).1 hS₂ i).gIsCokernel)
    (fun i j ↦ ?_) (Category.comp_id _).symm rfl
  let pA : ((TopPair.toSSetPair.obj (TopPair.ofSubset A)).right.chainComplex R) ⊗
      ((TopPair.toSSetPair.obj (TopPair.ofSubset B)).left.chainComplex S) ⟶
      (TopPair.ofSubset A).singularChainComplex R ⊗
        ((TopPair.toSSetPair.obj (TopPair.ofSubset B)).left.chainComplex S) :=
    (TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
      𝟙 ((TopPair.toSSetPair.obj (TopPair.ofSubset B)).left.chainComplex S)
  have : Epi (pA.f i) := by
    have hE := shortExact_tensorRightShortComplex
      ((TopPair.toSSetPair.obj (TopPair.ofSubset B)).left.chainComplex S)
      ((TopPair.toSSetPair.obj (TopPair.ofSubset A)).chainComplexShortComplex R)
      ((TopPair.toSSetPair.obj (TopPair.ofSubset A)).shortExact_chainComplexShortComplex R)
    exact ((shortExact_iff_degreewise_shortExact _).1 hE i).epi_g
  apply (cancel_epi (pA.f i)).1
  rw [comp_zero, HomologicalComplex.id_f, Category.comp_id]
  have hcomm : pA ≫ S₂.f =
      (𝟙 ((toSSet.obj X).chainComplex R) ⊗ₘ
        SSet.chainComplexMap (toSSet.map (TopPair.ofSubset B).map) S) ≫
        ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ 𝟙 ((toSSet.obj Y).chainComplex S)) := by
    refine (chainComplex_tensorHom_comp _ _ _ _).symm.trans ?_
    rw [Category.comp_id, Category.id_comp]
    exact (congrArg₂ (· ⊗ₘ ·) (Category.id_comp _).symm (Category.comp_id _).symm).trans
      (chainComplex_tensorHom_comp _ _ _ _)
  have hπH₁ := π_leftRelativeShuffleAlexanderWhitneyHomotopy_hom X Y A B R S i j
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
    (chainComplex_tensorHom_comp _ _ _ _).symm.trans <|
      (congrArg (_ ⊗ₘ ·)
        ((TopPair.toSSetPair.obj (TopPair.ofSubset B)).chainComplex_condition S)).trans
        (tensorHom_zero _)
  refine (Category.assoc _ _ _).symm.trans <|
    (eq_whisker ((HomologicalComplex.comp_f _ _ i).symm.trans
      ((HomologicalComplex.congr_hom hcomm i).trans (HomologicalComplex.comp_f _ _ i))) _).trans <|
    (Category.assoc _ _ _).trans <|
    (whisker_eq _ hπH₁).trans <|
    (eq_whisker (congrArg (fun g ↦
      (g ⊗ₘ SSet.chainComplexMap (toSSet.map (TopPair.ofSubset B).map) S).f i) hid) _).trans
      (hnat.trans ?_)
  refine (whisker_eq _ (eq_whisker (congrArg (fun g ↦
    (g ⊗ₘ SSet.chainComplexMap (toSSet.map (TopPair.ofSubset B).map) S).f j) hid.symm) _)).trans ?_
  exact (whisker_eq _ ((HomologicalComplex.comp_f _ _ j).symm.trans
    ((HomologicalComplex.congr_hom hzero j).trans (HomologicalComplex.zero_f _ _ j)))).trans
    comp_zero

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
`B ⊆ Y`, and `p + q = n`: the algebraic homology cross product of the relative singular chain
complexes, followed by the map induced on homology by `TopCat.relativeShuffle` and the inclusion
`TopCat.smallSingularSubcomplexPairToUnion` of small simplices into `fst⁻¹(A) ∪ snd⁻¹(B)`. -/
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
  let πA : (toSSet.obj X).chainComplex R ⟶ (TopPair.ofSubset A).singularChainComplex R :=
    (TopPair.ofSubset A).singularChainComplexπ R
  let πB : (toSSet.obj Y).chainComplex S ⟶ (TopPair.ofSubset B).singularChainComplex S :=
    (TopPair.ofSubset B).singularChainComplexπ S
  let πU : (toSSet.obj (X ⊗ Y)).chainComplex (R ⊗ S) ⟶
      (TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)).singularChainComplex (R ⊗ S) :=
    (TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)).singularChainComplexπ (R ⊗ S)
  let φ := relativeShuffle X Y A B R S
  let ψ := SSetPair.chainComplexMap
    (smallSingularSubcomplexPairToUnion (fst X Y ⁻¹' A) (snd X Y ⁻¹' B)) (R ⊗ S)
  have hsh : HomologicalComplex.tensorHom πA πB ≫ (φ ≫ ψ) = shuffle X Y R S ≫ πU :=
    (singularChainComplexπ_tensorHom_relativeShuffle_assoc X Y A B R S _).trans <|
      (Category.assoc _ _ _).trans <|
      whisker_eq _ (chainComplexπ_smallSingularSubcomplexPairToUnion (R := R ⊗ S)
        (U := fst X Y ⁻¹' A) (V := snd X Y ⁻¹' B))
  -- `singularHomologyπ` and `SSetPair.homologyMap` are by definition `homologyMap` on chains.
  exact (whisker_eq _ (whisker_eq _ (homologyMap_comp φ ψ n).symm)).trans <|
    (homologyCross_naturality_assoc πA πB p q n h (homologyMap (φ ≫ ψ) n)).trans <|
    (whisker_eq _ ((homologyMap_comp (HomologicalComplex.tensorHom πA πB) (φ ≫ ψ) n).symm.trans
      ((congrArg (homologyMap · n) hsh).trans (homologyMap_comp (shuffle X Y R S) πU n)))).trans <|
      (Category.assoc _ _ _).symm.trans
        (eq_whisker (singularHomologyCross_def X Y R S p q n h).symm _)

/-- **Naturality of the relative homology cross product** in continuous maps `f : X ⟶ X'` carrying
`A` into `A'` and `g : Y ⟶ Y'` carrying `B` into `B'`. -/
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

/-- **Naturality of the relative homology cross product** in both coefficient objects. -/
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
  let fA : (TopPair.ofSubset A).singularChainComplex R ⟶
      (TopPair.ofSubset A).singularChainComplex R' :=
    ((SSetPair.chainComplexFunctor C).map φ).app (TopPair.toSSetPair.obj (TopPair.ofSubset A))
  let fB : (TopPair.ofSubset B).singularChainComplex S ⟶
      (TopPair.ofSubset B).singularChainComplex S' :=
    ((SSetPair.chainComplexFunctor C).map ψ).app (TopPair.toSSetPair.obj (TopPair.ofSubset B))
  let e : (TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)).singularChainComplex (R ⊗ S) ⟶
      (TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)).singularChainComplex (R' ⊗ S') :=
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
