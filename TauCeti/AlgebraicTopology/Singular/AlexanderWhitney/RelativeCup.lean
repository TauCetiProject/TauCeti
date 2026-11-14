/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Bifunctor.Basic
public import TauCeti.AlgebraicTopology.Singular.AlexanderWhitney.Basic
public import TauCeti.AlgebraicTopology.Singular.AlexanderWhitney.Relative
public import TauCeti.AlgebraicTopology.Singular.KoszulBraiding
public import TauCeti.AlgebraicTopology.Singular.MayerVietoris.Relative

/-!
# Alexander–Whitney diagonals for relative cup products

The Alexander–Whitney diagonal `C(X; T) ⟶ C(X; R) ⊗ C(X; S)` of a space `X` sends a singular
simplex `σ` to `∑_{p + q = n} σ|[0, …, p] ⊗ σ|[p, …, n]`.  If `σ` lies in a subspace, so do its
front and back faces.  This file records the two descents of the diagonal to relative chains along
which relative cup products are taken.

* For a pair `(X, A)`, the diagonal followed by the quotient map to relative chains on the second
  factor vanishes on the chains of `A`, and descends to
  `TopPair.rightAlexanderWhitneyDiagonal : C(X, A; T) ⟶ C(X; R) ⊗ C(X, A; S)`.  It gives the
  action `Hᵖ(X) × H^q(X, A) ⟶ Hⁿ(X, A)` of absolute cohomology on relative cohomology.  Followed
  by the Koszul braiding it is chain homotopic to the relative diagonal
  `TopPair.alexanderWhitneyDiagonal : C(X, A; T) ⟶ C(X, A; S) ⊗ C(X; R)` of the braided
  coefficient morphism: the homotopy of `X` comparing the two orders of the factors is natural,
  so it carries the chains of `A` into those of `A × A` and descends to relative chains.
* For subsets `U` and `V` of `X`, the diagonal followed by the quotient maps on both factors
  vanishes on the chains of `U` and on those of `V`, hence on the chains `C(U) + C(V)` of the
  singular simplices of `X` lying in `U` or in `V` (the subcomplex `X.smallSingularSubcomplex
  ![U, V]`).  It descends to `TopCat.relativeAlexanderWhitneyDiagonal :
  C(X; U + V; T) ⟶ C(X, U; R) ⊗ C(X, V; S)`, where `C(X; U + V)` is the quotient of `C(X)` by
  `C(U) + C(V)`.  When `U` and `V` are open in `U ∪ V`, the small-chain theorem identifies
  `C(X; U + V)` with `C(X, U ∪ V)` up to quasi-isomorphism, which gives the relative cup product
  `Hᵖ(X, U) × H^q(X, V) ⟶ Hⁿ(X, U ∪ V)`.

* For pairs `(X, A)` and `(Y, B)`, composing `TopCat.relativeAlexanderWhitneyDiagonal` for
  `fst⁻¹(A)` and `snd⁻¹(B)` with the projections defines `TopCat.relativeAlexanderWhitney :
  C(X × Y; A × Y + X × B; R ⊗ S) ⟶ C(X, A; R) ⊗ C(Y, B; S)`.

## Main definitions and results

* `TopPair.rightAlexanderWhitneyDiagonal`, characterized by
  `TopPair.singularChainComplexπ_rightAlexanderWhitneyDiagonal` and natural in maps of pairs
  (`TopPair.rightAlexanderWhitneyDiagonal_naturality`).
* `TopPair.rightAlexanderWhitneyDiagonalKoszulBraidingHomotopy`: the right relative diagonal
  followed by the Koszul braiding is chain homotopic to the relative diagonal
  `TopPair.alexanderWhitneyDiagonal` of the braided coefficient morphism.
* `TopCat.relativeAlexanderWhitneyDiagonal`, characterized by
  `TopCat.chainComplexπ_relativeAlexanderWhitneyDiagonal`, natural in maps of spaces
  (`TopCat.relativeAlexanderWhitneyDiagonal_naturality`), and functorial in the chain coefficient
  morphism (`TauCeti.relativeAlexanderWhitneyDiagonal_comp`).
* `TopCat.relativeAlexanderWhitney`, characterized by
  `TopCat.chainComplexπ_relativeAlexanderWhitney` and natural in pairs
  (`TopCat.relativeAlexanderWhitney_naturality`) and coefficients
  (`TopCat.relativeAlexanderWhitney_coefficient_naturality`).

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.2, the relative cup product `Hᵏ(X, A) × Hˡ(X, B) ⟶ Hᵏ⁺ˡ(X, A ∪ B)`.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory

universe w v u

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C] {R S T : C}

namespace TopPair

/-- The Alexander–Whitney diagonal of the ambient space of a pair, followed by the quotient map to
relative chains on the second factor, vanishes on the singular chains of the subspace. -/
private lemma chainComplexMap_comp_alexanderWhitneyDiagonal_comp_whiskerLeft (P : TopPair.{w})
    (u : T ⟶ R ⊗ S) :
    SSet.chainComplexMap (toSSetPair.obj P).hom T ≫ P.fst.alexanderWhitneyDiagonal u ≫
      ((TopCat.toSSet.obj P.fst).chainComplex R ◁ P.singularChainComplexπ S) = 0 :=
  (TopCat.alexanderWhitneyDiagonal_naturality_assoc P.map u _).trans <|
    (congrArg (_ ≫ ·) <| (tensorHom_comp_whiskerLeft _ _ _).trans <|
      (congrArg (_ ⊗ₘ ·) (chainComplexMap_comp_singularChainComplexπ P S)).trans
        (HomologicalComplex.mapBifunctorMap_zero_right _ _ _ _ _)).trans comp_zero

/-- **The right relative Alexander–Whitney diagonal** `C(X, A; T) ⟶ C(X; R) ⊗ C(X, A; S)` of a
pair `(X, A)`: the Alexander–Whitney diagonal `C(X; T) ⟶ C(X; R) ⊗ C(X; S)` of `X` followed by
the quotient map to relative chains on the second factor, which vanishes on the chains of `A` and
so descends to relative chains. -/
def rightAlexanderWhitneyDiagonal (P : TopPair.{w}) (u : T ⟶ R ⊗ S) :
    P.singularChainComplex T ⟶
      (TopCat.toSSet.obj P.fst).chainComplex R ⊗ P.singularChainComplex S :=
  (CokernelCofork.IsColimit.desc' (P.isColimitCokernelCoforkSingularChainComplex T)
    (P.fst.alexanderWhitneyDiagonal u ≫
      ((TopCat.toSSet.obj P.fst).chainComplex R ◁ P.singularChainComplexπ S))
    (chainComplexMap_comp_alexanderWhitneyDiagonal_comp_whiskerLeft P u)).1

/-- The right relative Alexander–Whitney diagonal of a pair `(X, A)` is the descent of the
Alexander–Whitney diagonal of `X`, followed by the quotient map on the second factor. -/
@[reassoc (attr := simp)]
lemma singularChainComplexπ_rightAlexanderWhitneyDiagonal (P : TopPair.{w}) (u : T ⟶ R ⊗ S) :
    P.singularChainComplexπ T ≫ P.rightAlexanderWhitneyDiagonal u =
      P.fst.alexanderWhitneyDiagonal u ≫
        ((TopCat.toSSet.obj P.fst).chainComplex R ◁ P.singularChainComplexπ S) :=
  (CokernelCofork.IsColimit.desc' (P.isColimitCokernelCoforkSingularChainComplex T) _
    (chainComplexMap_comp_alexanderWhitneyDiagonal_comp_whiskerLeft P u)).2

/-- The right relative Alexander–Whitney diagonal is natural in maps of pairs. -/
@[reassoc]
lemma rightAlexanderWhitneyDiagonal_naturality {P P' : TopPair.{w}} (f : P ⟶ P')
    (u : T ⟶ R ⊗ S) :
    singularChainComplexMap f T ≫ P'.rightAlexanderWhitneyDiagonal u =
      P.rightAlexanderWhitneyDiagonal u ≫
        (SSet.chainComplexMap (TopCat.toSSet.map (Hom.fst f)) R ⊗ₘ
          singularChainComplexMap f S) := by
  rw [← cancel_epi (P.singularChainComplexπ T)]
  -- Term-mode steps: `rw` cannot match here, since the ambient chains appear both as
  -- `(toSSetPair.obj P).right.chainComplex R` and as `(TopCat.toSSet.obj P.fst).chainComplex R`.
  refine (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ P'.rightAlexanderWhitneyDiagonal u)
      (singularChainComplexπ_pair_naturality f T).symm).trans <|
    (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·) (singularChainComplexπ_rightAlexanderWhitneyDiagonal P' u)).trans <|
    (TopCat.alexanderWhitneyDiagonal_naturality_assoc _ _ _).trans <|
    (congrArg (_ ≫ ·) ((tensorHom_comp_whiskerLeft _ _ _).trans ?_)).trans <|
    (Category.assoc _ _ _).symm.trans
      (singularChainComplexπ_rightAlexanderWhitneyDiagonal_assoc P u _).symm
  exact (congrArg (_ ⊗ₘ ·) (singularChainComplexπ_pair_naturality f S)).trans
    (whiskerLeft_comp_tensorHom _ _ _).symm

section Braiding

variable [BraidedCategory C]
  [∀ (X : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft X)]
  [∀ (X : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight X)]

/-- **The two relative Alexander–Whitney diagonals agree up to the interchange of factors**: for a
pair `(X, A)`, the right relative diagonal `C(X, A; T) ⟶ C(X; R) ⊗ C(X, A; S)` of
`u : T ⟶ R ⊗ S` followed by the Koszul braiding is chain homotopic to the relative diagonal
`C(X, A; T) ⟶ C(X, A; S) ⊗ C(X; R)` of `u ≫ (β_ R S).hom`. The homotopy is the descent of the
homotopy `TopCat.alexanderWhitneyDiagonalKoszulBraidingHomotopy` of `X`, which by naturality
carries the chains of `A` into the chains of `A × A`. -/
def rightAlexanderWhitneyDiagonalKoszulBraidingHomotopy (P : TopPair.{w}) (u : T ⟶ R ⊗ S) :
    _root_.Homotopy (P.rightAlexanderWhitneyDiagonal u ≫ TauCeti.NatChainComplex.koszulBraidingHom
        ((TopCat.toSSet.obj P.fst).chainComplex R) (P.singularChainComplex S))
      (P.alexanderWhitneyDiagonal (u ≫ (β_ R S).hom)) :=
  -- The chains of `A` go to `C(A; S) ⊗ C(A; R)`, which the quotient map on the first factor kills.
  have hA : (SSet.chainComplexMap (TopCat.toSSet.map P.map) S ⊗ₘ
      SSet.chainComplexMap (TopCat.toSSet.map P.map) R) ≫
        (P.singularChainComplexπ S ▷ (TopCat.toSSet.obj P.fst).chainComplex R) = 0 :=
    (tensorHom_comp_whiskerRight _ _ _).trans <|
      (congrArg (· ⊗ₘ _) (chainComplexMap_comp_singularChainComplexπ P S)).trans
        (HomologicalComplex.zero_tensorHom _)
  have hκ : ((TopCat.toSSet.obj P.fst).chainComplex R ◁ P.singularChainComplexπ S) ≫
      TauCeti.NatChainComplex.koszulBraidingHom ((TopCat.toSSet.obj P.fst).chainComplex R)
        (P.singularChainComplex S) =
      TauCeti.NatChainComplex.koszulBraidingHom ((TopCat.toSSet.obj P.fst).chainComplex R)
          ((TopCat.toSSet.obj P.fst).chainComplex S) ≫
        (P.singularChainComplexπ S ▷ (TopCat.toSSet.obj P.fst).chainComplex R) :=
    TauCeti.NatChainComplex.koszulBraidingHom_naturality _ _ (𝟙 _) (P.singularChainComplexπ S)
  _root_.Homotopy.descCokernel (TopCat.alexanderWhitneyDiagonalKoszulBraidingHomotopy P.fst u)
    (SSet.chainComplexMap (TopCat.toSSet.map P.map) T) (P.singularChainComplexπ T)
    (P.singularChainComplexπ S ▷ (TopCat.toSSet.obj P.fst).chainComplex R)
    (fun n ↦ (toSSetPair.obj P).chainComplex_condition_f T n)
    (fun n ↦ (toSSetPair.obj P).isColimitCokernelCoforkChainComplexX T n)
    (fun i j ↦ (TopCat.alexanderWhitneyDiagonalKoszulBraidingHomotopy_hom_naturality_assoc
      P.map u i j _).trans <| (congrArg (_ ≫ ·) <| (HomologicalComplex.comp_f _ _ j).symm.trans <|
        (congrArg (fun φ ↦ φ.f j) hA).trans (HomologicalComplex.zero_f _ _ j)).trans comp_zero)
    ((singularChainComplexπ_rightAlexanderWhitneyDiagonal_assoc P u _).trans <|
      (Category.assoc _ _ _).trans <|
        (congrArg (P.fst.alexanderWhitneyDiagonal u ≫ ·) hκ).trans (Category.assoc _ _ _).symm)
    (singularChainComplexπ_alexanderWhitneyDiagonal P _)

end Braiding

end TopPair

namespace TopCat

variable {X Y : TopCat.{w}}

/-- The Alexander–Whitney diagonal of `X`, followed by the tensor product of two chain maps one of
which vanishes on the singular chains of `W`, vanishes on the singular chains of `W`. -/
private lemma chainComplexMap_comp_alexanderWhitneyDiagonal_comp_tensorHom_eq_zero (W : Set X)
    (u : T ⟶ R ⊗ S) {K₁ K₂ : ChainComplex C ℕ} (g₁ : (toSSet.obj X).chainComplex R ⟶ K₁)
    (g₂ : (toSSet.obj X).chainComplex S ⟶ K₂)
    (h : SSet.chainComplexMap (toSSet.map (ofHom (ContinuousMap.subtypeVal W))) R ≫ g₁ = 0 ∨
      SSet.chainComplexMap (toSSet.map (ofHom (ContinuousMap.subtypeVal W))) S ≫ g₂ = 0) :
    SSet.chainComplexMap (toSSet.map (ofHom (ContinuousMap.subtypeVal W))) T ≫
      X.alexanderWhitneyDiagonal u ≫ (g₁ ⊗ₘ g₂) = 0 := by
  rw [alexanderWhitneyDiagonal_naturality_assoc, tensorHom_comp_tensorHom]
  rcases h with h | h
  · rw [h]
    exact (congrArg _ (HomologicalComplex.mapBifunctorMap_zero_left _ _ _ _ _)).trans comp_zero
  · rw [h]
    exact (congrArg _ (HomologicalComplex.mapBifunctorMap_zero_right _ _ _ _ _)).trans comp_zero

/-- The Alexander–Whitney diagonal of `X`, followed by the quotient maps to the relative chains of
`(X, U)` and of `(X, V)` on the two factors, vanishes on the chains of the singular simplices lying
in `U` or in `V`. -/
private lemma chainComplexMap_comp_alexanderWhitneyDiagonal_comp_tensorHom (U V : Set X)
    (u : T ⟶ R ⊗ S) :
    SSet.chainComplexMap (X.smallSingularSubcomplex ![U, V]).ι T ≫ X.alexanderWhitneyDiagonal u ≫
      ((TopPair.ofSubset U).singularChainComplexπ R ⊗ₘ
        (TopPair.ofSubset V).singularChainComplexπ S) = 0 :=
  chainComplexMap_smallSingularSubcomplex_ι_comp_eq_zero ![U, V] _ <| Fin.forall_fin_two.2
    ⟨chainComplexMap_comp_alexanderWhitneyDiagonal_comp_tensorHom_eq_zero U u _ _
      (.inl (TopPair.chainComplexMap_comp_singularChainComplexπ (TopPair.ofSubset U) R)),
    chainComplexMap_comp_alexanderWhitneyDiagonal_comp_tensorHom_eq_zero V u _ _
      (.inr (TopPair.chainComplexMap_comp_singularChainComplexπ (TopPair.ofSubset V) S))⟩

/-- **The relative Alexander–Whitney diagonal** `C(X; U + V; T) ⟶ C(X, U; R) ⊗ C(X, V; S)` for
subsets `U` and `V` of `X`, where `C(X; U + V)` is the quotient of the singular chains of `X` by the
chains of the singular simplices lying in `U` or in `V`: the Alexander–Whitney diagonal of `X`
followed by the quotient maps on both factors, which vanishes on those chains and so descends. -/
def relativeAlexanderWhitneyDiagonal (U V : Set X) (u : T ⟶ R ⊗ S) :
    (X.smallSingularSubcomplex ![U, V]).pair.chainComplex T ⟶
      (TopPair.ofSubset U).singularChainComplex R ⊗ (TopPair.ofSubset V).singularChainComplex S :=
  (CokernelCofork.IsColimit.desc'
    ((X.smallSingularSubcomplex ![U, V]).pair.isColimitCokernelCoforkChainComplex T)
    (X.alexanderWhitneyDiagonal u ≫
      ((TopPair.ofSubset U).singularChainComplexπ R ⊗ₘ
        (TopPair.ofSubset V).singularChainComplexπ S))
    (chainComplexMap_comp_alexanderWhitneyDiagonal_comp_tensorHom U V u)).1

/-- The relative Alexander–Whitney diagonal is the descent of the Alexander–Whitney diagonal of
`X`, followed by the quotient maps on both factors. -/
@[reassoc (attr := simp)]
lemma chainComplexπ_relativeAlexanderWhitneyDiagonal (U V : Set X) (u : T ⟶ R ⊗ S) :
    (X.smallSingularSubcomplex ![U, V]).pair.chainComplexπ T ≫
        relativeAlexanderWhitneyDiagonal U V u =
      X.alexanderWhitneyDiagonal u ≫
        ((TopPair.ofSubset U).singularChainComplexπ R ⊗ₘ
          (TopPair.ofSubset V).singularChainComplexπ S) :=
  (CokernelCofork.IsColimit.desc'
    ((X.smallSingularSubcomplex ![U, V]).pair.isColimitCokernelCoforkChainComplex T) _
    (chainComplexMap_comp_alexanderWhitneyDiagonal_comp_tensorHom U V u)).2

/-- The relative Alexander–Whitney diagonal is natural in maps `f : X ⟶ Y` carrying `U` into `U'`
and `V` into `V'`. -/
@[reassoc]
lemma relativeAlexanderWhitneyDiagonal_naturality {U V : Set X} {U' V' : Set Y} (f : X ⟶ Y)
    (hfU : Set.MapsTo f U U') (hfV : Set.MapsTo f V V') (u : T ⟶ R ⊗ S) :
    SSetPair.chainComplexMap (smallSingularSubcomplexPairMap f hfU hfV) T ≫
        relativeAlexanderWhitneyDiagonal U' V' u =
      relativeAlexanderWhitneyDiagonal U V u ≫
        (TopPair.singularChainComplexMap (TopPair.ofSubsetMap f hfU) R ⊗ₘ
          TopPair.singularChainComplexMap (TopPair.ofSubsetMap f hfV) S) := by
  rw [← cancel_epi ((X.smallSingularSubcomplex ![U, V]).pair.chainComplexπ T),
    ← SSetPair.chainComplexπ_naturality_assoc, chainComplexπ_relativeAlexanderWhitneyDiagonal,
    chainComplexπ_relativeAlexanderWhitneyDiagonal_assoc, smallSingularSubcomplexPairMap_right]
  have hU := TopPair.singularChainComplexπ_pair_naturality (TopPair.ofSubsetMap f hfU) R
  have hV := TopPair.singularChainComplexπ_pair_naturality (TopPair.ofSubsetMap f hfV) S
  rw [TopPair.ofSubsetMap_fst] at hU hV
  -- Term-mode steps: `rw` cannot match here, since the ambient chains appear both as
  -- `(toSSetPair.obj P).right.chainComplex R` and as `(toSSet.obj X).chainComplex R`.
  refine (alexanderWhitneyDiagonal_naturality_assoc f u _).trans <|
    (congrArg (_ ≫ ·) ((tensorHom_comp_tensorHom
      (SSet.chainComplexMap (toSSet.map f) R) (SSet.chainComplexMap (toSSet.map f) S)
      ((TopPair.ofSubset U').singularChainComplexπ R)
      ((TopPair.ofSubset V').singularChainComplexπ S)).trans ?_)).trans
    (Category.assoc _ _ _).symm
  exact (congrArg₂ (· ⊗ₘ ·) hU hV).trans
    (tensorHom_comp_tensorHom _ _ _ _).symm

section RelativeAlexanderWhitney

open CartesianMonoidalCategory AlgebraicTopology

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

/-- Definitional unfolding of `TopCat.relativeAlexanderWhitney`. -/
lemma relativeAlexanderWhitney_def (X Y : TopCat.{w}) (A : Set X) (B : Set Y) (R S : C) :
    relativeAlexanderWhitney X Y A B R S =
      relativeAlexanderWhitneyDiagonal (fst X Y ⁻¹' A) (snd X Y ⁻¹' B) (𝟙 (R ⊗ S)) ≫
        (TopPair.singularChainComplexMap
            (TopPair.ofSubsetMap (fst X Y) (Set.mapsTo_preimage _ _)) R ⊗ₘ
          TopPair.singularChainComplexMap
            (TopPair.ofSubsetMap (snd X Y) (Set.mapsTo_preimage _ _)) S) :=
  (rfl)

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
    (tensorHom_comp_tensorHom _ _ _ _).trans
      ((congrArg₂ (· ⊗ₘ ·) hA.symm hB.symm).trans (tensorHom_comp_tensorHom _ _ _ _).symm)
  exact (chainComplexπ_relativeAlexanderWhitneyDiagonal_assoc
      (fst X Y ⁻¹' A) (snd X Y ⁻¹' B) (𝟙 (R ⊗ S)) _).trans <|
    (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·) htensor).trans <|
    (Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ _) (alexanderWhitney_eq_alexanderWhitneyDiagonal_comp X Y R S).symm)

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
  rw [← cancel_epi
    (((X ⊗ Y).smallSingularSubcomplex ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.chainComplexπ (R ⊗ S))]
  have hπ := SSetPair.chainComplexπ_naturality (R ⊗ S) (smallSingularSubcomplexPairMap (f ⊗ₘ g)
    (mapsTo_tensorHom_preimage_fst f g hf) (mapsTo_tensorHom_preimage_snd f g hg))
  have hA := TopPair.singularChainComplexπ_pair_naturality (TopPair.ofSubsetMap f hf) R
  have hB := TopPair.singularChainComplexπ_pair_naturality (TopPair.ofSubsetMap g hg) S
  rw [smallSingularSubcomplexPairMap_right] at hπ
  rw [TopPair.ofSubsetMap_fst] at hA hB
  exact (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ _) hπ.symm).trans <|
    (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·) (chainComplexπ_relativeAlexanderWhitney X' Y' A' B' R S)).trans <|
    (alexanderWhitney_naturality_assoc f g R S _).trans <|
    ((chainComplexπ_relativeAlexanderWhitney_assoc X Y A B R S _).trans <|
      (Category.assoc _ _ _).trans <|
      whisker_eq _ ((tensorHom_comp_tensorHom _ _ _ _).trans
        ((congrArg₂ (· ⊗ₘ ·) hA.symm hB.symm).trans (tensorHom_comp_tensorHom _ _ _ _).symm))).symm

/-- **Naturality of the relative Alexander–Whitney map** in both coefficient objects. -/
@[reassoc]
lemma relativeAlexanderWhitney_coefficient_naturality (X Y : TopCat.{w}) (A : Set X) (B : Set Y)
    {R S R' S' : C} (φ : R ⟶ R') (ψ : S ⟶ S') :
    ((SSetPair.chainComplexFunctor C).map (φ ⊗ₘ ψ)).app
        ((X ⊗ Y).smallSingularSubcomplex ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair ≫
        relativeAlexanderWhitney X Y A B R' S' =
      relativeAlexanderWhitney X Y A B R S ≫
        (((SSetPair.chainComplexFunctor C).map φ).app
            (TopPair.toSSetPair.obj (TopPair.ofSubset A)) ⊗ₘ
          ((SSetPair.chainComplexFunctor C).map ψ).app
            (TopPair.toSSetPair.obj (TopPair.ofSubset B))) := by
  rw [← cancel_epi
    (((X ⊗ Y).smallSingularSubcomplex ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.chainComplexπ (R ⊗ S))]
  have hπ := NatTrans.congr_app ((SSetPair.chainComplexFunctorπ C).naturality (φ ⊗ₘ ψ)).symm
    ((X ⊗ Y).smallSingularSubcomplex ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair
  have hA := NatTrans.congr_app ((SSetPair.chainComplexFunctorπ C).naturality φ).symm
    (TopPair.toSSetPair.obj (TopPair.ofSubset A))
  have hB := NatTrans.congr_app ((SSetPair.chainComplexFunctorπ C).naturality ψ).symm
    (TopPair.toSSetPair.obj (TopPair.ofSubset B))
  exact (Category.assoc _ _ _).symm.trans <|
    (eq_whisker hπ _).trans <|
    (Category.assoc _ _ _).trans <|
    (whisker_eq _ (chainComplexπ_relativeAlexanderWhitney X Y A B R' S')).trans <|
    (alexanderWhitney_coefficient_naturality_assoc X Y φ ψ _).trans <|
    ((chainComplexπ_relativeAlexanderWhitney_assoc X Y A B R S _).trans <|
      (Category.assoc _ _ _).trans <|
      whisker_eq _ ((tensorHom_comp_tensorHom _ _ _ _).trans
        ((congrArg₂ (· ⊗ₘ ·) hA hB).trans (tensorHom_comp_tensorHom _ _ _ _).symm))).symm

end RelativeAlexanderWhitney

end TopCat

namespace TauCeti

open AlgebraicTopology

/-- Changing chain coefficients along `f : T' ⟶ T` precomposes
`TopCat.relativeAlexanderWhitneyDiagonal` with the induced map on the small-chain quotient
complex. -/
@[reassoc]
lemma relativeAlexanderWhitneyDiagonal_comp {X : TopCat.{w}} {T' : C} (U V : Set X)
    (f : T' ⟶ T) (u : T ⟶ R ⊗ S) :
    TopCat.relativeAlexanderWhitneyDiagonal U V (f ≫ u) =
      ((SSetPair.chainComplexFunctor C).map f).app (X.smallSingularSubcomplex ![U, V]).pair ≫
        TopCat.relativeAlexanderWhitneyDiagonal U V u := by
  rw [← cancel_epi ((X.smallSingularSubcomplex ![U, V]).pair.chainComplexπ T')]
  have hπ := NatTrans.congr_app ((SSetPair.chainComplexFunctorπ C).naturality f).symm
    (X.smallSingularSubcomplex ![U, V]).pair
  have hD : X.alexanderWhitneyDiagonal (f ≫ u) =
      ((SSet.chainComplexFunctor C).map f).app (TopCat.toSSet.obj X) ≫
        X.alexanderWhitneyDiagonal u := by
    simp [alexanderWhitneyDiagonal_def]
  exact (TopCat.chainComplexπ_relativeAlexanderWhitneyDiagonal U V (f ≫ u)).trans <|
    (eq_whisker hD _).trans <|
    (Category.assoc _ _ _).trans <|
    (whisker_eq _ (TopCat.chainComplexπ_relativeAlexanderWhitneyDiagonal U V u).symm).trans <|
    (Category.assoc _ _ _).symm.trans <|
    (eq_whisker hπ.symm _).trans (Category.assoc _ _ _)

end TauCeti
