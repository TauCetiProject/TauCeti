/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Bifunctor.Basic
public import TauCeti.AlgebraicTopology.Singular.AlexanderWhitney.Basic
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
  action `Hᵖ(X) × H^q(X, A) ⟶ Hⁿ(X, A)` of absolute cohomology on relative cohomology.
* For subsets `U` and `V` of `X`, the diagonal followed by the quotient maps on both factors
  vanishes on the chains of `U` and on those of `V`, hence on the chains `C(U) + C(V)` of the
  singular simplices of `X` lying in `U` or in `V` (the subcomplex `X.smallSingularSubcomplex
  ![U, V]`).  It descends to `TopCat.relativeAlexanderWhitneyDiagonal :
  C(X; U + V; T) ⟶ C(X, U; R) ⊗ C(X, V; S)`, where `C(X; U + V)` is the quotient of `C(X)` by
  `C(U) + C(V)`.  When `U` and `V` are open in `U ∪ V`, the small-chain theorem identifies
  `C(X; U + V)` with `C(X, U ∪ V)` up to quasi-isomorphism, which gives the relative cup product
  `Hᵖ(X, U) × H^q(X, V) ⟶ Hⁿ(X, U ∪ V)`.

## Main definitions and results

* `TopPair.rightAlexanderWhitneyDiagonal`, characterized by
  `TopPair.singularChainComplexπ_rightAlexanderWhitneyDiagonal` and natural in maps of pairs
  (`TopPair.rightAlexanderWhitneyDiagonal_naturality`).
* `TopCat.relativeAlexanderWhitneyDiagonal`, characterized by
  `TopCat.chainComplexπ_relativeAlexanderWhitneyDiagonal` and natural in maps of spaces carrying
  `U` into `U'` and `V` into `V'` (`TopCat.relativeAlexanderWhitneyDiagonal_naturality`, along the
  maps of pairs `TopCat.smallSingularSubcomplexPairMap`).

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

end TopCat
