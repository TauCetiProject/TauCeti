/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.AlexanderWhitney.Basic
public import TauCeti.AlgebraicTopology.Singular.Relative

/-!
# The relative Alexander–Whitney diagonal

For a topological pair `(X, A)` and a coefficient morphism `u : T ⟶ R ⊗ S`, the Alexander–Whitney
diagonal `C(X; T) ⟶ C(X; R) ⊗ C(X; S)` of `X`, followed by the quotient map to relative chains on
the first factor, vanishes on the singular chains of `A`: a singular simplex `σ` of `A` is sent to
`∑_{p + q = n} σ|[0, …, p] ⊗ σ|[p, …, n]`, whose front faces lie in `A`. It therefore descends to
the relative Alexander–Whitney diagonal `C(X, A; T) ⟶ C(X, A; R) ⊗ C(X; S)`, along which relative
cap products are taken.

## Main definitions and results

* `TopPair.alexanderWhitneyDiagonal`: the relative Alexander–Whitney diagonal, characterized by
  `TopPair.singularChainComplexπ_alexanderWhitneyDiagonal`.
* `TopPair.alexanderWhitneyDiagonal_naturality`: it is natural in maps of pairs.

* `TopPair.alexanderWhitneyDiagonal_coefficient_naturality`: the coefficient square descends through
  the native quotient map to relative chains.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory

universe w v u

namespace TopPair

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

section Chain

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C] {R S T : C}

/-- The Alexander–Whitney diagonal of the ambient space of a pair, followed by the quotient map to
relative chains on the first factor, vanishes on the singular chains of the subspace. -/
private lemma chainComplexMap_comp_alexanderWhitneyDiagonal_comp_whiskerRight (P : TopPair.{w})
    (u : T ⟶ R ⊗ S) :
    SSet.chainComplexMap (toSSetPair.obj P).hom T ≫ P.fst.alexanderWhitneyDiagonal u ≫
      (P.singularChainComplexπ R ▷ (TopCat.toSSet.obj P.fst).chainComplex S) = 0 :=
  -- Term-mode steps: `rw` cannot match here, since the ambient chains appear both as
  -- `(toSSetPair.obj P).right.chainComplex R` and as `(TopCat.toSSet.obj P.fst).chainComplex R`.
  (TopCat.alexanderWhitneyDiagonal_naturality_assoc P.map u _).trans <|
    (congrArg (_ ≫ ·) <| (tensorHom_comp_whiskerRight _ _ _).trans <|
      (congrArg (· ⊗ₘ _) (chainComplexMap_comp_singularChainComplexπ P R)).trans
        (HomologicalComplex.zero_tensorHom _)).trans comp_zero

/-- **The relative Alexander–Whitney diagonal** `C(X, A; T) ⟶ C(X, A; R) ⊗ C(X; S)` of a pair
`(X, A)`: the Alexander–Whitney diagonal `C(X; T) ⟶ C(X; R) ⊗ C(X; S)` of `X` followed by the
quotient map to relative chains on the first factor, which vanishes on the chains of `A` and so
descends to relative chains. -/
def alexanderWhitneyDiagonal (P : TopPair.{w}) (u : T ⟶ R ⊗ S) :
    P.singularChainComplex T ⟶
      P.singularChainComplex R ⊗ (TopCat.toSSet.obj P.fst).chainComplex S :=
  (CokernelCofork.IsColimit.desc' (P.isColimitCokernelCoforkSingularChainComplex T)
    (P.fst.alexanderWhitneyDiagonal u ≫
      (P.singularChainComplexπ R ▷ (TopCat.toSSet.obj P.fst).chainComplex S))
    (chainComplexMap_comp_alexanderWhitneyDiagonal_comp_whiskerRight P u)).val

/-- The relative Alexander–Whitney diagonal of a pair `(X, A)` is the descent of the
Alexander–Whitney diagonal of `X`, followed by the quotient map on the first factor. -/
@[reassoc (attr := simp)]
lemma singularChainComplexπ_alexanderWhitneyDiagonal (P : TopPair.{w}) (u : T ⟶ R ⊗ S) :
    P.singularChainComplexπ T ≫ P.alexanderWhitneyDiagonal u =
      P.fst.alexanderWhitneyDiagonal u ≫
        (P.singularChainComplexπ R ▷ (TopCat.toSSet.obj P.fst).chainComplex S) :=
  (CokernelCofork.IsColimit.desc' (P.isColimitCokernelCoforkSingularChainComplex T) _
    (chainComplexMap_comp_alexanderWhitneyDiagonal_comp_whiskerRight P u)).property

/-- The relative Alexander–Whitney diagonal is natural in maps of pairs. -/
@[reassoc]
lemma alexanderWhitneyDiagonal_naturality {P P' : TopPair.{w}} (f : P ⟶ P') (u : T ⟶ R ⊗ S) :
    singularChainComplexMap f T ≫ P'.alexanderWhitneyDiagonal u =
      P.alexanderWhitneyDiagonal u ≫
        (singularChainComplexMap f R ⊗ₘ
          SSet.chainComplexMap (TopCat.toSSet.map (Hom.fst f)) S) := by
  rw [← cancel_epi (P.singularChainComplexπ T)]
  -- Term-mode steps, for the same reason as in
  -- `chainComplexMap_comp_alexanderWhitneyDiagonal_comp_whiskerRight`.
  refine (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ P'.alexanderWhitneyDiagonal u)
      (singularChainComplexπ_pair_naturality f T).symm).trans <|
    (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·) (singularChainComplexπ_alexanderWhitneyDiagonal P' u)).trans <|
    (TopCat.alexanderWhitneyDiagonal_naturality_assoc _ _ _).trans <|
    (congrArg (_ ≫ ·) ((tensorHom_comp_whiskerRight _ _ _).trans ?_)).trans <|
    (Category.assoc _ _ _).symm.trans
      (singularChainComplexπ_alexanderWhitneyDiagonal_assoc P u _).symm
  exact (congrArg (· ⊗ₘ _) (singularChainComplexπ_pair_naturality f R)).trans
    (whiskerRight_comp_tensorHom _ _ _).symm

section Coefficients

variable {R' S' T' : C}

/-- If `c ≫ u = u' ≫ (a ⊗ b)`, the relative Alexander–Whitney diagonals commute with the
chain coefficient maps of `a`, `b` and `c`. -/
theorem alexanderWhitneyDiagonal_coefficient_naturality (P : TopPair.{w})
    (u : T ⟶ R ⊗ S) (u' : T' ⟶ R' ⊗ S')
    (a : R' ⟶ R) (b : S' ⟶ S) (c : T' ⟶ T)
    (hu : c ≫ u = u' ≫ (a ⊗ₘ b)) :
    ((SSetPair.chainComplexFunctor C).map c).app (toSSetPair.obj P) ≫
        P.alexanderWhitneyDiagonal u =
      P.alexanderWhitneyDiagonal u' ≫ HomologicalComplex.tensorHom
        (((SSetPair.chainComplexFunctor C).map a).app (toSSetPair.obj P))
        (((SSet.chainComplexFunctor C).map b).app (TopCat.toSSet.obj P.fst)) := by
  have hc := P.singularChainComplexπ_coefficient_naturality c
  have hr := P.singularChainComplexπ_coefficient_naturality a
  rw [TauCeti.singularChainComplexFunctor_map_app] at hc hr
  have ht :
      ((((SSet.chainComplexFunctor C).map a).app (TopCat.toSSet.obj P.fst)) ⊗ₘ
          (((SSet.chainComplexFunctor C).map b).app (TopCat.toSSet.obj P.fst))) ≫
          (P.singularChainComplexπ R ▷ (TopCat.toSSet.obj P.fst).chainComplex S) =
        (P.singularChainComplexπ R' ▷ (TopCat.toSSet.obj P.fst).chainComplex S') ≫
          ((((SSetPair.chainComplexFunctor C).map a).app (toSSetPair.obj P)) ⊗ₘ
            (((SSet.chainComplexFunctor C).map b).app (TopCat.toSSet.obj P.fst))) := by
    have hcoeff := congrArg (· ⊗ₘ (((SSet.chainComplexFunctor C).map b).app
      (TopCat.toSSet.obj P.fst))) hr
    have hwhisker := whiskerRight_comp_tensorHom (P.singularChainComplexπ R')
      (((SSetPair.chainComplexFunctor C).map a).app (toSSetPair.obj P))
      (((SSet.chainComplexFunctor C).map b).app (TopCat.toSSet.obj P.fst))
    exact (tensorHom_comp_whiskerRight _ _ _).trans hcoeff |>.trans hwhisker.symm
  -- Native chain aliases obstruct rw/reassoc matching; compose typed associativity equations.
  apply (cancel_epi (P.singularChainComplexπ T')).mp
  calc
    _ = (((SSet.chainComplexFunctor C).map c).app (TopCat.toSSet.obj P.fst)) ≫
        P.singularChainComplexπ T ≫ P.alexanderWhitneyDiagonal u := by
        have hmap := (hc.symm =≫ P.alexanderWhitneyDiagonal u).trans (Category.assoc _ _ _)
        exact (Category.assoc _ _ _).symm.trans hmap
    _ = (((SSet.chainComplexFunctor C).map c).app (TopCat.toSSet.obj P.fst)) ≫
        P.fst.alexanderWhitneyDiagonal u ≫
          (P.singularChainComplexπ R ▷ (TopCat.toSSet.obj P.fst).chainComplex S) :=
      congrArg (_ ≫ ·) (singularChainComplexπ_alexanderWhitneyDiagonal P u)
    _ = P.fst.alexanderWhitneyDiagonal u' ≫
        ((((SSet.chainComplexFunctor C).map a).app (TopCat.toSSet.obj P.fst)) ⊗ₘ
          (((SSet.chainComplexFunctor C).map b).app (TopCat.toSSet.obj P.fst))) ≫
          (P.singularChainComplexπ R ▷ (TopCat.toSSet.obj P.fst).chainComplex S) := by
        have hmap := (TopCat.alexanderWhitneyDiagonal_coefficient_naturality
          P.fst u u' a b c hu =≫
            (P.singularChainComplexπ R ▷ (TopCat.toSSet.obj P.fst).chainComplex S)).trans
              (Category.assoc _ _ _)
        exact (Category.assoc _ _ _).symm.trans hmap
    _ = P.fst.alexanderWhitneyDiagonal u' ≫
        (P.singularChainComplexπ R' ▷ (TopCat.toSSet.obj P.fst).chainComplex S') ≫
          ((((SSetPair.chainComplexFunctor C).map a).app (toSSetPair.obj P)) ⊗ₘ
            (((SSet.chainComplexFunctor C).map b).app (TopCat.toSSet.obj P.fst))) :=
      congrArg (_ ≫ ·) ht
    _ = _ := by
      have hmap := ((singularChainComplexπ_alexanderWhitneyDiagonal P u').symm =≫
        (HomologicalComplex.tensorHom
          (((SSetPair.chainComplexFunctor C).map a).app (toSSetPair.obj P))
          (((SSet.chainComplexFunctor C).map b).app (TopCat.toSSet.obj P.fst)))).trans
            (Category.assoc _ _ _)
      exact (Category.assoc _ _ _).symm.trans hmap

end Coefficients

end Chain

end TopPair
