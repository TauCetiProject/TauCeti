/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.KoszulBraiding
public import TauCeti.AlgebraicTopology.Singular.AlexanderWhitney
public import TauCeti.CategoryTheory.Monoidal.Cartesian.Basic

/-!
# The singular Alexander–Whitney map and the interchange of factors

For spaces `X` and `Y`, the Alexander–Whitney map `C(X × Y; R ⊗ S) ⟶ C(X; R) ⊗ C(Y; S)` on
singular chains, followed by the Koszul braiding `x ⊗ y ↦ (-1)^(p * q) y ⊗ x`, is chain homotopic
to the map induced by the swap `X × Y ⟶ Y × X` and the coefficient braiding, followed by the
Alexander–Whitney map of `Y × X` (`TopCat.alexanderWhitneyKoszulBraidingHomotopy`).  Precomposing
with the diagonal, the Alexander–Whitney diagonal of a coefficient morphism `u : T ⟶ R ⊗ S`
followed by the Koszul braiding is chain homotopic to the Alexander–Whitney diagonal of
`u ≫ (β_ R S).hom` (`TopCat.alexanderWhitneyDiagonalKoszulBraidingHomotopy`).  This is the
chain-level form of the graded commutativity of the cup product.

Both homotopies are transported from the simplicial statement
`SSet.alexanderWhitneyKoszulBraidingHomotopy` along the comparison map
`Sing (X × Y) ⟶ Sing X × Sing Y`, which commutes with the swaps
(`CategoryTheory.CartesianMonoidalCategory.map_braiding_hom_comp_prodComparison`).

## References

* A. Hatcher, *Algebraic Topology*, Section 3.2, Theorem 3.11.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

universe w v u

namespace TopCat

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C] [BraidedCategory C]
  [∀ (X : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft X)]
  [∀ (X : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight X)]

/-- **The singular Alexander–Whitney map commutes with the interchange of factors up to
homotopy**: the Alexander–Whitney map `C(X × Y; R ⊗ S) ⟶ C(X; R) ⊗ C(Y; S)` followed by the Koszul
braiding, `x ⊗ y ↦ (-1)^(p * q) y ⊗ x` in bidegree `(p, q)`, is chain homotopic to the coefficient
braiding `R ⊗ S ⟶ S ⊗ R` followed by the map induced by the swap `X × Y ⟶ Y × X` and the
Alexander–Whitney map of `Y × X`. -/
def alexanderWhitneyKoszulBraidingHomotopy (X Y : TopCat.{w}) (R S : C) :
    Homotopy (alexanderWhitney X Y R S ≫ TauCeti.NatChainComplex.koszulBraidingHom
        ((toSSet.obj X).chainComplex R) ((toSSet.obj Y).chainComplex S))
      (((SSet.chainComplexFunctor C).map (β_ R S).hom).app (toSSet.obj (X ⊗ Y)) ≫
        SSet.chainComplexMap (toSSet.map (β_ X Y).hom) (S ⊗ R) ≫ alexanderWhitney Y X S R) :=
  (Homotopy.ofEq (by rw [alexanderWhitney_def, Category.assoc])).trans <|
    ((SSet.alexanderWhitneyKoszulBraidingHomotopy (toSSet.obj X) (toSSet.obj Y) R S).compLeft
      (SSet.chainComplexMap (CartesianMonoidalCategory.prodComparison toSSet X Y)
        (R ⊗ S))).trans <|
      Homotopy.ofEq <| by
        rw [alexanderWhitney_def, ← NatTrans.naturality_assoc, ← Functor.map_comp_assoc,
          ← CartesianMonoidalCategory.map_braiding_hom_comp_prodComparison, Functor.map_comp_assoc,
          NatTrans.naturality_assoc, NatTrans.naturality_assoc]

variable {R S T : C}

/-- **The Alexander–Whitney diagonal commutes with the interchange of factors up to homotopy**:
the Alexander–Whitney diagonal `C(X; T) ⟶ C(X; R) ⊗ C(X; S)` of `u : T ⟶ R ⊗ S` followed by the
Koszul braiding is chain homotopic to the Alexander–Whitney diagonal of `u ≫ (β_ R S).hom`. -/
def alexanderWhitneyDiagonalKoszulBraidingHomotopy (X : TopCat.{w}) (u : T ⟶ R ⊗ S) :
    Homotopy (X.alexanderWhitneyDiagonal u ≫ TauCeti.NatChainComplex.koszulBraidingHom
        ((toSSet.obj X).chainComplex R) ((toSSet.obj X).chainComplex S))
      (X.alexanderWhitneyDiagonal (u ≫ (β_ R S).hom)) :=
  (Homotopy.ofEq (by simp only [TauCeti.alexanderWhitneyDiagonal_def, Category.assoc])).trans <|
    ((alexanderWhitneyKoszulBraidingHomotopy X X R S).compLeft
      (((SSet.chainComplexFunctor C).map u).app _ ≫
        SSet.chainComplexMap (toSSet.map (lift (𝟙 X) (𝟙 X))) (R ⊗ S))).trans <|
      Homotopy.ofEq <| by
        rw [TauCeti.alexanderWhitneyDiagonal_def, Category.assoc, NatTrans.naturality_assoc,
          ← Functor.map_comp_assoc, ← Functor.map_comp, lift_braiding_hom, Functor.map_comp,
          NatTrans.comp_app,
          Category.assoc]

end TopCat
