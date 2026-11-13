/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.KoszulBraiding
public import TauCeti.AlgebraicTopology.Singular.AlexanderWhitney.Basic
public import TauCeti.AlgebraicTopology.Singular.EilenbergZilber
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
chain-level form of the graded commutativity of the cup product.  Both homotopies are natural in
the spaces (`TopCat.alexanderWhitneyKoszulBraidingHomotopy_hom_naturality` and
`TopCat.alexanderWhitneyDiagonalKoszulBraidingHomotopy_hom_naturality`), so they descend to
relative chains.

Both homotopies are transported from the simplicial statement
`SSet.alexanderWhitneyKoszulBraidingHomotopy` along the comparison map
`Sing (X × Y) ⟶ Sing X × Sing Y`, which commutes with the swaps
(`CategoryTheory.Functor.map_braiding_hom_comp_prodComparison`).

Since the shuffle map is a homotopy inverse of the Alexander–Whitney map (the Eilenberg–Zilber
theorem), the Koszul braiding followed by the shuffle map of `Y × X` is chain homotopic to the
shuffle map of `X × Y` followed by the coefficient braiding and the swap
(`TopCat.koszulBraidingShuffleHomotopy`).  This is the chain-level form of the graded
commutativity of the homology cross product.

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
          ← toSSet.map_braiding_hom_comp_prodComparison, Functor.map_comp_assoc,
          NatTrans.naturality_assoc, NatTrans.naturality_assoc]

/-- The homotopy of `TopCat.alexanderWhitneyKoszulBraidingHomotopy` is natural in both spaces:
maps `f : X ⟶ X'` and `g : Y ⟶ Y'` intertwine it with the homotopy for `X'` and `Y'`, the chains of
the target being mapped by `g` and `f` in the interchanged order. -/
@[reassoc]
lemma alexanderWhitneyKoszulBraidingHomotopy_hom_naturality {X X' Y Y' : TopCat.{w}}
    (f : X ⟶ X') (g : Y ⟶ Y') (R S : C) (i j : ℕ) :
    (SSet.chainComplexMap (toSSet.map (f ⊗ₘ g)) (R ⊗ S)).f i ≫
        (alexanderWhitneyKoszulBraidingHomotopy X' Y' R S).hom i j =
      (alexanderWhitneyKoszulBraidingHomotopy X Y R S).hom i j ≫
        (SSet.chainComplexMap (toSSet.map g) S ⊗ₘ SSet.chainComplexMap (toSSet.map f) R).f j := by
  simp only [alexanderWhitneyKoszulBraidingHomotopy, Homotopy.trans_hom, Homotopy.ofEq_hom,
    Homotopy.compLeft_hom, Pi.zero_apply, zero_add, add_zero, Category.assoc]
  rw [SSet.chainComplexMap_f_comp_assoc, CartesianMonoidalCategory.prodComparison_natural,
    ← SSet.chainComplexMap_f_comp_assoc,
    SSet.alexanderWhitneyKoszulBraidingHomotopy_hom_naturality]

/-- **The shuffle map commutes with the interchange of factors up to homotopy**: the Koszul
braiding `C(X; R) ⊗ C(Y; S) ⟶ C(Y; S) ⊗ C(X; R)`, `x ⊗ y ↦ (-1)^(p * q) y ⊗ x` in bidegree
`(p, q)`, followed by the shuffle map of `Y × X`, is chain homotopic to the shuffle map of `X × Y`
followed by the maps induced by the coefficient braiding `R ⊗ S ⟶ S ⊗ R` and the swap
`X × Y ⟶ Y × X`. -/
def koszulBraidingShuffleHomotopy (X Y : TopCat.{w}) (R S : C) :
    Homotopy (TauCeti.NatChainComplex.koszulBraidingHom ((toSSet.obj X).chainComplex R)
        ((toSSet.obj Y).chainComplex S) ≫ shuffle Y X S R)
      (shuffle X Y R S ≫ ((SSet.chainComplexFunctor C).map (β_ R S).hom).app (toSSet.obj (X ⊗ Y)) ≫
        SSet.chainComplexMap (toSSet.map (β_ X Y).hom) (S ⊗ R)) := by
  -- the shuffle map is a homotopy inverse of the Alexander–Whitney map on both sides, and the
  -- Alexander–Whitney map commutes with the interchange up to homotopy
  refine ((shuffleAlexanderWhitneyHomotopy X Y R S).compRightId _).symm.trans ?_
  refine (Homotopy.ofEq ?_).trans ((((alexanderWhitneyKoszulBraidingHomotopy X Y R S).compLeft
    (shuffle X Y R S)).compRight (shuffle Y X S R)).trans ?_)
  · simp only [Category.assoc]
  refine (Homotopy.ofEq ?_).trans ((alexanderWhitneyShuffleHomotopy Y X S R).compLeftId _)
  simp only [Category.assoc]

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

/-- The homotopy of `TopCat.alexanderWhitneyDiagonalKoszulBraidingHomotopy` is natural in the
space: a map `f : X ⟶ Y` intertwines it with the homotopy for `Y`. -/
@[reassoc]
lemma alexanderWhitneyDiagonalKoszulBraidingHomotopy_hom_naturality {X Y : TopCat.{w}}
    (f : X ⟶ Y) (u : T ⟶ R ⊗ S) (i j : ℕ) :
    (SSet.chainComplexMap (toSSet.map f) T).f i ≫
        (alexanderWhitneyDiagonalKoszulBraidingHomotopy Y u).hom i j =
      (alexanderWhitneyDiagonalKoszulBraidingHomotopy X u).hom i j ≫
        (SSet.chainComplexMap (toSSet.map f) S ⊗ₘ SSet.chainComplexMap (toSSet.map f) R).f j := by
  simp only [alexanderWhitneyDiagonalKoszulBraidingHomotopy, Homotopy.trans_hom,
    Homotopy.ofEq_hom, Homotopy.compLeft_hom, Pi.zero_apply, zero_add, add_zero,
    HomologicalComplex.comp_f, Category.assoc]
  -- Naturality of the diagonal: `f ≫ Δ_Y = Δ_X ≫ (f ⊗ f)`.
  have hΔ : f ≫ lift (𝟙 Y) (𝟙 Y) = lift (𝟙 X) (𝟙 X) ≫ (f ⊗ₘ f) := by simp
  rw [SSet.chainComplexMap_f_chainComplexFunctor_map_app_f_assoc,
    SSet.chainComplexMap_f_comp_assoc, ← Functor.map_comp, hΔ, Functor.map_comp,
    ← SSet.chainComplexMap_f_comp_assoc, alexanderWhitneyKoszulBraidingHomotopy_hom_naturality]

end TopCat
