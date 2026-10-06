/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cup
public import TauCeti.AlgebraicTopology.Singular.EilenbergZilber

/-!
# Cross products in singular cohomology

The external product sends classes on `X` and `Y` to a class on `X × Y`. It uses the
Alexander–Whitney map with a coefficient pairing `M ⊗ N ⟶ P`, and is natural in both spaces.
Pulling it back along the diagonal gives the cup product. Equivalently, the external product
is the cup product of the pullbacks along the two projections.

The Eilenberg–Zilber isomorphism identifies cohomology of the product with cohomology of
`Hom(C(X; R) ⊗ C(Y; S), P)`. Under this isomorphism the external product is represented by
the tensor product of cocycles. This comparison uses the shuffle–Alexander–Whitney chain
homotopy; it does not assert a Künneth decomposition of cohomology.

## References

* A. Hatcher, *Algebraic Topology*, Section 3.2, for cross products and the diagonal formula.
* S. Eilenberg and J. A. Zilber, *On products of complexes*, Amer. J. Math. 75 (1953).

The construction uses `TauCeti.ChainComplex.cup`, and the comparison uses
`TopCat.eilenbergZilberHomotopyEquiv` and `TauCeti.HomotopyEquiv.linearYonedaFunctorMap`.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory HomologicalComplex

universe w v u

namespace TauCeti

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
  [MonoidalCategory C] [MonoidalPreadditive C]
  (k : Type*) {R S M N P : C}

section CrossProduct

variable [CommRing k] [Linear k C] [MonoidalLinear k C]

/-- The bilinear external product in singular cohomology, induced by the Alexander–Whitney
map and the coefficient pairing `μ`. -/
def singularCross (X Y : TopCat.{w}) (μ : M ⊗ N ⟶ P) (p q n : ℕ) (h : p + q = n) :
    X.singularCohomology R k M p →ₗ[k] Y.singularCohomology S k N q →ₗ[k]
      (X ⊗ Y).singularCohomology (R ⊗ S) k P n :=
  ChainComplex.cup k (TopCat.alexanderWhitney X Y R S) μ p q n h

/-- The external product is the cohomology cup product along Alexander–Whitney. -/
lemma singularCross_def (X Y : TopCat.{w}) (μ : M ⊗ N ⟶ P)
    (p q n : ℕ) (h : p + q = n) :
    singularCross k X Y μ p q n h =
      ChainComplex.cup k (TopCat.alexanderWhitney X Y R S) μ p q n h :=
  (rfl)

/-- The external product of classes of cocycles is represented by their tensor cochain
precomposed with the Alexander–Whitney map. -/
@[simp]
lemma singularCross_homologyπ (X Y : TopCat.{w}) (μ : M ⊗ N ⟶ P)
    (p q n : ℕ) (h : p + q = n)
    (a : (X.singularCochainComplex R k M).cycles p)
    (b : (Y.singularCochainComplex S k N).cycles q) :
    singularCross k X Y μ p q n h ((X.singularCochainComplex R k M).homologyπ p a)
        ((Y.singularCochainComplex S k N).homologyπ q b) =
      ((X ⊗ Y).singularCochainComplex (R ⊗ S) k P).homologyπ n
        (ChainComplex.cupCycles k (TopCat.alexanderWhitney X Y R S) μ p q n h a b) :=
  ChainComplex.cup_homologyπ _ _ _ _ _ _ _ _

/-- External products commute with pullback along a product of continuous maps. -/
lemma singularCross_naturality {X Y X' Y' : TopCat.{w}} (f : X ⟶ X') (g : Y ⟶ Y')
    (μ : M ⊗ N ⟶ P) (p q n : ℕ) (h : p + q = n)
    (a : X'.singularCohomology R k M p) (b : Y'.singularCohomology S k N q) :
    singularCross k X Y μ p q n h (TopCat.singularCohomologyMap f p a)
        (TopCat.singularCohomologyMap g q b) =
      TopCat.singularCohomologyMap (f ⊗ₘ g) n (singularCross k X' Y' μ p q n h a b) :=
  ChainComplex.cup_naturality _ μ _ _ _ _ (TopCat.alexanderWhitney_naturality f g R S)
    p q n h a b

/-- Pulling the external product back along the diagonal gives the cup product. -/
lemma singularCross_diagonal (X : TopCat.{w}) (μ : M ⊗ N ⟶ P)
    (p q n : ℕ) (h : p + q = n)
    (a : X.singularCohomology R k M p) (b : X.singularCohomology S k N q) :
    TopCat.singularCohomologyMap (lift (𝟙 X) (𝟙 X)) n
        (singularCross k X X μ p q n h a b) =
      X.singularCup k (𝟙 (R ⊗ S)) μ p q n h a b := by
  simpa [singularCross_def, singularCup_def, alexanderWhitneyDiagonal_def] using
    (ChainComplex.cup_precomp (TopCat.alexanderWhitney X X R S) μ
      (SSet.chainComplexMap (TopCat.toSSet.map (lift (𝟙 X) (𝟙 X))) (R ⊗ S))
      p q n h a b).symm

/-- The external product is the cup product of pullbacks along the two projections. -/
lemma singularCross_eq_singularCup (X Y : TopCat.{w}) (μ : M ⊗ N ⟶ P)
    (p q n : ℕ) (h : p + q = n)
    (a : X.singularCohomology R k M p) (b : Y.singularCohomology S k N q) :
    singularCross k X Y μ p q n h a b =
      (X ⊗ Y).singularCup k (𝟙 (R ⊗ S)) μ p q n h
        (TopCat.singularCohomologyMap (fst X Y) p a)
        (TopCat.singularCohomologyMap (snd X Y) q b) := by
  have hdiag : lift (𝟙 (X ⊗ Y)) (𝟙 (X ⊗ Y)) ≫ (fst X Y ⊗ₘ snd X Y) = 𝟙 (X ⊗ Y) := by
    ext <;> simp
  have hD := TopCat.alexanderWhitney_naturality (fst X Y) (snd X Y) R S
  have hD' : TopCat.alexanderWhitney X Y R S =
      (X ⊗ Y).alexanderWhitneyDiagonal (𝟙 (R ⊗ S)) ≫
        HomologicalComplex.tensorHom
          (SSet.chainComplexMap (TopCat.toSSet.map (fst X Y)) R)
          (SSet.chainComplexMap (TopCat.toSSet.map (snd X Y)) S) := by
    rw [alexanderWhitneyDiagonal_def, (SSet.chainComplexFunctor C).map_id]
    simp only [NatTrans.id_app, Category.id_comp, Category.assoc]
    -- The singular-chain tensor notation is Mathlib's totalized tensor morphism.
    have hD'' : SSet.chainComplexMap (TopCat.toSSet.map (fst X Y ⊗ₘ snd X Y)) (R ⊗ S) ≫
        TopCat.alexanderWhitney X Y R S =
      TopCat.alexanderWhitney (X ⊗ Y) (X ⊗ Y) R S ≫
        HomologicalComplex.tensorHom
          (SSet.chainComplexMap (TopCat.toSSet.map (fst X Y)) R)
          (SSet.chainComplexMap (TopCat.toSSet.map (snd X Y)) S) := hD
    rw [← hD'']
    rw [← Category.assoc, ← ((SSet.chainComplexFunctor C).obj (R ⊗ S)).map_comp,
      ← TopCat.toSSet.map_comp, hdiag, TopCat.toSSet.map_id,
      ((SSet.chainComplexFunctor C).obj (R ⊗ S)).map_id, Category.id_comp]
  simpa [singularCross_def, singularCup_def] using
    (ChainComplex.cup_naturality (TopCat.alexanderWhitney X Y R S) μ
      ((X ⊗ Y).alexanderWhitneyDiagonal (𝟙 (R ⊗ S))) (𝟙 _) _ _
      (by simpa using hD') p q n h a b).symm

end CrossProduct

section EilenbergZilber

variable [Ring k] [Linear k C]
  [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft T)]
  [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight T)]

/-- The Eilenberg–Zilber isomorphism on cohomology with arbitrary target coefficients `P`.
Its forward map is pullback along the shuffle map, and its inverse is pullback along
Alexander–Whitney. -/
def singularEilenbergZilberCohomologyIso (X Y : TopCat.{w}) (R S P : C) (n : ℕ) :
    (X ⊗ Y).singularCohomology (R ⊗ S) k P n ≅
      (_root_.ChainComplex.linearYonedaObj
        (HomologicalComplex.tensorObj ((TopCat.toSSet.obj X).chainComplex R)
          ((TopCat.toSSet.obj Y).chainComplex S)) k P).homology n :=
  (HomotopyEquiv.linearYonedaFunctorMap k P
    (TopCat.eilenbergZilberHomotopyEquiv X Y R S).symm).toHomologyIso n

/-- The forward Eilenberg–Zilber comparison is induced by precomposition with the shuffle map. -/
@[simp]
lemma singularEilenbergZilberCohomologyIso_hom (X Y : TopCat.{w}) (R S P : C) (n : ℕ) :
    (singularEilenbergZilberCohomologyIso k X Y R S P n).hom =
      homologyMap
        (K := (X ⊗ Y).singularCochainComplex (R ⊗ S) k P)
        (L := _root_.ChainComplex.linearYonedaObj
          (HomologicalComplex.tensorObj ((TopCat.toSSet.obj X).chainComplex R)
            ((TopCat.toSSet.obj Y).chainComplex S)) k P)
        ((ChainComplex.linearYonedaFunctor k P).map (TopCat.shuffle X Y R S).op) n := by
  simp only [singularEilenbergZilberCohomologyIso, _root_.HomotopyEquiv.toHomologyIso,
    HomotopyEquiv.linearYonedaFunctorMap_hom, _root_.HomotopyEquiv.symm_hom,
    TopCat.eilenbergZilberHomotopyEquiv_inv]
  rfl

/-- The inverse Eilenberg–Zilber comparison is induced by precomposition with Alexander–Whitney. -/
@[simp]
lemma singularEilenbergZilberCohomologyIso_inv (X Y : TopCat.{w}) (R S P : C) (n : ℕ) :
    (singularEilenbergZilberCohomologyIso k X Y R S P n).inv =
      homologyMap
        (K := _root_.ChainComplex.linearYonedaObj
          (HomologicalComplex.tensorObj ((TopCat.toSSet.obj X).chainComplex R)
            ((TopCat.toSSet.obj Y).chainComplex S)) k P)
        (L := (X ⊗ Y).singularCochainComplex (R ⊗ S) k P)
        ((ChainComplex.linearYonedaFunctor k P).map
          (TopCat.alexanderWhitney X Y R S).op) n := by
  simp only [singularEilenbergZilberCohomologyIso, _root_.HomotopyEquiv.toHomologyIso,
    HomotopyEquiv.linearYonedaFunctorMap_inv, _root_.HomotopyEquiv.symm_inv,
    TopCat.eilenbergZilberHomotopyEquiv_hom]
  rfl

/-- The Eilenberg–Zilber comparison commutes with pullback along maps in both spaces. -/
@[reassoc]
lemma singularEilenbergZilberCohomologyIso_hom_naturality
    {X Y X' Y' : TopCat.{w}} (f : X ⟶ X') (g : Y ⟶ Y') (R S P : C) (n : ℕ) :
    TopCat.singularCohomologyMap (R := R ⊗ S) (k := k) (M := P) (f ⊗ₘ g) n ≫
        (singularEilenbergZilberCohomologyIso k X Y R S P n).hom =
      (singularEilenbergZilberCohomologyIso k X' Y' R S P n).hom ≫
        homologyMap
          (K := _root_.ChainComplex.linearYonedaObj
            (HomologicalComplex.tensorObj ((TopCat.toSSet.obj X').chainComplex R)
              ((TopCat.toSSet.obj Y').chainComplex S)) k P)
          (L := _root_.ChainComplex.linearYonedaObj
            (HomologicalComplex.tensorObj ((TopCat.toSSet.obj X).chainComplex R)
              ((TopCat.toSSet.obj Y).chainComplex S)) k P)
          ((ChainComplex.linearYonedaFunctor k P).map
            (HomologicalComplex.tensorHom
              (SSet.chainComplexMap (TopCat.toSSet.map f) R)
              (SSet.chainComplexMap (TopCat.toSSet.map g) S)).op) n := by
  let F := ChainComplex.linearYonedaFunctor k P ⋙
    HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.up ℕ) n
  have hF := congrArg F.map (congrArg Quiver.Hom.op (TopCat.shuffle_naturality f g R S))
  rw [op_comp, op_comp, F.map_comp, F.map_comp] at hF
  rw [singularEilenbergZilberCohomologyIso_hom, singularEilenbergZilberCohomologyIso_hom]
  exact hF.symm

/-- The inverse Eilenberg–Zilber comparison commutes with pullback in both spaces. -/
@[reassoc]
lemma singularEilenbergZilberCohomologyIso_inv_naturality
    {X Y X' Y' : TopCat.{w}} (f : X ⟶ X') (g : Y ⟶ Y') (R S P : C) (n : ℕ) :
    (singularEilenbergZilberCohomologyIso k X' Y' R S P n).inv ≫
        TopCat.singularCohomologyMap (R := R ⊗ S) (k := k) (M := P) (f ⊗ₘ g) n =
      homologyMap
          (K := _root_.ChainComplex.linearYonedaObj
            (HomologicalComplex.tensorObj ((TopCat.toSSet.obj X').chainComplex R)
              ((TopCat.toSSet.obj Y').chainComplex S)) k P)
          (L := _root_.ChainComplex.linearYonedaObj
            (HomologicalComplex.tensorObj ((TopCat.toSSet.obj X).chainComplex R)
              ((TopCat.toSSet.obj Y).chainComplex S)) k P)
          ((ChainComplex.linearYonedaFunctor k P).map
            (HomologicalComplex.tensorHom
              (SSet.chainComplexMap (TopCat.toSSet.map f) R)
              (SSet.chainComplexMap (TopCat.toSSet.map g) S)).op) n ≫
        (singularEilenbergZilberCohomologyIso k X Y R S P n).inv := by
  apply (cancel_mono (singularEilenbergZilberCohomologyIso k X Y R S P n).hom).1
  rw [Category.assoc, singularEilenbergZilberCohomologyIso_hom_naturality,
    Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end EilenbergZilber

section Comparison

variable [CommRing k] [Linear k C] [MonoidalLinear k C]
  [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft T)]
  [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight T)]

/-- Under Eilenberg–Zilber, the external product is the class of the tensor product of cocycles.
Here the cup product along the identity is the product on the tensor chain complex itself. -/
lemma singularEilenbergZilberCohomologyIso_hom_singularCross (X Y : TopCat.{w})
    (μ : M ⊗ N ⟶ P) (p q n : ℕ) (h : p + q = n)
    (a : X.singularCohomology R k M p) (b : Y.singularCohomology S k N q) :
    (singularEilenbergZilberCohomologyIso k X Y R S P n).hom
        (singularCross k X Y μ p q n h a b) =
      ChainComplex.cup k (𝟙 (HomologicalComplex.tensorObj ((TopCat.toSSet.obj X).chainComplex R)
        ((TopCat.toSSet.obj Y).chainComplex S))) μ p q n h a b := by
  rw [singularEilenbergZilberCohomologyIso_hom]
  exact (ChainComplex.cup_precomp (TopCat.alexanderWhitney X Y R S) μ
    (TopCat.shuffle X Y R S) p q n h a b).symm.trans
      (ChainComplex.cup_eq_of_homotopy _ μ
        (TopCat.shuffleAlexanderWhitneyHomotopy X Y R S) p q n h a b)

end Comparison

end TauCeti
