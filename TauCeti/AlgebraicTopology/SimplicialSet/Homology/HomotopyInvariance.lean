/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.HomotopyInvariance
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Relative
public import TauCeti.Algebra.Homology.Homotopy
public import TauCeti.AlgebraicTopology.SimplicialObject.ChainHomotopy

/-!
# Homotopy invariance of relative simplicial homology

A homotopy between maps of a pair of simplicial sets consists of a homotopy on the subcomplex
and a homotopy on the total complex which agree on the subcomplex, that is, `SSetPair.Homotopy`.
This file shows that such a homotopy induces a chain homotopy between the maps of relative chain
complexes, so that homotopic maps of pairs induce the same map on relative simplicial homology.

The relative chain complex is the degreewise cokernel of the inclusion of the chains of the
subcomplex, and the chain homotopy is obtained from `Homotopy.descCokernel`.  The input is the
compatibility of the chain homotopies of Mathlib's absolute homotopy invariance, which comes from
the commutative square of simplicial homotopies.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits MonoidalCategory Opposite

open scoped Simplicial

universe w v u

namespace SSet.Homotopy

variable {X Y X' Y' : SSet.{w}} {f g : X ⟶ Y} {f' g' : X' ⟶ Y'} {u : X ⟶ X'} {v : Y ⟶ Y'}

/-- Simplicial homotopies which fit into a commutative square induce compatible families of
morphisms `Xₙ ⟶ Y'ₙ₊₁`. -/
lemma toSimplicialObjectHomotopy_h_comm (H : SSet.Homotopy f g) (H' : SSet.Homotopy f' g')
    (hu : u ▷ Δ[1] ≫ H'.h = H.h ≫ v) (n : ℕ) (i : Fin (n + 1)) :
    u.app (op ⦋n⦌) ≫ H'.toSimplicialObjectHomotopy.h i =
      H.toSimplicialObjectHomotopy.h i ≫ v.app (op ⦋n + 1⦌) := by
  have key : ∀ x : X _⦋n⦌, yonedaEquiv.symm (u.app (op ⦋n⦌) x) ▷ Δ[1] ≫ H'.h =
      (yonedaEquiv.symm x ▷ Δ[1] ≫ H.h) ≫ v := fun x ↦ by
    rw [← yonedaEquiv_symm_comp, comp_whiskerRight, Category.assoc, hu, Category.assoc]
  ext x
  exact congrArg (fun φ ↦ φ.app (op ⦋n + 1⦌) (prodStdSimplex.nonDegenerateEquiv₁ i).1) (key x)

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]

/-- The chain homotopies induced by simplicial homotopies which fit into a commutative square are
compatible with the chain maps induced by that square. -/
lemma chainComplexMap_hom_comm (H : SSet.Homotopy f g) (H' : SSet.Homotopy f' g')
    (hu : u ▷ Δ[1] ≫ H'.h = H.h ≫ v) (R : C) (p q : ℕ) :
    (SSet.chainComplexMap u R).f p ≫ (H'.chainComplexMap R).hom p q =
      (H.chainComplexMap R).hom p q ≫ (SSet.chainComplexMap v R).f q :=
  SimplicialObject.Homotopy.toChainHomotopy_hom_comm _ _
    (((SimplicialObject.whiskering _ _).obj (sigmaConst.obj R)).map u)
    (((SimplicialObject.whiskering _ _).obj (sigmaConst.obj R)).map v)
    (fun n i ↦ by
      simp only [SimplicialObject.Homotopy.whiskerRight_h, Functor.whiskeringRight_obj_map,
        Functor.whiskerRight_app, ← Functor.map_comp,
        H.toSimplicialObjectHomotopy_h_comm H' hu n i]) p q

end SSet.Homotopy

namespace SSetPair

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]

/-- The quotient map onto the relative chain complex is natural in the pair. -/
@[reassoc]
lemma chainComplexπ_naturality {P P' : SSetPair.{w}} (f : P ⟶ P') (R : C) :
    P.chainComplexπ R ≫ SSetPair.chainComplexMap f R =
      SSet.chainComplexMap f.right R ≫ P'.chainComplexπ R :=
  (((chainComplexFunctorπ C).app R).naturality f).symm

/-- A homotopy between morphisms of pairs of simplicial sets consists of a homotopy on the
subcomplexes and a homotopy on the total complexes which agree on the subcomplexes. -/
@[ext]
structure Homotopy {P P' : SSetPair.{w}} (f g : P ⟶ P') where
  /-- The homotopy on the subcomplexes. -/
  left : SSet.Homotopy f.left g.left
  /-- The homotopy on the total complexes. -/
  right : SSet.Homotopy f.right g.right
  /-- The two homotopies agree on the subcomplexes. -/
  w : P.hom ▷ Δ[1] ≫ right.h = left.h ≫ P'.hom

namespace Homotopy

variable {P P' : SSetPair.{w}} {f g : P ⟶ P'} (H : Homotopy f g) (R : C)

/-- A homotopy of morphisms of pairs of simplicial sets induces a chain homotopy between the
induced morphisms of relative chain complexes. -/
def chainComplexMap :
    _root_.Homotopy (SSetPair.chainComplexMap f R) (SSetPair.chainComplexMap g R) :=
  _root_.Homotopy.descCokernel (SSet.chainComplexMap P.hom R) (P.chainComplexπ R)
    (SSet.chainComplexMap P'.hom R) (P'.chainComplexπ R)
    (fun n ↦ P.chainComplex_condition_f R n)
    (fun n ↦ P.isColimitCokernelCoforkChainComplexX R n)
    (fun n ↦ P'.chainComplex_condition_f R n)
    (H.right.chainComplexMap R) (H.left.chainComplexMap R).hom
    (fun _ _ ↦ H.left.chainComplexMap_hom_comm H.right H.w R _ _)
    (chainComplexπ_naturality f R) (chainComplexπ_naturality g R)

include H in
/-- Homotopic morphisms of pairs of simplicial sets induce the same morphism on relative
simplicial homology. -/
lemma congr_homologyMap [CategoryWithHomology C] (n : ℕ) :
    SSetPair.homologyMap f R n = SSetPair.homologyMap g R n :=
  (H.chainComplexMap R).homologyMap_eq n

end Homotopy

end SSetPair
