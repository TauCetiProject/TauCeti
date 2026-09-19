/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.HomotopyInvariance
public import TauCeti.Algebra.Homology.Homotopy
public import TauCeti.AlgebraicTopology.SimplicialObject.ChainHomotopy
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Relative
public import TauCeti.AlgebraicTopology.SimplicialSet.Homotopy

/-!
# Homotopy invariance of relative simplicial homology

A homotopy between morphisms of a pair of simplicial sets, that is, an `SSetPair.Homotopy`,
induces a chain homotopy between the maps of relative chain complexes, so that homotopic
morphisms of pairs induce the same map on relative simplicial homology, and morphisms of pairs
that are inverse to each other up to homotopy induce isomorphisms.

The relative chain complex is the degreewise cokernel of the inclusion of the chains of the
subcomplex, and the chain homotopy is obtained from `Homotopy.descCokernel`.  The input is the
compatibility of the chain homotopies of Mathlib's absolute homotopy invariance
(`Mathlib/AlgebraicTopology/SimplicialSet/Homology/HomotopyInvariance.lean`, F. Odermatt,
J. Riou), which comes from the commutative square of simplicial homotopies.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits MonoidalCategory

open scoped Simplicial

universe w v u

namespace SSet.Homotopy

variable {X Y X' Y' : SSet.{w}} {f g : X ⟶ Y} {f' g' : X' ⟶ Y'} {u : X ⟶ X'} {v : Y ⟶ Y'}
  {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]

/-- The chain homotopies induced by simplicial homotopies which fit into a commutative square are
compatible with the chain maps induced by that square. -/
lemma chainComplexMap_hom_comm (H : SSet.Homotopy f g) (H' : SSet.Homotopy f' g')
    (hu : u ▷ Δ[1] ≫ H'.h = H.h ≫ v) (R : C) (p q : ℕ) :
    (SSet.chainComplexMap u R).f p ≫ (H'.chainComplexMap R).hom p q =
      (H.chainComplexMap R).hom p q ≫ (SSet.chainComplexMap v R).f q := by
  dsimp only [SSet.Homotopy.chainComplexMap, SimplicialObject.Homotopy.sSetChainComplexMap]
  exact SimplicialObject.Homotopy.toChainHomotopy_hom_comm _ _
    (((SimplicialObject.whiskering _ _).obj (sigmaConst.obj R)).map u)
    (((SimplicialObject.whiskering _ _).obj (sigmaConst.obj R)).map v)
    (fun n i ↦ by
      simp only [SimplicialObject.Homotopy.whiskerRight_h, Functor.whiskeringRight_obj_map,
        Functor.whiskerRight_app, ← Functor.map_comp,
        H.toSimplicialObjectHomotopy_h_comm H' hu n i]) p q

end SSet.Homotopy

namespace SSetPair.Homotopy

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
  {P P' : SSetPair.{w}} {f g : P ⟶ P'} (H : Homotopy f g) (R : C)

/-- The chain homotopy on the total complexes carries the chains of the subcomplex into the
kernel of the quotient map onto relative chains. -/
lemma chainComplexMap_condition (i j : ℕ) :
    (SSet.chainComplexMap P.hom R).f i ≫ (H.right.chainComplexMap R).hom i j ≫
      (P'.chainComplexπ R).f j = 0 := by
  rw [← Category.assoc, H.left.chainComplexMap_hom_comm H.right H.w R i j, Category.assoc,
    P'.chainComplex_condition_f, comp_zero]

/-- A homotopy of morphisms of pairs of simplicial sets induces a chain homotopy between the
induced morphisms of relative chain complexes. -/
@[no_expose]
def chainComplexMap :
    _root_.Homotopy (SSetPair.chainComplexMap f R) (SSetPair.chainComplexMap g R) :=
  _root_.Homotopy.descCokernel (H.right.chainComplexMap R)
    (SSet.chainComplexMap P.hom R) (P.chainComplexπ R)
    (P'.chainComplexπ R)
    (fun n ↦ P.chainComplex_condition_f R n)
    (fun n ↦ P.isColimitCokernelCoforkChainComplexX R n)
    (H.chainComplexMap_condition R)
    (((chainComplexFunctorπ C).app R).naturality f).symm
    (((chainComplexFunctorπ C).app R).naturality g).symm

@[reassoc (attr := simp)]
lemma chainComplexMap_hom (p q : ℕ) :
    (P.chainComplexπ R).f p ≫ (H.chainComplexMap R).hom p q =
      (H.right.chainComplexMap R).hom p q ≫ (P'.chainComplexπ R).f q :=
  _root_.Homotopy.π_descCokernel_hom (H.right.chainComplexMap R)
    (SSet.chainComplexMap P.hom R) (P.chainComplexπ R)
    (P'.chainComplexπ R) (fun n ↦ P.chainComplex_condition_f R n)
    (fun n ↦ P.isColimitCokernelCoforkChainComplexX R n)
    (H.chainComplexMap_condition R)
    (((chainComplexFunctorπ C).app R).naturality f).symm
    (((chainComplexFunctorπ C).app R).naturality g).symm p q

include H in
/-- Homotopic morphisms of pairs of simplicial sets induce the same morphism on relative
simplicial homology. -/
lemma congr_homologyMap [CategoryWithHomology C] (n : ℕ) :
    SSetPair.homologyMap f R n = SSetPair.homologyMap g R n :=
  (H.chainComplexMap R).homologyMap_eq n

end SSetPair.Homotopy

namespace SSetPair

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
  [CategoryWithHomology C] {P P' : SSetPair.{w}}

/-- Morphisms of pairs of simplicial sets which are inverse to each other up to homotopy induce
isomorphisms on relative simplicial homology. -/
lemma isIso_homologyMap (f : P ⟶ P') (f' : P' ⟶ P) (H : Homotopy (f ≫ f') (𝟙 P))
    (H' : Homotopy (f' ≫ f) (𝟙 P')) (R : C) (n : ℕ) :
    IsIso (SSetPair.homologyMap f R n) := by
  refine ⟨SSetPair.homologyMap f' R n, ?_, ?_⟩
  · rw [← SSetPair.homologyMap_comp, H.congr_homologyMap R n, SSetPair.homologyMap_id]
  · rw [← SSetPair.homologyMap_comp, H'.congr_homologyMap R n, SSetPair.homologyMap_id]

end SSetPair
