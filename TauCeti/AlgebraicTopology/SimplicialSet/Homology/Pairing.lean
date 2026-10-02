/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.MapHomologicalComplex
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Basic

/-!
# Coefficient pairings on simplicial chains

Let `C` be a preadditive monoidal category with `w`-small coproducts, and let `M` be an object of
`C` such that `M ⊗ -` preserves `w`-small coproducts (for instance, any object of a closed
monoidal category such as `ModuleCat k`).  The simplicial chains `Cₙ(X; S)` of a simplicial set
`X` are the coproduct of one copy of `S` for each `n`-simplex, so `M ⊗ Cₙ(X; S)` is the coproduct
of one copy of `M ⊗ S` for each `n`-simplex.  A pairing `μ : M ⊗ S ⟶ P` of coefficient objects
therefore induces, simplex by simplex, a chain map `X.chainComplexPairing μ` from the complex
`M ⊗ C(X; S)` to `C(X; P)`: it is the identification `M ⊗ C(X; S) ≅ C(X; M ⊗ S)` of Mathlib's
`SSet.chainComplexFunctorObjCompMapIso` (for the coproduct-preserving functor `M ⊗ -`), followed
by the chain map induced by `μ`.  It is natural in `X` and in the coefficient objects.

This is how the coefficients of a cochain act on chains in the cap product: capping with a cochain
`φ : Cₚ(X; R) ⟶ M` produces an element of `M ⊗ C_q(X; S)`, which the pairing turns into a chain
with coefficients in `P`.

## Main definitions and results

* `SSet.ιChainComplex_chainComplexFunctorObjCompMapIso_inv_app_f`: the inverse of Mathlib's
  identification `F(C(X; R)) ≅ C(X; F(R))` on the summand of a simplex.
* `SSet.chainComplexPairing`: the chain map `M ⊗ C(X; S) ⟶ C(X; P)` induced by `μ`.
* `SSet.whiskerLeft_ιChainComplex_chainComplexPairing_f`: its value on the summand of a simplex.
* `SSet.chainComplexPairing_naturality`: it is natural in the simplicial set.
* `SSet.chainComplexPairing_comp_chainComplexFunctor_map_app` and
  `SSet.whiskerLeft_chainComplexFunctor_map_app_comp_chainComplexPairing`: it is natural in the
  coefficient objects.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory Simplicial

universe w v v' u u'

namespace SSet

section FunctorObjCompMapIso

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D] [Preadditive C]
  [Preadditive D] [HasCoproducts.{w} C] [HasCoproducts.{w} D]

/-- The inverse of the identification `F(C(X; R)) ≅ C(X; F(R))` of
`SSet.chainComplexFunctorObjCompMapIso`, for a coproduct-preserving functor `F`, sends the summand
`F(R)` of a simplex `x` to the image under `F` of the summand `R` of `x`.  Morphisms out of
`F(Cₙ(X; R))` are therefore determined on these images. -/
@[reassoc (attr := simp)]
lemma ιChainComplex_chainComplexFunctorObjCompMapIso_inv_app_f (X : SSet.{w}) (F : C ⥤ D)
    [F.Additive] [∀ T : Type w, PreservesColimitsOfShape (Discrete T) F] (R : C) {n : ℕ}
    (x : X _⦋n⦌) :
    X.ιChainComplex x ≫ ((chainComplexFunctorObjCompMapIso F R).inv.app X).f n =
      F.map (X.ιChainComplex x) := by
  rw [← map_ιChainComplex_chainComplexFunctorObjCompMapIso_hom_app_f X F, Category.assoc,
    ← HomologicalComplex.comp_f, Iso.hom_inv_id_app, HomologicalComplex.id_f]
  exact Category.comp_id _

end FunctorObjCompMapIso

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
  [MonoidalCategory C] [MonoidalPreadditive C] {M S P : C}
  [∀ J : Type w, PreservesColimitsOfShape (Discrete J) (tensorLeft M)]

/-- **The chain map induced by a coefficient pairing** `μ : M ⊗ S ⟶ P`: the chain map
`M ⊗ C(X; S) ⟶ C(X; P)` which sends the summand `M ⊗ S` of a simplex `x` to the summand `P` of `x`
through `μ` (`SSet.whiskerLeft_ιChainComplex_chainComplexPairing_f`).  It is the identification
`M ⊗ C(X; S) ≅ C(X; M ⊗ S)` followed by the chain map induced by `μ`. -/
def chainComplexPairing (X : SSet.{w}) (μ : M ⊗ S ⟶ P) :
    ((tensorLeft M).mapHomologicalComplex _).obj (X.chainComplex S) ⟶ X.chainComplex P :=
  (chainComplexFunctorObjCompMapIso (tensorLeft M) S).hom.app X ≫
    ((chainComplexFunctor C).map μ).app X

/-- The chain map induced by a coefficient pairing `μ` sends the summand `M ⊗ S` of a simplex `x`
to the summand `P` of `x` through `μ`. -/
@[reassoc (attr := simp)]
lemma whiskerLeft_ιChainComplex_chainComplexPairing_f (X : SSet.{w}) (μ : M ⊗ S ⟶ P) {n : ℕ}
    (x : X _⦋n⦌) :
    (M ◁ X.ιChainComplex x) ≫ (X.chainComplexPairing μ).f n = μ ≫ X.ιChainComplex x := by
  have := map_ιChainComplex_chainComplexFunctorObjCompMapIso_hom_app_f_assoc X (tensorLeft M) x
    (((chainComplexFunctor C).map μ).app X |>.f n)
  dsimp at this
  rw [chainComplexPairing, HomologicalComplex.comp_f, this,
    TauCeti.SSet.ιChainComplex_chainComplexFunctor_map_app_f]

/-- The chain map induced by a coefficient pairing is natural in the simplicial set. -/
@[reassoc]
lemma chainComplexPairing_naturality {X Y : SSet.{w}} (f : X ⟶ Y) (μ : M ⊗ S ⟶ P) :
    ((tensorLeft M).mapHomologicalComplex _).map (chainComplexMap f S) ≫
        Y.chainComplexPairing μ =
      X.chainComplexPairing μ ≫ chainComplexMap f P := by
  simpa [chainComplexPairing] using
    ((chainComplexFunctorObjCompMapIso (tensorLeft M) S).hom.naturality_assoc f
      (((chainComplexFunctor C).map μ).app Y)).trans
      (congrArg (_ ≫ ·) (((chainComplexFunctor C).map μ).naturality f))

/-- Pushing the chain map induced by a coefficient pairing `μ` forward along a coefficient
morphism `g : P ⟶ P'` is the chain map induced by the pairing `μ ≫ g`. -/
@[reassoc (attr := simp)]
lemma chainComplexPairing_comp_chainComplexFunctor_map_app (X : SSet.{w}) (μ : M ⊗ S ⟶ P)
    {P' : C} (g : P ⟶ P') :
    X.chainComplexPairing μ ≫ ((chainComplexFunctor C).map g).app X =
      X.chainComplexPairing (μ ≫ g) := by
  simp [chainComplexPairing]

/-- Precomposing the chain map induced by a coefficient pairing `μ'` with the chain map induced by
a coefficient morphism `g : S ⟶ S'` is the chain map induced by the pairing `(M ◁ g) ≫ μ'`. -/
@[reassoc (attr := simp)]
lemma whiskerLeft_chainComplexFunctor_map_app_comp_chainComplexPairing (X : SSet.{w}) {S' : C}
    (g : S ⟶ S') (μ' : M ⊗ S' ⟶ P) :
    ((tensorLeft M).mapHomologicalComplex _).map (((chainComplexFunctor C).map g).app X) ≫
        X.chainComplexPairing μ' =
      X.chainComplexPairing ((M ◁ g) ≫ μ') := by
  ext n : 1
  -- morphisms out of `M ⊗ Cₙ(X; S) ≅ Cₙ(X; M ⊗ S)` are determined on the simplices of `X`
  rw [← cancel_epi (((chainComplexFunctorObjCompMapIso (tensorLeft M) S).inv.app X).f n)]
  ext x
  simp [ιChainComplex_chainComplexFunctorObjCompMapIso_inv_app_f_assoc X (tensorLeft M),
    ← MonoidalCategory.whiskerLeft_comp_assoc]

end SSet
