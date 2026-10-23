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

In the same way, when tensoring on either side preserves `w`-small coproducts, the tensor product
`Cₚ(K; R) ⊗ C_q(L; S)` of chain groups of two simplicial sets is the coproduct of one copy of
`R ⊗ S` for each pair of a `p`-simplex of `K` and a `q`-simplex of `L`, which describes morphisms
out of tensor products of simplicial chains, such as the shuffle map.

## Main definitions and results

* `SSet.ιChainComplex_chainComplexFunctorObjCompMapIso_inv_app_f`: the inverse of Mathlib's
  identification `F(C(X; R)) ≅ C(X; F(R))` on the summand of a simplex.
* `SSet.chainComplexPairing`: the chain map `M ⊗ C(X; S) ⟶ C(X; P)` induced by `μ`.
* `SSet.whiskerLeft_ιChainComplex_chainComplexPairing_f`: its value on the summand of a simplex.
* `SSet.chainComplexPairing_naturality`: it is natural in the simplicial set.
* `SSet.chainComplexPairing_comp_chainComplexFunctor_map_app`,
  `SSet.whiskerLeft_chainComplexFunctor_map_app_comp_chainComplexPairing` and
  `SSet.whiskerRight_comp_chainComplexPairing`: it is natural in the coefficient objects.
* `SSet.tensorChainComplexXDesc` and `SSet.tensorChainComplexX_hom_ext`: morphisms out of the
  tensor product `Cₚ(K; R) ⊗ C_q(L; S)` of two chain groups are given, and determined, by their
  values on the summands `R ⊗ S` of pairs of simplices.
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

section Tensor

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C] [MonoidalCategory C]
  {K L : SSet.{w}} {R S A : C} {p q : ℕ}
  [∀ J : Type w, PreservesColimitsOfShape (Discrete J) (tensorLeft R)]
  [∀ (X : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight X)]

/-- The morphism out of the tensor product `Cₚ(K; R) ⊗ C_q(L; S)` of two simplicial chain groups
given by a morphism `φ x y : R ⊗ S ⟶ A` for each `p`-simplex `x` of `K` and `q`-simplex `y` of `L`
(`SSet.ιChainComplex_tensorHom_ιChainComplex_tensorChainComplexXDesc`).  When tensoring preserves
coproducts, `Cₚ(K; R) ⊗ C_q(L; S)` is the coproduct of one copy of `R ⊗ S` for each such pair. -/
def tensorChainComplexXDesc (φ : K _⦋p⦌ → L _⦋q⦌ → (R ⊗ S ⟶ A)) :
    (K.chainComplex R).X p ⊗ (L.chainComplex S).X q ⟶ A :=
  Cofan.IsColimit.desc (isColimitCofanMkObjOfIsColimit (tensorRight ((L.chainComplex S).X q)) _ _
    (K.isColimitChainComplexXCofan R p)) fun x ↦
      Cofan.IsColimit.desc (isColimitCofanMkObjOfIsColimit (tensorLeft R) _ _
        (L.isColimitChainComplexXCofan S q)) (φ x)

/-- The morphism `SSet.tensorChainComplexXDesc φ` on the summand of a pair of simplices `(x, y)` is
`φ x y`. -/
@[reassoc (attr := simp)]
lemma ιChainComplex_tensorHom_ιChainComplex_tensorChainComplexXDesc
    (φ : K _⦋p⦌ → L _⦋q⦌ → (R ⊗ S ⟶ A)) (x : K _⦋p⦌) (y : L _⦋q⦌) :
    (K.ιChainComplex x ⊗ₘ L.ιChainComplex y) ≫ tensorChainComplexXDesc φ = φ x y := by
  have h₁ := Cofan.IsColimit.fac (isColimitCofanMkObjOfIsColimit
    (tensorRight ((L.chainComplex S).X q)) _ _ (K.isColimitChainComplexXCofan R p))
    (fun x ↦ Cofan.IsColimit.desc (isColimitCofanMkObjOfIsColimit (tensorLeft R) _ _
      (L.isColimitChainComplexXCofan S q)) (φ x)) x
  have h₂ := Cofan.IsColimit.fac (isColimitCofanMkObjOfIsColimit (tensorLeft R) _ _
    (L.isColimitChainComplexXCofan S q)) (φ x) y
  simp only [cofan_mk_inj, Functor.flip_obj_map, curriedTensor_map_app,
    curriedTensor_obj_map] at h₁ h₂
  rw [tensorHom_def', Category.assoc, tensorChainComplexXDesc, h₁, h₂]

/-- Morphisms out of `Cₚ(K; R) ⊗ C_q(L; S)` are determined on the summands of pairs of simplices. -/
lemma tensorChainComplexX_hom_ext {f g : (K.chainComplex R).X p ⊗ (L.chainComplex S).X q ⟶ A}
    (h : ∀ (x : K _⦋p⦌) (y : L _⦋q⦌), (K.ιChainComplex x ⊗ₘ L.ιChainComplex y) ≫ f =
      (K.ιChainComplex x ⊗ₘ L.ιChainComplex y) ≫ g) :
    f = g := by
  refine Cofan.IsColimit.hom_ext (isColimitCofanMkObjOfIsColimit
    (tensorRight ((L.chainComplex S).X q)) _ _ (K.isColimitChainComplexXCofan R p)) _ _
      fun x ↦ Cofan.IsColimit.hom_ext (isColimitCofanMkObjOfIsColimit (tensorLeft R) _ _
        (L.isColimitChainComplexXCofan S q)) _ _ fun y ↦ ?_
  simpa [tensorHom_def'] using h x y

end Tensor

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

/-- Precomposing the chain map induced by a coefficient pairing `μ'` with the chain map
`g ▷ C(X; S) : M ⊗ C(X; S) ⟶ M' ⊗ C(X; S)` induced by a coefficient morphism `g : M ⟶ M'` is the
chain map induced by the pairing `(g ▷ S) ≫ μ'`. -/
@[reassoc (attr := simp)]
lemma whiskerRight_comp_chainComplexPairing (X : SSet.{w}) {M' : C}
    [∀ J : Type w, PreservesColimitsOfShape (Discrete J) (tensorLeft M')] (g : M ⟶ M')
    (μ' : M' ⊗ S ⟶ P) :
    (NatTrans.mapHomologicalComplex ((tensoringLeft C).map g) _).app (X.chainComplex S) ≫
        X.chainComplexPairing μ' =
      X.chainComplexPairing ((g ▷ S) ≫ μ') := by
  ext n : 1
  -- morphisms out of `M ⊗ Cₙ(X; S) ≅ Cₙ(X; M ⊗ S)` are determined on the simplices of `X`
  rw [← cancel_epi (((chainComplexFunctorObjCompMapIso (tensorLeft M) S).inv.app X).f n)]
  ext x
  simp [ιChainComplex_chainComplexFunctorObjCompMapIso_inv_app_f_assoc X (tensorLeft M),
    whisker_exchange_assoc]

end SSet
