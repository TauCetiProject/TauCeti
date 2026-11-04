/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.Mackey.Hom

/-!
# Naturality of the Mackey decomposition of intertwining spaces

The double-coset decomposition of `Hom(Ind A, Ind B)` is contravariantly natural in `A`
and covariantly natural in `B`. Thus pre- and postcomposition by induced morphisms become
pre- and postcomposition by the restricted morphisms in every intersection-subgroup Hom space.
These identities allow the decomposition to be used functorially, not just to count dimensions.

The representation-level statements work over commutative rings, without semisimplicity.

## References

* C. W. Curtis and I. Reiner, *Methods of Representation Theory*, Vol. I, §10.
-/

public section

open CategoryTheory TauCeti

namespace Rep

universe u

variable {k G : Type u} [CommRing k] [Group G] [Finite G] {H K : Subgroup G}

-- The naturality lemmas are used with `rw`: the existing simp lemmas for evaluating
-- the Hom equivalences expand their left-hand sides, so they are not simp normal forms.

/-- Precomposing by an induced morphism precomposes each Mackey component by its
restriction to the intersection subgroup. -/
theorem indHomMackeyLinearEquiv_naturality_left {A A' : Rep.{u} k H} (B : Rep.{u} k K)
    (f : A' ⟶ A) (φ : Rep.ind H.subtype A ⟶ Rep.ind K.subtype B)
    (D : DoubleCoset.Quotient (H : Set G) (K : Set G)) :
    indHomMackeyLinearEquiv A' B (Rep.indMap H.subtype f ≫ φ) D =
      (Rep.resFunctor ((mackeySubgroup D.out K H).subgroupOf H).subtype).map f ≫
        indHomMackeyLinearEquiv A B φ D := by
  classical
  let := Fintype.ofFinite (DoubleCoset.Quotient (H : Set G) (K : Set G))
  have hi : Rep.indResHomEquiv H.subtype A' (Rep.ind K.subtype B)
      (Rep.indMap H.subtype f ≫ φ) =
      f ≫ Rep.indResHomEquiv H.subtype A (Rep.ind K.subtype B) φ :=
    (Rep.indResAdjunction k H.subtype).homEquiv_naturality_left f φ
  rw [indHomMackeyLinearEquiv_apply, indHomMackeyLinearEquiv_apply, hi,
    Category.assoc, homDirectSumLinearEquiv_comp, Category.assoc]
  exact (Rep.resCoindAdjunction.{u, u, u, u} k
    ((mackeySubgroup D.out K H).subgroupOf H).subtype).homEquiv_naturality_left_symm
      f ((Rep.homDirectSumLinearEquiv A
        (fun E : DoubleCoset.Quotient (H : Set G) (K : Set G) ↦
          Rep.mackeySummand K H E.out B)
        ((Rep.indResHomEquiv H.subtype A (Rep.ind K.subtype B) φ) ≫
          (Rep.mackeyDecomposition (K := H) B).hom) D) ≫
        (Rep.indCoindIso (Rep.res (mackeyToH D.out K H) B)).hom)

/-- Postcomposing by an induced morphism postcomposes each Mackey component by its
conjugated restriction to the intersection subgroup. -/
theorem indHomMackeyLinearEquiv_naturality_right (A : Rep.{u} k H) {B B' : Rep.{u} k K}
    (φ : Rep.ind H.subtype A ⟶ Rep.ind K.subtype B) (g : B ⟶ B')
    (D : DoubleCoset.Quotient (H : Set G) (K : Set G)) :
    indHomMackeyLinearEquiv A B' (φ ≫ Rep.indMap K.subtype g) D =
      indHomMackeyLinearEquiv A B φ D ≫ (Rep.resFunctor (mackeyToH D.out K H)).map g := by
  classical
  let := Fintype.ofFinite (DoubleCoset.Quotient (H : Set G) (K : Set G))
  have hi : Rep.indResHomEquiv H.subtype A (Rep.ind K.subtype B')
      (φ ≫ Rep.indMap K.subtype g) =
      Rep.indResHomEquiv H.subtype A (Rep.ind K.subtype B) φ ≫
        (Rep.resFunctor H.subtype).map (Rep.indMap K.subtype g) :=
    (Rep.indResAdjunction k H.subtype).homEquiv_naturality_right φ (Rep.indMap K.subtype g)
  have hm := (Rep.mackeyDecompositionNatIso K H).hom.naturality g
  simp only [← Iso.app_hom, mackeyDecompositionNatIso_app, Functor.comp_map,
    Rep.indFunctor_map] at hm
  have hc :
      Rep.homDirectSumLinearEquiv A
        (fun E : DoubleCoset.Quotient (H : Set G) (K : Set G) ↦
          Rep.mackeySummand K H E.out B')
        ((Rep.indResHomEquiv H.subtype A (Rep.ind K.subtype B) φ) ≫
          (Rep.mackeyDecomposition (K := H) B).hom ≫
          (Rep.mackeyDirectSumFunctor K H).map g) D =
      Rep.homDirectSumLinearEquiv A
        (fun E : DoubleCoset.Quotient (H : Set G) (K : Set G) ↦
          Rep.mackeySummand K H E.out B)
        ((Rep.indResHomEquiv H.subtype A (Rep.ind K.subtype B) φ) ≫
          (Rep.mackeyDecomposition (K := H) B).hom) D ≫
        (Rep.mackeySummandFunctor K H D.out).map g := by
    ext x
    simp only [Representation.IntertwiningMap.coe_toLinearMap, Rep.hom_comp,
      Representation.IntertwiningMap.comp_apply]
    erw [homDirectSumLinearEquiv_apply, homDirectSumLinearEquiv_apply]
    -- The exposed direct-sum functor is defined by `DirectSum.lmap`, whose action
    -- on a coordinate is definitionally the corresponding summand map.
    rfl
  have hn := (Rep.indCoindNatIso k
    ((mackeySubgroup D.out K H).subgroupOf H)).hom.naturality
      ((Rep.resFunctor (mackeyToH D.out K H)).map g)
  simp only [Rep.indCoindNatIso_hom_app, Rep.indFunctor_map] at hn
  erw [indHomMackeyLinearEquiv_apply, indHomMackeyLinearEquiv_apply, hi,
    Category.assoc, hm, hc, Category.assoc, hn, ← Category.assoc]
  exact (Rep.resCoindAdjunction.{u, u, u, u} k
    ((mackeySubgroup D.out K H).subgroupOf H).subtype).homEquiv_naturality_right_symm _ _

end Rep

namespace FDRep

universe u

variable {k G : Type u} [Field k] [Group G] [Finite G] {H K : Subgroup G}

/-- The finite-dimensional Mackey Hom decomposition is contravariantly natural in its
source, over every field. -/
theorem indHomMackeyLinearEquiv_naturality_left {A A' : FDRep k H} (B : FDRep k K)
    (f : A' ⟶ A) (φ : indFDRep A ⟶ indFDRep B)
    (D : DoubleCoset.Quotient (H : Set G) (K : Set G)) :
    indHomMackeyLinearEquiv A' B (indFDRepMap f ≫ φ) D =
      (Action.res (FGModuleCat k)
        ((mackeySubgroup D.out K H).subgroupOf H).subtype).map f ≫
          indHomMackeyLinearEquiv A B φ D := by
  have h := Rep.indHomMackeyLinearEquiv_naturality_left
    ((forget₂ (FDRep k K) (Rep k K)).obj B)
    ((forget₂ (FDRep k H) (Rep k H)).map f)
    ((indFDRepForgetIso A).inv ≫
      (forget₂ (FDRep k G) (Rep k G)).map φ ≫ (indFDRepForgetIso B).hom) D
  apply (forget₂ (FDRep k
    ((mackeySubgroup D.out K H).subgroupOf H))
      (Rep k ((mackeySubgroup D.out K H).subgroupOf H))).map_injective
  simp only [Functor.map_comp, indHomMackeyLinearEquiv_apply,
    forget₂HomLinearEquiv_symm_apply, forget₂_map_indFDRepMap,
    MonoidHom.forget₂_map_actionRes, Category.assoc]
  erw [forget₂_map_forget₂HomLinearEquiv, forget₂_map_forget₂HomLinearEquiv]
  simp only [Iso.inv_hom_id_assoc]
  exact h

/-- The finite-dimensional Mackey Hom decomposition is covariantly natural in its
target, over every field. -/
theorem indHomMackeyLinearEquiv_naturality_right (A : FDRep k H) {B B' : FDRep k K}
    (φ : indFDRep A ⟶ indFDRep B) (g : B ⟶ B')
    (D : DoubleCoset.Quotient (H : Set G) (K : Set G)) :
    indHomMackeyLinearEquiv A B' (φ ≫ indFDRepMap g) D =
      indHomMackeyLinearEquiv A B φ D ≫
        (Action.res (FGModuleCat k) (mackeyToH D.out K H)).map g := by
  have h := Rep.indHomMackeyLinearEquiv_naturality_right
    ((forget₂ (FDRep k H) (Rep k H)).obj A)
    ((indFDRepForgetIso A).inv ≫
      (forget₂ (FDRep k G) (Rep k G)).map φ ≫ (indFDRepForgetIso B).hom)
    ((forget₂ (FDRep k K) (Rep k K)).map g) D
  apply (forget₂ (FDRep k
    ((mackeySubgroup D.out K H).subgroupOf H))
      (Rep k ((mackeySubgroup D.out K H).subgroupOf H))).map_injective
  simp only [Functor.map_comp, indHomMackeyLinearEquiv_apply,
    forget₂HomLinearEquiv_symm_apply, forget₂_map_indFDRepMap,
    MonoidHom.forget₂_map_actionRes, Category.assoc]
  erw [forget₂_map_forget₂HomLinearEquiv, forget₂_map_forget₂HomLinearEquiv]
  simp only [Iso.inv_hom_id, Category.comp_id, Rep.indFunctor_map]
  simp only [Category.assoc] at h
  -- The remaining type equality identifies forgetting an `Action.res` object with
  -- restricting the forgotten representation; both retain the same module and action.
  convert h using 1
  rfl

end FDRep
