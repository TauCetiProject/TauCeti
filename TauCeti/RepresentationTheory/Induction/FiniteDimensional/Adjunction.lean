/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Adjunction.Limits
public import TauCeti.RepresentationTheory.Induction.FiniteDimensional.Basic
public import TauCeti.RepresentationTheory.Induction.Restriction

/-!
# Adjunctions, Frobenius reciprocity, and exactness of finite-dimensional induction

Induction from a finite-index subgroup is both left and right adjoint to restriction on
finite-dimensional representations. Consequently it preserves finite limits and finite colimits,
and sends short exact sequences to short exact sequences over every field, including when the
group order vanishes in the field. This permits induction to descend to the exact Grothendieck
group, where nonsplit short exact sequences impose relations.

The adjunctions are restrictions of Mathlib's `Rep.indResAdjunction` and `Rep.resIndAdjunction`
along fully faithful inclusions using `ModuleCat.uliftFunctor` to place the carriers in a universe
containing both the field and the group. The private comparison with ordinary induction follows
`Rep.indMap`'s tensor-and-coinvariants construction and uses `TauCeti.indFDRepForgetEquiv`, so the
field and group may lie in separate universes.

The linear Hom-space forms are `FDRep.indResFDRepHomEquiv` and `FDRep.resIndFDRepHomEquiv`,
with the dimension identities `FDRep.finrank_hom_indFDRep` and `FDRep.finrank_hom_resFDRep` as
corollaries. These use the ordinary induced and restricted objects, with application lemmas
expressing both directions in terms of the categorical adjunctions.

Import this file to infer `PreservesFiniteLimits` and `PreservesFiniteColimits` for
`indFDRepFunctor`. With the short-exact-sequence API imported, apply
`CategoryTheory.ShortComplex.ShortExact.map_of_exact` to obtain preservation of short exact
sequences. No semisimplicity or finiteness of the ambient group is required.
-/

public section

namespace TauCeti

open CategoryTheory

universe u v

variable {k : Type u} {G : Type v} [Field k] [Group G] {S : Subgroup G} [S.FiniteIndex]

-- Lift the carriers to a universe containing both the field and the group, where Mathlib's
-- categorical induction adjunctions apply. All these comparison constructions remain private.
private noncomputable def fdRepInclusion (k : Type u) (G : Type v) [Field k] [Group G] :
    FDRep k G ⥤ Rep.{max u v} k G :=
  (forget₂ (FGModuleCat k) (ModuleCat k) ⋙ ModuleCat.uliftFunctor.{v, u} k).mapAction G ⋙
    Rep.ActionToRep k G

private noncomputable def fdRepInclusionEquiv (A : FDRep k G) :
    ((fdRepInclusion k G).obj A).ρ.Equiv
      ((forget₂ (FDRep k G) (Rep k G)).obj A).ρ :=
  .mk (ULift.moduleEquiv : ULift.{v} A ≃ₗ[k] A) (fun _ ↦ by ext; rfl)

private noncomputable def indFDRepInclusionEquiv (A : FDRep k S) :
    (((fdRepInclusion k S).obj A).ρ.ind S.subtype).Equiv
      (((forget₂ (FDRep k S) (Rep k S)).obj A).ρ.ind S.subtype) := by
  let e := fdRepInclusionEquiv A
  let f := Representation.Coinvariants.map _ _
    ((Representation.IntertwiningMap.id ((Representation.leftRegular k G).comp S.subtype)).tensor
      e.toIntertwiningMap)
  let g := Representation.Coinvariants.map _ _
    ((Representation.IntertwiningMap.id ((Representation.leftRegular k G).comp S.subtype)).tensor
      e.symm.toIntertwiningMap)
  refine .mk (LinearEquiv.ofLinearMap f g ?_ ?_) ?_
  · ext h x
    simp [f, g]
  · ext h x
    simp [f, g]
  · intro h
    ext h' x
    simp [f, Representation.ind]

private noncomputable def indFDRepInclusionIso (A : FDRep k S) :
    Rep.ind S.subtype ((fdRepInclusion k S).obj A) ≅
      (fdRepInclusion k G).obj (indFDRep A) :=
  Rep.mkIso ((indFDRepInclusionEquiv A).trans
    ((indFDRepForgetEquiv A).symm.trans (fdRepInclusionEquiv (indFDRep A)).symm))

private noncomputable def indFDRepInclusionNatIso :
    fdRepInclusion k S ⋙ Rep.indFunctor k S.subtype ≅
      indFDRepFunctor (k := k) (S := S) ⋙ fdRepInclusion k G :=
  NatIso.ofComponents (fun A ↦
    indFDRepInclusionIso A ≪≫
      (fdRepInclusion k G).mapIso (eqToIso (indFDRepFunctor_obj A)).symm) fun {A B} f ↦ by
    simp only [Functor.comp_map, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
      eqToIso.inv, indFDRepFunctor_map, Functor.map_comp]
    simp only [Category.assoc, ← Functor.map_comp, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp]
    simp only [Functor.map_comp, ← Category.assoc]
    apply (cancel_mono ((fdRepInclusion k G).map (eqToHom (indFDRepFunctor_obj B).symm))).mpr
    apply Rep.hom_ext
    dsimp only [Functor.comp_obj, Rep.indFunctor_obj, Rep.indFunctor_map]
    ext h x
    -- Tensor extensionality expresses this goal through curried maps; expose its value on an
    -- induced generator so that the comparison isomorphism's application lemma can rewrite it.
    change (indFDRepInclusionIso B).hom.hom
        ((Rep.indMap S.subtype ((fdRepInclusion k S).map f)).hom
          (Representation.IndV.mk S.subtype _ h x)) =
      ((fdRepInclusion k G).map (indFDRepMap f)).hom
        ((indFDRepInclusionIso A).hom.hom (Representation.IndV.mk S.subtype _ h x))
    -- As in the small-carrier comparison in `Basic`, `erw` reconciles the field's and
    -- commutative ring's semiring instances in `Rep.mkIso`'s application lemma.
    dsimp only [indFDRepInclusionIso]
    erw [Rep.mkIso_hom_hom_apply, Rep.mkIso_hom_hom_apply]
    -- The inclusions act by `ULift.up` and `ULift.down`; expose those maps on this generator
    -- to put the small-carrier conjugation in the form of `forget₂_map_indFDRepMap_apply`.
    change ULift.up ((indFDRepForgetEquiv B).symm
        (Representation.IndV.mk S.subtype _ h (f.hom.hom.hom x.down))) =
      ULift.up ((indFDRepMap f).hom.hom.hom
        ((indFDRepForgetEquiv A).symm (Representation.IndV.mk S.subtype _ h x.down)))
    congr 1
    -- Forgetting retains the same linear map, now in the spelling of the conjugation lemma.
    change _ = ((forget₂ (FDRep k G) (Rep k G)).map (indFDRepMap f)).hom _
    rw [forget₂_map_indFDRepMap_apply, Representation.Equiv.apply_symm_apply]
    rfl

/-- Finite-dimensional induction from a finite-index subgroup is left adjoint to restriction. -/
noncomputable def indResFDRepAdjunction :
    indFDRepFunctor (k := k) (S := S) ⊣ Action.res (FGModuleCat k) S.subtype :=
  (Rep.indResAdjunction.{0, u, v, v} k S.subtype).restrictFullyFaithful
    (by unfold fdRepInclusion; exact Functor.FullyFaithful.ofFullyFaithful _)
    (by unfold fdRepInclusion; exact Functor.FullyFaithful.ofFullyFaithful _)
    indFDRepInclusionNatIso
    -- Restriction commutes with inclusion: both use the same lifted module and action maps.
    (eqToIso (by rfl))

/-- For a finite-index subgroup, restriction is also left adjoint to finite-dimensional
induction. -/
noncomputable def resIndFDRepAdjunction :
    Action.res (FGModuleCat k) S.subtype ⊣ indFDRepFunctor (k := k) (S := S) := by
  classical
  exact (Rep.resIndAdjunction.{0, u, v} k S).restrictFullyFaithful
    (by unfold fdRepInclusion; exact Functor.FullyFaithful.ofFullyFaithful _)
    (by unfold fdRepInclusion; exact Functor.FullyFaithful.ofFullyFaithful _)
    -- Restriction commutes with the inclusion on both objects and morphisms.
    (eqToIso (by rfl)) indFDRepInclusionNatIso

/-- Finite-dimensional induction is a left adjoint. -/
noncomputable instance indFDRepFunctor_isLeftAdjoint :
    (indFDRepFunctor (k := k) (S := S)).IsLeftAdjoint :=
  indResFDRepAdjunction.isLeftAdjoint

/-- Finite-dimensional induction from a finite-index subgroup is a right adjoint. -/
noncomputable instance indFDRepFunctor_isRightAdjoint :
    (indFDRepFunctor (k := k) (S := S)).IsRightAdjoint :=
  resIndFDRepAdjunction.isRightAdjoint

end TauCeti

namespace FDRep

open CategoryTheory TauCeti

universe u v

variable {k : Type u} {G : Type v} [Field k] [Group G] {S : Subgroup G}

/-- **Frobenius reciprocity** for finite-dimensional representations, as a `k`-linear equivalence of
intertwining spaces: `Hom_G(Ind_S^G A, B) ≃ₗ[k] Hom_S(A, Res_S B)`.

This is the linear form of `TauCeti.indResFDRepAdjunction`, transported along the object
comparison for `TauCeti.indFDRepFunctor`. -/
noncomputable def indResFDRepHomEquiv [S.FiniteIndex] (A : FDRep k S) (B : FDRep k G) :
    (indFDRep A ⟶ B) ≃ₗ[k] (A ⟶ Subgroup.resFDRep S B) := by
  let e : ((indFDRepFunctor (k := k)).obj A ⟶ B) ≃ₗ[k] (A ⟶ Subgroup.resFDRep S B) :=
    { indResFDRepAdjunction.homAddEquiv A B with
      map_smul' := fun r f ↦ by simp [Adjunction.homEquiv_apply] }
  exact (Linear.homCongr k (eqToIso (indFDRepFunctor_obj A)).symm (Iso.refl B)).trans e

/-- On morphisms, reciprocity is the categorical adjunction after comparing the induced objects. -/
@[simp]
theorem indResFDRepHomEquiv_apply [S.FiniteIndex] (A : FDRep k S) (B : FDRep k G)
    (f : indFDRep A ⟶ B) :
    indResFDRepHomEquiv A B f =
      indResFDRepAdjunction.homEquiv A B (eqToHom (indFDRepFunctor_obj A) ≫ f) := by
  simp [indResFDRepHomEquiv, Linear.homCongr_apply]

/-- The inverse reciprocity map is the inverse categorical adjunction with the induced objects
compared. -/
@[simp]
theorem indResFDRepHomEquiv_symm_apply [S.FiniteIndex] (A : FDRep k S) (B : FDRep k G)
    (f : A ⟶ Subgroup.resFDRep S B) :
    (indResFDRepHomEquiv A B).symm f =
      eqToHom (indFDRepFunctor_obj A).symm ≫
        (indResFDRepAdjunction.homEquiv A B).symm f := by
  simp [indResFDRepHomEquiv, Linear.homCongr_symm_apply]

/-- The intertwining space out of an induced representation has the same dimension as the
intertwining space into the corresponding restriction. This is the quantitative content of
Frobenius reciprocity, and holds over an arbitrary field. -/
theorem finrank_hom_indFDRep [S.FiniteIndex] (A : FDRep k S) (B : FDRep k G) :
    Module.finrank k (indFDRep A ⟶ B) = Module.finrank k (A ⟶ Subgroup.resFDRep S B) :=
  (indResFDRepHomEquiv A B).finrank_eq

/-- **The second reciprocity**, available because induction from a finite-index subgroup is also a
*right* adjoint to restriction: `Hom_S(Res_S B, A) ≃ₗ[k] Hom_G(B, Ind_S^G A)`.

This is the linear form of `TauCeti.resIndFDRepAdjunction`, transported along the object
comparison for `TauCeti.indFDRepFunctor`. -/
noncomputable def resIndFDRepHomEquiv [S.FiniteIndex] (A : FDRep k S) (B : FDRep k G) :
    (Subgroup.resFDRep S B ⟶ A) ≃ₗ[k] (B ⟶ indFDRep A) := by
  let e : (B ⟶ (indFDRepFunctor (k := k)).obj A) ≃ₗ[k] (Subgroup.resFDRep S B ⟶ A) :=
    { (resIndFDRepAdjunction.homAddEquiv B A).symm with
      map_smul' := fun r f ↦ by simp [Adjunction.homEquiv_symm_apply] }
  exact e.symm.trans (Linear.homCongr k (Iso.refl B) (eqToIso (indFDRepFunctor_obj A)))

/-- On morphisms, the second reciprocity is the categorical adjunction followed by the
comparison of induced objects. -/
@[simp]
theorem resIndFDRepHomEquiv_apply [S.FiniteIndex] (A : FDRep k S) (B : FDRep k G)
    (f : Subgroup.resFDRep S B ⟶ A) :
    resIndFDRepHomEquiv A B f =
      resIndFDRepAdjunction.homEquiv B A f ≫ eqToHom (indFDRepFunctor_obj A) := by
  simp [resIndFDRepHomEquiv, Linear.homCongr_apply]

/-- The inverse second reciprocity map is the inverse categorical adjunction after comparing the
induced objects. -/
@[simp]
theorem resIndFDRepHomEquiv_symm_apply [S.FiniteIndex] (A : FDRep k S) (B : FDRep k G)
    (f : B ⟶ indFDRep A) :
    (resIndFDRepHomEquiv A B).symm f =
      (resIndFDRepAdjunction.homEquiv B A).symm
        (f ≫ eqToHom (indFDRepFunctor_obj A).symm) := by
  simp [resIndFDRepHomEquiv, Linear.homCongr_symm_apply]

/-- The dimension form of the second reciprocity. -/
theorem finrank_hom_resFDRep [S.FiniteIndex] (A : FDRep k S) (B : FDRep k G) :
    Module.finrank k (Subgroup.resFDRep S B ⟶ A) = Module.finrank k (B ⟶ indFDRep A) :=
  (resIndFDRepHomEquiv A B).finrank_eq

end FDRep
