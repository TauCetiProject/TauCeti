/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.RingTheory.Artinian.Defs
public import TauCeti.Algebra.Category.FGModuleCat.Basic
public import TauCeti.Algebra.Category.ModuleCat.FiniteLength.Basic
public import TauCeti.CategoryTheory.Preadditive.KrullSchmidt.Basic
import TauCeti.Algebra.Category.ModuleCat.KrullSchmidt
import TauCeti.CategoryTheory.Preadditive.KrullSchmidt.FullSubcategory
import TauCeti.Algebra.Category.ModuleCat.Indecomposable
import TauCeti.CategoryTheory.Functor.Indecomposable
import TauCeti.CategoryTheory.Functor.RingEquivEnd

/-!
# Decomposition into indecomposables in `FGModuleCat`

Every finitely generated Artinian module `X` is a direct summand of a finite sum of finitely
generated indecomposable modules `W j` (`FGModuleCat.exists_indecomposable_sum_comp_eq_id`). This
is read off from the existence half of the Krull-Schmidt theorem,
`TauCeti.exists_indecomposable_iso_biproduct`, inside `FGModuleCat A`. The summand is recorded by
morphisms `a j : X ⟶ W j` and `b j : W j ⟶ X` with `∑ j, a j ≫ b j = 𝟙 X`, which needs no
biproducts in `FGModuleCat A`. By Fitting's lemma, a finitely generated indecomposable module of
finite length has a local endomorphism ring (`FGModuleCat.isLocalRing_end_of_indecomposable`).
Over any ring, a finitely generated module is indecomposable as a module exactly when it is an
indecomposable object of `FGModuleCat A` (`FGModuleCat.indecomposable_obj_iff`).

Over a left Artinian ring `A`, for instance an Artin algebra, finitely generated modules have finite
length, so `mod A = FGModuleCat A` is a Krull-Schmidt category
(`FGModuleCat.isKrullSchmidt_of_isArtinianRing`).
-/

public section

namespace FGModuleCat

open CategoryTheory CategoryTheory.Limits

universe w v

variable {A : Type v} [Ring A]

/-- Every finitely generated Artinian module, for instance any finitely generated module over a left
Artinian ring, is isomorphic, in `FGModuleCat A`, to a finite biproduct of finitely generated
indecomposable modules. -/
theorem exists_indecomposable_iso_biproduct (X : FGModuleCat.{w} A) [IsArtinian A X.obj] :
    ∃ (n : ℕ) (F : Fin n → FGModuleCat.{w} A), (∀ j, Indecomposable (F j).obj) ∧
      Nonempty (X ≅ ⨁ F) := by
  obtain ⟨n, Q, hQ, ⟨d⟩⟩ := TauCeti.exists_indecomposable_iso_biproduct X.obj
  -- Each summand is a quotient of `X`, hence finitely generated.
  let F (j : Fin n) : FGModuleCat.{w} A := ⟨Q j, (ModuleCat.isFG_iff _).mpr
    (Module.Finite.of_surjective (d.hom ≫ biproduct.π Q j).hom
      ((ModuleCat.epi_iff_surjective _).mp inferInstance))⟩
  -- The inclusion into `ModuleCat A` preserves the biproduct.
  exact ⟨n, F, hQ, ⟨(ObjectProperty.fullyFaithfulι _).preimageIso
    (d ≪≫ ((ObjectProperty.ι _).mapBiproduct F).symm)⟩⟩

/-- Every finitely generated Artinian module `X` is a direct summand of a finite sum of finitely
generated indecomposable modules `W j`, in the form of morphisms `a j : X ⟶ W j` and
`b j : W j ⟶ X` with `∑ j, a j ≫ b j = 𝟙 X`. -/
theorem exists_indecomposable_sum_comp_eq_id (X : FGModuleCat.{w} A) [IsArtinian A X.obj] :
    ∃ (n : ℕ) (W : Fin n → FGModuleCat.{w} A) (a : ∀ j, X ⟶ W j) (b : ∀ j, W j ⟶ X),
      (∀ j, Indecomposable (W j).obj) ∧ ∑ j, a j ≫ b j = 𝟙 X := by
  obtain ⟨n, F, hF, ⟨e⟩⟩ := exists_indecomposable_iso_biproduct X
  refine ⟨n, F, fun j ↦ e.hom ≫ biproduct.π F j, fun j ↦ biproduct.ι F j ≫ e.inv, hF, ?_⟩
  calc _ = e.hom ≫ (∑ j, biproduct.π F j ≫ biproduct.ι F j) ≫ e.inv := by
        simp only [Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc]
    _ = 𝟙 X := by simp [biproduct.total]

/-- **Fitting's lemma** in `FGModuleCat A`: a finitely generated indecomposable module of finite
length (Noetherian and Artinian) has a local endomorphism ring. -/
theorem isLocalRing_end_of_indecomposable {X : FGModuleCat.{w} A} [IsNoetherian A X.obj]
    [IsArtinian A X.obj] (hX : Indecomposable X.obj) : IsLocalRing (End X) := by
  have hfl : IsFiniteLength A X.obj :=
    isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩
  have : IsLocalRing (End ((ObjectProperty.ι _).obj X)) :=
    (TauCeti.indecomposable_iff_isLocalRing_end X.obj hfl).mp hX
  exact ((ObjectProperty.fullyFaithfulι _).ringEquivEnd X).symm.isLocalRing

/-- A finitely generated module is indecomposable in the category of all modules exactly when it
is an indecomposable object of `mod A`, over any ring. -/
theorem indecomposable_obj_iff (P : FGModuleCat.{w} A) :
    Indecomposable P.obj ↔ Indecomposable P := by
  -- The inclusion `mod A ⥤ Mod A` is additive and fully faithful: it reflects indecomposability
  -- because it reflects zero objects, and preserves it because it is bijective on endomorphisms
  -- and idempotents split in `mod A`.
  let ι := ObjectProperty.ι (ModuleCat.isFG.{w} A)
  have := preservesBinaryBiproducts_of_preservesBiproducts ι
  exact ⟨fun h ↦ ι.indecomposable_of_indecomposable_obj_of_reflects_isZero_retract h
      fun _ ↦ IsZero.of_full_of_faithful_of_isZero ι _,
    fun h ↦ ι.indecomposable_obj_of_map_bijective h
      ((ObjectProperty.fullyFaithfulι _).map_bijective P P)⟩

open TauCeti in
/-- **`mod A` is Krull-Schmidt over a left Artinian ring `A`**, for instance an Artin algebra: the
finitely generated modules are the modules of finite length, which form a Krull-Schmidt category
(`TauCeti.isKrullSchmidt_isFiniteLength`). -/
instance isKrullSchmidt_of_isArtinianRing [IsArtinianRing A] :
    IsKrullSchmidt (FGModuleCat.{w} A) :=
  (ObjectProperty.fullSubcategoryCongr ModuleCat.isFiniteLength_eq_isFG).isKrullSchmidt

end FGModuleCat
