/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.RingTheory.Artinian.Defs
import TauCeti.Algebra.Category.ModuleCat.KrullSchmidt
import TauCeti.Algebra.Category.ModuleCat.Indecomposable
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
-/

public section

namespace FGModuleCat

open CategoryTheory CategoryTheory.Limits

universe w v

variable {A : Type v} [Ring A]

/-- Every finitely generated Artinian module `X` is a direct summand of a finite sum of finitely
generated indecomposable modules `W j`, in the form of morphisms `a j : X ⟶ W j` and
`b j : W j ⟶ X` with `∑ j, a j ≫ b j = 𝟙 X`. -/
theorem exists_indecomposable_sum_comp_eq_id (X : FGModuleCat.{w} A) [IsArtinian A X.obj] :
    ∃ (n : ℕ) (W : Fin n → FGModuleCat.{w} A) (a : ∀ j, X ⟶ W j) (b : ∀ j, W j ⟶ X),
      (∀ j, Indecomposable (W j).obj) ∧ ∑ j, a j ≫ b j = 𝟙 X := by
  obtain ⟨n, Q, hQ, ⟨d⟩⟩ := TauCeti.exists_indecomposable_iso_biproduct X.obj
  -- Each summand is a quotient of `X`, hence finitely generated.
  have hQf (j : Fin n) : Module.Finite A (Q j) := by
    refine Module.Finite.of_surjective (d.hom ≫ biproduct.π Q j).hom fun y ↦
      ⟨(biproduct.ι Q j ≫ d.inv).hom y, ?_⟩
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp]
    simp
  refine ⟨n, fun j ↦ ⟨Q j, (ModuleCat.isFG_iff _).mpr (hQf j)⟩,
    fun j ↦ ObjectProperty.homMk (d.hom ≫ biproduct.π Q j),
    fun j ↦ ObjectProperty.homMk (biproduct.ι Q j ≫ d.inv), hQ, ?_⟩
  have h : ∑ j, (d.hom ≫ biproduct.π Q j) ≫ biproduct.ι Q j ≫ d.inv = 𝟙 X.obj :=
    calc _ = d.hom ≫ (∑ j, biproduct.π Q j ≫ biproduct.ι Q j) ≫ d.inv := by
          simp only [Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc]
      _ = 𝟙 X.obj := by simp [biproduct.total]
  -- Check the identity after the faithful inclusion into `ModuleCat A`.
  apply (ObjectProperty.ι _).map_injective
  rw [Functor.map_sum, CategoryTheory.Functor.map_id]
  simpa using h

/-- **Fitting's lemma** in `FGModuleCat A`: a finitely generated indecomposable module of finite
length (Noetherian and Artinian) has a local endomorphism ring. -/
theorem isLocalRing_end_of_indecomposable {X : FGModuleCat.{w} A} [IsNoetherian A X.obj]
    [IsArtinian A X.obj] (hX : Indecomposable X.obj) : IsLocalRing (End X) := by
  have hfl : IsFiniteLength A X.obj :=
    isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩
  have : IsLocalRing (End ((ObjectProperty.ι _).obj X)) :=
    (TauCeti.indecomposable_iff_isLocalRing_end X.obj hfl).mp hX
  exact ((ObjectProperty.fullyFaithfulι _).ringEquivEnd X).symm.isLocalRing

end FGModuleCat
