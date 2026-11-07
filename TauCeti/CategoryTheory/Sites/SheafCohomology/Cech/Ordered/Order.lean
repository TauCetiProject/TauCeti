/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Ordered.HomotopyEquiv
import TauCeti.Data.Fin.Tuple.Sort
import TauCeti.Data.Finset.Inversions
import Mathlib.Tactic.LinearCombination

/-!
# Changing the order in the ordered Čech complex

For a family in a thin category with finite products, two linear orders on its index type give
naturally isomorphic ordered Čech complexes. The comparison extends a cochain alternately to
all tuples using `fromStrictMonoCechComplex` and then restricts using
`toStrictMonoCechComplex` for the new order. On each coordinate it therefore carries the sign of
the permutation sorting that tuple in the old order.

The comparisons satisfy identity and composition laws on complexes, not just on cohomology.
They allow an ordered presentation to be used without making its chosen order part of the
cohomological invariant. No covering assumption, finiteness, or division by factorials is used.

## References

* The Stacks Project, Cohomology of Sheaves, Remark 20.23.5 (tag 01FL).
-/

public section

noncomputable section

open CategoryTheory Limits Opposite Finset

universe w v v' u u'

namespace TauCeti.CategoryTheory

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] [Quiver.IsThin C]
  {A : Type u'} [Category.{v'} A] [Preadditive A] [HasProducts.{w} A]
  {ι : Type w} (U : ι → C)

private lemma changeOrder_absorption (o₁ o₂ : LinearOrder ι) :
    (letI := o₁; fromStrictMonoCechComplex (A := A) U) ≫
        (letI := o₂; toStrictMonoCechComplex U) ≫
        (letI := o₂; fromStrictMonoCechComplex U) =
      (letI := o₁; fromStrictMonoCechComplex U) := by
  apply NatTrans.ext
  funext P
  apply HomologicalComplex.hom_ext
  intro n
  refine Pi.hom_ext (f := fun b : Fin (n + 1) → ι ↦
    P.obj (op (∏ᶜ fun j ↦ U (b j)))) _ _ fun b ↦ ?_
  by_cases hb : Function.Injective b
  · let σ := @Tuple.sort _ _ o₂ b
    have hσ : Function.Injective (b ∘ σ) := hb.comp σ.injective
    have hsort := @Tuple.comp_sort_eq_comp_sort_of_range_eq ι o₁ _ (b ∘ σ) b hσ hb
      (σ.surjective.range_comp b)
    -- Multiplicativity of inversion signs makes sorting in either order compatible.
    have hsign₁ := @Finset.neg_one_pow_card_inversions_comp _ _ ι _ _ o₁ ℤ _ _
      σ.toEmbedding b hb univ
    have hsign₂ := @Finset.neg_one_pow_card_inversions_comp _ _ ι _ _ o₂ ℤ _ _
      σ.toEmbedding b hb univ
    simp only [map_univ_equiv, Equiv.coe_toEmbedding] at hsign₁ hsign₂
    dsimp only [σ] at hsign₂
    have hmono := @Tuple.strictMono_comp_sort ι o₂ _ b hb
    rw [inversions_eq_empty_of_monotone hmono.monotone, card_empty, pow_zero] at hsign₂
    have hsign :
        (-1 : ℤ) ^ #(@Finset.inversions _ _ _ o₂ b univ) *
            (-1 : ℤ) ^ #(@Finset.inversions _ _ _ o₁ (b ∘ σ) univ) =
          (-1 : ℤ) ^ #(@Finset.inversions _ _ _ o₁ b univ) := by
      rw [hsign₁]
      linear_combination -((-1 : ℤ) ^ #(@Finset.inversions _ _ _ o₁ b univ)) * hsign₂
    -- Compare coordinates after sorting twice; the increasing rearrangements agree.
    simp only [NatTrans.comp_app, HomologicalComplex.comp_f]
    -- The native terms use formal coproducts; `erw` unfolds this product presentation.
    erw [Category.assoc, Category.assoc]
    erw [@fromStrictMonoCechComplex_app_f_π _ _ _ _ _ _ _ _ o₂ U _ P n b hb]
    simp only [Preadditive.comp_zsmul, toStrictMonoCechComplex_app_f_π_assoc]
    erw [← Category.assoc,
      @fromStrictMonoCechComplex_app_f_π _ _ _ _ _ _ _ _ o₁ U _ P n (b ∘ σ) hσ,
      @fromStrictMonoCechComplex_app_f_π _ _ _ _ _ _ _ _ o₁ U _ P n b hb]
    simp only [Preadditive.zsmul_comp, smul_smul, hsign, Category.assoc, ← Functor.map_comp,
      ← op_comp]
    congr 1
    have hcoord (a a' : {a : Fin (n + 1) → ι //
        @StrictMono _ _ _ o₁.toPartialOrder.toPreorder a}) (ha : a = a')
        (f : (∏ᶜ fun j ↦ U (b j)) ⟶ ∏ᶜ fun j ↦ U (a.1 j))
        (g : (∏ᶜ fun j ↦ U (b j)) ⟶ ∏ᶜ fun j ↦ U (a'.1 j)) :
        (letI := o₁; strictMonoCechComplexπ U P a) ≫ P.map f.op =
          (letI := o₁; strictMonoCechComplexπ U P a') ≫ P.map g.op := by
      subst a'
      rw [Subsingleton.elim f g]
    exact hcoord _ _ (Subtype.ext hsort) _ _
  · simp only [NatTrans.comp_app, HomologicalComplex.comp_f]
    erw [Category.assoc, Category.assoc]
    erw [@fromStrictMonoCechComplex_app_f_π_of_not_injective _ _ _ _ _ _ _ _ o₂ U _ P n b hb,
      @fromStrictMonoCechComplex_app_f_π_of_not_injective _ _ _ _ _ _ _ _ o₁ U _ P n b hb]
    simp

/-- The natural isomorphism between ordered Čech complexes for two linear orders on the same
index type. It extends alternately using `o₁` and restricts using `o₂`. -/
def strictMonoCechComplexChangeOrder (o₁ o₂ : LinearOrder ι) :
    (letI := o₁; strictMonoCechComplexFunctor (A := A) U) ≅
      (letI := o₂; strictMonoCechComplexFunctor U) where
  hom := (letI := o₁; fromStrictMonoCechComplex U) ≫
    (letI := o₂; toStrictMonoCechComplex U)
  inv := (letI := o₂; fromStrictMonoCechComplex U) ≫
    (letI := o₁; toStrictMonoCechComplex U)
  hom_inv_id := by
    have h := congrArg (fun α ↦ α ≫ (letI := o₁; toStrictMonoCechComplex U))
      (changeOrder_absorption (A := A) U o₁ o₂)
    simpa only [Category.assoc, fromStrictMonoCechComplex_comp_toStrictMonoCechComplex] using h
  inv_hom_id := by
    have h := congrArg (fun α ↦ α ≫ (letI := o₂; toStrictMonoCechComplex U))
      (changeOrder_absorption (A := A) U o₂ o₁)
    simpa only [Category.assoc, fromStrictMonoCechComplex_comp_toStrictMonoCechComplex] using h

/-- Changing order is alternating extension followed by ordered restriction. -/
theorem strictMonoCechComplexChangeOrder_hom_def (o₁ o₂ : LinearOrder ι) :
    (strictMonoCechComplexChangeOrder (A := A) U o₁ o₂).hom =
      (letI := o₁; fromStrictMonoCechComplex U) ≫
        (letI := o₂; toStrictMonoCechComplex U) := (rfl)

/-- Reversing the change of order gives the inverse comparison. -/
@[simp]
theorem strictMonoCechComplexChangeOrder_symm (o₁ o₂ : LinearOrder ι) :
    (strictMonoCechComplexChangeOrder (A := A) U o₁ o₂).symm =
      strictMonoCechComplexChangeOrder U o₂ o₁ := by
  apply Iso.ext
  rfl

/-- Keeping the same order gives the identity isomorphism, already on complexes. -/
@[simp]
theorem strictMonoCechComplexChangeOrder_refl (o : LinearOrder ι) :
    strictMonoCechComplexChangeOrder (A := A) U o o = Iso.refl _ := by
  apply Iso.ext
  exact fromStrictMonoCechComplex_comp_toStrictMonoCechComplex U

/-- Alternating extension does not depend on the order used to present its source. -/
@[reassoc (attr := simp)]
theorem strictMonoCechComplexChangeOrder_hom_comp_from (o₁ o₂ : LinearOrder ι) :
    (strictMonoCechComplexChangeOrder (A := A) U o₁ o₂).hom ≫
        (letI := o₂; fromStrictMonoCechComplex U) =
      (letI := o₁; fromStrictMonoCechComplex U) :=
  (Category.assoc _ _ _).trans (changeOrder_absorption U o₁ o₂)

/-- Changes of order compose strictly: no homotopy correction is needed. -/
@[simp]
theorem strictMonoCechComplexChangeOrder_trans (o₁ o₂ o₃ : LinearOrder ι) :
    (strictMonoCechComplexChangeOrder (A := A) U o₁ o₂).trans
        (strictMonoCechComplexChangeOrder U o₂ o₃) =
      strictMonoCechComplexChangeOrder U o₁ o₃ := by
  apply Iso.ext
  simp only [Iso.trans_hom, strictMonoCechComplexChangeOrder_hom_def]
  have h := congrArg (fun α ↦ α ≫ (letI := o₃; toStrictMonoCechComplex U))
    (changeOrder_absorption (A := A) U o₁ o₂)
  simpa only [Category.assoc] using h

/-- The coordinate of the change-of-order map at an `o₂`-increasing tuple is the coordinate of
its `o₁`-increasing rearrangement, with the inversion sign of that rearrangement. -/
@[reassoc]
theorem strictMonoCechComplexChangeOrder_hom_app_f_π (o₁ o₂ : LinearOrder ι)
    (P : Cᵒᵖ ⥤ A) (n : ℕ)
    (b : {b : Fin (n + 1) → ι // @StrictMono _ _ _ o₂.toPartialOrder.toPreorder b}) :
    ((strictMonoCechComplexChangeOrder U o₁ o₂).hom.app P).f n ≫
        (letI := o₂; strictMonoCechComplexπ U P b) =
      (-1 : ℤ) ^ #(@Finset.inversions _ _ _ o₁ b.1 univ) •
        ((letI := o₁; strictMonoCechComplexπ U P
            ⟨b.1 ∘ Tuple.sort b.1, Tuple.strictMono_comp_sort (letI := o₂; b.2.injective)⟩) ≫
          P.map (Pi.lift fun j ↦ Pi.π (fun j ↦ U (b.1 j))
            (@Tuple.sort _ _ o₁ b.1 j)).op) := by
  rw [strictMonoCechComplexChangeOrder_hom_def]
  simp only [NatTrans.comp_app, HomologicalComplex.comp_f]
  -- Unfold the native tuple-product presentation to apply its coordinate formulas.
  erw [Category.assoc, toStrictMonoCechComplex_app_f_π,
    @fromStrictMonoCechComplex_app_f_π _ _ _ _ _ _ _ _ o₁ U _ P n b.1 (letI := o₂; b.2.injective)]

end TauCeti.CategoryTheory
