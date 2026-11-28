/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Colimits
public import TauCeti.CategoryTheory.Preadditive.Compact
public import TauCeti.CategoryTheory.Preadditive.SequenceDifference.Basic

import TauCeti.CategoryTheory.Preadditive.Yoneda

/-!
# Sequence–difference maps and compact objects

This module links `CategoryTheory.Functor.sequenceDifference` with objects `A` whose corepresented
functor `preadditiveCoyoneda.obj (op A)` preserves countable (or `X.obj`-shaped) coproducts.

* `TauCeti.coprodComparisonAddEquiv_telescopeDiff`: `TauCeti.coprodComparisonAddEquiv A X.obj`
  intertwines `ModuleCat.telescopeDiff` with postcomposition by `X.sequenceDifference`.
* `CategoryTheory.Functor.injective_comp_sequenceDifference`,
  `CategoryTheory.Functor.injective_comp_shift_sequenceDifference`: postcomposition with
  `X.sequenceDifference` and `(X.sequenceDifference)⟦(1 : ℤ)⟧'` is injective on morphisms out of
  `A`.

## Main results

* `TauCeti.coprodComparisonAddEquiv_telescopeDiff`
* `CategoryTheory.Functor.injective_comp_sequenceDifference`,
  `CategoryTheory.Functor.injective_comp_shift_sequenceDifference`
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped DirectSum

universe v u

section SequenceDifferenceCompact

variable {T : Type u} [Category.{v} T] [Preadditive T]

namespace TauCeti

/-- Under `coprodComparisonAddEquiv A X.obj`, `ModuleCat.telescopeDiff` on
`X ⋙ preadditiveCoyonedaObj A` corresponds to postcomposition with `X.sequenceDifference`. -/
theorem coprodComparisonAddEquiv_telescopeDiff (A : T) (X : ℕ ⥤ T) [HasCoproduct X.obj]
    [PreservesColimit (Discrete.functor X.obj) (preadditiveCoyoneda.obj (op A))]
    (a : ⨁ n, (A ⟶ X.obj n)) :
    coprodComparisonAddEquiv A X.obj (ModuleCat.telescopeDiff (X ⋙ preadditiveCoyonedaObj A) a) =
      coprodComparisonAddEquiv A X.obj a ≫ X.sequenceDifference := by
  -- Wrap `ModuleCat.telescopeDiff (X ⋙ preadditiveCoyonedaObj A)` at `⨁ n, (A ⟶ X.obj n)` so
  -- `DirectSum.induction_on` sees the same `AddCommMonoid` instance as `coprodComparisonAddEquiv`.
  let D : (⨁ n, (A ⟶ X.obj n)) →+ (⨁ n, (A ⟶ X.obj n)) :=
    { toFun := ModuleCat.telescopeDiff (X ⋙ preadditiveCoyonedaObj A)
      map_zero' := (ModuleCat.telescopeDiff (X ⋙ preadditiveCoyonedaObj A)).map_zero
      map_add' := (ModuleCat.telescopeDiff (X ⋙ preadditiveCoyonedaObj A)).map_add }
  have h : coprodComparisonAddEquiv A X.obj (D a) =
      coprodComparisonAddEquiv A X.obj a ≫ X.sequenceDifference := by
    induction a using DirectSum.induction_on with
    | zero => simp
    | of n g =>
      have hD : D (DirectSum.of (fun k ↦ A ⟶ X.obj k) n g) =
          DirectSum.of (fun k ↦ A ⟶ X.obj k) n g -
            DirectSum.of (fun k ↦ A ⟶ X.obj k) (n + 1)
              (g ≫ X.map (homOfLE (n.le_add_right 1))) := by
        have hlof := ModuleCat.telescopeDiff_lof (X ⋙ preadditiveCoyonedaObj A) n g
        simp only [DirectSum.lof_eq_of] at hlof
        simp only [Functor.comp_obj, Functor.comp_map, preadditiveCoyonedaObj_map_apply] at hlof
        exact hlof
      have hsub : (preadditiveCoyoneda.obj (op A)).map X.sequenceDifference
          ((preadditiveCoyoneda.obj (op A)).map (Sigma.ι X.obj n) g) =
          (preadditiveCoyoneda.obj (op A)).map (Sigma.ι X.obj n) g -
            (preadditiveCoyoneda.obj (op A)).map (Sigma.ι X.obj (n + 1))
              ((preadditiveCoyoneda.obj (op A)).map (X.map (homOfLE (n.le_add_right 1))) g) :=
        ConcreteCategory.congr_hom
          (X.map_ι_comp_map_sequenceDifference (preadditiveCoyoneda.obj (op A)) n) g
      simp only [preadditiveCoyoneda_obj_map_apply] at hsub
      rw [hD, map_sub, coprodComparisonAddEquiv_of, coprodComparisonAddEquiv_of]
      exact hsub.symm
    | add a b ha hb => simp [map_add, ha, hb, Preadditive.add_comp]
  exact h

end TauCeti

namespace CategoryTheory.Functor

/-- If `Hom(A, -)` preserves `∐ X.obj`, then postcomposition with `X.sequenceDifference` is
injective on `A ⟶ ∐ X.obj`. -/
theorem injective_comp_sequenceDifference {A : T} (X : ℕ ⥤ T) [HasCoproduct X.obj]
    [PreservesColimit (Discrete.functor X.obj) (preadditiveCoyoneda.obj (op A))] :
    Function.Injective (fun g : A ⟶ ∐ X.obj ↦ g ≫ X.sequenceDifference) := fun g₁ g₂ hg ↦ by
  dsimp only at hg
  obtain ⟨a₁, rfl⟩ := (TauCeti.coprodComparisonAddEquiv A X.obj).surjective g₁
  obtain ⟨a₂, rfl⟩ := (TauCeti.coprodComparisonAddEquiv A X.obj).surjective g₂
  rw [← TauCeti.coprodComparisonAddEquiv_telescopeDiff,
    ← TauCeti.coprodComparisonAddEquiv_telescopeDiff] at hg
  exact congrArg (TauCeti.coprodComparisonAddEquiv A X.obj) <|
    ModuleCat.telescopeDiff_injective (X ⋙ preadditiveCoyonedaObj A)
      ((TauCeti.coprodComparisonAddEquiv A X.obj).injective hg)

section Shift

variable [HasShift T ℤ] [∀ n : ℤ, (shiftFunctor T n).Additive]

/-- If `Hom(A, -)` preserves countable coproducts, then postcomposition with the shifted
sequence–difference map `(X.sequenceDifference)⟦(1 : ℤ)⟧'` is injective on
`A ⟶ (∐ X.obj)⟦(1 : ℤ)⟧`. -/
theorem injective_comp_shift_sequenceDifference {A : T} (X : ℕ ⥤ T) [HasCoproduct X.obj]
    [PreservesColimitsOfShape (Discrete ℕ) (preadditiveCoyoneda.obj (op A))] :
    Function.Injective (fun g : A ⟶ (∐ X.obj)⟦(1 : ℤ)⟧ ↦
      g ≫ (X.sequenceDifference)⟦(1 : ℤ)⟧') := fun g₁ g₂ hg ↦ by
  dsimp only at hg
  have := TauCeti.preservesColimitsOfShape_preadditiveCoyoneda_shift (Discrete ℕ) A (-1 : ℤ)
  let ε := (shiftFunctorCompIsoId T (1 : ℤ) (-1 : ℤ) (add_neg_cancel 1)).hom
  have hnat : ((X.sequenceDifference)⟦(1 : ℤ)⟧')⟦(-1 : ℤ)⟧' ≫ ε.app (∐ X.obj) =
      ε.app (∐ X.obj) ≫ X.sequenceDifference := ε.naturality _
  have h1 : (g₁⟦(-1 : ℤ)⟧' ≫ ε.app (∐ X.obj)) ≫ X.sequenceDifference =
      (g₂⟦(-1 : ℤ)⟧' ≫ ε.app (∐ X.obj)) ≫ X.sequenceDifference := by
    rw [Category.assoc, ← hnat, ← Functor.map_comp_assoc, hg, Functor.map_comp_assoc, hnat,
      ← Category.assoc]
  exact (shiftFunctor T (-1 : ℤ)).map_injective
    ((cancel_mono (ε.app (∐ X.obj))).1 (X.injective_comp_sequenceDifference h1))

end Shift

end CategoryTheory.Functor

end SequenceDifferenceCompact
