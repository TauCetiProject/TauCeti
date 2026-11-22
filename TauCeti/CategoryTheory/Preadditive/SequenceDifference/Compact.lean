/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Colimits
public import TauCeti.CategoryTheory.Preadditive.Compact
public import TauCeti.CategoryTheory.Preadditive.SequenceDifference.Basic

/-!
# Sequence–difference maps and compact objects

This module links `CategoryTheory.Functor.sequenceDifference` with objects `A` whose corepresented
functor `preadditiveCoyoneda.obj (op A)` preserves countable (or `X.obj`-shaped) coproducts.

* `TauCeti.compactSeqDirectSumEquiv`: identifies `⨁ n, ↑((X ⋙ preadditiveCoyonedaObj A).obj n)`
  additively with `A ⟶ ∐ X.obj`, intertwining `ModuleCat.telescopeDiff` with postcomposition by
  `X.sequenceDifference` (`TauCeti.compactSeqDirectSumEquiv_telescopeDiff`).
* `TauCeti.injective_comp_sequenceDifference`,
  `TauCeti.injective_comp_shift_sequenceDifference`: postcomposition with `X.sequenceDifference`
  and `(X.sequenceDifference)⟦(1 : ℤ)⟧'` is injective on morphisms out of `A`.

## Main definitions

* `TauCeti.compactSeqDirectSumEquiv`

## Main results

* `TauCeti.compactSeqDirectSumEquiv_of`, `TauCeti.compactSeqDirectSumEquiv_lof`,
  `TauCeti.compactSeqDirectSumEquiv_telescopeDiff`
* `TauCeti.injective_comp_sequenceDifference`,
  `TauCeti.injective_comp_shift_sequenceDifference`
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped DirectSum

universe v u

namespace TauCeti

section SequenceDifferenceCompact

variable {T : Type u} [Category.{v} T] [Preadditive T]

private def coyonedaToHom (A : T) (X : ℕ ⥤ T) (k : ℕ) :
    ↑((X ⋙ preadditiveCoyonedaObj A).obj k) ≃+ (A ⟶ X.obj k) :=
  { toFun := id, invFun := id, left_inv := fun _ ↦ rfl, right_inv := fun _ ↦ rfl,
    map_add' := fun _ _ ↦ rfl }

private def seqDirectSumEquiv (A : T) (X : ℕ ⥤ T) :
    (⨁ n, ↑((X ⋙ preadditiveCoyonedaObj A).obj n)) ≃+ (⨁ n, (A ⟶ X.obj n)) :=
  DFinsupp.mapRange.addEquiv (coyonedaToHom A X)

private theorem seqDirectSumEquiv_of (A : T) (X : ℕ ⥤ T) (n : ℕ)
    (g : ↑((X ⋙ preadditiveCoyonedaObj A).obj n)) :
    seqDirectSumEquiv A X
        (DirectSum.of (fun k ↦ ↑((X ⋙ preadditiveCoyonedaObj A).obj k)) n g) =
      DirectSum.of (fun k ↦ A ⟶ X.obj k) n (coyonedaToHom A X n g) :=
  DFinsupp.mapRange_single (f := fun k ↦ coyonedaToHom A X k) (hf := fun _ ↦ rfl) (i := n)

/-- For `A` such that `Hom(A, -)` preserves `∐ X.obj`, the composite additive equivalence
identifying the telescope domain `⨁ n, ↑((X ⋙ preadditiveCoyonedaObj A).obj n)` with
`A ⟶ ∐ X.obj`. -/
def compactSeqDirectSumEquiv (A : T) (X : ℕ ⥤ T) [HasCoproduct X.obj]
    [PreservesColimit (Discrete.functor X.obj) (preadditiveCoyoneda.obj (op A))] :
    (⨁ n, ↑((X ⋙ preadditiveCoyonedaObj A).obj n)) ≃+ (A ⟶ ∐ X.obj) :=
  (seqDirectSumEquiv A X).trans <|
    AddEquiv.ofBijective (coprodComparisonAddHom A X.obj)
      ((preservesColimit_discrete_preadditiveCoyoneda_iff A X.obj).1 inferInstance)

theorem compactSeqDirectSumEquiv_of (A : T) (X : ℕ ⥤ T) [HasCoproduct X.obj]
    [PreservesColimit (Discrete.functor X.obj) (preadditiveCoyoneda.obj (op A))]
    (n : ℕ) (g : ↑((X ⋙ preadditiveCoyonedaObj A).obj n)) :
    compactSeqDirectSumEquiv A X
        (DirectSum.of (fun k ↦ ↑((X ⋙ preadditiveCoyonedaObj A).obj k)) n g) =
      (g : A ⟶ X.obj n) ≫ Sigma.ι X.obj n := by
  dsimp only [compactSeqDirectSumEquiv, AddEquiv.trans_apply]
  rw [AddEquiv.ofBijective_apply, seqDirectSumEquiv_of, coprodComparisonAddHom_of]
  rfl

theorem compactSeqDirectSumEquiv_lof (A : T) (X : ℕ ⥤ T) [HasCoproduct X.obj]
    [PreservesColimit (Discrete.functor X.obj) (preadditiveCoyoneda.obj (op A))]
    (n : ℕ) (g : ↑((X ⋙ preadditiveCoyonedaObj A).obj n)) :
    compactSeqDirectSumEquiv A X
        (DirectSum.lof (End A)ᵐᵒᵖ ℕ (fun k ↦ ↑((X ⋙ preadditiveCoyonedaObj A).obj k)) n g) =
      (g : A ⟶ X.obj n) ≫ Sigma.ι X.obj n := by
  rw [DirectSum.lof_eq_of, compactSeqDirectSumEquiv_of]

/-- Under `compactSeqDirectSumEquiv A X`, `ModuleCat.telescopeDiff` on
`X ⋙ preadditiveCoyonedaObj A` corresponds to postcomposition with `X.sequenceDifference`. -/
theorem compactSeqDirectSumEquiv_telescopeDiff (A : T) (X : ℕ ⥤ T) [HasCoproduct X.obj]
    [PreservesColimit (Discrete.functor X.obj) (preadditiveCoyoneda.obj (op A))]
    (a : ⨁ n, ↑((X ⋙ preadditiveCoyonedaObj A).obj n)) :
    compactSeqDirectSumEquiv A X (ModuleCat.telescopeDiff (X ⋙ preadditiveCoyonedaObj A) a) =
      compactSeqDirectSumEquiv A X a ≫ X.sequenceDifference := by
  induction a using DirectSum.induction_on with
  | zero => simp
  | of n g =>
    let g' : A ⟶ X.obj n := g
    have hsub : (g' ≫ Sigma.ι X.obj n) ≫ X.sequenceDifference =
        g' ≫ Sigma.ι X.obj n -
          (g' ≫ X.map (homOfLE (n.le_add_right 1))) ≫ Sigma.ι X.obj (n + 1) := by
      rw [Category.assoc, X.ι_sequenceDifference, Preadditive.comp_sub, Category.assoc]
    rw [← DirectSum.lof_eq_of (End A)ᵐᵒᵖ, ModuleCat.telescopeDiff_lof, map_sub]
    refine (congrArg₂ (· - ·) (compactSeqDirectSumEquiv_lof A X n g)
      (compactSeqDirectSumEquiv_lof A X (n + 1) _)).trans ?_
    exact hsub.symm.trans (congrArg (· ≫ X.sequenceDifference)
      (compactSeqDirectSumEquiv_of A X n g).symm)
  | add a b ha hb =>
    rw [map_add, map_add, map_add, Preadditive.add_comp, ha, hb]

/-- If `Hom(A, -)` preserves `∐ X.obj`, then postcomposition with `X.sequenceDifference` is
injective on `A ⟶ ∐ X.obj`. -/
theorem injective_comp_sequenceDifference {A : T} (X : ℕ ⥤ T) [HasCoproduct X.obj]
    [PreservesColimit (Discrete.functor X.obj) (preadditiveCoyoneda.obj (op A))] :
    Function.Injective (fun g : A ⟶ ∐ X.obj ↦ g ≫ X.sequenceDifference) := fun g₁ g₂ hg ↦ by
  dsimp only at hg
  obtain ⟨a₁, rfl⟩ := (compactSeqDirectSumEquiv A X).surjective g₁
  obtain ⟨a₂, rfl⟩ := (compactSeqDirectSumEquiv A X).surjective g₂
  rw [← compactSeqDirectSumEquiv_telescopeDiff, ← compactSeqDirectSumEquiv_telescopeDiff] at hg
  exact congrArg (compactSeqDirectSumEquiv A X) <|
    ModuleCat.telescopeDiff_injective (X ⋙ preadditiveCoyonedaObj A)
      ((compactSeqDirectSumEquiv A X).injective hg)

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
  have := preservesColimitsOfShape_preadditiveCoyoneda_shift (Discrete ℕ) A (-1 : ℤ)
  let ε := (shiftFunctorCompIsoId T (1 : ℤ) (-1 : ℤ) (add_neg_cancel 1)).hom
  have hnat : ((X.sequenceDifference)⟦(1 : ℤ)⟧')⟦(-1 : ℤ)⟧' ≫ ε.app (∐ X.obj) =
      ε.app (∐ X.obj) ≫ X.sequenceDifference := ε.naturality _
  have h1 : (g₁⟦(-1 : ℤ)⟧' ≫ ε.app (∐ X.obj)) ≫ X.sequenceDifference =
      (g₂⟦(-1 : ℤ)⟧' ≫ ε.app (∐ X.obj)) ≫ X.sequenceDifference := by
    rw [Category.assoc, ← hnat, ← Functor.map_comp_assoc, hg, Functor.map_comp_assoc, hnat,
      ← Category.assoc]
  exact (shiftFunctor T (-1 : ℤ)).map_injective
    ((cancel_mono (ε.app (∐ X.obj))).1 (injective_comp_sequenceDifference X h1))

end Shift

end SequenceDifferenceCompact

end TauCeti
