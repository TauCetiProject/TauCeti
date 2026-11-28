/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Products
public import TauCeti.Algebra.Category.ModuleCat.Tower.Basic
public import TauCeti.CategoryTheory.Preadditive.SequenceDifference.Basic
public import TauCeti.CategoryTheory.Shift.Limits

import TauCeti.CategoryTheory.ConcreteCategory.Basic

/-!
# Sequence–difference maps and `ModuleCat`-valued contravariant functors

Given a sequence `X : ℕ ⥤ T` in a preadditive category and an additive contravariant functor
`F : Tᵒᵖ ⥤ ModuleCat.{s} R` preserving the countable product of `fun n ↦ op (X.obj n)`, the
coordinate linear equivalence `IsColimit.cofanOpToPiLinearEquiv` identifies the action of
`X.sequenceDifference` (and its shift `(X.sequenceDifference)⟦(1 : ℤ)⟧'`) on `F.obj (op (∐ X.obj))`
with `ModuleTower.shift` on `X.op ⋙ F` (respectively `(X ⋙ shiftFunctor T (1 : ℤ)).op ⋙ F`).

## Main results

* `CategoryTheory.Functor.cofanOpToPiLinearEquiv_map_eq_shift`,
  `CategoryTheory.Functor.cofanOpToPiLinearEquiv_map_sequenceDifference`,
  `CategoryTheory.Functor.cofanOpToPiLinearEquiv_map_shift_sequenceDifference`
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TauCeti

universe uR s v u

namespace CategoryTheory.Functor

section ModuleCatSequenceDifference

variable {T : Type u} [Category.{v} T] [Preadditive T]

/-- Coordinatewise, for any additive `F : Tᵒᵖ ⥤ ModuleCat.{s} R` and any colimit cofan `c` over
`Y : ℕ ⥤ T` whose dual product is preserved by `F`, an endomorphism `d : c.pt ⟶ c.pt` satisfying
`c.inj n ≫ d = c.inj n - Y.map (homOfLE _) ≫ c.inj (n + 1)` corresponds under
`cofanOpToPiLinearEquiv` to `ModuleTower.shift (Y.op ⋙ F)`. -/
theorem cofanOpToPiLinearEquiv_map_eq_shift {R : Type uR} [Ring R]
    (F : Tᵒᵖ ⥤ ModuleCat.{s} R) [F.Additive] (Y : ℕ ⥤ T) {c : Cofan Y.obj}
    (hc : IsColimit c) [PreservesLimit (Discrete.functor fun n ↦ op (Y.obj n)) F]
    (d : c.pt ⟶ c.pt)
    (hd : ∀ n, c.inj n ≫ d = c.inj n - Y.map (homOfLE (n.le_add_right 1)) ≫ c.inj (n + 1))
    (x : F.obj (op c.pt)) :
    hc.cofanOpToPiLinearEquiv F (F.map d.op x) =
      ModuleTower.shift (Y.op ⋙ F) (hc.cofanOpToPiLinearEquiv F x) := by
  funext n
  have h := congrArg (fun φ ↦ F.map φ.op x) (hd n)
  simp only [map_op_comp_apply, op_sub, F.map_sub, ModuleCat.hom_sub, LinearMap.sub_apply] at h
  simpa [ModuleTower.transition_def] using h

/-- Coordinatewise, `F.map X.sequenceDifference.op` corresponds under
`cofanOpToPiLinearEquiv` to `ModuleTower.shift (X.op ⋙ F)`. -/
theorem cofanOpToPiLinearEquiv_map_sequenceDifference {R : Type uR} [Ring R]
    (F : Tᵒᵖ ⥤ ModuleCat.{s} R) [F.Additive] (X : ℕ ⥤ T) [HasCoproduct X.obj]
    [PreservesLimit (Discrete.functor fun n ↦ op (X.obj n)) F]
    (x : F.obj (op (∐ X.obj))) :
    (coproductIsCoproduct X.obj).cofanOpToPiLinearEquiv F (F.map X.sequenceDifference.op x) =
      ModuleTower.shift (X.op ⋙ F)
        ((coproductIsCoproduct X.obj).cofanOpToPiLinearEquiv F x) :=
  cofanOpToPiLinearEquiv_map_eq_shift F X (coproductIsCoproduct X.obj)
    X.sequenceDifference (fun n ↦ by simp) x

section Shift

variable [HasShift T ℤ]

/-- Coordinatewise, `F.map ((X.sequenceDifference)⟦(1 : ℤ)⟧').op` corresponds under
`cofanOpToPiLinearEquiv` to `ModuleTower.shift ((X ⋙ shiftFunctor T (1 : ℤ)).op ⋙ F)`. -/
theorem cofanOpToPiLinearEquiv_map_shift_sequenceDifference {R : Type uR} [Ring R]
    (F : Tᵒᵖ ⥤ ModuleCat.{s} R) [F.Additive] [(shiftFunctor T (1 : ℤ)).Additive]
    (X : ℕ ⥤ T) [HasCoproduct X.obj]
    [PreservesLimit (Discrete.functor fun n ↦ op ((X.obj n)⟦(1 : ℤ)⟧)) F]
    (y : F.obj (op ((∐ X.obj)⟦(1 : ℤ)⟧))) :
    (isColimitShiftedCoproductCofan X.obj (1 : ℤ)).cofanOpToPiLinearEquiv F
        (F.map ((X.sequenceDifference)⟦(1 : ℤ)⟧').op y) =
      ModuleTower.shift ((X ⋙ shiftFunctor T (1 : ℤ)).op ⋙ F)
        ((isColimitShiftedCoproductCofan X.obj (1 : ℤ)).cofanOpToPiLinearEquiv F y) := by
  let : PreservesLimit (Discrete.functor fun n ↦ op ((X ⋙ shiftFunctor T (1 : ℤ)).obj n)) F :=
    ‹_›
  exact cofanOpToPiLinearEquiv_map_eq_shift F (X ⋙ shiftFunctor T (1 : ℤ))
    (isColimitShiftedCoproductCofan X.obj (1 : ℤ)) ((X.sequenceDifference)⟦(1 : ℤ)⟧')
    (X.map_ι_comp_map_sequenceDifference (shiftFunctor T (1 : ℤ))) y

end Shift

end ModuleCatSequenceDifference

end CategoryTheory.Functor
