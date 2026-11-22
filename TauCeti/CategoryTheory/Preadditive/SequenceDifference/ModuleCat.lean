/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Shift.Basic
public import TauCeti.Algebra.Category.ModuleCat.Products
public import TauCeti.Algebra.Category.ModuleCat.Tower.Basic
public import TauCeti.CategoryTheory.Preadditive.SequenceDifference.Basic

/-!
# Sequence–difference maps and `ModuleCat`-valued contravariant functors

Given a sequence `X : ℕ ⥤ T` in a preadditive category and an additive contravariant functor
`F : Tᵒᵖ ⥤ ModuleCat.{s} R` preserving the countable product of `fun n ↦ op (X.obj n)`, the
coordinate linear equivalence `IsColimit.cofanOpToPiLinearEquiv` identifies the action of
`X.sequenceDifference` (and its shift `(X.sequenceDifference)⟦(1 : ℤ)⟧'`) on `F.obj (op (∐ X.obj))`
with `ModuleTower.shift` on `X.op ⋙ F` (respectively `(X ⋙ shiftFunctor T (1 : ℤ)).op ⋙ F`).

## Main definitions

* `CategoryTheory.Functor.isColimitShiftedCoproductCofan`

## Main results

* `CategoryTheory.Functor.map_op_comp_apply`
* `CategoryTheory.Functor.cofanOpToPiLinearEquiv_map_of_isColimit`,
  `CategoryTheory.Functor.cofanOpToPiLinearEquiv_map_sequenceDifference`,
  `CategoryTheory.Functor.cofanOpToPiLinearEquiv_map_shift_sequenceDifference`
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TauCeti

universe uR s v u

namespace CategoryTheory.Functor

section ConcreteApply

/-- Evaluating `F.map (f ≫ g).op` on `u` for a contravariant functor `F : Tᵒᵖ ⥤ D` into a concrete
category equals `F.map f.op (F.map g.op u)`. -/
theorem map_op_comp_apply {T : Type*} [Category T] {D : Type*} [Category D]
    {FD : D → D → Type*} {CD : D → Type*} [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)]
    [ConcreteCategory D FD] (F : Tᵒᵖ ⥤ D) {X Y Z : T} (f : X ⟶ Y) (g : Y ⟶ Z)
    (u : CD (F.obj (op Z))) :
    F.map (f ≫ g).op u = F.map f.op (F.map g.op u) := by
  rw [op_comp, F.map_comp, CategoryTheory.comp_apply]

end ConcreteApply

section ModuleCatSequenceDifference

variable {T : Type u} [Category.{v} T] [Preadditive T]

/-- Coordinatewise, for any additive `F : Tᵒᵖ ⥤ ModuleCat.{s} R` and any colimit cofan `c` over
`Y : ℕ ⥤ T` whose dual product is preserved by `F`, an endomorphism `d : c.pt ⟶ c.pt` satisfying
`c.inj n ≫ d = c.inj n - Y.map (homOfLE _) ≫ c.inj (n + 1)` corresponds under
`cofanOpToPiLinearEquiv` to `ModuleTower.shift (Y.op ⋙ F)`. -/
theorem cofanOpToPiLinearEquiv_map_of_isColimit {R : Type uR} [Ring R]
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
  cofanOpToPiLinearEquiv_map_of_isColimit F X (coproductIsCoproduct X.obj)
    X.sequenceDifference (fun n ↦ by simp) x

section Shift

variable [HasShift T ℤ]

/-- The shifted coproduct cofan for `X ⋙ shiftFunctor T (1 : ℤ)` with vertex `(∐ X.obj)⟦1⟧` and
inclusions `(Sigma.ι X.obj n)⟦1⟧'` is a colimit cofan, since `shiftFunctor T (1 : ℤ)` is an
equivalence and hence preserves coproducts. -/
def isColimitShiftedCoproductCofan (X : ℕ ⥤ T) [HasCoproduct X.obj] :
    IsColimit (Cofan.mk (f := (X ⋙ shiftFunctor T (1 : ℤ)).obj) ((∐ X.obj)⟦(1 : ℤ)⟧)
      fun n ↦ (Sigma.ι X.obj n)⟦(1 : ℤ)⟧') :=
  (isColimitMapCoconeCofanMkEquiv (shiftFunctor T (1 : ℤ)) X.obj (Sigma.ι X.obj)).toFun
    (isColimitOfPreserves (shiftFunctor T (1 : ℤ)) (coproductIsCoproduct X.obj))

private theorem shifted_ι_sequenceDifference [(shiftFunctor T (1 : ℤ)).Additive]
    (X : ℕ ⥤ T) [HasCoproduct X.obj] (n : ℕ) :
    (Sigma.ι X.obj n)⟦(1 : ℤ)⟧' ≫ (X.sequenceDifference)⟦(1 : ℤ)⟧' =
      (Sigma.ι X.obj n)⟦(1 : ℤ)⟧' -
        (X.map (homOfLE (n.le_add_right 1)))⟦(1 : ℤ)⟧' ≫ (Sigma.ι X.obj (n + 1))⟦(1 : ℤ)⟧' := by
  rw [← Functor.map_comp, X.ι_sequenceDifference, Functor.map_sub, Functor.map_comp]

/-- Coordinatewise, `F.map ((X.sequenceDifference)⟦(1 : ℤ)⟧').op` corresponds under
`cofanOpToPiLinearEquiv` to `ModuleTower.shift ((X ⋙ shiftFunctor T (1 : ℤ)).op ⋙ F)`. -/
theorem cofanOpToPiLinearEquiv_map_shift_sequenceDifference {R : Type uR} [Ring R]
    (F : Tᵒᵖ ⥤ ModuleCat.{s} R) [F.Additive] [(shiftFunctor T (1 : ℤ)).Additive]
    (X : ℕ ⥤ T) [HasCoproduct X.obj]
    [PreservesLimit (Discrete.functor fun n ↦ op ((X ⋙ shiftFunctor T (1 : ℤ)).obj n)) F]
    (y : F.obj (op ((∐ X.obj)⟦(1 : ℤ)⟧))) :
    (isColimitShiftedCoproductCofan X).cofanOpToPiLinearEquiv F
        (F.map ((X.sequenceDifference)⟦(1 : ℤ)⟧').op y) =
      ModuleTower.shift ((X ⋙ shiftFunctor T (1 : ℤ)).op ⋙ F)
        ((isColimitShiftedCoproductCofan X).cofanOpToPiLinearEquiv F y) :=
  cofanOpToPiLinearEquiv_map_of_isColimit F (X ⋙ shiftFunctor T (1 : ℤ))
    (isColimitShiftedCoproductCofan X) ((X.sequenceDifference)⟦(1 : ℤ)⟧')
    (fun n ↦ X.shifted_ι_sequenceDifference n) y

end Shift

end ModuleCatSequenceDifference

end CategoryTheory.Functor
