/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.CategoryTheory.Abelian.Opposite

import TauCeti.Algebra.Homology.DerivedCategory.Opposite

/-!
# Ext in opposite abelian categories

Opposition exchanges the two objects of an Ext group and preserves its degree. This
identifies projective and injective dimension bounds across opposite abelian categories
(Mitchell, *Rings with several objects*, §9, p. 42).
-/

public section

open CategoryTheory Opposite DerivedCategory

namespace CategoryTheory.Abelian.Ext

variable {C : Type*} [Category* C] [Abelian C] [HasExt.{w₁} C] [HasExt.{w₂} Cᵒᵖ]

/-- Reversing arrows identifies `Extⁿ(X, Y)` with `Extⁿ(op Y, op X)` in the opposite category. -/
noncomputable def opAddEquiv (X Y : C) (n : ℕ) :
    Ext.{w₁} X Y n ≃+ Ext.{w₂} (op Y) (op X) n := by
  letI := HasDerivedCategory.standard C
  letI := HasDerivedCategory.standard Cᵒᵖ
  let e := DerivedCategory.opEquivalence C
  letI := e.functor.additive_of_preserves_binary_products
  -- Write the Ext class as a map from degree zero to a single complex in degree `-n`.
  let i := ((singleFunctors C).shiftIso (n : ℤ) (-(n : ℤ)) 0 (by simp)).app Y
  let j : e.functor.obj (op ((singleFunctor C (-(n : ℤ))).obj Y)) ≅
      (singleFunctor Cᵒᵖ (n : ℤ)).obj (op Y) := by
    simpa only [neg_neg] using opEquivalenceSingleIso C (-(n : ℤ)) Y
  let k : e.functor.obj (op ((singleFunctor C 0).obj X)) ≅
      (singleFunctor Cᵒᵖ 0).obj (op X) := by
    simpa only [neg_zero] using opEquivalenceSingleIso C 0 X
  -- In the opposite category, shift the resulting degree-`n` source back to degree zero.
  let s := ((singleFunctors Cᵒᵖ).shiftIso (n : ℤ) 0 (n : ℤ) (by simp)).app (op Y)
  let shift := Functor.FullyFaithful.ofFullyFaithful (shiftFunctor (DerivedCategory Cᵒᵖ) (n : ℤ))
  let equiv : Ext.{w₁} X Y n ≃ Ext.{w₂} (op Y) (op X) n :=
    homAddEquiv.toEquiv
      |>.trans i.homToEquiv
      |>.trans (CategoryTheory.opEquiv _ _).symm
      |>.trans e.fullyFaithfulFunctor.homEquiv
      |>.trans j.homFromEquiv
      |>.trans k.homToEquiv
      |>.trans shift.homEquiv
      |>.trans s.homFromEquiv
      |>.trans homAddEquiv.symm.toEquiv
  refine { toEquiv := equiv, map_add' := ?_ }
  intro a b
  simp [equiv, shift, Iso.homToEquiv, Iso.homFromEquiv, CategoryTheory.opEquiv,
    Preadditive.add_comp, Preadditive.comp_add]

end CategoryTheory.Abelian.Ext
