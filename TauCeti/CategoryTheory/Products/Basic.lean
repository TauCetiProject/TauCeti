/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

/-!
# Basic structures on product categories

This file supplies componentwise smallness and zero objects for Cartesian product categories.
-/

public section

open CategoryTheory

namespace TauCeti

open Limits ZeroObject

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- The product of essentially small categories is essentially small. -/
noncomputable instance [EssentiallySmall.{w₁} C] [EssentiallySmall.{w₂} D] :
    EssentiallySmall.{max w₁ w₂} (C × D) :=
  EssentiallySmall.mk' ((equivSmallModel C).prod (equivSmallModel D))

/-- A pair of zero objects is a zero object of the product category. -/
instance [HasZeroObject C] [HasZeroObject D] : HasZeroObject (C × D) where
  zero := ⟨(0, 0),
    { unique_to := fun X =>
        ⟨⟨⟨(isZero_zero C).to_ X.1, (isZero_zero D).to_ X.2⟩, fun f => by
            exact Prod.hom_ext ((isZero_zero C).eq_of_src _ _)
              ((isZero_zero D).eq_of_src _ _)⟩⟩
      unique_from := fun X =>
        ⟨⟨⟨(isZero_zero C).from_ X.1, (isZero_zero D).from_ X.2⟩, fun f => by
            exact Prod.hom_ext ((isZero_zero C).eq_of_tgt _ _)
              ((isZero_zero D).eq_of_tgt _ _)⟩⟩ } ⟩

end TauCeti
