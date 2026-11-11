/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Preorder

/-!
# Functors preserving well-order-continuous colimits

A functor `G` satisfies `PreservesWellOrderContinuousOfShape J G` when it preserves the colimits
of shape `Set.Iio j` for the limit elements `j` of the linear order `J`. This is what is needed to
transport a transfinite composition of shape `J` along `G`
(`CategoryTheory.TransfiniteCompositionOfShape.map`). This file records two sources of such
functors:

* every functor preserving all colimits of the relevant size, for instance every left adjoint
  (`CategoryTheory.Limits.preservesWellOrderContinuousOfShape_of_preservesColimitsOfSize`);
* the forgetful functor `Under X ⥤ C`
  (`CategoryTheory.Under.preservesWellOrderContinuousOfShape_forget`): a limit element `j` is not
  minimal, so `Set.Iio j` is a nonempty linear order, hence a connected category, and the forgetful
  functor preserves connected colimits.
-/

public section

universe w v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] (J : Type w) [LinearOrder J]

/-- A functor preserving all colimits indexed by categories in the universe of `J` preserves the
colimits defining well-order continuity for `J`; this applies to every left adjoint. -/
instance Limits.preservesWellOrderContinuousOfShape_of_preservesColimitsOfSize {D : Type*}
    [Category* D] (G : C ⥤ D) [PreservesColimitsOfSize.{w, w} G] :
    PreservesWellOrderContinuousOfShape J G where

/-- The forgetful functor from an under category preserves the colimits defining well-order
continuity: they are connected, since a limit element `j` is not minimal and so `Set.Iio j` is a
nonempty linear order. -/
instance Under.preservesWellOrderContinuousOfShape_forget (X : C) :
    PreservesWellOrderContinuousOfShape J (Under.forget X) where
  preservesColimitsOfShape j hj := by
    obtain ⟨k, hk⟩ := not_isMin_iff.1 hj.1
    have : Nonempty (Set.Iio j) := ⟨⟨k, hk⟩⟩
    infer_instance

end CategoryTheory
