/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.MatlisDuality.Basic
public import TauCeti.Algebra.Homology.DerivedCategory.Ext.WithSourceAction
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import TauCeti.Algebra.Category.ModuleCat.End

/-!
# The source action of the dual right regular module on Ext

Dualizing left multiplication on the right regular module gives a map from the algebra to
the opposite endomorphism ring of its dual. This induces a left action on Ext out of that dual.
-/

public section

open CategoryTheory

namespace TauCeti

universe u v w a

variable (R : Type w) [CommRing R] (E : Type v) [AddCommGroup E] [Module R E]
  {A : Type a} [Ring A] [Algebra R A]

/-- The opposite endomorphism action on the dual of the right regular module, induced by
left multiplication before dualizing. -/
noncomputable def matlisDualRightRegularEnd :
    A →+* (End (ModuleCat.matlisDualOpObj R E (ModuleCat.of Aᵐᵒᵖ (ULift.{max u v} A))))ᵐᵒᵖ where
  toFun a := MulOpposite.op
    (End.of (ModuleCat.matlisDualOpMap R E (rightRegularEnd.{a, max u v} a).asHom))
  map_one' := by
    apply MulOpposite.unop_injective
    apply End.ext
    simp [-rightRegularEnd_asHom]
  map_mul' a b := by
    apply MulOpposite.unop_injective
    apply End.ext
    simp [-rightRegularEnd_asHom]
  map_zero' := by
    apply MulOpposite.unop_injective
    apply End.ext
    simp [-rightRegularEnd_asHom]
  map_add' a b := by
    apply MulOpposite.unop_injective
    apply End.ext
    simp [ModuleCat.matlisDualOpMap_add, -rightRegularEnd_asHom]

/-- The source endomorphism is the dual of left multiplication. -/
@[simp]
theorem matlisDualRightRegularEnd_unop_asHom (b : A) :
    (matlisDualRightRegularEnd.{u, v, w, a} R E b).unop.asHom =
      ModuleCat.matlisDualOpMap R E (rightRegularEnd b).asHom :=
  (rfl)

end TauCeti
