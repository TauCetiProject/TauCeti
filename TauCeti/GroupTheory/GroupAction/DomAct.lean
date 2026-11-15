/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.DomAct.Basic
public import Mathlib.Algebra.Ring.Action.Basic
public import Mathlib.Algebra.Ring.Pi

/-!
# Domain actions on function semirings

The domain action preserves pointwise addition and multiplication, so it acts by semiring
endomorphisms. Pulling this action back along the double-opposite map gives right translation
on functions on a monoid. The action is opt-in, to avoid ambiguity with the pointwise action
on the codomain.
-/

public section

namespace DomMulAct

/-- The domain action on semiring-valued functions preserves their semiring structure. -/
instance instMulSemiringAction {M X R : Type*} [Monoid M] [MulAction M X] [Semiring R] :
    MulSemiringAction (DomMulAct M) (X → R) :=
  { (inferInstance : DistribMulAction (DomMulAct M) (X → R)),
    (inferInstance : MulDistribMulAction (DomMulAct M) (X → R)) with }

end DomMulAct

namespace TauCeti

/-- Right translation on functions: `(h • f) g = f (g * h)`.

Enable this with `attribute [local instance] rightRegularMulSemiringAction`; it is not a
global instance because functions also carry the pointwise action on their values. -/
abbrev rightRegularMulSemiringAction (M R : Type*) [Monoid M] [Semiring R] :
    MulSemiringAction M (M → R) :=
  MulSemiringAction.compHom (M → R)
    { toFun := fun h ↦ DomMulAct.mk (MulOpposite.op h)
      map_one' := rfl
      map_mul' := fun _ _ ↦ by simp only [MulOpposite.op_mul, DomMulAct.mk_mul] }

attribute [local instance] rightRegularMulSemiringAction

/-- Right translation evaluates a function at the right translate of its argument. -/
@[simp] theorem rightRegularMulSemiringAction_smul_apply
    {M R : Type*} [Monoid M] [Semiring R] (h : M) (f : M → R) (g : M) :
    (h • f) g = f (g * h) := (rfl)

/-- Right translation commutes with pointwise scalar multiplication. -/
instance rightRegularSMulCommClass {M R S : Type*} [Monoid M] [Semiring R] [SMul S R] :
    SMulCommClass M S (M → R) where
  smul_comm _ _ _ := rfl

end TauCeti
