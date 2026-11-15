/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Rigid.Simple
public import TauCeti.CategoryTheory.Simple.Classes

/-!
# Duality on simple classes

In a rigid monoidal abelian category with additive tensor product the right dual of a simple
object is simple (`TauCeti.simple_rightDual`), so duality acts on the simple isomorphism classes:
`TauCeti.SimpleClasses.dual` sends the class of `X` to the class of `Xᘁ`. In a finite semisimple
rigid category with simple tensor unit this action is an involution
(`TauCeti.SimpleClasses.dual_dual`, in `TauCeti/CategoryTheory/Semisimple/Rigid.lean`).

## Main declarations

* `TauCeti.SimpleClasses.dual`: the dual simple class;
* `TauCeti.SimpleClasses.dualReprIso`: its representative is isomorphic to the right dual of the
  representative;
* `TauCeti.SimpleClasses.dual_classOf` and `TauCeti.SimpleClasses.eq_dual_iff`: characterizations
  of the dual class.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §4.8
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory

namespace TauCeti

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [RigidCategory C]

namespace SimpleClasses

/-- The **dual** of a simple class: the class of the right dual of its representative. -/
def dual (S : SimpleClasses C) : SimpleClasses C :=
  classOf S.reprᘁ

/-- The representative of the dual class is isomorphic to the right dual of the representative. -/
def dualReprIso (S : SimpleClasses C) : S.dual.repr ≅ S.reprᘁ :=
  classOfReprIso _

/-- The dual of the class of a simple object is the class of its right dual. -/
@[simp]
theorem dual_classOf (X : C) [Simple X] : (classOf X).dual = classOf Xᘁ :=
  (classOf_eq_iff_nonempty_iso _ _).2 ⟨(classOfReprIso X).rightAdjointMate.symm⟩

/-- A simple class is the dual of `S` exactly when its representative is isomorphic to the right
dual of the representative of `S`. -/
theorem eq_dual_iff (S T : SimpleClasses C) : T = S.dual ↔ Nonempty (T.repr ≅ S.reprᘁ) := by
  rw [eq_iff_nonempty_iso]
  exact ⟨fun ⟨e⟩ ↦ ⟨e ≪≫ dualReprIso S⟩, fun ⟨e⟩ ↦ ⟨e ≪≫ (dualReprIso S).symm⟩⟩

end SimpleClasses

end TauCeti
