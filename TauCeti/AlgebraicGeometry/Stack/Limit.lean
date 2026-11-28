/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Stack.StackInGroupoids
public import TauCeti.CategoryTheory.Sites.Descent.Limit

/-!
# Pseudo-limits of stacks in groupoids

A small diagram of scheme pseudofunctors whose objects are fppf stacks in groupoids has a
pseudo-limit which is again an fppf stack in groupoids (`StackInGroupoids.limit`). Its fibre
over a scheme is the pseudo-limit of the fibre groupoids. The construction is the site-level
`TauCeti.Stack.limit`, so its projections, comparison modifications and universal property
are those of that construction.

Diagrams are expressed in the bicategory of scheme pseudofunctors, with the stack and groupoid
conditions on their objects. This retains the unit and composition modifications of the
diagram. The index category has objects and arrows in the universe of the schemes, while the
fibre categories have objects in `Type (u + 1)` and arrows in `Type u`.
-/

public section

open CategoryTheory Bicategory Opposite
open scoped Pseudofunctor.StrongTrans

namespace TauCeti.AlgebraicGeometry.StackInGroupoids

open _root_.AlgebraicGeometry

universe u

variable {I : Type u} [SmallCategory I]
  (D : Pseudofunctor (LocallyDiscrete I) SchPseudofunctor.{u})
  [∀ i, (D.obj (.mk i)).IsStack Scheme.fppfTopology]
  [∀ (i : I) (T : Scheme.{u}), IsGroupoid ((D.obj (.mk i)).obj (.mk (op T)))]

/-- The pseudo-limit of a small diagram of fppf stacks in groupoids. Its underlying
pseudofunctor is the fibrewise pseudo-limit of the diagram. -/
@[expose]
noncomputable def limit : StackInGroupoids.{u} where
  toSchPseudofunctor := Stack.limit.{u, u + 1, u} D
  isGroupoid _ := inferInstance
  isStack := inferInstance

namespace limit

/-- The projections, their comparison modifications and the universal property of the
pseudo-limit are `TauCeti.Stack.limit.π`, `.πCompMap`, `.lift`, `.liftCompπ`, `.isoLift`,
`.homMk`, `.isoMk` and `.hom_ext` on this underlying pseudofunctor. -/
@[simp]
theorem toSchPseudofunctor_eq :
    (limit D).toSchPseudofunctor = Stack.limit.{u, u + 1, u} D :=
  (rfl)

end limit

end TauCeti.AlgebraicGeometry.StackInGroupoids
