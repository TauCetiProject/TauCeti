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
diagram. For an index category with objects and arrows in `Type w`, the scheme universe is
`max u w`: scheme objects lie in `Type (max u w + 1)`, and the fibre categories have objects
in `Type (max u w + 1)` and arrows in `Type (max u w)`. Taking `w = 0` includes finite diagrams
over schemes in any universe `u`.
-/

public section

open CategoryTheory Bicategory Opposite
open scoped Pseudofunctor.StrongTrans

namespace TauCeti.AlgebraicGeometry.StackInGroupoids

open _root_.AlgebraicGeometry

universe u w

variable {I : Type w} [SmallCategory I]
  (D : Pseudofunctor (LocallyDiscrete I) SchPseudofunctor.{max u w})
  [∀ i, (D.obj (.mk i)).IsStack Scheme.fppfTopology]
  [∀ (i : I) (T : Scheme.{max u w}), IsGroupoid ((D.obj (.mk i)).obj (.mk (op T)))]

/-- The pseudo-limit of a small diagram of fppf stacks in groupoids. Its underlying
pseudofunctor is the fibrewise pseudo-limit of the diagram. -/
noncomputable def limit : StackInGroupoids.{max u w} where
  toSchPseudofunctor := Stack.limit.{w, max u w + 1, u} D
  isGroupoid _ := inferInstance
  isStack := inferInstance

namespace limit

/-- The projections, their comparison modifications and the universal property of the
pseudo-limit are `TauCeti.Stack.limit.π`, `.πCompMap`, `.lift`, `.liftCompπ`, `.isoLift`,
`.homMk`, `.isoMk` and `.hom_ext` on this underlying pseudofunctor. -/
@[simp]
theorem toSchPseudofunctor_eq :
    (limit D).toSchPseudofunctor = Stack.limit.{w, max u w + 1, u} D :=
  (rfl)

end limit

end TauCeti.AlgebraicGeometry.StackInGroupoids
