/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Stack.StackInGroupoids
public import TauCeti.CategoryTheory.Sites.Descent.Pi

/-!
# Products of stacks in groupoids

For a family `X i`, `i : I` with `I : Type u`, of stacks in groupoids over schemes, the product
`StackInGroupoids.pi X` is the site-level product `TauCeti.Stack.pi` of the underlying
pseudofunctors: over a scheme `T` its fibre is the product groupoid `∀ i, X i (T)`. It is an fppf
stack by `TauCeti.Stack.pi.isStack`. The empty product is the terminal stack in groupoids
`StackInGroupoids.terminal`, whose fibres have one object and one morphism. With the 2-fibre
products of `TauCeti.AlgebraicGeometry.StackInGroupoids.twoFiberProduct`, this gives the closure
of stacks in groupoids under products, 2-fibre products and the terminal object.

## Main definitions

* `TauCeti.AlgebraicGeometry.StackInGroupoids.pi X`: the product. Its underlying pseudofunctor is
  `TauCeti.Stack.pi` by definition (`pi.toSchPseudofunctor_eq`), so its projections, the morphism
  induced by a family of morphisms and its modifications are the site-level `TauCeti.Stack.pi.π`,
  `.lift`, `.liftCompπ`, `.homMk`, `.isoMk` and `.hom_ext`, and the product of a family of
  morphisms is `TauCeti.Stack.piMap`.
* `TauCeti.AlgebraicGeometry.StackInGroupoids.terminal`: the terminal stack in groupoids, with
  `TauCeti.Stack.terminal.lift` and `TauCeti.Stack.terminal.hom_ext`.

## Main results

* `TauCeti.AlgebraicGeometry.StackInGroupoids.isFiberwiseEquiv_piMap`: the product of fiberwise
  equivalences is a fiberwise equivalence.
* `TauCeti.AlgebraicGeometry.StackInGroupoids.terminal.isFiberwiseEquiv_lift`: a stack in
  groupoids whose fibres are nonempty, connected groupoids with trivial automorphism groups (that
  is, equivalent to the point) is fiberwise equivalent to the terminal stack.
-/

public section

open CategoryTheory Bicategory Opposite
open scoped Pseudofunctor.StrongTrans

namespace TauCeti.AlgebraicGeometry.StackInGroupoids

open _root_.AlgebraicGeometry

universe u

section pi

variable {I : Type u} (X : I → StackInGroupoids.{u})

/-- The **product** of a family of stacks in groupoids indexed by `I : Type u`: the site-level
product `TauCeti.Stack.pi` of the underlying pseudofunctors, whose fibre over a scheme `T` is the
product of the fibres of the `X i` over `T`. -/
@[expose]
noncomputable def pi : StackInGroupoids.{u} where
  toSchPseudofunctor := Stack.pi.{u, u + 1, u} fun i ↦ (X i).toSchPseudofunctor
  isGroupoid _ := inferInstance
  isStack := inferInstance

namespace pi

/-- The underlying pseudofunctor of the product is the site-level product, so its projections,
lifts and modifications are `TauCeti.Stack.pi.π`, `.lift`, `.homMk`, `.isoMk` and `.hom_ext`. -/
@[simp]
theorem toSchPseudofunctor_eq :
    (pi X).toSchPseudofunctor = Stack.pi.{u, u + 1, u} fun i ↦ (X i).toSchPseudofunctor :=
  (rfl)

end pi

variable {X} {Y : I → StackInGroupoids.{u}}

/-- **The product of fiberwise equivalences is a fiberwise equivalence.** -/
theorem isFiberwiseEquiv_piMap
    {f : ∀ i, (X i).toSchPseudofunctor ⟶ (Y i).toSchPseudofunctor}
    (hf : ∀ i, Hom.IsFiberwiseEquiv (f i)) :
    Hom.IsFiberwiseEquiv (X := pi X) (Y := pi Y) (Stack.piMap.{u, u + 1, u} f) :=
  (Hom.isFiberwiseEquiv_iff _).mpr fun T ↦
  have := fun i ↦ (Hom.isFiberwiseEquiv_iff _).mp (hf i) T
  Stack.isEquivalence_piMap_app.{u, u + 1, u} f (.mk (op T))

end pi

/-- The **terminal stack in groupoids**, the product of the empty family: its fibre over every
scheme is the groupoid with one object and one morphism. -/
@[expose]
noncomputable def terminal : StackInGroupoids.{u} where
  toSchPseudofunctor := Stack.terminal.{u + 1, u}
  isGroupoid _ := inferInstance
  isStack := inferInstance

namespace terminal

/-- The underlying pseudofunctor of the terminal stack in groupoids is the site-level terminal
pseudofunctor, so its morphisms and modifications are `TauCeti.Stack.terminal.lift`, `.homMk` and
`.hom_ext`. -/
@[simp]
theorem toSchPseudofunctor_eq : terminal.{u}.toSchPseudofunctor = Stack.terminal.{u + 1, u} :=
  (rfl)

/-- The fibres of the terminal stack in groupoids have exactly one object. -/
noncomputable instance instUniqueObj (T : LocallyDiscrete Scheme.{u}ᵒᵖ) :
    Unique (terminal.{u}.toSchPseudofunctor.obj T) :=
  Stack.terminal.instUniqueObj T

/-- A stack in groupoids whose fibres are nonempty, connected groupoids with trivial automorphism
groups is fiberwise equivalent to the terminal stack in groupoids. -/
theorem isFiberwiseEquiv_lift (K : StackInGroupoids.{u})
    (hne : ∀ T : Scheme.{u}, Nonempty (K.toSchPseudofunctor.obj (.mk (op T))))
    (hthin : ∀ T : Scheme.{u}, Quiver.IsThin (K.toSchPseudofunctor.obj (.mk (op T))))
    (hconn : ∀ (T : Scheme.{u}) (x y : K.toSchPseudofunctor.obj (.mk (op T))), Nonempty (x ⟶ y)) :
    Hom.IsFiberwiseEquiv (X := K) (Y := terminal)
      (Stack.terminal.lift.{u + 1, u} K.toSchPseudofunctor) :=
  (Hom.isFiberwiseEquiv_iff _).mpr fun T ↦
  Stack.terminal.isEquivalence_lift_app.{u + 1, u} _ (.mk (op T)) (hne T) (hthin T) (hconn T)

end terminal

end TauCeti.AlgebraicGeometry.StackInGroupoids
