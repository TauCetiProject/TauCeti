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
  `.lift`, `.liftCompπ`, `.homMk`, `.isoMk` and `.hom_ext`.
* `TauCeti.AlgebraicGeometry.StackInGroupoids.pi.map`: the product of a family of morphisms.
* `TauCeti.AlgebraicGeometry.StackInGroupoids.terminal`: the terminal stack in groupoids, with
  `TauCeti.Stack.terminal.lift` and `TauCeti.Stack.terminal.hom_ext`.

## Main results

* `TauCeti.AlgebraicGeometry.StackInGroupoids.pi.isFiberwiseEquiv_map`: the product of fiberwise
  equivalences is a fiberwise equivalence.
* `TauCeti.AlgebraicGeometry.StackInGroupoids.terminal.isFiberwiseEquiv_lift`: a stack in
  groupoids whose fibres all have exactly one object up to isomorphism is fiberwise equivalent to
  the terminal stack.
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

variable {X}

/-- The `i`-th projection out of the product of stacks in groupoids. -/
noncomputable abbrev π (i : I) : (pi X).toSchPseudofunctor ⟶ (X i).toSchPseudofunctor :=
  Stack.pi.π.{u, u + 1, u} (fun i ↦ (X i).toSchPseudofunctor) i

/-- The morphism into the product of stacks in groupoids induced by a family of morphisms. -/
noncomputable abbrev lift {K : StackInGroupoids.{u}}
    (a : ∀ i, K.toSchPseudofunctor ⟶ (X i).toSchPseudofunctor) :
    K.toSchPseudofunctor ⟶ (pi X).toSchPseudofunctor :=
  Stack.pi.lift.{u, u + 1, u} a

/-- The `i`-th projection of `lift a` is `a i`. -/
noncomputable abbrev liftCompπ {K : StackInGroupoids.{u}}
    (a : ∀ i, K.toSchPseudofunctor ⟶ (X i).toSchPseudofunctor) (i : I) :
    lift a ≫ π i ≅ a i :=
  Stack.pi.liftCompπ.{u, u + 1, u} a i

variable {Y : I → StackInGroupoids.{u}}

/-- The product `∏ X i ⟶ ∏ Y i` of a family of morphisms `f i : X i ⟶ Y i`. -/
noncomputable abbrev map (f : ∀ i, (X i).toSchPseudofunctor ⟶ (Y i).toSchPseudofunctor) :
    (pi X).toSchPseudofunctor ⟶ (pi Y).toSchPseudofunctor :=
  lift fun i ↦ π i ≫ f i

/-- The component of `pi.map f` over a scheme is the product of the components of the `f i`. -/
theorem map_app_toFunctor (f : ∀ i, (X i).toSchPseudofunctor ⟶ (Y i).toSchPseudofunctor)
    (T : Scheme.{u}) :
    ((map f).app (.mk (op T))).toFunctor =
      Functor.pi fun i ↦ ((f i).app (.mk (op T))).toFunctor :=
  (rfl)

/-- **The product of fiberwise equivalences is a fiberwise equivalence.** -/
theorem isFiberwiseEquiv_map
    {f : ∀ i, (X i).toSchPseudofunctor ⟶ (Y i).toSchPseudofunctor}
    (hf : ∀ i, Hom.IsFiberwiseEquiv (f i)) :
    Hom.IsFiberwiseEquiv (X := pi X) (Y := pi Y) (map f) :=
  (Hom.isFiberwiseEquiv_iff _).mpr fun T ↦ by
  have := fun i ↦ (Hom.isFiberwiseEquiv_iff _).mp (hf i) T
  rw [map_app_toFunctor]
  exact Functor.IsEquivalence.mk' (Functor.pi fun i ↦ ((f i).app (.mk (op T))).toFunctor.inv)
    (NatIso.pi fun i ↦ ((f i).app (.mk (op T))).toFunctor.asEquivalence.unitIso)
    (NatIso.pi fun i ↦ ((f i).app (.mk (op T))).toFunctor.asEquivalence.counitIso)

end pi

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

/-- The morphism from a stack in groupoids to the terminal stack in groupoids. -/
noncomputable abbrev lift (K : StackInGroupoids.{u}) :
    K.toSchPseudofunctor ⟶ terminal.{u}.toSchPseudofunctor :=
  Stack.terminal.lift.{u + 1, u} K.toSchPseudofunctor

/-- A stack in groupoids whose fibres are nonempty, connected groupoids with trivial automorphism
groups is fiberwise equivalent to the terminal stack in groupoids. -/
theorem isFiberwiseEquiv_lift (K : StackInGroupoids.{u})
    [∀ T : Scheme.{u}, Nonempty (K.toSchPseudofunctor.obj (.mk (op T)))]
    [∀ T : Scheme.{u}, Quiver.IsThin (K.toSchPseudofunctor.obj (.mk (op T)))]
    (h : ∀ (T : Scheme.{u}) (x y : K.toSchPseudofunctor.obj (.mk (op T))), Nonempty (x ⟶ y)) :
    Hom.IsFiberwiseEquiv (X := K) (Y := terminal) (lift K) :=
  (Hom.isFiberwiseEquiv_iff _).mpr fun T ↦
  { faithful := ⟨fun {_ _} _ _ _ ↦ Subsingleton.elim _ _⟩
    full := ⟨fun {x y} _ ↦ ⟨(h T x y).some, funext fun i ↦ i.elim⟩⟩
    essSurj := ⟨fun _ ↦ ⟨Classical.arbitrary _, ⟨eqToIso (Subsingleton.elim _ _)⟩⟩⟩ }

end terminal

end TauCeti.AlgebraicGeometry.StackInGroupoids
