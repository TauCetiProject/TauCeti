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
`TauCeti.Stack.limit`. The projection cone `StackInGroupoids.limit.cone`, the morphism
`StackInGroupoids.limit.lift`, its comparisons `StackInGroupoids.limit.liftCompπ`, and
`StackInGroupoids.limit.isoLift` and `.hom_ext` expose its universal property at bundled endpoints.

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

/-- The projection cone with apex the underlying pseudofunctor of the bundled limit.
Its `π`, `iso`, `iso_id` and `iso_comp` fields give the projections and their coherence laws. -/
def cone : Stack.limit.Cone.{w, max u w + 1, u} D (limit D).toSchPseudofunctor :=
  (toSchPseudofunctor_eq D).symm ▸ Stack.limit.cone.{w, max u w + 1, u} D

variable {D}

/-- The morphism from a bundled stack induced by a pseudo-cone. -/
def lift {K : StackInGroupoids.{max u w}}
    (c : Stack.limit.Cone.{w, max u w + 1, u} D K.toSchPseudofunctor) :
    K.toSchPseudofunctor ⟶ (limit D).toSchPseudofunctor :=
  (toSchPseudofunctor_eq D).symm ▸ Stack.limit.lift.{w, max u w + 1, u} c

/-- Composing the bundled lift with a projection recovers the corresponding cone leg. -/
def liftCompπ {K : StackInGroupoids.{max u w}}
    (c : Stack.limit.Cone.{w, max u w + 1, u} D K.toSchPseudofunctor) (i : I) :
    lift c ≫ (cone D).π i ≅ c.π i := by
  unfold lift cone
  exact Stack.limit.liftCompπ.{w, max u w + 1, u} c i

/-- Modifications into the bundled limit are determined by all their projections. -/
lemma hom_ext {K : StackInGroupoids.{max u w}}
    {φ ψ : K.toSchPseudofunctor ⟶ (limit D).toSchPseudofunctor}
    {n n' : φ ⟶ ψ} (h : ∀ i, n ▷ (cone D).π i = n' ▷ (cone D).π i) : n = n' := by
  unfold cone at h
  exact Stack.limit.hom_ext.{w, max u w + 1, u} h

/-- Any bundled morphism whose projections identify it with a cone is isomorphic to its lift. -/
def isoLift {K : StackInGroupoids.{max u w}}
    (c : Stack.limit.Cone.{w, max u w + 1, u} D K.toSchPseudofunctor)
    {φ : K.toSchPseudofunctor ⟶ (limit D).toSchPseudofunctor}
    (e : ∀ i, φ ≫ (cone D).π i ≅ c.π i)
    (he : ∀ ⦃i j : I⦄ (g : i ⟶ j), (e i).hom ▷ D.map g.toLoc ≫ (c.iso g).hom =
      (α_ _ _ _).hom ≫ φ ◁ ((cone D).iso g).hom ≫ (e j).hom) :
    φ ≅ lift c := by
  unfold cone at e he
  unfold lift
  exact Stack.limit.isoLift.{w, max u w + 1, u} c e he

/-- The uniqueness isomorphism has the prescribed projection components. -/
@[simp]
lemma isoLift_hom_whiskerRight_π {K : StackInGroupoids.{max u w}}
    (c : Stack.limit.Cone.{w, max u w + 1, u} D K.toSchPseudofunctor)
    {φ : K.toSchPseudofunctor ⟶ (limit D).toSchPseudofunctor}
    (e : ∀ i, φ ≫ (cone D).π i ≅ c.π i)
    (he : ∀ ⦃i j : I⦄ (g : i ⟶ j), (e i).hom ▷ D.map g.toLoc ≫ (c.iso g).hom =
      (α_ _ _ _).hom ≫ φ ◁ ((cone D).iso g).hom ≫ (e j).hom) (i : I) :
    (isoLift c e he).hom ▷ (cone D).π i = (e i).hom ≫ (liftCompπ c i).inv := by
  unfold isoLift liftCompπ cone
  exact Stack.limit.isoLift_hom_whiskerRight_π.{w, max u w + 1, u} c e he i

end limit

end TauCeti.AlgebraicGeometry.StackInGroupoids
