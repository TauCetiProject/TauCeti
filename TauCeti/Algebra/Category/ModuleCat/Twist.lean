/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Aut
public import TauCeti.Algebra.Category.ModuleCat.Smooth.Basic
public import TauCeti.CategoryTheory.Monoidal.Action.Basic
public import TauCeti.CategoryTheory.Monoidal.Action.FullSubcategory

/-!
# Twisting modules by ring automorphisms

Let a monoid `H` act on a ring `A` by ring automorphisms, through a monoid homomorphism
`a : H →* RingAut A`. Twisting an `A`-module `M` by `h : H` means restricting its scalars along
`(a h)⁻¹`: the twisted module `T_h M` has the same underlying abelian group as `M`, with
`x` acting as `(a h)⁻¹ x` acts on `M`. A morphism of modules is the same map between the
twisted modules. Since `(a (g * h))⁻¹ = (a h)⁻¹ ∘ (a g)⁻¹`, twisting by `g * h` is twisting by
`h` and then by `g`, so that `T_(g * h) = T_g ∘ T_h`.

This file assembles these twists into a left action of `Discrete H` on `ModuleCat A`, in the
sense of Mathlib's `MonoidalLeftAction`, that is, a coherent categorical action of `H`:

* `MonoidHom.restrictScalarsMonoidalLeftAction a`: the action, with action functors
  `ModuleCat.restrictScalars (a h).symm`. Its unitor and associator are the comparison
  isomorphisms of restriction of scalars, `ModuleCat.restrictScalarsId'App` and
  `ModuleCat.restrictScalarsComp'App`, whose underlying linear maps are identities.
  As natural isomorphisms of action functors they are `ModuleCat.restrictScalarsId'` and
  `ModuleCat.restrictScalarsComp'` (`MonoidHom.actionUnitNatIso_restrictScalarsMonoidalLeftAction`
  and `MonoidHom.actionLeftTensorIso_restrictScalarsMonoidalLeftAction`).
* The action functors are additive equivalences, and they are `R`-linear for an `R`-algebra `A`
  when `H` acts by `R`-algebra automorphisms.
* A property of modules is stable under the action when it is preserved by each twist. This is
  the case for the discrete modules of a topological ring (`TauCeti.discreteModules`) when `H`
  acts by homeomorphisms, and for the smooth modules for a family of left ideals
  (`TauCeti.smoothModules`) when each twist preserves the family up to cofinality. The action
  then restricts to these full subcategories.

Through `MonoidalLeftAction.pseudofunctor`, the action is a pseudofunctor out of the one-object
bicategory of `H` whose unit and composition comparisons are those of restriction of scalars.

## Implementation notes

The action is built directly from `ModuleCat.restrictScalars` and its comparison isomorphisms,
rather than by composing Mathlib's `RingCat.moduleCatRestrictScalarsPseudofunctor` with a functor
out of `SingleObj H`: along that route the action would live on a `Cat` object and its associator
would pick up the composition comparisons of the functor `SingleObj H ⥤ RingCatᵒᵖ`, so that it
would not be `ModuleCat.restrictScalarsComp'App` on the nose. The morphisms of `Discrete H` act
by identity maps, rather than by `eqToHom`, so that every coherence condition is an equality of
identity maps.

## References

Twisting categories of modules over completed enveloping algebras by automorphisms is the
categorical action of loop groups in

* Edward Frenkel, [Langlands Correspondence for Loop Groups](https://math.berkeley.edu/~frenkel/loop.pdf),
  §1.3.
-/

public section

universe v u

open CategoryTheory MonoidalCategory MonoidalLeftAction

namespace MonoidHom

variable {H : Type*} [Monoid H] {A : Type u} [Ring A] (a : H →* RingAut A)

/-- The left action of a monoid `H` on `ModuleCat A` by twisting along a homomorphism
`a : H →* RingAut A`: an element `h` acts by restricting scalars along `(a h)⁻¹`. The associator
`(g * h) ⊙ₗ M ≅ g ⊙ₗ h ⊙ₗ M` and the unitor `1 ⊙ₗ M ≅ M` are the comparison isomorphisms
of restriction of scalars, with identity underlying linear maps. -/
-- The body is exposed: the twisted module `h ⊙ₗ M` must be definitionally the restriction of
-- scalars of `M`, so that the lemmas below can state the comparison isomorphisms and the
-- underlying maps in terms of `ModuleCat.restrictScalars` and of elements of `M`.
@[instance_reducible, expose]
noncomputable def restrictScalarsMonoidalLeftAction :
    MonoidalLeftAction (Discrete H) (ModuleCat.{v} A) where
  actionObj h M := (ModuleCat.restrictScalars ((a h.as).symm : A →+* A)).obj M
  actionHomLeft {c c'} f M := ModuleCat.ofHom
    (X := (ModuleCat.restrictScalars ((a c.as).symm : A →+* A)).obj M)
    (Y := (ModuleCat.restrictScalars ((a c'.as).symm : A →+* A)).obj M)
    { toFun := fun x => x
      map_add' _ _ := rfl
      map_smul' _ _ := by
        obtain rfl := Discrete.ext (Discrete.eq_of_hom f)
        rfl }
  actionHomRight h _ _ f := (ModuleCat.restrictScalars ((a h.as).symm : A →+* A)).map f
  actionAssocIso g h M := ModuleCat.restrictScalarsComp'App _ _ _
    (by ext; simp [← RingAut.inv_apply, mul_inv_rev, RingAut.mul_apply]) M
  actionUnitIso M := ModuleCat.restrictScalarsId'App _
    (by ext; simp [RingAut.one_eq_refl]) M
  actionHom_def _ _ := by ext; rfl
  actionHomRight_id _ _ := by ext; rfl
  id_actionHomLeft _ _ := by ext; rfl
  actionHom_comp _ _ _ _ := by ext; rfl
  actionAssocIso_hom_naturality _ _ _ := by ext; rfl
  actionUnitIso_hom_naturality _ := by ext; rfl
  whiskerLeft_actionHomLeft _ _ _ _ _ := by ext; rfl
  whiskerRight_actionHomLeft _ _ _ := by ext; rfl
  associator_actionHom _ _ _ _ := by ext; rfl
  leftUnitor_actionHom _ _ := by ext; rfl
  rightUnitor_actionHom _ _ := by ext; rfl

/-- An element `h` acts on `ModuleCat A` by restricting scalars along `(a h)⁻¹`. -/
lemma restrictScalarsMonoidalLeftAction_actionObj (h : Discrete H) (M : ModuleCat.{v} A) :
    letI := a.restrictScalarsMonoidalLeftAction.{v}
    h ⊙ₗ M = (ModuleCat.restrictScalars ((a h.as).symm : A →+* A)).obj M :=
  (rfl)

/-- The twist of a morphism of modules is the same map of the underlying abelian groups. -/
@[simp]
lemma restrictScalarsMonoidalLeftAction_actionHomRight_hom_apply (h : Discrete H)
    {M N : ModuleCat.{v} A} (f : M ⟶ N) (x : M) :
    letI := a.restrictScalarsMonoidalLeftAction.{v}
    (h ⊴ₗ f) x = f x :=
  (rfl)

/-- The action of a morphism of `Discrete H` on a twisted module is the identity map of the
underlying abelian group. -/
@[simp]
lemma restrictScalarsMonoidalLeftAction_actionHomLeft_hom_apply {c c' : Discrete H} (f : c ⟶ c')
    (M : ModuleCat.{v} A) (x : M) :
    letI := a.restrictScalarsMonoidalLeftAction.{v}
    (f ⊵ₗ M).hom x = x :=
  (rfl)

/-- The associator of the twisting action is the identity map of the underlying abelian group. -/
@[simp]
lemma restrictScalarsMonoidalLeftAction_actionAssocIso_hom_apply (g h : Discrete H)
    (M : ModuleCat.{v} A) (x : M) :
    letI := a.restrictScalarsMonoidalLeftAction.{v}
    (αₗ g h M).hom x = x :=
  (rfl)

/-- The inverse of the associator of the twisting action is the identity map of the underlying
abelian group. -/
@[simp]
lemma restrictScalarsMonoidalLeftAction_actionAssocIso_inv_apply (g h : Discrete H)
    (M : ModuleCat.{v} A) (x : M) :
    letI := a.restrictScalarsMonoidalLeftAction.{v}
    (αₗ g h M).inv x = x :=
  (rfl)

/-- The unitor of the twisting action is the identity map of the underlying abelian group. -/
@[simp]
lemma restrictScalarsMonoidalLeftAction_actionUnitIso_hom_apply (M : ModuleCat.{v} A) (x : M) :
    letI := a.restrictScalarsMonoidalLeftAction.{v}
    (λₗ[Discrete H] M).hom x = x :=
  (rfl)

/-- The inverse of the unitor of the twisting action is the identity map of the underlying
abelian group. -/
@[simp]
lemma restrictScalarsMonoidalLeftAction_actionUnitIso_inv_apply (M : ModuleCat.{v} A) (x : M) :
    letI := a.restrictScalarsMonoidalLeftAction.{v}
    (λₗ[Discrete H] M).inv x = x :=
  (rfl)

/-- The unit comparison of the twisting action, as a natural isomorphism of action functors, is
`ModuleCat.restrictScalarsId'`. -/
lemma actionUnitNatIso_restrictScalarsMonoidalLeftAction :
    letI := a.restrictScalarsMonoidalLeftAction.{v}
    actionUnitNatIso (Discrete H) (ModuleCat.{v} A) =
      ModuleCat.restrictScalarsId' ((a 1).symm : A →+* A) (by ext; simp [RingAut.one_eq_refl]) :=
  (rfl)

/-- The product comparison `T_(g * h) ≅ T_h ⋙ T_g` of the twisting action, as a natural
isomorphism of action functors, is `ModuleCat.restrictScalarsComp'` for the factorization
`(a (g * h))⁻¹ = (a h)⁻¹ ∘ (a g)⁻¹`. -/
lemma actionLeftTensorIso_restrictScalarsMonoidalLeftAction (g h : H) :
    letI := a.restrictScalarsMonoidalLeftAction.{v}
    actionLeftTensorIso (ModuleCat.{v} A) (Discrete.mk g) (Discrete.mk h) =
      ModuleCat.restrictScalarsComp' ((a g).symm : A →+* A) ((a h).symm : A →+* A)
        ((a (g * h)).symm : A →+* A)
        (by ext; simp [← RingAut.inv_apply, mul_inv_rev, RingAut.mul_apply]) :=
  letI := a.restrictScalarsMonoidalLeftAction.{v}
  -- Both components are `ModuleCat.restrictScalarsComp'App`, the associator of the action.
  Iso.ext <| NatTrans.ext <| funext fun M => (actionLeftTensorIso_hom_app _ _ _ M).trans (rfl)

/-- The twisting action functors are additive. -/
instance additive_actionLeft_restrictScalarsMonoidalLeftAction (c : Discrete H) :
    letI := a.restrictScalarsMonoidalLeftAction.{v}
    (actionLeft (ModuleCat.{v} A) c).Additive :=
  inferInstanceAs (ModuleCat.restrictScalars ((a c.as).symm : A →+* A)).Additive

/-- The twisting action functors are equivalences, since they restrict scalars along ring
isomorphisms. -/
instance isEquivalence_actionLeft_restrictScalarsMonoidalLeftAction (c : Discrete H) :
    letI := a.restrictScalarsMonoidalLeftAction.{v}
    (actionLeft (ModuleCat.{v} A) c).IsEquivalence :=
  inferInstanceAs (ModuleCat.restrictScalars (a c.as).symm.toRingHom).IsEquivalence

open ModuleCat.Algebra in
/-- If `A` is an `R`-algebra and `H` acts by `R`-algebra automorphisms, the twisting action
functors are `R`-linear. -/
lemma linear_actionLeft_restrictScalarsMonoidalLeftAction (R : Type*) [CommSemiring R]
    [Algebra R A] (ha : ∀ h r, a h (algebraMap R A r) = algebraMap R A r) (c : Discrete H) :
    letI := a.restrictScalarsMonoidalLeftAction.{v}
    (actionLeft (ModuleCat.{v} A) c).Linear R :=
  let e : A ≃ₐ[R] A := AlgEquiv.ofRingEquiv (f := (a c.as).symm) fun r => by
    rw [RingEquiv.symm_apply_eq, ha]
  inferInstanceAs ((ModuleCat.restrictScalars e.toAlgHom.toRingHom).Linear R)

/-- A property of `A`-modules is stable under the twisting action if and only if it is preserved
by restriction of scalars along each `(a h)⁻¹`. -/
lemma isStableUnderLeftAction_restrictScalarsMonoidalLeftAction_iff {a : H →* RingAut A}
    {P : ObjectProperty (ModuleCat.{v} A)} :
    letI := a.restrictScalarsMonoidalLeftAction.{v}
    P.IsStableUnderLeftAction (Discrete H) ↔
      ∀ (h : H) (M : ModuleCat.{v} A), P M →
        P ((ModuleCat.restrictScalars ((a h).symm : A →+* A)).obj M) :=
  letI := a.restrictScalarsMonoidalLeftAction.{v}
  ⟨fun hP h M hM => hP.1 (Discrete.mk h) M hM, fun hP => ⟨fun c M hM => hP c.as M hM⟩⟩

/-- When `H` acts on a topological ring `A` by homeomorphisms, the twisting action preserves the
discrete modules, so it restricts to the full subcategory of discrete `A`-modules. -/
lemma isStableUnderLeftAction_discreteModules [TopologicalSpace A]
    (ha : ∀ h, Continuous (a h).symm) :
    letI := a.restrictScalarsMonoidalLeftAction.{v}
    (TauCeti.discreteModules.{v} A).IsStableUnderLeftAction (Discrete H) :=
  isStableUnderLeftAction_restrictScalarsMonoidalLeftAction_iff.2 fun h _ hM =>
    TauCeti.discreteModules_restrictScalars (ha h) hM

/-- When each twist pulls every left ideal of the family `J` back to a superset of some member of
`J`, the twisting action preserves the modules that are smooth for `J`, so it restricts to the
full subcategory of smooth modules. -/
lemma isStableUnderLeftAction_smoothModules {ι : Type*} (J : ι → Submodule A A)
    (hJ : ∀ h i, ∃ i', J i' ≤ Ideal.comap (a h).symm (J i)) :
    letI := a.restrictScalarsMonoidalLeftAction.{v}
    (TauCeti.smoothModules.{v} J).IsStableUnderLeftAction (Discrete H) :=
  isStableUnderLeftAction_restrictScalarsMonoidalLeftAction_iff.2 fun h _ hM =>
    TauCeti.smoothModules_restrictScalars _ (hJ h) hM

end MonoidHom
