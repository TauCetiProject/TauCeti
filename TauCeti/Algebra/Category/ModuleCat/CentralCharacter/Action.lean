/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.CentralCharacter.Basic
public import TauCeti.Algebra.Category.ModuleCat.Twist

/-!
# Coherent twists of strict central-character modules

An action by continuous algebra automorphisms preserving a central character acts on its
strict discrete module fiber. The action uses restriction through the inverse automorphism.
Its unit and product comparisons are inherited from native restriction of scalars, not chosen
independently: both directions have identity underlying maps. In particular, a center-fixing
action preserves every character fiber.

The construction consumes `discreteCentralCharacterModules` and its single-automorphism
transport theorem. Coherence comes from `MonoidHom.restrictScalarsMonoidalLeftAction` and the
native stable-full-subcategory action. The inclusion in all modules is equivariant with
identity lineators, and the action functors are linear over the coefficient ring.
For left actions the comparison at `g * h` has target `T_h ⋙ T_g`.

## References

* Edward Frenkel, *Langlands Correspondence for Loop Groups* (2007), §1.3: the loop-group
actions on categories with a prescribed central character.
-/

public section

universe v u

open CategoryTheory MonoidalCategory MonoidalLeftAction

namespace MonoidHom

variable {H : Type*} [Monoid H] {R : Type*} [CommRing R]
  {A : Type u} [Ring A] [Algebra R A] [TopologicalSpace A]
  (a : H →* (A ≃ₐ[R] A)) (χ : Subalgebra.center R A →ₐ[R] R)

/-- A character preserved by the inverse center maps is stable under twisting, provided the
inverse automorphisms are continuous. -/
lemma isStableUnderLeftAction_discreteCentralCharacterModules
    (ha : ∀ h, Continuous (a h).symm)
    (hχ : ∀ h, χ.comp (TauCeti.centerCongr (a h)).symm.toAlgHom = χ) :
    letI := restrictScalarsMonoidalLeftAction.{v}
      ((MulSemiringAction.toRingEquiv (A ≃ₐ[R] A) A).comp a)
    (TauCeti.discreteCentralCharacterModules.{v} χ).IsStableUnderLeftAction (Discrete H) := by
  let := restrictScalarsMonoidalLeftAction.{v}
    ((MulSemiringAction.toRingEquiv (A ≃ₐ[R] A) A).comp a)
  constructor
  intro h M hM
  have hm := TauCeti.discreteCentralCharacterModules_restrictScalars χ (a h.as) (ha h.as) hM
  rw [hχ] at hm
  exact hm

/-- A center-fixing action preserves every strict discrete character fiber. Only continuity
of the inverse algebra automorphisms is required. -/
lemma isStableUnderLeftAction_discreteCentralCharacterModules_of_centerFixed
    (ha : ∀ h, Continuous (a h).symm)
    (hz : ∀ h (z : Subalgebra.center R A), a h (z : A) = z) :
    letI := restrictScalarsMonoidalLeftAction.{v}
      ((MulSemiringAction.toRingEquiv (A ≃ₐ[R] A) A).comp a)
    (TauCeti.discreteCentralCharacterModules.{v} χ).IsStableUnderLeftAction (Discrete H) := by
  apply a.isStableUnderLeftAction_discreteCentralCharacterModules χ ha
  intro h
  apply AlgHom.ext
  intro z
  have hcenter : (TauCeti.centerCongr (a h)).symm z = z := by
    apply Subtype.ext
    rw [TauCeti.centerCongr_symm_apply_coe]
    exact (AlgEquiv.symm_apply_eq (a h)).mpr (hz h z).symm
  exact congrArg χ hcenter

variable (ha : ∀ h, Continuous (a h).symm)
  (hχ : ∀ h, χ.comp (TauCeti.centerCongr (a h)).symm.toAlgHom = χ)

/-- The coherent twisting action on a strict discrete character fiber. It restricts the
native action on all modules, so its unit and associator have identity underlying maps. -/
-- Exposed to keep underlying module elements available in the component formulas.
@[expose, instance_reducible]
noncomputable def discreteCentralCharacterMonoidalLeftAction :
    MonoidalLeftAction (Discrete H)
      (TauCeti.discreteCentralCharacterModules.{v} χ).FullSubcategory :=
  letI := restrictScalarsMonoidalLeftAction.{v}
    ((MulSemiringAction.toRingEquiv (A ≃ₐ[R] A) A).comp a)
  letI := a.isStableUnderLeftAction_discreteCentralCharacterModules χ ha hχ
  inferInstance

/-- Twisting the underlying module is native inverse restriction of scalars. -/
lemma discreteCentralCharacterMonoidalLeftAction_obj (h : Discrete H)
    (M : (TauCeti.discreteCentralCharacterModules.{v} χ).FullSubcategory) :
    letI := a.discreteCentralCharacterMonoidalLeftAction χ ha hχ
    (h ⊙ₗ M).obj = (ModuleCat.restrictScalars (a h.as).symm.toRingHom).obj M.obj :=
  (rfl)

/-- Twisting a morphism keeps its underlying map unchanged. -/
lemma discreteCentralCharacterMonoidalLeftAction_map (h : Discrete H)
    {M N : (TauCeti.discreteCentralCharacterModules.{v} χ).FullSubcategory} (f : M ⟶ N) :
    letI := a.discreteCentralCharacterMonoidalLeftAction χ ha hχ
    (h ⊴ₗ f).hom = (ModuleCat.restrictScalars (a h.as).symm.toRingHom).map f.hom :=
  (rfl)

/-- Forgetting a fiber twist is exactly restricting scalars after forgetting the fiber.
Thus the equivariant inclusion comparison uses identity components. -/
@[simp]
lemma discreteCentralCharacterMonoidalLeftAction_actionLeft_comp_ι (h : Discrete H) :
    letI := a.discreteCentralCharacterMonoidalLeftAction χ ha hχ
    actionLeft (TauCeti.discreteCentralCharacterModules.{v} χ).FullSubcategory h ⋙
        (TauCeti.discreteCentralCharacterModules χ).ι =
      (TauCeti.discreteCentralCharacterModules χ).ι ⋙
        ModuleCat.restrictScalars (a h.as).symm.toRingHom :=
  (rfl)

/-- The unit cell in the fiber is precisely the lift of the native unit cell. -/
lemma discreteCentralCharacterMonoidalLeftAction_unit
    (M : (TauCeti.discreteCentralCharacterModules.{v} χ).FullSubcategory) :
    letI := a.discreteCentralCharacterMonoidalLeftAction χ ha hχ
    (TauCeti.discreteCentralCharacterModules χ).ι.mapIso (λₗ[Discrete H] M) =
      ModuleCat.restrictScalarsId'App (a 1).symm.toRingHom
        (by ext; simp [← AlgEquiv.aut_inv]) M.obj :=
  (rfl)

/-- The product cell in the fiber is precisely the lift of native scalar-restriction
composition, with the order `T_(g*h) ≅ T_h ⋙ T_g`. This equality pins both directions. -/
lemma discreteCentralCharacterMonoidalLeftAction_assoc (g h : H)
    (M : (TauCeti.discreteCentralCharacterModules.{v} χ).FullSubcategory) :
    letI := a.discreteCentralCharacterMonoidalLeftAction χ ha hχ
    (TauCeti.discreteCentralCharacterModules χ).ι.mapIso
        (αₗ (Discrete.mk g) (Discrete.mk h) M) =
      ModuleCat.restrictScalarsComp'App (a g).symm.toRingHom (a h).symm.toRingHom
        (a (g * h)).symm.toRingHom
        (by ext; simp [← AlgEquiv.aut_inv, mul_inv_rev]) M.obj :=
  (rfl)

/-- The inclusion of the strict character fiber is equivariant for the fixed twist actions. -/
noncomputable instance leftLinearInclusionDiscreteCentralCharacterMonoidalLeftAction :
    letI := restrictScalarsMonoidalLeftAction.{v}
      ((MulSemiringAction.toRingEquiv (A ≃ₐ[R] A) A).comp a)
    letI := a.discreteCentralCharacterMonoidalLeftAction χ ha hχ
    (TauCeti.discreteCentralCharacterModules.{v} χ).ι.LeftLinear (Discrete H) :=
  letI := restrictScalarsMonoidalLeftAction.{v}
    ((MulSemiringAction.toRingEquiv (A ≃ₐ[R] A) A).comp a)
  letI := a.isStableUnderLeftAction_discreteCentralCharacterModules χ ha hχ
  inferInstance

open ModuleCat.Algebra in
/-- Each twist on the strict character fiber is linear over the coefficient ring. -/
instance linear_actionLeft_discreteCentralCharacterMonoidalLeftAction (h : Discrete H) :
    letI := a.discreteCentralCharacterMonoidalLeftAction χ ha hχ
    (actionLeft (TauCeti.discreteCentralCharacterModules.{v} χ).FullSubcategory h).Linear R := by
  let := restrictScalarsMonoidalLeftAction.{v}
    ((MulSemiringAction.toRingEquiv (A ≃ₐ[R] A) A).comp a)
  let := a.isStableUnderLeftAction_discreteCentralCharacterModules.{v} χ ha hχ
  let : (actionLeft (ModuleCat.{v} A) h).Linear R :=
    linear_actionLeft_restrictScalarsMonoidalLeftAction
      ((MulSemiringAction.toRingEquiv (A ≃ₐ[R] A) A).comp a) R (fun h r => (a h).commutes r) h
  infer_instance

end MonoidHom
