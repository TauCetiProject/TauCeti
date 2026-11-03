/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Grading.Universal
public import TauCeti.CategoryTheory.Monoidal.Linear
public import TauCeti.CategoryTheory.Monoidal.NaturalTransformation
public import TauCeti.CategoryTheory.Semisimple.CatCenter

/-!
# Monoidal automorphisms of the identity from characters of the universal grading group

Let `C` be a finite semisimple `R`-linear monoidal category with simple tensor unit. A character
`χ : universalGradingGroup C →* Rˣ` of its universal grading group determines a monoidal natural
automorphism of the identity functor of `C`: it acts on each simple object `X` as multiplication
by `χ (degree [X])`, and on an arbitrary object through a decomposition into simple objects
(`TauCeti.simpleScalarsToCatCenter`). It is monoidal because every simple constituent of `X ⊗ Y`,
for simple `X` and `Y`, has degree `degree [X] * degree [Y]`, and because the tensor unit has
trivial degree.

This gives a group homomorphism from the characters of the universal grading group to the group
`Aut_⊗(𝟭_C)` of monoidal natural automorphisms of the identity, which acts on the pivotal
structures of `C`. Over a field it is injective, since a character is determined by its values on
the degrees of the simple objects, which generate the group. This is the direction of the
isomorphism `Aut_⊗(𝟭_C) ≅ Hom(U(C), kˣ)` of Drinfeld, Gelaki, Nikshych and Ostrik which extends a
character to all objects.

## Main declarations

* `TauCeti.characterMonoidalAut`: the group homomorphism from characters of the universal
  grading group to monoidal natural automorphisms of the identity functor;
* `TauCeti.characterMonoidalAut_app_of_simple`: its value at `χ` acts on a simple object `X` as
  multiplication by `χ (degree [X])`, and `TauCeti.comp_characterMonoidalAut_app` describes it on
  an arbitrary object;
* `TauCeti.characterMonoidalAut_injective`: over a field, distinct characters give distinct
  automorphisms.

## References

* V. Drinfeld, S. Gelaki, D. Nikshych, V. Ostrik, *On braided fusion categories I*,
  Selecta Math. **16** (2010), §2.3
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §4.14
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory MonoidalCategory

universe v u w

section Scalars

variable {R : Type w} [CommMonoid R] {C : Type u} [Category.{v} C]
  [CategoryTheory.Limits.HasZeroMorphisms C] [MonoidalCategory C]

/-- The scalars of a character on the degrees of the simple classes. -/
private def degreeScalars (χ : universalGradingGroup C →* Rˣ) : SimpleClasses C → R :=
  fun S ↦ χ (universalGradingGroup.degree S)

private theorem degreeScalars_one : degreeScalars (1 : universalGradingGroup C →* Rˣ) = 1 :=
  funext fun S ↦ by simp [degreeScalars]

private theorem degreeScalars_mul (χ ψ : universalGradingGroup C →* Rˣ) :
    degreeScalars (χ * ψ) = degreeScalars ψ * degreeScalars χ :=
  funext fun S ↦ by simp [degreeScalars, mul_comm]

private theorem degreeScalars_mul_inv (χ : universalGradingGroup C →* Rˣ) :
    degreeScalars χ * degreeScalars χ⁻¹ = 1 :=
  funext fun S ↦ by simp [degreeScalars]

end Scalars

section Character

variable (R : Type w) [CommSemiring R] {C : Type u} [Category.{v} C] [Abelian C]
  [MonoidalCategory C] [Linear R C] [IsFiniteSemisimpleCategory C]

variable {R} in
/-- On a tensor product of simple objects, the central endomorphism given by a character acts as
the product of its scalars on the factors. -/
private theorem app_tensorObj_of_simple (χ : universalGradingGroup C →* Rˣ) (X Y : C)
    [Simple X] [Simple Y] :
    (simpleScalarsToCatCenter R C (degreeScalars χ)).app (X ⊗ Y) =
      (degreeScalars χ (SimpleClasses.classOf X) * degreeScalars χ (SimpleClasses.classOf Y)) •
        𝟙 (X ⊗ Y) := by
  refine (𝟭 C).hom_ext_of_simple fun S _ s ↦ ?_
  dsimp only [Functor.id_map, Functor.id_obj]
  rw [comp_simpleScalarsToCatCenter_app, Linear.comp_smul, Category.comp_id]
  by_cases hs : s = 0
  · simp [hs]
  · simp [degreeScalars, universalGradingGroup.degree_classOf_eq_mul s hs]

variable {R} in
/-- The natural automorphism of the identity functor given by a character, whose inverse is given
by the inverse character. -/
private def natIso (χ : universalGradingGroup C →* Rˣ) : 𝟭 C ≅ 𝟭 C :=
  (Aut.unitsEndEquivAut (𝟭 C)
    { val := simpleScalarsToCatCenter R C (degreeScalars χ)
      inv := simpleScalarsToCatCenter R C (degreeScalars χ⁻¹)
      val_inv := by rw [← map_mul, degreeScalars_mul_inv, map_one]
      inv_val := by rw [← map_mul, mul_comm, degreeScalars_mul_inv, map_one] }).asIso

variable {R} in
private theorem natIso_hom_app (χ : universalGradingGroup C →* Rˣ) (X : C) :
    (natIso χ).hom.app X = (simpleScalarsToCatCenter R C (degreeScalars χ)).app X :=
  (rfl)

variable [MonoidalPreadditive C] [MonoidalLinear R C]

variable {R} in
/-- The central endomorphism given by a character is compatible with tensor products. -/
private theorem app_tensorObj (χ : universalGradingGroup C →* Rˣ) (X Y : C) :
    (simpleScalarsToCatCenter R C (degreeScalars χ)).app (X ⊗ Y) =
      (simpleScalarsToCatCenter R C (degreeScalars χ)).app X ⊗ₘ
        (simpleScalarsToCatCenter R C (degreeScalars χ)).app Y := by
  -- Reduce to tensor products of simple objects, one factor at a time.
  refine (tensorRight Y).hom_ext_of_simple fun A _ u ↦ ?_
  refine (tensorLeft A).hom_ext_of_simple fun B _ v ↦ ?_
  dsimp only [curriedTensor_obj_obj, curriedTensor_obj_map, Functor.flip_obj_obj,
    Functor.flip_obj_map, curriedTensor_map_app]
  rw [← tensorHom_def'_assoc, ← tensorHom_def'_assoc, CatCenter.naturality,
    app_tensorObj_of_simple, tensorHom_comp_tensorHom, comp_simpleScalarsToCatCenter_app,
    comp_simpleScalarsToCatCenter_app]
  simp [smul_smul, mul_comm]

variable [Simple (𝟙_ C)]

variable {R} in
private instance (χ : universalGradingGroup C →* Rˣ) : NatTrans.IsMonoidal (natIso χ).hom where
  unit := by
    simp [natIso_hom_app, degreeScalars]
  tensor X Y := by
    simp [natIso_hom_app, app_tensorObj]

variable {R} in
/-- The monoidal natural automorphism of the identity functor given by a character. -/
private def monoidalAut (χ : universalGradingGroup C →* Rˣ) : Aut (LaxMonoidalFunctor.of (𝟭 C)) :=
  Aut.of (@LaxMonoidalFunctor.isoMk _ _ _ _ _ _ _ _ (natIso χ)
    (by exact (inferInstance : NatTrans.IsMonoidal (natIso χ).hom)))

variable {R} in
private theorem forgetAut_monoidalAut_app (χ : universalGradingGroup C →* Rˣ) (X : C) :
    (LaxMonoidalFunctor.forgetAut (𝟭 C) (monoidalAut χ)).asIso.hom.app X =
      (simpleScalarsToCatCenter R C (degreeScalars χ)).app X := by
  rw [LaxMonoidalFunctor.forgetAut_apply_asIso_hom]
  exact natIso_hom_app χ X

/-- A character of the universal grading group of a finite semisimple `R`-linear monoidal category
with simple unit gives the monoidal natural automorphism of the identity functor acting on each
simple object `X` as multiplication by the value of the character on the degree of `X`. -/
def characterMonoidalAut :
    (universalGradingGroup C →* Rˣ) →* Aut (LaxMonoidalFunctor.of (𝟭 C)) where
  toFun := monoidalAut
  map_one' := by
    apply LaxMonoidalFunctor.forgetAut_injective (𝟭 C)
    ext X
    rw [forgetAut_monoidalAut_app, degreeScalars_one, map_one, map_one]
    simp
  map_mul' χ ψ := by
    apply LaxMonoidalFunctor.forgetAut_injective (𝟭 C)
    ext X
    rw [forgetAut_monoidalAut_app, degreeScalars_mul, map_mul, map_mul, CatCenter.mul_app,
      Aut.mul_asIso, Iso.trans_hom, NatTrans.comp_app, forgetAut_monoidalAut_app,
      forgetAut_monoidalAut_app]

variable {R}

private theorem characterMonoidalAut_app (χ : universalGradingGroup C →* Rˣ) (X : C) :
    (LaxMonoidalFunctor.forgetAut (𝟭 C) (characterMonoidalAut R χ)).asIso.hom.app X =
      (simpleScalarsToCatCenter R C (degreeScalars χ)).app X :=
  forgetAut_monoidalAut_app χ X

/-- Precomposed with a morphism `s` out of a simple object `S`, the monoidal automorphism given by
a character `χ` is multiplication of `s` by `χ (degree [S])`. -/
@[reassoc]
theorem comp_characterMonoidalAut_app (χ : universalGradingGroup C →* Rˣ) {S X : C} [Simple S]
    (s : S ⟶ X) :
    s ≫ (LaxMonoidalFunctor.forgetAut (𝟭 C) (characterMonoidalAut R χ)).asIso.hom.app X =
      (χ (universalGradingGroup.degree (SimpleClasses.classOf S)) : R) • s := by
  rw [characterMonoidalAut_app, comp_simpleScalarsToCatCenter_app, degreeScalars]

/-- The monoidal automorphism given by a character `χ` acts on a simple object `X` as
multiplication by `χ (degree [X])`. -/
@[simp]
theorem characterMonoidalAut_app_of_simple (χ : universalGradingGroup C →* Rˣ) (X : C)
    [Simple X] :
    (LaxMonoidalFunctor.forgetAut (𝟭 C) (characterMonoidalAut R χ)).asIso.hom.app X =
      (χ (universalGradingGroup.degree (SimpleClasses.classOf X)) : R) • 𝟙 X := by
  rw [characterMonoidalAut_app, simpleScalarsToCatCenter_app_of_simple, degreeScalars]

end Character

section Injective

variable (k : Type w) [Field k] {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [Linear k C] [MonoidalLinear k C] [IsFiniteSemisimpleCategory C]
  [Simple (𝟙_ C)]

/-- Over a field, distinct characters of the universal grading group give distinct monoidal
automorphisms of the identity functor, since a character is determined by its values on the
degrees of the simple objects. -/
theorem characterMonoidalAut_injective :
    Function.Injective (characterMonoidalAut k (C := C)) := by
  intro χ ψ h
  ext S
  have hS := congrArg
    (fun a ↦ (LaxMonoidalFunctor.forgetAut (𝟭 C) a).asIso.hom.app S.repr) h
  simp only [characterMonoidalAut_app_of_simple, SimpleClasses.classOf_repr] at hS
  exact smul_left_injective k (CategoryTheory.id_ne_zero S.repr) hS

end Injective

end TauCeti
