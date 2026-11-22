/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Linear
public import TauCeti.CategoryTheory.Monoidal.Grading.Universal
public import TauCeti.CategoryTheory.Monoidal.NaturalTransformation
public import TauCeti.CategoryTheory.Preadditive.Schur

/-!
# Characters of the universal grading group from monoidal automorphisms

A monoidal natural automorphism of the identity acts on every simple object whose endomorphism ring
consists of scalars (`TauCeti.HasScalarSimpleEnd k C`) by a nonzero scalar. Naturality and
monoidality imply that these scalars multiply along tensor constituents, so they extend to a
character of the universal grading group. In a finite semisimple category the character determines
the automorphism, since natural transformations out of an additive functor are determined on simple
objects.

`TauCeti.monoidalAutCharacter` constructs this group homomorphism for any field `k` with
`[HasScalarSimpleEnd k C]` (in particular, automatically over an algebraically closed field when
simple objects have finite-dimensional endomorphisms), and `TauCeti.monoidalAutCharacter_injective`
proves its injectivity. The computation rule `TauCeti.monoidalAutCharacter_degree_smul_id`
describes its value on the degree of any simple object, without referring to chosen representatives
of simple classes. Surjectivity of the character map, which requires extending a compatible family
of scalars to all objects, is proved in `TauCeti.CategoryTheory.Monoidal.Grading.Classification`.

No rigidity, finiteness of the set of simple classes, or characteristic assumption is needed.

## References

* V. Drinfeld, S. Gelaki, D. Nikshych, V. Ostrik, *On braided fusion categories I*,
  Selecta Math. **16** (2010), §2.3
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §4.14
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory

universe v u

namespace TauCeti

variable (k : Type*) [Field k]

section Character

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C] [Linear k C]
  [HasScalarSimpleEnd k C]

private def simpleAutScalar (a : Aut (LaxMonoidalFunctor.of (𝟭 C))) (X : C) [Simple X] : kˣ :=
  Units.map (endAlgEquivOfSurjective k X (HasScalarSimpleEnd.surjective_algebraMap X)).toMonoidHom
    ((Aut.unitsEndEquivAut X).symm
      (Aut.of ((LaxMonoidalFunctor.forgetAut (𝟭 C) a).asIso.app X)))

private theorem simpleAutScalar_val (a : Aut (LaxMonoidalFunctor.of (𝟭 C)))
    (X : C) [Simple X] :
    (simpleAutScalar k a X : k) =
      endAlgEquivOfSurjective k X (HasScalarSimpleEnd.surjective_algebraMap X)
        (End.of ((LaxMonoidalFunctor.forgetAut (𝟭 C) a).asIso.hom.app X)) :=
  (rfl)

private theorem simpleAutScalar_smul_id (a : Aut (LaxMonoidalFunctor.of (𝟭 C)))
    (X : C) [Simple X] :
    (simpleAutScalar k a X : k) • 𝟙 X =
      (LaxMonoidalFunctor.forgetAut (𝟭 C) a).asIso.hom.app X :=
  endAlgEquivOfSurjective_smul_id _

private theorem simpleAutScalar_mul (a b : Aut (LaxMonoidalFunctor.of (𝟭 C)))
    (X : C) [Simple X] :
    simpleAutScalar k (a * b) X = simpleAutScalar k a X * simpleAutScalar k b X := by
  apply Units.ext
  simp only [Units.val_mul, simpleAutScalar_val, map_mul, Aut.mul_asIso, Iso.trans_hom,
    NatTrans.comp_app, End.of_comp]

private theorem simpleAutScalar_eq_of_iso (a : Aut (LaxMonoidalFunctor.of (𝟭 C)))
    {X Y : C} [Simple X] [Simple Y] (e : X ≅ Y) :
    simpleAutScalar k a X = simpleAutScalar k a Y := by
  apply Units.ext
  apply smul_left_injective k (CategoryTheory.id_ne_zero X)
  have h := (LaxMonoidalFunctor.forgetAut (𝟭 C) a).asIso.hom.naturality e.hom
  simp only [Functor.id_map] at h
  rw [← simpleAutScalar_smul_id k a X, ← simpleAutScalar_smul_id k a Y] at h
  apply (cancel_mono e.hom).1
  simpa using h.symm

variable [MonoidalPreadditive C] [MonoidalLinear k C]

private theorem simpleAutScalar_tensor (a : Aut (LaxMonoidalFunctor.of (𝟭 C)))
    (S T U : SimpleClasses C) (f : U.repr ⟶ S.repr ⊗ T.repr) (hf : f ≠ 0) :
    simpleAutScalar k a U.repr = simpleAutScalar k a S.repr * simpleAutScalar k a T.repr := by
  apply Units.ext
  apply smul_left_injective k hf
  let α := (LaxMonoidalFunctor.forgetAut (𝟭 C) a).asIso.hom
  have ht := NatTrans.IsMonoidal.tensor (τ := α) S.repr T.repr
  simp only [Functor.LaxMonoidal.id_μ, Category.id_comp, Category.comp_id] at ht
  have h := α.naturality f
  simp only [Functor.id_map] at h
  rw [ht, ← simpleAutScalar_smul_id k a S.repr, ← simpleAutScalar_smul_id k a T.repr,
    ← simpleAutScalar_smul_id k a U.repr] at h
  simpa [tensorHom_def, smul_smul, mul_comm] using h.symm

/-- A monoidal natural automorphism of the identity gives a character of the universal grading
group whenever simple objects have scalar endomorphisms (`HasScalarSimpleEnd k C`): on the degree
of a simple object it is the scalar by which the automorphism acts. -/
def monoidalAutCharacter :
    Aut (LaxMonoidalFunctor.of (𝟭 C)) →* (universalGradingGroup C →* kˣ) where
  toFun a := universalGradingGroup.lift (fun S ↦ simpleAutScalar k a S.repr)
    (simpleAutScalar_tensor k a)
  map_one' := by
    apply universalGradingGroup.hom_ext
    intro S
    apply Units.ext
    simp only [universalGradingGroup.lift_degree, MonoidHom.one_apply, simpleAutScalar_val,
      map_one, Aut.one_asIso, Iso.refl_hom, NatTrans.id_app, Functor.id_obj, End.of_id,
      Units.val_one]
  map_mul' a b := by
    apply universalGradingGroup.hom_ext
    intro S
    simpa only [universalGradingGroup.lift_degree, MonoidHom.mul_apply] using
      simpleAutScalar_mul k a b S.repr

/-- The value of the character on a simple degree is the scalar of the corresponding component
of the automorphism. -/
theorem monoidalAutCharacter_degree (a : Aut (LaxMonoidalFunctor.of (𝟭 C)))
    (S : SimpleClasses C) :
    (monoidalAutCharacter k a (universalGradingGroup.degree S) : k) =
      endAlgEquivOfSurjective k S.repr (HasScalarSimpleEnd.surjective_algebraMap S.repr)
        (End.of ((LaxMonoidalFunctor.forgetAut (𝟭 C) a).asIso.hom.app S.repr)) := by
  simp only [monoidalAutCharacter, MonoidHom.coe_mk, OneHom.coe_mk,
    universalGradingGroup.lift_degree, simpleAutScalar_val]

/-- The character on the universal degree of a simple object recovers the component of the
monoidal automorphism at that object. -/
@[simp]
theorem monoidalAutCharacter_degree_smul_id (a : Aut (LaxMonoidalFunctor.of (𝟭 C)))
    (X : C) [Simple X] :
    (monoidalAutCharacter k a (universalGradingGroup.degree (SimpleClasses.classOf X)) : k) •
        𝟙 X =
      (LaxMonoidalFunctor.forgetAut (𝟭 C) a).asIso.hom.app X := by
  have h := simpleAutScalar_eq_of_iso k a (SimpleClasses.classOfReprIso X)
  simp only [monoidalAutCharacter, MonoidHom.coe_mk, OneHom.coe_mk,
    universalGradingGroup.lift_degree, h, simpleAutScalar_smul_id]

/-- The structure map sends the value of `monoidalAutCharacter` at a simple class `S` to the
component of the automorphism at `S.repr`. -/
theorem algebraMap_monoidalAutCharacter_degree (a : Aut (LaxMonoidalFunctor.of (𝟭 C)))
    (S : SimpleClasses C) :
    algebraMap k (End S.repr) (monoidalAutCharacter k a (universalGradingGroup.degree S) : k) =
      End.of ((LaxMonoidalFunctor.forgetAut (𝟭 C) a).asIso.hom.app S.repr) := by
  apply End.ext
  rw [End.algebraMap_asHom]
  simpa only [SimpleClasses.classOf_repr] using monoidalAutCharacter_degree_smul_id k a S.repr

end Character

section Semisimple

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [Linear k C] [MonoidalLinear k C]
  [IsFiniteSemisimpleCategory C] [HasScalarSimpleEnd k C]

/-- In a finite semisimple category where simple objects have scalar endomorphisms, the character
of the universal grading group determines a monoidal natural automorphism of the identity. -/
theorem monoidalAutCharacter_injective :
    Function.Injective (monoidalAutCharacter k (C := C)) := by
  intro a b hab
  apply LaxMonoidalFunctor.forgetAut_injective (𝟭 C)
  apply Aut.ext
  apply Iso.ext
  apply natTrans_ext_of_simple
  intro X _
  rw [← monoidalAutCharacter_degree_smul_id k a X,
    ← monoidalAutCharacter_degree_smul_id k b X, hab]

end Semisimple

end TauCeti
