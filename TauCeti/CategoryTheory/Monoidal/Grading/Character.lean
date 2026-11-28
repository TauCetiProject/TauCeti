/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Linear
public import TauCeti.CategoryTheory.Monoidal.Grading.Universal.Basic
public import TauCeti.CategoryTheory.Monoidal.NaturalTransformation
public import TauCeti.CategoryTheory.Preadditive.Schur
public import TauCeti.CategoryTheory.Semisimple.Basic

/-!
# Characters of the universal grading group from monoidal automorphisms

A monoidal natural automorphism of the identity acts on every split simple object by a
nonzero scalar. Naturality and monoidality imply that these scalars multiply along tensor
constituents, so they extend to a character of the universal grading group. In a finite
semisimple category the character determines the automorphism, since natural transformations
out of an additive functor are determined on simple objects.

`TauCeti.monoidalAutCharacter` (generalizing `TauCeti.monoidalAutCharacterOfSurjective`, which
works over any field whenever `algebraMap k (End S)` is surjective on simple objects) is this
group homomorphism, and `TauCeti.monoidalAutCharacter_injective` proves its injectivity. The
computation rule `TauCeti.monoidalAutCharacter_degree_smul_id` describes its value on the degree of
any simple object, without referring to the chosen representatives of simple classes. Surjectivity,
which requires extending a compatible family of scalars to all objects, is not asserted here.

Only the endomorphism spaces of simple objects need be finite-dimensional (or merely scalar over an
arbitrary field for the `OfSurjective` variants). No rigidity, finiteness of the set of simple
classes, or characteristic assumption is needed.

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

section General

variable (k : Type*) [Field k]

section Character

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C] [Linear k C]

private def simpleAutScalarOfSurjective
    (hscalar : ∀ (S : C) [Simple S], Function.Surjective (algebraMap k (End S)))
    (a : Aut (LaxMonoidalFunctor.of (𝟭 C))) (X : C) [Simple X] : kˣ :=
  let h := End.exists_smul_id_eq_of_surjective (hscalar X)
    ((LaxMonoidalFunctor.forgetAut (𝟭 C) a).asIso.hom.app X)
  Units.mk0 h.choose fun h0 ↦ CategoryTheory.id_ne_zero X <| by
    have hf := h.choose_spec
    rw [h0, zero_smul] at hf
    have hi := (LaxMonoidalFunctor.forgetAut (𝟭 C) a).asIso.hom_inv_id_app X
    rw [← hf, Limits.zero_comp] at hi
    exact hi.symm

private theorem simpleAutScalarOfSurjective_smul_id
    (hscalar : ∀ (S : C) [Simple S], Function.Surjective (algebraMap k (End S)))
    (a : Aut (LaxMonoidalFunctor.of (𝟭 C))) (X : C) [Simple X] :
    (simpleAutScalarOfSurjective k hscalar a X : k) • 𝟙 X =
      (LaxMonoidalFunctor.forgetAut (𝟭 C) a).asIso.hom.app X :=
  (End.exists_smul_id_eq_of_surjective (hscalar X)
    ((LaxMonoidalFunctor.forgetAut (𝟭 C) a).asIso.hom.app X)).choose_spec

private theorem simpleAutScalarOfSurjective_one
    (hscalar : ∀ (S : C) [Simple S], Function.Surjective (algebraMap k (End S)))
    (X : C) [Simple X] :
    simpleAutScalarOfSurjective k hscalar 1 X = 1 := by
  apply Units.ext
  apply smul_left_injective k (CategoryTheory.id_ne_zero X)
  simpa [one_smul] using simpleAutScalarOfSurjective_smul_id k hscalar 1 X

private theorem simpleAutScalarOfSurjective_mul
    (hscalar : ∀ (S : C) [Simple S], Function.Surjective (algebraMap k (End S)))
    (a b : Aut (LaxMonoidalFunctor.of (𝟭 C))) (X : C) [Simple X] :
    simpleAutScalarOfSurjective k hscalar (a * b) X =
      simpleAutScalarOfSurjective k hscalar a X * simpleAutScalarOfSurjective k hscalar b X := by
  apply Units.ext
  apply smul_left_injective k (CategoryTheory.id_ne_zero X)
  dsimp only
  rw [simpleAutScalarOfSurjective_smul_id, Units.val_mul, mul_comm]
  have h1 : ((simpleAutScalarOfSurjective k hscalar b X : k) *
      (simpleAutScalarOfSurjective k hscalar a X : k)) • 𝟙 X =
      ((simpleAutScalarOfSurjective k hscalar b X : k) • 𝟙 X) ≫
        ((simpleAutScalarOfSurjective k hscalar a X : k) • 𝟙 X) := by
    rw [Linear.smul_comp, Linear.comp_smul, Category.comp_id, smul_smul]
  rw [h1]
  simp [simpleAutScalarOfSurjective_smul_id, map_mul, Aut.mul_asIso]

private theorem simpleAutScalarOfSurjective_eq_of_iso
    (hscalar : ∀ (S : C) [Simple S], Function.Surjective (algebraMap k (End S)))
    (a : Aut (LaxMonoidalFunctor.of (𝟭 C))) {X Y : C} [Simple X] [Simple Y] (e : X ≅ Y) :
    simpleAutScalarOfSurjective k hscalar a X = simpleAutScalarOfSurjective k hscalar a Y := by
  apply Units.ext
  apply smul_left_injective k (CategoryTheory.id_ne_zero X)
  have h := (LaxMonoidalFunctor.forgetAut (𝟭 C) a).asIso.hom.naturality e.hom
  simp only [Functor.id_map] at h
  rw [← simpleAutScalarOfSurjective_smul_id k hscalar a X,
    ← simpleAutScalarOfSurjective_smul_id k hscalar a Y] at h
  apply (cancel_mono e.hom).1
  simpa using h.symm

variable [MonoidalPreadditive C] [MonoidalLinear k C]

private theorem simpleAutScalarOfSurjective_tensor
    (hscalar : ∀ (S : C) [Simple S], Function.Surjective (algebraMap k (End S)))
    (a : Aut (LaxMonoidalFunctor.of (𝟭 C))) (S T U : SimpleClasses C)
    (f : U.repr ⟶ S.repr ⊗ T.repr) (hf : f ≠ 0) :
    simpleAutScalarOfSurjective k hscalar a U.repr =
      simpleAutScalarOfSurjective k hscalar a S.repr *
        simpleAutScalarOfSurjective k hscalar a T.repr := by
  apply Units.ext
  apply smul_left_injective k hf
  let α := (LaxMonoidalFunctor.forgetAut (𝟭 C) a).asIso.hom
  have ht := NatTrans.IsMonoidal.tensor (τ := α) S.repr T.repr
  simp only [Functor.LaxMonoidal.id_μ, Category.id_comp, Category.comp_id] at ht
  have h := α.naturality f
  simp only [Functor.id_map] at h
  rw [ht, ← simpleAutScalarOfSurjective_smul_id k hscalar a S.repr,
    ← simpleAutScalarOfSurjective_smul_id k hscalar a T.repr,
    ← simpleAutScalarOfSurjective_smul_id k hscalar a U.repr] at h
  simpa [tensorHom_def, smul_smul, mul_comm] using h.symm

/-- Given that every simple object has scalar endomorphisms, a monoidal natural automorphism of the
identity induces a character of the universal grading group: on the degree of a simple object it is
the scalar by which the automorphism acts. -/
def monoidalAutCharacterOfSurjective
    (hscalar : ∀ (S : C) [Simple S], Function.Surjective (algebraMap k (End S))) :
    Aut (LaxMonoidalFunctor.of (𝟭 C)) →* (universalGradingGroup C →* kˣ) where
  toFun a := universalGradingGroup.lift (fun S ↦ simpleAutScalarOfSurjective k hscalar a S.repr)
    (simpleAutScalarOfSurjective_tensor k hscalar a)
  map_one' := universalGradingGroup.hom_ext fun S ↦ by
    simp [simpleAutScalarOfSurjective_one]
  map_mul' a b := universalGradingGroup.hom_ext fun S ↦ by
    simp [simpleAutScalarOfSurjective_mul]

/-- The structure map sends the value of `monoidalAutCharacterOfSurjective` at `degree S` to the
component of the automorphism at `S.repr`. -/
theorem algebraMap_monoidalAutCharacterOfSurjective_degree
    (hscalar : ∀ (S : C) [Simple S], Function.Surjective (algebraMap k (End S)))
    (a : Aut (LaxMonoidalFunctor.of (𝟭 C))) (S : SimpleClasses C) :
    algebraMap k (End S.repr)
        (monoidalAutCharacterOfSurjective k hscalar a (universalGradingGroup.degree S) : k) =
      End.of ((LaxMonoidalFunctor.forgetAut (𝟭 C) a).asIso.hom.app S.repr) := by
  apply End.ext
  rw [End.algebraMap_asHom]
  simpa [monoidalAutCharacterOfSurjective] using
    simpleAutScalarOfSurjective_smul_id k hscalar a S.repr

/-- The character on the universal degree of a simple object recovers the component of the
monoidal automorphism at that object. -/
@[simp]
theorem monoidalAutCharacterOfSurjective_degree_smul_id
    (hscalar : ∀ (S : C) [Simple S], Function.Surjective (algebraMap k (End S)))
    (a : Aut (LaxMonoidalFunctor.of (𝟭 C))) (X : C) [Simple X] :
    (monoidalAutCharacterOfSurjective k hscalar a
        (universalGradingGroup.degree (SimpleClasses.classOf X)) : k) • 𝟙 X =
      (LaxMonoidalFunctor.forgetAut (𝟭 C) a).asIso.hom.app X := by
  have h := simpleAutScalarOfSurjective_eq_of_iso k hscalar a (SimpleClasses.classOfReprIso X)
  simp only [monoidalAutCharacterOfSurjective, MonoidHom.coe_mk, OneHom.coe_mk,
    universalGradingGroup.lift_degree, h, simpleAutScalarOfSurjective_smul_id]

end Character

section SemisimpleGeneral

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [Linear k C] [MonoidalLinear k C]
  [IsFiniteSemisimpleCategory C]

/-- In a finite semisimple category where simple objects have scalar endomorphisms, the character
of the universal grading group determines a monoidal natural automorphism of the identity. -/
theorem monoidalAutCharacterOfSurjective_injective
    (hscalar : ∀ (S : C) [Simple S], Function.Surjective (algebraMap k (End S))) :
    Function.Injective (monoidalAutCharacterOfSurjective k hscalar (C := C)) := by
  intro a b hab
  apply LaxMonoidalFunctor.forgetAut_injective (𝟭 C)
  apply Aut.ext
  apply Iso.ext
  apply natTrans_ext_of_simple
  intro X _
  rw [← monoidalAutCharacterOfSurjective_degree_smul_id k hscalar a X,
    ← monoidalAutCharacterOfSurjective_degree_smul_id k hscalar b X, hab]

end SemisimpleGeneral

end General

variable (k : Type*) [Field k] [IsAlgClosed k]

section Character

variable {C : Type u} [Category.{v} C] [Preadditive C] [CategoryTheory.Limits.HasKernels C]
  [MonoidalCategory C] [Linear k C] [MonoidalPreadditive C] [MonoidalLinear k C]
  [hfin : ∀ (X : C) [Simple X], FiniteDimensional k (X ⟶ X)]

include hfin

/-- A monoidal natural automorphism of the identity gives a character of the universal grading
group: on the degree of a simple object it is the scalar by which the automorphism acts. -/
def monoidalAutCharacter : Aut (LaxMonoidalFunctor.of (𝟭 C)) →*
    (universalGradingGroup C →* kˣ) :=
  monoidalAutCharacterOfSurjective k fun S _ ↦ (bijective_algebraMap_end_of_simple k S).surjective

/-- `monoidalAutCharacter` is `monoidalAutCharacterOfSurjective` applied to the surjective
scalar map from `k` to simple endomorphism algebras. -/
theorem monoidalAutCharacter_eq :
    monoidalAutCharacter (hfin := hfin) k (C := C) =
      monoidalAutCharacterOfSurjective k
        fun S _ ↦ (bijective_algebraMap_end_of_simple k S).surjective :=
  (rfl)

/-- The value of the character on a simple degree is the scalar of the corresponding component
of the automorphism. -/
theorem monoidalAutCharacter_degree (a : Aut (LaxMonoidalFunctor.of (𝟭 C)))
    (S : SimpleClasses C) :
    (monoidalAutCharacter (hfin := hfin) k a (universalGradingGroup.degree S) : k) =
      endAlgEquivOfSimple k S.repr
        (End.of ((LaxMonoidalFunctor.forgetAut (𝟭 C) a).asIso.hom.app S.repr)) := by
  refine ((endAlgEquivOfSimple_apply_eq_iff (X := S.repr)
    (End.of ((LaxMonoidalFunctor.forgetAut (𝟭 C) a).asIso.hom.app S.repr)) _).2 ?_).symm
  dsimp only [monoidalAutCharacter]
  simpa only [SimpleClasses.classOf_repr] using
    (monoidalAutCharacterOfSurjective_degree_smul_id k
      (fun S _ ↦ (bijective_algebraMap_end_of_simple k S).surjective) a S.repr).symm

/-- The character on the universal degree of a simple object recovers the component of the
monoidal automorphism at that object. -/
@[simp]
theorem monoidalAutCharacter_degree_smul_id (a : Aut (LaxMonoidalFunctor.of (𝟭 C)))
    (X : C) [Simple X] :
    (monoidalAutCharacter (hfin := hfin) k a
        (universalGradingGroup.degree (SimpleClasses.classOf X)) : k) • 𝟙 X =
      (LaxMonoidalFunctor.forgetAut (𝟭 C) a).asIso.hom.app X :=
  monoidalAutCharacterOfSurjective_degree_smul_id k
    (fun S _ ↦ (bijective_algebraMap_end_of_simple k S).surjective) a X

end Character

section Semisimple

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [Linear k C] [MonoidalLinear k C]
  [hfin : ∀ (X : C) [Simple X], FiniteDimensional k (X ⟶ X)]
  [IsFiniteSemisimpleCategory C]

/-- In a finite semisimple category, the character of the universal grading group determines a
monoidal natural automorphism of the identity. -/
theorem monoidalAutCharacter_injective :
    Function.Injective (monoidalAutCharacter (hfin := hfin) k (C := C)) :=
  monoidalAutCharacterOfSurjective_injective k
    fun S _ ↦ (bijective_algebraMap_end_of_simple k S).surjective

end Semisimple

end TauCeti
