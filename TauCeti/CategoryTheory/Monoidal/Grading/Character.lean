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
consists of scalars (`Function.Surjective (algebraMap k (End X))`) by a nonzero scalar. Naturality
and monoidality imply that these scalars multiply along tensor constituents, so they extend to a
character of the universal grading group. In a finite semisimple category the character determines
the automorphism, since natural transformations out of an additive functor are determined on simple
objects.

`TauCeti.monoidalAutCharacterOfSurjective` constructs this group homomorphism for any field `k`
such that `algebraMap k (End X)` is surjective for every simple `X` (in particular, without assuming
`k` is algebraically closed), and `TauCeti.monoidalAutCharacterOfSurjective_injective` proves its
injectivity. When `k` is algebraically closed and `End X` is finite-dimensional for simple `X`,
Schur's lemma gives surjectivity and `TauCeti.monoidalAutCharacter` specializes this construction.
The computation rule `TauCeti.monoidalAutCharacter_degree_smul_id` (and
`TauCeti.monoidalAutCharacterOfSurjective_degree_smul_id`) describes its value on the degree of any
simple object, without referring to chosen representatives of simple classes. Surjectivity of the
character map, which requires extending a compatible family of scalars to all objects, is proved in
`TauCeti.CategoryTheory.Monoidal.Grading.Classification`.

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

section Surjective

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C] [Linear k C]

private def endRingEquivOfSurjective
    (hsurj : ∀ (X : C) [Simple X], Function.Surjective (algebraMap k (End X)))
    (X : C) [Simple X] : End X ≃+* k :=
  have : Nontrivial (End X) :=
    ⟨⟨1, 0, fun h ↦ CategoryTheory.id_ne_zero X (congrArg End.asHom h)⟩⟩
  (RingEquiv.ofBijective (algebraMap k (End X))
    ⟨(algebraMap k (End X)).injective, hsurj X⟩).symm

omit [MonoidalCategory C] in
private theorem endRingEquivOfSurjective_smul_id
    (hsurj : ∀ (X : C) [Simple X], Function.Surjective (algebraMap k (End X)))
    {X : C} [Simple X] (f : End X) :
    endRingEquivOfSurjective k hsurj X f • 𝟙 X = f.asHom := by
  rw [← End.algebraMap_asHom]
  have : Nontrivial (End X) :=
    ⟨⟨1, 0, fun h ↦ CategoryTheory.id_ne_zero X (congrArg End.asHom h)⟩⟩
  exact congrArg End.asHom
    ((RingEquiv.ofBijective (algebraMap k (End X))
      ⟨(algebraMap k (End X)).injective, hsurj X⟩).apply_symm_apply f)

private def simpleAutScalar
    (hsurj : ∀ (X : C) [Simple X], Function.Surjective (algebraMap k (End X)))
    (a : Aut (LaxMonoidalFunctor.of (𝟭 C))) (X : C) [Simple X] : kˣ :=
  Units.map (endRingEquivOfSurjective k hsurj X).toMonoidHom
    ((Aut.unitsEndEquivAut X).symm
      (Aut.of ((LaxMonoidalFunctor.forgetAut (𝟭 C) a).asIso.app X)))

private theorem simpleAutScalar_val
    (hsurj : ∀ (X : C) [Simple X], Function.Surjective (algebraMap k (End X)))
    (a : Aut (LaxMonoidalFunctor.of (𝟭 C))) (X : C) [Simple X] :
    (simpleAutScalar k hsurj a X : k) = endRingEquivOfSurjective k hsurj X
      (End.of ((LaxMonoidalFunctor.forgetAut (𝟭 C) a).asIso.hom.app X)) := (rfl)

private theorem simpleAutScalar_smul_id
    (hsurj : ∀ (X : C) [Simple X], Function.Surjective (algebraMap k (End X)))
    (a : Aut (LaxMonoidalFunctor.of (𝟭 C))) (X : C) [Simple X] :
    (simpleAutScalar k hsurj a X : k) • 𝟙 X =
      (LaxMonoidalFunctor.forgetAut (𝟭 C) a).asIso.hom.app X :=
  endRingEquivOfSurjective_smul_id k hsurj _

private theorem simpleAutScalar_mul
    (hsurj : ∀ (X : C) [Simple X], Function.Surjective (algebraMap k (End X)))
    (a b : Aut (LaxMonoidalFunctor.of (𝟭 C))) (X : C) [Simple X] :
    simpleAutScalar k hsurj (a * b) X =
      simpleAutScalar k hsurj a X * simpleAutScalar k hsurj b X := by
  apply Units.ext
  simp only [Units.val_mul, simpleAutScalar_val, map_mul, Aut.mul_asIso, Iso.trans_hom,
    NatTrans.comp_app, End.of_comp]

private theorem simpleAutScalar_eq_of_iso
    (hsurj : ∀ (X : C) [Simple X], Function.Surjective (algebraMap k (End X)))
    (a : Aut (LaxMonoidalFunctor.of (𝟭 C))) {X Y : C} [Simple X] [Simple Y] (e : X ≅ Y) :
    simpleAutScalar k hsurj a X = simpleAutScalar k hsurj a Y := by
  apply Units.ext
  apply smul_left_injective k (CategoryTheory.id_ne_zero X)
  have h := (LaxMonoidalFunctor.forgetAut (𝟭 C) a).asIso.hom.naturality e.hom
  simp only [Functor.id_map] at h
  rw [← simpleAutScalar_smul_id k hsurj a X, ← simpleAutScalar_smul_id k hsurj a Y] at h
  apply (cancel_mono e.hom).1
  simpa using h.symm

variable [MonoidalPreadditive C] [MonoidalLinear k C]

private theorem simpleAutScalar_tensor
    (hsurj : ∀ (X : C) [Simple X], Function.Surjective (algebraMap k (End X)))
    (a : Aut (LaxMonoidalFunctor.of (𝟭 C)))
    (S T U : SimpleClasses C) (f : U.repr ⟶ S.repr ⊗ T.repr) (hf : f ≠ 0) :
    simpleAutScalar k hsurj a U.repr =
      simpleAutScalar k hsurj a S.repr * simpleAutScalar k hsurj a T.repr := by
  apply Units.ext
  apply smul_left_injective k hf
  let α := (LaxMonoidalFunctor.forgetAut (𝟭 C) a).asIso.hom
  have ht := NatTrans.IsMonoidal.tensor (τ := α) S.repr T.repr
  simp only [Functor.LaxMonoidal.id_μ, Category.id_comp, Category.comp_id] at ht
  have h := α.naturality f
  simp only [Functor.id_map] at h
  rw [ht, ← simpleAutScalar_smul_id k hsurj a S.repr,
    ← simpleAutScalar_smul_id k hsurj a T.repr,
    ← simpleAutScalar_smul_id k hsurj a U.repr] at h
  simpa [tensorHom_def, smul_smul, mul_comm] using h.symm

/-- A monoidal natural automorphism of the identity gives a character of the universal grading
group whenever every simple object has scalar endomorphisms (`Function.Surjective (algebraMap k
(End X))`): on the degree of a simple object it is the scalar by which the automorphism acts. -/
def monoidalAutCharacterOfSurjective
    (hsurj : ∀ (X : C) [Simple X], Function.Surjective (algebraMap k (End X))) :
    Aut (LaxMonoidalFunctor.of (𝟭 C)) →* (universalGradingGroup C →* kˣ) where
  toFun a := universalGradingGroup.lift (fun S ↦ simpleAutScalar k hsurj a S.repr)
    (simpleAutScalar_tensor k hsurj a)
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
      simpleAutScalar_mul k hsurj a b S.repr

/-- The character on the universal degree of a simple object recovers the component of the
monoidal automorphism at that object. -/
@[simp]
theorem monoidalAutCharacterOfSurjective_degree_smul_id
    (hsurj : ∀ (X : C) [Simple X], Function.Surjective (algebraMap k (End X)))
    (a : Aut (LaxMonoidalFunctor.of (𝟭 C))) (X : C) [Simple X] :
    (monoidalAutCharacterOfSurjective k hsurj a
        (universalGradingGroup.degree (SimpleClasses.classOf X)) : k) • 𝟙 X =
      (LaxMonoidalFunctor.forgetAut (𝟭 C) a).asIso.hom.app X := by
  have h := simpleAutScalar_eq_of_iso k hsurj a (SimpleClasses.classOfReprIso X)
  simp only [monoidalAutCharacterOfSurjective, MonoidHom.coe_mk, OneHom.coe_mk,
    universalGradingGroup.lift_degree, h, simpleAutScalar_smul_id]

/-- The structure map sends the value of `monoidalAutCharacterOfSurjective` at a simple class `S`
to the component of the automorphism at `S.repr`. -/
theorem algebraMap_monoidalAutCharacterOfSurjective_degree
    (hsurj : ∀ (X : C) [Simple X], Function.Surjective (algebraMap k (End X)))
    (a : Aut (LaxMonoidalFunctor.of (𝟭 C))) (S : SimpleClasses C) :
    algebraMap k (End S.repr)
        (monoidalAutCharacterOfSurjective k hsurj a (universalGradingGroup.degree S) : k) =
      End.of ((LaxMonoidalFunctor.forgetAut (𝟭 C) a).asIso.hom.app S.repr) := by
  apply End.ext
  rw [End.algebraMap_asHom]
  simpa only [SimpleClasses.classOf_repr] using
    monoidalAutCharacterOfSurjective_degree_smul_id k hsurj a S.repr

end Surjective

section SurjectiveSemisimple

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [Linear k C] [MonoidalLinear k C]
  [IsFiniteSemisimpleCategory C]

/-- In a finite semisimple category where simple objects have scalar endomorphisms, the character
of the universal grading group determines a monoidal natural automorphism of the identity. -/
theorem monoidalAutCharacterOfSurjective_injective
    (hsurj : ∀ (X : C) [Simple X], Function.Surjective (algebraMap k (End X))) :
    Function.Injective (monoidalAutCharacterOfSurjective k hsurj (C := C)) := by
  intro a b hab
  apply LaxMonoidalFunctor.forgetAut_injective (𝟭 C)
  apply Aut.ext
  apply Iso.ext
  apply natTrans_ext_of_simple
  intro X _
  rw [← monoidalAutCharacterOfSurjective_degree_smul_id k hsurj a X,
    ← monoidalAutCharacterOfSurjective_degree_smul_id k hsurj b X, hab]

end SurjectiveSemisimple

section Character

variable [IsAlgClosed k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [CategoryTheory.Limits.HasKernels C]
  [MonoidalCategory C] [Linear k C] [MonoidalPreadditive C] [MonoidalLinear k C]
  [hfin : ∀ (X : C) [Simple X], FiniteDimensional k (X ⟶ X)]

include hfin

/-- A monoidal natural automorphism of the identity gives a character of the universal grading
group: on the degree of a simple object it is the scalar by which the automorphism acts. -/
@[expose]
def monoidalAutCharacter : Aut (LaxMonoidalFunctor.of (𝟭 C)) →*
    (universalGradingGroup C →* kˣ) :=
  monoidalAutCharacterOfSurjective k fun X _ ↦ (bijective_algebraMap_end_of_simple k X).surjective

/-- The value of the character on a simple degree is the scalar of the corresponding component
of the automorphism. -/
theorem monoidalAutCharacter_degree (a : Aut (LaxMonoidalFunctor.of (𝟭 C)))
    (S : SimpleClasses C) :
    (monoidalAutCharacter (hfin := hfin) k a (universalGradingGroup.degree S) : k) =
      endAlgEquivOfSimple k S.repr
        (End.of ((LaxMonoidalFunctor.forgetAut (𝟭 C) a).asIso.hom.app S.repr)) := by
  rw [eq_comm, endAlgEquivOfSimple_apply_eq_iff]
  simpa only [monoidalAutCharacter, SimpleClasses.classOf_repr] using
    (monoidalAutCharacterOfSurjective_degree_smul_id k _ a S.repr).symm

/-- The character on the universal degree of a simple object recovers the component of the
monoidal automorphism at that object. -/
@[simp]
theorem monoidalAutCharacter_degree_smul_id (a : Aut (LaxMonoidalFunctor.of (𝟭 C)))
    (X : C) [Simple X] :
    (monoidalAutCharacter (hfin := hfin) k a
        (universalGradingGroup.degree (SimpleClasses.classOf X)) : k) • 𝟙 X =
      (LaxMonoidalFunctor.forgetAut (𝟭 C) a).asIso.hom.app X :=
  monoidalAutCharacterOfSurjective_degree_smul_id k _ a X

end Character

section Semisimple

variable [IsAlgClosed k]
variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [Linear k C] [MonoidalLinear k C]
  [hfin : ∀ (X : C) [Simple X], FiniteDimensional k (X ⟶ X)]
  [IsFiniteSemisimpleCategory C]

/-- In a finite semisimple category, the character of the universal grading group determines a
monoidal natural automorphism of the identity. -/
theorem monoidalAutCharacter_injective :
    Function.Injective (monoidalAutCharacter (hfin := hfin) k (C := C)) :=
  monoidalAutCharacterOfSurjective_injective k _

end Semisimple

end TauCeti
