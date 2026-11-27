/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TensorProduct.Basic
public import TauCeti.CategoryTheory.Linear.DeligneProduct.Basic
public import TauCeti.CategoryTheory.Preadditive.SingleObj

/-!
# Linear tensor products of one-object categories

The linear tensor product of the one-object categories of two algebras is the one-object
category of the tensor product algebra. The equivalence acts on morphisms by the canonical
identification of the tensor product of the two endomorphism modules with the underlying module
of the tensor product algebra.

The composition formula is the one in B. Mitchell, *Rings with several objects*,
Adv. Math. 8 (1972), §2, p. 13. In Mathlib's `SingleObj`, composition is `f ≫ g = g * f`
in both factors and in the target.
-/

public section

open CategoryTheory TensorProduct

namespace TauCeti.LinearTensor

variable {R A B : Type*} [CommSemiring R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]

private theorem singleObj_homEquiv_comp {X Y Z : LinearTensor R (SingleObj A) (SingleObj B)}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    homEquiv X Z (f ≫ g) = (homEquiv Y Z g : A ⊗[R] B) * homEquiv X Y f := by
  rcases X with ⟨X₁, X₂⟩
  rcases Y with ⟨Y₁, Y₂⟩
  rcases Z with ⟨Z₁, Z₂⟩
  induction f using hom_induction_on with
  | tmul a b =>
    induction g using hom_induction_on with
    | tmul c d =>
      rw [tmul_comp_tmul, homEquiv_tmul, homEquiv_tmul, homEquiv_tmul]
      simp only [SingleObj.comp_as_mul, Algebra.TensorProduct.tmul_mul_tmul]
    | add g g' h h' => simp only [Preadditive.comp_add, map_add, add_mul, h, h']
  | add f f' h h' => simp only [Preadditive.add_comp, map_add, mul_add, h, h']

variable (R A B) in
/-- The `R`-linear equivalence between the tensor of the one-object categories of `A` and
`B` and the one-object category of their tensor product algebra. -/
noncomputable def singleObjEquiv :
    LinearTensor R (SingleObj A) (SingleObj B) ≌ SingleObj (A ⊗[R] B) where
  functor :=
    { obj _ := SingleObj.star _
      map {X Y} f := homEquiv X Y f
      map_id X := by
        rcases X with ⟨X₁, X₂⟩
        rw [← tmul_id_id (k := R) X₁ X₂, homEquiv_tmul, SingleObj.id_as_one A X₁,
          SingleObj.id_as_one B X₂, SingleObj.id_as_one (A ⊗[R] B),
          Algebra.TensorProduct.one_def]
      map_comp f g := singleObj_homEquiv_comp f g }
  inverse :=
    { obj _ := ⟨SingleObj.star A, SingleObj.star B⟩
      map f := (homEquiv _ _).symm f
      map_id X := by
        rw [SingleObj.id_as_one (A ⊗[R] B) X, Algebra.TensorProduct.one_def,
          ← SingleObj.id_as_one A (SingleObj.star A), ← SingleObj.id_as_one B (SingleObj.star B),
          homEquiv_symm_tmul, tmul_id_id]
      map_comp f g := by
        apply (homEquiv _ _).injective
        rw [singleObj_homEquiv_comp]
        simp only [LinearEquiv.apply_symm_apply, SingleObj.comp_as_mul] }
  unitIso := Iso.refl _
  counitIso := Iso.refl _

/-- The forward comparison sends every object to the unique object of the tensor product algebra. -/
@[simp]
theorem singleObjEquiv_functor_obj (X : LinearTensor R (SingleObj A) (SingleObj B)) :
    (singleObjEquiv R A B).functor.obj X = SingleObj.star (A ⊗[R] B) := (rfl)

/-- The inverse comparison sends the unique object to the pair of the two unique objects. -/
@[simp]
theorem singleObjEquiv_inverse_obj (X : SingleObj (A ⊗[R] B)) :
    (singleObjEquiv R A B).inverse.obj X = ⟨SingleObj.star A, SingleObj.star B⟩ := (rfl)

/-- The forward comparison sends a morphism to the underlying element of the tensor product. -/
theorem singleObjEquiv_functor_map {X Y : LinearTensor R (SingleObj A) (SingleObj B)} (f : X ⟶ Y) :
    (singleObjEquiv R A B).functor.map f = homEquiv X Y f := (rfl)

/-- The inverse comparison views an element of the tensor product as a morphism of the pair. -/
theorem singleObjEquiv_inverse_map {X Y : SingleObj (A ⊗[R] B)} (f : X ⟶ Y) :
    (singleObjEquiv R A B).inverse.map f = (homEquiv _ _).symm f := (rfl)

/-- The forward comparison sends a pure tensor of morphisms to the pure tensor in the algebra. -/
@[simp]
theorem singleObjEquiv_functor_map_tmul {X X' : SingleObj A} {Y Y' : SingleObj B}
    (a : X ⟶ X') (b : Y ⟶ Y') :
    (singleObjEquiv R A B).functor.map (tmul a b) = a ⊗ₜ[R] b := (rfl)

/-- The inverse comparison sends a pure tensor in the algebra to the pure tensor of morphisms. -/
@[simp]
theorem singleObjEquiv_inverse_map_tmul {X Y : SingleObj (A ⊗[R] B)} (a : A) (b : B) :
    (singleObjEquiv R A B).inverse.map (X := X) (Y := Y) (a ⊗ₜ[R] b) =
      tmul (X := SingleObj.star A) (X' := SingleObj.star A)
        (Y := SingleObj.star B) (Y' := SingleObj.star B) a b := (rfl)

/-- The forward comparison is additive on morphisms. -/
instance singleObjEquiv_additive : (singleObjEquiv R A B).functor.Additive where
  map_add {_ _ f g} := (homEquiv _ _).map_add f g

/-- The forward comparison preserves the scalar action on morphisms. -/
instance singleObjEquiv_linear : (singleObjEquiv R A B).functor.Linear R where
  map_smul f r := (homEquiv _ _).map_smul r f

end TauCeti.LinearTensor
