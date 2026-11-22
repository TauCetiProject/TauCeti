/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# The constructor `End.of` and the algebraic structure of `End X`

Mathlib describes the monoid, additive group and module structures on `CategoryTheory.End X`
through the projection `End.asHom`. This file records the same compatibilities for the
constructor `End.of : (X ⟶ X) → End X`: it sends `𝟙 X` to `1`, a composite `f ≫ g` to the product
`End.of g * End.of f`, and sums, differences, negatives, zero and scalar multiples to the
corresponding operations in `End X`. As `simp` lemmas they push `End.of` inside expressions built
from morphisms `X ⟶ X`, so that algebra maps out of `End X` can then be applied termwise. We also
compute the structure map of an `R`-linear category, `(algebraMap R (End X) r).asHom = r • 𝟙 X`.
When that structure map is surjective, every endomorphism is a scalar multiple of the identity
(`CategoryTheory.End.exists_smul_id_eq_of_surjective`); over a field with nontrivial `End X`, this
packages into the algebra isomorphism `TauCeti.endAlgEquivOfSurjective : End X ≃ₐ[k] k`.

The native precomposition action of `(End X)ᵐᵒᵖ` on `X ⟶ Y` respects the ground
scalar tower.

When a scalar multiple `r • 𝟙` of the identity is invertible, its inverse commutes with every
morphism (`CategoryTheory.Linear.comp_inv_smul_id`), and an `R`-linear functor keeps it
invertible (`CategoryTheory.Functor.isIso_smul_id_obj`). For `r` a natural number or an integer
these apply in every preadditive category, through Mathlib's `ℕ`- and `ℤ`-linear structures.
An endomorphism with a scalar multiple equal to the identity is invertible
(`CategoryTheory.Linear.isIso_of_smul_eq_id`).

An additive linear functor induces an algebra homomorphism on endomorphisms,
`Functor.mapEndAlgHom`, which is injective when the functor is faithful and bijective
when the functor is bijective on the object's endomorphisms.
-/

public section

namespace CategoryTheory.End

universe w v u

variable {C : Type u} [Category.{v} C] {X : C}

/-- `End.of` sends the identity to `1`. -/
@[simp]
theorem of_id : End.of (𝟙 X) = 1 :=
  rfl

/-- `End.of` sends a composite to the product in the opposite order, since multiplication in
`End X` agrees with function composition. -/
@[simp]
theorem of_comp (f g : X ⟶ X) : End.of (f ≫ g) = End.of g * End.of f :=
  rfl

section Preadditive

variable [Preadditive C]

/-- `End.of` sends the zero morphism to `0`. -/
@[simp]
theorem of_zero : (End.of 0 : End X) = 0 := by
  ext; simp

/-- `End.of` is additive. -/
@[simp]
theorem of_add (f g : X ⟶ X) : End.of (f + g) = End.of f + End.of g := by
  ext; simp

/-- `End.of` commutes with negation. -/
@[simp]
theorem of_neg (f : X ⟶ X) : End.of (-f) = -End.of f := by
  ext; simp

/-- `End.of` commutes with subtraction. -/
@[simp]
theorem of_sub (f g : X ⟶ X) : End.of (f - g) = End.of f - End.of g := by
  ext; simp

/-- `End.of` commutes with scalar multiplication in an `R`-linear category. -/
@[simp]
theorem of_smul {R : Type w} [Semiring R] [Linear R C] (r : R) (f : X ⟶ X) :
    End.of (r • f) = r • End.of f := by
  ext; simp

/-- The structure map `R → End X` of an `R`-linear category sends `r` to `r • 𝟙 X`. -/
@[simp]
theorem algebraMap_asHom {R : Type w} [CommSemiring R] [Linear R C] (r : R) :
    (algebraMap R (End X) r).asHom = r • 𝟙 X := by
  rw [Algebra.algebraMap_eq_smul_one, smul_asHom, one_asHom]

/-- If the structure map `R → End X` is surjective, every endomorphism of `X` is a scalar
multiple `r • 𝟙 X` of the identity. -/
theorem exists_smul_id_eq_of_surjective {R : Type w} [CommSemiring R] [Linear R C]
    (h : Function.Surjective (algebraMap R (End X))) (f : X ⟶ X) : ∃ r : R, r • 𝟙 X = f := by
  obtain ⟨r, hr⟩ := h (End.of f)
  exact ⟨r, by rw [← algebraMap_asHom, hr]⟩

/-- The native precomposition action on morphisms respects ground-semiring scalars. -/
instance hom_isScalarTower_opEnd {R : Type w} [Semiring R] [Linear R C] (Y : C) :
    IsScalarTower R (End X)ᵐᵒᵖ (X ⟶ Y) where
  smul_assoc r d f := by simp [End.smul_left]

end Preadditive

end CategoryTheory.End

namespace TauCeti

open CategoryTheory

universe w v u

section Surjective

variable (k : Type w) [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]

/-- If the structure map `k → End X` of a nontrivial endomorphism algebra over a field `k` is
surjective, it is bijective. -/
theorem bijective_algebraMap_end_of_surjective (X : C) [Nontrivial (End X)]
    (hsurj : Function.Surjective (algebraMap k (End X))) :
    Function.Bijective (algebraMap k (End X)) :=
  ⟨fun a b hab ↦ by_contra fun h ↦ one_ne_zero (α := End X) <| by
    rw [← map_one (algebraMap k (End X)), ← mul_inv_cancel₀ (sub_ne_zero.mpr h),
      map_mul, map_sub, hab, sub_self, zero_mul], hsurj⟩

/-- Packaging scalar endomorphisms as an algebra isomorphism: if `End X` is nontrivial and
`algebraMap k (End X)` is surjective, then `End X` is isomorphic as a `k`-algebra to `k`. -/
noncomputable def endAlgEquivOfSurjective (X : C) [Nontrivial (End X)]
    (hsurj : Function.Surjective (algebraMap k (End X))) : End X ≃ₐ[k] k :=
  (AlgEquiv.ofBijective (Algebra.ofId k (End X)) <| by
    rw [show ⇑(Algebra.ofId k (End X)) = algebraMap k (End X) from funext (Algebra.ofId_apply _)]
    exact bijective_algebraMap_end_of_surjective k X hsurj).symm

variable {k}
variable {X : C} [Nontrivial (End X)] {hsurj : Function.Surjective (algebraMap k (End X))}

/-- The inverse of `endAlgEquivOfSurjective` is the structure map `algebraMap k (End X)`. -/
@[simp]
theorem endAlgEquivOfSurjective_symm_apply (c : k) :
    (endAlgEquivOfSurjective k X hsurj).symm c = algebraMap k (End X) c := by
  rw [endAlgEquivOfSurjective, AlgEquiv.symm_symm, AlgEquiv.ofBijective_apply, Algebra.ofId_apply]

/-- The structure map `algebraMap k (End X)` sends the scalar of an endomorphism `f` back to
`f`. -/
theorem algebraMap_endAlgEquivOfSurjective (f : End X) :
    algebraMap k (End X) (endAlgEquivOfSurjective k X hsurj f) = f := by
  rw [← endAlgEquivOfSurjective_symm_apply (hsurj := hsurj), AlgEquiv.symm_apply_apply]

/-- Every endomorphism of an object with scalar endomorphisms is its scalar times the identity. -/
@[simp]
theorem endAlgEquivOfSurjective_smul_id (f : End X) :
    endAlgEquivOfSurjective k X hsurj f • 𝟙 X = f.asHom := by
  rw [← End.algebraMap_asHom, algebraMap_endAlgEquivOfSurjective]

/-- The scalar of an endomorphism `f` is the unique `c` with `f = c • 𝟙 X`. -/
theorem endAlgEquivOfSurjective_apply_eq_iff (f : End X) (c : k) :
    endAlgEquivOfSurjective k X hsurj f = c ↔ f.asHom = c • 𝟙 X := by
  rw [← AlgEquiv.eq_symm_apply, End.ext_iff, endAlgEquivOfSurjective_symm_apply,
    End.algebraMap_asHom]

end Surjective

end TauCeti

namespace CategoryTheory

variable {C : Type*} [Category C] [Preadditive C] {R : Type*} [Semiring R]
  [CategoryTheory.Linear R C]

/-- The inverse of multiplication by a scalar `r` commutes with every morphism. -/
lemma Linear.comp_inv_smul_id {X Y : C} (f : X ⟶ Y) (r : R) [IsIso (r • 𝟙 X)]
    [IsIso (r • 𝟙 Y)] : f ≫ inv (r • 𝟙 Y) = inv (r • 𝟙 X) ≫ f := by
  rw [IsIso.eq_inv_comp, ← Category.assoc, IsIso.comp_inv_eq]
  simp

/-- An endomorphism with a scalar multiple equal to the identity is invertible. -/
lemma Linear.isIso_of_smul_eq_id {X : C} {t : X ⟶ X} {c : R} (h : c • t = 𝟙 X) : IsIso t :=
  ⟨c • 𝟙 X, by rw [Linear.comp_smul, Category.comp_id, h],
    by rw [Linear.smul_comp, Category.id_comp, h]⟩

/-- If multiplication by a scalar `r` is invertible on `X`, then it is invertible on the image of
`X` under any `R`-linear functor. -/
lemma Functor.isIso_smul_id_obj {D : Type*} [Category D] [Preadditive D]
    [CategoryTheory.Linear R D] (F : C ⥤ D) [F.Linear R] (r : R) (X : C) [IsIso (r • 𝟙 X)] :
    IsIso (r • 𝟙 (F.obj X)) := by
  rw [← F.map_id, ← F.map_smul]
  infer_instance

end CategoryTheory

namespace CategoryTheory.Functor

universe w v v' u u'

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  [Preadditive C] [Preadditive D] (F : C ⥤ D) (R : Type w) [CommSemiring R]
  [CategoryTheory.Linear R C] [CategoryTheory.Linear R D] [F.Additive] [F.Linear R]

/-- An additive linear functor induces an algebra homomorphism on endomorphisms. -/
def mapEndAlgHom (X : C) : End X →ₐ[R] End (F.obj X) where
  __ := F.mapEnd X
  map_zero' := by ext; simp
  map_add' f g := by ext; simp
  commutes' r := by ext; simp

/-- The induced algebra homomorphism acts by the functor on underlying endomorphisms. -/
@[simp]
theorem mapEndAlgHom_asHom (X : C) (f : End X) :
    (F.mapEndAlgHom R X f).asHom = F.map f.asHom :=
  (rfl)

/-- A faithful additive linear functor embeds each endomorphism algebra. -/
theorem mapEndAlgHom_injective [F.Faithful] (X : C) :
    Function.Injective (F.mapEndAlgHom R X) := by
  intro f g h
  apply End.ext
  apply F.map_injective
  simpa only [mapEndAlgHom_asHom] using congrArg End.asHom h

/-- An additive linear functor bijective on an object's endomorphisms induces a
bijective algebra homomorphism on its endomorphism algebra. -/
theorem mapEndAlgHom_bijective (X : C)
    (h : Function.Bijective (F.map : (X ⟶ X) → (F.obj X ⟶ F.obj X))) :
    Function.Bijective (F.mapEndAlgHom R X) := by
  constructor
  · intro f g hfg
    apply End.ext
    apply h.injective
    simpa only [mapEndAlgHom_asHom] using congrArg End.asHom hfg
  · intro g
    obtain ⟨f, hf⟩ := h.surjective g.asHom
    refine ⟨End.of f, End.ext ?_⟩
    simpa only [mapEndAlgHom_asHom] using hf

end CategoryTheory.Functor
