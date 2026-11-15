/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.MorphismIdeal.Equivalence
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Linear hom spaces of ideal quotients

In a linear category, every two-sided morphism ideal is closed under scalars: scalar
multiplication is composition with a scalar multiple of an identity. Its hom groups therefore
form submodules. The hom spaces of the ideal quotient are canonically linearly equivalent to
the quotients by these submodules. This allows linear algebra, such as dimension calculations,
to be applied to stable hom spaces without forgetting their scalar action.

The equivalence sends a coset represented by a morphism to its image under the quotient
functor. It is natural under linear functors carrying one ideal into another. Such functors,
and the equivalences they induce, remain linear after taking ideal quotients.

## References

* M. Auslander, I. Reiten, S. Smalø, *Representation Theory of Artin Algebras*,
  Chapter IV, Section 1.

The hom-space equivalence uses Mathlib's `LinearMap.quotKerEquivOfSurjective`, applied to
the quotient functor's `Functor.mapLinearMap`.
-/

public section

universe v u v' u'

namespace TauCeti.MorphismIdeal

open CategoryTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {D : Type u'} [Category.{v'} D] [Preadditive D]

section Semiring

variable (R : Type*) [Semiring R] [Linear R C]

/-- The hom subgroup of a two-sided ideal, viewed as a submodule of a linear hom space. -/
def homSubmodule (I : MorphismIdeal C) (X Y : C) : Submodule R (X ⟶ Y) :=
  { (I.hom X Y).toAddSubmonoid with
    smul_mem' := fun a {_} hf ↦ I.smul_mem (R := R) a hf }

@[simp]
theorem mem_homSubmodule (I : MorphismIdeal C) {X Y : C} (f : X ⟶ Y) :
    f ∈ I.homSubmodule R X Y ↔ f ∈ I.hom X Y := Iff.rfl

/-- The kernel of the quotient functor on each linear hom space is the ideal's hom submodule.
-/
@[simp]
theorem ker_quotientFunctor_mapLinearMap (I : MorphismIdeal C) (X Y : C) :
    LinearMap.ker (I.quotientFunctor.mapLinearMap R (X := X) (Y := Y)) =
      I.homSubmodule R X Y := by
  ext f
  simp

variable [Linear R D]

/-- The containment of ideals is exactly the containment required to map their hom-space
quotients using Mathlib's `Submodule.mapQ`. -/
theorem homSubmodule_le_comap (I : MorphismIdeal C) (J : MorphismIdeal D) (F : C ⥤ D)
    [F.Additive] [F.Linear R] (hF : I ≤ J.comap F) {X Y : C} :
    I.homSubmodule R X Y ≤
      (J.homSubmodule R (F.obj X) (F.obj Y)).comap (F.mapLinearMap R) := by
  intro f hf
  exact (mem_comap_hom J F).mp (le_def.mp hF f hf)

/-- A linear functor carrying one ideal into another induces a linear functor on their
quotient categories. -/
instance map_linear (I : MorphismIdeal C) (J : MorphismIdeal D) (F : C ⥤ D)
    [F.Additive] [F.Linear R] (hF : I ≤ J.comap F) : (I.map J F hF).Linear R := by
  rw [map_eq_lift]
  infer_instance

/-- The forward direction of an equivalence of ideal quotients is linear if the original
equivalence is linear. Mathlib's inverse-linearity instance supplies the inverse direction. -/
instance mapEquivalence_functor_linear (e : C ≌ D) [e.functor.Additive]
    [e.functor.Linear R] (I : MorphismIdeal C) (J : MorphismIdeal D)
    (h : I = J.comap e.functor) : (mapEquivalence e I J h).functor.Linear R := by
  rw [mapEquivalence_functor]
  infer_instance

end Semiring

section Ring

variable (R : Type*) [Ring R] [Linear R C] (I : MorphismIdeal C)

@[simp]
theorem homSubmodule_toAddSubgroup (X Y : C) :
    (I.homSubmodule R X Y).toAddSubgroup = I.hom X Y := by
  ext
  rfl

/-- The hom space of the ideal quotient is canonically the quotient of the original linear
hom space by the ideal's hom submodule. -/
noncomputable def homLinearEquiv (X Y : C) :
    ((X ⟶ Y) ⧸ I.homSubmodule R X Y) ≃ₗ[R]
      (I.quotientFunctor.obj X ⟶ I.quotientFunctor.obj Y) :=
  Submodule.quotEquivOfEq _ _ (I.ker_quotientFunctor_mapLinearMap R X Y).symm ≪≫ₗ
    (I.quotientFunctor.mapLinearMap R).quotKerEquivOfSurjective
      I.quotientFunctor.map_surjective

/-- A coset represented by a morphism corresponds to its quotient class. -/
@[simp]
theorem homLinearEquiv_mk {X Y : C} (f : X ⟶ Y) :
    I.homLinearEquiv R X Y (Submodule.Quotient.mk f) = I.quotientFunctor.map f := by
  rw [homLinearEquiv, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk]
  exact LinearMap.quotKerEquivOfSurjective_apply_mk _ _ f

/-- The inverse hom-space identification takes a represented quotient morphism to its coset. -/
@[simp]
theorem homLinearEquiv_symm_quotientFunctor_map {X Y : C} (f : X ⟶ Y) :
    (I.homLinearEquiv R X Y).symm (I.quotientFunctor.map f) = Submodule.Quotient.mk f := by
  apply (I.homLinearEquiv R X Y).injective
  simp

variable [Linear R D] (J : MorphismIdeal D) (F : C ⥤ D) [F.Additive] [F.Linear R]
  (hF : I ≤ J.comap F)

include hF

/-- The hom-space identification is natural under a linear functor carrying ideals into
ideals. The endpoint transports use the object formula of the induced quotient functor. -/
theorem homLinearEquiv_mapQ {X Y : C} (x : (X ⟶ Y) ⧸ I.homSubmodule R X Y) :
    J.homLinearEquiv R (F.obj X) (F.obj Y)
        ((I.homSubmodule R X Y).mapQ (J.homSubmodule R (F.obj X) (F.obj Y))
          (F.mapLinearMap R) (I.homSubmodule_le_comap R J F hF) x) =
      eqToHom (I.map_obj_quotientFunctor_obj J F hF X).symm ≫
        (I.map J F hF).map (I.homLinearEquiv R X Y x) ≫
          eqToHom (I.map_obj_quotientFunctor_obj J F hF Y) := by
  induction x using Submodule.Quotient.induction_on with
  | _ f =>
    simp [map_map_quotientFunctor_map]

end Ring

end TauCeti.MorphismIdeal
