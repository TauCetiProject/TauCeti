/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.AInfinity.StrictFunctor.Basic
public import TauCeti.CategoryTheory.AInfinity.SingleObj
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Strict

/-!
# Strict functors between one-object A-infinity categories

Strict morphisms of `A∞` algebras are exactly strict functors between their one-object
categories. The correspondence preserves identity and composition. It imposes no
unit condition on either side, and works over any commutative ground ring.

The correspondence transports strict algebra morphisms and their identity and composition
laws to one-object `A∞` categories, and recovers algebra morphisms from strict functors.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.4 and 7.1.
-/

public section

namespace TauCeti

universe uR uA uB uC

open GradedLinearQuiver AInfinitySingleObj

variable {R : Type uR} [CommRing R]
  {A : Type uA} {B : Type uB} {C : Type uC}
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]
  {𝒜 : AInfinityAlgebra R A} {ℬ : AInfinityAlgebra R B} {𝒞 : AInfinityAlgebra R C}

namespace AInfinityStrictHom

/-- A strict algebra morphism as a strict functor between one-object `A∞` categories. -/
noncomputable def toStrictFunctor (f : AInfinityStrictHom 𝒜 ℬ) :
    AInfinityStrictFunctor (aInfinityCategory 𝒜) (aInfinityCategory ℬ) where
  obj _ := star ℬ
  map _ _ := f.toLinearMap
  map_mem' _ _ {_} {_} ha := f.map_mem ha
  map_operation' X x := by
    rw [homProjection_m_homInclusion_aInfinityCategory]
    exact (f.map_m _ _).trans
      (homProjection_m_homInclusion_aInfinityCategory ℬ (fun _ ↦ star ℬ) _).symm

@[simp]
theorem toStrictFunctor_obj (f : AInfinityStrictHom 𝒜 ℬ) (X : AInfinitySingleObj 𝒜) :
    f.toStrictFunctor.obj X = star ℬ := (rfl)

@[simp]
theorem toStrictFunctor_map (f : AInfinityStrictHom 𝒜 ℬ) (X Y : AInfinitySingleObj 𝒜) :
    f.toStrictFunctor.map X Y = f.toLinearMap := (rfl)

end AInfinityStrictHom

namespace AInfinityStrictFunctor

/-- The algebra morphism determined by a strict functor between one-object categories. -/
noncomputable def toStrictHom
    (F : AInfinityStrictFunctor (aInfinityCategory 𝒜) (aInfinityCategory ℬ)) :
    AInfinityStrictHom 𝒜 ℬ where
  toLinearMap := F.map (star 𝒜) (star 𝒜)
  map_mem' ha := F.map_mem _ _ ha
  map_m' n := by
    ext x
    have h := F.map_operation (fun _ ↦ star 𝒜) x
    rw [homProjection_m_homInclusion_aInfinityCategory 𝒜 (fun _ ↦ star 𝒜) x] at h
    exact h.trans (homProjection_m_homInclusion_aInfinityCategory ℬ
      (fun _ ↦ F.obj (star 𝒜)) (fun i ↦ F.map _ _ (x i)))

@[simp]
theorem toStrictHom_toLinearMap
    (F : AInfinityStrictFunctor (aInfinityCategory 𝒜) (aInfinityCategory ℬ)) :
    F.toStrictHom.toLinearMap = F.map (star 𝒜) (star 𝒜) := (rfl)

/-- The algebra morphism associated to the identity functor is the identity morphism. -/
@[simp]
theorem toStrictHom_id (𝒜 : AInfinityAlgebra R A) :
    (AInfinityStrictFunctor.id (aInfinityCategory 𝒜)).toStrictHom =
      AInfinityStrictHom.id 𝒜 := by
  apply AInfinityStrictHom.toLinearMap_injective
  simp only [toStrictHom_toLinearMap, id_map, AInfinityStrictHom.id_toLinearMap]

/-- Passing from one-object strict functors to algebra morphisms preserves composition. -/
@[simp]
theorem toStrictHom_comp
    (G : AInfinityStrictFunctor (aInfinityCategory ℬ) (aInfinityCategory 𝒞))
    (F : AInfinityStrictFunctor (aInfinityCategory 𝒜) (aInfinityCategory ℬ)) :
    (G.comp F).toStrictHom = G.toStrictHom.comp F.toStrictHom := by
  apply AInfinityStrictHom.toLinearMap_injective
  simp only [toStrictHom_toLinearMap, comp_map, AInfinityStrictHom.comp_toLinearMap]

/-- Passing from a one-object strict functor to its algebra morphism and back is a round trip. -/
@[simp]
theorem toStrictFunctor_toStrictHom
    (F : AInfinityStrictFunctor (aInfinityCategory 𝒜) (aInfinityCategory ℬ)) :
    F.toStrictHom.toStrictFunctor = F := by
  have hobj : F.toStrictHom.toStrictFunctor.obj = F.obj :=
    funext fun _ ↦ Subsingleton.elim _ _
  apply ext hobj
  apply heq_of_eq
  funext X Y
  obtain rfl := Subsingleton.elim X (star 𝒜)
  obtain rfl := Subsingleton.elim Y (star 𝒜)
  rfl

end AInfinityStrictFunctor

namespace AInfinityStrictHom

/-- Passing from a strict algebra morphism to its one-object functor and back is a round trip. -/
@[simp]
theorem toStrictHom_toStrictFunctor (f : AInfinityStrictHom 𝒜 ℬ) :
    f.toStrictFunctor.toStrictHom = f := by
  apply toLinearMap_injective
  rfl

/-- Strict algebra morphisms and strict functors between their one-object categories coincide. -/
noncomputable def strictFunctorEquiv :
    AInfinityStrictHom 𝒜 ℬ ≃
      AInfinityStrictFunctor (aInfinityCategory 𝒜) (aInfinityCategory ℬ) where
  toFun := toStrictFunctor
  invFun := AInfinityStrictFunctor.toStrictHom
  left_inv := toStrictHom_toStrictFunctor
  right_inv := AInfinityStrictFunctor.toStrictFunctor_toStrictHom

@[simp]
theorem strictFunctorEquiv_apply (f : AInfinityStrictHom 𝒜 ℬ) :
    strictFunctorEquiv f = f.toStrictFunctor := (rfl)

@[simp]
theorem strictFunctorEquiv_symm_apply
    (F : AInfinityStrictFunctor (aInfinityCategory 𝒜) (aInfinityCategory ℬ)) :
    strictFunctorEquiv.symm F = F.toStrictHom := (rfl)

/-- The one-object comparison preserves identity. -/
@[simp]
theorem toStrictFunctor_id (𝒜 : AInfinityAlgebra R A) :
    (AInfinityStrictHom.id 𝒜).toStrictFunctor =
      AInfinityStrictFunctor.id (aInfinityCategory 𝒜) := by
  apply AInfinityStrictFunctor.ext (funext fun _ ↦ Subsingleton.elim _ _)
  exact heq_of_eq (by
    funext X Y
    simp only [toStrictFunctor_map, id_toLinearMap, AInfinityStrictFunctor.id_map])

/-- The one-object comparison preserves composition. -/
@[simp]
theorem toStrictFunctor_comp (g : AInfinityStrictHom ℬ 𝒞) (f : AInfinityStrictHom 𝒜 ℬ) :
    (g.comp f).toStrictFunctor = g.toStrictFunctor.comp f.toStrictFunctor := by
  apply AInfinityStrictFunctor.ext (funext fun _ ↦ Subsingleton.elim _ _)
  exact heq_of_eq (by
    funext X Y
    simp only [toStrictFunctor_map, comp_toLinearMap, AInfinityStrictFunctor.comp_map])

end AInfinityStrictHom

end TauCeti
