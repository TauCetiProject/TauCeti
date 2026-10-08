/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Map
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Strict

/-!
# Strict inclusions of pulled-back A-infinity algebras

The injective linear map defining `AInfinityAlgebra.comap` intertwines all operations,
so it defines a strict `A∞` morphism from the pullback to the original algebra.
Its underlying linear map is the given map. This construction supplies the inclusion
of the total algebra of a full `A∞` subcategory.
-/

public section

universe uR uA uB

namespace TauCeti.AInfinityAlgebra

variable {R : Type uR} {A : Type uA} {B : Type uB} [CommRing R]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  (ℬ : AInfinityAlgebra R B) (G : InternalGrading R A) (f : A →ₗ[R] B)
  (hf : Function.Injective f) (hG : ∀ (p : ℤ) (a : A), f a ∈ ℬ.grading.piece p ↔ a ∈ G.piece p)
  (hm : ∀ n, 0 < n → ∀ x : Fin n → A, ℬ.m n (fun i ↦ f (x i)) ∈ LinearMap.range f)

/-- The injective map along which an `A∞` algebra is pulled back, as a strict `A∞` morphism. -/
noncomputable def comapStrictHom : AInfinityStrictHom (ℬ.comap G f hf hG hm) ℬ where
  toLinearMap := f
  map_mem' ha := (hG _ _).2 (by rwa [comap_grading] at ha)
  map_m' n := MultilinearMap.ext fun x ↦ by simp

/-- The underlying linear map of the strict pullback inclusion is the given map. -/
@[simp]
theorem comapStrictHom_toLinearMap :
    (ℬ.comapStrictHom G f hf hG hm).toLinearMap = f := by
  simp [comapStrictHom]

/-- The strict `A∞` morphism `comapStrictHom` is the injective map along which the algebra is
pulled back. -/
@[simp]
theorem coe_comapStrictHom : ⇑(ℬ.comapStrictHom G f hf hG hm) = f :=
  congrArg (fun g : A →ₗ[R] B ↦ ⇑g) (comapStrictHom_toLinearMap ℬ G f hf hG hm)


end TauCeti.AInfinityAlgebra
