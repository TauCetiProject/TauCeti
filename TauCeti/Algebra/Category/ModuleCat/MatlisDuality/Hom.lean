/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.MatlisDuality.FiniteLength

/-!
# Linear Hom equivalence for Matlis duality

Dualizing morphisms of right modules into a module of finite scalar length gives a linear
equivalence with the corresponding reversed Hom space of left modules.
-/

public section

namespace ModuleCat

open CategoryTheory TauCeti
open scoped ModuleCat.Algebra

universe u v w t

attribute [local instance] moduleOfAlgebra isScalarTower_moduleOfAlgebra

variable {R : Type u} [CommRing R] {E : Type v} [AddCommGroup E] [Module R E]
  [Module.Injective R E] [Small.{v} R] {A : Type w} [Ring A] [Algebra R A]
  {N N' : ModuleCat.{max v t} Aᵐᵒᵖ}

/-- Matlis duality is linear and bijective on morphisms of right modules into a module of
finite length over the scalar ring. -/
noncomputable def matlisDualOpHomLinearEquiv
    (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] E) = 1)
    (hN' : IsFiniteLength R N') :
    (N ⟶ N') ≃ₗ[R] (matlisDualOpObj R E N' ⟶ matlisDualOpObj R E N) := by
  refine LinearEquiv.ofBijective
    { toFun := matlisDualOpMap R E
      map_add' := matlisDualOpMap_add R E
      map_smul' := fun c f ↦ ?_ } (bijective_matlisDualOpMap hE hN')
  ext φ : 2
  apply (matlisDualOpObjEquiv R E N).injective
  ext x
  simp only [matlisDualOpObjEquiv_map_apply]
  have hφ (y : matlisDualOpObj R E N) :
      matlisDualOpObjEquiv R E N (c • y) = c • matlisDualOpObjEquiv R E N y := by
    rw [← IsScalarTower.algebraMap_smul A c y, map_smul, IsScalarTower.algebraMap_smul]
  simp only [RingHom.id_apply, hom_smul, LinearMap.smul_apply]
  rw [map_smul, hφ, map_smul, LinearMap.smul_apply, matlisDualOpObjEquiv_map_apply]

/-- The Hom equivalence sends a morphism to its Matlis dual. -/
@[simp]
theorem matlisDualOpHomLinearEquiv_apply
    (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] E) = 1)
    (hN' : IsFiniteLength R N') (f : N ⟶ N') :
    matlisDualOpHomLinearEquiv hE hN' f = matlisDualOpMap R E f :=
  (rfl)

end ModuleCat
