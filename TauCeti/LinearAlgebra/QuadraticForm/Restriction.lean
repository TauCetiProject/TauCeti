/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Lift

/-!
# Restriction of quadratic maps

A quadratic map taking values in a submodule can be regarded as a quadratic map into that
submodule. In a scalar tower, restriction of the domain to a submodule over the smaller ring
determines the quadratic map whenever that submodule spans over the larger ring.
-/

public section

namespace QuadraticMap

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- Restrict the codomain of a quadratic map to a submodule containing its values. -/
def codRestrict (Q : QuadraticMap R M N) (P : Submodule R N) (h : ∀ x, Q x ∈ P) :
    QuadraticMap R M P :=
  ofPolar (fun x ↦ (⟨Q x, h x⟩ : P))
    (fun a x ↦ Subtype.ext (Q.map_smul a x))
    (fun x y z ↦ Subtype.ext (Q.polar_add_left x y z))
    (fun a x y ↦ Subtype.ext (Q.polar_smul_left a x y))

/-- Including a codomain-restricted value recovers the original value. -/
@[simp]
theorem coe_codRestrict_apply (Q : QuadraticMap R M N) (P : Submodule R N)
    (h : ∀ x, Q x ∈ P) (x : M) : (Q.codRestrict P h x : N) = Q x := (rfl)

section Extension

variable {A U D : Type*} [CommRing A] [Algebra R A]
  [AddCommGroup U] [Module R U] [Module A U] [IsScalarTower R A U]
  [AddCommGroup D] [Module A D]

/-- Two quadratic maps over an algebra agree everywhere if they agree along a linear map over
the base ring whose image spans their domain over the algebra. -/
theorem ext_of_span_range_eq_top (f : M →ₗ[R] U)
    (hf : Submodule.span A (LinearMap.range f : Set U) = ⊤)
    {Q Q' : QuadraticMap A U D} (h : ∀ x, Q (f x) = Q' (f x)) : Q = Q' := by
  let : Module R D := Module.compHom D (algebraMap R A)
  have : IsScalarTower R A D := IsScalarTower.of_compHom R A D
  have hsurj : Function.Surjective (f.liftBaseChange A) := by
    rwa [← LinearMap.range_eq_top, LinearMap.range_liftBaseChange]
  have heq : Q.comp (f.liftBaseChange A) = Q'.comp (f.liftBaseChange A) :=
    baseChange_ext fun x ↦ by simpa using h x
  ext x
  obtain ⟨t, rfl⟩ := hsurj x
  exact DFunLike.congr_fun heq t

end Extension

end QuadraticMap
