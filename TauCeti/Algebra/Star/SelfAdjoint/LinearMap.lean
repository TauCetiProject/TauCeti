/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.Module
import TauCeti.Algebra.Star.SelfAdjoint

/-!
# Polarization for complex linear maps on star modules

The self-adjoint part spans a complex star module over the complex scalars. A complex
linear map that preserves self-adjoint squares therefore preserves the anticommutator
on the entire module.
-/

public section

namespace LinearMap

/-- A complex linear map on a complex star module that preserves self-adjoint squares
preserves anticommutators. No involution on the codomain is required. -/
theorem map_mul_add_mul_of_map_mul_self_of_isSelfAdjoint
    {A B : Type*} [NonUnitalNonAssocRing A] [StarAddMonoid A] [Module ℂ A]
    [StarModule ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
    [NonUnitalNonAssocRing B] [Module ℂ B] [IsScalarTower ℂ B B] [SMulCommClass ℂ B B]
    (f : A →ₗ[ℂ] B)
    (hf : ∀ x, IsSelfAdjoint x → f (x * x) = f x * f x) (x y : A) :
    f (x * y + y * x) = f x * f y + f y * f x := by
  let symMulA := LinearMap.mul ℂ A + (LinearMap.mul ℂ A).flip
  let symMulB := LinearMap.mul ℂ B + (LinearMap.mul ℂ B).flip
  exact LinearMap.congr_fun₂
    (f := symMulA.compr₂ f) (g := (symMulB ∘ₗ f).compl₂ f)
    (LinearMap.ext_on span_selfAdjoint fun a ha ↦
      LinearMap.ext_on span_selfAdjoint fun b hb ↦
        f.toAddMonoidHom.map_mul_add_mul_of_isSelfAdjoint hf ha hb) x y

end LinearMap
