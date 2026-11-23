/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Invertible
public import Mathlib.Algebra.Star.Module
public import Mathlib.Basic.Real.Star
public import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Tactic.Linarith
import TauCeti.Algebra.Star.SelfAdjoint

/-!
# Polarization and symmetrization for linear maps on star modules

The self-adjoint part spans a complex star module over the complex scalars. A complex
linear map that preserves self-adjoint squares therefore preserves the anticommutator
on the entire module.

For a real-linear functional `t : E →ₗ[ℝ] ℝ`, precomposing with `selfAdjointPart ℝ` yields its
star-symmetrization `x ↦ (t x + t (star x)) / 2`, which preserves cyclicity and strict positivity on
`x * star x`.
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

section

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [StarAddMonoid E] [StarModule ℝ E]
  (t : E →ₗ[ℝ] ℝ)

/-- Evaluating `(t.comp (selfAdjoint.submodule ℝ E).subtype).comp (selfAdjointPart ℝ)` gives
`(t x + t (star x)) / 2`. -/
theorem comp_selfAdjointPart_apply (x : E) :
    ((t.comp (selfAdjoint.submodule ℝ E).subtype).comp (selfAdjointPart ℝ)) x =
      (t x + t (star x)) / 2 := by
  -- Unfold `LinearMap.comp` and the `selfAdjoint.submodule` / `selfAdjoint E` subtype coercions.
  change t (selfAdjointPart ℝ x : E) = (t x + t (star x)) / 2
  rw [selfAdjointPart_apply_coe, map_smul, map_add, smul_eq_mul, invOf_eq_inv, div_eq_inv_mul]

/-- The symmetrization `(t.comp (selfAdjoint.submodule ℝ E).subtype).comp (selfAdjointPart ℝ)` is
star-invariant. -/
theorem comp_selfAdjointPart_star (x : E) :
    ((t.comp (selfAdjoint.submodule ℝ E).subtype).comp (selfAdjointPart ℝ)) (star x) =
      ((t.comp (selfAdjoint.submodule ℝ E).subtype).comp (selfAdjointPart ℝ)) x := by
  simp only [comp_selfAdjointPart_apply, star_star, add_comm]

end

/-- The symmetrization `(t.comp (selfAdjoint.submodule ℝ E).subtype).comp (selfAdjointPart ℝ)`
inherits cyclicity from `t`. -/
theorem comp_selfAdjointPart_cyclic {E : Type*} [NonUnitalNonAssocRing E] [Module ℝ E] [StarRing E]
    [StarModule ℝ E] {t : E →ₗ[ℝ] ℝ} (hcyclic : ∀ x y : E, t (x * y) = t (y * x)) (x y : E) :
    ((t.comp (selfAdjoint.submodule ℝ E).subtype).comp (selfAdjointPart ℝ)) (x * y) =
      ((t.comp (selfAdjoint.submodule ℝ E).subtype).comp (selfAdjointPart ℝ)) (y * x) := by
  simp only [comp_selfAdjointPart_apply, star_mul, hcyclic x y, hcyclic (star y) (star x)]

/-- The symmetrization `(t.comp (selfAdjoint.submodule ℝ E).subtype).comp (selfAdjointPart ℝ)`
inherits strict positivity on `x * star x` from `t`. -/
theorem comp_selfAdjointPart_mul_star_pos {E : Type*} [NonUnitalNonAssocRing E] [Module ℝ E]
    [StarRing E] [StarModule ℝ E] {t : E →ₗ[ℝ] ℝ}
    (hpos : ∀ x : E, x ≠ 0 → 0 < t (x * star x)) {x : E} (hx : x ≠ 0) :
    0 < ((t.comp (selfAdjoint.submodule ℝ E).subtype).comp (selfAdjointPart ℝ)) (x * star x) := by
  have h := hpos x hx; simp only [comp_selfAdjointPart_apply, star_mul, star_star]; linarith

end LinearMap
