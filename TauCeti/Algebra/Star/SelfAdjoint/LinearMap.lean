/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Invertible
public import Mathlib.Algebra.Star.Module
public import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Basic.Real.Star
import TauCeti.Algebra.Star.SelfAdjoint

/-!
# Polarization and symmetrization for linear maps on star modules

Complex linear maps preserving self-adjoint squares preserve anticommutators. Over a commutative
ring with trivial star and invertible `2`, precomposing `t` with `selfAdjointPart R` yields its
star-symmetrization `x ↦ ⅟2 • (t x + t (star x))`.
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

variable {R E M : Type*} [CommRing R] [StarMul R] [TrivialStar R] [Invertible (2 : R)]
  [AddCommGroup E] [Module R E] [StarAddMonoid E] [StarModule R E]
  [AddCommMonoid M] [Module R M] (t : E →ₗ[R] M)

/-- Evaluating `(t.comp (selfAdjoint.submodule R E).subtype).comp (selfAdjointPart R)` gives
`(⅟2 : R) • (t x + t (star x))`. -/
theorem comp_selfAdjointPart_apply (x : E) :
    ((t.comp (selfAdjoint.submodule R E).subtype).comp (selfAdjointPart R)) x =
      (⅟2 : R) • (t x + t (star x)) := by
  erw [LinearMap.comp_apply, LinearMap.comp_apply, Submodule.subtype_apply,
    selfAdjointPart_apply_coe]; rw [map_smul, map_add]

/-- The symmetrization `(t.comp (selfAdjoint.submodule R E).subtype).comp (selfAdjointPart R)` is
star-invariant. -/
@[simp] theorem comp_selfAdjointPart_star (x : E) :
    ((t.comp (selfAdjoint.submodule R E).subtype).comp (selfAdjointPart R)) (star x) =
      ((t.comp (selfAdjoint.submodule R E).subtype).comp (selfAdjointPart R)) x := by
  simp only [comp_selfAdjointPart_apply, star_star, add_comm]

/-- On self-adjoint elements,
`(t.comp (selfAdjoint.submodule R E).subtype).comp (selfAdjointPart R)` agrees with `t`. -/
theorem comp_selfAdjointPart_apply_of_isSelfAdjoint {x : E} (hx : IsSelfAdjoint x) :
    ((t.comp (selfAdjoint.submodule R E).subtype).comp (selfAdjointPart R)) x = t x := by
  erw [LinearMap.comp_apply, LinearMap.comp_apply, Submodule.subtype_apply,
    hx.coe_selfAdjointPart_apply R]

end

/-- The symmetrization `(t.comp (selfAdjoint.submodule R E).subtype).comp (selfAdjointPart R)`
inherits cyclicity from `t`. -/
theorem comp_selfAdjointPart_cyclic {R E M : Type*} [CommRing R] [StarMul R] [TrivialStar R]
    [Invertible (2 : R)] [NonUnitalNonAssocRing E] [Module R E] [StarRing E] [StarModule R E]
    [AddCommMonoid M] [Module R M] {t : E →ₗ[R] M}
    (hcyclic : ∀ x y : E, t (x * y) = t (y * x)) (x y : E) :
    ((t.comp (selfAdjoint.submodule R E).subtype).comp (selfAdjointPart R)) (x * y) =
      ((t.comp (selfAdjoint.submodule R E).subtype).comp (selfAdjointPart R)) (y * x) := by
  simp only [comp_selfAdjointPart_apply, star_mul, hcyclic x y, hcyclic (star y) (star x)]

/-- The symmetrization `(t.comp (selfAdjoint.submodule ℝ E).subtype).comp (selfAdjointPart ℝ)`
inherits strict positivity on `x * star x` from `t`. -/
theorem comp_selfAdjointPart_mul_star_pos {E : Type*} [NonUnitalNonAssocRing E] [Module ℝ E]
    [StarRing E] [StarModule ℝ E] {t : E →ₗ[ℝ] ℝ}
    (hpos : ∀ x : E, x ≠ 0 → 0 < t (x * star x)) {x : E} (hx : x ≠ 0) :
    0 < ((t.comp (selfAdjoint.submodule ℝ E).subtype).comp (selfAdjointPart ℝ)) (x * star x) := by
  rw [comp_selfAdjointPart_apply_of_isSelfAdjoint t (IsSelfAdjoint.mul_star_self x)]
  exact hpos x hx

end LinearMap
