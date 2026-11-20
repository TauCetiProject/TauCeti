/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.Defs

/-!
# Divisibility of linear functionals

If a regular element `a` divides every value of a linear functional `f : M →ₗ[R] R`, then `f`
is `a` times a linear functional (`LinearMap.exists_smul_eq_of_forall_dvd`). The quotients
`f x / a` are unique because `a` is cancellable, and their uniqueness makes them linear.
-/

public section

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] {a : R}

/-- If `a` is a regular element dividing every value of a linear functional `f`, then `f` is `a`
times a linear functional. -/
theorem LinearMap.exists_smul_eq_of_forall_dvd {f : M →ₗ[R] R}
    (ha : IsLeftRegular a) (h : ∀ x, a ∣ f x) : ∃ g : M →ₗ[R] R, a • g = f := by
  choose c hc using h
  refine ⟨{ toFun := c, map_add' := fun x y ↦ ha ?_, map_smul' := fun r x ↦ ha ?_ },
    LinearMap.ext fun x ↦ ?_⟩
  · simp only [mul_add, ← hc, map_add]
  · simp only [← hc, RingHom.id_apply, smul_eq_mul, mul_left_comm a, map_smul]
  · simp [hc]
