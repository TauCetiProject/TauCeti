/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.NonZeroDivisors

/-!
# Divisibility of linear functionals

If a non-zero-divisor `a` divides every value of a linear functional `f : M →ₗ[R] R`, then `f`
is `a` times a linear functional (`LinearMap.exists_smul_eq_of_forall_dvd`). The quotients
`f x / a` are unique because `a` is cancellable, and their uniqueness makes them linear.
-/

public section

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {a : R}

/-- If `a` is a non-zero-divisor dividing every value of a linear functional `f`, then `f` is `a`
times a linear functional. -/
theorem LinearMap.exists_smul_eq_of_forall_dvd {f : M →ₗ[R] R}
    (ha : a ∈ nonZeroDivisors R) (h : ∀ x, a ∣ f x) : ∃ g : M →ₗ[R] R, a • g = f := by
  choose c hc using h
  have hcan : ∀ r s, a * r = a * s → r = s := fun r s ↦ (mul_cancel_left_mem_nonZeroDivisors ha).mp
  refine ⟨{ toFun := c, map_add' := fun x y ↦ hcan _ _ ?_, map_smul' := fun r x ↦ hcan _ _ ?_ },
    LinearMap.ext fun x ↦ ?_⟩
  · rw [← hc, mul_add, ← hc, ← hc, map_add]
  · rw [← hc, RingHom.id_apply, smul_eq_mul, mul_left_comm, ← hc, map_smul, smul_eq_mul]
  · simp [hc]
