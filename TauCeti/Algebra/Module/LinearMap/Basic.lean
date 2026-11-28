/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.Basic

/-!
# Splitting by left multiplication

In a (not necessarily associative) ring `A`, left multiplication by `a` and by `1 - a` add up
to the identity (`LinearMap.mulLeft_add_mulLeft_one_sub`). Hence a composite `f ∘ g` through `A`
splits as `f ∘ a ∘ g + f ∘ (1 - a) ∘ g`
(`LinearMap.comp_eq_comp_mulLeft_comp_add_comp_mulLeft_one_sub_comp`).
With `a` a cutoff function, this splits a composition of operators into a part near the support
of the cutoff and a part away from it.
-/

public section

namespace LinearMap

variable {R A M N : Type*} [Semiring R] [NonAssocRing A] [Module R A] [SMulCommClass R A A]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- Left multiplication by `a` and by `1 - a` add up to the identity. -/
theorem mulLeft_add_mulLeft_one_sub (a : A) :
    mulLeft R a + mulLeft R (1 - a) = LinearMap.id := by
  ext b
  simp [sub_mul]

/-- **Splitting a composite by left multiplication.** For linear maps `f : A → N`, `g : M → A`
and `a : A`, `f ∘ g = f ∘ a ∘ g + f ∘ (1 - a) ∘ g`. -/
theorem comp_eq_comp_mulLeft_comp_add_comp_mulLeft_one_sub_comp (f : A →ₗ[R] N)
    (g : M →ₗ[R] A) (a : A) :
    f ∘ₗ g = f ∘ₗ mulLeft R a ∘ₗ g + f ∘ₗ mulLeft R (1 - a) ∘ₗ g := by
  rw [← comp_add, ← add_comp, mulLeft_add_mulLeft_one_sub, id_comp]

end LinearMap
