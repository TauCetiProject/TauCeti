/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.Finsupp.Defs

/-!
# Exactness of componentwise maps on finitely supported functions

Applying an exact pair of linear maps to each coefficient preserves exactness. This gives the
exactness step for coefficient sequences identified with finitely supported families, without
requiring injectivity of the first map.
-/

public section

namespace Function.Exact

variable {R M N P α : Type*} [Semiring R]
  [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
  [Module R M] [Module R N] [Module R P]
  {f : M →ₗ[R] N} {g : N →ₗ[R] P}

/-- An exact pair of linear maps remains exact after applying it componentwise to finitely
supported functions. -/
theorem finsupp_mapRange (h : Function.Exact f g) :
    Function.Exact (Finsupp.mapRange.linearMap (α := α) f)
      (Finsupp.mapRange.linearMap (α := α) g) := by
  classical
  intro y
  constructor
  · intro hy
    have hy' (a : α) : g (y a) = 0 := congrArg (fun z : α →₀ P ↦ z a) hy
    choose x hx using fun a ↦ (h (y a)).mp (hy' a)
    let z : α →₀ M := Finsupp.onFinset y.support
      (fun a ↦ if y a = 0 then 0 else x a) (by
        intro a
        split_ifs <;> simp_all)
    refine ⟨z, ?_⟩
    ext a
    by_cases ha : y a = 0 <;> simp [z, ha, hx]
  · rintro ⟨x, rfl⟩
    ext a
    exact h.apply_apply_eq_zero (x a)

end Function.Exact
