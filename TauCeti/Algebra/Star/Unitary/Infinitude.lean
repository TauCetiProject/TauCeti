/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.SelfAdjoint
public import Mathlib.Algebra.Star.Unitary
public import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Infinitely many unitary elements

An infinite field whose involution is not the identity has infinitely many unitary (norm-one)
elements, in every characteristic. For `z` not fixed by `star`, the quotients
`(m + z) / (m + star z)`, with `m` self-adjoint, are pairwise distinct unitary elements, and there
are infinitely many self-adjoint `m` because `x` is determined by the self-adjoint elements
`x + star x` and `z * x + star (z * x)`.

For a CM field with complex conjugation, the unitary elements are the norm-one elements of the
field, the unitary scalars of every unitary group over it. Infinitely many such scalars are what
lets a scalar translate avoid the complement of a Cayley chart.

## Main results

* `selfAdjoint.infinite_of_exists_star_ne`: an infinite commutative ring without zero divisors
  whose involution is not the identity has infinitely many self-adjoint elements.
* `Unitary.infinite_of_exists_star_ne`: an infinite field whose involution is not the identity
  has infinitely many unitary elements.
-/

public section

/-- An infinite commutative ring without zero divisors whose involution is not the identity has
infinitely many self-adjoint elements. -/
theorem selfAdjoint.infinite_of_exists_star_ne {R : Type*} [CommRing R] [NoZeroDivisors R]
    [StarRing R] [Infinite R] (h : ∃ z : R, star z ≠ z) : Infinite (selfAdjoint R) := by
  obtain ⟨z, hz⟩ := h
  -- An element `x` is determined by the self-adjoint elements `x + star x` and
  -- `z * x + star (z * x)`.
  let T : R → selfAdjoint R := fun x ↦ ⟨x + star x, IsSelfAdjoint.add_star_self x⟩
  have hinj : Function.Injective (fun x ↦ (T x, T (z * x))) := by
    intro x y hxy
    have h₁ : x + star x = y + star y := congrArg (fun p ↦ (p.1 : R)) hxy
    have h₂ : z * x + star z * star x = z * y + star z * star y := by
      simpa [T, star_mul, mul_comm] using congrArg (fun p ↦ (p.2 : R)) hxy
    exact mul_left_cancel₀ (sub_ne_zero.mpr hz.symm) (by linear_combination h₂ - star z * h₁)
  have : Infinite (selfAdjoint R × selfAdjoint R) := Infinite.of_injective _ hinj
  exact (infinite_prod.mp inferInstance).elim And.left And.right

namespace Unitary

/-- **An infinite field whose involution is not the identity has infinitely many unitary
elements**, in every characteristic. -/
theorem infinite_of_exists_star_ne {K : Type*} [Field K] [Infinite K] [StarRing K]
    (h : ∃ z : K, star z ≠ z) : Infinite (unitary K) := by
  have := selfAdjoint.infinite_of_exists_star_ne h
  obtain ⟨z, hz⟩ := h
  have hden : ∀ m : selfAdjoint K, (m : K) + star z ≠ 0 := by
    intro m hm
    apply hz
    have hs := congrArg star hm
    simp only [star_add, selfAdjoint.star_val_eq, star_star, star_zero] at hs
    linear_combination hm - hs
  have hnum : ∀ m : selfAdjoint K, (m : K) + z ≠ 0 := by
    intro m hm
    apply hden m
    simpa only [star_add, selfAdjoint.star_val_eq, star_zero] using congrArg star hm
  have hmem : ∀ m : selfAdjoint K, ((m : K) + z) / (m + star z) ∈ unitary K := by
    intro m
    rw [mem_iff_star_mul_self]
    simp only [star_div₀, star_add, selfAdjoint.star_val_eq, star_star]
    field_simp [hnum m, hden m]
  -- The quotients `(m + z) / (m + star z)` are pairwise distinct.
  refine Infinite.of_injective (fun m : selfAdjoint K ↦ ⟨_, hmem m⟩) fun m m' hmm' ↦ ?_
  have h : ((m : K) + z) / (m + star z) = ((m' : K) + z) / (m' + star z) :=
    congrArg Subtype.val hmm'
  rw [div_eq_div_iff (hden m) (hden m')] at h
  exact Subtype.ext (mul_left_cancel₀ (sub_ne_zero.mpr hz.symm) (by linear_combination -h))

end Unitary
