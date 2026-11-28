/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Unitary
public import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Unitary elements of a field with a nontrivial involution

An infinite field `K` whose involution `star` is not the identity has infinitely many unitary
elements, that is elements `u` with `star u * u = 1`
(`Unitary.infinite_of_exists_star_ne`). For any `z` not fixed by `star`, the quotients
`(m + z) / (m + star z)`, with `m` in the fixed field, are pairwise distinct elements of norm one.
For a CM field with complex conjugation these are the norm-one elements of the field, the
unitary scalars of every unitary group over it.
-/

public section

namespace Unitary

/-- **An infinite field with a nontrivial involution has infinitely many unitary elements.**
For `star z ≠ z`, the elements `(m + z) / (m + star z)`, with `m` in the fixed field, are unitary
and pairwise distinct. This works in every characteristic. -/
theorem infinite_of_exists_star_ne {K : Type*} [Field K] [Infinite K] [StarRing K]
    (h : ∃ z : K, star z ≠ z) : Infinite (unitary K) := by
  obtain ⟨z, hz⟩ := h
  -- The two traces distinguish elements of `K`, so the fixed field is infinite.
  let T : K → selfAdjoint K := fun x ↦ ⟨x + star x, by
    change star (x + star x) = x + star x
    simp [add_comm]⟩
  have hinj : Function.Injective (fun x ↦ (T x, T (z * x))) := by
    intro x y hxy
    have h₁ : x + star x = y + star y := congrArg (fun p ↦ (p.1 : K)) hxy
    have h₂ : z * x + star z * star x = z * y + star z * star y := by
      simpa [T, star_mul, mul_comm] using congrArg (fun p ↦ (p.2 : K)) hxy
    have h : (z - star z) * (x - y) = 0 := by linear_combination h₂ - star z * h₁
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hz.symm))
  have : Infinite (selfAdjoint K × selfAdjoint K) := Infinite.of_injective _ hinj
  have : Infinite (selfAdjoint K) :=
    (infinite_prod.mp inferInstance).elim And.left And.right
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
    rw [mem_iff_star_mul_self, star_div₀, star_add, star_add,
      selfAdjoint.star_val_eq, star_star, div_mul_div_comm,
      mul_comm ((m : K) + star z), div_self (mul_ne_zero (hnum m) (hden m))]
  refine Infinite.of_injective (fun m : selfAdjoint K ↦ ⟨_, hmem m⟩) fun m m' hmm' ↦ ?_
  have h := congrArg Subtype.val hmm'
  change ((m : K) + z) / (m + star z) = ((m' : K) + z) / (m' + star z) at h
  rw [div_eq_div_iff (hden m) (hden m')] at h
  have h' : (z - star z) * ((m' : K) - m) = 0 := by linear_combination h
  exact Subtype.ext (sub_eq_zero.mp
    ((mul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr hz.symm))).symm

end Unitary
