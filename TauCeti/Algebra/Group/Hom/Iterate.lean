/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Data.Set.Function

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# One minus a locally nilpotent additive endomorphism

If every element of a subgroup `K` is killed by some iterate of an additive endomorphism `T`
preserving `K`, then `x ↦ x - T x` is a bijection of `K`: the inverse of `b` is the finite sum
`b + T b + ⋯ + T^[N - 1] b` for any `N` with `T^[N] b = 0`.
-/

public section

namespace AddMonoidHom

variable {A : Type*} [AddCommGroup A]

/-- One minus an additive endomorphism `T` is a bijection of a `T`-stable subgroup on which `T`
is locally nilpotent. -/
theorem bijOn_sub_of_exists_iterate_eq_zero (T : A →+ A) {K : AddSubgroup A}
    (hT : Set.MapsTo T K K) (hnil : ∀ x ∈ K, ∃ N, T^[N] x = 0) :
    Set.BijOn (fun x ↦ x - T x) K K := by
  have hiter (x : A) (hx : x ∈ K) (k : ℕ) : T^[k] x ∈ K := hT.iterate k hx
  refine ⟨fun x hx ↦ K.sub_mem hx (hT hx), fun x hx y hy h ↦ ?_, fun b hb ↦ ?_⟩
  · have hd : T (x - y) = x - y := by
      rw [map_sub]
      exact (sub_eq_sub_iff_sub_eq_sub.mp h).symm
    obtain ⟨N, hN⟩ := hnil _ (K.sub_mem hx hy)
    rw [← sub_eq_zero, ← hN, Function.iterate_fixed hd]
  · obtain ⟨N, hN⟩ := hnil b hb
    refine ⟨∑ k ∈ Finset.range N, T^[k] b, K.sum_mem fun k _ ↦ hiter b hb k, ?_⟩
    simp only [map_sum, ← Finset.sum_sub_distrib, ← Function.iterate_succ_apply' T]
    rw [Finset.sum_range_sub', Function.iterate_zero_apply, hN, sub_zero]

end AddMonoidHom
