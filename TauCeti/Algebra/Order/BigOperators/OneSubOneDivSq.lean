/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Products of the factors `1 - 1 / n ^ 2`

The product `∏_{1 < n ≤ N} (1 - 1 / n ^ 2)` telescopes to `(N + 1) / (2 N)`, which decreases to
`1 / 2`. Since every factor lies in `[0, 1]`, the product of these factors over any finite set of
distinct integers `n ≥ 2` is therefore at least `1 / 2`. This bounds from below Euler products
whose factors at the odd primes `p` are at least `1 - (p - 1)⁻²`, such as the singular series of
the three-primes problem.

## Main results

* `TauCeti.one_sub_one_div_sq_mem_Icc`: `0 ≤ 1 - 1 / x ^ 2 ≤ 1` for `x ≥ 1`.
* `TauCeti.prod_Ioc_one_sub_one_div_sq`: `∏_{1 < n ≤ N} (1 - 1 / n ^ 2) = (N + 1) / (2 N)`.
* `TauCeti.half_le_prod_one_sub_one_div_sq`: over distinct integers `n ≥ 2`, every finite product
  of the factors `1 - 1 / n ^ 2` is at least `1 / 2`.
-/

public section

open Finset

namespace TauCeti

variable {K : Type*}

/-- For `x ≥ 1`, the factor `1 - 1 / x ^ 2` lies in `[0, 1]`. -/
theorem one_sub_one_div_sq_mem_Icc [Field K] [LinearOrder K] [IsStrictOrderedRing K] {x : K}
    (hx : 1 ≤ x) : 1 - 1 / x ^ 2 ∈ Set.Icc (0 : K) 1 :=
  ⟨sub_nonneg.2 (div_le_one_of_le₀ (one_le_pow₀ hx) (sq_nonneg x)),
    sub_le_self 1 (by positivity)⟩

/-- `∏_{1 < n ≤ N} (1 - 1 / n ^ 2) = (N + 1) / (2 N)`, a telescoping product. -/
theorem prod_Ioc_one_sub_one_div_sq [Field K] [CharZero K] {N : ℕ} (hN : 1 ≤ N) :
    ∏ n ∈ Ioc 1 N, (1 - 1 / (n : K) ^ 2) = ((N : K) + 1) / (2 * N) := by
  induction N, hN using Nat.le_induction with
  | base => norm_num
  | succ N hN ih =>
    rw [prod_Ioc_succ_top (by omega), ih]
    have h₀ : (N : K) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    field_simp
    push_cast
    ring

/-- Over distinct integers `n ≥ 2`, every finite product of the factors `1 - 1 / n ^ 2` is at
least `1 / 2`. -/
theorem half_le_prod_one_sub_one_div_sq [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {ι : Type*} {s : Finset ι} {f : ι → ℕ} (hf : Set.InjOn f s) (hs : ∀ i ∈ s, 2 ≤ f i) :
    1 / 2 ≤ ∏ i ∈ s, (1 - 1 / (f i : K) ^ 2) := by
  rw [← prod_image (f := fun n : ℕ ↦ 1 - 1 / (n : K) ^ 2) hf]
  set N := max ((s.image f).sup id) 1
  have hN : 1 ≤ N := le_max_right _ _
  have hsub : s.image f ⊆ Ioc 1 N := by
    simp only [subset_iff, mem_image, mem_Ioc]
    rintro _ ⟨i, hi, rfl⟩
    exact ⟨hs i hi, (le_sup (f := id) (mem_image_of_mem f hi)).trans (le_max_left _ _)⟩
  have hfac : ∀ n ∈ Ioc 1 N, 1 - 1 / (n : K) ^ 2 ∈ Set.Icc (0 : K) 1 := fun n hn ↦
    one_sub_one_div_sq_mem_Icc (by exact_mod_cast (mem_Ioc.1 hn).1.le)
  refine le_trans ?_ (prod_le_prod_of_subset_of_le_one₀ hsub (fun n hn ↦ (hfac n hn).1)
    fun n hn _ ↦ (hfac n hn).2)
  rw [prod_Ioc_one_sub_one_div_sq hN, div_le_div_iff₀ (by norm_num) (by positivity)]
  linarith

end TauCeti
