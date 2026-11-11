/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.Ring.Nat

/-!
# Comparing exponents in finite products

`Nat.eq_of_prod_pow_eq_of_le` shows that ordered exponent families on natural-number bases
above `1` agree on a finite set if their products of powers over that set agree. It is used to
compare the numbers of maps between finite semisimple modules in
`TauCeti/RingTheory/Semisimple/Multiplicity.lean`.

`Finset.prod_nonneg_of_nonempty` and `Finset.prod_le_prod_of_nonneg_of_le` are the nonnegativity
and monotonicity of finite products, which need no `ZeroLEOneClass`. Nonnegativity needs a nonempty
index set, since the empty product `1` is the only place where `0 ≤ 1` would be used; monotonicity
holds for every index set, the empty case being `1 ≤ 1`.
-/

public section

namespace Nat

/-- If `1 < C i` and `f i ≤ g i` for every `i ∈ s`, and
`∏ i ∈ s, C i ^ f i = ∏ i ∈ s, C i ^ g i`, then `f i = g i` for every `i ∈ s`. -/
theorem eq_of_prod_pow_eq_of_le {ι : Type*} {s : Finset ι} {C f g : ι → ℕ}
    (hC : ∀ i ∈ s, 1 < C i) (hfg : ∀ i ∈ s, f i ≤ g i)
    (h : ∏ i ∈ s, C i ^ f i = ∏ i ∈ s, C i ^ g i) (i : ι) (hi : i ∈ s) : f i = g i := by
  by_contra hne
  refine (Finset.prod_lt_prod₀ (fun j hj ↦ Nat.pow_pos (zero_lt_one.trans (hC j hj)))
    (fun j hj ↦ Nat.pow_le_pow_right (zero_lt_one.trans (hC j hj)) (hfg j hj))
    ⟨i, hi, Nat.pow_lt_pow_right (hC i hi) ((hfg i hi).lt_of_ne hne)⟩).ne h

end Nat

namespace Finset

variable {ι R : Type*} [CommMonoidWithZero R] [Preorder R] [PosMulMono R] {s : Finset ι}
  {f g : ι → R}

/-- A product of nonnegative terms over a nonempty finset is nonnegative, without
`ZeroLEOneClass`. -/
theorem prod_nonneg_of_nonempty (hs : s.Nonempty) (h0 : ∀ i ∈ s, 0 ≤ f i) :
    0 ≤ ∏ i ∈ s, f i :=
  prod_induction_nonempty _ (0 ≤ ·) (fun _ _ ha hb ↦ mul_nonneg ha hb) hs h0

/-- **Monotonicity of finite products.** If `0 ≤ f i ≤ g i` on a finset `s`, then
`∏ i ∈ s, f i ≤ ∏ i ∈ s, g i`, without `ZeroLEOneClass`: the empty product is `1 ≤ 1`. -/
theorem prod_le_prod_of_nonneg_of_le (h0 : ∀ i ∈ s, 0 ≤ f i)
    (h1 : ∀ i ∈ s, f i ≤ g i) : ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  have := PosMulMono.toMulPosMono (α := R)
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => simpa using h1 a (by simp)
  | cons a s ha hs ih =>
    rw [prod_cons, prod_cons]
    exact mul_le_mul (h1 a (by simp)) (ih (fun i hi ↦ h0 i (by simp [hi]))
      fun i hi ↦ h1 i (by simp [hi]))
      (prod_nonneg_of_nonempty hs fun i hi ↦ h0 i (by simp [hi]))
      ((h0 a (by simp)).trans (h1 a (by simp)))

end Finset
