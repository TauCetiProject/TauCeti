/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Archimedean.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.GroupTheory.ArchimedeanDensely

/-!
# Power comparisons in ordered monoids with zero

This file collects power-comparison lemmas for nonnegative elements of a linearly ordered monoid
with zero and divisibility rigidity in discrete archimedean ordered groups with zero:

* a comparison `x ^ m ≤ y ^ n` depends only on the ratio `m : n`
  (`TauCeti.pow_le_pow_iff_of_mul_eq`);
* replacing the base `c ≥ 0` by `max 1 c ≥ 1` allows raising the exponent (`c ^ m ≤ max 1 c ^ n`
  for `m ≤ n`) and re-basing shifted or rescaled geometric bounds (`c ^ m ≤ (max 1 c ^ k) ^ n`
  for `m ≤ k * n`);
* in a `MulArchimedean` `LinearOrderedCommGroupWithZero` admitting a largest element strictly
  below `1`, no nonzero element other than `1` is a `k`-th power for arbitrarily large `k : ℕ`
  (`TauCeti.eq_one_of_forall_exists_le_pow_eq`).

## Main results

* `TauCeti.pow_le_pow_iff_of_mul_eq`: `x ^ m ≤ y ^ n ↔ x ^ m' ≤ y ^ n'` when the exponent pairs
  `(m, n)` and `(m', n')` are proportional.
* `TauCeti.pow_le_max_one_pow`: `c ^ m ≤ max 1 c ^ n` for `0 ≤ c` and `m ≤ n`.
* `TauCeti.pow_le_max_one_pow_pow`: `c ^ m ≤ (max 1 c ^ k) ^ n` for `0 ≤ c` and `m ≤ k * n`.
* `TauCeti.eq_one_of_forall_exists_le_pow_eq`: in a `MulArchimedean`
  `LinearOrderedCommGroupWithZero Γ` admitting a largest element strictly below `1`, a nonzero
  element that is a `k`-th power for arbitrarily large `k : ℕ` equals `1`.
-/

public section

namespace TauCeti

/-- In a linearly ordered monoid with zero, raising both sides of `x ^ m ≤ y ^ n` to a nonzero
power does not change it, so for nonnegative `x` and `y` the comparison depends only on the ratio
of the exponents: if `(m, n)` and `(m', n')` are proportional, with
`m * c = m' * c'` and `n * c = n' * c'` for nonzero `c` and `c'`, then
`x ^ m ≤ y ^ n ↔ x ^ m' ≤ y ^ n'`. -/
theorem pow_le_pow_iff_of_mul_eq {M₀ : Type*} [MonoidWithZero M₀] [LinearOrder M₀]
    [ZeroLEOneClass M₀] [PosMulStrictMono M₀] [MulPosMono M₀] {x y : M₀} (hx : 0 ≤ x) (hy : 0 ≤ y)
    {m n m' n' c c' : ℕ} (hc : c ≠ 0) (hc' : c' ≠ 0) (hm : m * c = m' * c')
    (hn : n * c = n' * c') : x ^ m ≤ y ^ n ↔ x ^ m' ≤ y ^ n' := by
  calc x ^ m ≤ y ^ n ↔ (x ^ m) ^ c ≤ (y ^ n) ^ c :=
        (pow_le_pow_iff_left₀ (pow_nonneg hx _) (pow_nonneg hy _) hc).symm
    _ ↔ (x ^ m') ^ c' ≤ (y ^ n') ^ c' := by simp only [← pow_mul, hm, hn]
    _ ↔ x ^ m' ≤ y ^ n' := pow_le_pow_iff_left₀ (pow_nonneg hx _) (pow_nonneg hy _) hc'

/-- For a nonnegative element `c` of a linearly ordered monoid with zero and exponents `m ≤ n`,
`c ^ m ≤ max 1 c ^ n`. -/
theorem pow_le_max_one_pow {M₀ : Type*} [MonoidWithZero M₀] [LinearOrder M₀]
    [ZeroLEOneClass M₀] [PosMulMono M₀] [MulPosMono M₀]
    {c : M₀} (hc : 0 ≤ c) {m n : ℕ} (hmn : m ≤ n) :
    c ^ m ≤ max 1 c ^ n :=
  (pow_le_pow_left₀ hc (le_max_right 1 c) m).trans (pow_le_pow_right₀ (le_max_left 1 c) hmn)

/-- For a nonnegative element `c` of a linearly ordered monoid with zero and `m ≤ k * n`,
`c ^ m ≤ (max 1 c ^ k) ^ n`. This re-bases shifted or rescaled geometric bounds such as
`c ^ (n + 2) ≤ (max 1 c ^ 2) ^ (n + 1)` back to exponent `n`. -/
theorem pow_le_max_one_pow_pow {M₀ : Type*} [MonoidWithZero M₀] [LinearOrder M₀]
    [ZeroLEOneClass M₀] [PosMulMono M₀] [MulPosMono M₀]
    {c : M₀} (hc : 0 ≤ c) {k m n : ℕ} (h : m ≤ k * n) :
    c ^ m ≤ (max 1 c ^ k) ^ n := by
  rw [← pow_mul]
  exact pow_le_max_one_pow hc h

/-- A nonzero element of a discrete archimedean ordered group with zero that admits `k`-th roots
for arbitrarily large `k : ℕ` is at least `1`. -/
private theorem one_le_of_forall_exists_le_pow_eq {Γ : Type*}
    [LinearOrderedCommGroupWithZero Γ] [MulArchimedean Γ]
    (hu : ∃ u : Γ, u < 1 ∧ ∀ δ < 1, δ ≤ u) {γ : Γ} (hγ : γ ≠ 0)
    (h : ∀ n : ℕ, ∃ k ≥ n, ∃ δ : Γ, δ ^ k = γ) :
    1 ≤ γ := by
  obtain ⟨u, hu1, hle⟩ := hu
  by_contra! hlt
  obtain ⟨n, hn⟩ := exists_pow_lt₀ hu1 (Units.mk0 γ hγ)
  simp only [Units.val_mk0] at hn
  obtain ⟨k, hkn, δ, hδ⟩ := h n
  have hδ1 : δ < 1 := by
    by_contra! h1
    exact hlt.not_ge ((one_le_pow₀ h1).trans_eq hδ)
  have hpow : δ ^ k ≤ u ^ n :=
    (pow_le_pow_left' (hle δ hδ1) k).trans (pow_le_pow_of_le_one zero_le hu1.le hkn)
  exact hn.not_ge (hδ ▸ hpow)

/-- **No nontrivial arbitrarily divisible values in a discrete archimedean ordered group with
zero.** In a `MulArchimedean` `LinearOrderedCommGroupWithZero Γ` admitting a largest element
strictly below `1`, if a nonzero `γ : Γ` is a `k`-th power for arbitrarily large `k : ℕ`, then
`γ = 1`. -/
theorem eq_one_of_forall_exists_le_pow_eq {Γ : Type*}
    [LinearOrderedCommGroupWithZero Γ] [MulArchimedean Γ]
    (hu : ∃ u : Γ, u < 1 ∧ ∀ δ < 1, δ ≤ u) {γ : Γ} (hγ : γ ≠ 0)
    (h : ∀ n : ℕ, ∃ k ≥ n, ∃ δ : Γ, δ ^ k = γ) :
    γ = 1 := by
  have hge := one_le_of_forall_exists_le_pow_eq hu hγ h
  have hge_inv : 1 ≤ γ⁻¹ :=
    one_le_of_forall_exists_le_pow_eq hu (inv_ne_zero hγ) fun n ↦ by
      obtain ⟨k, hkn, δ, hδ⟩ := h n
      exact ⟨k, hkn, δ⁻¹, by rw [inv_pow, hδ]⟩
  exact le_antisymm ((one_le_inv₀ (pos_iff_ne_zero.mpr hγ)).mp hge_inv) hge

end TauCeti
