/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Powers and compatibility of the complex roots of unity `exp(2πi / m)`

Mathlib's `Complex.isPrimitiveRoot_exp` says that `exp(2πi / m)` is a primitive `m`-th root of
unity. This file records its `e`-th power `exp(2πi * (e / d))`, compatibility along divisibility
(`exp(2πi / m) ^ (m / n) = exp(2πi / n)` for `n ∣ m` with `m ≠ 0`), and injectivity on natural
numbers strictly less than `h`.

## Main results

* `TauCeti.exp_two_pi_I_div_pow`: `exp(2πi / d) ^ e = exp(2πi * (e / d))`.
* `TauCeti.exp_two_pi_I_div_pow_div`: `exp(2πi / m) ^ (m / n) = exp(2πi / n)` for `n ∣ m`,
  `m ≠ 0`.
* `TauCeti.injOn_exp_two_pi_I_div`: `e ↦ exp(2πi * (e / h))` is injective on `Set.Iio h`.
* `TauCeti.nodup_map_exp_two_pi_I_div`: distinct natural numbers strictly below `h` map to
  distinct complex roots of unity `exp(2πi * (e / h))`.
-/

public section

open Complex Real

namespace TauCeti

/-- The `e`-th power of `exp(2πi / d)` is `exp(2πi * (e / d))`. -/
theorem exp_two_pi_I_div_pow (d : ℂ) (e : ℕ) :
    exp (2 * π * I / d) ^ e = exp (2 * π * I * (e / d)) := by
  rw [← Complex.exp_natCast_mul, mul_div_left_comm]

/-- The complex numbers `exp(2πi / m)` are compatible along the power maps: for `n ∣ m` with
`m ≠ 0`, `exp(2πi / m) ^ (m / n) = exp(2πi / n)`. -/
theorem exp_two_pi_I_div_pow_div {m n : ℕ} (hm : m ≠ 0) (h : n ∣ m) :
    exp (2 * π * I / m) ^ (m / n) = exp (2 * π * I / n) := by
  obtain ⟨k, rfl⟩ := h
  have hn : n ≠ 0 := left_ne_zero_of_mul hm
  have hk : k ≠ 0 := right_ne_zero_of_mul hm
  rw [exp_two_pi_I_div_pow, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hn)]
  congr 1
  push_cast
  field_simp

/-- The map `e ↦ exp(2πi * (e / h))` is injective on `{e : ℕ | e < h}`. -/
theorem injOn_exp_two_pi_I_div (h : ℕ) :
    Set.InjOn (fun e : ℕ => exp (2 * π * I * ((e : ℂ) / (h : ℂ)))) (Set.Iio h) := by
  intro a ha b hb hab
  have hh : h ≠ 0 := by have : a < h := ha; omega
  have hζ := Complex.isPrimitiveRoot_exp h hh
  dsimp only at hab
  rw [← exp_two_pi_I_div_pow, ← exp_two_pi_I_div_pow] at hab
  exact hζ.pow_inj ha hb hab

/-- Distinct natural numbers strictly less than `h` map to distinct complex roots of unity
`exp(2πi * (e / h))`. -/
theorem nodup_map_exp_two_pi_I_div {h : ℕ} {l : List ℕ} (hnd : l.Nodup)
    (hlt : ∀ e ∈ l, e < h) :
    (l.map fun e : ℕ => exp (2 * π * I * ((e : ℂ) / (h : ℂ)))).Nodup :=
  (List.nodup_map_iff_inj_on hnd).mpr fun _ ha _ hb =>
    injOn_exp_two_pi_I_div h (hlt _ ha) (hlt _ hb)

end TauCeti
