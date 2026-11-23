/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Compatibility and characterization of the complex roots of unity `exp(2πi / m)`

Mathlib's `Complex.isPrimitiveRoot_exp` says that `exp(2πi / m)` is a primitive `m`-th root of
unity. This file records:
* compatibility along the power maps (`TauCeti.exp_two_pi_I_div_pow_div`): for `n ∣ m` with
  `m ≠ 0`, `exp(2πi / m) ^ (m / n) = exp(2πi / n)`;
* characterization of a duplicate-free multiset of complex numbers whose elements are
  `exp(2πi e / h)` over a duplicate-free list `es` of residues `< h`
  (`TauCeti.multiset_eq_map_exp_of_mem_iff_of_nodup`).
-/

public section

open Complex Real

namespace TauCeti

/-- The complex numbers `exp(2πi / m)` are compatible along the power maps: for `n ∣ m` with
`m ≠ 0`, `exp(2πi / m) ^ (m / n) = exp(2πi / n)`. -/
theorem exp_two_pi_I_div_pow_div {m n : ℕ} (hm : m ≠ 0) (h : n ∣ m) :
    exp (2 * π * I / m) ^ (m / n) = exp (2 * π * I / n) := by
  obtain ⟨k, rfl⟩ := h
  have hn : n ≠ 0 := left_ne_zero_of_mul hm
  have hk : k ≠ 0 := right_ne_zero_of_mul hm
  rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hn), ← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

/-- A duplicate-free multiset of complex numbers whose elements are exactly `exp (2πi e / h)` as
`e` runs over a duplicate-free list `es` of residues `< h` equals `(es : Multiset ℕ).map _`. -/
theorem multiset_eq_map_exp_of_mem_iff_of_nodup {s : Multiset ℂ} {es : List ℕ} {h : ℕ}
    (hh : 0 < h) (hes_nd : es.Nodup) (hes_lt : ∀ e ∈ es, e < h) (hs_nd : s.Nodup)
    (hmem : ∀ ζ : ℂ, ζ ∈ s ↔
      ∃ e ∈ es, Complex.exp (2 * Real.pi * Complex.I * (e / (h : ℕ))) = ζ) :
    s = (es : Multiset ℕ).map fun e : ℕ ↦
      Complex.exp (2 * Real.pi * Complex.I * (e / (h : ℕ))) := by
  let ζ := Complex.exp (2 * Real.pi * Complex.I / h)
  have hζ : IsPrimitiveRoot ζ h := Complex.isPrimitiveRoot_exp h hh.ne'
  have hpow : ∀ e : ℕ, Complex.exp (2 * Real.pi * Complex.I * (e / (h : ℕ))) = ζ ^ e := fun e ↦ by
    dsimp [ζ]; rw [← Complex.exp_nat_mul]; congr 1; ring
  refine (Multiset.Nodup.ext hs_nd (Multiset.Nodup.map_on (fun x hx y hy hxy ↦ ?_)
    (Multiset.coe_nodup.mpr hes_nd))).mpr fun z ↦ ?_
  · rw [hpow, hpow] at hxy
    exact hζ.pow_inj (hes_lt x hx) (hes_lt y hy) hxy
  · simp [hmem]

end TauCeti
