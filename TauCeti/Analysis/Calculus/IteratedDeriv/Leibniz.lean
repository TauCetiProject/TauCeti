/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Leibniz's rule at a zero of a power

The `n`-th derivative of `z ↦ (z - a) ^ n • h z` at `a` is `n! • h a`: in Leibniz's rule every
other term differentiates `(z - a) ^ n` fewer than `n` times and so vanishes at `a`. If an
analytic function `f` factors as `f z = (z - a) ^ n • h z` (for instance through
`AnalyticOnNhd.exists_eq_prod_pow_smul`), this recovers its first possibly nonzero derivative at
`a` from the value of the quotient `h`.

More generally, multiplying by `(z - a) ^ p` shifts the Taylor coefficients at `a` up by `p`
without changing them.

## Main results

* `TauCeti.iteratedDeriv_pow_sub_smul`: the `n`-th derivative of `z ↦ (z - a) ^ p • h z` at `a`
  equals `n.descFactorial p • iteratedDeriv (n - p) h a`, unconditionally for all `n p : ℕ`
  (vanishing automatically when `n < p`).
* `TauCeti.iteratedDeriv_pow_sub_smul_iteratedDeriv`: the `k`-th derivative of
  `z ↦ (z - a) ^ p • iteratedDeriv q h z` at `a` equals
  `k.descFactorial p • iteratedDeriv (k + q - p) h a`, unconditionally for all `k p q : ℕ`.
* `TauCeti.iteratedDeriv_pow_sub_smul_self`: the `n = p` specialization.
* `TauCeti.inv_factorial_smul_iteratedDeriv_pow_sub_smul`: the `(p + i)`-th Taylor coefficient of
  `z ↦ (z - a) ^ p • h z` at `a` is the `i`-th Taylor coefficient of `h`.
-/

public section

namespace TauCeti

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {a : 𝕜}

/-- The `n`-th derivative of `z ↦ (z - a) ^ p • h z` at `a` is
`n.descFactorial p • iteratedDeriv (n - p) h a`: in Leibniz's rule every term other than `j = p`
differentiates `(z - a) ^ p` the wrong number of times and vanishes at `a`. When `n < p`,
`n.descFactorial p = 0`, so both sides vanish with no `p ≤ n` hypothesis. -/
theorem iteratedDeriv_pow_sub_smul (n p : ℕ) {h : 𝕜 → E} (hh : ContDiffAt 𝕜 n h a) :
    iteratedDeriv n (fun z ↦ (z - a) ^ p • h z) a =
      n.descFactorial p • iteratedDeriv (n - p) h a := by
  have hpow (j : ℕ) : iteratedDeriv j (fun z : 𝕜 ↦ (z - a) ^ p) a =
      if j = p then (p.factorial : 𝕜) else 0 := by
    simpa only [sub_self, iteratedDeriv_fun_pow_zero, Nat.cast_ite, Nat.cast_zero] using
      congrFun (iteratedDeriv_comp_sub_const j (fun w : 𝕜 ↦ w ^ p) a) a
  have hL := iteratedDerivWithin_smul (Set.mem_univ a) uniqueDiffOn_univ (n := n)
    (f := fun z : 𝕜 ↦ (z - a) ^ p) (by fun_prop) hh.contDiffWithinAt
  simp only [iteratedDerivWithin_univ] at hL
  have hfun : (fun z ↦ (z - a) ^ p • h z) = (fun z : 𝕜 ↦ (z - a) ^ p) • h := by
    ext z
    simp only [Pi.smul_apply']
  rw [hfun, hL]
  rcases lt_or_ge n p with hnp | hpn
  · rw [Nat.descFactorial_of_lt hnp, zero_smul]
    refine Finset.sum_eq_zero fun j hj ↦ ?_
    have hjp : j ≠ p := by
      have := Finset.mem_range.mp hj
      omega
    simp [hpow j, hjp]
  · rw [Finset.sum_eq_single_of_mem p (Finset.mem_range.mpr (by omega))
      fun j _ hj ↦ by simp [hpow j, hj]]
    simp only [hpow, ↓reduceIte, Nat.cast_smul_eq_nsmul, smul_smul,
      Nat.descFactorial_eq_factorial_mul_choose, mul_comm (n.choose p)]

/-- The `k`-th derivative of `z ↦ (z - a) ^ p • iteratedDeriv q h z` at `a` equals
`k.descFactorial p • iteratedDeriv (k + q - p) h a`, unconditionally for all `k p q : ℕ`.
When `k < p`, `k.descFactorial p = 0`, so both sides vanish automatically. -/
theorem iteratedDeriv_pow_sub_smul_iteratedDeriv (k p q : ℕ) {h : 𝕜 → E}
    (hh : ContDiffAt 𝕜 k (iteratedDeriv q h) a) :
    iteratedDeriv k (fun z ↦ (z - a) ^ p • iteratedDeriv q h z) a =
      k.descFactorial p • iteratedDeriv (k + q - p) h a := by
  rw [iteratedDeriv_pow_sub_smul k p hh]
  rcases lt_or_ge k p with hkp | hpk
  · simp [Nat.descFactorial_of_lt hkp]
  · congr 1
    simp only [iteratedDeriv_eq_iterate, ← Function.iterate_add_apply]
    rw [Nat.sub_add_comm hpk]

/-- The `n`-th derivative of `z ↦ (z - a) ^ n • h z` at `a` is `n! • h a`: in Leibniz's rule
every other term differentiates `(z - a) ^ n` fewer than `n` times and so vanishes at `a`. -/
theorem iteratedDeriv_pow_sub_smul_self {h : 𝕜 → E} {n : ℕ} (hh : ContDiffAt 𝕜 n h a) :
    iteratedDeriv n (fun z ↦ (z - a) ^ n • h z) a = n.factorial • h a := by
  simpa [Nat.descFactorial_self] using iteratedDeriv_pow_sub_smul n n hh

/-- **Taylor-shift invariance.** Multiplying `h` by `(z - a) ^ p` shifts its Taylor coefficients at
`a` up by `p` without changing them: the `(p + i)`-th Taylor coefficient at `a` of
`z ↦ (z - a) ^ p • h z` is the `i`-th Taylor coefficient of `h`. In Leibniz's rule only the term
that differentiates `(z - a) ^ p` exactly `p` times survives at `a`. -/
theorem inv_factorial_smul_iteratedDeriv_pow_sub_smul [CharZero 𝕜] (p i : ℕ) {h : 𝕜 → E}
    (hh : ContDiffAt 𝕜 (p + i) h a) :
    ((p + i).factorial : 𝕜)⁻¹ • iteratedDeriv (p + i) (fun z ↦ (z - a) ^ p • h z) a =
      (i.factorial : 𝕜)⁻¹ • iteratedDeriv i h a := by
  rw [iteratedDeriv_pow_sub_smul (p + i) p hh, Nat.add_sub_cancel_left,
    ← Nat.cast_smul_eq_nsmul 𝕜, smul_smul]
  congr 1
  have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right p i)
  rw [Nat.add_sub_cancel_left, mul_comm ((p + i).choose p),
    ← Nat.descFactorial_eq_factorial_mul_choose] at h
  have hd : ((p + i).descFactorial p : 𝕜) ≠ 0 := by
    rw [Nat.descFactorial_eq_factorial_mul_choose]
    exact Nat.cast_ne_zero.mpr (Nat.mul_ne_zero p.factorial_ne_zero
      (Nat.choose_pos (Nat.le_add_right p i)).ne')
  rw [← h]
  push_cast
  field_simp

end TauCeti
