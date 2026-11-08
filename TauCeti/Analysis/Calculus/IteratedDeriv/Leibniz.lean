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

* `TauCeti.iteratedDeriv_pow_sub_smul_self`: the identity above.
* `TauCeti.inv_factorial_smul_iteratedDeriv_pow_sub_smul`: the `(p + i)`-th Taylor coefficient of
  `z ↦ (z - a) ^ p • h z` at `a` is the `i`-th Taylor coefficient of `h`.
-/

public section

namespace TauCeti

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {a : 𝕜}

/-- The `n`-th derivative of `z ↦ (z - a) ^ n • h z` at `a` is `n! • h a`: in Leibniz's rule
every other term differentiates `(z - a) ^ n` fewer than `n` times and so vanishes at `a`. -/
theorem iteratedDeriv_pow_sub_smul_self {h : 𝕜 → E} {n : ℕ} (hh : ContDiffAt 𝕜 n h a) :
    iteratedDeriv n (fun z ↦ (z - a) ^ n • h z) a = n.factorial • h a := by
  have hp (i : ℕ) : iteratedDeriv i (fun z : 𝕜 ↦ (z - a) ^ n) a =
      if i = n then (n.factorial : 𝕜) else 0 := by
    rw [iteratedDeriv_comp_sub_const i (· ^ n) a]
    dsimp only
    rw [sub_self, iteratedDeriv_fun_pow_zero]
    split_ifs <;> simp
  have hL := iteratedDerivWithin_smul (Set.mem_univ a) uniqueDiffOn_univ
    (f := fun z : 𝕜 ↦ (z - a) ^ n) (by fun_prop) hh.contDiffWithinAt
  simp only [iteratedDerivWithin_univ] at hL
  have hfun : (fun z ↦ (z - a) ^ n • h z) = (fun z : 𝕜 ↦ (z - a) ^ n) • h := by
    ext z
    simp only [Pi.smul_apply']
  rw [hfun, hL,
    Finset.sum_eq_single_of_mem n (Finset.self_mem_range_succ n) fun i _ hi ↦ by simp [hp, hi]]
  simp [hp, Nat.cast_smul_eq_nsmul]

/-- **Taylor-shift invariance.** Multiplying `h` by `(z - a) ^ p` shifts its Taylor coefficients at
`a` up by `p` without changing them: the `(p + i)`-th Taylor coefficient at `a` of
`z ↦ (z - a) ^ p • h z` is the `i`-th Taylor coefficient of `h`. In Leibniz's rule only the term
that differentiates `(z - a) ^ p` exactly `p` times survives at `a`. -/
theorem inv_factorial_smul_iteratedDeriv_pow_sub_smul [CharZero 𝕜] (p i : ℕ) {h : 𝕜 → E}
    (hh : ContDiffAt 𝕜 (p + i) h a) :
    ((p + i).factorial : 𝕜)⁻¹ • iteratedDeriv (p + i) (fun z ↦ (z - a) ^ p • h z) a =
      (i.factorial : 𝕜)⁻¹ • iteratedDeriv i h a := by
  have hpow (j : ℕ) : iteratedDeriv j (fun z : 𝕜 ↦ (z - a) ^ p) a =
      if j = p then (p.factorial : 𝕜) else 0 := by
    simpa only [sub_self, iteratedDeriv_fun_pow_zero, Nat.cast_ite, Nat.cast_zero] using
      congrFun (iteratedDeriv_comp_sub_const j (fun w : 𝕜 ↦ w ^ p) a) a
  have hleib := iteratedDerivWithin_smul (Set.mem_univ a) uniqueDiffOn_univ (n := p + i)
    (f := fun z : 𝕜 ↦ (z - a) ^ p) (by fun_prop) hh.contDiffWithinAt
  simp only [iteratedDerivWithin_univ] at hleib
  have hfun : (fun z ↦ (z - a) ^ p • h z) = (fun z : 𝕜 ↦ (z - a) ^ p) • h := by
    ext z
    simp only [Pi.smul_apply']
  rw [hfun, hleib,
    Finset.sum_eq_single p (fun j _ hj ↦ by rw [hpow, ite_eq_right hj, zero_smul, smul_zero])
      (fun hp ↦ absurd (Finset.mem_range.2 (by omega)) hp),
    hpow, ite_eq_left rfl, Nat.add_sub_cancel_left, ← Nat.cast_smul_eq_nsmul 𝕜, smul_smul,
    smul_smul]
  congr 1
  have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right p i)
  rw [Nat.add_sub_cancel_left] at h
  have hC : ((p + i).choose p : 𝕜) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos (Nat.le_add_right p i)).ne'
  have hP : (p.factorial : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr p.factorial_ne_zero
  rw [← h]
  push_cast
  field_simp

end TauCeti
