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

## Main results

* `TauCeti.iteratedDeriv_pow_sub_smul_self`: the identity above.
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

end TauCeti
