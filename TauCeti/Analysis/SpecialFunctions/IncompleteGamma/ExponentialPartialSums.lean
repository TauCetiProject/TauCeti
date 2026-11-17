/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Exp.PartialSums.Basic
public import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Basic

/-!
# Uniform asymptotics of the regularized incomplete gamma function below the transition

Through the Erlang identity `P(n + 1, z) = 1 - e^{-z} ∑_{k ≤ n} z^k / k!`
(`TauCeti.regularizedGamma_natCast`), Buckholtz's uniform expansion of the scaled exponential
partial sums (`TauCeti.isBigO_sum_range_succ_div_factorial_sub`, DLMF 8.11.18–8.11.19) yields the
uniform large-parameter asymptotic expansion of `TauCeti.regularizedGamma (n + 1) (n * x)` across
`x ∈ [0, 1 - δ]` (`δ > 0`) to arbitrary order `m`.

## Main results

* `TauCeti.isBigO_regularizedGamma_natCast_add_one_mul_sub`: uniform `m`-term asymptotic expansion
  of `TauCeti.regularizedGamma (n + 1) (n * x)` on `atTop ×ˢ 𝓟 (Icc 0 (1 - δ))`.
* `TauCeti.regularizedGamma_natCast_add_one_mul_isEquivalent`: leading asymptotic equivalence
  `P(n + 1, n x) ~ e^{-n x} ((n x)^n / n!) (x / (1 - x))` as `n → ∞` for `x ∈ [0, 1)`.

## References

* *NIST Digital Library of Mathematical Functions*, [§8.11(v)](https://dlmf.nist.gov/8.11#v),
  Eqs. 8.11.18 and 8.11.19.
* J. D. Buckholtz, *Concerning an approximation of Copson*, Proc. Amer. Math. Soc. **14** (1963),
  564–568.
* N. M. Temme, *Special Functions: An Introduction to the Classical Functions of Mathematical
  Physics*, Wiley, 1996, §11.2.
-/

public section

noncomputable section

open Asymptotics Filter Set
open scoped Nat

namespace TauCeti

private theorem regularizedGamma_add_one_eq_exp_neg_mul_sub (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    regularizedGamma ((n : ℝ) + 1) x =
      Real.exp (-x) * (Real.exp x - ∑ k ∈ Finset.range (n + 1), x ^ k / (k ! : ℝ)) := by
  rw [← Nat.cast_add_one, regularizedGamma_natCast (Nat.succ_ne_zero n) hx]
  have hexp : Real.exp (-x) * Real.exp x = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  linear_combination -hexp

/-- Uniform asymptotic expansion of `TauCeti.regularizedGamma (n + 1) (n * x)` across `[0, 1 - δ]`
(`δ > 0`) to arbitrary order `m`. -/
theorem isBigO_regularizedGamma_natCast_add_one_mul_sub {δ : ℝ} (hδ : 0 < δ) (m : ℕ) :
    (fun q : ℕ × ℝ =>
      regularizedGamma ((q.1 : ℝ) + 1) ((q.1 : ℝ) * q.2) -
        Real.exp (-((q.1 : ℝ) * q.2)) * (((q.1 : ℝ) * q.2) ^ q.1 / (q.1 ! : ℝ)) *
          ∑ k ∈ Finset.range m, expPartialSumCoeff k q.2 / (q.1 : ℝ) ^ k)
      =O[atTop ×ˢ 𝓟 (Icc 0 (1 - δ))]
        fun q : ℕ × ℝ =>
          Real.exp (-((q.1 : ℝ) * q.2)) * (((q.1 : ℝ) * q.2) ^ q.1 / (q.1 ! : ℝ)) /
            (q.1 : ℝ) ^ m := by
  have hmono : (atTop : Filter ℕ) ×ˢ 𝓟 (Icc (0 : ℝ) (1 - δ)) ≤
      (atTop : Filter ℕ) ×ˢ 𝓟 (Iic (1 - δ)) :=
    prod_mono_right _ (principal_mono.mpr Icc_subset_Iic_self)
  have hbase := ((isBigO_sum_range_succ_div_factorial_sub hδ m).mono hmono).neg_left
  refine ((isBigO_refl (fun q : ℕ × ℝ => Real.exp (-((q.1 : ℝ) * q.2))) _).mul hbase).congr'
    ?_ (Eventually.of_forall fun q => by ring)
  filter_upwards [prod_mem_prod Filter.univ_mem (mem_principal_self (Icc 0 (1 - δ)))] with q hq
  rw [regularizedGamma_add_one_eq_exp_neg_mul_sub q.1 (mul_nonneg (Nat.cast_nonneg q.1) hq.2.1)]
  ring

/-- Leading asymptotic equivalence for `TauCeti.regularizedGamma (n + 1) (n * x)` as `n → ∞` for
every `x ∈ [0, 1)` (at `x = 0`, both sides vanish). -/
theorem regularizedGamma_natCast_add_one_mul_isEquivalent {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    (fun n : ℕ => regularizedGamma ((n : ℝ) + 1) ((n : ℝ) * x))
      ~[atTop]
        fun n : ℕ =>
          Real.exp (-((n : ℝ) * x)) * (((n : ℝ) * x) ^ n / (n ! : ℝ)) * (x / (1 - x)) := by
  have heq : (fun n : ℕ => Real.exp (-((n : ℝ) * x)) *
      (Real.exp ((n : ℝ) * x) - ∑ k ∈ Finset.range (n + 1), ((n : ℝ) * x) ^ k / (k ! : ℝ)))
      ~[atTop]
      fun n : ℕ => Real.exp (-((n : ℝ) * x)) *
        ((((n : ℝ) * x) ^ n / (n ! : ℝ)) * (x / (1 - x))) :=
    (IsEquivalent.refl (u := fun n : ℕ => Real.exp (-((n : ℝ) * x)))).mul
      (exp_mul_sub_sum_range_succ_isEquivalent hx1)
  refine (heq.congr_left ?_).congr_right (Eventually.of_forall fun n => by ring)
  filter_upwards with n
  exact (regularizedGamma_add_one_eq_exp_neg_mul_sub n (mul_nonneg (Nat.cast_nonneg n) hx0)).symm

end TauCeti

end
