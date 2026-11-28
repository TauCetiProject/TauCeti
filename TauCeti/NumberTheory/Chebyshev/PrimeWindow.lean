/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Chebyshev.ResidueClass
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Prime windows from progression estimates

A uniform Siegel–Walfisz estimate for the von Mangoldt sum supplies primes in every reduced
class in windows of any fixed positive logarithmic width, even as the modulus grows like a
power of the logarithm of the left endpoint. Subtract the two endpoint estimates and remove
the higher prime powers using the unrestricted Chebyshev bound.

For the classical progression estimate, see Montgomery–Vaughan,
*Multiplicative Number Theory I*, Corollary 11.19. The transfer below uses only the stated
error bound, with one more logarithmic power of saving than the modulus exponent.
-/

public section

open Filter Finset Real Set
open scoped Topology Chebyshev ArithmeticFunction.vonMangoldt

namespace Chebyshev

/-- The mass of higher prime powers in any class is at most their total mass. -/
theorem psiAP_sub_thetaAP_le (q : ℕ) (a : ZMod q) (x : ℝ) :
    psiAP q a x - thetaAP q a x ≤ ψ x - θ x := by
  classical
  have hprime (s : Finset ℕ) :
      ∑ p ∈ s.filter Nat.Prime, Λ p = ∑ p ∈ s.filter Nat.Prime, Real.log p :=
    sum_congr rfl fun p hp ↦ ArithmeticFunction.vonMangoldt_apply_prime (mem_filter.mp hp).2
  rw [psiAP_def, thetaAP_def, theta_eq_sum_primesLE, Nat.primesLE_eq_filter_Ioc_zero,
    Finset.filter_comm Nat.Prime (fun n : ℕ ↦ (n : ZMod q) = a), ← hprime, ← hprime]
  rw [← sum_filter_add_sum_filter_not _ Nat.Prime (fun n ↦ Λ n),
    Chebyshev.psi, ← sum_filter_add_sum_filter_not (Ioc 0 ⌊x⌋₊) Nat.Prime (fun n ↦ Λ n)]
  simp only [add_sub_cancel_left]
  exact sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ (filter_subset _ _))
    (fun _ _ _ ↦ ArithmeticFunction.vonMangoldt_nonneg)

/-- A strict increase of the Chebyshev prime sum detects a prime in the half-open interval. -/
theorem exists_prime_of_thetaAP_lt {q : ℕ} {a : ZMod q} {x y : ℝ}
    (h : thetaAP q a x < thetaAP q a y) :
    ∃ p : ℕ, p.Prime ∧ (p : ZMod q) = a ∧ (p : ℝ) ∈ Ioc x y := by
  classical
  by_contra! hnone
  apply h.not_ge
  rw [thetaAP_def, thetaAP_def]
  refine sum_le_sum_of_subset_of_nonneg (fun p hp ↦ ?_) fun p _ _ ↦ log_natCast_nonneg p
  obtain ⟨⟨hpy, hpP⟩, hpa⟩ := mem_filter.mp hp |>.imp_left Nat.mem_primesLE.mp
  have hy := (Nat.le_floor_iff' hpP.ne_zero).mp hpy
  have hx := le_of_not_gt fun hpx ↦ hnone p hpP hpa ⟨hpx, hy⟩
  exact mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨(Nat.le_floor_iff' hpP.ne_zero).mpr hx, hpP⟩, hpa⟩

/-- Higher prime powers cost at most `exp u / u^k` in each progression up to `exp u`, for all
large `u`. The threshold depends only on `k`, not on the progression. -/
theorem eventually_psiAP_sub_thetaAP_exp_le (k : ℕ) :
    ∀ᶠ u : ℝ in atTop, ∀ (q : ℕ) (a : ZMod q),
      psiAP q a (exp u) - thetaAP q a (exp u) ≤ exp u / u ^ k := by
  have ho := (isBigO_psi_sub_theta_sqrt.comp_tendsto tendsto_exp_atTop).mul_isLittleO
    (isLittleO_pow_exp_pos_mul_atTop k (by norm_num : 0 < (1 : ℝ) / 2))
  filter_upwards [eventually_gt_atTop (0 : ℝ), ho.bound zero_lt_one] with u hu h
  simp only [Function.comp_apply, Pi.sub_apply, one_mul] at h
  rw [← exp_half, one_div_mul_eq_div, ← exp_add, add_halves, norm_of_nonneg (exp_pos _).le] at h
  intro q a
  exact (psiAP_sub_thetaAP_le q a (exp u)).trans
    ((le_div_iff₀ (pow_pos hu _)).mpr ((le_abs_self _).trans h))

/-- A uniform progression estimate for `ψ` with a saving of `A + 1` logarithmic powers implies
prime existence in every window `(U, U + W]` of logarithms, for all `W` at least a fixed
positive width. The threshold for `U` is independent of `q ≤ U^A` and of its reduced class. -/
theorem eventually_exists_prime_log_mem_Ioc_of_psiAP_error (A : ℕ) {w C : ℝ} (hw : 0 < w)
    (hψ : ∀ᶠ x : ℝ in atTop, ∀ (q : ℕ) (a : (ZMod q)ˣ), q ≠ 0 → (q : ℝ) ≤ log x ^ A →
      |psiAP q a x - x / q.totient| ≤ C * x / log x ^ (A + 1)) :
    ∀ᶠ U : ℝ in atTop, ∀ (q : ℕ) (a : (ZMod q)ˣ), q ≠ 0 → (q : ℝ) ≤ U ^ A →
      ∀ W ≥ w, ∃ p : ℕ, p.Prime ∧ (p : ZMod q) = a ∧ log (p : ℝ) ∈ Ioc U (U + W) := by
  have hgap : 0 < 1 - exp (-w) := sub_pos.mpr (by simpa using exp_lt_exp.mpr (neg_neg_of_pos hw))
  have hshift : Tendsto (fun U : ℝ ↦ U + w) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_id
  have hleft := tendsto_exp_atTop.eventually hψ
  have hright := (tendsto_exp_atTop.comp hshift).eventually hψ
  have hpp := hshift.eventually (eventually_psiAP_sub_thetaAP_exp_le (A + 1))
  filter_upwards [hleft, hright, hpp, eventually_gt_atTop (0 : ℝ),
    eventually_gt_atTop ((2 * |C| + 1) / (1 - exp (-w)))] with U hL hR hP hU hlarge
  intro q a hq hsmall W hW
  simp only [Function.comp_apply, log_exp] at hL hR
  have hpow : U ^ (A + 1) ≤ (U + w) ^ (A + 1) := by gcongr; linarith
  have hsmall' : (q : ℝ) ≤ (U + w) ^ A := hsmall.trans (by gcongr; linarith)
  have hx : exp U ≤ exp (U + w) := exp_le_exp.mpr (by linarith)
  have hC : C * exp U ≤ |C| * exp (U + w) :=
    mul_le_mul (le_abs_self _) hx (exp_pos _).le (abs_nonneg _)
  have h₁ := (hL q a hq hsmall).trans (div_le_div_of_nonneg_right hC (by positivity))
  have h₂ := (hR q a hq hsmall').trans ((div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_abs_self C) (exp_pos _).le) (by positivity)).trans
    (div_le_div_of_nonneg_left (by positivity) (by positivity) hpow))
  have h₃ := (hP q a).trans (div_le_div_of_nonneg_left (exp_pos _).le (by positivity) hpow)
  have htot : 0 < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hq)
  have hmain : exp (U + w) * (1 - exp (-w)) / U ^ A ≤
      exp (U + w) / q.totient - exp U / q.totient := by
    rw [← sub_div, mul_sub, mul_one, ← exp_add, add_neg_cancel_right]
    exact div_le_div_of_nonneg_left (sub_nonneg.mpr hx) htot
      ((by exact_mod_cast Nat.totient_le q : (q.totient : ℝ) ≤ q).trans hsmall)
  have hpay : (2 * |C| + 1) * exp (U + w) / U ^ (A + 1) <
      exp (U + w) * (1 - exp (-w)) / U ^ A := by
    calc
      _ = ((2 * |C| + 1) / U) * (exp (U + w) / U ^ A) := by rw [pow_succ]; ring
      _ < (1 - exp (-w)) * (exp (U + w) / U ^ A) :=
        mul_lt_mul_of_pos_right ((div_lt_iff₀ hU).mpr (by linarith [(div_lt_iff₀ hgap).mp hlarge]))
          (by positivity)
      _ = _ := by ring
  have herr : (|C| * exp (U + w) / U ^ (A + 1)) * 2 + exp (U + w) / U ^ (A + 1) =
      (2 * |C| + 1) * exp (U + w) / U ^ (A + 1) := by ring
  have hθ : thetaAP q a (exp U) < thetaAP q a (exp (U + w)) := by
    linarith only [h₁, h₂, h₃, hmain, hpay, herr,
      thetaAP_le_psiAP q a (exp U),
      le_abs_self (psiAP q a (exp U) - exp U / q.totient),
      neg_abs_le (psiAP q a (exp (U + w)) - exp (U + w) / q.totient)]
  obtain ⟨p, hp, hpa, hpL, hpR⟩ := exists_prime_of_thetaAP_lt hθ
  have hppos : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  exact ⟨p, hp, hpa, (lt_log_iff_exp_lt hppos).mpr hpL,
    (log_le_iff_le_exp hppos).mpr (hpR.trans (exp_le_exp.mpr (by linarith)))⟩

end Chebyshev
