/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Exp.PartialSums.Coeff
public import TauCeti.Analysis.SpecialFunctions.Exp.Taylor

import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Uniform asymptotics of scaled exponential partial sums

For integer order `n` and real argument `x ≤ 1 - δ` (`δ > 0`), the partial sums
`e_n(n x) = ∑_{k ≤ n} (n x)^k / k!` of the exponential series satisfy Buckholtz's uniform
asymptotic expansion (DLMF 8.11.18–8.11.19)
`∑_{k ≤ n} (n x)^k / k! = e^{n x} - ((n x)^n / n!) (∑_{k < m} d_k(x) / n^k + O(n^{-m}))`
uniformly for `x ∈ (-∞, 1 - δ]`, where `d_k` is `TauCeti.expPartialSumCoeff` from
`TauCeti.Analysis.SpecialFunctions.Exp.PartialSums.Coeff`. See
`TauCeti.Analysis.SpecialFunctions.IncompleteGamma.ExponentialPartialSums` for the transfer to the
regularized incomplete gamma function via the Erlang identity.

The expansion is proved without splitting across the Szegő curve `|x e^{1 - x}| = 1`: starting
from the exact Taylor integral remainder (`Complex.exp_sub_sum_range_succ_eq_integral`), setting
`z = n w` (`Re w < 1`) expresses the normalized remainder after `m` integrations by parts against
`-∂_s ((1 - s)^n e^{n w s}) = n (1 - w (1 - s)) (1 - s)^{n - 1} e^{n w s}` as an integral of
`d_m(w (1 - s))` against a kernel of unit integral. For real `x < 1` this kernel is a probability
density on `[0, 1]`, yielding both an explicit uniform remainder bound on `(-∞, 1 - δ]` (and on
complex wedges `{w : ℂ | Re w ≤ 1 - δ ∧ |Im w| ≤ M * (1 - Re w)}`) and enveloping bounds by the
first neglected term on `[0, 1)`.

## Main results

* `TauCeti.integral_mul_one_sub_pow_mul_cexp_eq_sum_add_integral`,
  `TauCeti.cexp_mul_sub_sum_range_succ_eq_sum_add_integral`,
  `TauCeti.integral_mul_one_sub_pow_mul_exp_eq_sum_add_integral`,
  `TauCeti.exp_mul_sub_sum_range_succ_eq_sum_add_integral`: exact `m`-fold integration-by-parts
  remainder identities on `Re w < 1` and `x < 1`.
* `TauCeti.abs_sum_range_succ_div_factorial_sub_le`,
  `TauCeti.isBigO_sum_range_succ_div_factorial_sub`,
  `TauCeti.isBigO_div_exp_sub_sum_range_succ_sub`,
  `TauCeti.isBigO_sum_range_succ_div_factorial_sub_of_recurrence`: explicit uniform remainder bound
  and DLMF 8.11.18 uniformly on `(-∞, 1 - δ]` (`atTop ×ˢ 𝓟 (Iic (1 - δ))`), together with
  `TauCeti.norm_sum_range_succ_div_factorial_sub_le` and
  `TauCeti.isBigO_sum_range_succ_div_factorial_sub_complex` on complex wedges.
* `TauCeti.neg_one_pow_mul_integral_sub_sum_nonneg`, `TauCeti.neg_one_pow_mul_integral_sub_sum_le`,
  `TauCeti.tendsto_div_exp_sub_sum_range_succ_atTop`,
  `TauCeti.exp_mul_sub_sum_range_succ_isEquivalent`: enveloping bounds on `[0, 1)`, leading limit,
  and asymptotic equivalence for `x < 1`.

## References

* *NIST Digital Library of Mathematical Functions*, [§8.11(v)](https://dlmf.nist.gov/8.11#v),
  Eqs. 8.11.18 and 8.11.19.
* J. D. Buckholtz, *Concerning an approximation of Copson*, Proc. Amer. Math. Soc. **14** (1963),
  564–568.
* F. G. Tricomi, *Asymptotische Eigenschaften der unvollständigen Gammafunktion*, Math. Z. **53**
  (1950), 136–148.
* N. M. Temme, *Special Functions: An Introduction to the Classical Functions of Mathematical
  Physics*, Wiley, 1996, §11.2.
-/

public section

noncomputable section

open Asymptotics Filter MeasureTheory Polynomial Set
open scoped Nat Topology

/-! ### Exact `m`-fold integration-by-parts identities -/

namespace TauCeti

private def expKernel (n : ℕ) (w : ℂ) (s : ℝ) : ℂ :=
  (n : ℂ) * (1 - w * (1 - (s : ℂ))) * (1 - (s : ℂ)) ^ (n - 1) * Complex.exp ((n : ℂ) * w * s)

private theorem one_sub_mul_one_sub_re_pos {w : ℂ} (hw : w.re < 1) {s : ℝ} (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) :
    0 < (1 - w * (1 - (s : ℂ))).re := by
  have hre : (1 - w * (1 - (s : ℂ))).re = 1 - w.re * (1 - s) := by simp
  rw [hre]
  rcases le_or_gt w.re 0 with _ | _ <;> nlinarith

private theorem mul_one_sub_ne_one {w : ℂ} (hw : w.re < 1) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    w * (1 - (s : ℂ)) ≠ 1 := by
  intro h
  have hpos := one_sub_mul_one_sub_re_pos hw hs0 hs1
  rw [h, sub_self, Complex.zero_re] at hpos
  exact lt_irrefl 0 hpos

private theorem hasDerivAt_neg_one_sub_pow_mul_cexp {n : ℕ} (hn : n ≠ 0) (w : ℂ) (s : ℝ) :
    HasDerivAt (fun t : ℝ => -((1 - (t : ℂ)) ^ n * Complex.exp ((n : ℂ) * w * t)))
      (expKernel n w s) s := by
  rcases Nat.exists_eq_add_one.mpr (Nat.pos_of_ne_zero hn) with ⟨m, rfl⟩
  have h1a : HasDerivAt (fun t : ℝ => 1 - (t : ℂ)) (-1) s := by
    simpa using (hasDerivAt_id s).ofReal_comp.const_sub 1
  have h1 := h1a.fun_pow (m + 1)
  have h2 : HasDerivAt (fun t : ℝ => Complex.exp (((m + 1 : ℕ) : ℂ) * w * t))
      (Complex.exp (((m + 1 : ℕ) : ℂ) * w * s) * (((m + 1 : ℕ) : ℂ) * w)) s := by
    have hlin : HasDerivAt (fun t : ℝ => ((m + 1 : ℕ) : ℂ) * w * (t : ℂ))
        (((m + 1 : ℕ) : ℂ) * w) s := by
      simpa using (hasDerivAt_id s).ofReal_comp.const_mul (((m + 1 : ℕ) : ℂ) * w)
    exact hlin.cexp
  refine (h1.mul h2).neg.congr_deriv ?_
  dsimp only [expKernel]
  simp only [Nat.add_sub_cancel, pow_succ]
  push_cast
  ring

private theorem continuous_expKernel (n : ℕ) (w : ℂ) : Continuous (expKernel n w) := by
  unfold expKernel
  fun_prop

private theorem integral_expKernel {n : ℕ} (hn : n ≠ 0) (w : ℂ) :
    ∫ s in (0 : ℝ)..1, expKernel n w s = 1 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hasDerivAt_neg_one_sub_pow_mul_cexp hn w s)
    (continuous_expKernel n w).continuousOn.intervalIntegrable]
  simp [zero_pow hn]

private theorem integral_expPartialSumCoeff_mul_expKernel_zero {n : ℕ} (hn : n ≠ 0) {w : ℂ}
    (hw : w.re < 1) :
    ∫ s in (0 : ℝ)..1, expPartialSumCoeff 0 (w * (1 - (s : ℂ))) * expKernel n w s =
      ∫ s in (0 : ℝ)..1, (n : ℂ) * w * (1 - (s : ℂ)) ^ n * Complex.exp ((n : ℂ) * w * s) := by
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [Set.uIcc_of_le zero_le_one] at hs
  have hne : 1 - w * (1 - (s : ℂ)) ≠ 0 :=
    sub_ne_zero.mpr (mul_one_sub_ne_one hw hs.1 hs.2).symm
  rcases Nat.exists_eq_add_one.mpr (Nat.pos_of_ne_zero hn) with ⟨m, rfl⟩
  rw [expPartialSumCoeff_zero]
  dsimp only [expKernel]
  simp only [Nat.add_sub_cancel, pow_succ]
  push_cast
  field_simp [hne]

private theorem continuousOn_deriv_expPartialSumCoeff_mul_one_sub {w : ℂ} (hw : w.re < 1)
    (k : ℕ) :
    ContinuousOn (fun s : ℝ =>
      ((-1 : ℂ) ^ k * aeval (w * (1 - (s : ℂ))) (expPartialSumPoly (k + 1)) /
        (1 - w * (1 - (s : ℂ))) ^ (2 * k + 2)) * (-w)) (uIcc 0 1) := by
  rw [Set.uIcc_of_le zero_le_one]
  have hpoly : Continuous fun s : ℝ =>
      (-1 : ℂ) ^ k * aeval (w * (1 - (s : ℂ))) (expPartialSumPoly (k + 1)) := by
    have : Continuous fun z : ℂ => aeval z (expPartialSumPoly (k + 1)) := by
      simp_rw [aeval_eq_sum_range, zsmul_eq_mul]; fun_prop
    exact continuous_const.mul (this.comp (continuous_const.mul
      (continuous_const.sub Complex.continuous_ofReal)))
  refine (hpoly.continuousOn.div ?_ fun s (hs : s ∈ Icc (0 : ℝ) 1) =>
    pow_ne_zero _ (sub_ne_zero.mpr (mul_one_sub_ne_one hw hs.1 hs.2).symm)).mul continuousOn_const
  exact (continuous_const.sub (continuous_const.mul
    (continuous_const.sub Complex.continuous_ofReal))).pow (2 * k + 2) |>.continuousOn

private theorem integral_deriv_expPartialSumCoeff_mul_neg_pow_cexp {n : ℕ} (hn : n ≠ 0)
    {w : ℂ} (hw : w.re < 1) (k : ℕ) :
    ∫ s in (0 : ℝ)..1,
      (((-1 : ℂ) ^ k * aeval (w * (1 - (s : ℂ))) (expPartialSumPoly (k + 1)) /
          (1 - w * (1 - (s : ℂ))) ^ (2 * k + 2)) * (-w)) *
        -((1 - (s : ℂ)) ^ n * Complex.exp ((n : ℂ) * w * s)) =
      -((n : ℂ))⁻¹ * ∫ s in (0 : ℝ)..1,
        expPartialSumCoeff (k + 1) (w * (1 - (s : ℂ))) * expKernel n w s := by
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [Set.uIcc_of_le zero_le_one] at hs
  have h1w : 1 - w * (1 - (s : ℂ)) ≠ 0 :=
    sub_ne_zero.mpr (mul_one_sub_ne_one hw hs.1 hs.2).symm
  rcases Nat.exists_eq_add_one.mpr (Nat.pos_of_ne_zero hn) with ⟨m, rfl⟩
  have hnc : ((m : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  have hexp : 2 * (k + 1) + 1 = (2 * k + 2) + 1 := by omega
  dsimp only [expKernel]
  rw [expPartialSumCoeff_def, hexp]
  simp only [Nat.add_sub_cancel, pow_succ]
  push_cast
  field_simp [h1w, hnc]

private theorem integral_expPartialSumCoeff_mul_expKernel_succ {n : ℕ} (hn : n ≠ 0) {w : ℂ}
    (hw : w.re < 1) (k : ℕ) :
    ∫ s in (0 : ℝ)..1, expPartialSumCoeff k (w * (1 - (s : ℂ))) * expKernel n w s =
      expPartialSumCoeff k w + ((n : ℂ))⁻¹ *
        ∫ s in (0 : ℝ)..1, expPartialSumCoeff (k + 1) (w * (1 - (s : ℂ))) * expKernel n w s := by
  let g : ℝ → ℂ := fun s => w * (1 - (s : ℂ))
  let u : ℝ → ℂ := fun s => expPartialSumCoeff k (g s)
  let u' : ℝ → ℂ := fun s =>
    ((-1) ^ k * aeval (g s) (expPartialSumPoly (k + 1)) / (1 - g s) ^ (2 * k + 2)) * (-w)
  let v : ℝ → ℂ := fun s => -((1 - (s : ℂ)) ^ n * Complex.exp ((n : ℂ) * w * s))
  have hg_ne : ∀ s ∈ Icc (0 : ℝ) 1, g s ≠ 1 := fun s hs => mul_one_sub_ne_one hw hs.1 hs.2
  have hu : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt u (u' s) s := fun s hs => by
    have hg : HasDerivAt g (-w) s := by
      simpa [g] using ((hasDerivAt_id s).ofReal_comp.const_sub 1).const_mul w
    exact (hasDerivAt_expPartialSumCoeff k (hg_ne s hs)).comp s hg
  have hv : ∀ s, HasDerivAt v (expKernel n w s) s := hasDerivAt_neg_one_sub_pow_mul_cexp hn w
  have hu'_cont : ContinuousOn u' (uIcc 0 1) :=
    continuousOn_deriv_expPartialSumCoeff_mul_one_sub hw k
  have hu_cont : ContinuousOn u (uIcc 0 1) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact fun s hs => (hu s hs).continuousAt.continuousWithinAt
  have hv_cont : ContinuousOn v (uIcc 0 1) := fun s _ => (hv s).continuousAt.continuousWithinAt
  have hint1 : IntervalIntegrable (fun s => u' s * v s) volume 0 1 :=
    (hu'_cont.mul hv_cont).intervalIntegrable
  have hint2 : IntervalIntegrable (fun s => u s * expKernel n w s) volume 0 1 :=
    (hu_cont.mul (continuous_expKernel n w).continuousOn).intervalIntegrable
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := 1)
    (f := fun s => u s * v s) (f' := fun s => u' s * v s + u s * expKernel n w s)
    (fun s hs => by
      rw [Set.uIcc_of_le zero_le_one] at hs
      exact (hu s hs).mul (hv s))
    (hint1.add hint2)
  rw [intervalIntegral.integral_add hint1 hint2] at hftc
  have hbnd : u 1 * v 1 - u 0 * v 0 = expPartialSumCoeff k w := by
    dsimp only [u, v, g]; simp [zero_pow hn]
  have hterm : ∫ s in (0 : ℝ)..1, u' s * v s =
      -((n : ℂ))⁻¹ *
        ∫ s in (0 : ℝ)..1, expPartialSumCoeff (k + 1) (g s) * expKernel n w s :=
    integral_deriv_expPartialSumCoeff_mul_neg_pow_cexp hn hw k
  rw [hbnd, hterm] at hftc
  linear_combination hftc

/-- Exact `m`-fold integration-by-parts expansion of `∫₀¹ n w (1 - s)^n e^{n w s} ds` on the open
half-plane `Re w < 1`. -/
theorem integral_mul_one_sub_pow_mul_cexp_eq_sum_add_integral {n : ℕ} (hn : n ≠ 0) {w : ℂ}
    (hw : w.re < 1) (m : ℕ) :
    ∫ s in (0 : ℝ)..1, (n : ℂ) * w * (1 - (s : ℂ)) ^ n * Complex.exp ((n : ℂ) * w * s) =
      ∑ k ∈ Finset.range m, expPartialSumCoeff k w / (n : ℂ) ^ k +
        ((n : ℂ) ^ m)⁻¹ * ∫ s in (0 : ℝ)..1, expPartialSumCoeff m (w * (1 - (s : ℂ))) *
          ((n : ℂ) * (1 - w * (1 - (s : ℂ))) * (1 - (s : ℂ)) ^ (n - 1) *
            Complex.exp ((n : ℂ) * w * s)) := by
  have hind : ∀ l : ℕ,
      ∫ s in (0 : ℝ)..1, expPartialSumCoeff 0 (w * (1 - (s : ℂ))) * expKernel n w s =
        ∑ k ∈ Finset.range l, expPartialSumCoeff k w / (n : ℂ) ^ k +
          ((n : ℂ) ^ l)⁻¹ *
            ∫ s in (0 : ℝ)..1, expPartialSumCoeff l (w * (1 - (s : ℂ))) * expKernel n w s := by
    intro l
    induction l with
    | zero => simp
    | succ l ih =>
      rw [ih, integral_expPartialSumCoeff_mul_expKernel_succ hn hw l, Finset.sum_range_succ,
        pow_succ, mul_inv]
      ring
  rw [← integral_expPartialSumCoeff_mul_expKernel_zero hn hw, hind m]
  simp only [expKernel]

private theorem cexp_mul_sub_sum_range_succ_eq_mul_integral (n : ℕ) (w : ℂ) :
    Complex.exp ((n : ℂ) * w) - ∑ k ∈ Finset.range (n + 1), ((n : ℂ) * w) ^ k / (k ! : ℂ) =
      (((n : ℂ) * w) ^ n / (n ! : ℂ)) *
        ∫ s in (0 : ℝ)..1, (n : ℂ) * w * (1 - (s : ℂ)) ^ n * Complex.exp ((n : ℂ) * w * s) := by
  rw [Complex.exp_sub_sum_range_succ_eq_integral n ((n : ℂ) * w), pow_succ, mul_div_right_comm,
    mul_assoc, ← intervalIntegral.integral_const_mul]
  congr 1
  exact intervalIntegral.integral_congr fun s _ => by ring

/-- Exact `m`-term expansion with integral remainder for `e^{n w} - ∑_{k ≤ n} (n w)^k / k!` on the
open half-plane `Re w < 1`. -/
theorem cexp_mul_sub_sum_range_succ_eq_sum_add_integral {n : ℕ} (hn : n ≠ 0) {w : ℂ}
    (hw : w.re < 1) (m : ℕ) :
    Complex.exp ((n : ℂ) * w) - ∑ k ∈ Finset.range (n + 1), ((n : ℂ) * w) ^ k / (k ! : ℂ) =
      (((n : ℂ) * w) ^ n / (n ! : ℂ)) *
        (∑ k ∈ Finset.range m, expPartialSumCoeff k w / (n : ℂ) ^ k +
          ((n : ℂ) ^ m)⁻¹ * ∫ s in (0 : ℝ)..1, expPartialSumCoeff m (w * (1 - (s : ℂ))) *
            ((n : ℂ) * (1 - w * (1 - (s : ℂ))) * (1 - (s : ℂ)) ^ (n - 1) *
              Complex.exp ((n : ℂ) * w * s))) := by
  rw [cexp_mul_sub_sum_range_succ_eq_mul_integral,
    integral_mul_one_sub_pow_mul_cexp_eq_sum_add_integral hn hw m]

/-! ### Real-to-complex transport, uniform remainder bounds, and DLMF 8.11.18 -/

private theorem ofReal_intervalIntegral_zero_one {f : ℝ → ℝ} {F : ℝ → ℂ}
    (hf : ∀ s, ((f s : ℝ) : ℂ) = F s) :
    ((∫ s in (0 : ℝ)..1, f s : ℝ) : ℂ) = ∫ s in (0 : ℝ)..1, F s := by
  rw [← intervalIntegral.integral_ofReal]
  exact intervalIntegral.integral_congr fun s _ => hf s

private theorem ofReal_realExpKernel (n : ℕ) (x s : ℝ) :
    (((n : ℝ) * (1 - x * (1 - s)) * (1 - s) ^ (n - 1) *
        Real.exp ((n : ℝ) * x * s) : ℝ) : ℂ) =
      expKernel n (x : ℂ) s := by
  simp [expKernel, Complex.ofReal_exp]

private theorem ofReal_coeff_mul_realExpKernel (n m : ℕ) (x s : ℝ) :
    ((expPartialSumCoeff m (x * (1 - s)) *
        ((n : ℝ) * (1 - x * (1 - s)) * (1 - s) ^ (n - 1) *
          Real.exp ((n : ℝ) * x * s)) : ℝ) : ℂ) =
      expPartialSumCoeff m ((x : ℂ) * (1 - (s : ℂ))) * expKernel n (x : ℂ) s := by
  push_cast [expKernel, Complex.ofReal_exp]
  rfl

private theorem ofReal_mul_one_sub_pow_mul_exp (n : ℕ) (x s : ℝ) :
    (((n : ℝ) * x * (1 - s) ^ n * Real.exp ((n : ℝ) * x * s) : ℝ) : ℂ) =
      (n : ℂ) * (x : ℂ) * (1 - (s : ℂ)) ^ n * Complex.exp ((n : ℂ) * (x : ℂ) * s) := by
  push_cast [Complex.ofReal_exp]
  rfl

/-- Exact `m`-fold integration-by-parts expansion of `∫₀¹ n x (1 - s)^n e^{n x s} ds` for real
`x < 1`. -/
theorem integral_mul_one_sub_pow_mul_exp_eq_sum_add_integral {n : ℕ} (hn : n ≠ 0) {x : ℝ}
    (hx : x < 1) (m : ℕ) :
    ∫ s in (0 : ℝ)..1, (n : ℝ) * x * (1 - s) ^ n * Real.exp ((n : ℝ) * x * s) =
      ∑ k ∈ Finset.range m, expPartialSumCoeff k x / (n : ℝ) ^ k +
        ((n : ℝ) ^ m)⁻¹ * ∫ s in (0 : ℝ)..1, expPartialSumCoeff m (x * (1 - s)) *
          ((n : ℝ) * (1 - x * (1 - s)) * (1 - s) ^ (n - 1) *
            Real.exp ((n : ℝ) * x * s)) := by
  apply Complex.ofReal_inj.mp
  push_cast
  rw [ofReal_intervalIntegral_zero_one (ofReal_mul_one_sub_pow_mul_exp n x),
    ofReal_intervalIntegral_zero_one (ofReal_coeff_mul_realExpKernel n m x),
    integral_mul_one_sub_pow_mul_cexp_eq_sum_add_integral hn (by simpa using hx) m]
  simp only [expKernel]

private theorem exp_mul_sub_sum_range_succ_eq_mul_integral (n : ℕ) (x : ℝ) :
    Real.exp ((n : ℝ) * x) - ∑ k ∈ Finset.range (n + 1), ((n : ℝ) * x) ^ k / (k ! : ℝ) =
      (((n : ℝ) * x) ^ n / (n ! : ℝ)) *
        ∫ s in (0 : ℝ)..1, (n : ℝ) * x * (1 - s) ^ n * Real.exp ((n : ℝ) * x * s) := by
  apply Complex.ofReal_inj.mp
  push_cast [Complex.ofReal_exp]
  rw [cexp_mul_sub_sum_range_succ_eq_mul_integral,
    ofReal_intervalIntegral_zero_one (ofReal_mul_one_sub_pow_mul_exp n x)]

/-- Exact `m`-term expansion with integral remainder for `e^{n x} - ∑_{k ≤ n} (n x)^k / k!` for
real `x < 1`. -/
theorem exp_mul_sub_sum_range_succ_eq_sum_add_integral {n : ℕ} (hn : n ≠ 0) {x : ℝ} (hx : x < 1)
    (m : ℕ) :
    Real.exp ((n : ℝ) * x) - ∑ k ∈ Finset.range (n + 1), ((n : ℝ) * x) ^ k / (k ! : ℝ) =
      (((n : ℝ) * x) ^ n / (n ! : ℝ)) *
        (∑ k ∈ Finset.range m, expPartialSumCoeff k x / (n : ℝ) ^ k +
          ((n : ℝ) ^ m)⁻¹ * ∫ s in (0 : ℝ)..1, expPartialSumCoeff m (x * (1 - s)) *
            ((n : ℝ) * (1 - x * (1 - s)) * (1 - s) ^ (n - 1) *
              Real.exp ((n : ℝ) * x * s))) := by
  rw [exp_mul_sub_sum_range_succ_eq_mul_integral,
    integral_mul_one_sub_pow_mul_exp_eq_sum_add_integral hn hx m]

private theorem integral_real_expKernel {n : ℕ} (hn : n ≠ 0) (x : ℝ) :
    ∫ s in (0 : ℝ)..1,
      (n : ℝ) * (1 - x * (1 - s)) * (1 - s) ^ (n - 1) * Real.exp ((n : ℝ) * x * s) = 1 := by
  apply Complex.ofReal_inj.mp
  rw [ofReal_intervalIntegral_zero_one (ofReal_realExpKernel n x),
    integral_expKernel hn (x : ℂ), Complex.ofReal_one]

private theorem real_expKernel_nonneg (n : ℕ) {x : ℝ} (hx : x < 1) {s : ℝ} (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) :
    0 ≤ (n : ℝ) * (1 - x * (1 - s)) * (1 - s) ^ (n - 1) * Real.exp ((n : ℝ) * x * s) := by
  have h1x : 0 ≤ 1 - x * (1 - s) := by
    rcases le_or_gt x 0 with _ | _ <;> nlinarith
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) h1x) (pow_nonneg (by linarith) _))
    (Real.exp_pos _).le

private theorem abs_im_mul_one_sub_le {M : ℝ} {w : ℂ} (hw_re : w.re < 1)
    (hw_im : |w.im| ≤ M * (1 - w.re)) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    |(w * (1 - (s : ℂ))).im| ≤ M * (1 - (w * (1 - (s : ℂ))).re) := by
  have hM : 0 ≤ M :=
    nonneg_of_mul_nonneg_left ((abs_nonneg w.im).trans hw_im) (sub_pos.mpr hw_re)
  have hs_nonneg : 0 ≤ 1 - s := sub_nonneg.mpr hs1
  have him : (w * (1 - (s : ℂ))).im = w.im * (1 - s) := by simp
  have hre : (w * (1 - (s : ℂ))).re = w.re * (1 - s) := by simp
  rw [him, hre, abs_mul, abs_of_nonneg hs_nonneg]
  calc
    |w.im| * (1 - s) ≤ (M * (1 - w.re)) * (1 - s) :=
      mul_le_mul_of_nonneg_right hw_im hs_nonneg
    _ = M * (1 - s - w.re * (1 - s)) := by ring
    _ ≤ M * (1 - w.re * (1 - s)) := by nlinarith

private theorem norm_one_sub_mul_one_sub_le {M : ℝ} {w : ℂ} (hw_re : w.re < 1)
    (hw_im : |w.im| ≤ M * (1 - w.re)) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ‖1 - w * (1 - (s : ℂ))‖ ≤ (1 + M) * (1 - w.re * (1 - s)) := by
  have hs_im := abs_im_mul_one_sub_le hw_re hw_im hs0 hs1
  have hre_pos : 0 ≤ 1 - w.re * (1 - s) := by
    rcases le_or_gt w.re 0 with _ | _ <;> nlinarith
  have hre_sub : (1 - w * (1 - (s : ℂ))).re = 1 - w.re * (1 - s) := by simp
  have hre_mul : (w * (1 - (s : ℂ))).re = w.re * (1 - s) := by simp
  have him_sub : |(1 - w * (1 - (s : ℂ))).im| = |(w * (1 - (s : ℂ))).im| := by simp
  rw [hre_mul] at hs_im
  calc
    ‖1 - w * (1 - (s : ℂ))‖
      ≤ |(1 - w * (1 - (s : ℂ))).re| + |(1 - w * (1 - (s : ℂ))).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ = (1 - w.re * (1 - s)) + |(w * (1 - (s : ℂ))).im| := by
        rw [hre_sub, abs_of_nonneg hre_pos, him_sub]
    _ ≤ (1 - w.re * (1 - s)) + M * (1 - w.re * (1 - s)) := by linarith
    _ = (1 + M) * (1 - w.re * (1 - s)) := by ring

private theorem norm_coeff_mul_expKernel_le (n m : ℕ) {δ M : ℝ} (hδ : 0 < δ) {w : ℂ}
    (hw_re : w.re ≤ 1 - δ) (hw_im : |w.im| ≤ M * (1 - w.re)) {s : ℝ} (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) :
    ‖expPartialSumCoeff m (w * (1 - (s : ℂ))) * expKernel n w s‖ ≤
      ((2 * m - 1)‼ : ℝ) * (1 + M) ^ (2 * m + 2) * max 1 ((δ ^ (2 * m + 1))⁻¹) *
        ((n : ℝ) * (1 - w.re * (1 - s)) * (1 - s) ^ (n - 1) * Real.exp ((n : ℝ) * w.re * s)) := by
  have hw_lt : w.re < 1 := by linarith
  have hM : 0 ≤ M :=
    nonneg_of_mul_nonneg_left ((abs_nonneg w.im).trans hw_im) (sub_pos.mpr hw_lt)
  have hs_im := abs_im_mul_one_sub_le hw_lt hw_im hs0 hs1
  have hcoeff : ‖expPartialSumCoeff m (w * (1 - (s : ℂ)))‖ ≤
      ((2 * m - 1)‼ : ℝ) * (1 + M) ^ (2 * m + 1) * max 1 ((δ ^ (2 * m + 1))⁻¹) := by
    rcases le_or_gt w.re 0 with hre0 | hre0
    · have hs_re : (w * (1 - (s : ℂ))).re ≤ 0 := by simp; nlinarith
      exact (norm_expPartialSumCoeff_le_of_re_nonpos m hs_re hs_im).trans
        (le_mul_of_one_le_right (by positivity) (le_max_left 1 _))
    · have hs_re : (w * (1 - (s : ℂ))).re ≤ 1 - δ := by simp; nlinarith
      exact norm_expPartialSumCoeff_le_of_re_le m hδ hs_re hs_im
  have h1w := norm_one_sub_mul_one_sub_le hw_lt hw_im hs0 hs1
  have h1s : ‖(1 - (s : ℂ)) ^ (n - 1)‖ = (1 - s) ^ (n - 1) := by
    rw [norm_pow, ← abs_of_nonneg (sub_nonneg.mpr hs1), ← Real.norm_eq_abs, ← Complex.norm_real]
    congr 1
    push_cast
    rfl
  have hexp : ‖Complex.exp ((n : ℂ) * w * s)‖ = Real.exp ((n : ℝ) * w.re * s) := by
    rw [Complex.norm_exp]; congr 1; simp [mul_assoc]
  have hexp2 : 2 * m + 2 = (2 * m + 1) + 1 := by omega
  dsimp only [expKernel]
  rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_natCast, h1s, hexp]
  calc
    ‖expPartialSumCoeff m (w * (1 - (s : ℂ)))‖ *
        ((n : ℝ) * ‖1 - w * (1 - (s : ℂ))‖ * (1 - s) ^ (n - 1) * Real.exp ((n : ℝ) * w.re * s))
      ≤ (((2 * m - 1)‼ : ℝ) * (1 + M) ^ (2 * m + 1) * max 1 ((δ ^ (2 * m + 1))⁻¹)) *
          ((n : ℝ) * ((1 + M) * (1 - w.re * (1 - s))) * (1 - s) ^ (n - 1) *
            Real.exp ((n : ℝ) * w.re * s)) := by
        refine mul_le_mul hcoeff ?_ (by positivity) (by positivity)
        have hfac : 0 ≤ (1 - s) ^ (n - 1) * Real.exp ((n : ℝ) * w.re * s) :=
          mul_nonneg (pow_nonneg (by linarith) _) (Real.exp_pos _).le
        simpa [mul_assoc] using mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right h1w hfac) (Nat.cast_nonneg n)
    _ = ((2 * m - 1)‼ : ℝ) * (1 + M) ^ (2 * m + 2) * max 1 ((δ ^ (2 * m + 1))⁻¹) *
          ((n : ℝ) * (1 - w.re * (1 - s)) * (1 - s) ^ (n - 1) *
            Real.exp ((n : ℝ) * w.re * s)) := by
        rw [hexp2, pow_succ]; ring

private theorem norm_integral_coeff_mul_expKernel_le {n : ℕ} (hn : n ≠ 0) (m : ℕ) {δ M : ℝ}
    (hδ : 0 < δ) {w : ℂ} (hw_re : w.re ≤ 1 - δ) (hw_im : |w.im| ≤ M * (1 - w.re)) :
    ‖∫ s in (0 : ℝ)..1, expPartialSumCoeff m (w * (1 - (s : ℂ))) * expKernel n w s‖ ≤
      ((2 * m - 1)‼ : ℝ) * (1 + M) ^ (2 * m + 2) * max 1 ((δ ^ (2 * m + 1))⁻¹) := by
  let C : ℝ := ((2 * m - 1)‼ : ℝ) * (1 + M) ^ (2 * m + 2) * max 1 ((δ ^ (2 * m + 1))⁻¹)
  let g : ℝ → ℝ := fun s =>
    C * ((n : ℝ) * (1 - w.re * (1 - s)) * (1 - s) ^ (n - 1) * Real.exp ((n : ℝ) * w.re * s))
  have hg_int : IntervalIntegrable g volume 0 1 := by
    dsimp only [g]; exact (by fun_prop : Continuous _).continuousOn.intervalIntegrable
  calc
    ‖∫ s in (0 : ℝ)..1, expPartialSumCoeff m (w * (1 - (s : ℂ))) * expKernel n w s‖
      ≤ ∫ s in (0 : ℝ)..1, g s :=
        intervalIntegral.norm_integral_le_of_norm_le zero_le_one
          (Eventually.of_forall fun s hs =>
            norm_coeff_mul_expKernel_le n m hδ hw_re hw_im hs.1.le hs.2) hg_int
    _ = C := by
        dsimp only [g]
        rw [intervalIntegral.integral_const_mul, integral_real_expKernel hn w.re, mul_one]

/-- Explicit uniform remainder bound for `∑_{k ≤ n} (n w)^k / k!` on the complex wedge
`{w : ℂ | Re w ≤ 1 - δ ∧ |Im w| ≤ M * (1 - Re w)}` (`δ > 0`, `n ≠ 0`). -/
theorem norm_sum_range_succ_div_factorial_sub_le {n : ℕ} (hn : n ≠ 0) (m : ℕ) {δ M : ℝ}
    (hδ : 0 < δ) {w : ℂ} (hw_re : w.re ≤ 1 - δ) (hw_im : |w.im| ≤ M * (1 - w.re)) :
    ‖(∑ k ∈ Finset.range (n + 1), ((n : ℂ) * w) ^ k / (k ! : ℂ)) -
        (Complex.exp ((n : ℂ) * w) - (((n : ℂ) * w) ^ n / (n ! : ℂ)) *
          ∑ k ∈ Finset.range m, expPartialSumCoeff k w / (n : ℂ) ^ k)‖ ≤
      ‖((n : ℂ) * w) ^ n / (n ! : ℂ)‖ *
        (((2 * m - 1)‼ : ℝ) * (1 + M) ^ (2 * m + 2) * max 1 ((δ ^ (2 * m + 1))⁻¹)) /
          (n : ℝ) ^ m := by
  have hw_lt : w.re < 1 := by linarith
  have hrew : (∑ k ∈ Finset.range (n + 1), ((n : ℂ) * w) ^ k / (k ! : ℂ)) -
      (Complex.exp ((n : ℂ) * w) - (((n : ℂ) * w) ^ n / (n ! : ℂ)) *
        ∑ k ∈ Finset.range m, expPartialSumCoeff k w / (n : ℂ) ^ k) =
      -((((n : ℂ) * w) ^ n / (n ! : ℂ)) * (((n : ℂ) ^ m)⁻¹ *
        ∫ s in (0 : ℝ)..1, expPartialSumCoeff m (w * (1 - (s : ℂ))) * expKernel n w s)) := by
    simp only [expKernel]
    linear_combination -cexp_mul_sub_sum_range_succ_eq_sum_add_integral hn hw_lt m
  rw [hrew, norm_neg, norm_mul, norm_mul, norm_inv, norm_pow, Complex.norm_natCast, mul_div_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  rw [div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left
    (norm_integral_coeff_mul_expKernel_le hn m hδ hw_re hw_im) (by positivity)

/-- Uniform Buckholtz expansion of `∑_{k ≤ n} (n w)^k / k!` on the complex wedge
`{w : ℂ | Re w ≤ 1 - δ ∧ |Im w| ≤ M * (1 - Re w)}` (`δ > 0`). -/
theorem isBigO_sum_range_succ_div_factorial_sub_complex {δ : ℝ} (hδ : 0 < δ) (M : ℝ) (m : ℕ) :
    (fun q : ℕ × ℂ =>
      (∑ k ∈ Finset.range (q.1 + 1), ((q.1 : ℂ) * q.2) ^ k / (k ! : ℂ)) -
        (Complex.exp ((q.1 : ℂ) * q.2) - (((q.1 : ℂ) * q.2) ^ q.1 / (q.1 ! : ℂ)) *
          ∑ k ∈ Finset.range m, expPartialSumCoeff k q.2 / (q.1 : ℂ) ^ k))
      =O[atTop ×ˢ 𝓟 {w : ℂ | w.re ≤ 1 - δ ∧ |w.im| ≤ M * (1 - w.re)}]
        fun q : ℕ × ℂ => (((q.1 : ℂ) * q.2) ^ q.1 / (q.1 ! : ℂ)) / (q.1 : ℂ) ^ m := by
  rcases lt_or_ge M 0 with hM | _
  · have hempty : {w : ℂ | w.re ≤ 1 - δ ∧ |w.im| ≤ M * (1 - w.re)} = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro w ⟨hw_re, hw_im⟩
      have : M * (1 - w.re) < 0 := mul_neg_of_neg_of_pos hM (by linarith)
      linarith [abs_nonneg w.im]
    rw [hempty, principal_empty, prod_bot]
    exact isBigO_bot _ _
  · refine IsBigO.of_bound
      (((2 * m - 1)‼ : ℝ) * (1 + M) ^ (2 * m + 2) * max 1 ((δ ^ (2 * m + 1))⁻¹)) ?_
    filter_upwards [prod_mem_prod (eventually_ne_atTop 0) (mem_principal_self _)] with q hq
    have hrhs : ‖(((q.1 : ℂ) * q.2) ^ q.1 / (q.1 ! : ℂ)) / (q.1 : ℂ) ^ m‖ =
        ‖((q.1 : ℂ) * q.2) ^ q.1 / (q.1 ! : ℂ)‖ / (q.1 : ℝ) ^ m := by
      rw [norm_div, norm_pow, Complex.norm_natCast]
    rw [hrhs]
    refine (norm_sum_range_succ_div_factorial_sub_le hq.1 m hδ hq.2.1 hq.2.2).trans_eq ?_
    ring

private theorem ofReal_sum_range_succ_sub_approx (n m : ℕ) (x : ℝ) :
    (((∑ k ∈ Finset.range (n + 1), ((n : ℝ) * x) ^ k / (k ! : ℝ)) -
        (Real.exp ((n : ℝ) * x) - (((n : ℝ) * x) ^ n / (n ! : ℝ)) *
          ∑ k ∈ Finset.range m, expPartialSumCoeff k x / (n : ℝ) ^ k) : ℝ) : ℂ) =
      (∑ k ∈ Finset.range (n + 1), ((n : ℂ) * (x : ℂ)) ^ k / (k ! : ℂ)) -
        (Complex.exp ((n : ℂ) * (x : ℂ)) - (((n : ℂ) * (x : ℂ)) ^ n / (n ! : ℂ)) *
          ∑ k ∈ Finset.range m, expPartialSumCoeff k (x : ℂ) / (n : ℂ) ^ k) := by
  push_cast [Complex.ofReal_exp]
  rfl

/-- Explicit uniform remainder bound for `∑_{k ≤ n} (n x)^k / k!` across the entire real half-line
`x ≤ 1 - δ` (`δ > 0`, `n ≠ 0`). -/
theorem abs_sum_range_succ_div_factorial_sub_le {n : ℕ} (hn : n ≠ 0) (m : ℕ) {δ x : ℝ}
    (hδ : 0 < δ) (hx : x ≤ 1 - δ) :
    |(∑ k ∈ Finset.range (n + 1), ((n : ℝ) * x) ^ k / (k ! : ℝ)) -
        (Real.exp ((n : ℝ) * x) - (((n : ℝ) * x) ^ n / (n ! : ℝ)) *
          ∑ k ∈ Finset.range m, expPartialSumCoeff k x / (n : ℝ) ^ k)| ≤
      |((n : ℝ) * x) ^ n / (n ! : ℝ)| *
        (((2 * m - 1)‼ : ℝ) * max 1 ((δ ^ (2 * m + 1))⁻¹)) / (n : ℝ) ^ m := by
  have h := norm_sum_range_succ_div_factorial_sub_le hn m hδ (M := 0) (w := (x : ℂ))
    (by simpa using hx) (by simp)
  have hpref : ‖((n : ℂ) * (x : ℂ)) ^ n / (n ! : ℂ)‖ = |((n : ℝ) * x) ^ n / (n ! : ℝ)| := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real]
    congr 1
    push_cast
    rfl
  rw [← ofReal_sum_range_succ_sub_approx, Complex.norm_real, Real.norm_eq_abs, hpref] at h
  simpa using h

/-- Explicit uniform remainder bound for the normalized integral
`∫₀¹ n x (1 - s)^n e^{n x s} ds` across `x ≤ 1 - δ` (`δ > 0`, `n ≠ 0`). -/
theorem abs_integral_mul_one_sub_pow_mul_exp_sub_sum_le {n : ℕ} (hn : n ≠ 0) (m : ℕ) {δ x : ℝ}
    (hδ : 0 < δ) (hx : x ≤ 1 - δ) :
    |(∫ s in (0 : ℝ)..1, (n : ℝ) * x * (1 - s) ^ n * Real.exp ((n : ℝ) * x * s)) -
        ∑ k ∈ Finset.range m, expPartialSumCoeff k x / (n : ℝ) ^ k| ≤
      ((2 * m - 1)‼ : ℝ) * max 1 ((δ ^ (2 * m + 1))⁻¹) / (n : ℝ) ^ m := by
  have hx_lt : x < 1 := by linarith
  rw [integral_mul_one_sub_pow_mul_exp_eq_sum_add_integral hn hx_lt m, add_sub_cancel_left,
    abs_mul, abs_inv, abs_pow, Nat.abs_cast, div_eq_inv_mul]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have h := norm_integral_coeff_mul_expKernel_le hn m hδ (M := 0) (w := (x : ℂ))
    (by simpa using hx) (by simp)
  rw [← ofReal_intervalIntegral_zero_one (ofReal_coeff_mul_realExpKernel n m x),
    Complex.norm_real, Real.norm_eq_abs] at h
  simpa using h

/-- **DLMF 8.11.18**: uniform asymptotic expansion of the exponential partial sums
`∑_{k ≤ n} (n x)^k / k!` across `x ≤ 1 - δ` (`δ > 0`) to arbitrary order `m`. -/
theorem isBigO_sum_range_succ_div_factorial_sub {δ : ℝ} (hδ : 0 < δ) (m : ℕ) :
    (fun q : ℕ × ℝ =>
      (∑ k ∈ Finset.range (q.1 + 1), ((q.1 : ℝ) * q.2) ^ k / (k ! : ℝ)) -
        (Real.exp ((q.1 : ℝ) * q.2) - (((q.1 : ℝ) * q.2) ^ q.1 / (q.1 ! : ℝ)) *
          ∑ k ∈ Finset.range m, expPartialSumCoeff k q.2 / (q.1 : ℝ) ^ k))
      =O[atTop ×ˢ 𝓟 (Iic (1 - δ))]
        fun q : ℕ × ℝ => (((q.1 : ℝ) * q.2) ^ q.1 / (q.1 ! : ℝ)) / (q.1 : ℝ) ^ m := by
  refine IsBigO.of_bound (((2 * m - 1)‼ : ℝ) * max 1 ((δ ^ (2 * m + 1))⁻¹)) ?_
  filter_upwards [prod_mem_prod (eventually_ne_atTop 0) (mem_principal_self (Iic (1 - δ)))]
    with q hq
  have hrhs : ‖(((q.1 : ℝ) * q.2) ^ q.1 / (q.1 ! : ℝ)) / (q.1 : ℝ) ^ m‖ =
      |((q.1 : ℝ) * q.2) ^ q.1 / (q.1 ! : ℝ)| / (q.1 : ℝ) ^ m := by
    have hpow : |(q.1 : ℝ) ^ m| = (q.1 : ℝ) ^ m := abs_of_nonneg (by positivity)
    rw [Real.norm_eq_abs, abs_div, hpow]
  rw [Real.norm_eq_abs, hrhs]
  refine (abs_sum_range_succ_div_factorial_sub_le hq.1 m hδ hq.2).trans_eq ?_
  ring

/-- **DLMF 8.11.18** in normalized quotient form, uniformly on `x ≤ 1 - δ` (`δ > 0`). -/
theorem isBigO_div_exp_sub_sum_range_succ_sub {δ : ℝ} (hδ : 0 < δ) (m : ℕ) :
    (fun q : ℕ × ℝ =>
      (Real.exp ((q.1 : ℝ) * q.2) -
          ∑ k ∈ Finset.range (q.1 + 1), ((q.1 : ℝ) * q.2) ^ k / (k ! : ℝ)) /
        (((q.1 : ℝ) * q.2) ^ q.1 / (q.1 ! : ℝ)) -
        ∑ k ∈ Finset.range m, expPartialSumCoeff k q.2 / (q.1 : ℝ) ^ k)
      =O[atTop ×ˢ 𝓟 (Iic (1 - δ))] fun q : ℕ × ℝ => ((q.1 : ℝ) ^ m)⁻¹ := by
  refine IsBigO.of_bound (((2 * m - 1)‼ : ℝ) * max 1 ((δ ^ (2 * m + 1))⁻¹)) ?_
  filter_upwards [prod_mem_prod (eventually_ne_atTop 0) (mem_principal_self (Iic (1 - δ)))]
    with q hq
  simp only [Real.norm_eq_abs, abs_inv, abs_pow, Nat.abs_cast]
  rcases eq_or_ne q.2 0 with hx0 | hx0
  · have hzero : (Real.exp ((q.1 : ℝ) * q.2) -
          ∑ k ∈ Finset.range (q.1 + 1), ((q.1 : ℝ) * q.2) ^ k / (k ! : ℝ)) /
        (((q.1 : ℝ) * q.2) ^ q.1 / (q.1 ! : ℝ)) -
        ∑ k ∈ Finset.range m, expPartialSumCoeff k q.2 / (q.1 : ℝ) ^ k = 0 := by
      simp [hx0, zero_pow hq.1]
    rw [hzero, abs_zero]
    positivity
  · have hpref : ((q.1 : ℝ) * q.2) ^ q.1 / (q.1 ! : ℝ) ≠ 0 :=
      div_ne_zero (pow_ne_zero _ (mul_ne_zero (Nat.cast_ne_zero.mpr hq.1) hx0))
        (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero q.1))
    rw [exp_mul_sub_sum_range_succ_eq_mul_integral, mul_div_cancel_left₀ _ hpref]
    simpa [div_eq_mul_inv] using abs_integral_mul_one_sub_pow_mul_exp_sub_sum_le hq.1 m hδ hq.2

/-- **DLMF 8.11.18–8.11.19** stated directly in terms of any sequence `d : ℕ → ℝ → ℝ` satisfying
the differential recurrence `d 0 x = x / (1 - x)` and `d (k + 1) x = -(x / (1 - x)) * deriv (d k) x`
for `x ≠ 1`. -/
theorem isBigO_sum_range_succ_div_factorial_sub_of_recurrence {d : ℕ → ℝ → ℝ}
    (hd0 : ∀ x ≠ 1, d 0 x = x / (1 - x))
    (hd : ∀ k, ∀ x ≠ 1, d (k + 1) x = -(x / (1 - x)) * deriv (d k) x)
    {δ : ℝ} (hδ : 0 < δ) (m : ℕ) :
    (fun q : ℕ × ℝ =>
      (∑ k ∈ Finset.range (q.1 + 1), ((q.1 : ℝ) * q.2) ^ k / (k ! : ℝ)) -
        (Real.exp ((q.1 : ℝ) * q.2) - (((q.1 : ℝ) * q.2) ^ q.1 / (q.1 ! : ℝ)) *
          ∑ k ∈ Finset.range m, d k q.2 / (q.1 : ℝ) ^ k))
      =O[atTop ×ˢ 𝓟 (Iic (1 - δ))]
        fun q : ℕ × ℝ => (((q.1 : ℝ) * q.2) ^ q.1 / (q.1 ! : ℝ)) / (q.1 : ℝ) ^ m := by
  refine (isBigO_sum_range_succ_div_factorial_sub hδ m).congr' ?_ EventuallyEq.rfl
  filter_upwards [prod_mem_prod Filter.univ_mem (mem_principal_self (Iic (1 - δ)))] with q hq
  have hq2 : q.2 ≤ 1 - δ := hq.2
  have hne : q.2 ≠ 1 := by linarith
  have hsum : ∑ k ∈ Finset.range m, expPartialSumCoeff k q.2 / (q.1 : ℝ) ^ k =
      ∑ k ∈ Finset.range m, d k q.2 / (q.1 : ℝ) ^ k :=
    Finset.sum_congr rfl fun k _ => by rw [eq_expPartialSumCoeff_of_recurrence hd0 hd k hne]
  rw [hsum]

/-- Enveloping lower bound on `[0, 1)`: the `m`-th normalized remainder has sign `(-1)^m`. -/
theorem neg_one_pow_mul_integral_sub_sum_nonneg {n : ℕ} (hn : n ≠ 0) (m : ℕ) {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x < 1) :
    0 ≤ (-1) ^ m *
      ((∫ s in (0 : ℝ)..1, (n : ℝ) * x * (1 - s) ^ n * Real.exp ((n : ℝ) * x * s)) -
        ∑ k ∈ Finset.range m, expPartialSumCoeff k x / (n : ℝ) ^ k) := by
  rw [integral_mul_one_sub_pow_mul_exp_eq_sum_add_integral hn hx1 m, add_sub_cancel_left,
    ← mul_assoc, mul_comm ((-1 : ℝ) ^ m), mul_assoc, ← intervalIntegral.integral_const_mul]
  refine mul_nonneg (by positivity) (intervalIntegral.integral_nonneg zero_le_one fun s hs => ?_)
  rw [← mul_assoc]
  exact mul_nonneg
    (neg_one_pow_mul_expPartialSumCoeff_nonneg m
      (mul_nonneg hx0 (by linarith [hs.2])) (by nlinarith [hs.1, hs.2]))
    (real_expKernel_nonneg n hx1 hs.1 hs.2)

/-- Enveloping upper bound on `[0, 1)`: the `m`-th normalized remainder is bounded in magnitude by
the first neglected term `(-1)^m d_m(x) / n^m`. -/
theorem neg_one_pow_mul_integral_sub_sum_le {n : ℕ} (hn : n ≠ 0) (m : ℕ) {x : ℝ} (hx0 : 0 ≤ x)
    (hx1 : x < 1) :
    (-1) ^ m *
      ((∫ s in (0 : ℝ)..1, (n : ℝ) * x * (1 - s) ^ n * Real.exp ((n : ℝ) * x * s)) -
        ∑ k ∈ Finset.range m, expPartialSumCoeff k x / (n : ℝ) ^ k) ≤
      (-1) ^ m * expPartialSumCoeff m x / (n : ℝ) ^ m := by
  rw [integral_mul_one_sub_pow_mul_exp_eq_sum_add_integral hn hx1 m, add_sub_cancel_left,
    ← mul_assoc, mul_comm ((-1 : ℝ) ^ m), mul_assoc, ← intervalIntegral.integral_const_mul,
    div_eq_inv_mul]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  let K : ℝ → ℝ := fun s =>
    (n : ℝ) * (1 - x * (1 - s)) * (1 - s) ^ (n - 1) * Real.exp ((n : ℝ) * x * s)
  have hK_int : IntervalIntegrable K volume 0 1 := by
    dsimp only [K]; exact (by fun_prop : Continuous _).continuousOn.intervalIntegrable
  have hL_int : IntervalIntegrable
      (fun s => (-1 : ℝ) ^ m * (expPartialSumCoeff m (x * (1 - s)) * K s)) volume 0 1 := by
    dsimp only [K]
    have hc : ContinuousOn (fun s : ℝ => expPartialSumCoeff m (x * (1 - s))) (uIcc 0 1) := by
      rw [Set.uIcc_of_le zero_le_one]
      intro s hs
      have hne : x * (1 - s) ≠ 1 := by nlinarith [hs.1, hs.2]
      have hf : ContinuousAt (expPartialSumCoeff m) (x * (1 - s)) :=
        (hasDerivAt_expPartialSumCoeff m hne).continuousAt
      have hg : ContinuousAt (fun t : ℝ => x * (1 - t)) s := by fun_prop
      exact (hf.comp (f := fun t : ℝ => x * (1 - t)) hg).continuousWithinAt
    exact (continuousOn_const.mul (hc.mul (by fun_prop : Continuous _).continuousOn))
      |>.intervalIntegrable
  calc
    ∫ s in (0 : ℝ)..1, (-1 : ℝ) ^ m * (expPartialSumCoeff m (x * (1 - s)) * K s)
      ≤ ∫ s in (0 : ℝ)..1, ((-1 : ℝ) ^ m * expPartialSumCoeff m x) * K s := by
        refine intervalIntegral.integral_mono_on zero_le_one hL_int (hK_int.const_mul _)
          fun s hs => ?_
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right
          (neg_one_pow_mul_expPartialSumCoeff_mono m (mul_nonneg hx0 (by linarith [hs.2]))
            (by nlinarith [hs.1]) hx1)
          (real_expKernel_nonneg n hx1 hs.1 hs.2)
    _ = (-1) ^ m * expPartialSumCoeff m x := by
        rw [intervalIntegral.integral_const_mul, integral_real_expKernel hn x, mul_one]

/-- Pointwise limit `(e^{n x} - ∑_{k ≤ n} (n x)^k / k!) / ((n x)^n / n!) → x / (1 - x)` as
`n → ∞` for every `x < 1` (including `x = 0`, where both sides vanish). -/
theorem tendsto_div_exp_sub_sum_range_succ_atTop {x : ℝ} (hx : x < 1) :
    Tendsto (fun n : ℕ =>
      (Real.exp ((n : ℝ) * x) - ∑ k ∈ Finset.range (n + 1), ((n : ℝ) * x) ^ k / (k ! : ℝ)) /
        (((n : ℝ) * x) ^ n / (n ! : ℝ)))
      atTop (𝓝 (x / (1 - x))) := by
  have hbig : (fun n : ℕ =>
      (Real.exp ((n : ℝ) * x) - ∑ k ∈ Finset.range (n + 1), ((n : ℝ) * x) ^ k / (k ! : ℝ)) /
        (((n : ℝ) * x) ^ n / (n ! : ℝ)) - (x / (1 - x)))
      =O[atTop] fun n : ℕ => ((n : ℝ) ^ 1)⁻¹ := by
    have ht : Tendsto (fun n : ℕ => (n, x)) atTop (atTop ×ˢ 𝓟 (Iic (1 - (1 - x)))) :=
      tendsto_id.prodMk (tendsto_principal.mpr (Eventually.of_forall fun _ => by simp))
    simpa [Function.comp_def] using
      (isBigO_div_exp_sub_sum_range_succ_sub (δ := 1 - x) (sub_pos.mpr hx) 1).comp_tendsto ht
  have h0 : Tendsto (fun n : ℕ => ((n : ℝ) ^ 1)⁻¹) atTop (𝓝 0) := by
    simpa [Function.comp_def] using tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  simpa using (hbig.trans_tendsto h0).add_const (x / (1 - x))

/-- Leading asymptotic equivalence
`e^{n x} - ∑_{k ≤ n} (n x)^k / k! ~ ((n x)^n / n!) * (x / (1 - x))` as `n → ∞` for every `x < 1`
(at `x = 0`, both sides vanish for `n ≥ 1`). -/
theorem exp_mul_sub_sum_range_succ_isEquivalent {x : ℝ} (hx : x < 1) :
    (fun n : ℕ =>
      Real.exp ((n : ℝ) * x) - ∑ k ∈ Finset.range (n + 1), ((n : ℝ) * x) ^ k / (k ! : ℝ))
      ~[atTop] fun n : ℕ => (((n : ℝ) * x) ^ n / (n ! : ℝ)) * (x / (1 - x)) := by
  rw [IsEquivalent]
  have hbig : (fun n : ℕ =>
      (Real.exp ((n : ℝ) * x) - ∑ k ∈ Finset.range (n + 1), ((n : ℝ) * x) ^ k / (k ! : ℝ)) -
        (((n : ℝ) * x) ^ n / (n ! : ℝ)) * (x / (1 - x)))
      =O[atTop] fun n : ℕ => (((n : ℝ) * x) ^ n / (n ! : ℝ)) / (n : ℝ) := by
    have ht : Tendsto (fun n : ℕ => (n, x)) atTop (atTop ×ˢ 𝓟 (Iic (1 - (1 - x)))) :=
      tendsto_id.prodMk (tendsto_principal.mpr (Eventually.of_forall fun _ => by simp))
    have h := (isBigO_sum_range_succ_div_factorial_sub (δ := 1 - x) (sub_pos.mpr hx) 1).neg_left
      |>.comp_tendsto ht
    refine h.congr' ?_ (Eventually.of_forall fun n => by simp)
    filter_upwards with n
    simp only [Function.comp_apply, Finset.range_one, Finset.sum_singleton, expPartialSumCoeff_zero,
      pow_zero, div_one]
    ring
  rcases eq_or_ne x 0 with rfl | hx0
  · refine IsLittleO.congr' (isLittleO_zero _ _) ?_ EventuallyEq.rfl
    filter_upwards [eventually_ne_atTop 0] with n _
    simp [Finset.sum_range_succ']
  · have hx1 : x / (1 - x) ≠ 0 := div_ne_zero hx0 (sub_ne_zero.mpr hx.ne')
    refine hbig.trans_isLittleO ?_
    have hinv : (fun n : ℕ => ((n : ℝ))⁻¹) =o[atTop] fun _ : ℕ => x / (1 - x) :=
      (isLittleO_const_iff hx1).mpr
        (by simpa [Function.comp_def] using tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
    refine ((isBigO_refl (fun n : ℕ => ((n : ℝ) * x) ^ n / (n ! : ℝ)) atTop).mul_isLittleO
      hinv).congr' (Eventually.of_forall fun n => by ring)
      EventuallyEq.rfl

end TauCeti

end
