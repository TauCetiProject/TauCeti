/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import TauCeti.Analysis.Asymptotics.AsymptoticExpansion
public import TauCeti.Analysis.Calculus.IteratedDeriv.Within
import TauCeti.Analysis.Calculus.Deriv.InvPow
import TauCeti.Analysis.MellinTransform.Basic
import TauCeti.Analysis.SpecialFunctions.Integrability.Rpow
import TauCeti.Analysis.SpecialFunctions.Trigonometric.NonIntegrable
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Sinc

/-!
# Endpoint expansions of Fourier integrals

For a smooth amplitude `q`, repeated integration by parts expands the Fourier integral
`∫ e^{ixt} q(t) dt` as `x → +∞` in the derivatives of `q` at the endpoints (DLMF §2.3(i),
formulas 2.3.4 to 2.3.6). On a compact interval,

`∫_a^b e^{ixt} q(t) dt ∼ e^{iax} ∑ q^{(s)}(a) (i/x)^{s+1} - e^{ibx} ∑ q^{(s)}(b) (i/x)^{s+1}`,

and on `[a, ∞)` only the sum at `a` remains, provided each `∫ e^{ixt} q^{(s)}(t) dt` converges at
infinity uniformly for all large `x`. On a compact interval the remainder after `n` terms is at
most `x^{-n} ∫ |q^{(n)}|` for every `x > 0`; on `[a, ∞)` the same bound holds for all sufficiently
large `x` when, in addition, `q^{(n)}` is integrable on `(a, ∞)`.

On the half-line the boundary terms at infinity need an argument: convergence of two consecutive
integrals only shows that `e^{ixT} q^{(s)}(T)` has a limit as `T → ∞`. That limit vanishes because
it exists at two different frequencies (`Asymptotics.eq_zero_of_tendsto_cexp_smul`).

## Main results

* `Asymptotics.integral_cexp_smul_eq_sum_add`: the exact formula on a compact interval.
* `Asymptotics.norm_integral_cexp_smul_sub_sum_le`: the remainder bound on a compact interval.
* `Asymptotics.isBigO_integral_cexp_smul_sub_sum`: the expansion 2.3.4.
* `Asymptotics.exists_tendsto_integral_cexp_smul`: existence of the improper integral.
* `Asymptotics.tendsto_cexp_smul_atTop_zero`: vanishing of the boundary terms at infinity.
* `Asymptotics.eq_sum_add_of_tendsto_integral_cexp_smul`: the exact formula on a half-line.
* `Asymptotics.hasAsymptoticExpansion_of_tendsto_integral_cexp_smul`: the expansion 2.3.5.
* `Asymptotics.norm_sub_sum_le_of_tendsto_integral_cexp_smul`: the remainder bound on a half-line.
* `Asymptotics.norm_integral_cexp_smul_le_of_hasDerivAt`,
  `Asymptotics.exists_forall_norm_integral_cexp_smul_le`: decay of `r` with integrable `r'` gives
  convergence at infinity, uniformly for `x ≥ 1`.
* `Asymptotics.hasAsymptoticExpansion_of_tendsto_integral_cexp_smul_sinc`: that criterion is not
  necessary: `q(t) = sin t / t` on `[1, ∞)` has the expansion although `q'` is not integrable
  there (`Asymptotics.not_integrableOn_iteratedDerivWithin_one_sinc`).
* `Asymptotics.exists_tendsto_integral_cexp_smul_of_intervalIntegrable`,
  `Asymptotics.exists_tendsto_integral_cexp_smul_of_isBigO`: existence of the improper integral
  `∫₀^∞ e^{ixt} q(t) dt` for an amplitude integrable at `0`, or `O(t^a)` there with `a > -1`.
* `Asymptotics.tendsto_integral_cexp_smul_sub`: the improper integral over `(b, ∞)` is the one
  over `(0, ∞)` minus the integral over `(0, b)`.
-/

public section

noncomputable section

open Complex Filter Finset MeasureTheory Set intervalIntegral
open scoped ContDiff Real Topology

namespace Asymptotics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

private theorem hasDerivAt_cexp_mul_I (x t : ℝ) :
    HasDerivAt (fun t : ℝ => cexp (((x * t : ℝ) : ℂ) * I))
      (((x : ℂ) * I) * cexp (((x * t : ℝ) : ℂ) * I)) t := by
  have h : HasDerivAt (fun t : ℝ => ((x * t : ℝ) : ℂ) * I) ((x : ℂ) * I) t := by
    simpa using ((hasDerivAt_id t).const_mul x).ofReal_comp.mul_const I
  simpa [mul_comm] using h.cexp

private theorem continuous_cexp_mul_I (x : ℝ) :
    Continuous fun t : ℝ => cexp (((x * t : ℝ) : ℂ) * I) := by
  fun_prop

private theorem norm_I_div_pow {x : ℝ} (hx : 0 < x) (n : ℕ) :
    ‖(I / (x : ℂ)) ^ n‖ = (x ^ n)⁻¹ := by
  simp [abs_of_pos hx]

private theorem norm_integral_cexp_smul_le {f : ℝ → E} {a b x : ℝ} (hab : a ≤ b) :
    ‖∫ t in a..b, cexp (((x * t : ℝ) : ℂ) * I) • f t‖ ≤ ∫ t in a..b, ‖f t‖ := by
  refine (intervalIntegral.norm_integral_le_integral_norm hab).trans_eq ?_
  simp only [norm_smul, norm_exp_ofReal_mul_I, one_mul]

private theorem norm_integral_cexp_smul_le_setIntegral_Ioi {f : ℝ → E} {a x T T' : ℝ}
    (hf : IntegrableOn f (Ioi a)) (hT : a ≤ T) (hTT' : T ≤ T') :
    ‖∫ t in T..T', cexp (((x * t : ℝ) : ℂ) * I) • f t‖ ≤ ∫ t in Ioi a, ‖f t‖ := by
  refine (norm_integral_cexp_smul_le hTT').trans ?_
  rw [integral_of_le hTT']
  exact setIntegral_mono_set hf.norm (Eventually.of_forall fun _ => norm_nonneg _)
    (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi hT)).eventuallySubset

private theorem norm_cexp_smul_sub_cexp_smul_le (x y : ℝ) (u v : E) :
    ‖cexp ((x : ℂ) * I) • u - cexp ((y : ℂ) * I) • v‖ ≤ ‖u‖ + ‖v‖ := by
  refine (norm_sub_le _ _).trans_eq ?_
  simp only [norm_smul, norm_exp_ofReal_mul_I, one_mul]

section Compact

variable [CompleteSpace E]

/-- One integration by parts in a Fourier integral. -/
theorem integral_cexp_smul_eq_of_hasDerivAt {u u' : ℝ → E} {a b x : ℝ} (hab : a ≤ b) (hx : x ≠ 0)
    (hu : ContinuousOn u (Icc a b)) (hu' : ∀ t ∈ Ioo a b, HasDerivAt u (u' t) t)
    (hint : IntervalIntegrable u' volume a b) :
    ∫ t in a..b, cexp (((x * t : ℝ) : ℂ) * I) • u t =
      (I / x) • (cexp (((x * a : ℝ) : ℂ) * I) • u a - cexp (((x * b : ℝ) : ℂ) * I) • u b) +
        (I / x) • ∫ t in a..b, cexp (((x * t : ℝ) : ℂ) * I) • u' t := by
  have hec := continuous_cexp_mul_I x
  have hibp := integral_smul_deriv_eq_deriv_smul_of_hasDerivAt
    (u := fun t => cexp (((x * t : ℝ) : ℂ) * I)) (v := u) hec.continuousOn (uIcc_of_le hab ▸ hu)
    (fun t _ => hasDerivAt_cexp_mul_I x t)
    (fun t ht => hu' t (by rwa [min_eq_left hab, max_eq_right hab] at ht))
    ((hec.const_smul ((x : ℂ) * I)).intervalIntegrable a b) hint
  have hsm : ∫ t in a..b, ((x : ℂ) * I * cexp (((x * t : ℝ) : ℂ) * I)) • u t =
      ((x : ℂ) * I) • ∫ t in a..b, cexp (((x * t : ℝ) : ℂ) * I) • u t := by
    rw [← intervalIntegral.integral_smul]
    simp only [smul_smul]
  rw [hsm] at hibp
  have hk : (I / (x : ℂ)) * ((x : ℂ) * I) = -1 := by
    field_simp [ofReal_ne_zero.2 hx]
    simp
  calc ∫ t in a..b, cexp (((x * t : ℝ) : ℂ) * I) • u t
      = -((I / (x : ℂ)) • (((x : ℂ) * I) • ∫ t in a..b, cexp (((x * t : ℝ) : ℂ) * I) • u t)) := by
        rw [smul_smul, hk, neg_smul, one_smul, neg_neg]
    _ = _ := by
        rw [hibp]
        simp only [smul_sub]
        abel

/-- The exact formula after `n` integrations by parts, for a family `g` of successive
derivatives. -/
theorem integral_cexp_smul_eq_sum_add_of_hasDerivAt {g : ℕ → ℝ → E} {a b x : ℝ} (hab : a ≤ b)
    (hx : x ≠ 0) {n : ℕ} (hcont : ∀ i < n, ContinuousOn (g i) (Icc a b))
    (hderiv : ∀ i < n, ∀ t ∈ Ioo a b, HasDerivAt (g i) (g (i + 1) t) t)
    (hint : IntervalIntegrable (g n) volume a b) :
    ∫ t in a..b, cexp (((x * t : ℝ) : ℂ) * I) • g 0 t =
      ∑ s ∈ range n, (I / x) ^ (s + 1) •
          (cexp (((x * a : ℝ) : ℂ) * I) • g s a - cexp (((x * b : ℝ) : ℂ) * I) • g s b) +
        (I / x) ^ n • ∫ t in a..b, cexp (((x * t : ℝ) : ℂ) * I) • g n t := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : IntervalIntegrable (g n) volume a b :=
      (hcont n (by omega)).intervalIntegrable_of_Icc hab
    rw [ih (fun i hi => hcont i (by omega)) (fun i hi => hderiv i (by omega)) hn,
      integral_cexp_smul_eq_of_hasDerivAt hab hx (hcont n (by omega)) (hderiv n (by omega)) hint,
      Finset.sum_range_succ, smul_add, smul_smul, smul_smul, add_assoc, ← pow_succ]

/-- **DLMF 2.3.4, exact form.** The Fourier integral of a `C^n` function on a compact interval is
its first `n` endpoint terms plus `(i/x)^n ∫ e^{ixt} q^{(n)}(t) dt`. -/
theorem integral_cexp_smul_eq_sum_add {q : ℝ → E} {a b x : ℝ} (hab : a ≤ b) (hx : x ≠ 0) {n : ℕ}
    (hq : ContDiffOn ℝ n q (Icc a b)) :
    ∫ t in a..b, cexp (((x * t : ℝ) : ℂ) * I) • q t =
      ∑ s ∈ range n, (I / x) ^ (s + 1) •
          (cexp (((x * a : ℝ) : ℂ) * I) • iteratedDerivWithin s q (Icc a b) a -
            cexp (((x * b : ℝ) : ℂ) * I) • iteratedDerivWithin s q (Icc a b) b) +
        (I / x) ^ n • ∫ t in a..b, cexp (((x * t : ℝ) : ℂ) * I) •
          iteratedDerivWithin n q (Icc a b) t := by
  rcases hab.eq_or_lt with rfl | hab
  · simp
  have hU := uniqueDiffOn_Icc hab
  have h := integral_cexp_smul_eq_sum_add_of_hasDerivAt (g := fun i => iteratedDerivWithin i q
    (Icc a b)) hab.le hx (n := n)
    (fun i hi => hq.continuousOn_iteratedDerivWithin (by exact_mod_cast hi.le) hU)
    (fun i hi t ht => hq.hasDerivAt_iteratedDerivWithin (by exact_mod_cast hi)
      (Icc_mem_nhds ht.1 ht.2))
    ((hq.continuousOn_iteratedDerivWithin le_rfl hU).intervalIntegrable_of_Icc hab.le)
  simpa only [iteratedDerivWithin_zero] using h

/-- **DLMF 2.3.6.** The remainder after `n` endpoint terms on a compact interval is at most
`x^{-n} ∫_a^b |q^{(n)}|`. -/
theorem norm_integral_cexp_smul_sub_sum_le {q : ℝ → E} {a b x : ℝ} (hab : a ≤ b) (hx : 0 < x)
    {n : ℕ} (hq : ContDiffOn ℝ n q (Icc a b)) :
    ‖(∫ t in a..b, cexp (((x * t : ℝ) : ℂ) * I) • q t) -
        ∑ s ∈ range n, (I / x) ^ (s + 1) •
          (cexp (((x * a : ℝ) : ℂ) * I) • iteratedDerivWithin s q (Icc a b) a -
            cexp (((x * b : ℝ) : ℂ) * I) • iteratedDerivWithin s q (Icc a b) b)‖ ≤
      (x ^ n)⁻¹ * ∫ t in a..b, ‖iteratedDerivWithin n q (Icc a b) t‖ := by
  rw [integral_cexp_smul_eq_sum_add hab hx.ne' hq, add_sub_cancel_left, norm_smul,
    norm_I_div_pow hx]
  exact mul_le_mul_of_nonneg_left (norm_integral_cexp_smul_le hab) (by positivity)

/-- **DLMF 2.3.4.** For `q` of class `C^{N+1}` on `[a, b]`, the remainder after the first `N`
terms of the endpoint expansion of `∫_a^b e^{ixt} q(t) dt` is `O(x^{-N-1})` as `x → +∞`. -/
theorem isBigO_integral_cexp_smul_sub_sum {q : ℝ → E} {a b : ℝ} (hab : a ≤ b) {N : ℕ}
    (hq : ContDiffOn ℝ (N + 1 : ℕ) q (Icc a b)) :
    (fun x : ℝ => (∫ t in a..b, cexp (((x * t : ℝ) : ℂ) * I) • q t) -
        ∑ s ∈ range N, (I / x) ^ (s + 1) •
          (cexp (((x * a : ℝ) : ℂ) * I) • iteratedDerivWithin s q (Icc a b) a -
            cexp (((x * b : ℝ) : ℂ) * I) • iteratedDerivWithin s q (Icc a b) b))
      =O[atTop] fun x : ℝ => x⁻¹ ^ (N + 1) := by
  refine IsBigO.of_bound (‖iteratedDerivWithin N q (Icc a b) a‖ +
    ‖iteratedDerivWithin N q (Icc a b) b‖ +
      ∫ t in a..b, ‖iteratedDerivWithin (N + 1) q (Icc a b) t‖) ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  have hbound := norm_integral_cexp_smul_sub_sum_le hab hx hq
  rw [Finset.sum_range_succ, ← sub_sub] at hbound
  have hterm : ‖(I / (x : ℂ)) ^ (N + 1) •
      (cexp (((x * a : ℝ) : ℂ) * I) • iteratedDerivWithin N q (Icc a b) a -
        cexp (((x * b : ℝ) : ℂ) * I) • iteratedDerivWithin N q (Icc a b) b)‖ ≤
      (x ^ (N + 1))⁻¹ * (‖iteratedDerivWithin N q (Icc a b) a‖ +
        ‖iteratedDerivWithin N q (Icc a b) b‖) := by
    rw [norm_smul, norm_I_div_pow hx]
    exact mul_le_mul_of_nonneg_left (norm_cexp_smul_sub_cexp_smul_le _ _ _ _) (by positivity)
  have hpos : ‖x⁻¹ ^ (N + 1)‖ = (x ^ (N + 1))⁻¹ := by
    rw [norm_pow, norm_inv, Real.norm_of_nonneg hx.le, inv_pow]
  rw [hpos, add_mul, add_mul]
  refine (norm_le_norm_add_norm_sub' _ ((I / (x : ℂ)) ^ (N + 1) •
    (cexp (((x * a : ℝ) : ℂ) * I) • iteratedDerivWithin N q (Icc a b) a -
      cexp (((x * b : ℝ) : ℂ) * I) • iteratedDerivWithin N q (Icc a b) b))).trans ?_
  linarith

end Compact

/-- If `e^{ixT} u(T)` and `e^{iyT} u(T)` both converge as `T → ∞` at two different frequencies,
then the limits vanish. -/
theorem eq_zero_of_tendsto_cexp_smul {u : ℝ → E} {x y : ℝ} (hxy : x ≠ y) {L L' : E}
    (hx : Tendsto (fun T : ℝ => cexp (((x * T : ℝ) : ℂ) * I) • u T) atTop (𝓝 L))
    (hy : Tendsto (fun T : ℝ => cexp (((y * T : ℝ) : ℂ) * I) • u T) atTop (𝓝 L')) : L = 0 := by
  have hθ : x - y ≠ 0 := sub_ne_zero.2 hxy
  set δ : ℝ := π / (x - y) with hδ
  have hshift : Tendsto (fun T : ℝ => T + δ) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_id
  have hsum := hx.add (hx.comp hshift)
  have hdiff : Tendsto (fun T : ℝ => cexp (((y * T : ℝ) : ℂ) * I) • u T -
      cexp (((y * (T + δ) : ℝ) : ℂ) * I) • u (T + δ)) atTop (𝓝 0) := by
    simpa using hy.sub (hy.comp hshift)
  have key : ∀ T : ℝ, cexp (((x * T : ℝ) : ℂ) * I) • u T +
      cexp (((x * (T + δ) : ℝ) : ℂ) * I) • u (T + δ) =
      cexp ((((x - y) * T : ℝ) : ℂ) * I) • (cexp (((y * T : ℝ) : ℂ) * I) • u T -
        cexp (((y * (T + δ) : ℝ) : ℂ) * I) • u (T + δ)) := fun T => by
    have h1 : cexp (((x * T : ℝ) : ℂ) * I) =
        cexp ((((x - y) * T : ℝ) : ℂ) * I) * cexp (((y * T : ℝ) : ℂ) * I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    have h2 : cexp (((x * (T + δ) : ℝ) : ℂ) * I) =
        -(cexp ((((x - y) * T : ℝ) : ℂ) * I) * cexp (((y * (T + δ) : ℝ) : ℂ) * I)) := by
      have hδ' : (x - y) * δ = π := by rw [hδ]; field_simp
      have : ((x * (T + δ) : ℝ) : ℂ) * I =
          (((x - y) * T : ℝ) : ℂ) * I + ((y * (T + δ) : ℝ) : ℂ) * I + (π : ℂ) * I := by
        rw [← hδ']
        push_cast
        ring
      rw [this, Complex.exp_add, Complex.exp_add, Complex.exp_pi_mul_I]
      ring
    rw [h1, h2]
    simp only [smul_sub, smul_smul, neg_smul]
    abel
  have hzero : Tendsto (fun T : ℝ => cexp (((x * T : ℝ) : ℂ) * I) • u T +
      cexp (((x * (T + δ) : ℝ) : ℂ) * I) • u (T + δ)) atTop (𝓝 0) := by
    have hd0 : Tendsto (fun T : ℝ => ‖cexp (((y * T : ℝ) : ℂ) * I) • u T -
        cexp (((y * (T + δ) : ℝ) : ℂ) * I) • u (T + δ)‖) atTop (𝓝 0) := by
      simpa using hdiff.norm
    refine squeeze_zero_norm (fun T => le_of_eq ?_) hd0
    rw [key, norm_smul, norm_exp_ofReal_mul_I, one_mul]
  have h2L : (2 : ℂ) • L = 0 := by
    rw [two_smul]
    exact tendsto_nhds_unique hsum hzero
  exact (smul_eq_zero.1 h2L).resolve_left two_ne_zero

section HalfLine

variable [CompleteSpace E]

omit [CompleteSpace E] in
private theorem intervalIntegrable_cexp_smul {r : ℝ → E} {a : ℝ} (hr : ContinuousOn r (Ici a))
    (x : ℝ) {T T' : ℝ} (hT : a ≤ T) (hT' : a ≤ T') :
    IntervalIntegrable (fun t => cexp (((x * t : ℝ) : ℂ) * I) • r t) volume T T' := by
  refine ContinuousOn.intervalIntegrable ?_
  refine (continuous_cexp_mul_I x).continuousOn.smul (hr.mono fun t ht => ?_)
  exact le_trans (le_min hT hT') ht.1

/-- A Fourier integral whose tails are uniformly small converges at infinity. -/
theorem exists_tendsto_integral_cexp_smul {r : ℝ → E} {a x : ℝ} (hr : ContinuousOn r (Ici a))
    (hu : ∀ ε > 0, ∃ c : ℝ, ∀ T ≥ c, ∀ T' ≥ T,
      ‖∫ t in T..T', cexp (((x * t : ℝ) : ℂ) * I) • r t‖ ≤ ε) :
    ∃ L, Tendsto (fun T : ℝ => ∫ t in a..T, cexp (((x * t : ℝ) : ℂ) * I) • r t) atTop (𝓝 L) := by
  refine cauchySeq_tendsto_of_complete (Metric.cauchySeq_iff'.2 fun ε hε => ?_)
  obtain ⟨c, hc⟩ := hu (ε / 2) (half_pos hε)
  refine ⟨max c a, fun T hT => ?_⟩
  have hT' : max c a ≤ T := hT
  rw [dist_eq_norm, integral_interval_sub_left
    (intervalIntegrable_cexp_smul hr x le_rfl ((le_max_right c a).trans hT'))
    (intervalIntegrable_cexp_smul hr x le_rfl (le_max_right c a))]
  exact (hc _ (le_max_left c a) T hT').trans_lt (half_lt_self hε)

omit [CompleteSpace E] in
private theorem exists_forall_norm_le_of_tendsto {r : ℝ → E} {a x₀ : ℝ}
    (hr : ContinuousOn r (Ici a))
    (hu : ∀ ε > 0, ∃ c : ℝ, ∀ x ≥ x₀, ∀ T ≥ c, ∀ T' ≥ T,
      ‖∫ t in T..T', cexp (((x * t : ℝ) : ℂ) * I) • r t‖ ≤ ε) :
    ∃ M : ℝ, ∀ x ≥ x₀, ∀ L : E,
      Tendsto (fun T : ℝ => ∫ t in a..T, cexp (((x * t : ℝ) : ℂ) * I) • r t) atTop (𝓝 L) →
        ‖L‖ ≤ M := by
  obtain ⟨c, hc⟩ := hu 1 one_pos
  set d := max c a
  have had : a ≤ d := le_max_right c a
  refine ⟨(∫ t in a..d, ‖r t‖) + 1, fun x hx L hL => ?_⟩
  refine le_of_tendsto hL.norm ?_
  filter_upwards [eventually_ge_atTop d] with T hT
  rw [← integral_add_adjacent_intervals (intervalIntegrable_cexp_smul hr x le_rfl had)
    (intervalIntegrable_cexp_smul hr x had (had.trans hT))]
  exact (norm_add_le _ _).trans
    (add_le_add (norm_integral_cexp_smul_le had) (hc x hx d (le_max_left c a) T hT))

/-- If the Fourier integrals of `g₀` and of its derivative `g₁` converge at infinity at two
different nonzero frequencies, the boundary term `e^{ixT} g₀(T)` tends to `0`. -/
theorem tendsto_cexp_smul_atTop_zero {g₀ g₁ : ℝ → E} {a x y : ℝ}
    (h₀ : ContinuousOn g₀ (Ici a)) (h₁ : ContinuousOn g₁ (Ici a))
    (hd : ∀ t ∈ Ioi a, HasDerivAt g₀ (g₁ t) t) (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y)
    {A₀ A₁ B₀ B₁ : E}
    (hA₀ : Tendsto (fun T : ℝ => ∫ t in a..T, cexp (((x * t : ℝ) : ℂ) * I) • g₀ t) atTop (𝓝 A₀))
    (hA₁ : Tendsto (fun T : ℝ => ∫ t in a..T, cexp (((x * t : ℝ) : ℂ) * I) • g₁ t) atTop (𝓝 A₁))
    (hB₀ : Tendsto (fun T : ℝ => ∫ t in a..T, cexp (((y * t : ℝ) : ℂ) * I) • g₀ t) atTop (𝓝 B₀))
    (hB₁ : Tendsto (fun T : ℝ => ∫ t in a..T, cexp (((y * t : ℝ) : ℂ) * I) • g₁ t) atTop (𝓝 B₁)) :
    Tendsto (fun T : ℝ => cexp (((x * T : ℝ) : ℂ) * I) • g₀ T) atTop (𝓝 0) := by
  have hlim : ∀ {z : ℝ} {C₀ C₁ : E}, z ≠ 0 →
      Tendsto (fun T : ℝ => ∫ t in a..T, cexp (((z * t : ℝ) : ℂ) * I) • g₀ t) atTop (𝓝 C₀) →
      Tendsto (fun T : ℝ => ∫ t in a..T, cexp (((z * t : ℝ) : ℂ) * I) • g₁ t) atTop (𝓝 C₁) →
      ∃ L, Tendsto (fun T : ℝ => cexp (((z * T : ℝ) : ℂ) * I) • g₀ T) atTop (𝓝 L) := by
    intro z C₀ C₁ hz hC₀ hC₁
    have hzC : I / (z : ℂ) ≠ 0 := div_ne_zero I_ne_zero (ofReal_ne_zero.2 hz)
    refine ⟨cexp (((z * a : ℝ) : ℂ) * I) • g₀ a + C₁ - (I / (z : ℂ))⁻¹ • C₀, ?_⟩
    refine (((tendsto_const_nhds.add hC₁).sub (hC₀.const_smul _))).congr' ?_
    filter_upwards [eventually_ge_atTop a] with T hT
    have hibp := integral_cexp_smul_eq_of_hasDerivAt hT hz (h₀.mono Icc_subset_Ici_self)
      (fun t ht => hd t ht.1)
      (h₁.mono (uIcc_of_le hT ▸ Icc_subset_Ici_self)).intervalIntegrable
    rw [hibp, smul_add, smul_smul, smul_smul, inv_mul_cancel₀ hzC, one_smul, one_smul]
    abel
  obtain ⟨L, hL⟩ := hlim hx hA₀ hA₁
  obtain ⟨L', hL'⟩ := hlim hy hB₀ hB₁
  rwa [eq_zero_of_tendsto_cexp_smul hxy hL hL'] at hL

/-- The exact formula on the half-line, given the convergence of the integrals and the vanishing
of the boundary terms at infinity. -/
theorem eq_sum_add_of_tendsto_integral_cexp_smul {g : ℕ → ℝ → E} {a x : ℝ} (hx : x ≠ 0) {n : ℕ}
    (hcont : ∀ i ≤ n, ContinuousOn (g i) (Ici a))
    (hderiv : ∀ i < n, ∀ t ∈ Ioi a, HasDerivAt (g i) (g (i + 1) t) t) {F G : E}
    (hF : Tendsto (fun T : ℝ => ∫ t in a..T, cexp (((x * t : ℝ) : ℂ) * I) • g 0 t) atTop (𝓝 F))
    (hG : Tendsto (fun T : ℝ => ∫ t in a..T, cexp (((x * t : ℝ) : ℂ) * I) • g n t) atTop (𝓝 G))
    (hbdry : ∀ i < n, Tendsto (fun T : ℝ => cexp (((x * T : ℝ) : ℂ) * I) • g i T) atTop (𝓝 0)) :
    F = ∑ s ∈ range n, (I / x) ^ (s + 1) • (cexp (((x * a : ℝ) : ℂ) * I) • g s a) +
      (I / x) ^ n • G := by
  have hsum : Tendsto (fun T : ℝ => ∑ s ∈ range n, (I / x) ^ (s + 1) •
      (cexp (((x * a : ℝ) : ℂ) * I) • g s a - cexp (((x * T : ℝ) : ℂ) * I) • g s T))
      atTop (𝓝 (∑ s ∈ range n, (I / x) ^ (s + 1) • (cexp (((x * a : ℝ) : ℂ) * I) • g s a))) := by
    refine tendsto_finsetSum _ fun s hs => ?_
    simpa using (tendsto_const_nhds.sub (hbdry s (Finset.mem_range.1 hs))).const_smul
      ((I / (x : ℂ)) ^ (s + 1))
  refine tendsto_nhds_unique hF ((hsum.add (hG.const_smul _)).congr' ?_)
  filter_upwards [eventually_ge_atTop a] with T hT
  exact (integral_cexp_smul_eq_sum_add_of_hasDerivAt hT hx
    (fun i hi => (hcont i hi.le).mono Icc_subset_Ici_self)
    (fun i hi t ht => hderiv i hi t ht.1)
    ((hcont n le_rfl).mono (uIcc_of_le hT ▸ Icc_subset_Ici_self)).intervalIntegrable).symm

/-- For all large `x`, the improper integral of `q^{(n)}` exists and the exact formula holds. -/
private theorem eventually_exists_tendsto_and_eq_sum {q : ℝ → E} {a : ℝ} {n : ℕ}
    (hq : ContDiffOn ℝ n q (Ici a))
    (hunif : ∀ s ≤ n, ∃ x₀ : ℝ, ∀ ε > 0, ∃ c : ℝ, ∀ x ≥ x₀, ∀ T ≥ c, ∀ T' ≥ T,
      ‖∫ t in T..T', cexp (((x * t : ℝ) : ℂ) * I) • iteratedDerivWithin s q (Ici a) t‖ ≤ ε) :
    ∀ᶠ x : ℝ in atTop, ∃ G : E,
      Tendsto (fun T : ℝ => ∫ t in a..T, cexp (((x * t : ℝ) : ℂ) * I) •
        iteratedDerivWithin n q (Ici a) t) atTop (𝓝 G) ∧
      ∀ F : E, Tendsto (fun T : ℝ => ∫ t in a..T, cexp (((x * t : ℝ) : ℂ) * I) • q t) atTop (𝓝 F) →
        F = ∑ s ∈ range n, (cexp (((x * a : ℝ) : ℂ) * I) * (I / x) ^ (s + 1)) •
          iteratedDerivWithin s q (Ici a) a + (I / x) ^ n • G := by
  have hU : UniqueDiffOn ℝ (Ici a) := uniqueDiffOn_Ici a
  have hc : ∀ i ≤ n, ContinuousOn (iteratedDerivWithin i q (Ici a)) (Ici a) := fun i hi =>
    hq.continuousOn_iteratedDerivWithin (by exact_mod_cast hi) hU
  have hd : ∀ i < n, ∀ t ∈ Ioi a, HasDerivAt (iteratedDerivWithin i q (Ici a))
      (iteratedDerivWithin (i + 1) q (Ici a) t) t := fun i hi t ht =>
    hq.hasDerivAt_iteratedDerivWithin (by exact_mod_cast hi) (Ici_mem_nhds ht)
  choose! x₀ hx₀ using hunif
  have hlim : ∀ i ≤ n, ∀ z ≥ x₀ i, ∃ L, Tendsto (fun T : ℝ => ∫ t in a..T,
      cexp (((z * t : ℝ) : ℂ) * I) • iteratedDerivWithin i q (Ici a) t) atTop (𝓝 L) :=
    fun i hi z hz => exists_tendsto_integral_cexp_smul (hc i hi) fun ε hε => by
      obtain ⟨c, hc'⟩ := hx₀ i hi ε hε
      exact ⟨c, hc' z hz⟩
  filter_upwards [eventually_gt_atTop 0,
    (eventually_all_finset (Finset.range (n + 1))).2 fun i _ => eventually_ge_atTop (x₀ i)]
    with x hx hxs
  have hxi : ∀ i ≤ n, x ≥ x₀ i := fun i hi => hxs i (Finset.mem_range.2 (by omega))
  obtain ⟨G, hG⟩ := hlim n le_rfl x (hxi n le_rfl)
  refine ⟨G, hG, fun F hF => ?_⟩
  have hbdry : ∀ i < n, Tendsto (fun T : ℝ => cexp (((x * T : ℝ) : ℂ) * I) •
      iteratedDerivWithin i q (Ici a) T) atTop (𝓝 0) := fun i hi => by
    obtain ⟨A₀, hA₀⟩ := hlim i hi.le x (hxi i hi.le)
    obtain ⟨A₁, hA₁⟩ := hlim (i + 1) hi x (hxi _ hi)
    obtain ⟨B₀, hB₀⟩ := hlim i hi.le (x + 1) (by linarith [hxi i hi.le])
    obtain ⟨B₁, hB₁⟩ := hlim (i + 1) hi (x + 1) (by linarith [hxi (i + 1) hi])
    exact tendsto_cexp_smul_atTop_zero (hc i hi.le) (hc _ hi) (hd i hi) hx.ne' (by positivity)
      (by simp) hA₀ hA₁ hB₀ hB₁
  have h := eq_sum_add_of_tendsto_integral_cexp_smul
    (g := fun i => iteratedDerivWithin i q (Ici a)) hx.ne' (n := n) hc hd (by simpa using hF) hG
    hbdry
  rw [h]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [smul_smul, mul_comm]

/-- The scale `e^{iax} (i/x)^{s+1}` of the endpoint expansion at `a` is an asymptotic scale. -/
theorem isAsymptoticScale_cexp_mul_I_div_pow (a : ℝ) :
    IsAsymptoticScale atTop
      (fun (s : ℕ) (x : ℝ) => cexp (((x * a : ℝ) : ℂ) * I) * (I / (x : ℂ)) ^ (s + 1)) := by
  have h0 : Tendsto (fun x : ℝ => I / (x : ℂ)) atTop (𝓝 0) := by
    have : Tendsto (fun x : ℝ => ((x⁻¹ : ℝ) : ℂ)) atTop (𝓝 ((0 : ℝ) : ℂ)) :=
      (continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_zero
    simpa [div_eq_mul_inv] using this.const_mul I
  refine IsAsymptoticScale.of_isLittleO fun s => ?_
  exact (isBigO_refl (fun x : ℝ => cexp (((x * a : ℝ) : ℂ) * I)) atTop).mul_isLittleO
    ((isAsymptoticScale_pow h0).isLittleO (s + 1))

/-- **DLMF 2.3.5.** If `q` is smooth on `[a, ∞)` and each `∫ e^{ixt} q^{(s)}(t) dt` converges at
infinity uniformly for all large `x`, the improper integral `F x` of `e^{ixt} q(t)` over
`[a, ∞)`, which exists for large `x` by `exists_tendsto_integral_cexp_smul`, has the expansion
`e^{iax} ∑ q^{(s)}(a) (i/x)^{s+1}` as `x → +∞`. -/
theorem hasAsymptoticExpansion_of_tendsto_integral_cexp_smul {q : ℝ → E} {a : ℝ} {F : ℝ → E}
    (hq : ContDiffOn ℝ ∞ q (Ici a))
    (hunif : ∀ s : ℕ, ∃ x₀ : ℝ, ∀ ε > 0, ∃ c : ℝ, ∀ x ≥ x₀, ∀ T ≥ c, ∀ T' ≥ T,
      ‖∫ t in T..T', cexp (((x * t : ℝ) : ℂ) * I) • iteratedDerivWithin s q (Ici a) t‖ ≤ ε)
    (hF : ∀ᶠ x : ℝ in atTop,
      Tendsto (fun T : ℝ => ∫ t in a..T, cexp (((x * t : ℝ) : ℂ) * I) • q t) atTop (𝓝 (F x))) :
    HasAsymptoticExpansion atTop
      (fun (s : ℕ) (x : ℝ) => cexp (((x * a : ℝ) : ℂ) * I) * (I / (x : ℂ)) ^ (s + 1))
      (fun s => iteratedDerivWithin s q (Ici a) a) F := by
  refine HasAsymptoticExpansion.of_isBigO fun N => ?_
  have hU : UniqueDiffOn ℝ (Ici a) := uniqueDiffOn_Ici a
  obtain ⟨x₁, hx₁⟩ := hunif (N + 1)
  obtain ⟨M, hM⟩ := exists_forall_norm_le_of_tendsto (x₀ := x₁) (a := a)
    (hq.continuousOn_iteratedDerivWithin (by exact_mod_cast le_top) hU) hx₁
  refine IsBigO.of_bound (‖iteratedDerivWithin N q (Ici a) a‖ + |M|) ?_
  filter_upwards [hF, eventually_exists_tendsto_and_eq_sum (n := N + 1)
    (hq.of_le (by exact_mod_cast le_top)) (fun s _ => hunif s),
    eventually_gt_atTop 0, eventually_ge_atTop x₁] with x hFx ⟨G, hG, hEq⟩ hx hxx₁
  rw [hEq _ hFx, Finset.sum_range_succ, add_assoc, add_sub_cancel_left]
  have hnormφ : ‖cexp (((x * a : ℝ) : ℂ) * I) * (I / (x : ℂ)) ^ (N + 1)‖ = (x ^ (N + 1))⁻¹ := by
    rw [norm_mul, norm_exp_ofReal_mul_I, one_mul, norm_I_div_pow hx]
  rw [hnormφ]
  calc _ ≤ ‖(cexp (((x * a : ℝ) : ℂ) * I) * (I / (x : ℂ)) ^ (N + 1)) •
        iteratedDerivWithin N q (Ici a) a‖ + ‖(I / (x : ℂ)) ^ (N + 1) • G‖ := norm_add_le _ _
    _ = (x ^ (N + 1))⁻¹ * ‖iteratedDerivWithin N q (Ici a) a‖ + (x ^ (N + 1))⁻¹ * ‖G‖ := by
      rw [norm_smul, norm_smul, hnormφ, norm_I_div_pow hx]
    _ ≤ (‖iteratedDerivWithin N q (Ici a) a‖ + |M|) * (x ^ (N + 1))⁻¹ := by
      have hG' : ‖G‖ ≤ |M| := (hM x hxx₁ G hG).trans (le_abs_self M)
      have : 0 ≤ (x ^ (N + 1))⁻¹ := by positivity
      nlinarith

/-- **DLMF 2.3.6 on a half-line.** When `q^{(n)}` is integrable on `(a, ∞)`, for all large `x` the
remainder after `n` terms of the expansion of the improper integral is at most
`x^{-n} ∫_a^∞ |q^{(n)}|`. -/
theorem norm_sub_sum_le_of_tendsto_integral_cexp_smul {q : ℝ → E} {a : ℝ} {n : ℕ}
    (hq : ContDiffOn ℝ n q (Ici a))
    (hunif : ∀ s ≤ n, ∃ x₀ : ℝ, ∀ ε > 0, ∃ c : ℝ, ∀ x ≥ x₀, ∀ T ≥ c, ∀ T' ≥ T,
      ‖∫ t in T..T', cexp (((x * t : ℝ) : ℂ) * I) • iteratedDerivWithin s q (Ici a) t‖ ≤ ε)
    (hn : IntegrableOn (iteratedDerivWithin n q (Ici a)) (Ioi a)) :
    ∀ᶠ x : ℝ in atTop, ∀ F : E,
      Tendsto (fun T : ℝ => ∫ t in a..T, cexp (((x * t : ℝ) : ℂ) * I) • q t) atTop (𝓝 F) →
      ‖F - ∑ s ∈ range n, (cexp (((x * a : ℝ) : ℂ) * I) * (I / x) ^ (s + 1)) •
          iteratedDerivWithin s q (Ici a) a‖ ≤
        (x ^ n)⁻¹ * ∫ t in Ioi a, ‖iteratedDerivWithin n q (Ici a) t‖ := by
  filter_upwards [eventually_exists_tendsto_and_eq_sum hq hunif, eventually_gt_atTop 0]
    with x ⟨G, hG, hEq⟩ hx F hF
  rw [hEq F hF, add_sub_cancel_left, norm_smul, norm_I_div_pow hx]
  refine mul_le_mul_of_nonneg_left (le_of_tendsto hG.norm ?_) (by positivity)
  filter_upwards [eventually_ge_atTop a] with T hT
  exact norm_integral_cexp_smul_le_setIntegral_Ioi hn le_rfl hT

/-- One integration by parts bounds a Fourier integral over `[T, T']` by the values of `r` at the
ends and the tail of `∫ |r'|`. -/
theorem norm_integral_cexp_smul_le_of_hasDerivAt {r r' : ℝ → E} {a x T T' : ℝ}
    (hr : ContinuousOn r (Ici a)) (hr' : ∀ t ∈ Ioi a, HasDerivAt r (r' t) t)
    (hint : IntegrableOn r' (Ioi a)) (hx : 0 < x) (hT : a ≤ T) (hTT' : T ≤ T') :
    ‖∫ t in T..T', cexp (((x * t : ℝ) : ℂ) * I) • r t‖ ≤
      x⁻¹ * (‖r T‖ + ‖r T'‖ + ∫ t in Ioi T, ‖r' t‖) := by
  have hsub : Ioi T ⊆ Ioi a := Ioi_subset_Ioi hT
  have hint' : IntervalIntegrable r' volume T T' :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hTT').2
      (hint.mono_set (Ioc_subset_Ioi_self.trans hsub))
  rw [integral_cexp_smul_eq_of_hasDerivAt hTT' hx.ne'
    (hr.mono fun t ht => hT.trans ht.1) (fun t ht => hr' t (lt_of_le_of_lt hT ht.1)) hint',
    ← smul_add, norm_smul]
  have hnorm : ‖I / (x : ℂ)‖ = x⁻¹ := by simpa using norm_I_div_pow hx 1
  rw [hnorm]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact (norm_add_le _ _).trans (add_le_add (norm_cexp_smul_sub_cexp_smul_le _ _ _ _)
    (norm_integral_cexp_smul_le_setIntegral_Ioi (hint.mono_set hsub) le_rfl hTT'))

/-- If `r` tends to `0` at infinity and `r'` is integrable on `(a, ∞)`, then
`∫ e^{ixt} r(t) dt` converges at infinity uniformly for `x ≥ 1`. -/
theorem exists_forall_norm_integral_cexp_smul_le {r r' : ℝ → E} {a : ℝ}
    (hr' : ∀ t ∈ Ioi a, HasDerivAt r (r' t) t) (h0 : Tendsto r atTop (𝓝 0))
    (hint : IntegrableOn r' (Ioi a)) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, ∀ x ≥ (1 : ℝ), ∀ T ≥ c, ∀ T' ≥ T,
      ‖∫ t in T..T', cexp (((x * t : ℝ) : ℂ) * I) • r t‖ ≤ ε := by
  have htail : Tendsto (fun T : ℝ => ∫ t in Ioi T, ‖r' t‖) atTop (𝓝 0) :=
    tendsto_integral_Ioi_zero tendsto_id
  have hnorm : Tendsto (fun T : ℝ => ‖r T‖) atTop (𝓝 0) := by simpa using h0.norm
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨c₁, hc₁⟩ := eventually_atTop.1 (hnorm.eventually (gt_mem_nhds hε3))
  obtain ⟨c₂, hc₂⟩ := eventually_atTop.1 (htail.eventually (gt_mem_nhds hε3))
  refine ⟨max (a + 1) (max c₁ c₂), fun x hx T hT T' hT' => ?_⟩
  have hTa : a + 1 ≤ T := (le_max_left _ _).trans hT
  have hT₁ : c₁ ≤ T := ((le_max_left _ _).trans (le_max_right _ _)).trans hT
  have hT₂ : c₂ ≤ T := ((le_max_right _ _).trans (le_max_right _ _)).trans hT
  have hsub : Ioi (a + 1) ⊆ Ioi a := Ioi_subset_Ioi (by linarith)
  have hbound := norm_integral_cexp_smul_le_of_hasDerivAt (a := a + 1)
    (fun t ht => (hr' t (Set.mem_Ioi.2 (by have := mem_Ici.1 ht; linarith))).continuousAt
      |>.continuousWithinAt)
    (fun t ht => hr' t (hsub ht)) (hint.mono_set hsub) (by linarith : 0 < x) hTa hT'
  have h1 := hc₁ T hT₁
  have h2 := hc₁ T' (hT₁.trans hT')
  have h3 := hc₂ T hT₂
  have hsum : 0 ≤ ‖r T‖ + ‖r T'‖ + ∫ t in Ioi T, ‖r' t‖ :=
    add_nonneg (by positivity) (integral_nonneg fun _ => norm_nonneg _)
  have hinv : x⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hx
  nlinarith

section SincCheck

/-- The oscillating inverse powers `e^{iνt} t^{-k}`. -/
private def oscPow (ν : ℝ) (k : ℕ) (t : ℝ) : ℂ :=
  cexp (((ν * t : ℝ) : ℂ) * I) * ((t⁻¹ ^ k : ℝ) : ℂ)

/-- The span of the oscillating inverse powers of frequency `±1` and order at least `1`. It
contains `sinc` on `[1, ∞)` and is stable under differentiation. -/
private def oscSpan : Submodule ℂ (ℝ → ℂ) :=
  Submodule.span ℂ {f | ∃ ν : ℝ, (ν = 1 ∨ ν = -1) ∧ ∃ k : ℕ, 1 ≤ k ∧ f = oscPow ν k}

/-- Tails of the Fourier integral are small, uniformly for `x ≥ 2`. -/
private def TailSmall (f : ℝ → ℂ) : Prop :=
  ∀ ε > 0, ∃ c ≥ (1 : ℝ), ∀ x ≥ (2 : ℝ), ∀ T ≥ c, ∀ T' ≥ T,
    ‖∫ t in T..T', cexp (((x * t : ℝ) : ℂ) * I) • f t‖ ≤ ε

private theorem oscPow_mem {ν : ℝ} (hν : ν = 1 ∨ ν = -1) {k : ℕ} (hk : 1 ≤ k) :
    oscPow ν k ∈ oscSpan :=
  Submodule.subset_span ⟨ν, hν, k, hk, rfl⟩

private theorem hasDerivAt_oscPow (ν : ℝ) (k : ℕ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (oscPow ν k)
      (((ν : ℂ) * I) • oscPow ν k t + (-(k : ℂ)) • oscPow ν (k + 1) t) t := by
  have h := (hasDerivAt_cexp_mul_I ν t).mul (TauCeti.hasDerivAt_inv_pow k ht).ofReal_comp
  refine h.congr_deriv ?_
  simp only [oscPow, smul_eq_mul]
  push_cast
  ring

private theorem continuousOn_oscPow (ν : ℝ) (k : ℕ) : ContinuousOn (oscPow ν k) (Ici 1) :=
  fun t ht => (hasDerivAt_oscPow ν k (by have := mem_Ici.1 ht; positivity)).continuousAt
    |>.continuousWithinAt

private theorem tailSmall_oscPow {ν : ℝ} (hν : ν = 1 ∨ ν = -1) {k : ℕ} (hk : 1 ≤ k) :
    TailSmall (oscPow ν k) := by
  intro ε hε
  have h0 : Tendsto (fun t : ℝ => ((t⁻¹ ^ k : ℝ) : ℂ)) atTop (𝓝 0) := by
    simpa [Function.comp_def, zero_pow (by omega : k ≠ 0)] using
      (continuous_ofReal.tendsto _).comp ((tendsto_inv_atTop_zero (𝕜 := ℝ)).pow k)
  obtain ⟨c, hc⟩ := exists_forall_norm_integral_cexp_smul_le (a := 1)
    (r := fun t : ℝ => ((t⁻¹ ^ k : ℝ) : ℂ))
    (r' := fun t : ℝ => (((-(k : ℝ) * t⁻¹ ^ (k + 1) : ℝ)) : ℂ))
    (fun t ht => (TauCeti.hasDerivAt_inv_pow k (one_pos.trans ht).ne').ofReal_comp)
    h0 (((TauCeti.integrableOn_Ioi_inv_pow (by omega) one_pos).const_mul _).ofReal) hε
  refine ⟨max c 1, le_max_right _ _, fun x hx T hT T' hT' => ?_⟩
  have hfreq : x + ν ≥ 1 := by rcases hν with rfl | rfl <;> linarith
  refine le_of_eq_of_le ?_ (hc (x + ν) hfreq T ((le_max_left _ _).trans hT) T' hT')
  congr 1
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [oscPow, smul_eq_mul, ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

private theorem continuousOn_of_mem_oscSpan {f : ℝ → ℂ} (hf : f ∈ oscSpan) :
    ContinuousOn f (Ici 1) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨ν, -, k, -, rfl⟩ := hf
    exact continuousOn_oscPow ν k
  | zero => exact continuousOn_const
  | add f g _ _ hf hg => exact hf.add hg
  | smul κ f _ hf => exact hf.const_smul κ

private theorem tailSmall_of_mem_oscSpan {f : ℝ → ℂ} (hf : f ∈ oscSpan) : TailSmall f := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨ν, hν, k, hk, rfl⟩ := hf
    exact tailSmall_oscPow hν hk
  | zero => exact fun ε hε => ⟨1, le_rfl, fun x _ T _ T' _ => by simpa using hε.le⟩
  | add f g hf' hg' hf hg =>
    intro ε hε
    obtain ⟨c₁, hc₁, h₁⟩ := hf (ε / 2) (half_pos hε)
    obtain ⟨c₂, -, h₂⟩ := hg (ε / 2) (half_pos hε)
    refine ⟨max c₁ c₂, hc₁.trans (le_max_left _ _), fun x hx T hT T' hT' => ?_⟩
    have hT₁ : (1 : ℝ) ≤ T := hc₁.trans ((le_max_left _ _).trans hT)
    have hint : ∀ {u : ℝ → ℂ}, ContinuousOn u (Ici 1) →
        IntervalIntegrable (fun t => cexp (((x * t : ℝ) : ℂ) * I) • u t) volume T T' :=
      fun hu => intervalIntegrable_cexp_smul hu x hT₁ (hT₁.trans hT')
    have hsplit : ∫ t in T..T', cexp (((x * t : ℝ) : ℂ) * I) • (f + g) t =
        (∫ t in T..T', cexp (((x * t : ℝ) : ℂ) * I) • f t) +
          ∫ t in T..T', cexp (((x * t : ℝ) : ℂ) * I) • g t := by
      simp only [Pi.add_apply, smul_add]
      exact intervalIntegral.integral_add (hint (continuousOn_of_mem_oscSpan hf'))
        (hint (continuousOn_of_mem_oscSpan hg'))
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    linarith [h₁ x hx T ((le_max_left _ _).trans hT) T' hT',
      h₂ x hx T ((le_max_right _ _).trans hT) T' hT']
  | smul κ f _ hf =>
    intro ε hε
    obtain ⟨c, hc, h⟩ := hf (ε / (‖κ‖ + 1)) (by positivity)
    refine ⟨c, hc, fun x hx T hT T' hT' => ?_⟩
    have hsmul : ∫ t in T..T', cexp (((x * t : ℝ) : ℂ) * I) • (κ • f) t =
        κ • ∫ t in T..T', cexp (((x * t : ℝ) : ℂ) * I) • f t := by
      rw [← intervalIntegral.integral_smul]
      refine intervalIntegral.integral_congr fun t _ => ?_
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [hsmul, norm_smul]
    have hb := h x hx T hT T' hT'
    calc ‖κ‖ * _ ≤ (‖κ‖ + 1) * (ε / (‖κ‖ + 1)) :=
          mul_le_mul (by linarith) hb (norm_nonneg _) (by positivity)
      _ = ε := by field_simp

private theorem exists_hasDerivAt_of_mem_oscSpan {f : ℝ → ℂ} (hf : f ∈ oscSpan) :
    ∃ f' ∈ oscSpan, ∀ t ∈ Ioi (0 : ℝ), HasDerivAt f (f' t) t := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨ν, hν, k, hk, rfl⟩ := hf
    refine ⟨((ν : ℂ) * I) • oscPow ν k + (-(k : ℂ)) • oscPow ν (k + 1),
      oscSpan.add_mem (oscSpan.smul_mem _ (oscPow_mem hν hk))
        (oscSpan.smul_mem _ (oscPow_mem hν (by omega))), fun t ht => ?_⟩
    exact hasDerivAt_oscPow ν k (ne_of_gt ht)
  | zero => exact ⟨0, oscSpan.zero_mem, fun t _ => hasDerivAt_const t (0 : ℂ)⟩
  | add f g _ _ hf hg =>
    obtain ⟨f', hf'm, hf'⟩ := hf
    obtain ⟨g', hg'm, hg'⟩ := hg
    exact ⟨f' + g', oscSpan.add_mem hf'm hg'm, fun t ht => (hf' t ht).add (hg' t ht)⟩
  | smul κ f _ hf =>
    obtain ⟨f', hf'm, hf'⟩ := hf
    exact ⟨κ • f', oscSpan.smul_mem κ hf'm, fun t ht => (hf' t ht).const_smul κ⟩

private theorem sinc_eq_oscSpan {t : ℝ} (ht : t ≠ 0) :
    ((Real.sinc t : ℝ) : ℂ) = ((2 * I)⁻¹ • (oscPow 1 1 - oscPow (-1) 1)) t := by
  have hs : (2 : ℂ) * Complex.sin t = (cexp (-(t : ℂ) * I) - cexp ((t : ℂ) * I)) * I :=
    Complex.two_sin t
  have htC : (t : ℂ) ≠ 0 := ofReal_ne_zero.2 ht
  have hsin : Complex.sin t = (cexp ((t : ℂ) * I) - cexp (-(t : ℂ) * I)) / (2 * I) := by
    rw [eq_div_iff (mul_ne_zero two_ne_zero I_ne_zero)]
    linear_combination I * hs + (cexp (-(t : ℂ) * I) - cexp ((t : ℂ) * I)) * I_sq
  simp only [Real.sinc_of_ne_zero ht, oscPow, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  push_cast
  rw [hsin]
  simp only [one_mul, neg_mul, pow_one]
  field_simp

private theorem exists_mem_oscSpan_eqOn_iteratedDerivWithin (s : ℕ) :
    ∃ f ∈ oscSpan, EqOn (iteratedDerivWithin s (fun t : ℝ => ((Real.sinc t : ℝ) : ℂ)) (Ici 1)) f
      (Ici 1) := by
  induction s with
  | zero =>
    refine ⟨(2 * I)⁻¹ • (oscPow 1 1 - oscPow (-1) 1),
      oscSpan.smul_mem _ (oscSpan.sub_mem (oscPow_mem (Or.inl rfl) le_rfl)
        (oscPow_mem (Or.inr rfl) le_rfl)), fun t ht => ?_⟩
    rw [iteratedDerivWithin_zero]
    exact sinc_eq_oscSpan (by have := mem_Ici.1 ht; positivity)
  | succ s ih =>
    obtain ⟨f, hf, hEq⟩ := ih
    obtain ⟨f', hf'm, hf'⟩ := exists_hasDerivAt_of_mem_oscSpan hf
    refine ⟨f', hf'm, fun t ht => ?_⟩
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht
    rw [iteratedDerivWithin_succ, derivWithin_congr hEq (hEq ht)]
    exact (hf' t ht0).hasDerivWithinAt.derivWithin (uniqueDiffOn_Ici 1 t ht)

/-- For `q(t) = sin t / t` on `[1, ∞)`, each `∫ e^{ixt} q^{(s)}(t) dt` converges at infinity
uniformly for `x ≥ 2`. -/
theorem exists_forall_norm_integral_cexp_smul_iteratedDerivWithin_sinc_le (s : ℕ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ c : ℝ, ∀ x ≥ (2 : ℝ), ∀ T ≥ c, ∀ T' ≥ T,
      ‖∫ t in T..T', cexp (((x * t : ℝ) : ℂ) * I) •
        iteratedDerivWithin s (fun t : ℝ => ((Real.sinc t : ℝ) : ℂ)) (Ici 1) t‖ ≤ ε := by
  obtain ⟨f, hf, hEq⟩ := exists_mem_oscSpan_eqOn_iteratedDerivWithin s
  obtain ⟨c, hc, h⟩ := tailSmall_of_mem_oscSpan hf ε hε
  refine ⟨c, fun x hx T hT T' hT' => ?_⟩
  refine le_of_eq_of_le ?_ (h x hx T hT T' hT')
  congr 1
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le hT'] at ht
  simp only [hEq (hc.trans (hT.trans ht.1) : (1 : ℝ) ≤ t)]

/-- For `q(t) = sin t / t`, the derivative `q'` within `[1, ∞)` is not integrable on `(1, ∞)`, so
`exists_forall_norm_integral_cexp_smul_le` does not apply to `q`. -/
theorem not_integrableOn_iteratedDerivWithin_one_sinc :
    ¬ IntegrableOn (iteratedDerivWithin 1 (fun t : ℝ => ((Real.sinc t : ℝ) : ℂ)) (Ici 1))
      (Ioi 1) := by
  intro h
  refine TauCeti.not_integrableOn_Ioi_deriv_sinc one_pos ?_
  have hc : IntegrableOn (fun t : ℝ => ((deriv Real.sinc t : ℝ) : ℂ)) (Ioi 1) := by
    refine h.congr_fun (fun t ht => ?_) measurableSet_Ioi
    rw [iteratedDerivWithin_one, derivWithin_of_mem_nhds (Ici_mem_nhds ht)]
    exact (Real.analyticAt_sinc t).differentiableAt.hasDerivAt.ofReal_comp.deriv
  simpa only [RCLike.re_to_complex, Complex.ofReal_re] using hc.re

/-- The expansion 2.3.5 applies to `q(t) = sin t / t` on `[1, ∞)`, although `q'` is not integrable
there (`not_integrableOn_iteratedDerivWithin_one_sinc`). -/
theorem hasAsymptoticExpansion_of_tendsto_integral_cexp_smul_sinc {F : ℝ → ℂ}
    (hF : ∀ᶠ x : ℝ in atTop, Tendsto (fun T : ℝ => ∫ t in (1 : ℝ)..T,
      cexp (((x * t : ℝ) : ℂ) * I) • ((Real.sinc t : ℝ) : ℂ)) atTop (𝓝 (F x))) :
    HasAsymptoticExpansion atTop
      (fun (s : ℕ) (x : ℝ) => cexp (((x * (1 : ℝ) : ℝ) : ℂ) * I) * (I / (x : ℂ)) ^ (s + 1))
      (fun s => iteratedDerivWithin s (fun t : ℝ => ((Real.sinc t : ℝ) : ℂ)) (Ici 1) 1) F :=
  hasAsymptoticExpansion_of_tendsto_integral_cexp_smul
    (ofRealCLM.contDiff.comp Real.contDiff_sinc).contDiffOn
    (fun s => ⟨2, fun _ hε =>
      exists_forall_norm_integral_cexp_smul_iteratedDerivWithin_sinc_le s hε⟩) hF

end SincCheck

end HalfLine

section FromZero

/-- **Existence of the Fourier integral.** If `q` is integrable on `(0, 1)` and continuous on
`(0, ∞)`, and `∫ e^{ixt} q(t) dt` converges at `∞`, then the improper integral
`∫₀^∞ e^{ixt} q(t) dt` exists. When `q(t) = O(t^a)` as `t → 0+` for some `a > -1`, the
integrability on `(0, 1)` is automatic; see
`Asymptotics.exists_tendsto_integral_cexp_smul_of_isBigO`. -/
theorem exists_tendsto_integral_cexp_smul_of_intervalIntegrable [CompleteSpace E] {q : ℝ → E}
    {x : ℝ} (hq : ContinuousOn q (Ioi 0)) (hint : IntervalIntegrable q volume 0 1)
    (hu : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, ∀ T' ≥ T,
      ‖∫ t in T..T', cexp (((x * t : ℝ) : ℂ) * I) • q t‖ ≤ ε) :
    ∃ F : E, Tendsto (fun T : ℝ => ∫ t in (0 : ℝ)..T, cexp (((x * t : ℝ) : ℂ) * I) • q t) atTop
      (𝓝 F) := by
  have hc := continuous_cexp_mul_I x
  have hq1 : ContinuousOn q (Ici 1) := hq.mono fun t (ht : 1 ≤ t) => zero_lt_one.trans_le ht
  obtain ⟨L, hL⟩ := exists_tendsto_integral_cexp_smul hq1 hu
  refine ⟨(∫ t in (0 : ℝ)..1, cexp (((x * t : ℝ) : ℂ) * I) • q t) + L,
    (tendsto_const_nhds.add hL).congr' ?_⟩
  filter_upwards [eventually_ge_atTop 1] with T hT
  exact intervalIntegral.integral_add_adjacent_intervals (hint.continuousOn_smul hc.continuousOn)
    ((hc.continuousOn.smul (hq1.mono Icc_subset_Ici_self)).intervalIntegrable_of_Icc hT)

/-- **Existence of the Fourier integral** for an amplitude with a power bound at `0`. If `q` is
continuous on `(0, ∞)` with `q(t) = O(t^a)` as `t → 0+` for some `a > -1`, and
`∫ e^{ixt} q(t) dt` converges at `∞`, then the improper integral `∫₀^∞ e^{ixt} q(t) dt` exists.
Under the hypotheses of `Asymptotics.hasAsymptoticExpansion_fourier` this applies at every large
`x`: the bound at `0+` is the case `k = N = 0` of its expansion hypothesis, with
`a = Re α₀ - 1`, and the convergence at `∞` is the case `k = 0` of its uniform convergence
hypothesis. -/
theorem exists_tendsto_integral_cexp_smul_of_isBigO [CompleteSpace E] {q : ℝ → E} {x a : ℝ}
    (hq : ContinuousOn q (Ioi 0)) (ha : -1 < a) (hq0 : q =O[𝓝[>] 0] fun t => t ^ a)
    (hu : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, ∀ T' ≥ T,
      ‖∫ t in T..T', cexp (((x * t : ℝ) : ℂ) * I) • q t‖ ≤ ε) :
    ∃ F : E, Tendsto (fun T : ℝ => ∫ t in (0 : ℝ)..T, cexp (((x * t : ℝ) : ℂ) * I) • q t) atTop
      (𝓝 F) := by
  -- `q = t^{1-1} q` on `(0, 1]`, so the Mellin power-bound criterion at `z = 1` applies.
  have h := TauCeti.integrableOn_Ioc_cpow_smul_of_isBigO (hq.locallyIntegrableOn measurableSet_Ioi)
    (b := -a) (by simpa using hq0) (z := 1) (by simp only [one_re]; linarith)
  simp only [sub_self, cpow_zero, one_smul] at h
  exact exists_tendsto_integral_cexp_smul_of_intervalIntegrable hq
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2 h) hu

/-- **Splitting off the integral near `0`.** If `∫₀^T e^{ixt} q(t) dt → L` as `T → ∞`, `q` is
continuous on `[b, ∞)` and `e^{ixt} q(t)` is integrable on `(0, b)`, then
`∫_b^T e^{ixt} q(t) dt → L - ∫₀^b e^{ixt} q(t) dt`. -/
theorem tendsto_integral_cexp_smul_sub {q : ℝ → E} {x b : ℝ} {L : E}
    (hq : ContinuousOn q (Ici b))
    (hint : IntervalIntegrable (fun t => cexp (((x * t : ℝ) : ℂ) * I) • q t) volume 0 b)
    (hL : Tendsto (fun T : ℝ => ∫ t in (0 : ℝ)..T, cexp (((x * t : ℝ) : ℂ) * I) • q t) atTop
      (𝓝 L)) :
    Tendsto (fun T : ℝ => ∫ t in b..T, cexp (((x * t : ℝ) : ℂ) * I) • q t) atTop
      (𝓝 (L - ∫ t in (0 : ℝ)..b, cexp (((x * t : ℝ) : ℂ) * I) • q t)) := by
  refine (hL.sub_const _).congr' ?_
  filter_upwards [eventually_ge_atTop b] with T hT
  rw [← intervalIntegral.integral_add_adjacent_intervals hint
    (ContinuousOn.intervalIntegrable_of_Icc hT ((continuous_cexp_mul_I x).continuousOn.smul
      (hq.mono Icc_subset_Ici_self)))]
  simp

end FromZero

end Asymptotics
