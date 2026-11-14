/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CanonicalProduct.Divisor
public import TauCeti.Analysis.Complex.GrowthOrder
import TauCeti.Analysis.Complex.Basic
import TauCeti.Analysis.Complex.Conformal.Reflection.LogDeriv
import TauCeti.Analysis.Complex.DivisorFactorization
import TauCeti.Analysis.Complex.GrowthOrder.Zero.Summability
import TauCeti.Analysis.Complex.LocalLogDeriv
import TauCeti.Analysis.Convex.SimplyConnected
import TauCeti.Analysis.Meromorphic.Conj

/-!
# Hadamard's factorization theorem at order at most one

An entire function `f : ℂ → ℂ` of growth order at most `1` with `f 0 ≠ 0` factors as the product
of an exponential of an affine function and the genus-one canonical product over its zeros:

`f s = f 0 * exp (logDeriv f 0 * s) * divisorProductOne f s`
`    = exp (a + b * s) * ∏' ρ : ℂ, E₁(s / ρ) ^ m_ρ`,

where `E₁(z) = (1 - z) exp z` is `Complex.weierstrassFactorOne` and `m_ρ` is the multiplicity
`(MeromorphicOn.divisor f Set.univ ρ).toNat`. Off the zero set, the logarithmic derivative of `f`
has the paired partial-fraction expansion

`logDeriv f s = logDeriv f 0 + ∑' ρ, m_ρ * (1 / (s - ρ) + 1 / ρ)`,

converging absolutely at each point off the zeros and locally uniformly on `{s | f s ≠ 0}`.

The proof follows Landau's local logarithmic-derivative method (Montgomery–Vaughan §11.1):
1. Jensen's bound and dyadic summation (`TauCeti.OrderLE.summable_divisor_mul_norm_rpow`) give
   `∑_ρ m_ρ ‖ρ⁻¹‖ ^ 2 < ∞`, so `divisorProductOne f` is entire with the same divisor as `f`.
2. At exponent `3 / 2 > 1`, the subtracted local logarithmic-derivative estimate
   `AnalyticOnNhd.norm_logDeriv_sub_logDeriv_sub_finsum_divisor_le` bounds
   `logDeriv f s - logDeriv f 0` minus the finite partial-fraction sum on `closedBall 0 n` by
   `O(n ^ (-1 / 2))`, identifying `logDeriv f s - logDeriv f 0` with
   `logDeriv (divisorProductOne f) s` wherever `f s ≠ 0`.
3. Dividing `f` by `divisorProductOne f`
   (`TauCeti.exists_differentiableOn_eqOn_mul_exp_of_divisor_eq`) gives
   `f = divisorProductOne f * exp H` for an entire `H` whose derivative agrees with `logDeriv f 0`
   near `0`, hence everywhere by analytic continuation.

When every zero of `f` lies in the closed critical strip `0 ≤ Re ρ ≤ 1`, the bound
`0 ≤ Re (1 / ρ) ≤ ‖ρ⁻¹‖ ^ 2` makes `∑' ρ, m_ρ * Re (1 / ρ)` and `∑' ρ, m_ρ * Re (1 / (s - ρ))`
separately summable. Under a functional symmetry `f (1 - z) = c * conj (f (conj z))`, permuting the
zeros by `ρ ↦ 1 - conj ρ` (`TauCeti.divisorSupportOneSubConj`, `TauCeti.logDeriv_one_sub_conj`)
yields `Re (logDeriv f 0) = -∑' ρ, m_ρ * Re (1 / ρ)` and eliminates the constant term from
`Re (logDeriv f s)`.

## Main results

* `TauCeti.OrderLE.summable_divisor_toNat_mul_norm_inv_sq`: weighted inverse-square summability of
  the zeros of an entire function of order at most `1`.
* `TauCeti.OrderLE.eq_mul_cexp_logDeriv_mul_divisorProductOne`,
  `TauCeti.OrderLE.exists_eq_cexp_add_logDeriv_mul_divisorProductOne`: Hadamard factorization in
  terms of `divisorProductOne f`, identifying the linear coefficient as `logDeriv f 0`.
* `TauCeti.hadamard_of_orderLE_one`: Hadamard's factorization theorem over `ℂ` in terms of
  `Multipliable` and `∏' ρ : ℂ, weierstrassFactorOne (s / ρ) ^ m_ρ`.
* `TauCeti.OrderLE.logDeriv_eq_add_tsum`, `TauCeti.OrderLE.hasSumLocallyUniformlyOn_logDeriv`:
  pointwise and locally uniform partial-fraction expansions of `logDeriv f`.
* `TauCeti.OrderLE.re_logDeriv_zero_eq_neg_tsum`, `TauCeti.OrderLE.re_logDeriv_eq_tsum`:
  real-part cancellation `Re (logDeriv f 0) = -∑' ρ, m_ρ * Re (1 / ρ)` and
  `Re (logDeriv f s) = ∑' ρ, m_ρ * Re (1 / (s - ρ))` under critical-strip zero location and
  functional symmetry.

## References

* J. Hadamard, *Étude sur les propriétés des fonctions entières et en particulier d'une fonction
  considérée par Riemann*, J. Math. Pures Appl. (4) **9** (1893), 171–215.
* H. Davenport, *Multiplicative Number Theory*, 3rd ed., GTM 74, Chapters 11–12.
* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I*, Cambridge University
  Press, 2007, §§10.2 and 11.1.
-/

public section

open Complex ComplexConjugate Filter Metric Topology Asymptotics Bornology
open scoped BigOperators

namespace TauCeti

namespace OrderLE

/-- The zeros of an entire function of order at most `1`, counted with their native divisor
multiplicities, have summable weighted inverse squares. -/
theorem summable_divisor_toNat_mul_norm_inv_sq {f : ℂ → ℂ}
    (h : OrderLE f 1) (hf : Differentiable ℂ f) :
    Summable (fun ρ : (MeromorphicOn.divisor f Set.univ).support ↦
      ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℝ) * ‖(ρ : ℂ)⁻¹‖ ^ 2) := by
  have hfa : AnalyticOnNhd ℂ f Set.univ := fun z _ ↦ hf.analyticAt z
  refine (h.summable_divisor_mul_norm_rpow hf (by norm_num : (1 : ℝ) < 2)).congr fun ρ ↦ ?_
  rw [hfa.natCast_toNat_divisor, Real.rpow_neg (norm_nonneg _), Real.rpow_two, norm_inv, inv_pow]

/-- The genus-one native divisor product of an entire function of order at most `1` is entire. -/
@[fun_prop]
theorem differentiable_divisorProductOne {f : ℂ → ℂ}
    (h : OrderLE f 1) (hf : Differentiable ℂ f) :
    Differentiable ℂ (divisorProductOne f) :=
  TauCeti.differentiable_divisorProductOne (h.summable_divisor_toNat_mul_norm_inv_sq hf)

/-- Rewrites the finite partial-fraction sum over `closedBall 0 R` at `z₀ = 0` as the finite sum
over the norm-`R` sublevel of the whole-plane divisor support. -/
private theorem finsum_divisor_closedBall_eq_sum_sublevel {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (R : ℝ) (s : ℂ) :
    (∑ᶠ ρ, (MeromorphicOn.divisor f (closedBall 0 R) ρ : ℂ) * (1 / (s - ρ) - 1 / (0 - ρ))) =
      ∑ ρ ∈ (MeromorphicOn.divisor_norm_sublevel_finite f R).toFinset,
        ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℂ) * (1 / (s - ρ) + 1 / ρ) := by
  classical
  have hfa : AnalyticOnNhd ℂ f Set.univ := fun z _ ↦ hf.analyticAt z
  have hball : AnalyticOnNhd ℂ f (closedBall 0 R) := fun z _ ↦ hf.analyticAt z
  let d := MeromorphicOn.divisor f Set.univ
  let D := MeromorphicOn.divisor f (closedBall 0 R)
  let S := (MeromorphicOn.divisor_norm_sublevel_finite f R).toFinset
  let emb : d.support ↪ ℂ := ⟨Subtype.val, Subtype.coe_injective⟩
  have hsupp : (fun ρ : ℂ ↦ (D ρ : ℂ) * (1 / (s - ρ) - 1 / (0 - ρ))).support ⊆ S.map emb := by
    intro z hz
    have hDz : D z ≠ 0 := fun h0 ↦ hz (by simp [h0])
    have hzR : z ∈ closedBall (0 : ℂ) R := by
      by_contra hnot
      exact hDz (Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hnot)
    have hdz : d z = D z := by
      rw [MeromorphicOn.divisor_apply hfa.meromorphicOn (Set.mem_univ z),
        MeromorphicOn.divisor_apply hball.meromorphicOn hzR]
    have hmem : z ∈ d.support := Function.mem_support.mpr (hdz ▸ hDz)
    rw [Finset.mem_coe, Finset.mem_map]
    refine ⟨⟨z, hmem⟩, ?_, rfl⟩
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    simpa [dist_zero_right] using hzR
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_map]
  refine Finset.sum_congr rfl fun ρ hρ ↦ ?_
  have hρR : (ρ : ℂ) ∈ closedBall (0 : ℂ) R := by
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hρ
    simpa [dist_zero_right] using hρ
  have hdD : D ρ = d ρ := by
    rw [MeromorphicOn.divisor_apply hball.meromorphicOn hρR,
      MeromorphicOn.divisor_apply hfa.meromorphicOn (Set.mem_univ _)]
  dsimp only [emb]
  rw [Function.Embedding.coeFn_mk, hdD, ← hfa.natCast_toNat_divisor, zero_sub, div_neg,
    sub_neg_eq_add]

/-- Applying the subtracted Landau bound on `closedBall 0 (2 * n)` at growth exponent `3 / 2`
bounds the difference between `logDeriv f s - logDeriv f 0` and the radius-`n` partial-fraction sum
by `O(n ^ (-2)) + O(n ^ (-1 / 2))`. -/
private theorem exists_eventually_norm_logDeriv_sub_sum_sublevel_le {f : ℂ → ℂ}
    (h : OrderLE f 1) (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0) {s : ℂ} (hs : f s ≠ 0) :
    ∃ K : ℝ, ∀ᶠ n : ℕ in atTop,
      ‖logDeriv f s - logDeriv f 0 -
          ∑ ρ ∈ (MeromorphicOn.divisor_norm_sublevel_finite f n).toFinset,
            ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℂ) * (1 / (s - ρ) + 1 / ρ)‖ ≤
        384 * ‖s‖ * Real.log K * ((2 * (n : ℝ)) ^ 2)⁻¹ +
          384 * ‖s‖ * (2 * (n : ℝ)) ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨C, _, hC⟩ := (h.isBigO (by norm_num : (1 : ℝ) < 3 / 2)).exists_pos
  obtain ⟨L, _, hL⟩ := Filter.hasBasis_cobounded_norm.mem_iff.mp hC.bound
  set K : ℝ := max 1 (C / ‖f 0‖)
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨K, ?_⟩
  filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop ⌈L⌉₊,
    eventually_ge_atTop ⌈4 * ‖s‖⌉₊] with n hn1 hnL hns
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn1
  have hR_pos : 0 < 2 * (n : ℝ) := by positivity
  have hRL : L ≤ 2 * (n : ℝ) := by
    have : L ≤ (n : ℝ) := (Nat.le_ceil L).trans (Nat.cast_le.mpr hnL)
    linarith
  have hsR : ‖s - 0‖ ≤ 2 * (n : ℝ) / 8 := by
    have : 4 * ‖s‖ ≤ (n : ℝ) := (Nat.le_ceil _).trans (Nat.cast_le.mpr hns)
    rw [sub_zero]
    linarith
  let M : ℝ := K * Real.exp ((2 * (n : ℝ)) ^ (3 / 2 : ℝ))
  have hM : ∀ w ∈ sphere (0 : ℂ) (2 * (n : ℝ)), ‖f w‖ ≤ M * ‖f 0‖ := fun w hw ↦ by
    have hwR : ‖w‖ = 2 * (n : ℝ) := by simpa [dist_zero_right] using hw
    have hwbound : ‖f w‖ ≤ C * Real.exp ((2 * (n : ℝ)) ^ (3 / 2 : ℝ)) := by
      have hLw : ‖f w‖ ≤ C * ‖Real.exp (‖w‖ ^ (3 / 2 : ℝ))‖ := hL (hRL.trans hwR.symm.le)
      rw [Real.norm_eq_abs, Real.abs_exp, hwR] at hLw
      exact hLw
    have hCK : C ≤ K * ‖f 0‖ := by
      rw [← div_le_iff₀ (norm_pos_iff.mpr hf0)]
      exact le_max_right _ _
    calc ‖f w‖ ≤ C * Real.exp ((2 * (n : ℝ)) ^ (3 / 2 : ℝ)) := hwbound
      _ ≤ (K * ‖f 0‖) * Real.exp ((2 * (n : ℝ)) ^ (3 / 2 : ℝ)) := by gcongr
      _ = M * ‖f 0‖ := by dsimp [M]; ring
  have hball : AnalyticOnNhd ℂ f (closedBall 0 (2 * (n : ℝ))) := fun z _ ↦ hf.analyticAt z
  have hlandau := hball.norm_logDeriv_sub_logDeriv_sub_finsum_divisor_le hR_pos hf0 hM hsR hs
  have hhalf : 2 * (n : ℝ) / 2 = (n : ℝ) := by ring
  rw [hhalf, finsum_divisor_closedBall_eq_sum_sublevel hf n s, sub_zero] at hlandau
  refine hlandau.trans (le_of_eq ?_)
  have hlogM : Real.log M = Real.log K + (2 * (n : ℝ)) ^ (3 / 2 : ℝ) := by
    dsimp [M]
    rw [Real.log_mul hK0.ne' (Real.exp_pos _).ne', Real.log_exp]
  have hrpow : (2 * (n : ℝ)) ^ (3 / 2 : ℝ) / (2 * (n : ℝ)) ^ 2 =
      (2 * (n : ℝ)) ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_two (2 * (n : ℝ)), ← Real.rpow_sub hR_pos]
    norm_num
  rw [hlogM]
  calc 384 * ‖s‖ / (2 * (n : ℝ)) ^ 2 * (Real.log K + (2 * (n : ℝ)) ^ (3 / 2 : ℝ))
      = 384 * ‖s‖ * Real.log K * ((2 * (n : ℝ)) ^ 2)⁻¹ +
          384 * ‖s‖ * ((2 * (n : ℝ)) ^ (3 / 2 : ℝ) / (2 * (n : ℝ)) ^ 2) := by ring
    _ = 384 * ‖s‖ * Real.log K * ((2 * (n : ℝ)) ^ 2)⁻¹ +
          384 * ‖s‖ * (2 * (n : ℝ)) ^ (-(1 / 2 : ℝ)) := by rw [hrpow]

/-- Off the zeros of an entire function `f` of order at most `1` with `f 0 ≠ 0`, `logDeriv f`
differs from `logDeriv (divisorProductOne f)` by the constant `logDeriv f 0`. -/
theorem logDeriv_eq_add_logDeriv_divisorProductOne {f : ℂ → ℂ}
    (h : OrderLE f 1) (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0) {s : ℂ} (hs : f s ≠ 0) :
    logDeriv f s = logDeriv f 0 + logDeriv (divisorProductOne f) s := by
  have hsum := h.summable_divisor_toNat_mul_norm_inv_sq hf
  have h0 := (hf.analyticAt 0).notMem_divisor_support (U := Set.univ) hf0
  have hssupp := (hf.analyticAt s).notMem_divisor_support (U := Set.univ) hs
  let g : (MeromorphicOn.divisor f Set.univ).support → ℂ := fun ρ ↦
    ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℂ) * (1 / (s - ρ) + 1 / ρ)
  have hg_sum : HasSum g (logDeriv (divisorProductOne f) s) := by
    rw [logDeriv_divisorProductOne h0 hsum hssupp]
    exact (summable_norm_natCast_divisor_mul_one_div_sub_add_one_div h0 hsum hssupp).of_norm.hasSum
  obtain ⟨K, hbound⟩ := exists_eventually_norm_logDeriv_sub_sum_sublevel_le h hf hf0 hs
  have htwo_nat : Tendsto (fun n : ℕ ↦ 2 * (n : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop two_pos
  have hrhs : Tendsto (fun n : ℕ ↦ 384 * ‖s‖ * Real.log K * ((2 * (n : ℝ)) ^ 2)⁻¹ +
      384 * ‖s‖ * (2 * (n : ℝ)) ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) := by
    have h₁ : Tendsto (fun n : ℕ ↦ 384 * ‖s‖ * Real.log K * ((2 * (n : ℝ)) ^ 2)⁻¹)
        atTop (𝓝 0) := by
      simpa using (tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp
        htwo_nat)).const_mul (384 * ‖s‖ * Real.log K)
    have h₂ : Tendsto (fun n : ℕ ↦ 384 * ‖s‖ * (2 * (n : ℝ)) ^ (-(1 / 2 : ℝ)))
        atTop (𝓝 0) := by
      simpa using ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
        htwo_nat).const_mul (384 * ‖s‖)
    simpa using h₁.add h₂
  have hlhs : Tendsto (fun n : ℕ ↦ ‖logDeriv f s - logDeriv f 0 -
      ∑ ρ ∈ (MeromorphicOn.divisor_norm_sublevel_finite f n).toFinset, g ρ‖)
      atTop (𝓝 ‖logDeriv f s - logDeriv f 0 - logDeriv (divisorProductOne f) s‖) :=
    (tendsto_const_nhds.sub (MeromorphicOn.tendsto_sum_divisor_norm_sublevel_atTop hg_sum)).norm
  have hzero : ‖logDeriv f s - logDeriv f 0 - logDeriv (divisorProductOne f) s‖ ≤ 0 :=
    le_of_tendsto_of_tendsto hlhs hrhs hbound
  have heq := norm_le_zero_iff.mp hzero
  linear_combination heq

/-- **Hadamard's factorization theorem at order at most one**, native-divisor form with explicit
coefficients: `f z = f 0 * exp (logDeriv f 0 * z) * divisorProductOne f z`. -/
theorem eq_mul_cexp_logDeriv_mul_divisorProductOne {f : ℂ → ℂ}
    (h : OrderLE f 1) (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0) (z : ℂ) :
    f z = f 0 * exp (logDeriv f 0 * z) * divisorProductOne f z := by
  have hsum := h.summable_divisor_toNat_mul_norm_inv_sq hf
  have hP : Differentiable ℂ (divisorProductOne f) := TauCeti.differentiable_divisorProductOne hsum
  obtain ⟨H, hHd, hfeq⟩ := exists_differentiableOn_eqOn_mul_exp_of_divisor_eq
    (convex_univ.isSimplyConnected Set.univ_nonempty) isOpen_univ
    (fun w _ ↦ hf.analyticAt w) (fun w _ ↦ hP.analyticAt w)
    ⟨0, Set.mem_univ 0, hf0⟩ ⟨0, Set.mem_univ 0, by simp⟩
    (divisor_divisorProductOne hf hf0 hsum).symm
  have hH : Differentiable ℂ H := differentiableOn_univ.mp hHd
  have hf_eq (w : ℂ) : f w = divisorProductOne f w * exp (H w) := hfeq (Set.mem_univ w)
  -- Near `0`, `f` and `divisorProductOne f` are nonzero, so `deriv H = logDeriv f 0` there,
  -- hence everywhere by the identity theorem.
  have hderiv_near : ∀ᶠ w : ℂ in 𝓝 0, deriv H w = logDeriv f 0 := by
    filter_upwards [hf.continuous.continuousAt.eventually_ne hf0] with w hfw
    have hPw : divisorProductOne f w ≠ 0 :=
      (divisorProductOne_eq_zero_iff hf hf0 hsum w).not.mpr hfw
    have hlog₁ : logDeriv f w = logDeriv (divisorProductOne f) w + deriv H w := by
      have hmul : logDeriv f w =
          logDeriv (divisorProductOne f) w + logDeriv (fun u ↦ exp (H u)) w := by
        conv_lhs => rw [funext hf_eq]
        exact logDeriv_fun_mul w hPw (exp_ne_zero (H w)) (hP w) (hH.cexp w)
      have hexp : logDeriv (fun u ↦ exp (H u)) w = deriv H w := by
        rw [logDeriv_apply, deriv_cexp (hH w), mul_div_cancel_left₀ _ (exp_ne_zero _)]
      rw [hmul, hexp]
    have hlog₂ := h.logDeriv_eq_add_logDeriv_divisorProductOne hf hf0 hfw
    rw [hlog₁, add_comm _ (deriv H w)] at hlog₂
    exact add_right_cancel hlog₂
  have hderiv_all (w : ℂ) : deriv H w = logDeriv f 0 := by
    have ha₁ : AnalyticOnNhd ℂ (deriv H) Set.univ := fun u _ ↦ (hH.analyticAt u).deriv
    have ha₂ : AnalyticOnNhd ℂ (fun _ : ℂ ↦ logDeriv f 0) Set.univ := fun _ _ ↦ analyticAt_const
    have hfreq : ∃ᶠ u : ℂ in 𝓝[≠] 0, deriv H u = logDeriv f 0 :=
      (hderiv_near.filter_mono nhdsWithin_le_nhds).frequently
    exact ha₁.eqOn_of_preconnected_of_frequently_eq ha₂ isPreconnected_univ
      (Set.mem_univ 0) hfreq (Set.mem_univ w)
  have hconst := is_const_of_deriv_eq_zero (f := fun w ↦ H w - logDeriv f 0 * w)
    (by fun_prop) fun w ↦ by
      rw [deriv_fun_sub (hH w) (by fun_prop), deriv_const_mul_field, deriv_id'', mul_one,
        hderiv_all w, sub_self]
  have hH_aff : H z = H 0 + logDeriv f 0 * z := by
    have := hconst z 0
    simp only [mul_zero, sub_zero] at this
    linear_combination this
  have hf0_eq : f 0 = exp (H 0) := by simpa using hf_eq 0
  rw [hf_eq z, hH_aff, exp_add, ← hf0_eq]
  ring

/-- **Hadamard's factorization theorem at order at most one**, affine-exponential form:
`f z = exp (a + logDeriv f 0 * z) * divisorProductOne f z` with `exp a = f 0`. -/
theorem exists_eq_cexp_add_logDeriv_mul_divisorProductOne {f : ℂ → ℂ}
    (h : OrderLE f 1) (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0) :
    ∃ a : ℂ, exp a = f 0 ∧ ∀ z : ℂ, f z = exp (a + logDeriv f 0 * z) * divisorProductOne f z :=
  ⟨log (f 0), exp_log hf0, fun z ↦ by
    rw [exp_add, exp_log hf0]
    exact h.eq_mul_cexp_logDeriv_mul_divisorProductOne hf hf0 z⟩

/-- The paired partial-fraction series of `logDeriv f` is absolutely convergent at every point off
the zeros of `f`. -/
theorem summable_norm_natCast_divisor_mul_one_div_sub_add_one_div {f : ℂ → ℂ}
    (h : OrderLE f 1) (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0) {s : ℂ} (hs : f s ≠ 0) :
    Summable (fun ρ : (MeromorphicOn.divisor f Set.univ).support ↦
      ‖((MeromorphicOn.divisor f Set.univ ρ).toNat : ℂ) * (1 / (s - ρ) + 1 / ρ)‖) :=
  TauCeti.summable_norm_natCast_divisor_mul_one_div_sub_add_one_div
    ((hf.analyticAt 0).notMem_divisor_support hf0)
    (h.summable_divisor_toNat_mul_norm_inv_sq hf)
    ((hf.analyticAt s).notMem_divisor_support hs)

/-- **Partial-fraction expansion of the logarithmic derivative** at order at most one: away from
the zeros of `f`, `logDeriv f s = logDeriv f 0 + ∑' ρ, m_ρ * (1 / (s - ρ) + 1 / ρ)`. -/
theorem logDeriv_eq_add_tsum {f : ℂ → ℂ}
    (h : OrderLE f 1) (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0) {s : ℂ} (hs : f s ≠ 0) :
    logDeriv f s = logDeriv f 0 + ∑' ρ : (MeromorphicOn.divisor f Set.univ).support,
      ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℂ) * (1 / (s - ρ) + 1 / ρ) := by
  rw [h.logDeriv_eq_add_logDeriv_divisorProductOne hf hf0 hs,
    logDeriv_divisorProductOne
      ((hf.analyticAt 0).notMem_divisor_support hf0)
      (h.summable_divisor_toNat_mul_norm_inv_sq hf)
      ((hf.analyticAt s).notMem_divisor_support hs)]

/-- The paired partial-fraction series converges locally uniformly on `{s | f s ≠ 0}` to
`logDeriv f - logDeriv f 0`. -/
theorem hasSumLocallyUniformlyOn_logDeriv {f : ℂ → ℂ}
    (h : OrderLE f 1) (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0) :
    HasSumLocallyUniformlyOn
      (fun (ρ : (MeromorphicOn.divisor f Set.univ).support) s ↦
        ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℂ) * (1 / (s - ρ) + 1 / ρ))
      (fun s ↦ logDeriv f s - logDeriv f 0) {s : ℂ | f s ≠ 0} := by
  have hsum := h.summable_divisor_toNat_mul_norm_inv_sq hf
  have h0 := (hf.analyticAt 0).notMem_divisor_support (U := Set.univ) hf0
  have hset : {s : ℂ | f s ≠ 0} = ((MeromorphicOn.divisor f Set.univ).support)ᶜ := by
    ext s
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff]
    constructor
    · exact (hf.analyticAt s).notMem_divisor_support
    · intro hs hfs
      exact divisorProductOne_ne_zero hsum h0 hs
        ((divisorProductOne_eq_zero_iff hf hf0 hsum s).mpr hfs)
  rw [hset]
  exact (hasSumLocallyUniformlyOn_logDeriv_divisorProductOne h0 hsum).congr_right fun s hs ↦ by
    have hfs : f s ≠ 0 := by
      have hs' : s ∈ {z : ℂ | f z ≠ 0} := hset.symm ▸ hs
      exact hs'
    rw [h.logDeriv_eq_add_logDeriv_divisorProductOne hf hf0 hfs, add_sub_cancel_left]

/-! ### Critical-strip zero location and real-part cancellation -/

/-- When every zero of `f` has real part in `[0, 1]`, the real parts `m_ρ * Re (1 / ρ)` are
nonnegative and summable, bounded termwise by `m_ρ * ‖ρ⁻¹‖ ^ 2`. -/
theorem summable_divisor_toNat_mul_re_one_div {f : ℂ → ℂ}
    (h : OrderLE f 1) (hf : Differentiable ℂ f)
    (hstrip : ∀ ρ : ℂ, f ρ = 0 → ρ.re ∈ Set.Icc 0 1) :
    Summable (fun ρ : (MeromorphicOn.divisor f Set.univ).support ↦
      ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℝ) * (1 / (ρ : ℂ)).re) := by
  refine Summable.of_nonneg_of_le (fun ρ ↦ ?_) (fun ρ ↦ ?_)
    (h.summable_divisor_toNat_mul_norm_inv_sq hf)
  · have hρ := hstrip ρ ((hf.analyticAt ρ).apply_eq_zero_of_divisor_ne_zero ρ.property)
    exact mul_nonneg (Nat.cast_nonneg _)
      (by simpa only [one_div, Complex.inv_re_nonneg] using hρ.1)
  · have hρ := hstrip ρ ((hf.analyticAt ρ).apply_eq_zero_of_divisor_ne_zero ρ.property)
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    rw [one_div, inv_re, normSq_eq_norm_sq, norm_inv, inv_pow, ← one_div]
    exact div_le_div_of_nonneg_right hρ.2 (sq_nonneg _)

/-- When every zero of `f` has real part in `[0, 1]`, the unsubtracted real-part series
`∑' ρ, m_ρ * Re (1 / (s - ρ))` is summable at every point `s` with `f s ≠ 0`. -/
theorem summable_divisor_toNat_mul_re_one_div_sub {f : ℂ → ℂ}
    (h : OrderLE f 1) (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0)
    (hstrip : ∀ ρ : ℂ, f ρ = 0 → ρ.re ∈ Set.Icc 0 1) {s : ℂ} (hs : f s ≠ 0) :
    Summable (fun ρ : (MeromorphicOn.divisor f Set.univ).support ↦
      ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℝ) * (1 / (s - ρ)).re) := by
  have hpair : Summable (fun ρ : (MeromorphicOn.divisor f Set.univ).support ↦
      (((MeromorphicOn.divisor f Set.univ ρ).toNat : ℂ) * (1 / (s - ρ) + 1 / ρ)).re) :=
    Complex.reCLM.summable
      (h.summable_norm_natCast_divisor_mul_one_div_sub_add_one_div hf hf0 hs).of_norm
  have hinv := h.summable_divisor_toNat_mul_re_one_div hf hstrip
  refine (hpair.sub hinv).congr fun ρ ↦ ?_
  simp only [mul_re, natCast_re, natCast_im, zero_mul, sub_zero, add_re]
  ring

/-- Splitting `Re (logDeriv f s)` into `Re (logDeriv f 0)`, `∑' ρ, m_ρ * Re (1 / (s - ρ))`, and
`∑' ρ, m_ρ * Re (1 / ρ)` when every zero lies in `0 ≤ Re ρ ≤ 1`. -/
private theorem re_logDeriv_eq_add_tsum_add_tsum {f : ℂ → ℂ}
    (h : OrderLE f 1) (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0)
    (hstrip : ∀ ρ : ℂ, f ρ = 0 → ρ.re ∈ Set.Icc 0 1) {s : ℂ} (hs : f s ≠ 0) :
    (logDeriv f s).re = (logDeriv f 0).re +
      (∑' ρ : (MeromorphicOn.divisor f Set.univ).support,
        ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℝ) * (1 / (s - ρ)).re) +
      (∑' ρ : (MeromorphicOn.divisor f Set.univ).support,
        ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℝ) * (1 / (ρ : ℂ)).re) := by
  have hc := (h.summable_norm_natCast_divisor_mul_one_div_sub_add_one_div hf hf0 hs).of_norm
  have hsub := h.summable_divisor_toNat_mul_re_one_div_sub hf hf0 hstrip hs
  have hinv := h.summable_divisor_toNat_mul_re_one_div hf hstrip
  have htsum_re : (∑' ρ : (MeromorphicOn.divisor f Set.univ).support,
      ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℂ) * (1 / (s - ρ) + 1 / ρ)).re =
      ∑' ρ : (MeromorphicOn.divisor f Set.univ).support,
        (((MeromorphicOn.divisor f Set.univ ρ).toNat : ℝ) * (1 / (s - ρ)).re +
          ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℝ) * (1 / (ρ : ℂ)).re) := by
    rw [← Complex.reCLM_apply, ContinuousLinearMap.map_tsum Complex.reCLM hc]
    refine tsum_congr fun ρ ↦ ?_
    rw [Complex.reCLM_apply, mul_re, natCast_re, natCast_im, zero_mul, sub_zero, add_re, mul_add]
  rw [h.logDeriv_eq_add_tsum hf hf0 hs, add_re, htsum_re, Summable.tsum_add hsub hinv, add_assoc]

/-- **Real-part formula for the Hadamard linear constant.** Let `f` be entire of order at most `1`
with `f 0 ≠ 0`, all zeros in `0 ≤ Re ρ ≤ 1`, and `f (1 - z) = c * conj (f (conj z))` for a
constant `c`. Then `Re (logDeriv f 0) = -∑' ρ, m_ρ * Re (1 / ρ)`. -/
theorem re_logDeriv_zero_eq_neg_tsum {f : ℂ → ℂ}
    (h : OrderLE f 1) (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0)
    (hstrip : ∀ ρ : ℂ, f ρ = 0 → ρ.re ∈ Set.Icc 0 1)
    {c : ℂ} (hfe : ∀ z : ℂ, f (1 - z) = c * conj (f (conj z))) :
    (logDeriv f 0).re = -∑' ρ : (MeromorphicOn.divisor f Set.univ).support,
      ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℝ) * (1 / (ρ : ℂ)).re := by
  have hc : c ≠ 0 := by
    rintro rfl
    have h0 := hfe 1
    simp only [sub_self, zero_mul] at h0
    exact hf0 h0
  have hf1 : f 1 ≠ 0 := by
    have h1 := hfe 0
    rw [sub_zero, map_zero] at h1
    rw [h1]
    exact mul_ne_zero hc (star_ne_zero.mpr hf0)
  have hlog1 : (logDeriv f 1).re = -(logDeriv f 0).re := by
    have h0 := congrArg re (logDeriv_one_sub_conj hfe 0)
    simpa using h0
  let d := MeromorphicOn.divisor f Set.univ
  have hperm : (∑' ρ : d.support, ((d ρ).toNat : ℝ) * (1 / (1 - (ρ : ℂ))).re) =
      ∑' ρ : d.support, ((d ρ).toNat : ℝ) * (1 / (ρ : ℂ)).re := by
    symm
    rw [← (divisorSupportOneSubConj hfe).tsum_eq]
    refine tsum_congr fun ρ ↦ ?_
    simp only [d, coe_divisorSupportOneSubConj_apply, divisor_one_sub_conj hfe]
    congr 1
    rw [← conj_re]
    simp
  have hexp1 := h.re_logDeriv_eq_add_tsum_add_tsum hf hf0 hstrip hf1
  rw [hperm, hlog1] at hexp1
  linarith

/-- **Cancelled real-part expansion of the logarithmic derivative.** Under the hypotheses of
`OrderLE.re_logDeriv_zero_eq_neg_tsum`, for every `s` with `f s ≠ 0` one has
`Re (logDeriv f s) = ∑' ρ, m_ρ * Re (1 / (s - ρ))`, with no additive constant. -/
theorem re_logDeriv_eq_tsum {f : ℂ → ℂ}
    (h : OrderLE f 1) (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0)
    (hstrip : ∀ ρ : ℂ, f ρ = 0 → ρ.re ∈ Set.Icc 0 1)
    {c : ℂ} (hfe : ∀ z : ℂ, f (1 - z) = c * conj (f (conj z)))
    {s : ℂ} (hs : f s ≠ 0) :
    (logDeriv f s).re = ∑' ρ : (MeromorphicOn.divisor f Set.univ).support,
      ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℝ) * (1 / (s - ρ)).re := by
  rw [h.re_logDeriv_eq_add_tsum_add_tsum hf hf0 hstrip hs,
    h.re_logDeriv_zero_eq_neg_tsum hf hf0 hstrip hfe]
  ring

/-- When every zero lies in `0 ≤ Re ρ ≤ 1` and `1 ≤ Re s`, every summand `m_ρ * Re (1 / (s - ρ))`
is nonnegative, so their series has nonnegative sum. -/
theorem tsum_divisor_toNat_mul_re_one_div_sub_nonneg {f : ℂ → ℂ}
    (hstrip : ∀ ρ : ℂ, f ρ = 0 → ρ.re ∈ Set.Icc 0 1) (hf : Differentiable ℂ f)
    {s : ℂ} (hs : 1 ≤ s.re) :
    0 ≤ ∑' ρ : (MeromorphicOn.divisor f Set.univ).support,
      ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℝ) * (1 / (s - ρ)).re := by
  refine tsum_nonneg fun ρ ↦ mul_nonneg (Nat.cast_nonneg _) ?_
  have hρ := hstrip ρ ((hf.analyticAt ρ).apply_eq_zero_of_divisor_ne_zero ρ.property)
  rw [one_div, Complex.inv_re_nonneg, sub_re, sub_nonneg]
  exact hρ.2.trans hs

end OrderLE

/-- **Hadamard's factorization theorem at order at most one.** For an entire function `f` of growth
order at most `1` with `f 0 ≠ 0`, there exist `a b : ℂ` such that at every `s : ℂ` the genus-one
canonical product over `ℂ` is multipliable and `f s = exp (a + b * s) * ∏' ρ, E₁(s / ρ) ^ m_ρ`. -/
theorem hadamard_of_orderLE_one {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h : OrderLE f 1)
    (hf0 : f 0 ≠ 0) :
    ∃ a b : ℂ, ∀ s : ℂ,
      Multipliable (fun ρ : ℂ ↦
        weierstrassFactorOne (s / ρ) ^ (MeromorphicOn.divisor f Set.univ ρ).toNat) ∧
      f s = exp (a + b * s) * ∏' ρ : ℂ,
        weierstrassFactorOne (s / ρ) ^ (MeromorphicOn.divisor f Set.univ ρ).toNat := by
  have hsum := h.summable_divisor_toNat_mul_norm_inv_sq hf
  obtain ⟨a, _, ha⟩ := h.exists_eq_cexp_add_logDeriv_mul_divisorProductOne hf hf0
  refine ⟨a, logDeriv f 0, fun s ↦ ?_⟩
  have hfn : (fun ρ : ℂ ↦
      weierstrassFactorOne (s / ρ) ^ (MeromorphicOn.divisor f Set.univ ρ).toNat) =
      fun ρ : ℂ ↦ weierstrassFactorOne (ρ⁻¹ * s) ^ (MeromorphicOn.divisor f Set.univ ρ).toNat := by
    ext ρ
    rw [div_eq_inv_mul]
  have hprod : HasProd (fun ρ : ℂ ↦
      weierstrassFactorOne (s / ρ) ^ (MeromorphicOn.divisor f Set.univ ρ).toNat)
      (divisorProductOne f s) := hfn ▸ hasProd_divisorProductOne hsum s
  exact ⟨hprod.multipliable, (ha s).trans (congrArg (exp (a + logDeriv f 0 * s) * ·)
    hprod.tprod_eq.symm)⟩

/-! ### Examples -/

/-- For `f s = exp (c * s)`, the divisor support is empty, the canonical product is `1`, and the
factorization reads `exp (c * s) = 1 * exp (c * s) * 1`. -/
example (c s : ℂ) :
    exp (c * s) = exp (c * 0) * exp (logDeriv (fun z ↦ exp (c * z)) 0 * s) *
      divisorProductOne (fun z ↦ exp (c * z)) s :=
  (orderLE_cexp_mul c).eq_mul_cexp_logDeriv_mul_divisorProductOne (by fun_prop) (by simp) s

/-- For `f s = 1 - s`, the polynomial has order at most `0 ≤ 1`, `f 0 = 1`, and `logDeriv f 0 = -1`,
recovering `1 - s = exp (-s) * E₁(s)` via `divisorProductOne (1 - ·) s = E₁(s)`. -/
example (s : ℂ) :
    1 - s = (1 - (0 : ℂ)) * exp (logDeriv (fun z : ℂ ↦ 1 - z) 0 * s) *
      divisorProductOne (fun z : ℂ ↦ 1 - z) s := by
  have hord : OrderLE (fun z : ℂ ↦ 1 - z) 1 := by
    have hp := ((1 : Polynomial ℂ) - Polynomial.X).orderLE_eval.mono zero_le_one
    simpa using hp
  exact hord.eq_mul_cexp_logDeriv_mul_divisorProductOne (by fun_prop) (by norm_num) s

end TauCeti
