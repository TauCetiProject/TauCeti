/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import TauCeti.Analysis.CompletelyMonotone.BernsteinMeasures
public import TauCeti.Analysis.CompletelyMonotone.BernsteinProkhorov

/-!
# Bernstein kernel convergence and Prokhorov identification

The final analytic step of the Chafaï proof of Bernstein's theorem: the Bernstein kernel
`φ_n(x, ·)` converges uniformly to the Laplace kernel `e^{-x·}` on `ℝ≥0`
(`kernel_uniform_conv`), so the finite-`n` Chafaï identities pass to the weak limit
(`prokhorov_limit_identification`), yielding the Laplace representation
`f t = L + ∫ e^{-tp} dμ₀`.

## Main declarations

* `TauCeti.kernel_uniform_conv`: uniform convergence of `φ_n(x, ·)` to `e^{-x·}` on `[0, ∞)`.
* `TauCeti.prokhorov_limit_identification`: the weak-limit Laplace representation of `f`.

## References

* D. Chafaï, *Aspects of the Bernstein theorem* (2013).
-/

public section

open MeasureTheory Set Filter
open scoped ContDiff NNReal Topology

namespace TauCeti

variable {C : ℝ}

/-- **Uniform convergence of the Bernstein kernel** on `[0, ∞)` for fixed `x > 0`:
For any `ε > 0`, eventually in `n`, `|φ_n(x,p) - e^{-xp}| < ε` for ALL `p ≥ 0`.

The proof uses: (1) uniform convergence on `[0, R]` for any `R`, and
(2) exponential tail decay: for `p ≥ R`, both `φ_n(x,p) ≤ e^{-xR+o(1)}` and
`e^{-xp} ≤ e^{-xR}`, so `|φ_n - e^{-xp}| ≤ 2e^{-xR}` which is small for large `R`. -/
private lemma kernel_uniform_conv (x : ℝ) (hx : 0 < x) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∀ p, 0 ≤ p →
      |bernstein_kernel n x p - Real.exp (-(x * p))| < ε := by
  have hkernel_le : ∀ n, 2 ≤ n → ∀ p, 0 ≤ p →
      bernstein_kernel n x p ≤ Real.exp (-(x * p)) := by
    intro n hn p hp
    rw [bernstein_kernel_of_two_le hn]
    by_cases h : 1 - x * p / ↑(n - 1) ≤ 0
    · simp only [max_eq_right h]
      rw [zero_pow (by omega : n - 1 ≠ 0)]
      exact le_of_lt (Real.exp_pos _)
    · push Not at h; rw [max_eq_left h.le]
      have hle : 1 - x * p / ↑(n - 1) ≤ Real.exp (-(x * p / ↑(n - 1))) := by
        linarith [Real.add_one_le_exp (-(x * p / ↑(n - 1)))]
      calc (1 - x * p / ↑(n - 1)) ^ (n - 1)
          ≤ (Real.exp (-(x * p / ↑(n - 1)))) ^ (n - 1) := by
            apply pow_le_pow_left₀ h.le hle
        _ = Real.exp (↑(n - 1) * -(x * p / ↑(n - 1))) := by
            rw [← Real.exp_nat_mul]
        _ = Real.exp (-(x * p)) := by
            congr 1
            have : (↑(n - 1) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
            field_simp
  have hkernel_nn : ∀ n p, 0 ≤ bernstein_kernel n x p := by
    intro n p; exact bernstein_kernel_nonneg n x p
  have htail : Tendsto (fun R => Real.exp (-(x * R))) atTop (nhds 0) := by
    apply Tendsto.comp Real.tendsto_exp_neg_atTop_nhds_zero
    exact Filter.tendsto_id.const_mul_atTop hx
  obtain ⟨R₀, hR₀⟩ := Metric.tendsto_atTop.mp htail (ε / 2) (half_pos hε)
  set R := max R₀ 1
  have hR_tail : Real.exp (-(x * R)) < ε / 2 := by
    have h1 := hR₀ R (le_max_left _ _)
    rwa [dist_zero_right, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)] at h1
  have hunif : ∃ N : ℕ, ∀ n, N ≤ n → ∀ p, 0 ≤ p → p ≤ R →
      |bernstein_kernel n x p - Real.exp (-(x * p))| < ε / 2 := by
    -- Quantitative bound: |(1-u/m)^m - e^{-u}| ≤ u²/(m-u) via log(1-t) ≥ -t-t²/(1-t)
    set C := x * R
    have hR_pos : 0 < R := lt_of_lt_of_le one_pos (le_max_right R₀ 1)
    have hC_pos : 0 < C := mul_pos hx hR_pos
    obtain ⟨N₀, hN₀⟩ := exists_nat_gt (C + 2 + 2 * C ^ 2 / ε)
    refine ⟨N₀, fun n hn p hp hpR => ?_⟩
    have hn_gt : (↑n : ℝ) > C + 2 + 2 * C ^ 2 / ε :=
      lt_of_lt_of_le hN₀ (Nat.cast_le.mpr hn)
    have haux : 0 ≤ 2 * C ^ 2 / ε := div_nonneg (by positivity) hε.le
    have hn_ge2 : 2 ≤ n := by exact_mod_cast (show (2 : ℝ) < ↑n by linarith [hC_pos]).le
    have hle := hkernel_le n hn_ge2 p hp
    rw [abs_of_nonpos (by linarith), neg_sub]
    set m := n - 1
    have hm_pos : (0 : ℝ) < ↑m := Nat.cast_pos.mpr (by omega)
    have hm_eq : (↑m : ℝ) = ↑n - 1 := by
      rw [Nat.cast_sub (show 1 ≤ n by omega)]; simp
    have hxp_nn : 0 ≤ x * p := mul_nonneg hx.le hp
    have hxp_le_C : x * p ≤ C := mul_le_mul_of_nonneg_left hpR hx.le
    have hm_gt_C : C < ↑m := by linarith
    set u := x * p / ↑m with hu_def
    have hu_nn : 0 ≤ u := div_nonneg hxp_nn hm_pos.le
    have hu_lt_1 : u < 1 := by rw [div_lt_one hm_pos]; linarith
    have h1u : 0 < 1 - u := by linarith
    have hkernel_eq : bernstein_kernel n x p = (1 - u) ^ m := by
      rw [bernstein_kernel_of_two_le hn_ge2]
      congr 1; exact max_eq_left (by linarith)
    rw [hkernel_eq]
    set b := ↑m * u ^ 2 / (1 - u) with hb_def
    have hb_nn : 0 ≤ b :=
      div_nonneg (mul_nonneg (Nat.cast_nonneg m) (sq_nonneg u)) h1u.le
    have hmu : ↑m * u = x * p := by simp only [hu_def]; field_simp
    -- Lower bound: (1-u)^m ≥ exp(-xp - b) via log(1-u) ≥ -u - u²/(1-u)
    have hpow_ge : (1 - u) ^ m ≥ Real.exp (-(x * p) - b) := by
      have heq : (1 - u) ^ m = Real.exp (↑m * Real.log (1 - u)) := by
        rw [← Real.rpow_natCast (1 - u) m, Real.rpow_def_of_pos h1u, mul_comm]
      rw [heq]; gcongr
      rw [show -(x * p) - b = ↑m * (-u - u ^ 2 / (1 - u)) from by
        rw [← hmu, hb_def]; ring]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg m)
      have habs : |u| < 1 := by rwa [abs_of_nonneg hu_nn]
      have hlog := Real.abs_log_sub_add_sum_range_le habs 1
      simp only [Finset.sum_range_one, Nat.cast_zero, zero_add, div_one, pow_one] at hlog
      rw [abs_of_nonneg hu_nn, show u ^ (1 + 1) = u ^ 2 from by ring] at hlog
      linarith [(abs_le.mp hlog).1]
    -- Chain: exp(-xp) - (1-u)^m ≤ exp(-xp) - exp(-xp-b) ≤ b
    have hstep : Real.exp (-(x * p)) - (1 - u) ^ m ≤ b := by
      suffices h : Real.exp (-(x * p)) - Real.exp (-(x * p) - b) ≤ b from by linarith
      have : Real.exp (-(x * p) - b) = Real.exp (-(x * p)) * Real.exp (-b) := by
        rw [← Real.exp_add]; ring_nf
      rw [this]; nlinarith [Real.exp_pos (-(x * p)), Real.exp_pos (-b),
        Real.exp_le_one_iff.mpr (neg_nonpos.mpr hxp_nn), Real.add_one_le_exp (-b)]
    -- b = (xp)²/(m-xp) ≤ C²/(m-C) < ε/2
    have hb_eq : b = (x * p) ^ 2 / (↑m - x * p) := by
      simp only [hb_def, hu_def]; field_simp
    have hm_gt_C' : 0 < ↑m - C := by linarith
    have hb_le : b ≤ C ^ 2 / (↑m - C) := by
      rw [hb_eq]
      exact div_le_div₀ (sq_nonneg C) (sq_le_sq' (by linarith) hxp_le_C)
        hm_gt_C' (by linarith)
    have hfinal : C ^ 2 / (↑m - C) < ε / 2 := by
      rw [div_lt_div_iff₀ hm_gt_C' (by positivity : (0:ℝ) < 2)]
      have h1 : ↑m - C > 2 * C ^ 2 / ε := by linarith [hm_eq]
      have h2 : ε * (↑m - C) > ε * (2 * C ^ 2 / ε) := mul_lt_mul_of_pos_left h1 hε
      rw [mul_div_cancel₀ _ (ne_of_gt hε)] at h2; linarith
    linarith
  obtain ⟨N₁, hN₁⟩ := hunif
  refine ⟨max N₁ 2, fun n hn p hp => ?_⟩
  have hn2 : 2 ≤ n := le_trans (le_max_right N₁ 2) hn
  by_cases hpR : p ≤ R
  · linarith [hN₁ n (le_trans (le_max_left _ _) hn) p hp hpR]
  · push Not at hpR
    have h1 := hkernel_le n hn2 p hp
    rw [abs_of_nonpos (by linarith)]
    have h2 : Real.exp (-(x * p)) ≤ Real.exp (-(x * R)) := by
        apply Real.exp_le_exp_of_le
        linarith [mul_le_mul_of_nonneg_left (le_of_lt hpR) (le_of_lt hx)]
    linarith [hkernel_nn n p]

-- **Kernel approximation error → 0**: For measures `σ_n` supported on `[0,∞)`
-- with uniformly bounded mass, the integral of the difference
-- `φ_{n+2}(x,·) - e^{-x·}` against `σ_n` tends to zero.
--
-- For `x = 0` the integrand is identically 0. For `x > 0`, the convergence
-- `φ_n(x,p) → e^{-xp}` is UNIFORM in `p ∈ [0,∞)` (both functions have exponential
-- tail decay), so `|∫(φ_n - e^{-xp})dσ_n| ≤ sup|φ_n - e^{-xp}| · σ_n(ℝ) → 0`.
private lemma kernel_approx_error_tendsto
    (σ : ℕ → Measure ℝ≥0) (l : Filter ℕ) (hl : l ≤ atTop)
    (hfin : ∀ n, IsFiniteMeasure (σ n))
    (hmass : ∀ n, (σ n) Set.univ ≤ ENNReal.ofReal C)
    (x : ℝ) (hx : 0 ≤ x) :
    Tendsto (fun n => ∫ p : ℝ≥0, (bernstein_kernel (n + 2) x (p : ℝ) -
        Real.exp (-(x * (p : ℝ)))) ∂(σ n)) l (nhds 0) := by
  by_cases hx0 : x = 0
  · -- x = 0: integrand = 0 since bernstein_kernel n 0 p = 1 = exp(0) for n ≥ 2
    subst hx0
    suffices h : ∀ n, ∫ p : ℝ≥0, (bernstein_kernel (n + 2) 0 (p : ℝ) -
        Real.exp (-(0 * (p : ℝ)))) ∂(σ n) = 0 by
      simp only [h]; exact tendsto_const_nhds
    intro n; apply integral_eq_zero_of_ae; apply ae_of_all; intro p
    change bernstein_kernel (n + 2) 0 (p : ℝ) - Real.exp (-(0 * (p : ℝ))) = 0
    rw [bernstein_kernel_of_two_le (by omega : 2 ≤ n + 2)]
    simp
  · -- x > 0: uniform convergence on [0,∞) + mass bound
    have hx_pos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    rw [Metric.tendsto_nhds]; intro ε hε
    have hmax_pos : 0 < max C 1 := lt_max_of_lt_right one_pos
    obtain ⟨N, hN⟩ := kernel_uniform_conv x hx_pos
      (ε / (2 * max C 1)) (div_pos hε (by positivity))
    filter_upwards [hl (eventually_ge_atTop N)] with n hn
    rw [dist_zero_right]
    haveI := hfin n
    have hnN : N ≤ n + 2 := le_trans hn (Nat.le_add_right _ _)
    calc ‖∫ p : ℝ≥0, (bernstein_kernel (n + 2) x (p : ℝ) -
          Real.exp (-(x * (p : ℝ)))) ∂(σ n)‖
        ≤ ∫ p : ℝ≥0, ‖bernstein_kernel (n + 2) x (p : ℝ) -
            Real.exp (-(x * (p : ℝ)))‖ ∂(σ n) :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ _, (ε / (2 * max C 1)) ∂(σ n) := by
          apply integral_mono_of_nonneg
            (ae_of_all _ fun p => norm_nonneg _) (integrable_const _)
          rw [EventuallyLE]
          exact ae_of_all _ fun p => by
            rw [Real.norm_eq_abs]
            exact le_of_lt (hN (n + 2) hnN (p : ℝ) p.2)
      _ = ε / (2 * max C 1) * ((σ n) Set.univ).toReal := by
          simp [MeasureTheory.integral_const, smul_eq_mul, Measure.real, mul_comm]
      _ ≤ ε / (2 * max C 1) * max C 1 := by
          apply mul_le_mul_of_nonneg_left _ (le_of_lt (div_pos hε (by positivity)))
          exact ENNReal.toReal_le_of_le_ofReal (le_of_lt hmax_pos)
            (le_trans (hmass n) (ENNReal.ofReal_le_ofReal (le_max_left C 1)))
      _ = ε / 2 := by field_simp
      _ < ε := half_lt_self hε

/-- The integral `∫ φ_{n+2}(x,p) dσ_n` converges to `∫ e^{-xp} dμ₀` along
the subsequence. Decomposes as:
  `∫ φ_{n_k+2} dσ_{n_k} = ∫ (φ_{n_k+2} - e^{-xp}) dσ_{n_k} + ∫ e^{-xp} dσ_{n_k}`
where the first term → 0 (`kernel_approx_error_tendsto`) and the second
term → `∫ e^{-xp} dμ₀` (`tendsto_exp_integral`). -/
private lemma integral_bernstein_kernel_tendsto
    (σ : ℕ → Measure ℝ≥0) (l : Filter ℕ) (μ₀ : Measure ℝ≥0)
    [IsFiniteMeasure μ₀]
    (hfin : ∀ n, IsFiniteMeasure (σ n))
    (hl : l ≤ atTop)
    (hweak : ∀ (g : BoundedContinuousFunction ℝ≥0 ℝ),
      Tendsto (fun n => ∫ p, g p ∂(σ n)) l (nhds (∫ p, g p ∂μ₀)))
    (hmass : ∀ n, (σ n) Set.univ ≤ ENNReal.ofReal C)
    (x : ℝ) (hx : 0 ≤ x) :
    Tendsto (fun n => ∫ p : ℝ≥0, bernstein_kernel (n + 2) x (p : ℝ) ∂(σ n)) l
      (nhds (∫ p : ℝ≥0, Real.exp (-(x * (p : ℝ))) ∂μ₀)) := by
  -- Strategy: show the difference with ∫ e^{-xp} dσ_{φ(k)} → 0 (kernel error),
  -- and ∫ e^{-xp} dσ_{φ(k)} → ∫ e^{-xp} dμ₀ (weak convergence).
  -- Combined: ∫ φ_{φ(k)+2} dσ_{φ(k)} → ∫ e^{-xp} dμ₀.
  have hterm1 := kernel_approx_error_tendsto (C := C) σ l hl hfin hmass x hx
  have hterm2 := tendsto_exp_integral σ l μ₀ hweak x hx
  -- The sum of a net tending to 0 and one tending to L tends to L.
  rw [show (∫ p : ℝ≥0, Real.exp (-(x * (p : ℝ))) ∂μ₀) =
      0 + ∫ p : ℝ≥0, Real.exp (-(x * (p : ℝ))) ∂μ₀ from
    (zero_add _).symm]
  apply Tendsto.congr _ (hterm1.add hterm2)
  intro n; haveI := hfin n
  -- ∫ (φ - e^{-xp}) dσ + ∫ e^{-xp} dσ = ∫ φ dσ (linearity).
  have hbk_int : Integrable (fun p : ℝ≥0 => bernstein_kernel (n + 2) x (p : ℝ)) (σ n) := by
    apply Integrable.mono' (integrable_const (1 : ℝ))
    · exact ((measurable_bernstein_kernel (n + 2) x).comp
        measurable_subtype_coe).aestronglyMeasurable
    · apply ae_of_all
      intro p
      simp only [Real.norm_eq_abs]
      rw [bernstein_kernel_of_two_le (by omega : 2 ≤ n + 2)]
      simp only [show n + 2 - 1 = n + 1 from by omega]
      have hmax : max (1 - x * (p : ℝ) / ↑(n + 1)) 0 ≤ 1 := by
        apply max_le _ (by norm_num)
        have : 0 ≤ x * (p : ℝ) / ↑(n + 1) := div_nonneg (mul_nonneg hx p.2) (by positivity)
        linarith
      have : 0 ≤ max (1 - x * (p : ℝ) / ↑(n + 1)) 0 := le_max_right _ _
      rw [abs_of_nonneg (pow_nonneg this _)]
      exact pow_le_one₀ (n := n + 1) this hmax
  have hexp_int : Integrable (fun p : ℝ≥0 => Real.exp (-(x * (p : ℝ)))) (σ n) := by
    apply Integrable.mono' (integrable_const (1 : ℝ))
    · exact Measurable.aestronglyMeasurable (by fun_prop)
    · apply ae_of_all
      intro p
      simp only [Real.norm_eq_abs]
      have : Real.exp (-(x * (p : ℝ))) ≤ 1 :=
        Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hx p.2))
      rw [abs_of_pos (Real.exp_pos _)]
      exact this
  linarith [MeasureTheory.integral_sub hbk_int hexp_int]

private lemma diagonal_convergence
    (f : ℝ → ℝ) (L : ℝ)
    (σ : ℕ → Measure ℝ≥0) (l : Filter ℕ) (μ₀ : Measure ℝ≥0)
    [NeBot l]
    [IsFiniteMeasure μ₀]
    (hfin : ∀ n, IsFiniteMeasure (σ n))
    (hl : l ≤ atTop)
    (hweak : ∀ (g : BoundedContinuousFunction ℝ≥0 ℝ),
      Tendsto (fun n => ∫ p, g p ∂(σ n)) l (nhds (∫ p, g p ∂μ₀)))
    (hmass : ∀ n, (σ n) Set.univ ≤ ENNReal.ofReal C)
    (x : ℝ) (hx : 0 ≤ x)
    (hident : ∀ n, f x - L = ∫ p : ℝ≥0, bernstein_kernel (n + 2) x (p : ℝ) ∂(σ n)) :
    f x - L = ∫ p : ℝ≥0, Real.exp (-(x * (p : ℝ))) ∂μ₀ := by
  -- The net ∫ φ_{n+2}(x,p) dσ_n = f(x) - L for all n (constant).
  have hconst : ∀ n, ∫ p : ℝ≥0, bernstein_kernel (n + 2) x (p : ℝ) ∂(σ n) = f x - L :=
    fun n => (hident n).symm
  -- The same net converges to ∫ e^{-xp} dμ₀.
  have htends := integral_bernstein_kernel_tendsto (C := C)
    σ l μ₀ hfin hl hweak hmass x hx
  -- A constant net converging to a limit implies the constant equals the limit.
  exact tendsto_nhds_unique (tendsto_const_nhds.congr (fun n => (hconst n).symm)) htends

lemma prokhorov_limit_identification (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f)
    (L : ℝ) (_hL : Tendsto f Filter.atTop (nhds L)) (_hL_nn : 0 ≤ L)
    (hmass_bound : ∀ n, 2 ≤ n →
      (chafaiRescaled f n) Set.univ ≤ ENNReal.ofReal (f 0 - L))
    (hfin : ∀ n, 2 ≤ n → IsFiniteMeasure (chafaiRescaled f n))
    (hidentity : ∀ n, 2 ≤ n → ∀ x, 0 ≤ x →
      f x - L = ∫ p : ℝ≥0, bernstein_kernel n x (p : ℝ) ∂(chafaiRescaled f n)) :
    ∃ (μ₀ : Measure ℝ≥0), IsFiniteMeasure μ₀ ∧
      ∀ t, 0 ≤ t → f t = L + ∫ p : ℝ≥0, Real.exp (-(t * (p : ℝ))) ∂μ₀ := by
  -- Shift indices: work with σ(n) = chafaiRescaled f (n+2) to avoid the n ≥ 2 condition
  set σ := fun n => chafaiRescaled f (n + 2) with hσ_def
  have hfin_σ : ∀ n, IsFiniteMeasure (σ n) := fun n => hfin (n + 2) (by omega)
  have hmass_σ : ∀ n, (σ n) Set.univ ≤ ENNReal.ofReal (f 0 - L) :=
    fun n => hmass_bound (n + 2) (by omega)
  have hident_σ : ∀ n, 2 ≤ n + 2 → ∀ x, 0 ≤ x →
      f x - L = ∫ p : ℝ≥0, bernstein_kernel (n + 2) x (p : ℝ) ∂(σ n) :=
    fun n hn2 x hx => hidentity (n + 2) hn2 x hx
  -- Step 1: Prokhorov extraction — get subsequence σ_{φ(k)} → μ₀
  have htight_σ : ∀ ε : ℝ, 0 < ε →
      ∃ K : Set ℝ≥0, IsCompact K ∧ ∀ n, (σ n) Kᶜ ≤ ENNReal.ofReal ε := by
    /- Tightness from CM structure (genuinely >30 lines):
       For ε > 0, choose x₀ = 1/K for large K (continuity of f at 0 gives
       f(0) - f(1/K) < ε(1 - e⁻¹)). From hident_σ with x = 0:
       toReal(σ_n(univ)) = f(0) - L (exact mass). With x = 1/K:
       f(1/K) - L = ∫ φ_{n+2}(1/K, p) dσ_n. The difference:
       ∫ (1 - φ_{n+2}(1/K, p)) dσ_n = f(0) - f(1/K).
       For p > K: φ_{n+2}(1/K, p) = max(1-(p/K)/(n+1), 0)^{n+1}
       ≤ exp(-p/K) ≤ exp(-1) (by one_sub_div_pow_le_exp_neg),
       so 1 - φ ≥ 1 - e⁻¹. Therefore:
       (1 - e⁻¹) · toReal(σ_n(Ioi K)) ≤ ∫_{Ioi K} (1-φ) dσ_n
       ≤ ∫ (1-φ) dσ_n = f(0) - f(1/K) < ε(1 - e⁻¹).
       So toReal(σ_n(Ioi K)) < ε, hence σ_n(Ioi K) ≤ ENNReal.ofReal ε.
       Blocking: the ℝ-integral decomposition ∫(1-φ) = ∫1 - ∫φ requires
       integrability of φ_{n+2} wrt σ_n (bounded measurable on finite measure),
       and the lower bound ∫_{Ioi K}(1-φ) ≥ (1-e⁻¹)·toReal(σ_n(Ioi K))
       requires converting between set integrals and measure evaluations
       via integral_indicator/setIntegral and ENNReal.le_ofReal_iff_toReal_le.
       The continuity-at-0 step needs ContinuousOn.tendsto or Tendsto
       from hcm.contDiffOn.continuousOn. Total: ~35 lines. -/
    intro ε hε
    -- Mass identity: (σ n univ).toReal = f 0 - L (from hident at x=0, kernel=1)
    have hmass_real : ∀ n, (σ n Set.univ).toReal = f 0 - L := by
      intro n; haveI := hfin_σ n
      have h1 := hident_σ n (by omega) 0 le_rfl
      have hkernel_zero :
          (fun p : ℝ≥0 => bernstein_kernel (n + 2) 0 (p : ℝ)) = fun _ => (1 : ℝ) := by
        ext p
        rw [bernstein_kernel_of_two_le (by omega : 2 ≤ n + 2)]
        simp only [zero_mul, zero_div, sub_zero, zero_le_one, max_eq_left, one_pow]
      rw [hkernel_zero] at h1
      simp only [MeasureTheory.integral_const, smul_eq_mul, mul_one] at h1
      -- h1 : f 0 - L = ∫ 1 dσ_n = (σ_n).real univ
      rw [show (σ n).real Set.univ = (σ n Set.univ).toReal from by
        simp [Measure.real]] at h1
      linarith
    -- Integral bound: (1-exp(-x₀K)) · toReal(σ_n(Ioi K)) ≤ f(0)-f(x₀)
    have hbound : ∀ (x₀ K : ℝ) (hx₀ : 0 < x₀) (hK : 0 < K), ∀ n,
        (1 - Real.exp (-(x₀ * K))) *
          (σ n (Set.Ioi (⟨K, hK.le⟩ : ℝ≥0))).toReal ≤ f 0 - f x₀ := by
      intro x₀ K hx₀ hK n; haveI := hfin_σ n
      let Knn : ℝ≥0 := ⟨K, hK.le⟩
      -- f(0)-f(x₀) = mass - ∫ kernel (from hmass_real + hident_σ)
      have h_diff : f 0 - f x₀ = (σ n Set.univ).toReal -
          ∫ p : ℝ≥0, bernstein_kernel (n + 2) x₀ (p : ℝ) ∂(σ n) := by
        linarith [hmass_real n, hident_σ n (by omega) x₀ hx₀.le]
      -- ∫ kernel ≤ mass - (1-exp(-x₀K))·σ(Ioi K).toReal
      -- ↔ (1-exp(-x₀K))·σ(Ioi K).toReal ≤ mass - ∫ kernel = f(0)-f(x₀)
      rw [h_diff]
      -- ∫ kernel ≤ σ(Iic K) + exp(-x₀K)·σ(Ioi K) = σ(univ) - (1-exp(-x₀K))·σ(Ioi K)
      have hmeas : (σ n Set.univ).toReal =
          (σ n (Set.Iic Knn)).toReal + (σ n (Set.Ioi Knn)).toReal := by
        rw [← Set.Iic_union_Ioi,
          measure_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi,
          ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
      set c := Real.exp (-(x₀ * K))
      set g := fun p : ℝ≥0 => Set.indicator (Set.Iic Knn) (fun _ => (1:ℝ)) p +
        Set.indicator (Set.Ioi Knn) (fun _ => c) p
      have hg_val : ∫ p, g p ∂(σ n) =
          (σ n (Set.Iic Knn)).toReal + c * (σ n (Set.Ioi Knn)).toReal := by
        simp only [g]
        rw [integral_add ((integrable_const (1:ℝ)).indicator measurableSet_Iic)
          ((integrable_const c).indicator measurableSet_Ioi),
          integral_indicator_const _ measurableSet_Iic,
          integral_indicator_const _ measurableSet_Ioi,
          Measure.real, Measure.real, smul_eq_mul, smul_eq_mul, mul_one, mul_comm]
      have hkernel_int :
          Integrable (fun p : ℝ≥0 => bernstein_kernel (n + 2) x₀ (p : ℝ)) (σ n) := by
        apply Integrable.mono' (integrable_const (1 : ℝ))
        · exact ((measurable_bernstein_kernel (n + 2) x₀).comp
            measurable_subtype_coe).aestronglyMeasurable
        · apply ae_of_all
          intro p
          simp only [Real.norm_eq_abs]
          rw [bernstein_kernel_of_two_le (by omega : 2 ≤ n + 2)]
          simp only [show n + 2 - 1 = n + 1 from by omega]
          have hmax : max (1 - x₀ * (p : ℝ) / ↑(n + 1)) 0 ≤ 1 := by
            apply max_le _ (by norm_num)
            have : 0 ≤ x₀ * (p : ℝ) / ↑(n + 1) :=
              div_nonneg (mul_nonneg hx₀.le p.2) (by positivity)
            linarith
          have : 0 ≤ max (1 - x₀ * (p : ℝ) / ↑(n + 1)) 0 := le_max_right _ _
          rw [abs_of_nonneg (pow_nonneg this _)]
          exact pow_le_one₀ (n := n + 1) this hmax
      have hkernel_le_g :
          (fun p : ℝ≥0 => bernstein_kernel (n + 2) x₀ (p : ℝ)) ≤ᶠ[MeasureTheory.ae (σ n)] g := by
        apply ae_of_all
        intro p
        by_cases hpK : p ≤ Knn
        · have hkernel_le_one : bernstein_kernel (n + 2) x₀ (p : ℝ) ≤ 1 := by
            rw [bernstein_kernel_of_two_le (by omega : 2 ≤ n + 2)]
            simp only [show n + 2 - 1 = n + 1 from by omega]
            have hmax : max (1 - x₀ * (p : ℝ) / ↑(n + 1)) 0 ≤ 1 := by
              apply max_le _ (by norm_num)
              have : 0 ≤ x₀ * (p : ℝ) / ↑(n + 1) :=
                div_nonneg (mul_nonneg hx₀.le p.2) (by positivity)
              linarith
            exact pow_le_one₀ (le_max_right _ _) hmax
          have hg_eq : g p = 1 := by
            unfold g
            rw [Set.indicator_of_mem (show p ∈ Set.Iic Knn from hpK),
              Set.indicator_of_notMem (show p ∉ Set.Ioi Knn from not_lt.mpr hpK)]
            simp
          simpa [hg_eq] using hkernel_le_one
        · have hpK' : Knn < p := lt_of_not_ge hpK
          have hpK'_real : K < (p : ℝ) := by exact_mod_cast hpK'
          have hkernel_le_exp :
              bernstein_kernel (n + 2) x₀ (p : ℝ) ≤ Real.exp (-(x₀ * (p : ℝ))) := by
            have hxp_nonneg : 0 ≤ x₀ * (p : ℝ) := mul_nonneg hx₀.le p.2
            rw [bernstein_kernel_of_two_le (by omega : 2 ≤ n + 2)]
            simp only [show n + 2 - 1 = n + 1 from by omega]
            by_cases hxp : x₀ * (p : ℝ) ≤ ↑(n + 1)
            · have hmax_eq : max (1 - x₀ * (p : ℝ) / ↑(n + 1)) 0 =
                  1 - x₀ * (p : ℝ) / ↑(n + 1) := by
                apply max_eq_left
                have hdiv : x₀ * (p : ℝ) / ↑(n + 1) ≤ 1 := by
                  exact (div_le_iff₀ (by positivity : (0 : ℝ) < ↑(n + 1))).2 (by simpa using hxp)
                linarith
              rw [hmax_eq]
              simpa using Real.one_sub_div_pow_le_exp_neg (n := n + 1) (t := x₀ * (p : ℝ)) hxp
            · have hmax_eq : max (1 - x₀ * (p : ℝ) / ↑(n + 1)) 0 = 0 := by
                apply max_eq_right
                push Not at hxp
                have : 1 < x₀ * (p : ℝ) / ↑(n + 1) := by
                  exact (lt_div_iff₀ (by positivity : (0 : ℝ) < ↑(n + 1))).2 (by simpa using hxp)
                linarith
              rw [hmax_eq, zero_pow (by positivity)]
              exact le_of_lt (Real.exp_pos _)
          have hexp_le : Real.exp (-(x₀ * (p : ℝ))) ≤ c := by
            dsimp [c]
            apply Real.exp_le_exp.mpr
            nlinarith [mul_le_mul_of_nonneg_left hpK'_real.le hx₀.le]
          have hg_eq : g p = c := by
            unfold g
            rw [Set.indicator_of_notMem (show p ∉ Set.Iic Knn from not_le.mpr hpK'),
              Set.indicator_of_mem (show p ∈ Set.Ioi Knn from hpK')]
            simp
          rw [hg_eq]
          exact hkernel_le_exp.trans hexp_le
      have hle : ∫ p : ℝ≥0, bernstein_kernel (n+2) x₀ (p : ℝ) ∂(σ n) ≤ ∫ p, g p ∂(σ n) := by
        apply integral_mono_ae
          hkernel_int
          ((integrable_const (1:ℝ)).indicator measurableSet_Iic |>.add
            ((integrable_const c).indicator measurableSet_Ioi))
          hkernel_le_g
      linarith
    -- Choose x₀ > 0 with f(0)-f(x₀) < ε/2 (continuity at 0)
    have hx₀ : ∃ x₀ : ℝ, 0 < x₀ ∧ f 0 - f x₀ < ε / 2 := by
      have hcont : ContinuousWithinAt f (Set.Ici 0) 0 :=
        hcm.contDiffOn.continuousOn.continuousWithinAt (Set.mem_Ici.mpr le_rfl)
      rw [Metric.continuousWithinAt_iff] at hcont
      obtain ⟨δ, hδ, hclose⟩ := hcont (ε / 2) (half_pos hε)
      refine ⟨δ / 2, by positivity, ?_⟩
      have hdist : dist (f (δ/2)) (f 0) < ε / 2 :=
        hclose (Set.mem_Ici.mpr (by positivity)) (by
          rw [dist_zero_right, Real.norm_eq_abs, abs_of_pos (by positivity)]; linarith)
      rw [Real.dist_eq] at hdist
      rw [show f 0 - f (δ/2) = -(f (δ/2) - f 0) from by ring]
      linarith [neg_abs_le (f (δ/2) - f 0)]
    obtain ⟨x₀, hx₀_pos, hx₀_bound⟩ := hx₀
    -- Choose K = max(1/x₀, 1) so exp(-x₀K) ≤ exp(-1) < 1/2
    set K : ℝ := max (1 / x₀) 1
    have hK : 0 < K := by dsimp [K]; exact lt_max_of_lt_right one_pos
    let Knn : ℝ≥0 := ⟨K, hK.le⟩
    refine ⟨Set.Icc 0 Knn, isCompact_Icc, fun n => ?_⟩
    -- σ_n(Ioi K) ≤ ofReal ε
    have hexp : Real.exp (-(x₀ * K)) ≤ 1 / 2 := by
      calc Real.exp (-(x₀ * K))
          ≤ Real.exp (-1) := by
            apply Real.exp_le_exp_of_le; linarith [show 1 / x₀ ≤ K from le_max_left _ _,
              mul_le_mul_of_nonneg_left (show 1 / x₀ ≤ K from le_max_left _ _) hx₀_pos.le,
              div_mul_cancel₀ (1 : ℝ) (ne_of_gt hx₀_pos)]
        _ ≤ 1 / 2 := by
            rw [Real.exp_neg]
            -- 1/e ≤ 1/2 ↔ 2 ≤ e
            rw [inv_le_comm₀ (Real.exp_pos 1) (by positivity : (0:ℝ) < 1/2)]
            linarith [Real.add_one_le_exp (1 : ℝ)]
    have hcompl : (Set.Icc 0 Knn : Set ℝ≥0)ᶜ = Set.Ioi Knn := by
      ext p
      simp
    rw [hcompl]
    have h_toReal_le : (σ n (Set.Ioi Knn)).toReal ≤ ε := by
      have h1 := hbound x₀ K hx₀_pos hK n
      have h2 : (1 : ℝ) / 2 ≤ 1 - Real.exp (-(x₀ * max (1/x₀) 1)) := by linarith
      have h2' : (1 : ℝ) / 2 ≤ 1 - Real.exp (-(x₀ * K)) := by
        dsimp [K] at hexp ⊢
        linarith
      have h3 : 0 ≤ (σ n (Set.Ioi Knn)).toReal := ENNReal.toReal_nonneg
      nlinarith
    rwa [← ENNReal.ofReal_toReal (ne_of_lt (measure_lt_top (σ n) _)),
      ENNReal.ofReal_le_ofReal_iff hε.le]
  obtain ⟨μ₀, U, hUle, hfin_μ, hmass_μ, hweak⟩ :=
    finite_measure_cluster_limit σ (f 0 - L) hmass_σ htight_σ
  -- Step 2: Verify the Laplace identity via diagonal convergence
  refine ⟨μ₀, hfin_μ, fun t ht => ?_⟩
  -- We need: f t = L + ∫ e^{-tp} dμ₀, i.e., f t - L = ∫ e^{-tp} dμ₀
  have hdiag := diagonal_convergence (C := f 0 - L) f L
    σ (U : Filter ℕ) μ₀ hfin_σ hUle hweak hmass_σ t ht
    (fun n => hident_σ n (by omega) t ht)
  linarith


end TauCeti
