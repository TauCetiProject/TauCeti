/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Floor.Semiring
public import TauCeti.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Rank windows for theta chains

At scale `x`, the chain length is chosen near `x ^ (1/2 - ε/16)` and the source rank near
`x ^ (9/2 + 10*ε)`. The same choices leave room for the word code, ensure that the host
degree is at least the fourth power of the chain length, and imply the rank bounds in the
Frobenius Riesz comparison. All eventual estimates are uniform in the ranks and host
cardinality within their windows.

The parameter choices are those of L. Alpöge's `Formalism.MainNotions.Lnk.Win_at` and
`Formalism.BasicNotions.Ranks` in his
[Lean formalization](https://github.com/leanprover-community/riemann-hypothesis).
-/

public section

open Filter Real

namespace TauCeti.ThetaLift

/-- Both rank windows contain even positive integers at every scale `x ≥ 1`, provided
the corresponding exponents are nonnegative. -/
theorem exists_even_chain_ranks {x ε : ℝ} (hx : 1 ≤ x) (hε : ε ≤ 8) (hk : -(9 / 20) ≤ ε) :
    ∃ m k : ℕ, Even m ∧ Even k ∧
      x ^ (1 / 2 - ε / 16) ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * x ^ (1 / 2 - ε / 16) ∧
      x ^ (9 / 2 + 10 * ε) ≤ (k : ℝ) ∧ (k : ℝ) ≤ 2 * x ^ (9 / 2 + 10 * ε) := by
  let n (p : ℝ) : ℕ := 2 * ⌈x ^ p / 2⌉₊
  have hn (p : ℝ) (hp : 0 ≤ p) : x ^ p ≤ (n p : ℝ) ∧ (n p : ℝ) ≤ 2 * x ^ p := by
    have hx' := one_le_rpow hx hp
    simp only [n, Nat.cast_mul, Nat.cast_ofNat]
    refine ⟨by linarith [Nat.le_ceil (x ^ p / 2)], ?_⟩
    by_cases h : 2 ≤ x ^ p
    · linarith [Nat.ceil_lt_add_one (by positivity : 0 ≤ x ^ p / 2)]
    · have hceil : ⌈x ^ p / 2⌉₊ ≤ 1 := Nat.ceil_le.mpr (by norm_num; linarith)
      have hceil' : (⌈x ^ p / 2⌉₊ : ℝ) ≤ 1 := by exact_mod_cast hceil
      linarith
  obtain ⟨hm₁, hm₂⟩ := hn (1 / 2 - ε / 16) (by linarith)
  obtain ⟨hk₁, hk₂⟩ := hn (9 / 2 + 10 * ε) (by linarith)
  exact ⟨n _, n _, even_two.mul_right _, even_two.mul_right _, hm₁, hm₂, hk₁, hk₂⟩

/-- The chosen rank windows imply the enlarged `ε/100` windows and the chain-length
bounds used in the Riesz sum comparison. -/
theorem eventually_chain_rank_windows {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ m k : ℝ,
      x ^ (1 / 2 - ε / 16) ≤ m → m ≤ 2 * x ^ (1 / 2 - ε / 16) →
      x ^ (9 / 2 + 10 * ε) ≤ k → k ≤ 2 * x ^ (9 / 2 + 10 * ε) →
      x ^ (1 / 2 - ε / 16 - ε / 100) ≤ m ∧ m ≤ x ^ (1 / 2 - ε / 16 + ε / 100) ∧
      x ^ (9 / 2 + 10 * ε - ε / 100) ≤ k ∧ k ≤ x ^ (9 / 2 + 10 * ε + ε / 100) ∧
      x ^ (1 / 2 - ε) ≤ m ∧ m ≤ x ^ (1 / 2 + ε / 2) := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    eventually_const_mul_rpow_le_rpow (by linarith : 1 / 2 - ε / 16 < 1 / 2 - ε / 16 + ε / 100) 2,
    eventually_const_mul_rpow_le_rpow (by linarith : 9 / 2 + 10 * ε < 9 / 2 + 10 * ε + ε / 100) 2]
    with x hx hm hk m k hm₁ hm₂ hk₁ hk₂
  exact ⟨(rpow_le_rpow_of_exponent_le hx (by linarith)).trans hm₁, hm₂.trans hm,
    (rpow_le_rpow_of_exponent_le hx (by linarith)).trans hk₁, hk₂.trans hk,
    (rpow_le_rpow_of_exponent_le hx (by linarith)).trans hm₁,
    (hm₂.trans hm).trans (rpow_le_rpow_of_exponent_le hx (by linarith))⟩

/-- The host-degree and word-code conditions at the chosen ranks. Here `A` is the number of
infinite places of the CM host, whose degree is `2*A`. The bound on `x` depends on `ε` and
the word-code constant `C`, not on `A`, `m` or `k`. -/
theorem eventually_chain_word_count_bounds {ε : ℝ} (hε : 0 < ε) (C : ℝ) :
    ∀ᶠ x : ℝ in atTop, ∀ A m k : ℝ,
      x ^ (2 + 8 * ε) ≤ A → A ≤ 2 * x ^ (2 + 8 * ε) →
      0 ≤ m → m ≤ 2 * x ^ (1 / 2 - ε / 16) → x ^ (9 / 2 + 10 * ε) ≤ k →
      m ^ 4 ≤ 2 * A ∧ x ^ (ε / 100) * m ^ 5 * (2 * A) * x ^ (2 * ε) ≤ k ∧
      C * m ^ 5 * A * x ^ ε ≤ k := by
  let M : ℝ := 1 / 2 - ε / 16
  let F : ℝ := 2 + 8 * ε
  let K : ℝ := 9 / 2 + 10 * ε
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    eventually_const_mul_rpow_le_rpow (show 4 * M < F by dsimp [M, F]; linarith) 16,
    eventually_const_mul_rpow_le_rpow (show 5 * M + F + 2 * ε + ε / 100 < K by
      dsimp [M, F, K]; linarith) 128,
    eventually_const_mul_rpow_le_rpow (show 5 * M + F + ε < K by
      dsimp [M, F, K]; linarith) (64 * |C|)] with x hx h4 h5 hC A m k hA hA₂ hm₀ hm hk
  have hx₀ := zero_lt_one.trans_le hx
  have hA₀ := (rpow_pos_of_pos hx₀ F).le.trans hA
  have hpow (n : ℕ) : (x ^ M) ^ n = x ^ (n * M) := by
    rw [mul_comm, rpow_mul_natCast hx₀.le]
  refine ⟨?_, ?_, ?_⟩
  · calc
      m ^ 4 ≤ (2 * x ^ M) ^ 4 := by gcongr
      _ = 16 * x ^ (4 * M) := by rw [mul_pow, hpow]; norm_num
      _ ≤ x ^ F := h4
      _ ≤ 2 * A := by linarith
  · calc
      _ ≤ x ^ (ε / 100) * (2 * x ^ M) ^ 5 * (2 * (2 * x ^ F)) * x ^ (2 * ε) := by gcongr
      _ = 128 * x ^ (5 * M + F + 2 * ε + ε / 100) := by
        rw [mul_pow, hpow]
        simp only [rpow_add hx₀, Nat.cast_ofNat]
        ring
      _ ≤ k := h5.trans hk
  · calc
      _ ≤ |C| * (2 * x ^ M) ^ 5 * (2 * x ^ F) * x ^ ε := by gcongr; exact le_abs_self C
      _ = (64 * |C|) * x ^ (5 * M + F + ε) := by
        rw [mul_pow, hpow]
        simp only [rpow_add hx₀, Nat.cast_ofNat]
        ring
      _ ≤ k := hC.trans hk

/-- The selected host cardinality and rank windows place the source rank between `x*m` and
`A²*x^(1/2-ε)`, and give `m ≤ 2*A ≤ k`. The square-root and quadratic rank inequalities
are the corresponding size conditions for the local estimates. -/
theorem eventually_chain_rank_comparison {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ A m k : ℝ,
      x ^ (2 + 8 * ε) ≤ A → A ≤ 2 * x ^ (2 + 8 * ε) →
      x ^ (1 / 2 - ε / 16) ≤ m → m ≤ 2 * x ^ (1 / 2 - ε / 16) →
      x ^ (9 / 2 + 10 * ε) ≤ k → k ≤ 2 * x ^ (9 / 2 + 10 * ε) →
      x * m ≤ k ∧ k ≤ A ^ 2 * x ^ (1 / 2 - ε) ∧ m ≤ 2 * A ∧ 2 * A ≤ k ∧
      √(k / m) ≤ A * x ^ (-ε) ∧ m ^ 2 * x ^ ε ≤ k := by
  let M : ℝ := 1 / 2 - ε / 16
  let F : ℝ := 2 + 8 * ε
  let K : ℝ := 9 / 2 + 10 * ε
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    eventually_const_mul_rpow_le_rpow (show 1 + M < K by dsimp [M, K]; linarith) 2,
    eventually_const_mul_rpow_le_rpow (show K < 2 * F + (1 / 2 - ε) by dsimp [K, F]; linarith) 2,
    eventually_const_mul_rpow_le_rpow (show F < K by dsimp [F, K]; linarith) 4,
    eventually_const_mul_rpow_le_rpow (show K < M + 2 * (F - ε) by dsimp [K, F, M]; linarith) 2,
    eventually_const_mul_rpow_le_rpow (show 2 * M + ε < K by dsimp [K, M]; linarith) 4]
    with x hx hxm hkA hf hsq hm_sq A m k hA hA₂ hm₁ hm₂ hk₁ hk₂
  have hx₀ := zero_lt_one.trans_le hx
  have hm₀ := (rpow_pos_of_pos hx₀ M).trans_le hm₁
  have hA₀ := (rpow_pos_of_pos hx₀ F).trans_le hA
  have hpow (t : ℝ) : (x ^ t) ^ 2 = x ^ (2 * t) := by
    rw [mul_comm, ← rpow_mul_natCast hx₀.le t 2]; norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc
      x * m ≤ x * (2 * x ^ M) := by gcongr
      _ = 2 * x ^ (1 + M) := by rw [rpow_add hx₀, rpow_one]; ring
      _ ≤ k := hxm.trans hk₁
  · refine hk₂.trans (hkA.trans ?_)
    rw [rpow_add hx₀, ← hpow]
    gcongr
  · have hMF : M ≤ F := by dsimp [M, F]; linarith
    exact hm₂.trans (mul_le_mul_of_nonneg_left
      ((rpow_le_rpow_of_exponent_le hx hMF).trans hA) (by norm_num))
  · linarith [hf.trans hk₁]
  · apply (sqrt_le_iff).2
    refine ⟨by positivity, (div_le_iff₀ hm₀).2 (hk₂.trans (hsq.trans ?_))⟩
    have hF : x ^ (F - ε) = x ^ F * x ^ (-ε) := by rw [sub_eq_add_neg, rpow_add hx₀]
    rw [rpow_add hx₀, ← hpow, hF, mul_comm _ m]
    gcongr
  · calc
      _ ≤ (2 * x ^ M) ^ 2 * x ^ ε := by gcongr
      _ = 4 * x ^ (2 * M + ε) := by rw [mul_pow, hpow, rpow_add hx₀]; ring
      _ ≤ k := hm_sq.trans hk₁

/-- The logarithm-dependent comparisons between the chain length and the source rank.
The discriminant enters only through an upper bound on its logarithm. -/
theorem eventually_chain_rank_log_comparison {ε : ℝ} (hε : 0 ≤ ε) (D : ℝ) :
    ∀ᶠ x : ℝ in atTop, ∀ m k rd : ℝ,
      0 ≤ m → m ≤ 2 * x ^ (1 / 2 - ε / 16) → x ^ (9 / 2 + 10 * ε) ≤ k →
      log rd ≤ D * x ^ ε →
      m * √x * log x ≤ k ∧ x ^ (ε / 100) * m ^ 6 * x ^ ε ≤ k * log k ∧
      x ^ (ε / 100) * m ^ 3 * x ^ ε * log rd ≤ k * (log k) ^ 2 := by
  let M : ℝ := 1 / 2 - ε / 16
  let K : ℝ := 9 / 2 + 10 * ε
  filter_upwards [eventually_ge_atTop (exp 1),
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 16)).eventuallyLE,
    eventually_const_mul_rpow_le_rpow (show M + 1 / 2 + 1 / 16 < K by
      dsimp [M, K]; linarith) 2,
    eventually_const_mul_rpow_le_rpow (show 6 * M + ε + ε / 100 < K by
      dsimp [M, K]; linarith) 64,
    eventually_const_mul_rpow_le_rpow (show 3 * M + 2 * ε + ε / 100 < K by
      dsimp [M, K]; linarith) (8 * |D|)] with x hx hlog hb₁ hb₂ hb₃ m k rd hm₀ hm hk hrd
  have hx₀ := (exp_pos _).trans_le hx
  have hlog₁ : 1 ≤ log x := by simpa only [log_exp] using log_le_log (exp_pos 1) hx
  rw [Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg (by positivity)] at hlog
  have hk₀ := (rpow_pos_of_pos hx₀ K).trans_le hk
  have hlogk : 1 ≤ log k := hlog₁.trans <| (le_mul_of_one_le_left (by linarith)
    (show 1 ≤ K by dsimp [K]; linarith)).trans (le_log_of_rpow_le hx₀ hk)
  have hpow (n : ℕ) : (x ^ M) ^ n = x ^ (n * M) := by
    rw [mul_comm, rpow_mul_natCast hx₀.le]
  refine ⟨?_, ?_, ?_⟩
  · calc
      _ ≤ (2 * x ^ M) * x ^ (1 / 2 : ℝ) * x ^ (1 / 16 : ℝ) := by rw [sqrt_eq_rpow]; gcongr
      _ = 2 * x ^ (M + 1 / 2 + 1 / 16) := by simp only [rpow_add hx₀]; ring
      _ ≤ k := hb₁.trans hk
  · calc
      _ ≤ x ^ (ε / 100) * (2 * x ^ M) ^ 6 * x ^ ε := by gcongr
      _ = 64 * x ^ (6 * M + ε + ε / 100) := by
        rw [mul_pow, hpow]; simp only [rpow_add hx₀, Nat.cast_ofNat]; ring
      _ ≤ k := hb₂.trans hk
      _ ≤ _ := le_mul_of_one_le_right hk₀.le hlogk
  · calc
      _ ≤ x ^ (ε / 100) * m ^ 3 * x ^ ε * (|D| * x ^ ε) := by
        gcongr
        exact hrd.trans (mul_le_mul_of_nonneg_right (le_abs_self D) (by positivity))
      _ ≤ x ^ (ε / 100) * (2 * x ^ M) ^ 3 * x ^ ε * (|D| * x ^ ε) := by gcongr
      _ = (8 * |D|) * x ^ (3 * M + 2 * ε + ε / 100) := by
        rw [mul_pow, hpow, show 2 * ε = ε + ε by ring]
        simp only [rpow_add hx₀, Nat.cast_ofNat]; ring
      _ ≤ k := hb₃.trans hk
      _ ≤ _ := le_mul_of_one_le_right hk₀.le (one_le_pow₀ hlogk)

/-- A polynomially bounded host degree has a logarithm small relative to the chain length,
including after squaring. -/
theorem eventually_chain_host_log_bounds {ε : ℝ} (hε : ε < 8) :
    ∀ᶠ x : ℝ in atTop, ∀ f m : ℝ,
      1 ≤ f → f ≤ 4 * x ^ (2 + 8 * ε) → x ^ (1 / 2 - ε / 16) ≤ m →
      log f ≤ √(m / 2 - 1) ∧ (log f) ^ 2 ≤ m ^ 2 * x ^ ε := by
  let M : ℝ := 1 / 2 - ε / 16
  let F : ℝ := 2 + 8 * ε
  have hM : 0 < M := by dsimp [M]; linarith
  by_cases hF : 0 ≤ F
  swap
  · -- A degree at least one cannot lie in a shrinking host window.
    have hlim : Tendsto (fun x : ℝ ↦ 4 * x ^ F) atTop (nhds 0) := by
      simpa only [neg_neg, mul_zero] using
        (tendsto_rpow_neg_atTop (neg_pos.mpr (lt_of_not_ge hF))).const_mul (4 : ℝ)
    filter_upwards [hlim.eventually_lt_const (by norm_num : (0 : ℝ) < 1)] with x hx f _ hf hf₂ _
    exact False.elim (not_lt_of_ge (hf.trans hf₂) hx)
  have hFM : 0 ≤ F + 3 := by linarith
  filter_upwards [eventually_ge_atTop (exp 1), (tendsto_rpow_atTop hM).eventually_ge_atTop (4 : ℝ),
    ((isLittleO_log_rpow_atTop (half_pos (half_pos hM))).const_mul_left (F + 3)).eventuallyLE,
    eventually_const_mul_rpow_le_rpow (half_lt_self hM) 4] with x hx hxM hlog hb f m hf hf₂ hm
  have hx₀ := (exp_pos _).trans_le hx
  have hx₁ := (one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hx
  have hlog₁ : 1 ≤ log x := by simpa only [log_exp] using log_le_log (exp_pos 1) hx
  have hm₄ := hxM.trans hm
  rw [Real.norm_of_nonneg (mul_nonneg hFM (by linarith)),
    Real.norm_of_nonneg (by positivity)] at hlog
  have hlogf : log f ≤ x ^ (M / 2 / 2) := calc
    log f ≤ log (4 * x ^ F) := log_le_log (by linarith) hf₂
    _ ≤ (F + 3) * log x := by
      rw [log_mul (by norm_num) (rpow_pos_of_pos hx₀ F).ne', log_rpow hx₀]
      nlinarith [log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)]
    _ ≤ _ := hlog
  have hlogf_sq : (log f) ^ 2 ≤ x ^ (M / 2) := calc
    _ ≤ (x ^ (M / 2 / 2)) ^ 2 := by gcongr; exact log_nonneg hf
    _ = x ^ (M / 2) := by rw [← rpow_mul_natCast hx₀.le]; congr 1; norm_num
  refine ⟨(le_sqrt (log_nonneg hf) (by linarith)).2 (by linarith [hb.trans hm]), ?_⟩
  calc
    _ ≤ x ^ (M / 2) := hlogf_sq
    _ ≤ x ^ (M * (2 : ℕ) + ε) := by
      apply rpow_le_rpow_of_exponent_le hx₁
      dsimp [F] at hF
      dsimp [M]
      norm_num
      linarith
    _ = (x ^ M) ^ 2 * x ^ ε := by rw [rpow_add hx₀, rpow_mul_natCast hx₀.le]
    _ ≤ _ := by gcongr

/-- The host degree and target rank dominate the remaining logarithmic costs in the
rank conditions. The host degree is `2*A`, and the target rank is `k + m - 1`. -/
theorem eventually_chain_host_size_bounds {ε : ℝ} (hε : 0 ≤ ε) (hε₈ : ε < 8) :
    ∀ᶠ x : ℝ in atTop, ∀ A m k : ℝ,
      x ^ (2 + 8 * ε) ≤ A → A ≤ 2 * x ^ (2 + 8 * ε) →
      x ^ (1 / 2 - ε / 16) ≤ m → x ^ (9 / 2 + 10 * ε) ≤ k →
      let f := 2 * A
      let r := k + m - 1
      x ^ (ε / 100) * ε * log x ≤ r * f * log r ∧ x ^ (ε / 100) * x ^ ε ≤ f * log k ∧
      f ≤ m ^ 2 * A ∧ f ≤ r ^ 2 := by
  let F : ℝ := 2 + 8 * ε
  let K : ℝ := 9 / 2 + 10 * ε
  filter_upwards [eventually_ge_atTop (exp 1),
    (tendsto_rpow_atTop (by linarith : 0 < 1 / 2 - ε / 16)).eventually_ge_atTop (2 : ℝ),
    ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).const_mul_left ε).eventuallyLE,
    eventually_const_mul_rpow_le_rpow (show F < K by dsimp [F, K]; linarith) 4]
    with x hx hxM hlog hF A m k hA₁ hA₂ hm hk f r
  have hx₀ := (exp_pos _).trans_le hx
  have hx₁ := one_le_exp (by norm_num : (0 : ℝ) ≤ 1) |>.trans hx
  have hlog₁ : 1 ≤ log x := by simpa only [log_exp] using log_le_log (exp_pos 1) hx
  have hA : 1 ≤ A := (one_le_rpow hx₁ (show 0 ≤ F by dsimp [F]; linarith)).trans hA₁
  have hm₂ := hxM.trans hm
  have hk₁ := (one_le_rpow hx₁ (show 0 ≤ K by dsimp [K]; linarith)).trans hk
  have hlogk : 1 ≤ log k := hlog₁.trans <| (le_mul_of_one_le_left (by linarith)
    (show 1 ≤ K by dsimp [K]; linarith)).trans (le_log_of_rpow_le hx₀ hk)
  have hf : 1 ≤ f := by dsimp [f]; linarith
  have hkr : k ≤ r := by dsimp [r]; linarith
  have hlogr := hlogk.trans (log_le_log (by linarith) hkr)
  rw [Real.norm_of_nonneg (mul_nonneg hε (by linarith)),
    Real.norm_of_nonneg (by positivity)] at hlog
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc
      _ ≤ x ^ (ε / 100) * x ^ (1 : ℝ) := by rw [mul_assoc]; gcongr
      _ ≤ x ^ K := by
        rw [← rpow_add hx₀]
        exact rpow_le_rpow_of_exponent_le hx₁ (by dsimp [K]; linarith)
      _ ≤ r := hk.trans hkr
      _ ≤ r * f * log r := by
        have hr : 0 ≤ r := by linarith
        exact (le_mul_of_one_le_right hr hf).trans
          (le_mul_of_one_le_right (mul_nonneg hr (by linarith)) hlogr)
  · calc
      _ ≤ x ^ F := by
        rw [← rpow_add hx₀]
        exact rpow_le_rpow_of_exponent_le hx₁ (by dsimp [F]; linarith)
      _ ≤ f := by dsimp [f]; linarith
      _ ≤ f * log k := le_mul_of_one_le_right (by linarith) hlogk
  · dsimp [f]
    gcongr
    nlinarith
  · calc
      f ≤ 4 * x ^ F := by dsimp [f]; linarith
      _ ≤ r := (hF.trans hk).trans hkr
      _ ≤ r ^ 2 := by nlinarith

end TauCeti.ThetaLift
