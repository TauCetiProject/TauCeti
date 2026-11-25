/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Chebyshev
public import TauCeti.NumberTheory.Explicit.MultiplicativeFunctions.Liouville
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Harmonic.Bounds
import TauCeti.Algebra.BigOperators.Intervals
import TauCeti.Analysis.SpecialFunctions.Log.Factorial
import TauCeti.NumberTheory.AbelSummation
import TauCeti.NumberTheory.Chebyshev.Asymptotics

/-!
# The Möbius form of the prime number theorem

From the prime number theorem `ψ(x) ∼ x` (Mathlib's `Chebyshev.isEquivalent_psi_id`) this file
derives, by elementary means, that the Mertens function `M(x) = ∑_{n ≤ x} μ(n)` is `o(x)`, that
the Liouville summatory function `L_λ(x) = ∑_{n ≤ x} λ(n)` is `o(x)`, and that the logarithmic
sum `m(x) = ∑_{n ≤ x} μ(n) / n` tends to `0`.

For `M`, summing `μ · log = -(μ * Λ)` over `n ≤ x` gives
`M(x) log x = ∑_{k ≤ x} μ(k) (log (x / k) - ψ(x / k))`. Writing `ψ(y) = y + (ψ(y) - y)`, the
three resulting sums are `O(x)` (`Real.sum_log_div_le`), `O(x)` (Meissel's identity) and
`o(x log x)` (the prime number theorem in the form `Chebyshev.exists_abs_psi_sub_le` and the
harmonic bound), so `M(x) log x = o(x log x)`.

For `m`, take naturals `N` and `K`. Split Meissel's identity at `K N` at `N`. In the terms with
`N < n ≤ K N`, write the weight `⌊K N / n⌋` as the number of `1 ≤ j < K` with `n ≤ K N / j` and
swap the sums (`Finset.sum_Ioc_div_smul_eq_sum_Ico_sum_Ioc`). This gives
`K N |m(N)| ≤ 1 + N + ∑_{1 ≤ j < K} (|M(K N / j)| + |M(N)|)`. With `M(x) = o(x)` the right side
is at most `1 + N + ε K² N` for large `N`, so `|m(N)| ≤ 2 / K + ε K`.

The argument is adapted from `PrimeNumberTheoremAnd/Consequences.lean` (`M_log_identity`,
`M_isLittleO`, `mu_pnt`, `sum_mobius_floor_tail_isLittleO`, `mu_pnt_alt`) in the
PrimeNumberTheoremAnd project (https://github.com/TauCetiProject/PrimeNumberTheoremAnd, revision
`5a91b7a`).

## Main declarations

* `TauCeti.sum_moebius_mul_log_eq_neg_sum_moebius_mul_psi`:
  `∑_{n ≤ x} μ(n) log n = -∑_{k ≤ x} μ(k) ψ(x / k)`.
* `TauCeti.moebiusSum_mul_log_eq`: `M(x) log x = ∑_{k ≤ x} μ(k) (log (x / k) - ψ(x / k))`.
* `TauCeti.abs_moebiusSum_mul_log_le`: if `|ψ(y) - y| ≤ ε y + C` for `y ≥ 0`, then
  `|M(x)| log x ≤ ε x log x + (2 + ε + C) x + 1` for `x ≥ 1`.
* `TauCeti.moebiusSum_isLittleO`: `M(x) = o(x)`.
* `TauCeti.liouvilleSum_isLittleO`: `L_λ(x) = o(x)`.
* `TauCeti.mul_abs_moebiusDivSum_le`: `K N |m(N)| ≤ 1 + N + ∑_{1 ≤ j < K} (|M(K N / j)| + |M(N)|)`.
* `TauCeti.tendsto_moebiusDivSum_atTop`: `m(x) → 0`.
-/

public section

open Finset Filter Asymptotics
open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt ArithmeticFunction.zeta
  Chebyshev Topology

namespace TauCeti

variable {x : ℝ}

/-! ### The Mertens function -/

private theorem abs_moebius_mul_le (n : ℕ) (t : ℝ) : |(μ n : ℝ) * t| ≤ |t| := by
  rw [abs_mul]
  exact mul_le_of_le_one_left (abs_nonneg t) (mod_cast ArithmeticFunction.abs_moebius_le_one)

/-- `|μ(n) (x / n - ⌊x / n⌋)| ≤ 1` for `x ≥ 0`, as the fractional part lies in `[0, 1)`. -/
private theorem abs_moebius_mul_sub_natFloor_le (hx : 0 ≤ x) (n : ℕ) :
    |(μ n : ℝ) * (x / n - ⌊x / n⌋₊)| ≤ 1 := by
  refine (abs_moebius_mul_le n _).trans (abs_le.mpr ⟨?_, ?_⟩)
  · linarith [Nat.floor_le (div_nonneg hx n.cast_nonneg)]
  · linarith [Nat.lt_floor_add_one (x / n)]

/-- `∑_{n ≤ x} μ(n) log n = -∑_{k ≤ x} μ(k) ψ(x / k)`, the sum over `n ≤ x` of
`μ · log = -(μ * Λ)`. -/
theorem sum_moebius_mul_log_eq_neg_sum_moebius_mul_psi (x : ℝ) :
    ∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) * Real.log n = -∑ k ∈ Icc 1 ⌊x⌋₊, (μ k : ℝ) * ψ (x / k) := by
  have hzeta : (μ : ArithmeticFunction ℝ).pmul ArithmeticFunction.log * ζ = -Λ := by
    ext n
    rw [ArithmeticFunction.coe_mul_zeta_apply]
    simp_rw [ArithmeticFunction.pmul_apply, ArithmeticFunction.intCoe_apply]
    exact ArithmeticFunction.sum_moebius_mul_log_eq
  have hconv : (μ : ArithmeticFunction ℝ).pmul ArithmeticFunction.log = μ * -Λ := by
    rw [← hzeta, mul_comm, mul_assoc, ArithmeticFunction.coe_zeta_mul_coe_moebius, mul_one]
  have hsum := congrArg (fun f : ArithmeticFunction ℝ ↦ ∑ n ∈ Ioc 0 ⌊x⌋₊, f n) hconv
  simp only [ArithmeticFunction.pmul_apply, ArithmeticFunction.intCoe_apply,
    ArithmeticFunction.log_apply, ArithmeticFunction.sum_Ioc_mul_eq_sum_sum,
    neg_apply, sum_neg_distrib, mul_neg] at hsum
  rw [← Icc_add_one_left_eq_Ioc, zero_add] at hsum
  rw [hsum]
  refine congrArg _ (sum_congr rfl fun k _ ↦ ?_)
  rw [Chebyshev.psi, Nat.floor_div_natCast]

/-- `M(x) log x = ∑_{k ≤ x} μ(k) (log (x / k) - ψ(x / k))`. -/
theorem moebiusSum_mul_log_eq (x : ℝ) :
    moebiusSum x * Real.log x =
      ∑ k ∈ Icc 1 ⌊x⌋₊, (μ k : ℝ) * (Real.log (x / k) - ψ (x / k)) := by
  have hterm : ∀ k ∈ Icc 1 ⌊x⌋₊, (μ k : ℝ) * (Real.log (x / k) - ψ (x / k)) =
      (μ k : ℝ) * Real.log x - (μ k : ℝ) * Real.log k - (μ k : ℝ) * ψ (x / k) := by
    intro k hk
    obtain ⟨hk1, hkx⟩ := mem_Icc.mp hk
    have hx : 0 < x := Nat.floor_pos.mp (hk1.trans hkx) |>.trans_lt' one_pos
    rw [Real.log_div hx.ne' (by positivity)]
    ring
  rw [sum_congr rfl hterm, sum_sub_distrib, sum_sub_distrib, ← sum_mul,
    sum_moebius_mul_log_eq_neg_sum_moebius_mul_psi, moebiusSum_def]
  ring

/-- `|∑_{k ≤ x} μ(k) x / k| ≤ x + 1` for `x ≥ 1`, by Meissel's identity. -/
private theorem abs_sum_moebius_mul_div_le (hx1 : 1 ≤ x) :
    |∑ k ∈ Icc 1 ⌊x⌋₊, (μ k : ℝ) * (x / k)| ≤ x + 1 := by
  have hx0 : 0 ≤ x := zero_le_one.trans hx1
  have hsplit : ∑ k ∈ Icc 1 ⌊x⌋₊, (μ k : ℝ) * (x / k) =
      1 + ∑ k ∈ Icc 1 ⌊x⌋₊, (μ k : ℝ) * (x / k - ⌊x / k⌋₊) := by
    rw [← sum_moebius_mul_natFloor_div hx1, ← sum_add_distrib]
    exact sum_congr rfl fun _ _ ↦ by ring
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  linarith [abs_sum_Icc_one_natFloor_le (abs_moebius_mul_sub_natFloor_le hx0) hx0]

/-- If `|ψ(y) - y| ≤ ε y + C` for every `y ≥ 0`, then
`|M(x)| log x ≤ ε x log x + (2 + ε + C) x + 1` for every `x ≥ 1`. For `ε > 0` such a `C` exists by
`Chebyshev.exists_abs_psi_sub_le`. -/
theorem abs_moebiusSum_mul_log_le {ε C : ℝ} (hC : ∀ y, 0 ≤ y → |ψ y - y| ≤ ε * y + C)
    (hx1 : 1 ≤ x) :
    |moebiusSum x| * Real.log x ≤ ε * x * Real.log x + (2 + ε + C) * x + 1 := by
  have hC0 : 0 ≤ C := by simpa using hC 0 le_rfl
  have hε : 0 ≤ ε := by
    by_contra! hε
    have h := hC ((C + 1) / -ε) (div_nonneg (by linarith) (by linarith))
    have hy : ε * ((C + 1) / -ε) = -(C + 1) := by
      rw [div_neg, mul_neg, mul_div_cancel₀ _ hε.ne]
    linarith [abs_nonneg (ψ ((C + 1) / -ε) - (C + 1) / -ε)]
  have hx0 : 0 ≤ x := zero_le_one.trans hx1
  set S := Icc 1 ⌊x⌋₊
  have hk : ∀ k ∈ S, (0 : ℝ) < k ∧ (k : ℝ) ≤ x := fun k hk ↦
    ⟨by exact_mod_cast (mem_Icc.mp hk).1,
      (Nat.cast_le.mpr (mem_Icc.mp hk).2).trans (Nat.floor_le hx0)⟩
  have h1 : |∑ k ∈ S, (μ k : ℝ) * Real.log (x / k)| ≤ x := by
    refine (abs_sum_le_sum_abs _ _).trans
      ((sum_le_sum fun k hkS ↦ ?_).trans (Real.sum_log_div_le hx0))
    refine (abs_moebius_mul_le k _).trans_eq (abs_of_nonneg (Real.log_nonneg ?_))
    exact (one_le_div (hk k hkS).1).mpr (hk k hkS).2
  have h2 := abs_sum_moebius_mul_div_le hx1
  have hharm : ∑ k ∈ S, (k : ℝ)⁻¹ ≤ 1 + Real.log x := by
    simpa [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] using
      harmonic_floor_le_one_add_log x hx1
  have h3 : |∑ k ∈ S, (μ k : ℝ) * (ψ (x / k) - x / k)| ≤ ε * x * (1 + Real.log x) + C * x := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ k ∈ S, |(μ k : ℝ) * (ψ (x / k) - x / k)|
        ≤ ∑ k ∈ S, (ε * x * (k : ℝ)⁻¹ + C) := sum_le_sum fun k hkS ↦
          (abs_moebius_mul_le k _).trans <|
            (hC _ (div_nonneg hx0 (hk k hkS).1.le)).trans_eq (by ring)
      _ = ε * x * ∑ k ∈ S, (k : ℝ)⁻¹ + C * ⌊x⌋₊ := by
        rw [sum_add_distrib, ← mul_sum, sum_const, Nat.card_Icc, add_tsub_cancel_right,
          nsmul_eq_mul, mul_comm C]
      _ ≤ ε * x * (1 + Real.log x) + C * x := by
        gcongr
        exact Nat.floor_le hx0
  have hid : moebiusSum x * Real.log x = ∑ k ∈ S, (μ k : ℝ) * Real.log (x / k) -
      ∑ k ∈ S, (μ k : ℝ) * (x / k) - ∑ k ∈ S, (μ k : ℝ) * (ψ (x / k) - x / k) := by
    rw [moebiusSum_mul_log_eq, ← sum_sub_distrib, ← sum_sub_distrib]
    exact sum_congr rfl fun _ _ ↦ by ring
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  rw [← abs_of_nonneg hlog0, ← abs_mul, hid, abs_of_nonneg hlog0]
  have := abs_sub (∑ k ∈ S, (μ k : ℝ) * Real.log (x / k) - ∑ k ∈ S, (μ k : ℝ) * (x / k))
    (∑ k ∈ S, (μ k : ℝ) * (ψ (x / k) - x / k))
  have := abs_sub (∑ k ∈ S, (μ k : ℝ) * Real.log (x / k)) (∑ k ∈ S, (μ k : ℝ) * (x / k))
  linarith

/-- **The Möbius form of the prime number theorem**: the Mertens function satisfies
`M(x) = o(x)`. -/
theorem moebiusSum_isLittleO : moebiusSum =o[atTop] fun x ↦ x := by
  refine isLittleO_iff.mpr fun c hc ↦ ?_
  set ε := c / 2 with hε_def
  have hε : 0 < ε := half_pos hc
  obtain ⟨C, hC⟩ := Chebyshev.exists_abs_psi_sub_le hε
  have hC0 : 0 ≤ C := by simpa using hC 0 le_rfl
  set D := 3 + ε + C
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (D / ε), eventually_ge_atTop 1]
    with x hlog hx1
  have hx0 : 0 ≤ x := zero_le_one.trans hx1
  have hD : D ≤ ε * Real.log x := by rwa [div_le_iff₀ hε, mul_comm] at hlog
  have hlog0 : 0 < Real.log x := lt_of_lt_of_le (div_pos (by positivity) hε) hlog
  have hM := abs_moebiusSum_mul_log_le hC hx1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hx0]
  refine le_of_mul_le_mul_right ?_ hlog0
  have hc2 : c * x * Real.log x = 2 * (ε * x * Real.log x) := by rw [hε_def]; ring
  linarith [mul_le_mul_of_nonneg_right hD hx0]

/-- The Liouville summatory function satisfies `L_λ(x) = o(x)`. -/
theorem liouvilleSum_isLittleO : liouvilleSum =o[atTop] fun x ↦ x :=
  liouvilleSum_isLittleO_iff.mpr moebiusSum_isLittleO

/-! ### The logarithmic sum -/

/-- `N ≤ K N / j` for `1 ≤ j < K`. -/
private theorem le_mul_div_of_mem_Ico {N K j : ℕ} (hj : j ∈ Ico 1 K) : N ≤ K * N / j :=
  (Nat.le_div_iff_mul_le (mem_Ico.mp hj).1).mpr
    (by rw [mul_comm]; exact Nat.mul_le_mul_right N (mem_Ico.mp hj).2.le)

/-- For naturals `N` and `K`,
`K N |m(N)| ≤ 1 + N + ∑_{1 ≤ j < K} (|M(K N / j)| + |M(N)|)`. -/
theorem mul_abs_moebiusDivSum_le (N K : ℕ) :
    K * N * |moebiusDivSum N| ≤
      1 + N + ∑ j ∈ Ico 1 K, (|moebiusSum ↑(K * N / j)| + |moebiusSum N|) := by
  rcases Nat.eq_zero_or_pos (K * N) with hKN | hKN
  · have : (K : ℝ) * N = 0 := by exact_mod_cast hKN
    rw [this, zero_mul]
    positivity
  have hNK : N ≤ K * N := Nat.le_mul_of_pos_left N (Nat.pos_of_mul_pos_right hKN)
  have hIcc (m : ℕ) : Icc 1 m = Ioc 0 m := by
    rw [← Icc_add_one_left_eq_Ioc, zero_add]
  have hsplit (m : ℕ) (hm : N ≤ m) :
      ∑ n ∈ Ioc N m, (μ n : ℝ) = moebiusSum m - moebiusSum N := by
    rw [moebiusSum_natCast, moebiusSum_natCast, hIcc, hIcc,
      ← sum_Ioc_consecutive _ (Nat.zero_le N) hm]
    ring
  have hmeissel := sum_moebius_mul_natFloor_div (x := ((K * N : ℕ) : ℝ)) (by exact_mod_cast hKN)
  simp only [Nat.floor_div_eq_div, Nat.floor_natCast] at hmeissel
  rw [hIcc, ← sum_Ioc_consecutive _ (Nat.zero_le N) hNK] at hmeissel
  have htail : ∑ n ∈ Ioc N (K * N), (μ n : ℝ) * ↑(K * N / n) =
      ∑ j ∈ Ico 1 K, (moebiusSum ↑(K * N / j) - moebiusSum N) := by
    simp_rw [mul_comm (μ _ : ℝ), ← nsmul_eq_mul]
    rw [sum_Ioc_div_smul_eq_sum_Ico_sum_Ioc]
    exact sum_congr rfl fun j hj ↦ hsplit _ (le_mul_div_of_mem_Ico hj)
  have hhead : ∑ n ∈ Icc 1 N, (μ n : ℝ) * ↑(K * N / n) =
      1 - ∑ j ∈ Ico 1 K, (moebiusSum ↑(K * N / j) - moebiusSum N) := by
    rw [← htail, hIcc]
    linarith
  have hmain : (K * N : ℝ) * moebiusDivSum N =
      (1 - ∑ j ∈ Ico 1 K, (moebiusSum ↑(K * N / j) - moebiusSum N)) +
        ∑ n ∈ Icc 1 N, (μ n : ℝ) * (((K * N : ℕ) : ℝ) / n - ⌊((K * N : ℕ) : ℝ) / n⌋₊) := by
    rw [← hhead, moebiusDivSum_natCast, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun n _ ↦ ?_
    rw [Nat.floor_div_eq_div]
    push_cast
    ring
  have herr := abs_sum_Icc_one_natFloor_le
    (abs_moebius_mul_sub_natFloor_le (x := ((K * N : ℕ) : ℝ)) (by positivity)) N.cast_nonneg
  rw [Nat.floor_natCast] at herr
  have hj : |∑ j ∈ Ico 1 K, (moebiusSum ↑(K * N / j) - moebiusSum N)| ≤
      ∑ j ∈ Ico 1 K, (|moebiusSum ↑(K * N / j)| + |moebiusSum N|) :=
    (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun _ _ ↦ abs_sub _ _)
  rw [← abs_of_nonneg (by positivity : (0 : ℝ) ≤ K * N), ← abs_mul, hmain]
  refine (abs_add_le _ _).trans ?_
  linarith [abs_sub (1 : ℝ) (∑ j ∈ Ico 1 K, (moebiusSum ↑(K * N / j) - moebiusSum N)),
    abs_one (α := ℝ)]

/-- **The logarithmic form of the prime number theorem**: `m(x) = ∑_{n ≤ x} μ(n) / n → 0`. -/
theorem tendsto_moebiusDivSum_atTop : Tendsto moebiusDivSum atTop (𝓝 0) := by
  have hnat : Tendsto (fun N : ℕ ↦ moebiusDivSum N) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨K, hK⟩ := exists_nat_gt (4 / ε)
    have hK0 : (0 : ℝ) < K := (div_pos (by norm_num) hε).trans hK
    have hεK : 4 < ε * K := by rwa [div_lt_iff₀ hε, mul_comm] at hK
    set δ := ε / (8 * K)
    have hδ : 0 < δ := by positivity
    obtain ⟨T, hT⟩ := eventually_atTop.mp (moebiusSum_isLittleO.def hδ)
    obtain ⟨N₀, hN₀⟩ := exists_nat_ge T
    refine ⟨max N₀ 1, fun N hN ↦ ?_⟩
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (le_max_right _ _).trans hN
    have hTN : T ≤ N := hN₀.trans (by exact_mod_cast (le_max_left _ _).trans hN)
    have hM (m : ℕ) (hm : N ≤ m) : |moebiusSum m| ≤ δ * m := by
      simpa [Real.norm_eq_abs] using hT m (hTN.trans (by exact_mod_cast hm))
    have hterm : ∀ j ∈ Ico 1 K, |moebiusSum ↑(K * N / j)| + |moebiusSum N| ≤ 2 * δ * (K * N) := by
      intro j hj
      have hj1 := (mem_Ico.mp hj).1
      have h1 : ((K * N / j : ℕ) : ℝ) ≤ K * N := by exact_mod_cast Nat.div_le_self _ _
      have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hj1.trans (mem_Ico.mp hj).2.le
      have h2 : (N : ℝ) ≤ K * N := le_mul_of_one_le_left (Nat.cast_nonneg N) hK1
      linarith [hM _ (le_mul_div_of_mem_Ico hj), hM N le_rfl, mul_le_mul_of_nonneg_left h1 hδ.le,
        mul_le_mul_of_nonneg_left h2 hδ.le]
    have hsum : ∑ j ∈ Ico 1 K, (|moebiusSum ↑(K * N / j)| + |moebiusSum N|) ≤
        K * (2 * δ * (K * N)) := by
      refine (sum_le_sum hterm).trans ?_
      rw [sum_const, Nat.card_Ico, nsmul_eq_mul]
      gcongr
      exact_mod_cast Nat.sub_le K 1
    have hbound := mul_abs_moebiusDivSum_le N K
    have hδK : K * (2 * δ * (K * N)) = ε * K * N / 4 := by
      simp only [δ]
      field_simp
      ring
    rw [Real.dist_eq, sub_zero]
    have hKN : (0 : ℝ) < K * N := by positivity
    refine lt_of_mul_lt_mul_left ?_ hKN.le
    -- `ε K N > 4 N ≥ 2 (1 + N)`, so `1 + N + ε K N / 4 < ε K N`.
    have h4N : 4 * N < ε * K * N := mul_lt_mul_of_pos_right hεK (by linarith)
    linarith
  exact (hnat.comp tendsto_nat_floor_atTop).congr fun x ↦ moebiusDivSum_natFloor x

end TauCeti
