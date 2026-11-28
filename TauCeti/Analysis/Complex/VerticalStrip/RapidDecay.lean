/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import TauCeti.Analysis.Complex.CanonicalProduct.RankBound
public import TauCeti.Analysis.Complex.FiniteOrder
import Mathlib.Analysis.Analytic.Polynomial
import TauCeti.Analysis.Complex.CanonicalProduct.FiniteRank
import TauCeti.Analysis.MvPolynomial.L1Norm
import TauCeti.Analysis.Normed.Ring.PowSubPow

/-!
# Rapid decay on vertical strips and interpolation of polynomial zero fibres

A function `ν` on `ℂⁿ = ι → ℂ` decays rapidly on vertical strips
(`TauCeti.HasRapidVerticalDecay`) if on every strip `‖Re z‖ ≤ M`, for the sup norm of the real
parts, `(1 + ‖z‖) ^ r * ‖ν z‖` is bounded for every `r : ℕ`. Such functions are the spectral
symbols from which Schwartz multipliers on real reductive groups are built, so one needs entire
functions with prescribed zeros and this decay.

The damping factor `exp (∑ i, z i ^ (2 * m))` with `m` odd has real part
`-‖z‖ ^ (2 * m) + O((1 + ‖z‖) ^ (2 * m - 1))` on each vertical strip, because
`(i y) ^ (2 * m) = -y ^ (2 * m)`. It therefore beats every bound `exp (C * (1 + ‖z‖) ^ D)`
with `D < 2 * m` there (`TauCeti.hasRapidVerticalDecay_mul_cexp_sum_pow`), and it has no zeros.
Composing an entire function `ψ` of finite order with a polynomial `q` gives such a bound, so
`ψ (q z) * exp (∑ i, z i ^ (2 * m))` is an entire, rapidly vertically decreasing function whose
zero set is exactly `q⁻¹ (ψ⁻¹ 0)`. Applied to a canonical product, this realizes `q⁻¹ Λ` as
such a zero set for every set `Λ ⊆ ℂ` of finite rank.

## Main definitions

* `TauCeti.HasRapidVerticalDecay`: rapid decay on vertical strips.

## Main results

* `TauCeti.HasRapidVerticalDecay.mul_of_norm_le`: rapid decay survives multiplication by a
  function of polynomial growth on vertical strips.
* `TauCeti.hasRapidVerticalDecay_mul_cexp_sum_pow`: the damping factor turns a bound
  `exp (C * (1 + ‖z‖) ^ D)` into rapid vertical decay.
* `TauCeti.exists_differentiable_hasRapidVerticalDecay_eq_zero_iff`: for `ψ` entire of finite
  order and a polynomial `q`, some entire rapidly vertically decreasing `ν` vanishes exactly
  where `ψ (q z) = 0`.
* `Set.HasRankBound.exists_differentiable_hasRapidVerticalDecay_eq_zero_iff`: the same for
  the zero set `q⁻¹ Λ` with `Λ` of finite rank.

## References

* R. Beuzart-Plessis, Y. Liu, W. Zhang, X. Zhu, *Isolation of cuspidal spectrum, with application
  to the Gan–Gross–Prasad conjecture*, Ann. of Math. (2) **194** (2021), §2.1, Proposition 2.4
  and Remark 2.7.
-/

public section

open Complex Finset MvPolynomial

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- A function on `ι → ℂ` *decays rapidly on vertical strips* if on each strip `‖Re z‖ ≤ M`,
for the sup norm of the real parts, `(1 + ‖z‖) ^ r * ‖ν z‖` is bounded for every `r : ℕ`. -/
def HasRapidVerticalDecay (ν : (ι → ℂ) → ℂ) : Prop :=
  ∀ M : ℝ, ∀ r : ℕ, ∃ C : ℝ, ∀ z : ι → ℂ, ‖fun i ↦ (z i).re‖ ≤ M → (1 + ‖z‖) ^ r * ‖ν z‖ ≤ C

variable {μ ν : (ι → ℂ) → ℂ}

/-- The defining property of `HasRapidVerticalDecay`. -/
theorem hasRapidVerticalDecay_def : HasRapidVerticalDecay ν ↔ ∀ M : ℝ, ∀ r : ℕ, ∃ C : ℝ,
    ∀ z : ι → ℂ, ‖fun i ↦ (z i).re‖ ≤ M → (1 + ‖z‖) ^ r * ‖ν z‖ ≤ C :=
  Iff.rfl

/-- The zero function decays rapidly on vertical strips. -/
theorem hasRapidVerticalDecay_zero : HasRapidVerticalDecay (0 : (ι → ℂ) → ℂ) :=
  fun _ _ ↦ ⟨0, fun _ _ ↦ by simp⟩

namespace HasRapidVerticalDecay

/-- A function dominated by a rapidly vertically decreasing function decays rapidly. -/
theorem mono (hν : HasRapidVerticalDecay ν) (h : ∀ z, ‖μ z‖ ≤ ‖ν z‖) :
    HasRapidVerticalDecay μ := by
  intro M r
  obtain ⟨C, hC⟩ := hν M r
  exact ⟨C, fun z hz ↦ (mul_le_mul_of_nonneg_left (h z) (by positivity)).trans (hC z hz)⟩

/-- Rapid vertical decay is closed under addition. -/
theorem add (hμ : HasRapidVerticalDecay μ) (hν : HasRapidVerticalDecay ν) :
    HasRapidVerticalDecay (μ + ν) := by
  intro M r
  obtain ⟨C, hC⟩ := hμ M r
  obtain ⟨C', hC'⟩ := hν M r
  refine ⟨C + C', fun z hz ↦ ?_⟩
  calc
    _ ≤ (1 + ‖z‖) ^ r * (‖μ z‖ + ‖ν z‖) := by gcongr; exact norm_add_le _ _
    _ = (1 + ‖z‖) ^ r * ‖μ z‖ + (1 + ‖z‖) ^ r * ‖ν z‖ := mul_add _ _ _
    _ ≤ C + C' := add_le_add (hC z hz) (hC' z hz)

/-- Rapid vertical decay survives multiplication by a function `μ` of polynomial growth on
vertical strips: on each strip `‖Re z‖ ≤ M`, `‖μ z‖ ≤ C * (1 + ‖z‖) ^ k` for some `C` and `k`. -/
theorem mul_of_norm_le (hν : HasRapidVerticalDecay ν)
    (hμ : ∀ M : ℝ, ∃ C : ℝ, ∃ k : ℕ, ∀ z : ι → ℂ, ‖fun i ↦ (z i).re‖ ≤ M →
      ‖μ z‖ ≤ C * (1 + ‖z‖) ^ k) :
    HasRapidVerticalDecay (μ * ν) := by
  intro M r
  obtain ⟨C, k, hC⟩ := hμ M
  obtain ⟨C', hC'⟩ := hν M (r + k)
  refine ⟨max C 0 * C', fun z hz ↦ ?_⟩
  have hμz : ‖μ z‖ ≤ max C 0 * (1 + ‖z‖) ^ k :=
    (hC z hz).trans (by gcongr; exact le_max_left _ _)
  calc
    (1 + ‖z‖) ^ r * ‖(μ * ν) z‖ ≤ (1 + ‖z‖) ^ r * (max C 0 * (1 + ‖z‖) ^ k * ‖ν z‖) := by
      rw [Pi.mul_apply, norm_mul]
      gcongr
    _ = max C 0 * ((1 + ‖z‖) ^ (r + k) * ‖ν z‖) := by ring
    _ ≤ max C 0 * C' := mul_le_mul_of_nonneg_left (hC' z hz) (le_max_right C 0)

/-- Rapid vertical decay is preserved by scalar multiples. -/
theorem const_mul (hν : HasRapidVerticalDecay ν) (c : ℂ) :
    HasRapidVerticalDecay fun z ↦ c * ν z :=
  hν.mul_of_norm_le (μ := fun _ ↦ c) fun _ ↦ ⟨‖c‖, 0, fun _ _ ↦ by simp⟩

end HasRapidVerticalDecay

/-! ### The damping factor -/

/-- On a vertical strip `|Re w| ≤ M`, the real part of `w ^ (2 * m)` for odd `m` is at most
`-‖w‖ ^ (2 * m) + 2 (2 m) M ‖w‖ ^ (2 * m - 1)`, since `(i y) ^ (2 * m) = -y ^ (2 * m)`. -/
private theorem re_pow_le {m : ℕ} (hm : Odd m) {M : ℝ} {w : ℂ} (hw : |w.re| ≤ M) :
    (w ^ (2 * m)).re ≤ -‖w‖ ^ (2 * m) + 2 * (2 * m) * M * ‖w‖ ^ (2 * m - 1) := by
  have hy : |w.im| ≤ ‖w‖ := abs_im_le_norm w
  have hmax : max ‖w‖ ‖I * w.im‖ = ‖w‖ := by simpa using hy
  -- The imaginary part alone contributes `-|Im w| ^ (2 * m)`.
  have hI : ((I * w.im) ^ (2 * m)).re = -|w.im| ^ (2 * m) := by
    rw [mul_pow, pow_mul, I_sq, hm.neg_one_pow, (even_two_mul m).pow_abs, ← ofReal_pow,
      neg_one_mul, neg_re, ofReal_re]
  -- Replacing `I * Im w` by `w` changes the power by at most `|Re w| (2 m) ‖w‖ ^ (2 m - 1)`.
  have hdiff : ‖w ^ (2 * m) - (I * w.im) ^ (2 * m)‖ ≤ M * (2 * m) * ‖w‖ ^ (2 * m - 1) := by
    refine (norm_pow_sub_pow_le _ _ _).trans ?_
    have hsub : w - I * w.im = w.re := by apply Complex.ext <;> simp
    rw [hsub, hmax, norm_real, Real.norm_eq_abs]
    push_cast
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hw (by positivity))
      (by positivity)
  have hnorm : ‖w‖ ^ (2 * m) - |w.im| ^ (2 * m) ≤ M * (2 * m) * ‖w‖ ^ (2 * m - 1) := by
    refine (le_abs_self _).trans ((abs_pow_sub_pow_le _ _ _).trans ?_)
    have hre : ‖w‖ - |w.im| ≤ |w.re| := by linarith [norm_le_abs_re_add_abs_im w]
    rw [abs_of_nonneg (sub_nonneg.mpr hy), abs_norm, abs_abs, max_eq_left hy]
    push_cast
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hre.trans hw) (by positivity))
      (by positivity)
  have hre := re_le_norm (w ^ (2 * m) - (I * w.im) ^ (2 * m))
  rw [sub_re, hI] at hre
  linarith

/-- On a vertical strip `‖Re z‖ ≤ M`, the real part of `∑ i, z i ^ (2 * m)` for odd `m` is at
most `-‖z‖ ^ (2 * m) + K ‖z‖ ^ (2 * m - 1)` with `K = 2 (2 m) M |ι|`. -/
private theorem re_sum_pow_le {m : ℕ} (hm : Odd m) {M : ℝ} {z : ι → ℂ}
    (hz : ‖fun i ↦ (z i).re‖ ≤ M) :
    (∑ i, z i ^ (2 * m)).re ≤
      -‖z‖ ^ (2 * m) + 2 * (2 * m) * M * Fintype.card ι * ‖z‖ ^ (2 * m - 1) := by
  have hM : 0 ≤ M := (norm_nonneg _).trans hz
  have hzi : ∀ i, |(z i).re| ≤ M := fun i ↦
    (Real.norm_eq_abs _ ▸ norm_le_pi_norm (fun i ↦ (z i).re) i).trans hz
  -- The sup norm is one of the coordinate norms, so its power is at most the sum of powers.
  have hsup : ‖z‖ ^ (2 * m) ≤ ∑ i, ‖z i‖ ^ (2 * m) := by
    rcases isEmpty_or_nonempty ι with hι | hι
    · simp [Subsingleton.elim z 0, hm.pos.ne']
    · obtain ⟨i, -, hi⟩ := exists_mem_eq_sup univ univ_nonempty fun i ↦ ‖z i‖₊
      have hzi : ‖z‖ = ‖z i‖ := by rw [Pi.norm_def, hi, coe_nnNorm]
      rw [hzi]
      exact single_le_sum (f := fun i ↦ ‖z i‖ ^ (2 * m)) (fun _ _ ↦ by positivity) (mem_univ i)
  have hsum : ∑ i, ‖z i‖ ^ (2 * m - 1) ≤ Fintype.card ι * ‖z‖ ^ (2 * m - 1) := by
    simpa using sum_le_card_nsmul univ (fun i ↦ ‖z i‖ ^ (2 * m - 1)) _
      fun i _ ↦ pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm z i) _
  rw [re_sum]
  calc
    _ ≤ ∑ i, (-‖z i‖ ^ (2 * m) + 2 * (2 * m) * M * ‖z i‖ ^ (2 * m - 1)) :=
      sum_le_sum fun i _ ↦ re_pow_le hm (hzi i)
    _ = -∑ i, ‖z i‖ ^ (2 * m) + 2 * (2 * m) * M * ∑ i, ‖z i‖ ^ (2 * m - 1) := by
      rw [sum_add_distrib, sum_neg_distrib, mul_sum]
    _ ≤ _ := by
      have := mul_le_mul_of_nonneg_left hsum (by positivity : (0 : ℝ) ≤ 2 * (2 * m) * M)
      nlinarith

/-- For `B, t ≥ 0`, `B (1 + t) ^ n - t ^ (n + 1) ≤ (B + n + 1) ^ (n + 1)`: replacing `t` by
`u = 1 + t` costs at most `(n + 1) u ^ n`, and `B' u ^ n - u ^ (n + 1)` is negative once
`u ≥ B'`. -/
private theorem mul_one_add_pow_sub_pow_succ_le {B t : ℝ} (hB : 0 ≤ B) (ht : 0 ≤ t) (n : ℕ) :
    B * (1 + t) ^ n - t ^ (n + 1) ≤ (B + (n + 1)) ^ (n + 1) := by
  set u := 1 + t
  have hu : 0 ≤ u := by positivity
  have htu : u ^ (n + 1) - t ^ (n + 1) ≤ (n + 1) * u ^ n := by
    have h := (le_abs_self _).trans (abs_pow_sub_pow_le u t (n + 1))
    rwa [show u - t = 1 by ring, abs_one, abs_of_nonneg hu, abs_of_nonneg ht,
      max_eq_left (by linarith : t ≤ u), one_mul, Nat.add_sub_cancel, Nat.cast_succ] at h
  set B' := B + (n + 1)
  have hB' : 0 ≤ B' := by positivity
  have hpoly : B' * u ^ n - u ^ (n + 1) ≤ B' ^ (n + 1) := by
    rcases le_total u B' with huB | huB
    · have : B' * u ^ n ≤ B' * B' ^ n := by gcongr
      rw [pow_succ' B']
      nlinarith [pow_nonneg hu (n + 1)]
    · have : B' * u ^ n ≤ u * u ^ n := by gcongr
      rw [pow_succ' u]
      nlinarith [pow_nonneg hB' (n + 1)]
  simp only [B'] at hpoly
  nlinarith

/-- **Vertical damping.** If `‖Φ z‖ ≤ exp (C * (1 + ‖z‖) ^ D)` everywhere and `m` is odd with
`D < 2 * m`, then `Φ z * exp (∑ i, z i ^ (2 * m))` decays rapidly on vertical strips. -/
theorem hasRapidVerticalDecay_mul_cexp_sum_pow {Φ : (ι → ℂ) → ℂ} {C : ℝ} {D m : ℕ}
    (hm : Odd m) (hD : D < 2 * m) (hΦ : ∀ z, ‖Φ z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ D)) :
    HasRapidVerticalDecay fun z ↦ Φ z * cexp (∑ i, z i ^ (2 * m)) := by
  intro M r
  obtain ⟨n, hn⟩ : ∃ n, 2 * m = n + 1 := ⟨2 * m - 1, by have := hm.pos; omega⟩
  have hn1 : 2 * m - 1 = n := by omega
  have hD' : D ≤ n := by omega
  have hn0 : n ≠ 0 := by have := hm.pos; omega
  set M' := max M 0
  set K : ℝ := 2 * (2 * m) * M' * Fintype.card ι
  set B : ℝ := r + |C| + K
  have hB : 0 ≤ B := by positivity
  refine ⟨Real.exp ((B + (n + 1)) ^ (n + 1)), fun z hz ↦ ?_⟩
  set t := ‖z‖
  set u := 1 + t
  have ht : 0 ≤ t := norm_nonneg z
  have hu : 1 ≤ u := le_add_of_nonneg_right ht
  have hre : (∑ i, z i ^ (2 * m)).re ≤ -t ^ (n + 1) + K * t ^ n := by
    simpa [hn, hn1, K] using re_sum_pow_le hm (hz.trans (le_max_left M 0))
  -- Each term of the exponent is at most a multiple of `u ^ n`.
  have hr : (1 + t) ^ r ≤ Real.exp (r * u ^ n) :=
    calc
      (1 + t) ^ r ≤ Real.exp t ^ r := by gcongr; linarith [Real.add_one_le_exp t]
      _ = Real.exp (r * t) := (Real.exp_natCast_mul ..).symm
      _ ≤ _ := by
        gcongr
        exact (by linarith : t ≤ u).trans (le_self_pow₀ hu hn0)
  have hC : C * u ^ D ≤ |C| * u ^ n :=
    (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hu hD') (abs_nonneg C))
  have hKt : K * t ^ n ≤ K * u ^ n := by gcongr; linarith
  rw [norm_mul, norm_exp]
  calc
    (1 + t) ^ r * (‖Φ z‖ * Real.exp (∑ i, z i ^ (2 * m)).re) ≤
        Real.exp (r * u ^ n) * (Real.exp (C * u ^ D) * Real.exp (-t ^ (n + 1) + K * t ^ n)) := by
      gcongr
      exact hΦ z
    _ = Real.exp (r * u ^ n + C * u ^ D + (-t ^ (n + 1) + K * t ^ n)) := by
      simp only [Real.exp_add]
      ring
    _ ≤ Real.exp (B * (1 + t) ^ n - t ^ (n + 1)) := by
      gcongr
      simp only [B]
      linarith
    _ ≤ _ := Real.exp_le_exp.mpr (mul_one_add_pow_sub_pow_succ_le hB ht n)

/-- The Gaussian `exp (∑ i, z i ^ 2)` decays rapidly on vertical strips: there its norm is
`exp (∑ i, (Re z i) ^ 2 - (Im z i) ^ 2)`. -/
theorem hasRapidVerticalDecay_cexp_sum_sq :
    HasRapidVerticalDecay fun z : ι → ℂ ↦ cexp (∑ i, z i ^ 2) := by
  simpa using hasRapidVerticalDecay_mul_cexp_sum_pow (ι := ι) (Φ := fun _ ↦ 1) (C := 0) (D := 0)
    odd_one (by norm_num) fun _ ↦ by simp

/-! ### Interpolation of polynomial zero fibres -/

/-- **Interpolation of a polynomial zero fibre**, for `ψ` with an explicit growth bound: if `ψ` is
entire with `‖ψ w‖ ≤ exp (C * (1 + ‖w‖) ^ d)` and `q` is a polynomial, some entire function
decaying rapidly on vertical strips vanishes exactly where `ψ (q z) = 0`. -/
theorem exists_differentiable_hasRapidVerticalDecay_eq_zero_iff_of_norm_le {ψ : ℂ → ℂ}
    (hψ : Differentiable ℂ ψ) {C : ℝ} {d : ℕ}
    (hbound : ∀ w, ‖ψ w‖ ≤ Real.exp (C * (1 + ‖w‖) ^ d)) (q : MvPolynomial ι ℂ) :
    ∃ ν : (ι → ℂ) → ℂ, Differentiable ℂ ν ∧ HasRapidVerticalDecay ν ∧
      ∀ z, ν z = 0 ↔ ψ (eval z q) = 0 := by
  set e := q.totalDegree
  set L := q.l1Norm
  have hL : 0 ≤ L := l1Norm_nonneg q
  -- The polynomial grows at most like `(1 + ‖z‖) ^ e`.
  have hq : ∀ z : ι → ℂ, 1 + ‖eval z q‖ ≤ (1 + L) * (1 + ‖z‖) ^ e := by
    intro z
    have hmax : max 1 ‖z‖ ≤ 1 + ‖z‖ := max_le (by linarith [norm_nonneg z]) (by linarith)
    have hpow : 1 ≤ (1 + ‖z‖) ^ e := one_le_pow₀ (by linarith [norm_nonneg z])
    have h : ‖eval z q‖ ≤ L * (1 + ‖z‖) ^ e :=
      (norm_eval_le_l1Norm_mul_max_one_pow q z).trans (by gcongr)
    nlinarith
  -- Hence `ψ ∘ q` satisfies a bound of the same shape, with exponent `d * e`.
  have hcomp : ∀ z : ι → ℂ,
      ‖ψ (eval z q)‖ ≤ Real.exp (max C 0 * (1 + L) ^ d * (1 + ‖z‖) ^ (d * e)) := by
    intro z
    calc
      ‖ψ (eval z q)‖ ≤ Real.exp (C * (1 + ‖eval z q‖) ^ d) := hbound _
      _ ≤ Real.exp (max C 0 * (1 + ‖eval z q‖) ^ d) := by gcongr; exact le_max_left C 0
      _ ≤ Real.exp (max C 0 * ((1 + L) * (1 + ‖z‖) ^ e) ^ d) := by
        gcongr
        exact hq z
      _ = _ := by rw [mul_pow, ← pow_mul, mul_comm e d, mul_assoc]
  refine ⟨fun z ↦ ψ (eval z q) * cexp (∑ i, z i ^ (2 * (2 * (d * e) + 1))), ?_,
    hasRapidVerticalDecay_mul_cexp_sum_pow (odd_two_mul_add_one _) (by omega) hcomp,
    fun z ↦ by simp [exp_ne_zero]⟩
  have hq' : Differentiable ℂ fun z : ι → ℂ ↦ eval z q :=
    differentiableOn_univ.mp (AnalyticOnNhd.eval_mvPolynomial q).differentiableOn
  exact (hψ.comp hq').mul (by fun_prop)

/-- **Interpolation of a polynomial zero fibre.** If `ψ` is entire of finite order and `q` is a
polynomial on `ι → ℂ`, some entire function decaying rapidly on vertical strips vanishes exactly
on `q⁻¹ (ψ⁻¹ 0)`. -/
theorem exists_differentiable_hasRapidVerticalDecay_eq_zero_iff {ψ : ℂ → ℂ}
    (hψ : Differentiable ℂ ψ) (horder : IsFiniteOrder ψ) (q : MvPolynomial ι ℂ) :
    ∃ ν : (ι → ℂ) → ℂ, Differentiable ℂ ν ∧ HasRapidVerticalDecay ν ∧
      ∀ z, ν z = 0 ↔ ψ (eval z q) = 0 :=
  let ⟨_, _, _, hbound⟩ := horder.exists_norm_le_exp_mul_one_add_norm_pow hψ.continuous
  exists_differentiable_hasRapidVerticalDecay_eq_zero_iff_of_norm_le hψ hbound q

/-- **Interpolation of the pullback of a set of finite rank.** If `Λ ⊆ ℂ` has a rank bound and `q`
is a polynomial on `ι → ℂ`, some entire function decaying rapidly on vertical strips vanishes
exactly on `q⁻¹ Λ`. It is obtained from the canonical product of `Λ`. -/
theorem _root_.Set.HasRankBound.exists_differentiable_hasRapidVerticalDecay_eq_zero_iff
    {Λ : Set ℂ} {p : ℕ} (h : Λ.HasRankBound p) (q : MvPolynomial ι ℂ) :
    ∃ ν : (ι → ℂ) → ℂ, Differentiable ℂ ν ∧ HasRapidVerticalDecay ν ∧
      ∀ z, ν z = 0 ↔ eval z q ∈ Λ := by
  obtain ⟨ν, hν, hdecay, hzero⟩ :=
    exists_differentiable_hasRapidVerticalDecay_eq_zero_iff_of_norm_le
      h.differentiable_canonicalProduct h.norm_canonicalProduct_le_exp q
  exact ⟨ν, hν, hdecay, fun z ↦ (hzero z).trans h.canonicalProduct_eq_zero_iff⟩

end TauCeti

/-! ### Examples -/

/-- The Gaussian `exp (-z ^ 2)` grows like `exp (t ^ 2)` along the imaginary axis `z = t i`, so it
does not decay rapidly on vertical strips. -/
example : ¬ TauCeti.HasRapidVerticalDecay fun z : Fin 1 → ℂ ↦ Complex.exp (-∑ i, z i ^ 2) := by
  intro h
  obtain ⟨C, hC⟩ := h 0 0
  have := hC (fun _ ↦ C * Complex.I) (by simp)
  simp only [pow_zero, one_mul, Complex.norm_exp] at this
  have hre : (-∑ i : Fin 1, ((C : ℂ) * Complex.I) ^ 2).re = C ^ 2 := by
    simp [mul_pow, ← ofReal_pow]
  rw [hre] at this
  nlinarith [Real.add_one_le_exp (C ^ 2)]
