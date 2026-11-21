/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.RegularizedHypergeometric.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# The regularized Kummer function as a function of its parameters

Olver's regularized Kummer function `𝐌(a, b, z) = M(a, b, z) / Γ(b)` is Mathlib's
`Complex.regularizedHGFun {a} {b} z`, the sum of the series `∑ (a)ₙ zⁿ / (n! Γ(b + n))`. Since
`1 / Γ` is entire, every term of this series is an entire function of `a`, `b` and `z`, and the
series converges locally uniformly in all three variables (DLMF §13.2(i)). Hence `𝐌` is jointly
continuous in `(a, b, z)`, and it is entire in `a` and in `b` separately; no parameter is
excluded at the poles of `Γ(b)`.

The local majorant comes from the shifted Gamma bound `‖1 / Γ(s + n)‖ ≤ ‖1 / Γ(s)‖ / n!` for
`1 ≤ Re s`: for `‖a‖ ≤ A`, `‖z‖ ≤ R` and `1 ≤ Re (b + N)`, the `(n + N)`-th term of the series of
`𝐌(a, b, z)` is at most `‖1 / Γ(b + N)‖` times the `(n + N)`-th term of the series of
`𝐌(A, 1 - N, R)`, whose `(n + N)`-th coefficient is `(A)_{n + N} / ((n + N)! n!)`.

## Main results

* `Complex.norm_regularizedHGFunCoeff_singleton_mul_pow_le` — the termwise majorant.
* `Complex.exists_summable_eventually_norm_regularizedHGFunCoeff_singleton_mul_pow_le` — a
  summable majorant of the tail of the series, uniform near every point `(a, b, z)`.
* `Complex.continuous_regularizedHGFun_singleton` — joint continuity of `𝐌` in `(a, b, z)`.
* `Continuous.regularizedHGFun_singleton` — `x ↦ 𝐌(f x, g x, h x)` is continuous for continuous
  `f`, `g` and `h`.
* `Differentiable.regularizedHGFun_singleton` — `w ↦ 𝐌(f w, g w, h w)` is entire for entire
  `f`, `g` and `h`.
* `Complex.differentiable_regularizedHGFun_singleton_left` and
  `Complex.differentiable_regularizedHGFun_singleton_right` — `𝐌` is entire in `a` and in `b`.

The proofs are adapted from the lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>),
file `DLMF/Confluent/Regularized.lean`.
-/

public section

noncomputable section

open Filter
open scoped Nat Topology

namespace Complex

/-- The coefficients of `𝐌(a, b, ·)` are jointly holomorphic in the parameters `(a, b)`. -/
theorem differentiable_regularizedHGFunCoeff_singleton (n : ℕ) :
    Differentiable ℂ fun q : ℂ × ℂ => regularizedHGFunCoeff {q.1} {q.2} n := by
  simp only [regularizedHGFunCoeff, Multiset.map_singleton, Multiset.prod_singleton,
    div_eq_mul_inv, mul_inv]
  exact ((Polynomial.differentiable _).comp differentiable_fst).mul
    ((differentiable_one_div_Gamma.comp
      (by fun_prop : Differentiable ℂ fun q : ℂ × ℂ => q.2 + n)).const_mul _)

/-- The termwise majorant of the series of `𝐌(a, b, z)`: for `‖a‖ ≤ A`, `‖z‖ ≤ R` and
`1 ≤ Re (b + N)`, the `(n + N)`-th term is at most `‖1 / Γ(b + N)‖` times the `(n + N)`-th term
of the series of `𝐌(A, 1 - N, R)`. -/
theorem norm_regularizedHGFunCoeff_singleton_mul_pow_le {a b z : ℂ} {A R : ℝ} {N : ℕ}
    (ha : ‖a‖ ≤ A) (hz : ‖z‖ ≤ R) (hb : 1 ≤ (b + N).re) (n : ℕ) :
    ‖regularizedHGFunCoeff {a} {b} (n + N) * z ^ (n + N)‖ ≤
      ‖(Gamma (b + N))⁻¹‖ *
        ‖regularizedHGFunCoeff {(A : ℂ)} {1 - (N : ℂ)} (n + N) * (R : ℂ) ^ (n + N)‖ := by
  have hA : 0 ≤ A := (norm_nonneg a).trans ha
  have hR : 0 ≤ R := (norm_nonneg z).trans hz
  have hpoch (m : ℕ) : ‖(ascPochhammer ℂ m).eval a‖ ≤ ‖(ascPochhammer ℂ m).eval (A : ℂ)‖ := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval, norm_mul, norm_mul]
      have hlin : ‖a + m‖ ≤ ‖(A : ℂ) + m‖ := by
        rw [← ofReal_natCast, ← ofReal_add, norm_real, Real.norm_of_nonneg (by positivity)]
        exact (norm_add_le _ _).trans (by simpa using ha)
      exact mul_le_mul ih hlin (norm_nonneg _) (norm_nonneg _)
  have hshift : 1 - (N : ℂ) + ((n + N : ℕ) : ℂ) = n + 1 := by push_cast; ring
  have hΓ : Gamma (1 - (N : ℂ) + ((n + N : ℕ) : ℂ)) = n ! := by
    rw [hshift, Gamma_nat_eq_factorial]
  have hbN : b + N + n = b + ((n + N : ℕ) : ℂ) := by push_cast; ring
  have hG := norm_inv_Gamma_add_natCast_le hb n
  rw [hbN] at hG
  simp only [regularizedHGFunCoeff, Multiset.map_singleton, Multiset.prod_singleton, hΓ,
    div_eq_mul_inv, mul_inv, norm_mul, norm_inv, norm_pow, norm_real, norm_natCast,
    Real.norm_of_nonneg hR]
  simp only [norm_inv] at hG
  calc _ ≤ ‖(ascPochhammer ℂ (n + N)).eval (A : ℂ)‖ * (((n + N)! : ℝ)⁻¹ *
        (‖Gamma (b + N)‖⁻¹ / n !)) * R ^ (n + N) := by gcongr; exact hpoch _
    _ = _ := by ring

/-- Near every point `(a, b, z)`, the tail of the series of `𝐌` beyond a fixed index `N` has a
summable majorant, uniform in the point. -/
theorem exists_summable_eventually_norm_regularizedHGFunCoeff_singleton_mul_pow_le
    (x : ℂ × ℂ × ℂ) :
    ∃ N : ℕ, ∃ u : ℕ → ℝ, Summable u ∧ ∀ᶠ p in 𝓝 x, ∀ n : ℕ,
      ‖regularizedHGFunCoeff {p.1} {p.2.1} (n + N) * p.2.2 ^ (n + N)‖ ≤ u n := by
  obtain ⟨a₀, b₀, z₀⟩ := x
  obtain ⟨N, hN⟩ := exists_nat_ge (2 - b₀.re)
  have hΓ : Continuous fun b : ℂ => (Gamma (b + N))⁻¹ :=
    (differentiable_one_div_Gamma.comp (differentiable_id.add_const (N : ℂ))).continuous
  obtain ⟨C, hC⟩ := (isCompact_closedBall b₀ 1).exists_bound_of_continuousOn hΓ.continuousOn
  set A := ‖a₀‖ + 1
  set R := ‖z₀‖ + 1
  refine ⟨N, fun n => C * ‖regularizedHGFunCoeff {(A : ℂ)} {1 - (N : ℂ)} (n + N) *
    (R : ℂ) ^ (n + N)‖, ((summable_nat_add_iff N).2
      (summable_norm_regularizedHGFun (by simp) (R : ℂ))).mul_left C, ?_⟩
  have ha : ∀ᶠ p : ℂ × ℂ × ℂ in 𝓝 (a₀, b₀, z₀), ‖p.1‖ < A :=
    (continuous_fst.norm.tendsto _).eventually (gt_mem_nhds (by simp [A]))
  have hb : ∀ᶠ p : ℂ × ℂ × ℂ in 𝓝 (a₀, b₀, z₀), p.2.1 ∈ Metric.ball b₀ 1 :=
    (continuous_snd.fst.tendsto _).eventually (Metric.ball_mem_nhds b₀ one_pos)
  have hz : ∀ᶠ p : ℂ × ℂ × ℂ in 𝓝 (a₀, b₀, z₀), ‖p.2.2‖ < R :=
    (continuous_snd.snd.norm.tendsto _).eventually (gt_mem_nhds (by simp [R]))
  filter_upwards [ha, hb, hz] with p hpa hpb hpz n
  have hre : 1 ≤ (p.2.1 + N).re := by
    have := (abs_re_le_norm (p.2.1 - b₀)).trans_lt (by rwa [← dist_eq_norm])
    rw [sub_re, abs_lt] at this
    rw [add_re, natCast_re]
    linarith
  refine (norm_regularizedHGFunCoeff_singleton_mul_pow_le hpa.le hpz.le hre n).trans ?_
  gcongr
  exact hC _ (Metric.ball_subset_closedBall hpb)

/-- The series of `𝐌(a, b, z)`, split after its first `N` terms. -/
private theorem regularizedHGFun_singleton_eq_sum_range_add_tsum (a b z : ℂ) (N : ℕ) :
    regularizedHGFun {a} {b} z =
      ∑ n ∈ Finset.range N, regularizedHGFunCoeff {a} {b} n * z ^ n +
        ∑' n : ℕ, regularizedHGFunCoeff {a} {b} (n + N) * z ^ (n + N) := by
  rw [← (hasSum_regularizedHGFun (by simp) z).tsum_eq,
    (hasSum_regularizedHGFun (a := {a}) (b := {b}) (by simp) z).summable.sum_add_tsum_nat_add]

/-- The regularized Kummer function `𝐌(a, b, z)` is jointly continuous in the parameters and the
argument. -/
theorem continuous_regularizedHGFun_singleton :
    Continuous fun p : ℂ × ℂ × ℂ => regularizedHGFun {p.1} {p.2.1} p.2.2 := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨N, u, hu, hev⟩ :=
    exists_summable_eventually_norm_regularizedHGFunCoeff_singleton_mul_pow_le x
  obtain ⟨U, hU, hUo, hxU⟩ := eventually_nhds_iff.1 hev
  have hterm (n : ℕ) : Continuous fun p : ℂ × ℂ × ℂ =>
      regularizedHGFunCoeff {p.1} {p.2.1} n * p.2.2 ^ n :=
    ((differentiable_regularizedHGFunCoeff_singleton n).continuous.comp
      (continuous_fst.prodMk continuous_snd.fst)).mul (continuous_snd.snd.pow n)
  simp_rw [regularizedHGFun_singleton_eq_sum_range_add_tsum _ _ _ N]
  exact (continuous_finsetSum _ fun n _ => hterm n).continuousAt.add
    ((continuousOn_tsum (fun n => (hterm (n + N)).continuousOn) hu
      fun n p hp => hU p hp n).continuousAt (hUo.mem_nhds hxU))

/-- For continuous `f`, `g` and `h`, the function `x ↦ 𝐌(f x, g x, h x)` is continuous. -/
@[fun_prop]
theorem _root_.Continuous.regularizedHGFun_singleton {X : Type*} [TopologicalSpace X]
    {f g h : X → ℂ} (hf : Continuous f) (hg : Continuous g) (hh : Continuous h) :
    Continuous fun x => regularizedHGFun {f x} {g x} (h x) :=
  continuous_regularizedHGFun_singleton.comp (hf.prodMk (hg.prodMk hh))

/-- For entire `f`, `g` and `h`, the function `w ↦ 𝐌(f w, g w, h w)` is entire. -/
@[fun_prop]
theorem _root_.Differentiable.regularizedHGFun_singleton {f g h : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) (hh : Differentiable ℂ h) :
    Differentiable ℂ fun w => regularizedHGFun {f w} {g w} (h w) := by
  intro w₀
  obtain ⟨N, u, hu, hev⟩ :=
    exists_summable_eventually_norm_regularizedHGFunCoeff_singleton_mul_pow_le
      (f w₀, g w₀, h w₀)
  obtain ⟨V, hV, hVo, hw₀V⟩ := eventually_nhds_iff.1
    ((hf.continuous.prodMk (hg.continuous.prodMk hh.continuous)).continuousAt.eventually hev)
  have hterm (n : ℕ) : Differentiable ℂ fun w =>
      regularizedHGFunCoeff {f w} {g w} n * h w ^ n :=
    ((differentiable_regularizedHGFunCoeff_singleton n).comp (hf.prodMk hg)).mul (hh.pow n)
  simp_rw [regularizedHGFun_singleton_eq_sum_range_add_tsum _ _ _ N]
  exact (Differentiable.fun_sum fun n _ => hterm n).differentiableAt.add
    ((differentiableOn_tsum_of_summable_norm hu (fun n => (hterm (n + N)).differentiableOn) hVo
      fun n w hw => hV w hw n).differentiableAt (hVo.mem_nhds hw₀V))

/-- For fixed `b` and `z`, the regularized Kummer function `a ↦ 𝐌(a, b, z)` is entire. -/
theorem differentiable_regularizedHGFun_singleton_left (b z : ℂ) :
    Differentiable ℂ fun a => regularizedHGFun {a} {b} z :=
  differentiable_id.regularizedHGFun_singleton (differentiable_const b) (differentiable_const z)

/-- For fixed `a` and `z`, the regularized Kummer function `b ↦ 𝐌(a, b, z)` is entire. -/
theorem differentiable_regularizedHGFun_singleton_right (a z : ℂ) :
    Differentiable ℂ fun b => regularizedHGFun {a} {b} z :=
  (differentiable_const a).regularizedHGFun_singleton differentiable_id (differentiable_const z)

end Complex
