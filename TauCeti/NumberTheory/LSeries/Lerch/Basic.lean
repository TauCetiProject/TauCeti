/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn

/-!
# The Lerch series

For `‖z‖ < 1` and complex `s`, `c`, the Lerch series is
`Φ(z, s, c) = ∑_{n ≥ 0} zⁿ exp (-s log (n + c))`, with Mathlib's principal logarithm. When
`0 < re c` every `n + c` lies in the right half-plane, `exp (-s log (n + c))` is the principal
power `(n + c) ^ (-s)`, and `Φ` is the Lerch transcendent on its initial domain. The `n = 0`
term is kept at `z = 0`, where `0 ^ 0 = 1`, so `Φ(0, s, c) = exp (-s log c)`. Its values for
`‖z‖ ≥ 1` are those of Mathlib's `tsum` and carry no continuation.

The series converges absolutely for `‖z‖ < 1` and every `c`: the terms grow at most
polynomially in `n`, and a finite shift of the index moves `c` into the right half-plane. On
the polydisc domain `‖z‖ < 1`, `0 < re c`, in the coordinates `(s, z, c)`, the terms and their
Fréchet derivatives have locally summable majorants, so the series converges locally uniformly
and `(s, z, c) ↦ Φ(z, s, c)` is complex differentiable, that is, jointly holomorphic. The
derivative in `s` is the termwise derivative `-∑ zⁿ log (n + c) exp (-s log (n + c))`, and
that series converges absolutely. These are the initial germs for the analytic continuation
of `Φ` and for its differential relations in `z` and `c`.

## Main results

* `TauCeti.lerchSeries`: the Lerch series `Φ(z, s, c)`.
* `TauCeti.hasSum_lerchSeries`, `TauCeti.summable_norm_lerchSeries`: absolute convergence for
  `‖z‖ < 1` and all `s`, `c`.
* `TauCeti.lerchSeries_eq_exp_add_mul_lerchSeries_add_one`: `Φ(z, s, c) = c⁻ˢ + z Φ(z, s, c + 1)`,
  and its iterate `TauCeti.lerchSeries_eq_sum_add_pow_mul`.
* `TauCeti.hasSumLocallyUniformlyOn_lerchSeries`: locally uniform convergence on the polydisc
  domain.
* `TauCeti.differentiableOn_lerchSeries`: joint holomorphy on the polydisc domain.
* `TauCeti.hasDerivAt_lerchSeries_exponent`: the termwise derivative in `s`.
* `TauCeti.lerchSeries_zero_exponent`, `TauCeti.lerchSeries_neg_one_exponent`: the rational
  values `Φ(z, 0, c) = 1 / (1 - z)` and `Φ(z, -1, c) = c / (1 - z) + z / (1 - z)²`.

## References

* Jeffrey C. Lagarias and Wen-Ching Winnie Li, *The Lerch zeta function II. Analytic
  continuation*, Forum Math. 24 (2012), §2, (2.1), and §5; arXiv:1005.4967.
* Jeffrey C. Lagarias and Wen-Ching Winnie Li, *The Lerch zeta function III. Polylogarithms
  and special values*, Res. Math. Sci. 3 (2016), introduction, (1.1), and §3.3.
-/

public section

open Complex Filter Topology Asymptotics Set Metric
open scoped Real

namespace TauCeti

/-! ### Estimates for the terms

On a neighbourhood `‖s‖ < S`, `‖z‖ < r < 1`, `δ < re c`, `‖c‖ < M` of a point of the polydisc
domain, the logarithm `log (n + c)` grows like `log n`, so `exp (-s log (n + c))` grows at most
polynomially in `n` and the geometric factor `zⁿ` absorbs it, uniformly together with the
Fréchet derivatives of the terms. -/

private theorem abs_log_le {x δ B : ℝ} (hδ : 0 < δ) (hx : δ ≤ x) (hxB : x ≤ B) (hB : 1 ≤ B) :
    |Real.log x| ≤ |Real.log δ| + Real.log B := by
  have h1 : Real.log δ ≤ Real.log x := Real.log_le_log hδ hx
  have h2 : Real.log x ≤ Real.log B := Real.log_le_log (hδ.trans_le hx) hxB
  have h3 : 0 ≤ Real.log B := Real.log_nonneg hB
  refine abs_le.2 ⟨?_, ?_⟩ <;> linarith [neg_abs_le (Real.log δ), le_abs_self (Real.log δ)]

private theorem norm_log_le {w : ℂ} {δ B : ℝ} (hδ : 0 < δ) (hw : δ ≤ ‖w‖) (hwB : ‖w‖ ≤ B)
    (hB : 1 ≤ B) : ‖log w‖ ≤ |Real.log δ| + π + Real.log B := by
  calc ‖log w‖ ≤ |(log w).re| + |(log w).im| := norm_le_abs_re_add_abs_im _
    _ ≤ (|Real.log δ| + Real.log B) + π := by
      rw [log_re, log_im]
      exact add_le_add (abs_log_le hδ hw hwB hB) (abs_arg_le_pi w)
    _ = _ := by ring

private theorem norm_exp_neg_mul_log_le {s w : ℂ} {S δ B : ℝ} (hs : ‖s‖ ≤ S) (hδ : 0 < δ)
    (hw : δ ≤ ‖w‖) (hwB : ‖w‖ ≤ B) (hB : 1 ≤ B) :
    ‖exp (-s * log w)‖ ≤ Real.exp (S * (|Real.log δ| + π)) * B ^ ⌈S⌉₊ := by
  have hS : 0 ≤ S := (norm_nonneg s).trans hs
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB
  rw [norm_exp]
  calc Real.exp (-s * log w).re ≤ Real.exp (S * (|Real.log δ| + π) + ⌈S⌉₊ * Real.log B) := by
        refine Real.exp_le_exp.2 ((re_le_norm _).trans ?_)
        rw [norm_mul, norm_neg]
        calc ‖s‖ * ‖log w‖ ≤ S * (|Real.log δ| + π + Real.log B) :=
              mul_le_mul hs (norm_log_le hδ hw hwB hB) (norm_nonneg _) hS
          _ ≤ _ := by nlinarith [Nat.le_ceil S]
    _ = _ := by rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log (by linarith)]

/-- The `n`-th term of the Lerch series, in the coordinates `(s, z, c)`. -/
private noncomputable def term (n : ℕ) (p : ℂ × ℂ × ℂ) : ℂ :=
  p.2.1 ^ n * exp (-p.1 * log (n + p.2.2))

/-- The Fréchet derivative of `term n` at `p`. -/
private noncomputable def term' (n : ℕ) (p : ℂ × ℂ × ℂ) : ℂ × ℂ × ℂ →L[ℂ] ℂ :=
  p.2.1 ^ n • (exp (-p.1 * log (n + p.2.2)) •
      (-p.1 • ((n + p.2.2)⁻¹ • ((ContinuousLinearMap.snd ℂ ℂ ℂ).comp
        (ContinuousLinearMap.snd ℂ ℂ (ℂ × ℂ)))) +
        log (n + p.2.2) • -ContinuousLinearMap.fst ℂ ℂ (ℂ × ℂ))) +
    exp (-p.1 * log (n + p.2.2)) • ((n * p.2.1 ^ (n - 1)) •
      (ContinuousLinearMap.fst ℂ ℂ ℂ).comp (ContinuousLinearMap.snd ℂ ℂ (ℂ × ℂ)))

private theorem natCast_add_mem_slitPlane (n : ℕ) {c : ℂ} (hc : 0 < c.re) :
    (n : ℂ) + c ∈ slitPlane :=
  mem_slitPlane_iff.2 <| Or.inl <| by
    simp only [add_re, natCast_re]
    positivity

private theorem term'_apply_one_zero (n : ℕ) (p : ℂ × ℂ × ℂ) :
    term' n p ((1 : ℂ), (0 : ℂ × ℂ)) =
      -(p.2.1 ^ n * log (n + p.2.2) * exp (-p.1 * log (n + p.2.2))) := by
  simp [term']
  ring

private theorem hasFDerivAt_term (n : ℕ) {p : ℂ × ℂ × ℂ} (hp : (n + p.2.2) ∈ slitPlane) :
    HasFDerivAt (term n) (term' n p) p := by
  have hz : HasFDerivAt (fun q : ℂ × ℂ × ℂ => q.2.1) ((ContinuousLinearMap.fst ℂ ℂ ℂ).comp
      (ContinuousLinearMap.snd ℂ ℂ (ℂ × ℂ))) p := hasFDerivAt_snd.fst
  have hc : HasFDerivAt (fun q : ℂ × ℂ × ℂ => (n : ℂ) + q.2.2)
      ((ContinuousLinearMap.snd ℂ ℂ ℂ).comp (ContinuousLinearMap.snd ℂ ℂ (ℂ × ℂ))) p :=
    hasFDerivAt_snd.snd.const_add _
  have hlog := (hasDerivAt_log hp).comp_hasFDerivAt p hc
  have hs : HasFDerivAt (fun q : ℂ × ℂ × ℂ => -q.1) (-ContinuousLinearMap.fst ℂ ℂ (ℂ × ℂ)) p :=
    hasFDerivAt_fst.neg
  exact ((hasDerivAt_pow n p.2.1).comp_hasFDerivAt p hz).mul (hs.mul hlog).cexp

private theorem norm_term'_le (n : ℕ) (p : ℂ × ℂ × ℂ) :
    ‖term' n p‖ ≤ ‖p.2.1‖ ^ n * (‖exp (-p.1 * log (n + p.2.2))‖ *
        (‖p.1‖ * ‖(n + p.2.2)⁻¹‖ + ‖log (n + p.2.2)‖)) +
      ‖exp (-p.1 * log (n + p.2.2))‖ * (n * ‖p.2.1‖ ^ (n - 1)) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  simp only [term', add_apply, smul_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.coe_snd', ContinuousLinearMap.coe_fst', neg_apply, smul_eq_mul]
  have h1 : ‖v.1‖ ≤ ‖v‖ := norm_fst_le v
  have h2 : ‖v.2.1‖ ≤ ‖v‖ := (norm_fst_le v.2).trans (norm_snd_le v)
  have h3 : ‖v.2.2‖ ≤ ‖v‖ := (norm_snd_le v.2).trans (norm_snd_le v)
  calc _ ≤ ‖p.2.1‖ ^ n * (‖exp (-p.1 * log (n + p.2.2))‖ *
          (‖p.1‖ * (‖(n + p.2.2)⁻¹‖ * ‖v.2.2‖) + ‖log (n + p.2.2)‖ * ‖v.1‖)) +
        ‖exp (-p.1 * log (n + p.2.2))‖ * (n * ‖p.2.1‖ ^ (n - 1) * ‖v.2.1‖) := by
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_mul, norm_pow, norm_mul]
          gcongr
          refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;> simp
        · simp
    _ ≤ ‖p.2.1‖ ^ n * (‖exp (-p.1 * log (n + p.2.2))‖ *
          (‖p.1‖ * (‖(n + p.2.2)⁻¹‖ * ‖v‖) + ‖log (n + p.2.2)‖ * ‖v‖)) +
        ‖exp (-p.1 * log (n + p.2.2))‖ * (n * ‖p.2.1‖ ^ (n - 1) * ‖v‖) := by gcongr
    _ = _ := by ring

/-- The summable majorant of the Lerch terms and their derivatives on the neighbourhood
`‖s‖ < S`, `‖z‖ < r`, `δ < re c`, `‖c‖ < M`. -/
private noncomputable def majorant (S r δ M : ℝ) (n : ℕ) : ℝ :=
  Real.exp (S * (|Real.log δ| + π)) * (S / δ + |Real.log δ| + π + 1 + r⁻¹) *
    ((M * (n + 1)) ^ (⌈S⌉₊ + 1) * r ^ n)

private theorem summable_majorant (S δ M : ℝ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Summable (majorant S r δ M) := by
  have h := (summable_nat_add_iff 1).2
    (summable_pow_mul_geometric_of_norm_lt_one (⌈S⌉₊ + 1) (r := r)
      (by rwa [Real.norm_of_nonneg hr0.le]))
  refine (h.mul_left (Real.exp (S * (|Real.log δ| + π)) * (S / δ + |Real.log δ| + π + 1 + r⁻¹) *
    M ^ (⌈S⌉₊ + 1) * r⁻¹)).congr fun n => ?_
  simp only [majorant, Nat.cast_add, Nat.cast_one, mul_pow, pow_succ r n]
  field_simp

/-- On the neighbourhood of `majorant`, the shifted parameter `n + c` stays in the annulus
`δ ≤ ‖n + c‖ ≤ M (n + 1)`. -/
private theorem le_norm_natCast_add_and_le {δ M : ℝ} {c : ℂ} (n : ℕ) (hM : 1 ≤ M)
    (hc : δ ≤ c.re) (hcM : ‖c‖ ≤ M) :
    δ ≤ ‖(n : ℂ) + c‖ ∧ ‖(n : ℂ) + c‖ ≤ M * (n + 1) := by
  have hn := Nat.cast_nonneg (α := ℝ) n
  refine ⟨(by simpa using add_le_add hn hc : δ ≤ ((n : ℂ) + c).re).trans (re_le_norm _),
    (norm_add_le _ _).trans ?_⟩
  rw [Complex.norm_natCast]
  nlinarith

private theorem norm_term_le_majorant {S r δ M : ℝ} {s z c : ℂ} (n : ℕ) (hr0 : 0 < r)
    (hδ : 0 < δ) (hM : 1 ≤ M) (hs : ‖s‖ ≤ S) (hz : ‖z‖ ≤ r) (hc : δ ≤ c.re) (hcM : ‖c‖ ≤ M) :
    ‖term n (s, z, c)‖ ≤ majorant S r δ M n := by
  obtain ⟨hδw, hwP⟩ := le_norm_natCast_add_and_le n hM hc hcM
  have hP : 1 ≤ M * (n + 1) := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hS : 0 ≤ S := (norm_nonneg s).trans hs
  have hF : 1 ≤ M * (n + 1) * (S / δ + |Real.log δ| + π + 1 + r⁻¹) := by
    have : 0 ≤ S / δ := by positivity
    nlinarith [inv_nonneg.2 hr0.le, abs_nonneg (Real.log δ), Real.pi_pos]
  calc ‖term n (s, z, c)‖ = ‖z‖ ^ n * ‖exp (-s * log (n + c))‖ := by simp [term]
    _ ≤ r ^ n * (Real.exp (S * (|Real.log δ| + π)) * (M * (n + 1)) ^ ⌈S⌉₊) := by
        gcongr
        exact norm_exp_neg_mul_log_le hs hδ hδw hwP hP
    _ = Real.exp (S * (|Real.log δ| + π)) * (M * (n + 1)) ^ ⌈S⌉₊ * r ^ n * 1 := by ring
    _ ≤ Real.exp (S * (|Real.log δ| + π)) * (M * (n + 1)) ^ ⌈S⌉₊ * r ^ n *
          (M * (n + 1) * (S / δ + |Real.log δ| + π + 1 + r⁻¹)) := by gcongr
    _ = majorant S r δ M n := by simp only [majorant]; ring

private theorem norm_term'_le_majorant {S r δ M : ℝ} {s z c : ℂ} (n : ℕ) (hr0 : 0 < r)
    (hδ : 0 < δ) (hM : 1 ≤ M) (hs : ‖s‖ ≤ S) (hz : ‖z‖ ≤ r) (hc : δ ≤ c.re) (hcM : ‖c‖ ≤ M) :
    ‖term' n (s, z, c)‖ ≤ majorant S r δ M n := by
  obtain ⟨hδw, hwP⟩ := le_norm_natCast_add_and_le n hM hc hcM
  set P : ℝ := M * (n + 1)
  set A : ℝ := |Real.log δ| + π
  have hn : (n : ℝ) ≤ P := by simp only [P]; nlinarith
  have hP : 1 ≤ P := by simp only [P]; nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hL : ‖log (n + c)‖ ≤ A + P := (norm_log_le hδ hδw hwP hP).trans
    (by linarith [Real.log_le_sub_one_of_pos (by linarith : 0 < P)])
  have hinv : ‖((n : ℂ) + c)⁻¹‖ ≤ δ⁻¹ := by
    rw [norm_inv]
    exact inv_anti₀ hδ hδw
  have hzn' : (n : ℝ) * ‖z‖ ^ (n - 1) ≤ P * r ^ n * r⁻¹ := by
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp only [CharP.cast_eq_zero, zero_mul]
      positivity
    · calc (n : ℝ) * ‖z‖ ^ (n - 1) ≤ P * r ^ (n - 1) := by gcongr
        _ = P * r ^ n * r⁻¹ := by
            rw [pow_sub₀ _ hr0.ne' (by omega : 1 ≤ n), pow_one]
            ring
  have hA : 0 ≤ A := by positivity
  have hS : 0 ≤ S := (norm_nonneg s).trans hs
  have hSδ : 0 ≤ S / δ := div_nonneg hS hδ.le
  calc ‖term' n (s, z, c)‖ ≤ r ^ n * (Real.exp (S * A) * P ^ ⌈S⌉₊ * (S * δ⁻¹ + (A + P))) +
        Real.exp (S * A) * P ^ ⌈S⌉₊ * (P * r ^ n * r⁻¹) := by
        have hE := norm_exp_neg_mul_log_le hs hδ hδw hwP hP
        refine (norm_term'_le n (s, z, c)).trans ?_
        dsimp only
        gcongr
    _ = Real.exp (S * A) * P ^ ⌈S⌉₊ * r ^ n * (S / δ + A + P + P * r⁻¹) := by ring
    _ ≤ Real.exp (S * A) * P ^ ⌈S⌉₊ * r ^ n * (P * (S / δ + A + 1 + r⁻¹)) := by
        gcongr
        nlinarith
    _ = majorant S r δ M n := by simp only [majorant, P, A]; ring

/-- Each point of the disc domain has a preconnected open neighbourhood on which the terms of
the Lerch series and their derivatives have a common summable majorant. -/
private theorem exists_nhds_summable_bound {p : ℂ × ℂ × ℂ} (hz : ‖p.2.1‖ < 1)
    (hc : 0 < p.2.2.re) :
    ∃ U : Set (ℂ × ℂ × ℂ), IsOpen U ∧ IsPreconnected U ∧ p ∈ U ∧
      U ⊆ {q | ‖q.2.1‖ < 1 ∧ 0 < q.2.2.re} ∧ ∃ u : ℕ → ℝ, Summable u ∧
        ∀ n, ∀ q ∈ U, ‖term n q‖ ≤ u n ∧ ‖term' n q‖ ≤ u n := by
  have hr0 : 0 < (‖p.2.1‖ + 1) / 2 := by positivity
  have hr1 : (‖p.2.1‖ + 1) / 2 < 1 := by linarith
  have hδ : 0 < p.2.2.re / 2 := by positivity
  have hM : 1 ≤ ‖p.2.2‖ + 1 := by linarith [norm_nonneg p.2.2]
  refine ⟨ball 0 (‖p.1‖ + 1) ×ˢ ball 0 ((‖p.2.1‖ + 1) / 2) ×ˢ
      ({c | p.2.2.re / 2 < c.re} ∩ ball 0 (‖p.2.2‖ + 1)),
    isOpen_ball.prod (isOpen_ball.prod ((isOpen_lt continuous_const continuous_re).inter
      isOpen_ball)),
    (convex_ball _ _).isPreconnected.prod ((convex_ball _ _).isPreconnected.prod
      ((convex_halfSpace_re_gt _).inter (convex_ball _ _)).isPreconnected), ?_, ?_, _,
    summable_majorant (‖p.1‖ + 1) (p.2.2.re / 2) (‖p.2.2‖ + 1) hr0 hr1, ?_⟩
  · simp only [mem_prod, mem_ball_zero_iff, mem_inter_iff, mem_ofPred_eq]
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rintro q ⟨-, hqz, hqc, -⟩
    rw [mem_ball_zero_iff] at hqz
    exact ⟨hqz.trans hr1, hδ.trans hqc⟩
  rintro n ⟨s, z, c⟩ ⟨hs, hz, hc, hcM⟩
  rw [mem_ball_zero_iff] at hs hz hcM
  exact ⟨norm_term_le_majorant n hr0 hδ hM hs.le hz.le hc.le hcM.le,
    norm_term'_le_majorant n hr0 hδ hM hs.le hz.le hc.le hcM.le⟩

/-! ### The Lerch series -/

/-- The Lerch series `Φ(z, s, c) = ∑_{n ≥ 0} zⁿ exp (-s log (n + c))`, with the principal
logarithm. It converges absolutely for `‖z‖ < 1` (`TauCeti.hasSum_lerchSeries`); for `0 < re c`
its terms are the principal powers `zⁿ (n + c) ^ (-s)`. -/
noncomputable def lerchSeries (z s c : ℂ) : ℂ :=
  ∑' n : ℕ, z ^ n * exp (-s * log (n + c))

/-- Unfold the Lerch series as a `tsum`. -/
theorem lerchSeries_def (z s c : ℂ) :
    lerchSeries z s c = ∑' n : ℕ, z ^ n * exp (-s * log (n + c)) :=
  (rfl)

private theorem summable_norm_term {p : ℂ × ℂ × ℂ} (hz : ‖p.2.1‖ < 1) (hc : 0 < p.2.2.re) :
    Summable fun n => ‖term n p‖ :=
  let ⟨_, _, _, hpU, _, _, hu, hb⟩ := exists_nhds_summable_bound hz hc
  .of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => (hb n p hpU).1) hu

/-- A series `∑ zⁿ F (n + c)` that converges absolutely whenever `0 < re c` converges absolutely
for every `c`, since a finite shift of the index moves `c` into the right half-plane. -/
private theorem summable_norm_pow_mul_of_re_pos {z : ℂ} (F : ℂ → ℂ)
    (h : ∀ c : ℂ, 0 < c.re → Summable fun n : ℕ => ‖z ^ n * F (n + c)‖) (c : ℂ) :
    Summable fun n : ℕ => ‖z ^ n * F (n + c)‖ := by
  obtain ⟨k, hk⟩ := exists_nat_gt (-c.re)
  rw [← summable_nat_add_iff k]
  refine ((h (k + c) (by simp; linarith)).mul_left (‖z‖ ^ k)).congr fun n => ?_
  simp only [norm_mul, norm_pow, pow_add, Nat.cast_add, add_assoc]
  ring

/-- The Lerch series converges absolutely for `‖z‖ < 1`, for every `s` and `c`. -/
theorem summable_norm_lerchSeries {z : ℂ} (hz : ‖z‖ < 1) (s c : ℂ) :
    Summable fun n : ℕ => ‖z ^ n * exp (-s * log (n + c))‖ :=
  summable_norm_pow_mul_of_re_pos (fun w => exp (-s * log w))
    (fun c hc => by simpa [term] using summable_norm_term (p := (s, z, c)) hz hc) c

/-- For `‖z‖ < 1` the Lerch series sums to `lerchSeries z s c`, for every `s` and `c`. -/
theorem hasSum_lerchSeries {z : ℂ} (hz : ‖z‖ < 1) (s c : ℂ) :
    HasSum (fun n : ℕ => z ^ n * exp (-s * log (n + c))) (lerchSeries z s c) :=
  (summable_norm_lerchSeries hz s c).of_norm.hasSum

/-- At `z = 0` only the `n = 0` term survives, since `0 ^ 0 = 1`. -/
@[simp]
theorem lerchSeries_zero_left (s c : ℂ) : lerchSeries 0 s c = exp (-s * log c) := by
  rw [lerchSeries_def, tsum_eq_single 0 fun n hn => by simp [hn]]
  simp

/-- Splitting off the first `k` terms: `Φ(z, s, c) = ∑_{i < k} zⁱ exp (-s log (i + c)) +
zᵏ Φ(z, s, k + c)`. -/
theorem lerchSeries_eq_sum_add_pow_mul {z : ℂ} (hz : ‖z‖ < 1) (s c : ℂ) (k : ℕ) :
    lerchSeries z s c = ∑ i ∈ Finset.range k, z ^ i * exp (-s * log (i + c)) +
      z ^ k * lerchSeries z s (k + c) := by
  rw [lerchSeries_def z s c, ← (hasSum_lerchSeries hz s c).summable.sum_add_tsum_nat_add k,
    lerchSeries_def, ← tsum_mul_left]
  exact congrArg _ (tsum_congr fun n => by push_cast; ring_nf)

/-- The shift relation `Φ(z, s, c) = exp (-s log c) + z Φ(z, s, c + 1)`; for `0 < re c` the
first term is `c ^ (-s)`. -/
theorem lerchSeries_eq_exp_add_mul_lerchSeries_add_one {z : ℂ} (hz : ‖z‖ < 1) (s c : ℂ) :
    lerchSeries z s c = exp (-s * log c) + z * lerchSeries z s (c + 1) := by
  simpa [add_comm] using lerchSeries_eq_sum_add_pow_mul hz s c 1

/-- At `s = 0` the Lerch series is the geometric series, independently of `c`. -/
theorem lerchSeries_zero_exponent {z : ℂ} (hz : ‖z‖ < 1) (c : ℂ) :
    lerchSeries z 0 c = (1 - z)⁻¹ := by
  simpa [lerchSeries_def] using tsum_geometric_of_norm_lt_one hz

/-- At `s = -1` the Lerch series is `∑ zⁿ (n + c) = c / (1 - z) + z / (1 - z)²`. The parameter
must avoid the nonpositive integers: at `c = -m` the totalized `exp (log 0) = 1` replaces the
vanishing term `m + c`. -/
theorem lerchSeries_neg_one_exponent {z c : ℂ} (hz : ‖z‖ < 1) (hc : ∀ n : ℕ, c ≠ -n) :
    lerchSeries z (-1) c = c / (1 - z) + z / (1 - z) ^ 2 := by
  refine (hasSum_lerchSeries hz (-1) c).unique ?_
  have h := ((hasSum_geometric_of_norm_lt_one hz).mul_left c).add
    (hasSum_coe_mul_geometric_of_norm_lt_one hz)
  convert h using 1
  · ext n
    have hn : (n : ℂ) + c ≠ 0 := fun h => hc n (by linear_combination h)
    rw [neg_neg, one_mul, exp_log hn]
    ring
  · ring

/-- The Lerch series converges locally uniformly on the polydisc domain `‖z‖ < 1`, `0 < re c`,
in the coordinates `(s, z, c)`. -/
theorem hasSumLocallyUniformlyOn_lerchSeries :
    HasSumLocallyUniformlyOn
      (fun (n : ℕ) (p : ℂ × ℂ × ℂ) => p.2.1 ^ n * exp (-p.1 * log (n + p.2.2)))
      (fun p => lerchSeries p.2.1 p.1 p.2.2) {p | ‖p.2.1‖ < 1 ∧ 0 < p.2.2.re} := by
  refine hasSumLocallyUniformlyOn_of_of_forall_exists_nhds fun p hp => ?_
  obtain ⟨U, hUo, -, hpU, -, u, hu, hb⟩ := exists_nhds_summable_bound hp.1 hp.2
  exact ⟨U, mem_nhdsWithin_of_mem_nhds (hUo.mem_nhds hpU),
    HasSumUniformlyOn.of_norm_le_summable hu fun n q hq => (hb n q hq).1⟩

private theorem hasFDerivAt_lerchSeries {p : ℂ × ℂ × ℂ} (hz : ‖p.2.1‖ < 1) (hc : 0 < p.2.2.re) :
    HasFDerivAt (fun q : ℂ × ℂ × ℂ => lerchSeries q.2.1 q.1 q.2.2) (∑' n, term' n p) p ∧
      Summable fun n => ‖term' n p‖ := by
  obtain ⟨U, hUo, hUc, hpU, hUD, u, hu, hb⟩ := exists_nhds_summable_bound hz hc
  exact ⟨hasFDerivAt_tsum_of_isPreconnected hu hUo hUc
    (fun n q hq => hasFDerivAt_term n (natCast_add_mem_slitPlane n (hUD hq).2))
    (fun n q hq => (hb n q hq).2) hpU (summable_norm_term hz hc).of_norm hpU,
    .of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => (hb n p hpU).2) hu⟩

/-- **Joint holomorphy of the Lerch series.** The map `(s, z, c) ↦ Φ(z, s, c)` is complex
differentiable on the polydisc domain `‖z‖ < 1`, `0 < re c`. -/
theorem differentiableOn_lerchSeries :
    DifferentiableOn ℂ (fun p : ℂ × ℂ × ℂ => lerchSeries p.2.1 p.1 p.2.2)
      {p | ‖p.2.1‖ < 1 ∧ 0 < p.2.2.re} := fun _ hp =>
  (hasFDerivAt_lerchSeries hp.1 hp.2).1.differentiableAt.differentiableWithinAt

/-- The termwise `s`-derivative of the Lerch series converges absolutely for `‖z‖ < 1`, for
every `s` and `c`. -/
theorem summable_norm_lerchSeries_deriv_exponent {z : ℂ} (hz : ‖z‖ < 1) (s c : ℂ) :
    Summable fun n : ℕ => ‖z ^ n * log (n + c) * exp (-s * log (n + c))‖ := by
  have key (c : ℂ) (hc : 0 < c.re) :
      Summable fun n : ℕ => ‖z ^ n * (log (n + c) * exp (-s * log (n + c)))‖ := by
    refine .of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
      (hasFDerivAt_lerchSeries (p := (s, z, c)) hz hc).2
    have h := (term' n (s, z, c)).le_opNorm ((1 : ℂ), (0 : ℂ × ℂ))
    rwa [term'_apply_one_zero, norm_neg, Prod.norm_def, norm_one, norm_zero,
      max_eq_left zero_le_one, mul_one, mul_assoc] at h
  simpa only [mul_assoc] using
    summable_norm_pow_mul_of_re_pos (fun w => log w * exp (-s * log w)) key c

private theorem hasDerivAt_lerchSeries_exponent_of_re_pos {z c : ℂ} (hz : ‖z‖ < 1)
    (hc : 0 < c.re) (s : ℂ) :
    HasDerivAt (fun s => lerchSeries z s c)
      (-∑' n : ℕ, z ^ n * log (n + c) * exp (-s * log (n + c))) s := by
  obtain ⟨hF, hsum⟩ := hasFDerivAt_lerchSeries (p := (s, z, c)) hz hc
  have h : HasDerivAt (fun s => lerchSeries z s c) ((∑' n, term' n (s, z, c)) ((1 : ℂ), 0)) s :=
    hF.comp_hasDerivAt (f := fun s => (s, z, c)) s
      ((hasDerivAt_id s).prodMk (hasDerivAt_const s (z, c)))
  convert h using 1
  have happ := (ContinuousLinearMap.apply ℂ ℂ ((1 : ℂ), (0 : ℂ × ℂ))).map_tsum hsum.of_norm
  simp only [ContinuousLinearMap.apply_apply, term'_apply_one_zero] at happ
  rw [happ, tsum_neg]

/-- The derivative of the Lerch series in `s` is the termwise derivative
`∂ₛ Φ(z, s, c) = -∑ zⁿ log (n + c) exp (-s log (n + c))`, for `‖z‖ < 1` and every `c`. -/
theorem hasDerivAt_lerchSeries_exponent {z : ℂ} (hz : ‖z‖ < 1) (s c : ℂ) :
    HasDerivAt (fun s => lerchSeries z s c)
      (-∑' n : ℕ, z ^ n * log (n + c) * exp (-s * log (n + c))) s := by
  obtain ⟨k, hk⟩ := exists_nat_gt (-c.re)
  have hpos := hasDerivAt_lerchSeries_exponent_of_re_pos hz (c := k + c) (by simp; linarith) s
  have hsum : HasDerivAt (fun s => ∑ i ∈ Finset.range k, z ^ i * exp (-s * log (i + c)))
      (∑ i ∈ Finset.range k, z ^ i * (exp (-s * log (i + c)) * (-1 * log (i + c)))) s :=
    .fun_sum fun i _ => (((hasDerivAt_id s).neg.mul_const _).cexp).const_mul _
  have h := hsum.add (hpos.const_mul (z ^ k))
  rw [funext fun s => lerchSeries_eq_sum_add_pow_mul hz s c k]
  convert h using 1
  rw [← (summable_norm_lerchSeries_deriv_exponent hz s c).of_norm.sum_add_tsum_nat_add k,
    neg_add, ← Finset.sum_neg_distrib, mul_neg, ← tsum_mul_left]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by ring
  · exact congrArg _ (tsum_congr fun n => by push_cast; ring_nf)

end TauCeti
