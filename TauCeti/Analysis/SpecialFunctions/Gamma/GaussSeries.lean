/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
module

public import TauCeti.Analysis.SpecialFunctions.Gamma.Real
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.Complex.HalfPlane
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
import Mathlib.NumberTheory.ZetaValues
import TauCeti.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Gauss' series for digamma

The paired reciprocal series `∑' n, (1 / (n + 1) - 1 / (s + n))` converges absolutely at
every complex point, and outside the nonpositive integers it equals `digamma s + γ`.
Pairing is essential: the two reciprocal series do not converge separately.

The proof first identifies the sum on the positive real axis using the digamma recurrence
and its explicit logarithmic asymptotic. Local uniform convergence extends the identity
through the right half-plane by the identity theorem. Recurrences for the sum and digamma
then extend it to every regular complex point. Telescoping the finite partial sums also yields
the Euler–Gauss limit representation `log (s + N) - ∑_{k ≤ N} (s + k)⁻¹ → digamma s`
(`Complex.tendsto_log_add_sub_sum_inv_add`).

Subtracting Gauss' series at two regular arguments cancels Euler's constant and expresses
`digamma s - digamma w` as the absolutely convergent series
`∑' n, (s - w) / ((w + n) * (s + n))`. This yields the sharp Lipschitz bound `π² / 6` on
`{s : ℂ | 1 ≤ s.re}`, strict monotonicity of `Real.digamma`, strict antitonicity and antitonicity of
`t ↦ ψ(t + b) - ψ(t + a)` when `a < b` (resp. `a ≤ b`), uniform upper bounds on shifted
differences, and Euler's integral representation
`∫ w in (0 : ℝ)..1, (w ^ (a - 1) - 1) / (1 - w) = ψ(1) - ψ(a)` for `0 < a`.

## References

* [NIST DLMF, equation 5.7.6](https://dlmf.nist.gov/5.7.E6),
  [equation 5.9.16](https://dlmf.nist.gov/5.9.E16).
* F. Calegari, V. Dimitrov and Y. Tang (CDT), *The unbounded denominators conjecture*,
  J. Amer. Math. Soc. 38 (2025), Lemma 5.2.9, p. 676.
* T. Tao, [Mathlib PR #43556](https://github.com/leanprover-community/mathlib4/pull/43556),
  for the Gauss series theorem statements.
-/

public section

open Complex Real Filter Set Topology Asymptotics

namespace Complex

private noncomputable def gaussTerm (s : ℂ) (n : ℕ) : ℂ :=
  1 / ((n : ℂ) + 1) - 1 / (s + n)

private theorem gaussTerm_eq {s : ℂ} {n : ℕ} (hsn : s + n ≠ 0) :
    gaussTerm s n = (s - 1) / (((n : ℂ) + 1) * (s + n)) := by
  rw [gaussTerm, div_sub_div _ _ n.cast_add_one_ne_zero hsn]
  ring

private theorem norm_natCast_add_one (n : ℕ) : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by
  simpa only [Nat.cast_add, Nat.cast_one] using Complex.norm_natCast (n + 1)

private theorem summable_gaussTerm (s : ℂ) : Summable (gaussTerm s) := by
  have hu : Summable (fun n : ℕ ↦ (2 * ‖s - 1‖) / (n : ℝ) ^ 2) := by
    exact ((Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))).mul_left
      (2 * ‖s - 1‖)).congr (fun n ↦ by ring)
  apply hu.of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop (2 * ⌈‖s‖⌉₊ + 1)] with n hn
  have hnR : (2 : ℝ) * (⌈‖s‖⌉₊ : ℝ) + 1 ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith [Nat.cast_nonneg (α := ℝ) ⌈‖s‖⌉₊]
  have hnorm : (n : ℝ) - ‖s‖ ≤ ‖s + n‖ := by
    simpa only [Complex.norm_natCast, add_comm] using norm_sub_le_norm_add (n : ℂ) s
  have hlow : (n : ℝ) / 2 ≤ ‖s + n‖ := by linarith [Nat.le_ceil ‖s‖]
  have hsn : s + n ≠ 0 := norm_pos_iff.mp (by linarith)
  rw [gaussTerm_eq hsn, norm_div, norm_mul, norm_natCast_add_one]
  have hden : 0 < ((n : ℝ) + 1) * ‖s + n‖ :=
    mul_pos (by linarith) (by linarith)
  apply (div_le_div_iff₀ hden (by positivity : 0 < (n : ℝ) ^ 2)).mpr
  have hprod : (n : ℝ) ^ 2 / 2 ≤ ((n : ℝ) + 1) * ‖s + n‖ := by
    nlinarith [mul_le_mul_of_nonneg_left hlow (by positivity : 0 ≤ (n : ℝ) + 1)]
  nlinarith only [mul_le_mul_of_nonneg_left hprod (norm_nonneg (s - 1))]

private theorem gaussTerm_sum (s : ℂ) (hs : ∀ m : ℕ, s ≠ -(m : ℂ)) (N : ℕ) :
    ∑ n ∈ Finset.range N, gaussTerm s n =
      digamma s + Real.eulerMascheroniConstant + digamma (N + 1) - digamma (s + N) := by
  rw [add_comm (N : ℂ) 1, digamma_apply_add_nat (ne_neg_natCast_of_re_pos (by norm_num)) N,
    digamma_apply_add_nat hs N, digamma_one]
  simp only [gaussTerm, Finset.sum_sub_distrib, add_comm (1 : ℂ), one_div]
  ring

private noncomputable def gaussSeries (s : ℂ) : ℂ :=
  -Real.eulerMascheroniConstant + ∑' n, gaussTerm s n

private theorem hasSumLocallyUniformlyOn_gaussTerm :
    HasSumLocallyUniformlyOn (fun n s ↦ gaussTerm s n)
      (fun s ↦ ∑' n, gaussTerm s n) {s : ℂ | 0 < s.re} := by
  apply hasSumLocallyUniformlyOn_of_forall_compact (isOpen_re_gt 0)
  intro K hKU hK
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn continuous_id.continuousOn
  let C := max (R + 1) 1
  have hC : 0 ≤ C := le_trans zero_le_one (le_max_right _ _)
  have hu : Summable (fun n : ℕ ↦ C / (n : ℝ) ^ 2) := by
    exact ((Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))).mul_left C).congr
      (fun n ↦ by ring)
  apply HasSumUniformlyOn.of_norm_le_summable_eventually hu
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn s hs
  have hs0 : 0 < s.re := hKU hs
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hnum' : ‖s - 1‖ ≤ C := by
    calc ‖s - 1‖ ≤ ‖s‖ + 1 := by simpa using norm_sub_le s 1
         _ ≤ R + 1 := by simpa using add_le_add_right (hR s hs) 1
         _ ≤ C := le_max_left _ _
  have hden : (n : ℝ) ≤ ‖s + n‖ := by
    have h := Complex.re_le_norm (s + n)
    simp only [Complex.add_re, Complex.natCast_re] at h
    linarith
  have hsn : s + n ≠ 0 := norm_pos_iff.mp (by linarith)
  rw [gaussTerm_eq hsn, norm_div, norm_mul, norm_natCast_add_one]
  apply (div_le_div_iff₀ (by nlinarith : 0 < ((n : ℝ) + 1) * ‖s + n‖)
    (by positivity : 0 < (n : ℝ) ^ 2)).mpr
  have hprod : (n : ℝ) ^ 2 ≤ ((n : ℝ) + 1) * ‖s + n‖ := by
    nlinarith [mul_le_mul_of_nonneg_left hden (by positivity : 0 ≤ (n : ℝ) + 1)]
  nlinarith only [mul_le_mul_of_nonneg_right hnum' (sq_nonneg (n : ℝ)),
    mul_le_mul_of_nonneg_left hprod hC]

private theorem differentiableOn_gaussSeries :
    DifferentiableOn ℂ gaussSeries {s : ℂ | 0 < s.re} := by
  have hfinite (N : Finset ℕ) : DifferentiableOn ℂ
      (fun s ↦ ∑ n ∈ N, gaussTerm s n) {s : ℂ | 0 < s.re} := by
    apply DifferentiableOn.fun_sum
    intro n _
    unfold gaussTerm
    apply DifferentiableOn.sub (by fun_prop)
    apply DifferentiableOn.div (by fun_prop) (by fun_prop)
    intro s hs
    simpa only [ne_eq, add_eq_zero_iff_eq_neg] using ne_neg_natCast_of_re_pos hs n
  exact (hasSumLocallyUniformlyOn_gaussTerm.differentiableOn
    (Eventually.of_forall hfinite) (isOpen_re_gt 0)).const_add _

private theorem tendsto_psi_error :
    Tendsto (fun x : ℝ ↦ digamma (x : ℂ) - Complex.log (x : ℂ)) atTop (𝓝 0) :=
  isBigO_digamma_ofReal_sub_log.trans_tendsto tendsto_inv_atTop_zero

private theorem tendsto_digamma_nat_shift_diff {x : ℝ} (hx : 0 < x) :
    Tendsto (fun N : ℕ ↦ digamma ((N : ℝ) + 1) - digamma ((N : ℝ) + x)) atTop (𝓝 0) := by
  have ht1 : Tendsto (fun N : ℕ ↦ (N : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have htx : Tendsto (fun N : ℕ ↦ (N : ℝ) + x) atTop atTop :=
    tendsto_atTop_add_const_right atTop x tendsto_natCast_atTop_atTop
  have hlogs : Tendsto (fun N : ℕ ↦ Complex.log (((N : ℝ) + 1) : ℂ) -
      Complex.log (((N : ℝ) + x) : ℂ)) atTop (𝓝 0) := by
    have hr : Tendsto (fun N : ℕ ↦ Real.log ((N : ℝ) + 1) - Real.log ((N : ℝ) + x)) atTop
        (𝓝 0) := by
      simpa only [Function.comp_def, sub_sub_sub_cancel_right, sub_zero] using
        ((Real.tendsto_log_comp_add_sub_log 1).sub
          (Real.tendsto_log_comp_add_sub_log x)).comp tendsto_natCast_atTop_atTop
    have h := continuous_ofReal.continuousAt.tendsto.comp hr
    convert h using 1
    ext N
    dsimp only [Function.comp_apply]
    rw [Complex.ofReal_sub, ofReal_log (by positivity), ofReal_log (by positivity)]
    simp only [Complex.ofReal_add, Complex.ofReal_one]
  have h := ((tendsto_psi_error.comp ht1).sub (tendsto_psi_error.comp htx)).add hlogs
  convert h using 1
  · ext N
    simp only [Function.comp_apply]
    push_cast
    ring
  · simp

private theorem digamma_ofReal_eq_gaussSeries {x : ℝ} (hx : 0 < x) :
    digamma (x : ℂ) = gaussSeries x := by
  have hs := ne_neg_natCast_of_re_pos (by simpa using hx : 0 < (x : ℂ).re)
  have ht : Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.range N, gaussTerm x n) atTop
      (𝓝 (digamma (x : ℂ) + Real.eulerMascheroniConstant)) := by
    have h := (tendsto_digamma_nat_shift_diff hx).const_add
      (digamma (x : ℂ) + Real.eulerMascheroniConstant)
    convert h using 1
    · ext N
      rw [gaussTerm_sum (x : ℂ) hs]
      push_cast
      rw [add_comm (x : ℂ) (N : ℂ)]
      ring
    · simp
  have he := tendsto_nhds_unique (summable_gaussTerm _).hasSum.tendsto_sum_nat ht
  dsimp [gaussSeries]
  rw [he]
  ring

private theorem analyticOnNhd_digamma_pos :
    AnalyticOnNhd ℂ digamma {s : ℂ | 0 < s.re} := by
  have hΓ : AnalyticOnNhd ℂ Gamma {s : ℂ | 0 < s.re} := by
    apply DifferentiableOn.analyticOnNhd _ (isOpen_re_gt 0)
    intro s hs
    exact (differentiableAt_Gamma s (ne_neg_natCast_of_re_pos hs)).differentiableWithinAt
  simpa only [digamma_def, logDeriv, Pi.div_def] using
    hΓ.deriv.div hΓ (fun s hs ↦ Gamma_ne_zero (ne_neg_natCast_of_re_pos hs))

private theorem digamma_eq_gaussSeries_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    digamma s = gaussSeries s := by
  let v : ℕ → ℝ := fun n ↦ 1 + ((n : ℝ) + 1)⁻¹
  have hv : Tendsto v atTop (𝓝 1) := by
    have hn : Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    simpa only [v, add_zero, Function.comp_def] using (tendsto_inv_atTop_zero.comp hn).const_add 1
  have hvc : Tendsto (fun n ↦ (v n : ℂ)) atTop (𝓝 (1 : ℂ)) := by
    simpa only [Function.comp_def, ofReal_one] using continuous_ofReal.continuousAt.tendsto.comp hv
  have hvp : Tendsto (fun n ↦ (v n : ℂ)) atTop (𝓝[≠] (1 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hvc, Eventually.of_forall fun n ↦ ?_⟩
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    have hr := congrArg Complex.re h
    simp only [ofReal_re, one_re, v] at hr
    have hn : 0 < ((n : ℝ) + 1)⁻¹ := by positivity
    linarith
  have hfreq : ∃ᶠ z in 𝓝[≠] (1 : ℂ), digamma z = gaussSeries z := by
    apply hvp.frequently
    exact (Eventually.of_forall fun n ↦ digamma_ofReal_eq_gaussSeries
      (show 0 < v n by dsimp [v]; positivity)).frequently
  exact (analyticOnNhd_digamma_pos.eqOn_of_preconnected_of_frequently_eq
    (differentiableOn_gaussSeries.analyticOnNhd (isOpen_re_gt 0))
    (convex_halfSpace_re_gt 0).isPreconnected (by norm_num : (1 : ℂ) ∈ {s : ℂ | 0 < s.re})
    hfreq) hs

private theorem tendsto_inv_add_nat (s : ℂ) :
    Tendsto (fun N : ℕ ↦ (s + N)⁻¹) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp only [norm_inv]
  apply tendsto_inv_atTop_zero.comp
  apply tendsto_atTop_mono (fun n ↦ ?_)
    (tendsto_atTop_add_const_right atTop (-‖s‖) tendsto_natCast_atTop_atTop)
  simpa only [add_comm, Complex.norm_natCast, sub_eq_add_neg] using norm_sub_le_norm_add (n : ℂ) s

private theorem gaussSeries_add_one (s : ℂ) :
    gaussSeries (s + 1) = gaussSeries s + s⁻¹ := by
  have hsub := (summable_gaussTerm (s + 1)).sub (summable_gaussTerm s)
  have hfinite (N : ℕ) : ∑ n ∈ Finset.range N, (gaussTerm (s + 1) n - gaussTerm s n) =
      s⁻¹ - (s + N)⁻¹ := by
    have heq (n : ℕ) : gaussTerm (s + 1) n - gaussTerm s n =
        (s + n)⁻¹ - (s + (n + 1 : ℕ))⁻¹ := by
      simp only [gaussTerm, one_div, Nat.cast_add, Nat.cast_one]
      rw [add_right_comm s 1 (n : ℂ)]
      ring
    simp_rw [heq]
    simpa using Finset.sum_range_sub' (fun n : ℕ ↦ (s + n)⁻¹) N
  have ht : Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.range N,
      (gaussTerm (s + 1) n - gaussTerm s n)) atTop (𝓝 (s⁻¹)) := by
    simp_rw [hfinite]
    simpa using tendsto_const_nhds.sub (tendsto_inv_add_nat s)
  have hsum : ∑' n, (gaussTerm (s + 1) n - gaussTerm s n) = s⁻¹ :=
    tendsto_nhds_unique hsub.hasSum.tendsto_sum_nat ht
  rw [(summable_gaussTerm (s + 1)).tsum_sub (summable_gaussTerm s)] at hsum
  dsimp [gaussSeries]
  linear_combination hsum

private theorem gaussSeries_add_nat (s : ℂ) (N : ℕ) :
    gaussSeries (s + N) = gaussSeries s + ∑ n ∈ Finset.range N, (s + n)⁻¹ := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.cast_add, Nat.cast_one, ← add_assoc, gaussSeries_add_one,
      ih, Finset.sum_range_succ]
    ring

private theorem digamma_eq_gaussSeries_regular {s : ℂ} (hs : ∀ m : ℕ, s ≠ -(m : ℂ)) :
    digamma s = gaussSeries s := by
  let N := ⌈1 - s.re⌉₊
  have hpos : 0 < (s + N).re := by
    simp only [add_re, natCast_re]
    have hN := Nat.le_ceil (1 - s.re)
    dsimp only [N]
    linarith
  have h := digamma_eq_gaussSeries_of_re_pos hpos
  rw [digamma_apply_add_nat hs N, gaussSeries_add_nat s N] at h
  exact add_right_cancel h

/-- The paired summands in Gauss' digamma series form an absolutely convergent complex series
for every `s`. At a pole `s = -m`, the single term `1 / (s + m)` is `0` by convention. -/
theorem summable_gaussSeries (s : ℂ) :
    Summable (fun n : ℕ ↦ 1 / ((n : ℂ) + 1) - 1 / (s + n)) := summable_gaussTerm s

/-- Gauss' paired reciprocal series equals complex digamma away from its poles. -/
theorem digamma_eq_gaussSeries {s : ℂ} (hs : ∀ m : ℕ, s ≠ -(m : ℂ)) :
    digamma s = -Real.eulerMascheroniConstant +
      ∑' n : ℕ, (1 / ((n : ℂ) + 1) - 1 / (s + n)) := by
  simpa only [gaussSeries, gaussTerm] using digamma_eq_gaussSeries_regular hs

/-- The termwise difference `(s - w) / ((w + n) * (s + n))` of two Gauss digamma series is
summable for all complex `s` and `w`. -/
theorem summable_sub_div_add_mul_add (s w : ℂ) :
    Summable fun n : ℕ ↦ (s - w) / ((w + n) * (s + n)) := by
  refine ((summable_gaussSeries s).sub (summable_gaussSeries w)).congr_cofinite ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_ge_atTop (⌈‖s‖⌉₊ + ⌈‖w‖⌉₊ + 1)] with n hn
  have hnR : (⌈‖s‖⌉₊ : ℝ) + ⌈‖w‖⌉₊ + 1 ≤ n := by exact_mod_cast hn
  have hns : ‖s‖ < (n : ℝ) := by linarith [Nat.le_ceil ‖s‖, Nat.cast_nonneg (α := ℝ) ⌈‖w‖⌉₊]
  have hnw : ‖w‖ < (n : ℝ) := by linarith [Nat.le_ceil ‖w‖, Nat.cast_nonneg (α := ℝ) ⌈‖s‖⌉₊]
  have hs0 : s + n ≠ 0 := fun h ↦ hns.ne' (by simp [add_eq_zero_iff_eq_neg.mp h])
  have hw0 : w + n ≠ 0 := fun h ↦ hnw.ne' (by simp [add_eq_zero_iff_eq_neg.mp h])
  rw [sub_sub_sub_cancel_left, div_sub_div _ _ hw0 hs0]
  ring

/-- Away from the nonpositive integers, `digamma s - digamma w` equals the reciprocal-product
series `∑' n, (s - w) / ((w + n) * (s + n))`. -/
theorem digamma_sub_digamma_eq_tsum {s w : ℂ}
    (hs : ∀ m : ℕ, s ≠ -(m : ℂ)) (hw : ∀ m : ℕ, w ≠ -(m : ℂ)) :
    digamma s - digamma w = ∑' n : ℕ, (s - w) / ((w + n) * (s + n)) := by
  rw [digamma_eq_gaussSeries hs, digamma_eq_gaussSeries hw,
    add_sub_add_left_eq_sub, ← (summable_gaussSeries s).tsum_sub (summable_gaussSeries w)]
  refine tsum_congr fun n ↦ ?_
  have hs0 : s + n ≠ 0 := fun h ↦ hs n (add_eq_zero_iff_eq_neg.mp h)
  have hw0 : w + n ≠ 0 := fun h ↦ hw n (add_eq_zero_iff_eq_neg.mp h)
  rw [sub_sub_sub_cancel_left, div_sub_div _ _ hw0 hs0]
  ring

/-- Sharp Lipschitz bound for complex digamma on the closed half-plane `{s : ℂ | 1 ≤ s.re}`:
`‖digamma s - digamma w‖ ≤ ‖s - w‖ * (π² / 6)`. -/
theorem norm_digamma_sub_digamma_le_of_one_le_re {s w : ℂ}
    (hs : 1 ≤ s.re) (hw : 1 ≤ w.re) :
    ‖digamma s - digamma w‖ ≤ ‖s - w‖ * (Real.pi ^ 2 / 6) := by
  have hp2 : HasSum (fun n : ℕ ↦ 1 / ((n : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
    simpa [Nat.cast_add, Nat.cast_one] using (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
  have hsum := hp2.mul_left ‖s - w‖
  have hbd (n : ℕ) : ‖(s - w) / ((w + n) * (s + n))‖ ≤ ‖s - w‖ * (1 / ((n : ℝ) + 1) ^ 2) := by
    have hsn : (n : ℝ) + 1 ≤ ‖s + n‖ := by
      have := Complex.re_le_norm (s + n); simp at this; linarith
    have hwn : (n : ℝ) + 1 ≤ ‖w + n‖ := by
      have := Complex.re_le_norm (w + n); simp at this; linarith
    rw [norm_div, norm_mul, mul_one_div]
    exact div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
      (by nlinarith [n.cast_nonneg (α := ℝ)])
  rw [digamma_sub_digamma_eq_tsum (ne_neg_natCast_of_re_pos (by linarith))
    (ne_neg_natCast_of_re_pos (by linarith)), ← hsum.tsum_eq]
  exact (norm_tsum_le_tsum_norm (summable_sub_div_add_mul_add s w).norm).trans
    ((Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hbd hsum.summable).tsum_le_tsum
      hbd hsum.summable)

private theorem tendsto_log_add_natCast_sub_log (s : ℂ) :
    Tendsto (fun N : ℕ ↦ Complex.log (s + N) - Complex.log (((N : ℝ) + 2 : ℝ) : ℂ))
      atTop (𝓝 0) := by
  have hiR : Tendsto (fun N : ℕ ↦ ((N : ℝ) + 2)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop)
  have hi : Tendsto (fun N : ℕ ↦ ((N : ℂ) + 2)⁻¹) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ofReal_inv, ofReal_add, ofReal_natCast, ofReal_ofNat,
      ofReal_zero] using continuous_ofReal.continuousAt.tendsto.comp hiR
  let z : ℕ → ℂ := fun N ↦ 1 + (s - 2) * ((N : ℂ) + 2)⁻¹
  have hz : Tendsto z atTop (𝓝 (1 : ℂ)) := by
    simpa only [z, mul_zero, add_zero] using (hi.const_mul (s - 2)).const_add 1
  have hl : Tendsto (fun N : ℕ ↦ Complex.log (z N)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (continuousAt_clog one_mem_slitPlane).tendsto.comp hz
  have heq (N : ℕ) : s + N = z N * (((N : ℝ) + 2 : ℝ) : ℂ) := by
    dsimp [z]
    push_cast
    have hn : (N : ℂ) + 2 ≠ 0 := by
      intro hn
      have h := congrArg Complex.re hn
      norm_num at h
      linarith [Nat.cast_nonneg (α := ℝ) N]
    field_simp
    ring
  refine hl.congr' ?_
  filter_upwards [hz.eventually_ne one_ne_zero] with N hnz
  rw [heq N, Complex.log_mul_ofReal ((N : ℝ) + 2) (by positivity) (z N) hnz,
    ofReal_log (by positivity : (0 : ℝ) ≤ (N : ℝ) + 2)]
  ring

/-- Euler–Gauss limit representation of the digamma function: for every non-pole `s`
(`∀ n : ℕ, s ≠ -n`), `log (s + N) - ∑_{k ≤ N} (s + k)⁻¹ → ψ(s)` as `N → ∞`. -/
theorem tendsto_log_add_sub_sum_inv_add {s : ℂ} (hs : ∀ n : ℕ, s ≠ -(n : ℂ)) :
    Tendsto (fun N : ℕ ↦ Complex.log (s + N) - ∑ k ∈ Finset.Icc 0 N, (s + k)⁻¹)
      atTop (𝓝 (digamma s)) := by
  have hsum : Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.range (N + 1), gaussTerm s n) atTop
      (𝓝 (digamma s + Real.eulerMascheroniConstant)) := by
    have htsum : ∑' n : ℕ, gaussTerm s n = digamma s + Real.eulerMascheroniConstant := by
      rw [digamma_eq_gaussSeries_regular hs, gaussSeries]
      ring
    simpa only [Function.comp_def, htsum] using
      (summable_gaussTerm s).hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hpsi : Tendsto (fun N : ℕ ↦
      digamma (((N : ℝ) + 2 : ℝ) : ℂ) - Complex.log (((N : ℝ) + 2 : ℝ) : ℂ)) atTop (𝓝 0) :=
    tendsto_psi_error.comp (tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop)
  have h := (((hsum.add (tendsto_log_add_natCast_sub_log s)).sub hpsi).sub_const
    (Real.eulerMascheroniConstant : ℂ))
  convert h using 1
  · ext N
    have hg := gaussTerm_sum s hs (N + 1)
    have hd := digamma_apply_add_nat hs (N + 1)
    rw [Nat.range_succ_eq_Icc_zero] at hd
    have hN2 : (((N + 1 : ℕ) : ℂ) + 1) = (((N : ℝ) + 2 : ℝ) : ℂ) := by push_cast; ring
    rw [hN2, hd] at hg
    linear_combination -hg
  · simp

end Complex

namespace Real

private theorem gaussTerm_ofReal_re (x : ℝ) (n : ℕ) :
    (1 / ((n : ℂ) + 1) - 1 / ((x : ℂ) + n)).re = 1 / ((n : ℝ) + 1) - 1 / (x + n) := by
  have h : 1 / ((n : ℂ) + 1) - 1 / ((x : ℂ) + n) =
      ((1 / ((n : ℝ) + 1) - 1 / (x + n) : ℝ) : ℂ) := by
    push_cast; rfl
  rw [h, Complex.ofReal_re]

/-- The paired summands in Gauss' real digamma series are summable at every real `x`. -/
theorem summable_gaussSeries (x : ℝ) :
    Summable fun n : ℕ ↦ 1 / ((n : ℝ) + 1) - 1 / (x + n) :=
  (Complex.reCLM.summable (Complex.summable_gaussSeries (x : ℂ))).congr fun n ↦ by
    rw [Complex.reCLM_apply, gaussTerm_ofReal_re]

/-- Gauss' paired reciprocal series equals real digamma away from the nonpositive integers. -/
theorem digamma_eq_gaussSeries {x : ℝ} (hx : ∀ m : ℕ, x ≠ -(m : ℝ)) :
    digamma x = -eulerMascheroniConstant +
      ∑' n : ℕ, (1 / ((n : ℝ) + 1) - 1 / (x + n)) := by
  have h := congrArg Complex.re
    (Complex.digamma_eq_gaussSeries (s := x) fun m hm ↦ hx m (by exact_mod_cast hm))
  rw [Complex.digamma_ofReal, Complex.ofReal_re, Complex.add_re, Complex.neg_re, Complex.ofReal_re,
    ← Complex.reCLM_apply, Complex.reCLM.map_tsum (Complex.summable_gaussSeries (x : ℂ))] at h
  exact h.trans <| congrArg (-eulerMascheroniConstant + ·) <| tsum_congr fun n ↦ by
    rw [Complex.reCLM_apply, gaussTerm_ofReal_re]

/-- The real reciprocal-product series `(x - y) / ((y + n) * (x + n))` is summable for all
real `x` and `y`. -/
theorem summable_sub_div_add_mul_add (x y : ℝ) :
    Summable fun n : ℕ ↦ (x - y) / ((y + n) * (x + n)) :=
  (Complex.reCLM.summable (Complex.summable_sub_div_add_mul_add (x : ℂ) (y : ℂ))).congr fun n ↦ by
    rw [Complex.reCLM_apply]; norm_cast

/-- Away from the nonpositive integers, `Real.digamma x - Real.digamma y` equals
`∑' n, (x - y) / ((y + n) * (x + n))`. -/
theorem digamma_sub_digamma_eq_tsum {x y : ℝ}
    (hx : ∀ m : ℕ, x ≠ -(m : ℝ)) (hy : ∀ m : ℕ, y ≠ -(m : ℝ)) :
    digamma x - digamma y = ∑' n : ℕ, (x - y) / ((y + n) * (x + n)) := by
  have h := congrArg Complex.re (Complex.digamma_sub_digamma_eq_tsum
    (s := x) (w := y) (fun m hm ↦ hx m (by exact_mod_cast hm))
    (fun m hm ↦ hy m (by exact_mod_cast hm)))
  rw [Complex.digamma_ofReal, Complex.digamma_ofReal, ← Complex.ofReal_sub, Complex.ofReal_re,
    ← Complex.reCLM_apply,
    Complex.reCLM.map_tsum (Complex.summable_sub_div_add_mul_add (x : ℂ) (y : ℂ))] at h
  exact h.trans <| tsum_congr fun n ↦ by rw [Complex.reCLM_apply]; norm_cast

/-- Real digamma is strictly monotone on the positive real axis. -/
theorem strictMonoOn_digamma : StrictMonoOn digamma (Ioi 0) := by
  intro x hx y hy hxy
  rw [← sub_pos, digamma_sub_digamma_eq_tsum
    (fun m ↦ by linarith [mem_Ioi.mp hy, m.cast_nonneg (α := ℝ)])
    (fun m ↦ by linarith [mem_Ioi.mp hx, m.cast_nonneg (α := ℝ)])]
  refine (summable_sub_div_add_mul_add y x).tsum_pos (fun n ↦ div_nonneg (sub_nonneg.mpr hxy.le)
    (mul_pos (by linarith [mem_Ioi.mp hx, n.cast_nonneg (α := ℝ)])
      (by linarith [mem_Ioi.mp hy, n.cast_nonneg (α := ℝ)])).le) 0 ?_
  simpa using div_pos (sub_pos.mpr hxy) (mul_pos (mem_Ioi.mp hx) (mem_Ioi.mp hy))

/-- When `a < b`, the shifted digamma difference `t ↦ ψ(t + b) - ψ(t + a)` is strictly antitone
on `(-a, ∞)`. -/
theorem strictAntiOn_digamma_add_sub_digamma_add {a b : ℝ} (hab : a < b) :
    StrictAntiOn (fun t : ℝ ↦ digamma (t + b) - digamma (t + a)) (Ioi (-a)) := by
  intro t₁ ht₁ t₂ _ ht
  have hreg {u : ℝ} (hu : 0 < u) (m : ℕ) : u ≠ -(m : ℝ) := by linarith [m.cast_nonneg (α := ℝ)]
  have h0 := mem_Ioi.mp ht₁
  dsimp only
  rw [digamma_sub_digamma_eq_tsum (hreg (by linarith)) (hreg (by linarith)),
    digamma_sub_digamma_eq_tsum (hreg (by linarith)) (hreg (by linarith))]
  refine (summable_sub_div_add_mul_add (t₂ + b) (t₂ + a)).tsum_lt_tsum (i := 0) (fun n ↦ ?_) ?_
    (summable_sub_div_add_mul_add (t₁ + b) (t₁ + a))
  · simp only [add_sub_add_left_eq_sub]
    have _ := n.cast_nonneg (α := ℝ)
    exact div_le_div_of_nonneg_left (sub_nonneg.mpr hab.le) (mul_pos (by linarith) (by linarith))
      (mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith))
  · simp only [add_sub_add_left_eq_sub, Nat.cast_zero, add_zero]
    exact div_lt_div_of_pos_left (sub_pos.mpr hab) (mul_pos (by linarith) (by linarith))
      (mul_lt_mul'' (by linarith) (by linarith) (by linarith) (by linarith))

/-- When `a ≤ b`, the shifted digamma difference `t ↦ ψ(t + b) - ψ(t + a)` is antitone on
`(-a, ∞)`. -/
theorem antitoneOn_digamma_add_sub_digamma_add {a b : ℝ} (hab : a ≤ b) :
    AntitoneOn (fun t : ℝ ↦ digamma (t + b) - digamma (t + a)) (Ioi (-a)) := by
  rcases hab.eq_or_lt with rfl | hlt
  · intro _ _ _ _ _; simp
  · exact (strictAntiOn_digamma_add_sub_digamma_add hlt).antitoneOn

/-- Uniform upper bound on shifted digamma differences: for `t₀ ≤ t`, `-t₀ < c`, `c ≤ a`, and
`c ≤ b`, `ψ(t + b) - ψ(t + a) ≤ ψ(t₀ + b) - ψ(t₀ + c)` (generalizing CDT Lemma 5.2.9). -/
theorem digamma_add_sub_digamma_add_le {t₀ t c a b : ℝ}
    (ht : t₀ ≤ t) (hc : -t₀ < c) (hca : c ≤ a) (hcb : c ≤ b) :
    digamma (t + b) - digamma (t + a) ≤ digamma (t₀ + b) - digamma (t₀ + c) :=
  (sub_le_sub_left (monotoneOn_digamma
    (mem_Ioi.mpr (by linarith)) (mem_Ioi.mpr (by linarith)) (by linarith)) _).trans <|
    antitoneOn_digamma_add_sub_digamma_add hcb
      (mem_Ioi.mpr (by linarith)) (mem_Ioi.mpr (by linarith)) ht

section EulerIntegral

open MeasureTheory

private theorem abs_rpow_sub_one_div_one_sub_le {a w : ℝ} (ha : 0 < a) (hw : w ∈ Ioo (0 : ℝ) 1) :
    |(w ^ (a - 1) - 1) / (1 - w)| ≤ w ^ (a - 1) + (⌈a⌉₊ : ℝ) := by
  have h1w : 0 < 1 - w := sub_pos.mpr hw.2
  rw [abs_div, abs_of_pos h1w, div_le_iff₀ h1w]
  rcases le_or_gt a 1 with ha1 | ha1
  · have hge : 1 ≤ w ^ (a - 1) := by
      simpa using rpow_le_rpow_of_exponent_ge hw.1 hw.2.le (by linarith : a - 1 ≤ 0)
    have hwa : w ^ (a - 1) * w = w ^ a := by rw [← rpow_add_one hw.1.ne', sub_add_cancel]
    have hle1 : w ^ a ≤ 1 := rpow_le_one hw.1.le hw.2.le ha.le
    rw [abs_of_nonneg (sub_nonneg.mpr hge)]
    nlinarith [Nat.cast_nonneg (α := ℝ) ⌈a⌉₊]
  · have hle : w ^ (a - 1) ≤ 1 := rpow_le_one hw.1.le hw.2.le (by linarith)
    have hpow : w ^ ⌈a⌉₊ ≤ w ^ (a - 1) := by
      rw [← rpow_natCast]
      exact rpow_le_rpow_of_exponent_ge hw.1 hw.2.le (by linarith [Nat.le_ceil a])
    have hgeom := geom_sum_mul w ⌈a⌉₊
    have hsum_le : ∑ i ∈ Finset.range ⌈a⌉₊, w ^ i ≤ (⌈a⌉₊ : ℝ) :=
      (Finset.sum_le_card_nsmul _ _ 1 fun i _ ↦ pow_le_one₀ hw.1.le hw.2.le).trans_eq (by simp)
    rw [abs_of_nonpos (sub_nonpos.mpr hle), neg_sub]
    nlinarith [rpow_nonneg hw.1.le (a - 1)]

/-- For every `0 < a`, the Euler digamma kernel `(w ^ (a - 1) - 1) / (1 - w)` is interval
integrable on `[0, 1]`. -/
theorem intervalIntegrable_rpow_sub_one_div_one_sub {a : ℝ} (ha : 0 < a) :
    IntervalIntegrable (fun w : ℝ ↦ (w ^ (a - 1) - 1) / (1 - w)) volume 0 1 := by
  have hdom : IntervalIntegrable (fun w : ℝ ↦ w ^ (a - 1) + (⌈a⌉₊ : ℝ)) volume 0 1 :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith)).add intervalIntegrable_const
  rw [intervalIntegrable_iff, IntegrableOn, uIoc_of_le zero_le_one,
    ← Measure.restrict_congr_set Ioo_ae_eq_Ioc] at hdom ⊢
  refine hdom.mono' ((((ContinuousOn.rpow_const (s := Ioo (0 : ℝ) 1) continuousOn_id
    fun w hw ↦ Or.inl hw.1.ne').sub continuousOn_const).div (continuousOn_const.sub continuousOn_id)
      fun w hw ↦ sub_ne_zero.mpr hw.2.ne').aestronglyMeasurable measurableSet_Ioo) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with w hw
  simpa only [Real.norm_eq_abs] using abs_rpow_sub_one_div_one_sub_le ha hw

private theorem integral_finset_rpow_sub_pow {a : ℝ} (ha : 0 < a) (N : ℕ) :
    ∫ w in (0 : ℝ)..1, (∑ k ∈ Finset.range N, (w ^ ((k : ℝ) + a - 1) - w ^ k)) =
      ∑ k ∈ Finset.range N, (1 / ((k : ℝ) + a) - 1 / ((k : ℝ) + 1)) := by
  rw [intervalIntegral.integral_finsetSum fun k _ ↦
    (intervalIntegral.intervalIntegrable_rpow' (by linarith [k.cast_nonneg (α := ℝ)])).sub
      (Continuous.intervalIntegrable (by fun_prop) 0 1)]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have hka : (0 : ℝ) < (k : ℝ) + a := by linarith [k.cast_nonneg (α := ℝ)]
  rw [intervalIntegral.integral_sub (intervalIntegral.intervalIntegrable_rpow' (by linarith))
      (Continuous.intervalIntegrable (by fun_prop) 0 1),
    integral_rpow (Or.inl (by linarith)), integral_pow, sub_add_cancel, one_rpow,
    zero_rpow hka.ne']
  simp [zero_pow (Nat.succ_ne_zero k)]

/-- **Euler's integral representation of real digamma** (DLMF 5.9.16): for every `0 < a`,
`∫ w in (0 : ℝ)..1, (w ^ (a - 1) - 1) / (1 - w) = digamma 1 - digamma a`
(equivalently `-eulerMascheroniConstant - digamma a`). -/
theorem integral_rpow_sub_one_div_one_sub {a : ℝ} (ha : 0 < a) :
    ∫ w in (0 : ℝ)..1, (w ^ (a - 1) - 1) / (1 - w) = digamma 1 - digamma a := by
  let F : ℕ → ℝ → ℝ := fun N w ↦ ∑ k ∈ Finset.range N, (w ^ ((k : ℝ) + a - 1) - w ^ k)
  have hrpow_mul {w : ℝ} (hw : 0 < w) (k : ℕ) :
      w ^ ((k : ℝ) + a - 1) - w ^ k = (w ^ (a - 1) - 1) * w ^ k := by
    rw [sub_mul, one_mul, (by ring : (k : ℝ) + a - 1 = (a - 1) + k), rpow_add hw, rpow_natCast]
  have hdct : Tendsto (fun N ↦ ∫ w in (0 : ℝ)..1, F N w) atTop
      (𝓝 (∫ w in (0 : ℝ)..1, (w ^ (a - 1) - 1) / (1 - w))) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (F := F)
      (fun w ↦ w ^ (a - 1) + (⌈a⌉₊ : ℝ)) (Eventually.of_forall fun N ↦ ?_)
      (Eventually.of_forall fun N ↦ ?_)
      ((intervalIntegral.intervalIntegrable_rpow' (by linarith)).add intervalIntegrable_const) ?_
    · exact (intervalIntegrable_iff.mp (IntervalIntegrable.sum (Finset.range N) fun k _ ↦
        (intervalIntegral.intervalIntegrable_rpow' (by linarith [k.cast_nonneg (α := ℝ)])).sub
          (Continuous.intervalIntegrable (by fun_prop) 0 1))).aestronglyMeasurable.congr
        (Eventually.of_forall fun w ↦ Finset.sum_apply w _ _)
    · filter_upwards [Measure.ae_ne volume (1 : ℝ)] with w hw1 hw
      rw [uIoc_of_le zero_le_one] at hw
      have hwoo : w ∈ Ioo (0 : ℝ) 1 := ⟨hw.1, lt_of_le_of_ne hw.2 hw1⟩
      have hFN : F N w = (w ^ (a - 1) - 1) * ∑ k ∈ Finset.range N, w ^ k := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ ↦ hrpow_mul hwoo.1 k
      rw [hFN, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (Finset.sum_nonneg fun k _ ↦ pow_nonneg hwoo.1.le k)]
      refine (mul_le_mul_of_nonneg_left (sum_le_hasSum _ (fun _ _ ↦ pow_nonneg hwoo.1.le _)
        (hasSum_geometric_of_lt_one hwoo.1.le hwoo.2)) (abs_nonneg _)).trans ?_
      rw [← abs_of_pos (inv_pos.mpr (sub_pos.mpr hwoo.2)), ← abs_mul, ← div_eq_mul_inv]
      exact abs_rpow_sub_one_div_one_sub_le ha hwoo
    · filter_upwards [Measure.ae_ne volume (1 : ℝ)] with w hw1 hw
      rw [uIoc_of_le zero_le_one] at hw
      exact (div_eq_mul_inv (w ^ (a - 1) - 1) (1 - w) ▸
        ((hasSum_geometric_of_lt_one hw.1.le (lt_of_le_of_ne hw.2 hw1)).mul_left _).congr_fun
          fun k ↦ hrpow_mul hw.1 k).tendsto_sum_nat
  simp_rw [F, integral_finset_rpow_sub_pow ha] at hdct
  have hd := digamma_eq_gaussSeries (x := a) fun m ↦ by linarith [m.cast_nonneg (α := ℝ)]
  have hgauss := (summable_gaussSeries a).hasSum.neg
  rw [(by rw [digamma_one]; linarith :
    -(∑' n : ℕ, (1 / ((n : ℝ) + 1) - 1 / (a + n))) = digamma 1 - digamma a)] at hgauss
  exact tendsto_nhds_unique hdct (hgauss.congr_fun fun k ↦ by ring).tendsto_sum_nat

end EulerIntegral

end Real
