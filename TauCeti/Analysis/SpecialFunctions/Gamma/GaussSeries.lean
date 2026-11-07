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

/-!
# Gauss' series for digamma

At every complex point outside the nonpositive integers, the paired reciprocal series
`∑' n, (1 / (n + 1) - 1 / (s + n))` converges absolutely and equals `digamma s + γ`.
The same statements hold for real arguments. Pairing is essential: the two reciprocal
series do not converge separately.

The proof first identifies the sum on the positive real axis using the digamma recurrence
and its explicit logarithmic asymptotic. Local uniform convergence extends the identity
through the right half-plane by the identity theorem. Recurrences for the sum and digamma
then extend it to every regular complex point.

## References and API provenance

* [NIST DLMF, equation 5.7.6](https://dlmf.nist.gov/5.7.E6).
* The public theorem names and statements follow Terence Tao's active
  [Mathlib PR #43556](https://github.com/leanprover-community/mathlib4/pull/43556).
  The auxiliary series and the right-half-plane continuation argument are private.
-/

public section

open Complex Real Filter Set Topology Asymptotics

namespace Complex

private noncomputable def gaussTerm (s : ℂ) (n : ℕ) : ℂ :=
  1 / ((n : ℂ) + 1) - 1 / (s + n)

private theorem gaussTerm_eq {s : ℂ} (hs : ∀ m : ℕ, s ≠ -(m : ℂ)) (n : ℕ) :
    gaussTerm s n = (s - 1) / (((n : ℂ) + 1) * (s + n)) := by
  have hsn : s + (n : ℂ) ≠ 0 := by simpa only [ne_eq, add_eq_zero_iff_eq_neg] using hs n
  rw [gaussTerm, div_sub_div _ _ n.cast_add_one_ne_zero hsn]
  ring

private theorem summable_gaussTerm {s : ℂ} (hs : ∀ m : ℕ, s ≠ -(m : ℂ)) :
    Summable (gaussTerm s) := by
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
  have hn1 : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using Complex.norm_natCast (n + 1)
  rw [gaussTerm_eq hs, norm_div, norm_mul, hn1]
  have hden : 0 < ((n : ℝ) + 1) * ‖s + n‖ :=
    mul_pos (by linarith) (by linarith)
  apply (div_le_div_iff₀ hden (by positivity : 0 < (n : ℝ) ^ 2)).mpr
  have hprod : (n : ℝ) ^ 2 / 2 ≤ ((n : ℝ) + 1) * ‖s + n‖ := by
    nlinarith [mul_le_mul_of_nonneg_left hlow (by positivity : 0 ≤ (n : ℝ) + 1)]
  nlinarith only [mul_le_mul_of_nonneg_left hprod (norm_nonneg (s - 1))]

private theorem gaussTerm_sum (s : ℂ) (hs : ∀ m : ℕ, s ≠ -(m : ℂ)) (N : ℕ) :
    ∑ n ∈ Finset.range N, gaussTerm s n =
      digamma s + Real.eulerMascheroniConstant + digamma (N + 1) - digamma (s + N) := by
  have h1 : ∀ m : ℕ, (1 : ℂ) ≠ -(m : ℂ) := by
    intro m hm
    have h := congrArg Complex.re hm
    simp only [one_re, neg_re, natCast_re] at h
    linarith [Nat.cast_nonneg (α := ℝ) m]
  rw [add_comm (N : ℂ) 1, digamma_apply_add_nat h1 N, digamma_apply_add_nat hs N, digamma_one]
  simp only [gaussTerm, Finset.sum_sub_distrib, add_comm (1 : ℂ), one_div]
  ring

private theorem nonpole_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    ∀ m : ℕ, s ≠ -(m : ℂ) := by
  intro m hm
  have h := congrArg Complex.re hm
  simp only [Complex.neg_re, Complex.natCast_re] at h
  linarith [Nat.cast_nonneg (α := ℝ) m]

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
  have hn1 : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using Complex.norm_natCast (n + 1)
  rw [gaussTerm_eq (nonpole_of_re_pos hs0), norm_div, norm_mul, hn1]
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
    simpa only [ne_eq, add_eq_zero_iff_eq_neg] using nonpole_of_re_pos hs n
  exact (hasSumLocallyUniformlyOn_gaussTerm.differentiableOn
    (Eventually.of_forall hfinite) (isOpen_re_gt 0)).const_add _

private theorem tendsto_psi_error :
    Tendsto (fun x : ℝ ↦ digamma (x : ℂ) - Complex.log (x : ℂ)) atTop (𝓝 0) :=
  isBigO_digamma_ofReal_sub_log.trans_tendsto tendsto_inv_atTop_zero

private theorem tendsto_log_nat_shift_diff {x : ℝ} (hx : 0 < x) :
    Tendsto (fun N : ℕ ↦ Real.log ((N : ℝ) + 1) - Real.log ((N : ℝ) + x)) atTop (𝓝 0) := by
  have ht : Tendsto (fun N : ℕ ↦ (N : ℝ) + x) atTop atTop :=
    tendsto_atTop_add_const_right atTop x tendsto_natCast_atTop_atTop
  have hi := tendsto_inv_atTop_zero.comp ht
  have hr : Tendsto (fun N : ℕ ↦ ((N : ℝ) + 1) / ((N : ℝ) + x)) atTop (𝓝 1) := by
    have h := (hi.const_mul (1 - x)).const_add 1
    convert h using 1
    · ext N
      have hNx : (N : ℝ) + x ≠ 0 := by positivity
      dsimp only [Function.comp_apply]
      field_simp [hNx]
      ring
    · simp
  have hl := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hr
  convert hl using 1
  · ext N
    change Real.log ((N : ℝ) + 1) - Real.log ((N : ℝ) + x) =
      Real.log (((N : ℝ) + 1) / ((N : ℝ) + x))
    exact (Real.log_div (by positivity) (by positivity)).symm
  · simp

private theorem tendsto_digamma_nat_shift_diff {x : ℝ} (hx : 0 < x) :
    Tendsto (fun N : ℕ ↦ digamma ((N : ℝ) + 1) - digamma ((N : ℝ) + x)) atTop (𝓝 0) := by
  have ht1 : Tendsto (fun N : ℕ ↦ (N : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have htx : Tendsto (fun N : ℕ ↦ (N : ℝ) + x) atTop atTop :=
    tendsto_atTop_add_const_right atTop x tendsto_natCast_atTop_atTop
  have hlogs : Tendsto (fun N : ℕ ↦ Complex.log (((N : ℝ) + 1) : ℂ) -
      Complex.log (((N : ℝ) + x) : ℂ)) atTop (𝓝 0) := by
    have h := continuous_ofReal.continuousAt.tendsto.comp (tendsto_log_nat_shift_diff hx)
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
  have hs := nonpole_of_re_pos (by simpa using hx : 0 < (x : ℂ).re)
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
  have he := tendsto_nhds_unique (summable_gaussTerm hs).hasSum.tendsto_sum_nat ht
  dsimp [gaussSeries]
  rw [he]
  ring

private theorem analyticOnNhd_digamma_pos :
    AnalyticOnNhd ℂ digamma {s : ℂ | 0 < s.re} := by
  have hΓ : AnalyticOnNhd ℂ Gamma {s : ℂ | 0 < s.re} := by
    apply DifferentiableOn.analyticOnNhd _ (isOpen_re_gt 0)
    intro s hs
    exact (differentiableAt_Gamma s (nonpole_of_re_pos hs)).differentiableWithinAt
  simpa only [digamma_def, logDeriv, Pi.div_def] using
    hΓ.deriv.div hΓ (fun s hs ↦ Gamma_ne_zero (nonpole_of_re_pos hs))

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
    change (v n : ℂ) ≠ 1
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

private theorem nonpole_add_nat {s : ℂ} (hs : ∀ m : ℕ, s ≠ -(m : ℂ)) (N : ℕ) :
    ∀ m : ℕ, s + N ≠ -(m : ℂ) := by
  intro m hm
  apply hs (m + N)
  push_cast at hm ⊢
  linear_combination hm

private theorem tendsto_inv_add_nat (s : ℂ) :
    Tendsto (fun N : ℕ ↦ (s + N)⁻¹) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp only [norm_inv]
  apply tendsto_inv_atTop_zero.comp
  apply tendsto_atTop_mono (fun n ↦ ?_)
    (tendsto_atTop_add_const_right atTop (-‖s‖) tendsto_natCast_atTop_atTop)
  simpa only [add_comm, Complex.norm_natCast, sub_eq_add_neg] using norm_sub_le_norm_add (n : ℂ) s

private theorem gaussSeries_add_one {s : ℂ} (hs : ∀ m : ℕ, s ≠ -(m : ℂ)) :
    gaussSeries (s + 1) = gaussSeries s + s⁻¹ := by
  have hs1 : ∀ m : ℕ, s + 1 ≠ -(m : ℂ) := by simpa using nonpole_add_nat hs 1
  have hsub := (summable_gaussTerm hs1).sub (summable_gaussTerm hs)
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
  rw [(summable_gaussTerm hs1).tsum_sub (summable_gaussTerm hs)] at hsum
  dsimp [gaussSeries]
  linear_combination hsum

private theorem gaussSeries_add_nat {s : ℂ} (hs : ∀ m : ℕ, s ≠ -(m : ℂ)) (N : ℕ) :
    gaussSeries (s + N) = gaussSeries s + ∑ n ∈ Finset.range N, (s + n)⁻¹ := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.cast_add, Nat.cast_one, ← add_assoc, gaussSeries_add_one (nonpole_add_nat hs N),
      ih, Finset.sum_range_succ]
    ring

private theorem digamma_eq_gaussSeries_regular {s : ℂ} (hs : ∀ m : ℕ, s ≠ -(m : ℂ)) :
    digamma s = gaussSeries s := by
  let N := ⌈1 - s.re⌉₊
  have hpos : 0 < (s + N).re := by
    simp only [add_re, natCast_re]
    have hN := Nat.le_ceil (1 - s.re)
    change 0 < s.re + (⌈1 - s.re⌉₊ : ℝ)
    linarith
  have h := digamma_eq_gaussSeries_of_re_pos hpos
  rw [digamma_apply_add_nat hs N, gaussSeries_add_nat hs N] at h
  exact add_right_cancel h

/-- The paired summands in Gauss' digamma series form an absolutely convergent complex series
at every regular point. -/
theorem summable_gaussSeries {s : ℂ} (hs : ∀ m : ℕ, s ≠ -(m : ℂ)) :
    Summable (fun n : ℕ ↦ 1 / ((n : ℂ) + 1) - 1 / (s + n)) := summable_gaussTerm hs

/-- Gauss' paired reciprocal series equals complex digamma away from its poles. -/
theorem digamma_eq_gaussSeries {s : ℂ} (hs : ∀ m : ℕ, s ≠ -(m : ℂ)) :
    digamma s = -Real.eulerMascheroniConstant +
      ∑' n : ℕ, (1 / ((n : ℂ) + 1) - 1 / (s + n)) := by
  simpa only [gaussSeries, gaussTerm] using digamma_eq_gaussSeries_regular hs

end Complex

namespace Real

/-- The paired summands in the real Gauss series are summable at each regular real point. -/
theorem summable_gaussSeries {x : ℝ} (hx : ∀ m : ℕ, x ≠ -(m : ℝ)) :
    Summable (fun n : ℕ ↦ 1 / ((n : ℝ) + 1) - 1 / (x + n)) := by
  apply Complex.summable_ofReal.mp
  have hc : ∀ m : ℕ, (x : ℂ) ≠ -(m : ℂ) := fun m h ↦ hx m (by exact_mod_cast h)
  simpa only [Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_add,
    Complex.ofReal_one, Complex.ofReal_natCast] using Complex.summable_gaussSeries hc

/-- Gauss' paired reciprocal series equals real digamma away from its poles. -/
theorem digamma_eq_gaussSeries {x : ℝ} (hx : ∀ m : ℕ, x ≠ -(m : ℝ)) :
    digamma x = -eulerMascheroniConstant +
      ∑' n : ℕ, (1 / ((n : ℝ) + 1) - 1 / (x + n)) := by
  have hc : ∀ m : ℕ, (x : ℂ) ≠ -(m : ℂ) := fun m h ↦ hx m (by exact_mod_cast h)
  apply Complex.ofReal_injective
  push_cast
  simpa [← Complex.digamma_ofReal] using Complex.digamma_eq_gaussSeries hc

end Real
