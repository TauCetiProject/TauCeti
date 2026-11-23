/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.MellinTransform.Basic

/-!
# Mellin transforms of compactly supported functions

If `f : ℝ → E` is locally integrable on `(0, ∞)` and supported inside a compact interval
`[a, b] ⊂ (0, ∞)` on `(0, ∞)` (that is, `Function.support f ∩ Ioi 0 ⊆ Icc a b`), then its Mellin
transform `mellin f` converges absolutely on all of `ℂ`, is entire, and is uniformly bounded on
every vertical strip `σ₁ ≤ Re s ≤ σ₂`.

For real-valued functions `ν : ℝ → ℝ` with `Function.support ν ∩ Ioi 0 ⊆ Icc a b` and
`∫₀^∞ ν(x) dx / x = 1`, this file also records the exact integral formula
`mellin ν ε - 1 = ∫₀^∞ (x ^ ε - 1) (ν x / x) dx` (`TauCeti.mellin_ofReal_sub_one_eq`) and the
quantitative bound `‖mellin ν ε - 1‖ ≤ max b 1 * max |log a| |log b| * ε` for `0 ≤ ε ≤ 1` when
`ν ≥ 0` on `(0, ∞)` (`TauCeti.norm_mellin_ofReal_sub_one_le`).

When `f` is `C^k` on `(0, ∞)` with `Function.support f ∩ Ioi 0 ⊆ Icc a b`, repeated integration
by parts with vanishing boundary terms yields
`(∏ j ∈ Finset.range k, (s + j)) • mellin f s = (-1) ^ k • mellin (iteratedDeriv k f) (s + k)`
for every `s : ℂ`, giving vertical-strip decay `‖mellin f s‖ ≤ C / (1 + ‖s‖) ^ k` on every strip
`σ₁ ≤ Re s ≤ σ₂`.

## Main results

* `MellinConvergent.of_support_subset_Icc`, `TauCeti.mellinConvergent_of_support_subset_Icc`,
  `TauCeti.differentiable_mellin_of_support_subset_Icc`: entireness and all-`s` Mellin convergence
  of a function supported in `[a, b] ⊂ (0, ∞)` on `(0, ∞)`.
* `TauCeti.norm_mellin_le_of_support_subset_Icc`: explicit uniform bound on vertical strips.
* `TauCeti.mellin_ofReal_sub_one_eq`, `TauCeti.norm_mellin_ofReal_sub_one_le`: exact difference
  formula and quantitative bound for `mellin ν ε - 1`.
* `TauCeti.smul_mellin_eq_neg_mellin_deriv`,
  `TauCeti.prod_smul_mellin_eq_neg_one_pow_smul_mellin_iteratedDeriv`: single and iterated
  integration by parts.
* `TauCeti.exists_norm_mellin_le_of_contDiffOn_of_support_subset_Icc`: vertical-strip decay
  `O((1 + ‖s‖)⁻ᵏ)` for `C^k` functions supported in `[a, b] ⊂ (0, ∞)` on `(0, ∞)`.

## References

* A. Kontorovich, T. Tao and contributors, *Prime Number Theorem And …*, §4.3 (Mellin transforms
  of compactly supported bumps).
-/

public section

open MeasureTheory Complex Set Filter Asymptotics
open scoped Topology

/-- If `f` has `Function.support f ∩ Ioi 0 ⊆ Icc a b` with `0 < a` and is Mellin convergent at
some `s₀`, then `f` is Mellin convergent at every `s : ℂ`. -/
theorem MellinConvergent.of_support_subset_Icc {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f : ℝ → E} {a b : ℝ} {s₀ : ℂ} (hf : MellinConvergent f s₀) (ha : 0 < a)
    (hsupp : Function.support f ∩ Ioi 0 ⊆ Icc a b) (s : ℂ) :
    MellinConvergent f s := by
  by_cases hab : a ≤ b
  · set M := max (a ^ (s.re - s₀.re)) (b ^ (s.re - s₀.re))
    have hcont : ContinuousOn (fun t : ℝ ↦ (t : ℂ) ^ (s - s₀)) (Ioi 0) :=
      continuousOn_of_forall_continuousAt fun t ht ↦
        continuousAt_ofReal_cpow_const _ _ (Or.inr (ne_of_gt ht))
    have hEq : ∀ t ∈ Ioi (0 : ℝ),
        (t : ℂ) ^ (s - 1) • f t = (t : ℂ) ^ (s - s₀) • ((t : ℂ) ^ (s₀ - 1) • f t) := fun t ht ↦ by
      rw [smul_smul, ← cpow_add _ _ (ofReal_ne_zero.mpr (ne_of_gt ht))]
      congr 2
      ring
    have hmeas : AEStronglyMeasurable (fun t : ℝ ↦ (t : ℂ) ^ (s - 1) • f t)
        (volume.restrict (Ioi (0 : ℝ))) :=
      ((hcont.aestronglyMeasurable measurableSet_Ioi).smul hf.aestronglyMeasurable).congr
        ((ae_restrict_mem measurableSet_Ioi).mono fun t ht ↦ (hEq t ht).symm)
    refine (hf.norm.const_mul M).mono' hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [hEq t ht, norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht, sub_re]
    by_cases hft : f t = 0
    · simp [hft]
    · have htab : t ∈ Icc a b := hsupp ⟨hft, ht⟩
      have hpow : t ^ (s.re - s₀.re) ≤ M := by
        rcases le_or_gt 0 (s.re - s₀.re) with hr | hr
        · exact (Real.rpow_le_rpow (ha.le.trans htab.1) htab.2 hr).trans (le_max_right _ _)
        · exact (Real.rpow_le_rpow_of_nonpos ha htab.1 hr.le).trans (le_max_left _ _)
      exact mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
  · have hzero : EqOn (fun t : ℝ ↦ (t : ℂ) ^ (s - 1) • f t) 0 (Ioi 0) := fun t ht ↦ by
      have hft : f t = 0 := Function.notMem_support.mp fun h ↦ by
        have hmem := hsupp ⟨h, ht⟩
        rw [Icc_eq_empty hab] at hmem
        exact hmem
      simp [hft]
    exact (integrableOn_zero (s := Ioi (0 : ℝ))).congr_fun (fun t ht ↦ (hzero ht).symm)
      measurableSet_Ioi

namespace TauCeti

section Basic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- If `f` has `Function.support f ∩ Ioi 0 ⊆ Icc a b` with `0 < a`, its Mellin transform equals
the set integral over `[a, b]`. -/
theorem mellin_eq_setIntegral_Icc_of_support_subset {f : ℝ → E} {a b : ℝ} (ha : 0 < a)
    (hsupp : Function.support f ∩ Ioi 0 ⊆ Icc a b) (s : ℂ) :
    mellin f s = ∫ t in Icc a b, (t : ℂ) ^ (s - 1) • f t := by
  have hIcc : Icc a b ⊆ Ioi (0 : ℝ) := fun _ ht ↦ ha.trans_le ht.1
  rw [mellin]
  refine setIntegral_eq_of_subset_of_ae_sdiff_eq_zero measurableSet_Ioi.nullMeasurableSet hIcc ?_
  refine Eventually.of_forall fun t ht ↦ ?_
  have hft : f t = 0 := Function.notMem_support.mp fun h ↦ ht.2 (hsupp ⟨h, ht.1⟩)
  simp [hft]

/-- If `f` has `Function.support f ∩ Ioi 0 ⊆ Icc a b` with `0 < a ≤ b`, its Mellin transform
equals the interval integral over `a..b`. -/
theorem mellin_eq_intervalIntegral_of_support_subset_Icc {f : ℝ → E} {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hsupp : Function.support f ∩ Ioi 0 ⊆ Icc a b) (s : ℂ) :
    mellin f s = ∫ t in a..b, (t : ℂ) ^ (s - 1) • f t := by
  rw [mellin_eq_setIntegral_Icc_of_support_subset ha hsupp s,
    MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]

omit [NormedSpace ℂ E] in
private lemma eventually_eq_zero_atTop_of_support_inter_Ioi_subset {f : ℝ → E} {a b : ℝ}
    (hsupp : Function.support f ∩ Ioi 0 ⊆ Icc a b) :
    f =ᶠ[atTop] 0 := by
  filter_upwards [eventually_gt_atTop (max b 0)] with t ht
  exact Function.notMem_support.mp fun h ↦
    (lt_of_le_of_lt (le_max_left b 0) ht).not_ge
      (hsupp ⟨h, lt_of_le_of_lt (le_max_right b 0) ht⟩).2

omit [NormedSpace ℂ E] in
private lemma eventually_eq_zero_nhdsGT_of_support_inter_Ioi_subset {f : ℝ → E} {a b : ℝ}
    (ha : 0 < a) (hsupp : Function.support f ∩ Ioi 0 ⊆ Icc a b) :
    f =ᶠ[𝓝[>] 0] 0 := by
  filter_upwards [Ioo_mem_nhdsGT ha] with t ht
  exact Function.notMem_support.mp fun h ↦ ht.2.not_ge (hsupp ⟨h, ht.1⟩).1

/-- A locally integrable function on `(0, ∞)` with `Function.support f ∩ Ioi 0 ⊆ Icc a b` (`0 < a`)
is Mellin convergent at every `s : ℂ`. -/
theorem mellinConvergent_of_support_subset_Icc {f : ℝ → E} {a b : ℝ} (ha : 0 < a)
    (hsupp : Function.support f ∩ Ioi 0 ⊆ Icc a b) (hf : LocallyIntegrableOn f (Ioi 0)) (s : ℂ) :
    MellinConvergent f s := by
  have hIcc : IntegrableOn f (Icc a b) :=
    hf.integrableOn_compact_subset (fun _ ht ↦ ha.trans_le ht.1) isCompact_Icc
  have hind : IntegrableOn ((Icc a b).indicator f) (Ioi 0) :=
    (hIcc.integrable_indicator measurableSet_Icc).integrableOn
  have h1 : MellinConvergent f 1 := by
    refine hind.congr_fun (fun t ht ↦ ?_) measurableSet_Ioi
    rw [sub_self, cpow_zero, one_smul]
    by_cases hmem : t ∈ Icc a b
    · exact indicator_of_mem hmem f
    · rw [indicator_of_notMem hmem, eq_comm]
      exact Function.notMem_support.mp fun h ↦ hmem (hsupp ⟨h, ht⟩)
  exact h1.of_support_subset_Icc ha hsupp s

/-- The Mellin transform of a locally integrable function on `(0, ∞)` with
`Function.support f ∩ Ioi 0 ⊆ Icc a b` (`0 < a`) is entire. -/
theorem differentiable_mellin_of_support_subset_Icc {f : ℝ → E} {a b : ℝ} (ha : 0 < a)
    (hsupp : Function.support f ∩ Ioi 0 ⊆ Icc a b) (hf : LocallyIntegrableOn f (Ioi 0)) :
    Differentiable ℂ (mellin f) := fun s ↦
  mellin_differentiableAt_of_isBigO_rpow hf
    ((eventually_eq_zero_atTop_of_support_inter_Ioi_subset hsupp).trans_isBigO (isBigO_zero _ _))
    (lt_add_one s.re)
    ((eventually_eq_zero_nhdsGT_of_support_inter_Ioi_subset ha hsupp).trans_isBigO
      (isBigO_zero _ _))
    (sub_one_lt s.re)

/-- Explicit uniform bound for `mellin f` on any vertical strip `σ₁ ≤ Re s ≤ σ₂` when `f` is
locally integrable on `(0, ∞)` and `Function.support f ∩ Ioi 0 ⊆ Icc a b` (`0 < a`). -/
theorem norm_mellin_le_of_support_subset_Icc {f : ℝ → E} {a b σ₁ σ₂ : ℝ} {s : ℂ}
    (ha : 0 < a) (hsupp : Function.support f ∩ Ioi 0 ⊆ Icc a b)
    (hf : LocallyIntegrableOn f (Ioi 0)) (hσ₁ : σ₁ ≤ s.re) (hσ₂ : s.re ≤ σ₂) :
    ‖mellin f s‖ ≤
      max (max (a ^ (σ₁ - 1)) (a ^ (σ₂ - 1))) (max (b ^ (σ₁ - 1)) (b ^ (σ₂ - 1))) *
        ∫ t in Icc a b, ‖f t‖ := by
  set M := max (max (a ^ (σ₁ - 1)) (a ^ (σ₂ - 1))) (max (b ^ (σ₁ - 1)) (b ^ (σ₂ - 1)))
  by_cases hab : a ≤ b
  · have hb : 0 < b := ha.trans_le hab
    have hpow_exp (x : ℝ) (hx : 0 < x) :
        x ^ (s.re - 1) ≤ max (x ^ (σ₁ - 1)) (x ^ (σ₂ - 1)) := by
      rcases le_or_gt 1 x with hx1 | hx1
      · exact (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)).trans (le_max_right _ _)
      · exact (Real.rpow_le_rpow_of_exponent_ge hx hx1.le (by linarith)).trans (le_max_left _ _)
    have hpow_le {t : ℝ} (ht : t ∈ Icc a b) : t ^ (s.re - 1) ≤ M := by
      have htb : t ^ (s.re - 1) ≤ max (a ^ (s.re - 1)) (b ^ (s.re - 1)) := by
        rcases le_or_gt 0 (s.re - 1) with hr | hr
        · exact (Real.rpow_le_rpow (ha.le.trans ht.1) ht.2 hr).trans (le_max_right _ _)
        · exact (Real.rpow_le_rpow_of_nonpos ha ht.1 hr.le).trans (le_max_left _ _)
      exact htb.trans (max_le_max (hpow_exp a ha) (hpow_exp b hb))
    have hint_f : IntegrableOn f (Icc a b) :=
      hf.integrableOn_compact_subset (fun _ ht ↦ ha.trans_le ht.1) isCompact_Icc
    have hint_mel : IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ (s - 1) • f t) (Icc a b) :=
      (mellinConvergent_of_support_subset_Icc ha hsupp hf s).mono_set
        fun _ ht ↦ ha.trans_le ht.1
    rw [mellin_eq_setIntegral_Icc_of_support_subset ha hsupp s, ← integral_const_mul]
    calc
      ‖∫ t in Icc a b, (t : ℂ) ^ (s - 1) • f t‖
        ≤ ∫ t in Icc a b, ‖(t : ℂ) ^ (s - 1) • f t‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t in Icc a b, M * ‖f t‖ := by
          refine setIntegral_mono_on hint_mel.norm (hint_f.norm.const_mul M) measurableSet_Icc
            fun t ht ↦ ?_
          rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos (ha.trans_le ht.1), sub_re, one_re]
          exact mul_le_mul_of_nonneg_right (hpow_le ht) (norm_nonneg _)
  · rw [mellin_eq_setIntegral_Icc_of_support_subset ha hsupp s, Icc_eq_empty hab]
    simp

private lemma mellin_ofReal_sub_one_integrableOn {ν : ℝ → ℝ} {a b ε : ℝ} (ha : 0 < a)
    (hνs : Function.support ν ∩ Ioi 0 ⊆ Icc a b) (hνm : ∫ x in Ioi (0 : ℝ), ν x / x = 1) :
    IntegrableOn (fun x ↦ (x ^ ε - 1) * (ν x / x)) (Ioi (0 : ℝ)) ∧
      mellin (fun x ↦ (ν x : ℂ)) (ε : ℂ) - 1 =
        ((∫ x in Ioi (0 : ℝ), (x ^ ε - 1) * (ν x / x) : ℝ) : ℂ) := by
  have hconv_0 : MellinConvergent (fun x ↦ (ν x : ℂ)) 0 :=
    (mellinConvergent_ofReal_zero_iff ν).mpr (integrable_of_integral_eq_one hνm)
  have hsuppc : Function.support (fun x ↦ (ν x : ℂ)) ∩ Ioi 0 ⊆ Icc a b := fun x hx ↦
    hνs ⟨fun h ↦ hx.1 (by simp [h]), hx.2⟩
  have hconv_ε : MellinConvergent (fun x ↦ (ν x : ℂ)) (ε : ℂ) :=
    hconv_0.of_support_subset_Icc ha hsuppc (ε : ℂ)
  have hpt : EqOn (fun x : ℝ ↦ (x : ℂ) ^ ((ε : ℂ) - 1) • (ν x : ℂ) -
      (x : ℂ) ^ ((0 : ℂ) - 1) • (ν x : ℂ))
      (fun x : ℝ ↦ ((((x ^ ε - 1) * (ν x / x) : ℝ) : ℂ))) (Ioi (0 : ℝ)) := fun x hx ↦ by
    have hxc : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hx)
    simp only [smul_eq_mul, zero_sub, cpow_neg_one]
    rw [cpow_sub _ _ hxc, cpow_one, ← ofReal_cpow hx.le]
    push_cast
    field_simp [hxc]
  refine ⟨Complex.reCLM.integrable_comp ((hconv_ε.sub hconv_0).congr_fun hpt measurableSet_Ioi),
    ?_⟩
  have h1 : (1 : ℂ) = mellin (fun x ↦ (ν x : ℂ)) 0 := by rw [mellin_ofReal_zero, hνm, ofReal_one]
  rw [h1, mellin, mellin, ← integral_sub hconv_ε hconv_0,
    setIntegral_congr_fun measurableSet_Ioi hpt, integral_complex_ofReal]

/-- Exact integral formula for `mellin ν ε - 1` when `ν : ℝ → ℝ` has
`Function.support ν ∩ Ioi 0 ⊆ Icc a b` (`0 < a`) and `∫₀^∞ ν(x) dx / x = 1`. -/
theorem mellin_ofReal_sub_one_eq {ν : ℝ → ℝ} {a b ε : ℝ} (ha : 0 < a)
    (hνs : Function.support ν ∩ Ioi 0 ⊆ Icc a b) (hνm : ∫ x in Ioi (0 : ℝ), ν x / x = 1) :
    mellin (fun x ↦ (ν x : ℂ)) (ε : ℂ) - 1 =
      ((∫ x in Ioi (0 : ℝ), (x ^ ε - 1) * (ν x / x) : ℝ) : ℂ) :=
  (mellin_ofReal_sub_one_integrableOn ha hνs hνm).2

/-- For `ν : ℝ → ℝ` nonnegative on `(0, ∞)` with `Function.support ν ∩ Ioi 0 ⊆ Icc a b` (`0 < a`),
`∫₀^∞ ν(x) dx / x = 1`, and `0 ≤ ε ≤ 1`,
`‖mellin ν ε - 1‖ ≤ max b 1 * max |log a| |log b| * ε`. -/
theorem norm_mellin_ofReal_sub_one_le {ν : ℝ → ℝ} {a b ε : ℝ} (ha : 0 < a)
    (hν0 : ∀ x > 0, 0 ≤ ν x) (hνs : Function.support ν ∩ Ioi 0 ⊆ Icc a b)
    (hνm : ∫ x in Ioi (0 : ℝ), ν x / x = 1) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    ‖mellin (fun x ↦ (ν x : ℂ)) (ε : ℂ) - 1‖ ≤
      max b 1 * max |Real.log a| |Real.log b| * ε := by
  have hint_div : IntegrableOn (fun x ↦ ν x / x) (Ioi (0 : ℝ)) := integrable_of_integral_eq_one hνm
  obtain ⟨hint_real, hsub⟩ := mellin_ofReal_sub_one_integrableOn (ε := ε) ha hνs hνm
  rw [hsub, Complex.norm_real, Real.norm_eq_abs]
  set L := max |Real.log a| |Real.log b|
  have hpow_bd {x : ℝ} (hx : x ∈ Icc a b) : |x ^ ε - 1| ≤ max b 1 * L * ε := by
    have hx0 : 0 < x := ha.trans_le hx.1
    have hlog_abs : |Real.log x| ≤ L := abs_le.mpr
      ⟨(neg_le_neg (le_max_left _ _)).trans ((neg_abs_le _).trans (Real.log_le_log ha hx.1)),
        (Real.log_le_log hx0 hx.2).trans ((le_abs_self _).trans (le_max_right _ _))⟩
    rw [Real.rpow_def_of_pos hx0, mul_comm (Real.log x) ε]
    set u := ε * Real.log x
    rcases le_or_gt 0 (Real.log x) with hlog_nn | hlog_neg
    · have hu_le : u ≤ ε * L := mul_le_mul_of_nonneg_left ((le_abs_self _).trans hlog_abs) hε0
      have hexp_le : Real.exp u ≤ max b 1 :=
        ((Real.exp_le_exp.mpr ((mul_le_of_le_one_left hlog_nn hε1).trans
          (Real.log_le_log hx0 hx.2))).trans_eq (Real.exp_log (hx0.trans_le hx.2))).trans
          (le_max_left b 1)
      have h1 : Real.exp u - 1 ≤ u * Real.exp u := by
        have hmul := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-u)) (Real.exp_pos u).le
        rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at hmul
        linarith
      rw [abs_of_nonneg (sub_nonneg.mpr (Real.one_le_exp (mul_nonneg hε0 hlog_nn)))]
      calc Real.exp u - 1 ≤ u * Real.exp u := h1
        _ ≤ (ε * L) * max b 1 := mul_le_mul hu_le hexp_le (Real.exp_pos u).le (by positivity)
        _ = max b 1 * L * ε := by ring
    · have hnegu : -u ≤ ε * L := by
        simpa [u, mul_neg] using mul_le_mul_of_nonneg_left ((neg_le_abs _).trans hlog_abs) hε0
      rw [abs_of_nonpos (sub_nonpos.mpr
        (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hε0 hlog_neg.le))), neg_sub]
      nlinarith [Real.add_one_le_exp u, le_max_right b 1,
        mul_nonneg hε0 (le_trans (abs_nonneg _) (le_max_left |Real.log a| |Real.log b|))]
  calc |∫ x in Ioi (0 : ℝ), (x ^ ε - 1) * (ν x / x)|
    _ ≤ ∫ x in Ioi (0 : ℝ), |(x ^ ε - 1) * (ν x / x)| := abs_integral_le_integral_abs
    _ ≤ ∫ x in Ioi (0 : ℝ), (max b 1 * L * ε) * (ν x / x) := by
        refine setIntegral_mono_on hint_real.abs (hint_div.const_mul _) measurableSet_Ioi
          fun x hx ↦ ?_
        rw [abs_mul, abs_of_nonneg (div_nonneg (hν0 x hx) hx.le)]
        by_cases hνx : ν x = 0
        · simp [hνx]
        · exact mul_le_mul_of_nonneg_right (hpow_bd (hνs ⟨hνx, hx⟩))
            (div_nonneg (hν0 x hx) hx.le)
    _ = max b 1 * L * ε := by rw [integral_const_mul, hνm, mul_one]

end Basic

section IntegrationByParts

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

private lemma support_iteratedDeriv_inter_Ioi_subset_Icc {f : ℝ → E} {a b : ℝ} (k : ℕ)
    (hsupp : Function.support f ∩ Ioi 0 ⊆ Icc a b) :
    Function.support (iteratedDeriv k f) ∩ Ioi 0 ⊆ Icc a b := fun t ⟨ht, ht0⟩ ↦ by
  have heq : EqOn f 0 (Ioi 0 \ Icc a b) := fun u hu ↦
    Function.notMem_support.mp fun h ↦ hu.2 (hsupp ⟨h, hu.1⟩)
  by_contra htab
  exact ht ((heq.iteratedDeriv_of_isOpen (isOpen_Ioi.sdiff isClosed_Icc) k ⟨ht0, htab⟩).trans
    iteratedDeriv_const_zero)

private lemma support_deriv_inter_Ioi_subset_Icc {f : ℝ → E} {a b : ℝ}
    (hsupp : Function.support f ∩ Ioi 0 ⊆ Icc a b) :
    Function.support (deriv f) ∩ Ioi 0 ⊆ Icc a b := by
  simpa only [iteratedDeriv_one] using support_iteratedDeriv_inter_Ioi_subset_Icc 1 hsupp

/-- Integration by parts for the Mellin transform of a function `f` differentiable on `(0, ∞)`
with `deriv f` locally integrable on `(0, ∞)` and `Function.support f ∩ Ioi 0 ⊆ Icc a b` (`0 < a`):
`s • mellin f s = -mellin (deriv f) (s + 1)` for every `s : ℂ`. -/
theorem smul_mellin_eq_neg_mellin_deriv {f : ℝ → E} {a b : ℝ} (ha : 0 < a)
    (hsupp : Function.support f ∩ Ioi 0 ⊆ Icc a b) (hf : DifferentiableOn ℝ f (Ioi 0))
    (hf' : LocallyIntegrableOn (deriv f) (Ioi 0)) (s : ℂ) :
    s • mellin f s = -mellin (deriv f) (s + 1) := by
  by_cases hE : CompleteSpace E
  · set a' := a / 2
    set b' := max a b + 1
    have ha' : 0 < a' := half_pos ha
    have ha'a : a' < a := half_lt_self ha
    have hbb' : b < b' := (le_max_right a b).trans_lt (lt_add_one _)
    have ha'b' : a' ≤ b' := by linarith [le_max_left a b]
    have hsub : Icc a b ⊆ Icc a' b' := fun t ht ↦ ⟨ha'a.le.trans ht.1, ht.2.trans hbb'.le⟩
    have hsupp' : Function.support (deriv f) ∩ Ioi 0 ⊆ Icc a b :=
      support_deriv_inter_Ioi_subset_Icc hsupp
    have hfa' : f a' = 0 := Function.notMem_support.mp fun h ↦ ha'a.not_ge (hsupp ⟨h, ha'⟩).1
    have hfb' : f b' = 0 := Function.notMem_support.mp fun h ↦
      hbb'.not_ge (hsupp ⟨h, ha.trans_le (by linarith [le_max_left a b])⟩).2
    have hmem_Ioi : ∀ t ∈ uIcc a' b', t ∈ Ioi (0 : ℝ) := by
      rw [uIcc_of_le ha'b']
      exact fun t ht ↦ ha'.trans_le ht.1
    have hu : ∀ t ∈ uIcc a' b', HasDerivAt (fun x : ℝ ↦ (x : ℂ) ^ s)
        (s * (t : ℂ) ^ (s - 1)) t := fun t ht ↦ by
      rcases eq_or_ne s 0 with rfl | hs
      · simpa only [cpow_zero, zero_mul] using hasDerivAt_const t (1 : ℂ)
      · exact hasDerivAt_ofReal_cpow_const (hmem_Ioi t ht).ne' hs
    have hv : ∀ t ∈ uIcc a' b', HasDerivAt f (deriv f t) t := fun t ht ↦
      ((hf t (hmem_Ioi t ht)).differentiableAt (Ioi_mem_nhds (hmem_Ioi t ht))).hasDerivAt
    have hu' : IntervalIntegrable (fun t : ℝ ↦ s * (t : ℂ) ^ (s - 1)) volume a' b' :=
      (continuousOn_const.mul (continuousOn_of_forall_continuousAt fun t ht ↦
        continuousAt_ofReal_cpow_const _ _ (Or.inr (hmem_Ioi t ht).ne'))).intervalIntegrable
    have hv' : IntervalIntegrable (deriv f) volume a' b' := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le ha'b']
      exact hf'.integrableOn_compact_subset (fun t ht ↦ ha'.trans_le ht.1) isCompact_Icc
    have hibp := intervalIntegral.integral_smul_deriv_eq_deriv_smul hu hv hu' hv'
    rw [hfa', hfb', smul_zero, smul_zero, sub_self, zero_sub] at hibp
    have hm_deriv : mellin (deriv f) (s + 1) = ∫ t in a'..b', (t : ℂ) ^ s • deriv f t := by
      rw [mellin_eq_intervalIntegral_of_support_subset_Icc ha' ha'b' (hsupp'.trans hsub) (s + 1)]
      simp only [add_sub_cancel_right]
    have hm_f : s • mellin f s = ∫ t in a'..b', (s * (t : ℂ) ^ (s - 1)) • f t := by
      rw [mellin_eq_intervalIntegral_of_support_subset_Icc ha' ha'b' (hsupp.trans hsub) s,
        ← intervalIntegral.integral_smul]
      simp_rw [mul_smul]
    rw [hm_deriv, hibp, neg_neg, hm_f]
  · simp [mellin, integral_of_not_completeSpace hE]

/-- Iterated integration by parts for the Mellin transform of a `C^k` function on `(0, ∞)` with
`Function.support f ∩ Ioi 0 ⊆ Icc a b` (`0 < a`). -/
theorem prod_smul_mellin_eq_neg_one_pow_smul_mellin_iteratedDeriv {f : ℝ → E} {a b : ℝ} {k : ℕ}
    (ha : 0 < a) (hsupp : Function.support f ∩ Ioi 0 ⊆ Icc a b) (hf : ContDiffOn ℝ k f (Ioi 0))
    (s : ℂ) :
    (∏ j ∈ Finset.range k, (s + (j : ℂ))) • mellin f s =
      (-1 : ℂ) ^ k • mellin (iteratedDeriv k f) (s + (k : ℂ)) := by
  induction k generalizing f s with
  | zero => simp
  | succ k ih =>
    have hdiff : DifferentiableOn ℝ f (Ioi 0) := hf.differentiableOn (by simp)
    have hderiv_cd : ContDiffOn ℝ k (deriv f) (Ioi 0) :=
      hf.deriv_of_isOpen isOpen_Ioi (by norm_cast)
    have hderiv_loc : LocallyIntegrableOn (deriv f) (Ioi 0) :=
      hderiv_cd.continuousOn.locallyIntegrableOn measurableSet_Ioi
    have hderiv_supp : Function.support (deriv f) ∩ Ioi 0 ⊆ Icc a b :=
      support_deriv_inter_Ioi_subset_Icc hsupp
    have hprod : ∏ j ∈ Finset.range (k + 1), (s + (j : ℂ)) =
        (∏ j ∈ Finset.range k, ((s + 1) + (j : ℂ))) * s := by
      rw [Finset.prod_range_succ']
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero]
      congr 1
      refine Finset.prod_congr rfl fun j _ ↦ ?_
      ring
    rw [hprod, mul_smul, smul_mellin_eq_neg_mellin_deriv ha hsupp hdiff hderiv_loc s, smul_neg,
      ih hderiv_supp hderiv_cd (s + 1), iteratedDeriv_succ', ← neg_smul, pow_succ', neg_one_mul]
    congr 2
    push_cast
    ring

private lemma pow_one_add_norm_le_mul_prod {s : ℂ} {k : ℕ} (hs : 2 * (k : ℝ) < ‖s‖) :
    (1 + ‖s‖) ^ k ≤ (4 : ℝ) ^ k * ∏ j ∈ Finset.range k, ‖s + (j : ℂ)‖ := by
  calc (1 + ‖s‖) ^ k = ∏ _j ∈ Finset.range k, (1 + ‖s‖) := by
        rw [Finset.prod_const, Finset.card_range]
    _ ≤ ∏ j ∈ Finset.range k, (4 * ‖s + (j : ℂ)‖) := by
        gcongr with j hj
        have hjk : (j : ℝ) < (k : ℝ) := Nat.cast_lt.mpr (Finset.mem_range.mp hj)
        have hk1 : (1 : ℝ) ≤ (k : ℝ) :=
          Nat.one_le_cast.mpr (Nat.pos_of_ne_zero fun h ↦ by simp [h] at hj)
        have htri : ‖s‖ ≤ ‖s + (j : ℂ)‖ + (j : ℝ) := by
          simpa [Complex.norm_natCast] using norm_add_le (s + (j : ℂ)) (-(j : ℂ))
        linarith
    _ = (4 : ℝ) ^ k * ∏ j ∈ Finset.range k, ‖s + (j : ℂ)‖ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]

/-- Vertical-strip decay of the Mellin transform of a `C^k` function on `(0, ∞)` with
`Function.support f ∩ Ioi 0 ⊆ Icc a b` (`0 < a`): on every strip `σ₁ ≤ Re s ≤ σ₂`,
`‖mellin f s‖ ≤ C / (1 + ‖s‖) ^ k`. -/
theorem exists_norm_mellin_le_of_contDiffOn_of_support_subset_Icc {f : ℝ → E} {a b σ₁ σ₂ : ℝ}
    {k : ℕ} (ha : 0 < a) (hsupp : Function.support f ∩ Ioi 0 ⊆ Icc a b)
    (hf : ContDiffOn ℝ k f (Ioi 0)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ →
      ‖mellin f s‖ ≤ C / (1 + ‖s‖) ^ k := by
  have hf_loc : LocallyIntegrableOn f (Ioi 0) :=
    hf.continuousOn.locallyIntegrableOn measurableSet_Ioi
  have hfk_supp : Function.support (iteratedDeriv k f) ∩ Ioi 0 ⊆ Icc a b :=
    support_iteratedDeriv_inter_Ioi_subset_Icc k hsupp
  have hfk_loc : LocallyIntegrableOn (iteratedDeriv k f) (Ioi 0) :=
    ((hf.continuousOn_iteratedDerivWithin le_rfl isOpen_Ioi.uniqueDiffOn).congr
      fun _ ht ↦ (iteratedDerivWithin_of_isOpen isOpen_Ioi ht).symm).locallyIntegrableOn
        measurableSet_Ioi
  set M₀ := max (max (a ^ (σ₁ - 1)) (a ^ (σ₂ - 1))) (max (b ^ (σ₁ - 1)) (b ^ (σ₂ - 1))) *
    ∫ t in Icc a b, ‖f t‖
  set Mₖ := max (max (a ^ (σ₁ + k - 1)) (a ^ (σ₂ + k - 1)))
    (max (b ^ (σ₁ + k - 1)) (b ^ (σ₂ + k - 1))) * ∫ t in Icc a b, ‖iteratedDeriv k f t‖
  have hM₀_nonneg : 0 ≤ M₀ :=
    mul_nonneg ((Real.rpow_pos_of_pos ha _).le.trans ((le_max_left _ _).trans (le_max_left _ _)))
      (setIntegral_nonneg measurableSet_Icc fun _ _ ↦ norm_nonneg _)
  refine ⟨max ((1 + 2 * (k : ℝ)) ^ k * M₀) ((4 : ℝ) ^ k * Mₖ),
    le_max_of_le_left (by positivity), fun s hσ₁ hσ₂ ↦ ?_⟩
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < (1 + ‖s‖) ^ k)]
  rcases le_or_gt ‖s‖ (2 * (k : ℝ)) with hs | hs
  · have h0 : ‖mellin f s‖ ≤ M₀ :=
      norm_mellin_le_of_support_subset_Icc ha hsupp hf_loc hσ₁ hσ₂
    have hpow : (1 + ‖s‖) ^ k ≤ (1 + 2 * (k : ℝ)) ^ k := by gcongr
    exact (mul_le_mul h0 hpow (by positivity) hM₀_nonneg).trans
      (mul_comm M₀ _ ▸ le_max_left _ _)
  · have hk_bd : ‖mellin (iteratedDeriv k f) (s + (k : ℂ))‖ ≤ Mₖ :=
      norm_mellin_le_of_support_subset_Icc ha hfk_supp hfk_loc (by simp [hσ₁]) (by simp [hσ₂])
    have hibp := congrArg norm
      (prod_smul_mellin_eq_neg_one_pow_smul_mellin_iteratedDeriv ha hsupp hf s)
    simp only [norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      Complex.norm_prod] at hibp
    calc ‖mellin f s‖ * (1 + ‖s‖) ^ k
      _ ≤ ‖mellin f s‖ * ((4 : ℝ) ^ k * ∏ j ∈ Finset.range k, ‖s + (j : ℂ)‖) := by
          gcongr
          exact pow_one_add_norm_le_mul_prod hs
      _ = (4 : ℝ) ^ k * ((∏ j ∈ Finset.range k, ‖s + (j : ℂ)‖) * ‖mellin f s‖) := by ring
      _ = (4 : ℝ) ^ k * ‖mellin (iteratedDeriv k f) (s + (k : ℂ))‖ := by rw [hibp]
      _ ≤ (4 : ℝ) ^ k * Mₖ := by gcongr
      _ ≤ _ := le_max_right _ _

end IntegrationByParts

end TauCeti
