/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Mellin transforms of compactly supported functions

If `f : ℝ → E` is locally integrable on `(0, ∞)` and supported inside a compact interval
`[a, b] ⊂ (0, ∞)`, then its Mellin transform `mellin f` converges absolutely on all of `ℂ`, is
entire, and is uniformly bounded on every vertical strip `σ₁ ≤ Re s ≤ σ₂`.

When `f` is `C^k` on `(0, ∞)` with support in `[a, b]`, repeated integration by parts with
vanishing boundary terms yields
`(∏ j ∈ Finset.range k, (s + j)) • mellin f s = (-1) ^ k • mellin (iteratedDeriv k f) (s + k)`
for every `s : ℂ`, giving vertical-strip decay `‖mellin f s‖ ≤ C / (1 + ‖s‖) ^ k` on every strip
`σ₁ ≤ Re s ≤ σ₂`.

## Main results

* `TauCeti.mellin_zero`, `TauCeti.mellin_ofReal_zero`, `TauCeti.mellinConvergent_ofReal_zero_iff`:
  the Mellin transform and convergence at `s = 0` in terms of `dt / t`.
* `TauCeti.mellinConvergent_of_support_subset_Icc`,
  `MellinConvergent.of_support_subset_Icc`,
  `TauCeti.differentiable_mellin_of_support_subset_Icc`: entireness and all-`s` Mellin convergence
  of a function supported in `[a, b] ⊂ (0, ∞)`.
* `TauCeti.norm_mellin_le_of_support_subset_Icc`: explicit uniform bound on vertical strips.
* `TauCeti.smul_mellin_eq_neg_mellin_deriv`,
  `TauCeti.prod_smul_mellin_eq_mellin_iteratedDeriv`: single and iterated integration by parts.
* `TauCeti.exists_norm_mellin_le_of_contDiffOn_of_support_subset_Icc`: vertical-strip decay
  `O((1 + ‖s‖)⁻ᵏ)` for `C^k` functions supported in `[a, b] ⊂ (0, ∞)`.

## References

* A. Kontorovich, T. Tao and contributors, *Prime Number Theorem And …*, §4.3 (Mellin transforms
  of compactly supported bumps).
-/

public section

open MeasureTheory Complex Set Filter Asymptotics
open scoped Topology

/-- If `f` is supported in `[a, b] ⊂ (0, ∞)` and Mellin convergent at some `s₀`, then `f` is
Mellin convergent at every `s : ℂ`. -/
theorem MellinConvergent.of_support_subset_Icc {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f : ℝ → E} {a b : ℝ} {s₀ : ℂ} (hf : MellinConvergent f s₀) (ha : 0 < a)
    (hsupp : Function.support f ⊆ Icc a b) (s : ℂ) :
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
    · have htab : t ∈ Icc a b := hsupp hft
      have hpow : t ^ (s.re - s₀.re) ≤ M := by
        rcases le_or_gt 0 (s.re - s₀.re) with hr | hr
        · exact (Real.rpow_le_rpow (ha.le.trans htab.1) htab.2 hr).trans (le_max_right _ _)
        · exact (Real.rpow_le_rpow_of_nonpos ha htab.1 hr.le).trans (le_max_left _ _)
      exact mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
  · have hzero : EqOn (fun t : ℝ ↦ (t : ℂ) ^ (s - 1) • f t) 0 (Ioi 0) := fun t _ ↦ by
      have hft : f t = 0 := Function.notMem_support.mp fun h ↦ by
        rw [Icc_eq_empty hab] at hsupp
        exact hsupp h
      simp [hft]
    exact (integrableOn_zero (s := Ioi (0 : ℝ))).congr_fun (fun t ht ↦ (hzero ht).symm)
      measurableSet_Ioi

namespace TauCeti

section Basic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The Mellin transform at `0` is the integral against `dt / t`. -/
theorem mellin_zero (f : ℝ → E) :
    mellin f 0 = ∫ t in Ioi (0 : ℝ), (t : ℂ)⁻¹ • f t := by
  simp only [mellin, zero_sub, cpow_neg_one]

/-- The Mellin transform at `0` of a real-valued function is its `dt / t`-integral. -/
theorem mellin_ofReal_zero (f : ℝ → ℝ) :
    mellin (fun t ↦ (f t : ℂ)) 0 = ((∫ t in Ioi (0 : ℝ), f t / t : ℝ) : ℂ) := by
  rw [mellin_zero, ← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
  simp [div_eq_inv_mul]

/-- Mellin convergence at `0` of a real-valued function is equivalent to integrability of
`f t / t` on `(0, ∞)`. -/
theorem mellinConvergent_ofReal_zero_iff (f : ℝ → ℝ) :
    MellinConvergent (fun t ↦ (f t : ℂ)) 0 ↔ IntegrableOn (fun t ↦ f t / t) (Ioi (0 : ℝ)) := by
  have hEq : (fun t : ℝ ↦ (t : ℂ) ^ ((0 : ℂ) - 1) • (f t : ℂ)) =
      fun t : ℝ ↦ ((f t / t : ℝ) : ℂ) := by
    ext t
    simp [cpow_neg_one, div_eq_inv_mul]
  rw [MellinConvergent, hEq, IntegrableOn, IntegrableOn]
  exact ⟨fun h ↦ Complex.reCLM.integrable_comp h, fun h ↦ Complex.ofRealCLM.integrable_comp h⟩

/-- If `f` is supported in `[a, b]` with `0 < a`, its Mellin transform equals the set integral
over `[a, b]`. -/
theorem mellin_eq_setIntegral_Icc_of_support_subset {f : ℝ → E} {a b : ℝ} (ha : 0 < a)
    (hsupp : Function.support f ⊆ Icc a b) (s : ℂ) :
    mellin f s = ∫ t in Icc a b, (t : ℂ) ^ (s - 1) • f t := by
  have hzero : ∀ t, t ∉ Icc a b → (t : ℂ) ^ (s - 1) • f t = 0 := fun t ht ↦ by
    have hft : f t = 0 := Function.notMem_support.mp fun h ↦ ht (hsupp h)
    simp [hft]
  rw [mellin, setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht ↦
      hzero t fun h ↦ ht (ha.trans_le h.1),
    setIntegral_eq_integral_of_forall_compl_eq_zero hzero]

/-- If `f` is supported in `[a, b]` with `0 < a ≤ b`, its Mellin transform equals the interval
integral over `a..b`. -/
theorem mellin_eq_intervalIntegral_of_support_subset_Icc {f : ℝ → E} {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hsupp : Function.support f ⊆ Icc a b) (s : ℂ) :
    mellin f s = ∫ t in a..b, (t : ℂ) ^ (s - 1) • f t := by
  rw [mellin_eq_setIntegral_Icc_of_support_subset ha hsupp s,
    MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]

/-- A locally integrable function on `(0, ∞)` supported in `[a, b] ⊂ (0, ∞)` is Mellin convergent
at every `s : ℂ`. -/
theorem mellinConvergent_of_support_subset_Icc {f : ℝ → E} {a b : ℝ} (ha : 0 < a)
    (hsupp : Function.support f ⊆ Icc a b) (hf : LocallyIntegrableOn f (Ioi 0)) (s : ℂ) :
    MellinConvergent f s := by
  have htop : f =O[atTop] fun t : ℝ ↦ t ^ (-(s.re + 1)) := by
    refine (isBigO_zero _ atTop).congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_gt_atTop b] with t ht
    exact (Function.notMem_support.mp fun h ↦ ht.not_ge (hsupp h).2).symm
  have hbot : f =O[𝓝[>] 0] fun t : ℝ ↦ t ^ (-(s.re - 1)) := by
    refine (isBigO_zero _ (𝓝[>] 0)).congr' ?_ EventuallyEq.rfl
    filter_upwards [Ioo_mem_nhdsGT ha] with t ht
    exact (Function.notMem_support.mp fun h ↦ ht.2.not_ge (hsupp h).1).symm
  exact mellinConvergent_of_isBigO_rpow hf htop (lt_add_one s.re) hbot (sub_one_lt s.re)

/-- The Mellin transform of a locally integrable function on `(0, ∞)` supported in `[a, b] ⊂ (0, ∞)`
is entire. -/
theorem differentiable_mellin_of_support_subset_Icc {f : ℝ → E} {a b : ℝ} (ha : 0 < a)
    (hsupp : Function.support f ⊆ Icc a b) (hf : LocallyIntegrableOn f (Ioi 0)) :
    Differentiable ℂ (mellin f) := fun s ↦ by
  have htop : f =O[atTop] fun t : ℝ ↦ t ^ (-(s.re + 1)) := by
    refine (isBigO_zero _ atTop).congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_gt_atTop b] with t ht
    exact (Function.notMem_support.mp fun h ↦ ht.not_ge (hsupp h).2).symm
  have hbot : f =O[𝓝[>] 0] fun t : ℝ ↦ t ^ (-(s.re - 1)) := by
    refine (isBigO_zero _ (𝓝[>] 0)).congr' ?_ EventuallyEq.rfl
    filter_upwards [Ioo_mem_nhdsGT ha] with t ht
    exact (Function.notMem_support.mp fun h ↦ ht.2.not_ge (hsupp h).1).symm
  exact mellin_differentiableAt_of_isBigO_rpow hf htop (lt_add_one s.re) hbot (sub_one_lt s.re)

/-- Explicit uniform bound for `mellin f` on any vertical strip `σ₁ ≤ Re s ≤ σ₂` when `f` is
locally integrable on `(0, ∞)` and supported in `[a, b] ⊂ (0, ∞)`. -/
theorem norm_mellin_le_of_support_subset_Icc {f : ℝ → E} {a b σ₁ σ₂ : ℝ} {s : ℂ}
    (ha : 0 < a) (hsupp : Function.support f ⊆ Icc a b) (hf : LocallyIntegrableOn f (Ioi 0))
    (hσ₁ : σ₁ ≤ s.re) (hσ₂ : s.re ≤ σ₂) :
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

end Basic

section IntegrationByParts

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Integration by parts for the Mellin transform of a function supported in `[a, b] ⊂ (0, ∞)`:
`s • mellin f s = -mellin (deriv f) (s + 1)` for every `s : ℂ`. -/
theorem smul_mellin_eq_neg_mellin_deriv {f : ℝ → E} {a b : ℝ} (ha : 0 < a)
    (hsupp : Function.support f ⊆ Icc a b) (hf : DifferentiableOn ℝ f (Ioi 0))
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
    have hsupp' : Function.support (deriv f) ⊆ Icc a b :=
      support_deriv_subset.trans (closure_minimal hsupp isClosed_Icc)
    have hfa' : f a' = 0 := Function.notMem_support.mp fun h ↦ ha'a.not_ge (hsupp h).1
    have hfb' : f b' = 0 := Function.notMem_support.mp fun h ↦ hbb'.not_ge (hsupp h).2
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

/-- Iterated integration by parts for the Mellin transform of a `C^k` function on `(0, ∞)`
supported in `[a, b] ⊂ (0, ∞)`. -/
theorem prod_smul_mellin_eq_mellin_iteratedDeriv {f : ℝ → E} {a b : ℝ} {k : ℕ}
    (ha : 0 < a) (hsupp : Function.support f ⊆ Icc a b) (hf : ContDiffOn ℝ k f (Ioi 0)) (s : ℂ) :
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
    have hderiv_supp : Function.support (deriv f) ⊆ Icc a b :=
      support_deriv_subset.trans (closure_minimal hsupp isClosed_Icc)
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

/-- Vertical-strip decay of the Mellin transform of a `C^k` function on `(0, ∞)` supported in
`[a, b] ⊂ (0, ∞)`: on every strip `σ₁ ≤ Re s ≤ σ₂`, `‖mellin f s‖ ≤ C / (1 + ‖s‖) ^ k`. -/
theorem exists_norm_mellin_le_of_contDiffOn_of_support_subset_Icc {f : ℝ → E} {a b σ₁ σ₂ : ℝ}
    {k : ℕ} (ha : 0 < a) (hsupp : Function.support f ⊆ Icc a b)
    (hf : ContDiffOn ℝ k f (Ioi 0)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ →
      ‖mellin f s‖ ≤ C / (1 + ‖s‖) ^ k := by
  have hf_loc : LocallyIntegrableOn f (Ioi 0) :=
    hf.continuousOn.locallyIntegrableOn measurableSet_Ioi
  have hfk_supp : Function.support (iteratedDeriv k f) ⊆ Icc a b := fun t ht ↦ by
    have heq : EqOn f 0 (Icc a b)ᶜ := fun u hu ↦ Function.notMem_support.mp fun h ↦ hu (hsupp h)
    by_contra htab
    exact ht ((heq.iteratedDeriv_of_isOpen isClosed_Icc.isOpen_compl k htab).trans
      iteratedDeriv_const_zero)
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
    have hibp := congrArg norm (prod_smul_mellin_eq_mellin_iteratedDeriv ha hsupp hf s)
    simp only [norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      Complex.norm_prod] at hibp
    have hprod_ge : (1 + ‖s‖) ^ k ≤ (4 : ℝ) ^ k * ∏ j ∈ Finset.range k, ‖s + (j : ℂ)‖ := by
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
    calc ‖mellin f s‖ * (1 + ‖s‖) ^ k
      _ ≤ ‖mellin f s‖ * ((4 : ℝ) ^ k * ∏ j ∈ Finset.range k, ‖s + (j : ℂ)‖) := by gcongr
      _ = (4 : ℝ) ^ k * ((∏ j ∈ Finset.range k, ‖s + (j : ℂ)‖) * ‖mellin f s‖) := by ring
      _ = (4 : ℝ) ^ k * ‖mellin (iteratedDeriv k f) (s + (k : ℂ))‖ := by rw [hibp]
      _ ≤ (4 : ℝ) ^ k * Mₖ := by gcongr
      _ ≤ _ := le_max_right _ _

end IntegrationByParts

end TauCeti
