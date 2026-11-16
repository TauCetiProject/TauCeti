/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Mellin transforms of compactly supported functions

For a function `f : ℝ → E` supported in a compact interval `[a, b]` with `0 < a`, the Mellin
transform `mellin f` is entire and coincides with the compact interval integral
`∫ t in a..b, (t : ℂ) ^ (s - 1) • f t`. When `f` is `C^k`, repeated integration by parts with no
boundary terms yields the functional identity
`(∏ j ∈ Finset.range k, (s + j)) • mellin f s = (-1) ^ k • mellin (iteratedDeriv k f) (s + k)`,
from which one deduces uniform rapid decay `‖mellin f s‖ ≤ C / (1 + ‖s‖) ^ k` on every vertical
strip `σ₁ ≤ Re s ≤ σ₂`.

## Main results

* `TauCeti.mellin_zero`: `mellin f 0 = ∫ t in Ioi 0, (t : ℂ)⁻¹ • f t`.
* `TauCeti.mellin_eq_intervalIntegral_of_support_subset`: restriction of `mellin f s` to `[a, b]`.
* `TauCeti.mellinConvergent_of_integrableOn_support_subset` and
  `TauCeti.differentiable_mellin_of_integrableOn_support_subset`: absolute convergence everywhere
  and entirety of `mellin f` for integrable functions supported in `[a, b]` (`0 < a`).
* `TauCeti.smul_mellin_eq_neg_mellin_deriv` and
  `TauCeti.prod_add_smul_mellin_eq_mellin_iteratedDeriv`: one-step and `k`-fold integration by
  parts for `mellin f`.
* `TauCeti.exists_norm_mellin_le_div_one_add_norm_pow`: uniform vertical-strip decay
  `‖mellin f s‖ ≤ C / (1 + ‖s‖) ^ k` for `C^k` functions supported in `[a, b]` (`0 < a`).

## References

* Alex Kontorovich, Terence Tao, et al., *Prime Number Theorem And …*, §4.3 (Mellin transforms of
  compactly supported bumps).
-/

public section

open MeasureTheory Complex Set Filter
open scoped Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Evaluating the Mellin transform at `s = 0` integrates `t⁻¹ • f t` over `(0, ∞)`. -/
theorem mellin_zero (f : ℝ → E) :
    mellin f 0 = ∫ t in Ioi (0 : ℝ), (t : ℂ)⁻¹ • f t := by
  simp only [mellin, zero_sub, Complex.cpow_neg_one]

/-- If `f` is supported in `[a, b]` with `0 ≤ a`, its Mellin transform equals the compact interval
integral over `[a, b]`. -/
theorem mellin_eq_intervalIntegral_of_support_subset {f : ℝ → E} {a b : ℝ} (ha : 0 ≤ a)
    (hf : Function.support f ⊆ Icc a b) (s : ℂ) :
    mellin f s = ∫ t in a..b, (t : ℂ) ^ (s - 1) • f t := by
  rcases le_or_gt a b with hab | hba
  · have hind : EqOn (fun t : ℝ ↦ (t : ℂ) ^ (s - 1) • f t)
        ((Icc a b).indicator fun t : ℝ ↦ (t : ℂ) ^ (s - 1) • f t) (Ioi 0) := by
      intro t _
      by_cases ht : t ∈ Icc a b
      · simp [ht]
      · simp [ht, Function.notMem_support.mp fun h ↦ ht (hf h)]
    rw [mellin, setIntegral_congr_fun measurableSet_Ioi hind,
      setIntegral_indicator measurableSet_Icc, intervalIntegral.integral_of_le hab]
    rcases ha.eq_or_lt with rfl | ha'
    · have hinter : Ioi (0 : ℝ) ∩ Icc 0 b = Ioc 0 b := by
        ext t
        simp only [mem_inter_iff, mem_Ioi, mem_Icc, mem_Ioc]
        constructor <;> intro h <;> grind
      rw [hinter]
    · have hinter : Ioi (0 : ℝ) ∩ Icc a b = Icc a b :=
        inter_eq_right.mpr (fun t ht ↦ ha'.trans_le ht.1)
      rw [hinter, integral_Icc_eq_integral_Ioc]
  · rw [Icc_eq_empty_of_lt hba, subset_empty_iff, Function.support_eq_empty_iff] at hf
    simp [hf, mellin]

omit [NormedSpace ℂ E] in
/-- A function integrable on `[a, b]` and supported in `[a, b]` is globally integrable on `ℝ`,
hence locally integrable on `(0, ∞)`. -/
private lemma locallyIntegrableOn_Ioi_of_integrableOn_support_subset {f : ℝ → E} {a b : ℝ}
    (hint : IntegrableOn f (Icc a b)) (hf : Function.support f ⊆ Icc a b) :
    LocallyIntegrableOn f (Ioi 0) := by
  have hind : (Icc a b).indicator f = f := Set.indicator_eq_self.mpr hf
  have hfi : Integrable f := by
    rw [← hind]
    exact (integrable_indicator_iff measurableSet_Icc).mpr hint
  exact hfi.locallyIntegrable.locallyIntegrableOn (Ioi 0)

omit [NormedSpace ℂ E] in
/-- A function supported in `[a, b]` with `0 < a` vanishes near `0⁺` and `+∞`, so it is
`O(t ^ r)` at both ends for every exponent `r`. -/
private lemma isBigO_rpow_of_support_subset {f : ℝ → E} {a b : ℝ} (ha : 0 < a)
    (hf : Function.support f ⊆ Icc a b) (r : ℝ) :
    (f =O[atTop] fun t : ℝ ↦ t ^ r) ∧ (f =O[𝓝[>] 0] fun t : ℝ ↦ t ^ r) := by
  refine ⟨?_, ?_⟩
  · refine Asymptotics.IsBigO.of_bound 0 ?_
    filter_upwards [eventually_gt_atTop b] with t ht
    have hnot : t ∉ Icc a b := fun h ↦ not_lt_of_ge h.2 ht
    simp [Function.notMem_support.mp fun h ↦ hnot (hf h)]
  · refine Asymptotics.IsBigO.of_bound 0 ?_
    filter_upwards [Ioo_mem_nhdsGT ha] with t ht
    have hnot : t ∉ Icc a b := fun h ↦ not_lt_of_ge h.1 ht.2
    simp [Function.notMem_support.mp fun h ↦ hnot (hf h)]

/-- If `f` is integrable on `[a, b]` and supported in `[a, b]` with `0 < a`, its Mellin transform
converges absolutely at every `s : ℂ`. -/
theorem mellinConvergent_of_integrableOn_support_subset {f : ℝ → E} {a b : ℝ} (ha : 0 < a)
    (hint : IntegrableOn f (Icc a b)) (hf : Function.support f ⊆ Icc a b) (s : ℂ) :
    MellinConvergent f s := by
  have hloc := locallyIntegrableOn_Ioi_of_integrableOn_support_subset hint hf
  have htop := (isBigO_rpow_of_support_subset ha hf (-(s.re + 1))).1
  have hbot := (isBigO_rpow_of_support_subset ha hf (-(s.re - 1))).2
  exact mellinConvergent_of_isBigO_rpow (a := s.re + 1) (b := s.re - 1) hloc htop (by linarith)
    hbot (by linarith)

/-- If `f` is integrable on `[a, b]` and supported in `[a, b]` with `0 < a`, its Mellin transform
is an entire function of `s : ℂ`. -/
theorem differentiable_mellin_of_integrableOn_support_subset {f : ℝ → E} {a b : ℝ} (ha : 0 < a)
    (hint : IntegrableOn f (Icc a b)) (hf : Function.support f ⊆ Icc a b) :
    Differentiable ℂ (mellin f) := by
  intro s
  have hloc := locallyIntegrableOn_Ioi_of_integrableOn_support_subset hint hf
  have htop := (isBigO_rpow_of_support_subset ha hf (-(s.re + 1))).1
  have hbot := (isBigO_rpow_of_support_subset ha hf (-(s.re - 1))).2
  exact mellin_differentiableAt_of_isBigO_rpow (a := s.re + 1) (b := s.re - 1) hloc htop
    (by linarith) hbot (by linarith)

/-- Uniform bound for `‖mellin f s‖` on any vertical strip `σ₁ ≤ Re s ≤ σ₂` when `f` is
integrable on `[a, b]` and supported in `[a, b]` with `0 < a`. -/
theorem exists_norm_mellin_le_of_integrableOn_support_subset {f : ℝ → E} {a b : ℝ} (ha : 0 < a)
    (hint : IntegrableOn f (Icc a b)) (hf : Function.support f ⊆ Icc a b) (σ₁ σ₂ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → ‖mellin f s‖ ≤ C := by
  let M : ℝ := max (max (a ^ (σ₁ - 1)) (a ^ (σ₂ - 1))) (max (b ^ (σ₁ - 1)) (b ^ (σ₂ - 1)))
  have hM0 : 0 ≤ M := le_trans (le_trans (Real.rpow_nonneg ha.le _) (le_max_left _ _))
    (le_max_left _ _)
  refine ⟨M * ∫ t in Icc a b, ‖f t‖, mul_nonneg hM0 (integral_nonneg fun _ ↦ norm_nonneg _), ?_⟩
  intro s hσ₁ hσ₂
  rcases le_or_gt a b with hab | hba
  · rw [mellin_eq_intervalIntegral_of_support_subset ha.le hf s,
      intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
    have hpow (x : ℝ) (hx : 0 < x) {r : ℝ} (hr1 : σ₁ - 1 ≤ r) (hr2 : r ≤ σ₂ - 1) :
        x ^ r ≤ max (x ^ (σ₁ - 1)) (x ^ (σ₂ - 1)) := by
      rcases le_or_gt 1 x with hx1 | hx1
      · exact (Real.rpow_le_rpow_of_exponent_le hx1 hr2).trans (le_max_right _ _)
      · exact (Real.rpow_le_rpow_of_exponent_ge hx hx1.le hr1).trans (le_max_left _ _)
    have hbound : ∀ t ∈ Icc a b, ‖(t : ℂ) ^ (s - 1) • f t‖ ≤ M * ‖f t‖ := by
      intro t ht
      have ht0 : 0 < t := ha.trans_le ht.1
      have hb0 : 0 < b := ht0.trans_le ht.2
      rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.sub_re, Complex.one_re]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      have htb : t ^ (s.re - 1) ≤ max (a ^ (s.re - 1)) (b ^ (s.re - 1)) := by
        rcases le_or_gt 0 (s.re - 1) with hr | hr
        · exact (Real.rpow_le_rpow ht0.le ht.2 hr).trans (le_max_right _ _)
        · exact (Real.rpow_le_rpow_of_nonpos ha ht.1 hr.le).trans (le_max_left _ _)
      refine htb.trans (max_le ?_ ?_)
      · exact (hpow a ha (by linarith) (by linarith)).trans (le_max_left _ _)
      · exact (hpow b hb0 (by linarith) (by linarith)).trans (le_max_right _ _)
    calc ‖∫ t in Icc a b, (t : ℂ) ^ (s - 1) • f t‖
        ≤ ∫ t in Icc a b, ‖(t : ℂ) ^ (s - 1) • f t‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t in Icc a b, M * ‖f t‖ := by
          refine setIntegral_mono_on ?_ (hint.norm.const_mul M) measurableSet_Icc hbound
          have hmc := mellinConvergent_of_integrableOn_support_subset ha hint hf s
          exact (hmc.mono_set fun t (ht : t ∈ Icc a b) ↦ ha.trans_le ht.1).norm
      _ = M * ∫ t in Icc a b, ‖f t‖ := integral_const_mul M _
  · rw [Icc_eq_empty_of_lt hba, subset_empty_iff, Function.support_eq_empty_iff] at hf
    simp [hf, mellin]

/-- One-step integration by parts for the Mellin transform of a differentiable compactly supported
function: `s • mellin f s = -mellin (deriv f) (s + 1)` for every `s : ℂ`. -/
theorem smul_mellin_eq_neg_mellin_deriv {f : ℝ → E} {a b : ℝ} (ha : 0 < a)
    (hdiff : Differentiable ℝ f) (hint : IntegrableOn (deriv f) (Icc a b))
    (hsupp : Function.support f ⊆ Icc a b) (s : ℂ) :
    s • mellin f s = -mellin (deriv f) (s + 1) := by
  by_cases hE : CompleteSpace E
  · rcases le_or_gt a b with hab | hba
    · have hsupp' : Function.support (deriv f) ⊆ Icc a b :=
        support_deriv_subset.trans (closure_minimal hsupp isClosed_Icc)
      have hfa : f a = 0 := by
        have hlt : f =ᶠ[𝓝[<] a] 0 := by
          filter_upwards [self_mem_nhdsWithin] with t ht
          have hnot : t ∉ Icc a b := fun h ↦ not_lt_of_ge h.1 ht
          exact Function.notMem_support.mp fun h ↦ hnot (hsupp h)
        exact tendsto_nhds_unique
          (hdiff.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
          (tendsto_const_nhds.congr' hlt.symm)
      have hfb : f b = 0 := by
        have hgt : f =ᶠ[𝓝[>] b] 0 := by
          filter_upwards [self_mem_nhdsWithin] with t ht
          have hnot : t ∉ Icc a b := fun h ↦ not_lt_of_ge h.2 ht
          exact Function.notMem_support.mp fun h ↦ hnot (hsupp h)
        exact tendsto_nhds_unique
          (hdiff.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
          (tendsto_const_nhds.congr' hgt.symm)
      have hderiv : ∀ t ∈ uIcc a b,
          HasDerivAt (fun y : ℝ ↦ (y : ℂ) ^ s • f y)
            ((t : ℂ) ^ s • deriv f t + (s * (t : ℂ) ^ (s - 1)) • f t) t := by
        intro t ht
        rw [uIcc_of_le hab] at ht
        have ht0 : t ≠ 0 := (ha.trans_le ht.1).ne'
        have hcpow : HasDerivAt (fun y : ℝ ↦ (y : ℂ) ^ s) (s * (t : ℂ) ^ (s - 1)) t := by
          rcases eq_or_ne s 0 with rfl | hs
          · simpa only [Complex.cpow_zero, zero_mul] using hasDerivAt_const t (1 : ℂ)
          · exact hasDerivAt_ofReal_cpow_const ht0 hs
        exact hcpow.fun_smul (hdiff t).hasDerivAt
      have hint1 : IntervalIntegrable (fun t : ℝ ↦ (t : ℂ) ^ s • deriv f t) volume a b := by
        have hmc := mellinConvergent_of_integrableOn_support_subset ha hint hsupp' (s + 1)
        have hsub : IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ s • deriv f t) (Ioc a b) := by
          simpa only [add_sub_cancel_right] using
            hmc.mono_set fun t (ht : t ∈ Ioc a b) ↦ ha.trans ht.1
        exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr hsub
      have hint2 :
          IntervalIntegrable (fun t : ℝ ↦ (s * (t : ℂ) ^ (s - 1)) • f t) volume a b := by
        have hmc := mellinConvergent_of_integrableOn_support_subset ha
          hdiff.continuous.integrableOn_Icc hsupp s
        have hsub : IntegrableOn (fun t : ℝ ↦ (s * (t : ℂ) ^ (s - 1)) • f t) (Ioc a b) := by
          simpa only [IntegrableOn, mul_smul, Pi.smul_def] using
            (hmc.mono_set fun t (ht : t ∈ Ioc a b) ↦ ha.trans ht.1).smul s
        exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr hsub
      have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hint1.add hint2)
      rw [hfa, hfb, smul_zero, smul_zero, sub_self, intervalIntegral.integral_add hint1 hint2]
        at hftc
      have hm1 : (∫ t in a..b, (t : ℂ) ^ s • deriv f t) = mellin (deriv f) (s + 1) := by
        rw [mellin_eq_intervalIntegral_of_support_subset ha.le hsupp' (s + 1), add_sub_cancel_right]
      have hm2 : (∫ t in a..b, (s * (t : ℂ) ^ (s - 1)) • f t) = s • mellin f s := by
        simp only [mul_smul, intervalIntegral.integral_smul,
          mellin_eq_intervalIntegral_of_support_subset ha.le hsupp s]
      rw [hm1, hm2] at hftc
      exact eq_neg_of_add_eq_zero_right hftc
    · rw [Icc_eq_empty_of_lt hba, subset_empty_iff, Function.support_eq_empty_iff] at hsupp
      simp [hsupp, mellin]
  · simp [mellin, integral_of_not_completeSpace hE]

/-- `k`-fold integration by parts for the Mellin transform of a `C^k` compactly supported function:
`(∏ j ∈ Finset.range k, (s + j)) • mellin f s = (-1)^k • mellin (iteratedDeriv k f) (s + k)`. -/
theorem prod_add_smul_mellin_eq_mellin_iteratedDeriv {f : ℝ → E} {k : ℕ} {a b : ℝ} (ha : 0 < a)
    (hf : ContDiff ℝ k f) (hsupp : Function.support f ⊆ Icc a b) (s : ℂ) :
    (∏ j ∈ Finset.range k, (s + j)) • mellin f s =
      (-1 : ℂ) ^ k • mellin (iteratedDeriv k f) (s + k) := by
  induction k generalizing f s with
  | zero =>
    simp [iteratedDeriv_zero]
  | succ k ih =>
    have hf' : ContDiff ℝ k (deriv f) := hf.deriv'
    have hdiff : Differentiable ℝ f := hf.differentiable (by simp)
    have hsupp' : Function.support (deriv f) ⊆ Icc a b :=
      support_deriv_subset.trans (closure_minimal hsupp isClosed_Icc)
    have hprod : (∏ j ∈ Finset.range (k + 1), (s + j)) =
        (∏ j ∈ Finset.range k, ((s + 1) + j)) * s := by
      rw [Finset.prod_range_succ']
      simp only [Nat.cast_zero, add_zero, Nat.cast_add, Nat.cast_one]
      congr 1
      refine Finset.prod_congr rfl fun j _ ↦ ?_
      ring
    rw [hprod, mul_smul,
      smul_mellin_eq_neg_mellin_deriv ha hdiff hf'.continuous.integrableOn_Icc hsupp s,
      smul_neg, ih hf' hsupp' (s + 1), ← neg_smul, ← neg_one_mul, ← pow_succ',
      ← iteratedDeriv_succ' (f := f)]
    congr 2
    push_cast
    ring

/-- Division form of `k`-fold integration by parts for `mellin f s`, away from the nonpositive
integers `0, -1, ..., -(k - 1)`. -/
theorem mellin_eq_div_prod_smul_mellin_iteratedDeriv {f : ℝ → E} {k : ℕ} {a b : ℝ} (ha : 0 < a)
    (hf : ContDiff ℝ k f) (hsupp : Function.support f ⊆ Icc a b) {s : ℂ}
    (hs : ∀ j < k, s + j ≠ 0) :
    mellin f s =
      ((-1 : ℂ) ^ k / ∏ j ∈ Finset.range k, (s + j)) • mellin (iteratedDeriv k f) (s + k) := by
  have hne : (∏ j ∈ Finset.range k, (s + j)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j hj ↦ hs j (Finset.mem_range.mp hj)
  have hibp := prod_add_smul_mellin_eq_mellin_iteratedDeriv ha hf hsupp s
  calc mellin f s
      = (∏ j ∈ Finset.range k, (s + j))⁻¹ • ((∏ j ∈ Finset.range k, (s + j)) • mellin f s) :=
        (inv_smul_smul₀ hne _).symm
    _ = (∏ j ∈ Finset.range k, (s + j))⁻¹ • ((-1 : ℂ) ^ k • mellin (iteratedDeriv k f) (s + k)) :=
        by rw [hibp]
    _ = ((-1 : ℂ) ^ k / ∏ j ∈ Finset.range k, (s + j)) • mellin (iteratedDeriv k f) (s + k) := by
        rw [smul_smul, div_eq_inv_mul]

/-- Uniform rapid decay on vertical strips: if `f` is `C^k` and supported in `[a, b]` with `0 < a`,
then for any `σ₁, σ₂ : ℝ` there is `C ≥ 0` such that `‖mellin f s‖ ≤ C / (1 + ‖s‖) ^ k` whenever
`σ₁ ≤ Re s ≤ σ₂`. -/
theorem exists_norm_mellin_le_div_one_add_norm_pow {f : ℝ → E} {k : ℕ} {a b : ℝ} (ha : 0 < a)
    (hf : ContDiff ℝ k f) (hsupp : Function.support f ⊆ Icc a b) (σ₁ σ₂ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ →
      ‖mellin f s‖ ≤ C / (1 + ‖s‖) ^ k := by
  obtain ⟨C₀, hC₀0, hC₀⟩ := exists_norm_mellin_le_of_integrableOn_support_subset ha
    hf.continuous.integrableOn_Icc hsupp σ₁ σ₂
  rcases eq_or_ne k 0 with rfl | hk
  · exact ⟨C₀, hC₀0, fun s h1 h2 ↦ by simpa using hC₀ s h1 h2⟩
  have hsupp_k : Function.support (iteratedDeriv k f) ⊆ Icc a b := by
    intro x hx
    apply closure_minimal hsupp isClosed_Icc
    apply support_iteratedFDeriv_subset (𝕜 := ℝ) k
    intro h0
    exact hx (by rw [iteratedDeriv_eq_iteratedFDeriv, h0]; simp)
  obtain ⟨Cₖ, hCₖ0, hCₖ⟩ := exists_norm_mellin_le_of_integrableOn_support_subset ha
    (hf.continuous_iteratedDeriv' k).integrableOn_Icc hsupp_k (σ₁ + k) (σ₂ + k)
  let C : ℝ := max (Cₖ * 4 ^ k) (C₀ * (1 + 2 * (k : ℝ)) ^ k)
  have hC0 : 0 ≤ C := le_trans (by positivity) (le_max_left _ _)
  refine ⟨C, hC0, fun s hσ₁ hσ₂ ↦ ?_⟩
  have hdenom : 0 < (1 + ‖s‖) ^ k := by positivity
  rw [le_div_iff₀ hdenom]
  by_cases hs : ‖s‖ ≤ 2 * (k : ℝ)
  · calc ‖mellin f s‖ * (1 + ‖s‖) ^ k
        ≤ C₀ * (1 + 2 * (k : ℝ)) ^ k :=
          mul_le_mul (hC₀ s hσ₁ hσ₂) (pow_le_pow_left₀ (by positivity) (by linarith) k)
            (by positivity) hC₀0
      _ ≤ C := le_max_right _ _
  · push Not at hs
    have hk1 : (1 : ℝ) ≤ k := Nat.one_le_cast.mpr (Nat.pos_of_ne_zero hk)
    have h1s : 1 + ‖s‖ ≤ 4 * (‖s‖ / 2) := by linarith
    have hprod_lb : (‖s‖ / 2) ^ k ≤ ‖∏ j ∈ Finset.range k, (s + j)‖ := by
      rw [norm_prod]
      calc (‖s‖ / 2) ^ k
          = ∏ _j ∈ Finset.range k, (‖s‖ / 2) := by
            rw [Finset.prod_const, Finset.card_range]
        _ ≤ ∏ j ∈ Finset.range k, ‖s + (j : ℂ)‖ := by
            refine Finset.prod_le_prod₀ (fun _ _ ↦ by positivity) fun j hj ↦ ?_
            have hjk : (j : ℝ) < k := Nat.cast_lt.mpr (Finset.mem_range.mp hj)
            have hrev := norm_sub_norm_le s (-(j : ℂ))
            rw [sub_neg_eq_add, norm_neg, Complex.norm_natCast] at hrev
            linarith
    have hibp := congrArg norm (prod_add_smul_mellin_eq_mellin_iteratedDeriv ha hf hsupp s)
    simp only [norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul] at hibp
    have hsk : ‖mellin (iteratedDeriv k f) (s + k)‖ ≤ Cₖ := by
      refine hCₖ (s + k) ?_ ?_ <;> simp <;> linarith
    calc ‖mellin f s‖ * (1 + ‖s‖) ^ k
        ≤ ‖mellin f s‖ * (4 * (‖s‖ / 2)) ^ k :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h1s k) (norm_nonneg _)
      _ = ((‖s‖ / 2) ^ k * ‖mellin f s‖) * 4 ^ k := by rw [mul_pow]; ring
      _ ≤ (‖∏ j ∈ Finset.range k, (s + j)‖ * ‖mellin f s‖) * 4 ^ k := by
          gcongr
      _ = ‖mellin (iteratedDeriv k f) (s + k)‖ * 4 ^ k := by rw [hibp]
      _ ≤ Cₖ * 4 ^ k := by gcongr
      _ ≤ C := le_max_left _ _

end TauCeti
