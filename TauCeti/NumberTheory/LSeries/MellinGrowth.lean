/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
module

public import TauCeti.Analysis.MellinTransform.Growth
public import Mathlib.NumberTheory.LSeries.AbstractFuncEq

/-!
# Order-one growth from split Mellin integrals

For Mathlib's `WeakFEPair`, the entire part `Λ₀` is the sum of two Mellin tails over
`(1, ∞)`, with the dual argument `k-s` and the root number `ε`.
If both kernel tails have exponential bounds, these integrals give
`‖Λ₀(s)‖ ≤ exp (C (1+‖s‖) log (2+‖s‖))` for a fixed positive `C`.
Thus a complex-valued `Λ₀` has order at most one.

The split identity and norm bound also apply to vector-valued pairs. They use
Mathlib's Mellin inversion substitution and indicator integrals. The entire-part
construction and its functional equation are David Loeffler's Mathlib theory;
this file supplies the quantitative growth adapter.

## References

* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, Chapter 5.
-/

public section

open Real Set MeasureTheory Filter Topology Asymptotics

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

private theorem mellinConvergent_indicator_Ioi_one {f : ℝ → E} {s : ℂ}
    (hf : IntegrableOn (fun u : ℝ ↦ (u : ℂ) ^ (s - 1) • f u) (Ioi 1)) :
    MellinConvergent ((Ioi 1).indicator f) s := by
  simp_rw [MellinConvergent, ← indicator_smul, integrableOn_indicator_iff
    measurableSet_Ioi.nullMeasurableSet, inter_eq_left.mpr (Ioi_subset_Ioi zero_le_one)]
  exact hf

private theorem mellin_indicator_Ioi_one (f : ℝ → E) (s : ℂ) :
    mellin ((Ioi 1).indicator f) s = ∫ (u : ℝ) in Ioi 1, (u : ℂ) ^ (s - 1) • f u := by
  simp_rw [mellin, ← indicator_smul, setIntegral_indicator measurableSet_Ioi,
    inter_eq_right.mpr (Ioi_subset_Ioi zero_le_one)]

private theorem WeakFEPair_f_modif_eq (P : WeakFEPair E) {x : ℝ} (hx : 0 < x) :
    P.f_modif x = (Ioi 1).indicator (fun u ↦ P.f u - P.f₀) x +
      P.ε • (x : ℂ) ^ (-(P.k : ℂ)) •
        (Ioi 1).indicator (fun u ↦ P.g u - P.g₀) x⁻¹ := by
  rcases lt_trichotomy 1 x with h | rfl | h
  · have hinv : x⁻¹ ≤ 1 := (inv_le_one₀ hx).mpr h.le
    simp [WeakFEPair.f_modif, h, notMem_Ioo_of_ge h.le, notMem_Ioi.mpr hinv]
  · simp [WeakFEPair.f_modif]
  · have hinv : 1 < x⁻¹ := (one_lt_inv₀ hx).mpr h
    have hfe := P.h_feq x⁻¹ (inv_pos.mpr hx)
    simp only [one_div, inv_inv, inv_rpow hx.le, ← rpow_neg hx.le] at hfe
    have hpow : (x : ℂ) ^ (-(P.k : ℂ)) = (x ^ (-P.k) : ℝ) := by
      rw [Complex.ofReal_cpow hx.le, Complex.ofReal_neg]
    simp only [WeakFEPair.f_modif, Pi.add_apply, indicator_of_notMem (notMem_Ioi.mpr h.le),
      zero_add, indicator_of_mem (mem_Ioo.mpr ⟨hx, h⟩),
      indicator_of_mem (mem_Ioi.mpr hinv), hpow, smul_sub, ← mul_smul, hfe]

/-- The entire part of a weak functional-equation pair is the sum of its two upper Mellin
tails, with the root number multiplying the dual tail. -/
theorem _root_.WeakFEPair.Λ₀_eq_integral_add_smul_integral (P : WeakFEPair E) (s : ℂ)
    (hf : IntegrableOn (fun u : ℝ ↦ (u : ℂ) ^ (s - 1) • (P.f u - P.f₀)) (Ioi 1))
    (hg : IntegrableOn (fun u : ℝ ↦ (u : ℂ) ^ ((P.k - s) - 1) • (P.g u - P.g₀)) (Ioi 1)) :
    P.Λ₀ s = (∫ (u : ℝ) in Ioi 1, (u : ℂ) ^ (s - 1) • (P.f u - P.f₀)) +
      P.ε • (∫ (u : ℝ) in Ioi 1, (u : ℂ) ^ ((P.k - s) - 1) • (P.g u - P.g₀)) := by
  let F := (Ioi 1).indicator (fun u ↦ P.f u - P.f₀)
  let G := (Ioi 1).indicator (fun u ↦ P.g u - P.g₀)
  have hF : MellinConvergent F s := mellinConvergent_indicator_Ioi_one hf
  have hG : MellinConvergent G (P.k - s) := mellinConvergent_indicator_Ioi_one hg
  have hi : MellinConvergent (fun x ↦ G x⁻¹) (s - P.k) := by
    have hi := (MellinConvergent.comp_rpow (f := G) (s := s - P.k)
      (a := -1) (by norm_num)).mpr
      (by simpa only [Complex.ofReal_neg, Complex.ofReal_one, div_neg, div_one, neg_sub] using hG)
    simpa only [rpow_neg_one] using hi
  have ht : MellinConvergent (fun x ↦ P.ε • (x : ℂ) ^ (-(P.k : ℂ)) • G x⁻¹) s := by
    apply MellinConvergent.const_smul
    apply MellinConvergent.cpow_smul.mpr
    simpa only [sub_eq_add_neg] using hi
  have he : P.Λ₀ s = mellin (fun x ↦ F x + P.ε • (x : ℂ) ^ (-(P.k : ℂ)) • G x⁻¹) s := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    change (x : ℂ) ^ (s - 1) • P.f_modif x =
      (x : ℂ) ^ (s - 1) • (F x + P.ε • (x : ℂ) ^ (-(P.k : ℂ)) • G x⁻¹)
    rw [WeakFEPair_f_modif_eq P hx]
  rw [he, (hasMellin_add hF ht).2, mellin_const_smul, mellin_cpow_smul, mellin_comp_inv]
  simp only [neg_add_rev, neg_neg]
  rw [mellin_indicator_Ioi_one, mellin_indicator_Ioi_one]
  simp only [sub_eq_add_neg]


/-- Exponential decay of both kernels gives a global logarithmic-exponential bound for the
entire part of their Mellin continuation. The two tails may have different decay exponents. -/
theorem _root_.WeakFEPair.exists_norm_Λ₀_le_exp_mul_log (P : WeakFEPair E)
    {C₁ c₁ α₁ C₂ c₂ α₂ : ℝ}
    (hC₁ : 0 ≤ C₁) (hc₁ : 0 < c₁) (hα₁ : 0 < α₁)
    (hC₂ : 0 ≤ C₂) (hc₂ : 0 < c₂) (hα₂ : 0 < α₂)
    (hf : ∀ u ∈ Ioi 1, ‖P.f u - P.f₀‖ ≤ C₁ * exp (-c₁ * u ^ α₁))
    (hg : ∀ u ∈ Ioi 1, ‖P.g u - P.g₀‖ ≤ C₂ * exp (-c₂ * u ^ α₂)) :
    ∃ C > 0, ∀ s : ℂ, ‖P.Λ₀ s‖ ≤ exp (C * (1 + ‖s‖) * log (2 + ‖s‖)) := by
  obtain ⟨A, hA, hF⟩ := exists_norm_integral_cpow_smul_le_exp_mul_log hC₁ hc₁ hα₁ hf
  obtain ⟨B, hB, hG⟩ := exists_norm_integral_cpow_smul_le_exp_mul_log hC₂ hc₂ hα₂ hg
  let M := ‖(P.k : ℂ)‖ + 3
  let K := A + B * M * (2 * M + 1)
  have hM : 0 < M := by dsimp [M]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  let D := 1 + ‖P.ε‖
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨K + 2 * D, by positivity, fun s ↦ ?_⟩
  have hfmeas := ((P.hf_int.sub (locallyIntegrableOn_const P.f₀)).mono_set
    (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable
  have hgmeas := ((P.hg_int.sub (locallyIntegrableOn_const P.g₀)).mono_set
    (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable
  rw [WeakFEPair.Λ₀_eq_integral_add_smul_integral P s
    (integrableOn_cpow_smul_of_norm_le_exp_neg_mul_rpow hc₁ hα₁ hfmeas hf s)
    (integrableOn_cpow_smul_of_norm_le_exp_neg_mul_rpow hc₂ hα₂ hgmeas hg (P.k - s))]
  have hW : 0 ≤ (1 + ‖s‖) * log (2 + ‖s‖) :=
    mul_nonneg (by positivity) (log_nonneg (by linarith [norm_nonneg s]))
  have ht : ‖(P.k : ℂ) - s‖ ≤ (1 + ‖(P.k : ℂ)‖) * (1 + ‖s‖) := by
    exact (norm_sub_le _ _).trans (by nlinarith [norm_nonneg (P.k : ℂ), norm_nonneg s])
  have hscale := add_one_mul_log_add_two_le (norm_nonneg s) (norm_nonneg ((P.k : ℂ) - s))
    (show 0 ≤ 1 + ‖(P.k : ℂ)‖ by positivity) ht
  have hF' : ‖∫ (u : ℝ) in Ioi 1, (u : ℂ) ^ (s - 1) • (P.f u - P.f₀)‖ ≤
      exp (K * (1 + ‖s‖) * log (2 + ‖s‖)) := by
    apply (hF s).trans
    apply exp_le_exp.mpr
    dsimp [K]
    nlinarith [mul_nonneg (show 0 ≤ B * M * (2 * M + 1) by positivity) hW]
  have hG' : ‖∫ (u : ℝ) in Ioi 1, (u : ℂ) ^ ((P.k - s) - 1) • (P.g u - P.g₀)‖ ≤
      exp (K * (1 + ‖s‖) * log (2 + ‖s‖)) := by
    apply (hG (P.k - s)).trans
    apply exp_le_exp.mpr
    have hbscale := mul_le_mul_of_nonneg_left hscale hB.le
    dsimp [M] at *
    dsimp [K]
    nlinarith [mul_nonneg hA.le hW]
  have hL : (1 / 2 : ℝ) ≤ log (2 + ‖s‖) := by
    have h2 : (1 / 2 : ℝ) ≤ log 2 := by
      convert one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2) using 1; norm_num
    exact h2.trans (log_le_log (by norm_num) (by linarith [norm_nonneg s]))
  calc
    _ ≤ ‖∫ (u : ℝ) in Ioi 1, (u : ℂ) ^ (s - 1) • (P.f u - P.f₀)‖ +
        ‖P.ε • (∫ (u : ℝ) in Ioi 1, (u : ℂ) ^ ((P.k - s) - 1) • (P.g u - P.g₀))‖ :=
      norm_add_le _ _
    _ ≤ D * exp (K * (1 + ‖s‖) * log (2 + ‖s‖)) := by
      rw [norm_smul]
      dsimp [D]
      nlinarith [mul_le_mul_of_nonneg_left hG' (norm_nonneg P.ε)]
    _ ≤ exp D * exp (K * (1 + ‖s‖) * log (2 + ‖s‖)) := by
      gcongr
      linarith [add_one_le_exp D]
    _ = exp (D + K * (1 + ‖s‖) * log (2 + ‖s‖)) := (exp_add _ _).symm
    _ ≤ _ := by
      apply exp_le_exp.mpr
      have hRL : (1 / 2 : ℝ) ≤ (1 + ‖s‖) * log (2 + ‖s‖) := by
        nlinarith [norm_nonneg s]
      nlinarith [mul_le_mul_of_nonneg_left hRL hD.le]

/-- The entire part of a complex weak functional-equation pair has order at most one when
both kernels have exponential tails. -/
theorem _root_.WeakFEPair.orderLE_Λ₀_of_norm_sub_le_exp_neg_mul_rpow (P : WeakFEPair ℂ)
    {C₁ c₁ α₁ C₂ c₂ α₂ : ℝ}
    (hC₁ : 0 ≤ C₁) (hc₁ : 0 < c₁) (hα₁ : 0 < α₁)
    (hC₂ : 0 ≤ C₂) (hc₂ : 0 < c₂) (hα₂ : 0 < α₂)
    (hf : ∀ u ∈ Ioi 1, ‖P.f u - P.f₀‖ ≤ C₁ * exp (-c₁ * u ^ α₁))
    (hg : ∀ u ∈ Ioi 1, ‖P.g u - P.g₀‖ ≤ C₂ * exp (-c₂ * u ^ α₂)) :
    OrderLE P.Λ₀ 1 := by
  obtain ⟨C, _, hC⟩ := P.exists_norm_Λ₀_le_exp_mul_log hC₁ hc₁ hα₁ hC₂ hc₂ hα₂ hf hg
  exact orderLE_one_of_norm_le_exp_mul_log hC

end TauCeti
