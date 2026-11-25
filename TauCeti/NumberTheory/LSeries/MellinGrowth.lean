/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
module

public import TauCeti.Analysis.MellinTransform.Growth
public import TauCeti.Analysis.Complex.FiniteOrder
public import TauCeti.Analysis.Complex.VerticalStrip.Growth
public import TauCeti.NumberTheory.LSeries.FEPairWithLevel
import TauCeti.Analysis.SpecialFunctions.Exp.StretchedDecay

/-!
# Order-one and vertical-strip growth from split Mellin integrals

For Mathlib's `WeakFEPair` and its level-`N` counterpart `TauCeti.FEPairWithLevel`, the entire
part `Λ₀` is the sum of two Mellin tails over `(1, ∞)`, with the dual argument `k - s` and the
root number `ε`. If both kernel tails have stretched-exponential decay `=O[atTop]` (which is
preserved under the level-`N` rescaling `g (· / N)`), these integrals give
`‖Λ₀(s)‖ ≤ exp (C (1 + ‖s‖) log (2 + ‖s‖))` for a fixed positive `C` together with uniform
boundedness on every closed vertical strip `a ≤ Re s ≤ b`.

Passing from `Λ₀` to the pole-cleared entire completion `entireΛ` (or directly to `Λ` when both
constant terms vanish) yields:
* global `exp (C (1 + ‖s‖) log (2 + ‖s‖))` norm bounds for vector-valued pairs;
* `OrderLE _ 1` and `IsFiniteOrder _` for complex-valued pairs;
* polynomial `HasVerticalStripGrowth` on every closed vertical strip.

The split identity and norm bounds use Mathlib's Mellin inversion substitution and the upper-tail
indicator identities of `TauCeti.Analysis.MellinTransform.Basic`. The entire-part construction and
its functional equation are David Loeffler's Mathlib theory; this file supplies the quantitative
growth adapter for weak, strong, pole-cleared, and level-`N` pairs.

## References

* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, Chapter 5.
-/

public section

open Real Set MeasureTheory Filter Topology Asymptotics

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

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
  have hF : MellinConvergent F s := (mellinConvergent_indicator_Ioi_iff zero_le_one).mpr hf
  have hG : MellinConvergent G (P.k - s) := (mellinConvergent_indicator_Ioi_iff zero_le_one).mpr hg
  have hi : MellinConvergent (fun x ↦ G x⁻¹) (s - P.k) :=
    (mellinConvergent_comp_inv_iff G (s - P.k)).mpr (by rwa [neg_sub])
  have ht : MellinConvergent (fun x ↦ P.ε • (x : ℂ) ^ (-(P.k : ℂ)) • G x⁻¹) s := by
    apply MellinConvergent.const_smul
    apply MellinConvergent.cpow_smul.mpr
    simpa only [sub_eq_add_neg] using hi
  have he : P.Λ₀ s = mellin (fun x ↦ F x + P.ε • (x : ℂ) ^ (-(P.k : ℂ)) • G x⁻¹) s := by
    rw [WeakFEPair.Λ₀, mellin, mellin]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
    rw [WeakFEPair_f_modif_eq P hx]
  rw [he, (hasMellin_add hF ht).2, mellin_const_smul, mellin_cpow_smul, mellin_comp_inv]
  simp only [neg_add_rev, neg_neg]
  rw [mellin_indicator_Ioi _ zero_le_one, mellin_indicator_Ioi _ zero_le_one]
  simp only [sub_eq_add_neg]

/-- Stretched-exponential decay of both kernel tails gives a global logarithmic-exponential bound
for the entire part of their Mellin continuation. The two tails may have different decay
exponents. -/
theorem _root_.WeakFEPair.exists_norm_Λ₀_le_exp_mul_log (P : WeakFEPair E)
    {c₁ α₁ c₂ α₂ : ℝ} (hc₁ : 0 < c₁) (hα₁ : 0 < α₁) (hc₂ : 0 < c₂) (hα₂ : 0 < α₂)
    (hf : (fun u ↦ P.f u - P.f₀) =O[atTop] fun u ↦ exp (-c₁ * u ^ α₁))
    (hg : (fun u ↦ P.g u - P.g₀) =O[atTop] fun u ↦ exp (-c₂ * u ^ α₂)) :
    ∃ C > 0, ∀ s : ℂ, ‖P.Λ₀ s‖ ≤ exp (C * (1 + ‖s‖) * log (2 + ‖s‖)) := by
  have hf_loc := (P.hf_int.sub (locallyIntegrableOn_const P.f₀)).mono_set
    (Ici_subset_Ioi.mpr zero_lt_one)
  have hg_loc := (P.hg_int.sub (locallyIntegrableOn_const P.g₀)).mono_set
    (Ici_subset_Ioi.mpr zero_lt_one)
  obtain ⟨A, hA, hF⟩ :=
    exists_norm_integral_cpow_smul_le_exp_mul_log_of_isBigO hf_loc hc₁ hα₁ hf
  obtain ⟨B, hB, hG⟩ :=
    exists_norm_integral_cpow_smul_le_exp_mul_log_of_isBigO hg_loc hc₂ hα₂ hg
  obtain ⟨B', -, hG_aff⟩ := exists_norm_comp_mul_add_le_exp_mul_log ⟨B, hB, hG⟩ (-1) P.k
  let K := max A B'
  let D := 1 + ‖P.ε‖
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨K + 2 * D, add_pos (lt_max_of_lt_left hA) (by positivity), fun s ↦ ?_⟩
  rw [WeakFEPair.Λ₀_eq_integral_add_smul_integral P s
    (integrableOn_cpow_smul_of_isBigO_exp_neg_mul_rpow hf_loc hc₁ hα₁ hf s)
    (integrableOn_cpow_smul_of_isBigO_exp_neg_mul_rpow hg_loc hc₂ hα₂ hg (P.k - s))]
  have hF' : ‖∫ (u : ℝ) in Ioi 1, (u : ℂ) ^ (s - 1) • (P.f u - P.f₀)‖ ≤
      exp (K * (1 + ‖s‖) * log (2 + ‖s‖)) :=
    (hF s).trans (exp_mul_one_add_mul_log_two_add_le_of_le (le_max_left A B') (norm_nonneg s))
  have hG' : ‖∫ (u : ℝ) in Ioi 1, (u : ℂ) ^ ((P.k - s) - 1) • (P.g u - P.g₀)‖ ≤
      exp (K * (1 + ‖s‖) * log (2 + ‖s‖)) := by
    have harg : (-1 : ℂ) * s + P.k = P.k - s := by ring
    exact (harg ▸ hG_aff s).trans
      (exp_mul_one_add_mul_log_two_add_le_of_le (le_max_right A B') (norm_nonneg s))
  calc
    _ ≤ ‖∫ (u : ℝ) in Ioi 1, (u : ℂ) ^ (s - 1) • (P.f u - P.f₀)‖ +
        ‖P.ε • (∫ (u : ℝ) in Ioi 1, (u : ℂ) ^ ((P.k - s) - 1) • (P.g u - P.g₀))‖ :=
      norm_add_le _ _
    _ ≤ D * exp (K * (1 + ‖s‖) * log (2 + ‖s‖)) := by
      rw [norm_smul]; dsimp [D]; nlinarith [mul_le_mul_of_nonneg_left hG' (norm_nonneg P.ε)]
    _ ≤ _ := mul_exp_mul_one_add_mul_log_two_add_le hD.le (norm_nonneg s)

/-- The entire part of a complex weak functional-equation pair has order at most one when
both kernel tails decay stretched-exponentially. -/
theorem _root_.WeakFEPair.orderLE_Λ₀ (P : WeakFEPair ℂ)
    {c₁ α₁ c₂ α₂ : ℝ} (hc₁ : 0 < c₁) (hα₁ : 0 < α₁) (hc₂ : 0 < c₂) (hα₂ : 0 < α₂)
    (hf : (fun u ↦ P.f u - P.f₀) =O[atTop] fun u ↦ exp (-c₁ * u ^ α₁))
    (hg : (fun u ↦ P.g u - P.g₀) =O[atTop] fun u ↦ exp (-c₂ * u ^ α₂)) :
    OrderLE P.Λ₀ 1 := by
  obtain ⟨C, _, hC⟩ := P.exists_norm_Λ₀_le_exp_mul_log hc₁ hα₁ hc₂ hα₂ hf hg
  exact orderLE_one_of_norm_le_exp_mul_log hC

/-- If both kernel tails decay stretched-exponentially, the entire part of a weak
functional-equation pair is bounded on each closed vertical strip `a ≤ Re s ≤ b`. -/
theorem _root_.WeakFEPair.exists_norm_Λ₀_le_of_re_mem_Icc (P : WeakFEPair E)
    {c₁ α₁ c₂ α₂ : ℝ} (hc₁ : 0 < c₁) (hα₁ : 0 < α₁) (hc₂ : 0 < c₂) (hα₂ : 0 < α₂)
    (hf : (fun u ↦ P.f u - P.f₀) =O[atTop] fun u ↦ exp (-c₁ * u ^ α₁))
    (hg : (fun u ↦ P.g u - P.g₀) =O[atTop] fun u ↦ exp (-c₂ * u ^ α₂)) (a b : ℝ) :
    ∃ M, ∀ s : ℂ, s.re ∈ Icc a b → ‖P.Λ₀ s‖ ≤ M := by
  have hf_loc := (P.hf_int.sub (locallyIntegrableOn_const P.f₀)).mono_set
    (Ici_subset_Ioi.mpr zero_lt_one)
  have hg_loc := (P.hg_int.sub (locallyIntegrableOn_const P.g₀)).mono_set
    (Ici_subset_Ioi.mpr zero_lt_one)
  obtain ⟨B₁, _, hB₁⟩ :=
    exists_norm_integral_cpow_smul_le_of_re_le_of_isBigO hf_loc hc₁ hα₁ hf b
  obtain ⟨B₂, _, hB₂⟩ :=
    exists_norm_integral_cpow_smul_le_of_re_le_of_isBigO hg_loc hc₂ hα₂ hg (P.k - a)
  refine ⟨B₁ + ‖P.ε‖ * B₂, fun s hs ↦ ?_⟩
  rw [WeakFEPair.Λ₀_eq_integral_add_smul_integral P s
    (integrableOn_cpow_smul_of_isBigO_exp_neg_mul_rpow hf_loc hc₁ hα₁ hf s)
    (integrableOn_cpow_smul_of_isBigO_exp_neg_mul_rpow hg_loc hc₂ hα₂ hg (P.k - s))]
  have hdual : ((P.k : ℂ) - s).re ≤ P.k - a := by
    simp only [Complex.sub_re, Complex.ofReal_re]
    linarith [hs.1]
  refine (norm_add_le _ _).trans (add_le_add (hB₁ s hs.2) ?_)
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (hB₂ (P.k - s) hdual) (norm_nonneg _)

/-- Stretched-exponential decay of both kernel tails gives polynomial vertical-strip growth of
`Λ₀` for a complex weak functional-equation pair. -/
theorem _root_.WeakFEPair.hasVerticalStripGrowth_Λ₀ (P : WeakFEPair ℂ)
    {c₁ α₁ c₂ α₂ : ℝ} (hc₁ : 0 < c₁) (hα₁ : 0 < α₁) (hc₂ : 0 < c₂) (hα₂ : 0 < α₂)
    (hf : (fun u ↦ P.f u - P.f₀) =O[atTop] fun u ↦ exp (-c₁ * u ^ α₁))
    (hg : (fun u ↦ P.g u - P.g₀) =O[atTop] fun u ↦ exp (-c₂ * u ^ α₂)) :
    HasVerticalStripGrowth P.Λ₀ :=
  hasVerticalStripGrowth_of_forall_bound
    (P.exists_norm_Λ₀_le_of_re_mem_Icc hc₁ hα₁ hc₂ hα₂ hf hg)

/-- A global logarithmic-exponential bound on `Λ₀` transfers to the pole-cleared entire completion
`entireΛ`, absorbing both the quadratic factor `s (s - k)` and the linear residue terms. -/
theorem _root_.WeakFEPair.exists_norm_entireΛ_le_exp_mul_log_of_Λ₀ (P : WeakFEPair E)
    (hΛ₀ : ∃ C > 0, ∀ s : ℂ, ‖P.Λ₀ s‖ ≤ exp (C * (1 + ‖s‖) * log (2 + ‖s‖))) :
    ∃ C' > 0, ∀ s : ℂ, ‖P.entireΛ s‖ ≤ exp (C' * (1 + ‖s‖) * log (2 + ‖s‖)) := by
  obtain ⟨C, hC, hbound⟩ := hΛ₀
  let K := C + 2 + 2 * ‖(P.k : ℂ)‖
  let D := 1 + ‖P.f₀‖ + ‖P.ε • P.g₀‖
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨K + 2 * D, by dsimp [K]; positivity, fun s ↦ ?_⟩
  have hs0 : ‖s‖ ≤ exp (1 * (1 + ‖s‖) * log (2 + ‖s‖)) := by
    simpa using norm_sub_le_exp_mul_log 0 s
  have hsk : ‖s - P.k‖ ≤ exp ((1 + 2 * ‖(P.k : ℂ)‖) * (1 + ‖s‖) * log (2 + ‖s‖)) :=
    norm_sub_le_exp_mul_log (P.k : ℂ) s
  have h1 : ‖(s * (s - P.k)) • P.Λ₀ s‖ ≤ exp (K * (1 + ‖s‖) * log (2 + ‖s‖)) := by
    rw [norm_smul, norm_mul]
    calc ‖s‖ * ‖s - P.k‖ * ‖P.Λ₀ s‖
        ≤ (exp (1 * (1 + ‖s‖) * log (2 + ‖s‖)) *
            exp ((1 + 2 * ‖(P.k : ℂ)‖) * (1 + ‖s‖) * log (2 + ‖s‖))) *
            exp (C * (1 + ‖s‖) * log (2 + ‖s‖)) :=
          mul_le_mul (mul_le_mul hs0 hsk (norm_nonneg _) (exp_pos _).le) (hbound s)
            (norm_nonneg _) (by positivity)
      _ = exp (K * (1 + ‖s‖) * log (2 + ‖s‖)) := by
          rw [← exp_add, ← exp_add]
          congr 1; dsimp [K]; ring
  have h2 : ‖(s - P.k) • P.f₀‖ ≤ ‖P.f₀‖ * exp (K * (1 + ‖s‖) * log (2 + ‖s‖)) := by
    rw [norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_left
      (hsk.trans (exp_mul_one_add_mul_log_two_add_le_of_le (by dsimp [K]; linarith)
        (norm_nonneg s))) (norm_nonneg _)
  have h3 : ‖s • (P.ε • P.g₀)‖ ≤ ‖P.ε • P.g₀‖ * exp (K * (1 + ‖s‖) * log (2 + ‖s‖)) := by
    rw [norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_left
      (hs0.trans (exp_mul_one_add_mul_log_two_add_le_of_le
        (by dsimp [K]; linarith [norm_nonneg (P.k : ℂ)]) (norm_nonneg s))) (norm_nonneg _)
  rw [WeakFEPair.entireΛ_def]
  calc
    _ ≤ ‖(s * (s - P.k)) • P.Λ₀ s - (s - P.k) • P.f₀‖ + ‖s • (P.ε • P.g₀)‖ := norm_add_le _ _
    _ ≤ ‖(s * (s - P.k)) • P.Λ₀ s‖ + ‖(s - P.k) • P.f₀‖ + ‖s • (P.ε • P.g₀)‖ :=
      add_le_add (norm_sub_le _ _) le_rfl
    _ ≤ D * exp (K * (1 + ‖s‖) * log (2 + ‖s‖)) := by dsimp [D]; linarith
    _ ≤ _ := mul_exp_mul_one_add_mul_log_two_add_le hD.le (norm_nonneg s)

/-- Vertical-strip growth of `Λ₀` transfers to the pole-cleared entire completion `entireΛ`. -/
theorem _root_.WeakFEPair.hasVerticalStripGrowth_entireΛ_of_Λ₀ (P : WeakFEPair ℂ)
    (hΛ₀ : HasVerticalStripGrowth P.Λ₀) : HasVerticalStripGrowth P.entireΛ := by
  have heq : ∀ s, P.entireΛ s =
      (s * (s - P.k)) * P.Λ₀ s - (s - P.k) * P.f₀ + s * (P.ε * P.g₀) := fun s ↦ by
    simp [WeakFEPair.entireΛ_def]
  rw [hasVerticalStripGrowth_congr heq]
  exact (((hasVerticalStripGrowth_id.mul
    (hasVerticalStripGrowth_id.sub hasVerticalStripGrowth_const)).mul hΛ₀).sub
    ((hasVerticalStripGrowth_id.sub hasVerticalStripGrowth_const).mul
      hasVerticalStripGrowth_const)).add
    (hasVerticalStripGrowth_id.mul hasVerticalStripGrowth_const)

/-- Stretched-exponential decay of both kernel tails gives a global logarithmic-exponential bound
for the pole-cleared completion `entireΛ` of a weak functional-equation pair. -/
theorem _root_.WeakFEPair.exists_norm_entireΛ_le_exp_mul_log (P : WeakFEPair E)
    {c₁ α₁ c₂ α₂ : ℝ} (hc₁ : 0 < c₁) (hα₁ : 0 < α₁) (hc₂ : 0 < c₂) (hα₂ : 0 < α₂)
    (hf : (fun u ↦ P.f u - P.f₀) =O[atTop] fun u ↦ exp (-c₁ * u ^ α₁))
    (hg : (fun u ↦ P.g u - P.g₀) =O[atTop] fun u ↦ exp (-c₂ * u ^ α₂)) :
    ∃ C > 0, ∀ s : ℂ, ‖P.entireΛ s‖ ≤ exp (C * (1 + ‖s‖) * log (2 + ‖s‖)) :=
  P.exists_norm_entireΛ_le_exp_mul_log_of_Λ₀
    (P.exists_norm_Λ₀_le_exp_mul_log hc₁ hα₁ hc₂ hα₂ hf hg)

/-- The pole-cleared entire completion `entireΛ` of a complex weak pair has order at most one when
both kernel tails decay stretched-exponentially. -/
theorem _root_.WeakFEPair.orderLE_entireΛ (P : WeakFEPair ℂ)
    {c₁ α₁ c₂ α₂ : ℝ} (hc₁ : 0 < c₁) (hα₁ : 0 < α₁) (hc₂ : 0 < c₂) (hα₂ : 0 < α₂)
    (hf : (fun u ↦ P.f u - P.f₀) =O[atTop] fun u ↦ exp (-c₁ * u ^ α₁))
    (hg : (fun u ↦ P.g u - P.g₀) =O[atTop] fun u ↦ exp (-c₂ * u ^ α₂)) :
    OrderLE P.entireΛ 1 := by
  obtain ⟨C, _, hC⟩ := P.exists_norm_entireΛ_le_exp_mul_log hc₁ hα₁ hc₂ hα₂ hf hg
  exact orderLE_one_of_norm_le_exp_mul_log hC

/-- The pole-cleared entire completion `entireΛ` of a complex weak pair has finite order when both
kernel tails decay stretched-exponentially. -/
theorem _root_.WeakFEPair.isFiniteOrder_entireΛ (P : WeakFEPair ℂ)
    {c₁ α₁ c₂ α₂ : ℝ} (hc₁ : 0 < c₁) (hα₁ : 0 < α₁) (hc₂ : 0 < c₂) (hα₂ : 0 < α₂)
    (hf : (fun u ↦ P.f u - P.f₀) =O[atTop] fun u ↦ exp (-c₁ * u ^ α₁))
    (hg : (fun u ↦ P.g u - P.g₀) =O[atTop] fun u ↦ exp (-c₂ * u ^ α₂)) :
    IsFiniteOrder P.entireΛ :=
  (P.orderLE_entireΛ hc₁ hα₁ hc₂ hα₂ hf hg).isFiniteOrder

/-- The pole-cleared entire completion `entireΛ` of a complex weak pair has polynomial
vertical-strip growth when both kernel tails decay stretched-exponentially. -/
theorem _root_.WeakFEPair.hasVerticalStripGrowth_entireΛ (P : WeakFEPair ℂ)
    {c₁ α₁ c₂ α₂ : ℝ} (hc₁ : 0 < c₁) (hα₁ : 0 < α₁) (hc₂ : 0 < c₂) (hα₂ : 0 < α₂)
    (hf : (fun u ↦ P.f u - P.f₀) =O[atTop] fun u ↦ exp (-c₁ * u ^ α₁))
    (hg : (fun u ↦ P.g u - P.g₀) =O[atTop] fun u ↦ exp (-c₂ * u ^ α₂)) :
    HasVerticalStripGrowth P.entireΛ :=
  P.hasVerticalStripGrowth_entireΛ_of_Λ₀ (P.hasVerticalStripGrowth_Λ₀ hc₁ hα₁ hc₂ hα₂ hf hg)

section Strong

/-- For a strong functional-equation pair, stretched-exponential decay of `f` and `g` gives a
global logarithmic-exponential bound directly on the entire completed function `Λ`. -/
theorem _root_.IsStrongFEPair.exists_norm_Λ_le_exp_mul_log {P : WeakFEPair E}
    (hP : IsStrongFEPair P) {c₁ α₁ c₂ α₂ : ℝ}
    (hc₁ : 0 < c₁) (hα₁ : 0 < α₁) (hc₂ : 0 < c₂) (hα₂ : 0 < α₂)
    (hf : P.f =O[atTop] fun u ↦ exp (-c₁ * u ^ α₁))
    (hg : P.g =O[atTop] fun u ↦ exp (-c₂ * u ^ α₂)) :
    ∃ C > 0, ∀ s : ℂ, ‖P.Λ s‖ ≤ exp (C * (1 + ‖s‖) * log (2 + ‖s‖)) := by
  rw [hP.Λ_eq_Λ₀]
  exact P.exists_norm_Λ₀_le_exp_mul_log hc₁ hα₁ hc₂ hα₂
    (by simpa [hP.hf₀] using hf) (by simpa [hP.hg₀] using hg)

/-- For a complex strong functional-equation pair, stretched-exponential decay of `f` and `g`
implies that the completed function `Λ` has order at most one. -/
theorem _root_.IsStrongFEPair.orderLE_Λ {P : WeakFEPair ℂ} (hP : IsStrongFEPair P)
    {c₁ α₁ c₂ α₂ : ℝ} (hc₁ : 0 < c₁) (hα₁ : 0 < α₁) (hc₂ : 0 < c₂) (hα₂ : 0 < α₂)
    (hf : P.f =O[atTop] fun u ↦ exp (-c₁ * u ^ α₁))
    (hg : P.g =O[atTop] fun u ↦ exp (-c₂ * u ^ α₂)) :
    OrderLE P.Λ 1 := by
  obtain ⟨C, _, hC⟩ := hP.exists_norm_Λ_le_exp_mul_log hc₁ hα₁ hc₂ hα₂ hf hg
  exact orderLE_one_of_norm_le_exp_mul_log hC

/-- For a complex strong functional-equation pair, stretched-exponential decay of `f` and `g`
implies that `Λ` has finite order. -/
theorem _root_.IsStrongFEPair.isFiniteOrder_Λ {P : WeakFEPair ℂ} (hP : IsStrongFEPair P)
    {c₁ α₁ c₂ α₂ : ℝ} (hc₁ : 0 < c₁) (hα₁ : 0 < α₁) (hc₂ : 0 < c₂) (hα₂ : 0 < α₂)
    (hf : P.f =O[atTop] fun u ↦ exp (-c₁ * u ^ α₁))
    (hg : P.g =O[atTop] fun u ↦ exp (-c₂ * u ^ α₂)) :
    IsFiniteOrder P.Λ :=
  (hP.orderLE_Λ hc₁ hα₁ hc₂ hα₂ hf hg).isFiniteOrder

/-- For a strong functional-equation pair, stretched-exponential decay of `f` and `g` implies
boundedness of `Λ` on each closed vertical strip `a ≤ Re s ≤ b`. -/
theorem _root_.IsStrongFEPair.exists_norm_Λ_le_of_re_mem_Icc {P : WeakFEPair E}
    (hP : IsStrongFEPair P) {c₁ α₁ c₂ α₂ : ℝ}
    (hc₁ : 0 < c₁) (hα₁ : 0 < α₁) (hc₂ : 0 < c₂) (hα₂ : 0 < α₂)
    (hf : P.f =O[atTop] fun u ↦ exp (-c₁ * u ^ α₁))
    (hg : P.g =O[atTop] fun u ↦ exp (-c₂ * u ^ α₂)) (a b : ℝ) :
    ∃ M, ∀ s : ℂ, s.re ∈ Icc a b → ‖P.Λ s‖ ≤ M := by
  rw [hP.Λ_eq_Λ₀]
  exact P.exists_norm_Λ₀_le_of_re_mem_Icc hc₁ hα₁ hc₂ hα₂
    (by simpa [hP.hf₀] using hf) (by simpa [hP.hg₀] using hg) a b

/-- For a complex strong functional-equation pair, stretched-exponential decay of `f` and `g`
gives vertical-strip growth of `Λ`. -/
theorem _root_.IsStrongFEPair.hasVerticalStripGrowth_Λ {P : WeakFEPair ℂ} (hP : IsStrongFEPair P)
    {c₁ α₁ c₂ α₂ : ℝ} (hc₁ : 0 < c₁) (hα₁ : 0 < α₁) (hc₂ : 0 < c₂) (hα₂ : 0 < α₂)
    (hf : P.f =O[atTop] fun u ↦ exp (-c₁ * u ^ α₁))
    (hg : P.g =O[atTop] fun u ↦ exp (-c₂ * u ^ α₂)) :
    HasVerticalStripGrowth P.Λ :=
  hasVerticalStripGrowth_of_forall_bound
    (hP.exists_norm_Λ_le_of_re_mem_Icc hc₁ hα₁ hc₂ hα₂ hf hg)

end Strong

namespace FEPairWithLevel

/-- Stretched-exponential decay of `f - f₀` and `g - g₀` gives a global logarithmic-exponential
bound for the entire part `toWeakFEPair.Λ₀` at any positive level `N`. -/
theorem exists_norm_toWeakFEPair_Λ₀_le_exp_mul_log (P : FEPairWithLevel E)
    {c₁ α₁ c₂ α₂ : ℝ} (hc₁ : 0 < c₁) (hα₁ : 0 < α₁) (hc₂ : 0 < c₂) (hα₂ : 0 < α₂)
    (hf : (fun u ↦ P.f u - P.f₀) =O[atTop] fun u ↦ exp (-c₁ * u ^ α₁))
    (hg : (fun u ↦ P.g u - P.g₀) =O[atTop] fun u ↦ exp (-c₂ * u ^ α₂)) :
    ∃ C > 0, ∀ s : ℂ, ‖P.toWeakFEPair.Λ₀ s‖ ≤ exp (C * (1 + ‖s‖) * log (2 + ‖s‖)) :=
  P.toWeakFEPair.exists_norm_Λ₀_le_exp_mul_log hc₁ hα₁
    (div_pos hc₂ (rpow_pos_of_pos P.hN α₂)) hα₂ (by simpa using hf)
    (by simpa using isBigO_comp_div_exp_neg_mul_rpow P.hN hg)

/-- At any positive level, `toWeakFEPair.Λ₀` has order at most one when both kernel tails decay
stretched-exponentially. -/
theorem orderLE_toWeakFEPair_Λ₀ (P : FEPairWithLevel ℂ)
    {c₁ α₁ c₂ α₂ : ℝ} (hc₁ : 0 < c₁) (hα₁ : 0 < α₁) (hc₂ : 0 < c₂) (hα₂ : 0 < α₂)
    (hf : (fun u ↦ P.f u - P.f₀) =O[atTop] fun u ↦ exp (-c₁ * u ^ α₁))
    (hg : (fun u ↦ P.g u - P.g₀) =O[atTop] fun u ↦ exp (-c₂ * u ^ α₂)) :
    OrderLE P.toWeakFEPair.Λ₀ 1 :=
  P.toWeakFEPair.orderLE_Λ₀ hc₁ hα₁
    (div_pos hc₂ (rpow_pos_of_pos P.hN α₂)) hα₂ (by simpa using hf)
    (by simpa using isBigO_comp_div_exp_neg_mul_rpow P.hN hg)

/-- At any positive level, `toWeakFEPair.Λ₀` is bounded on every closed vertical strip
`a ≤ Re s ≤ b` when both kernel tails decay stretched-exponentially. -/
theorem exists_norm_toWeakFEPair_Λ₀_le_of_re_mem_Icc (P : FEPairWithLevel E)
    {c₁ α₁ c₂ α₂ : ℝ} (hc₁ : 0 < c₁) (hα₁ : 0 < α₁) (hc₂ : 0 < c₂) (hα₂ : 0 < α₂)
    (hf : (fun u ↦ P.f u - P.f₀) =O[atTop] fun u ↦ exp (-c₁ * u ^ α₁))
    (hg : (fun u ↦ P.g u - P.g₀) =O[atTop] fun u ↦ exp (-c₂ * u ^ α₂)) (a b : ℝ) :
    ∃ M, ∀ s : ℂ, s.re ∈ Icc a b → ‖P.toWeakFEPair.Λ₀ s‖ ≤ M :=
  P.toWeakFEPair.exists_norm_Λ₀_le_of_re_mem_Icc hc₁ hα₁
    (div_pos hc₂ (rpow_pos_of_pos P.hN α₂)) hα₂ (by simpa using hf)
    (by simpa using isBigO_comp_div_exp_neg_mul_rpow P.hN hg) a b

/-- At any positive level, `toWeakFEPair.Λ₀` has vertical-strip growth when both kernel tails
decay stretched-exponentially. -/
theorem hasVerticalStripGrowth_toWeakFEPair_Λ₀ (P : FEPairWithLevel ℂ)
    {c₁ α₁ c₂ α₂ : ℝ} (hc₁ : 0 < c₁) (hα₁ : 0 < α₁) (hc₂ : 0 < c₂) (hα₂ : 0 < α₂)
    (hf : (fun u ↦ P.f u - P.f₀) =O[atTop] fun u ↦ exp (-c₁ * u ^ α₁))
    (hg : (fun u ↦ P.g u - P.g₀) =O[atTop] fun u ↦ exp (-c₂ * u ^ α₂)) :
    HasVerticalStripGrowth P.toWeakFEPair.Λ₀ :=
  P.toWeakFEPair.hasVerticalStripGrowth_Λ₀ hc₁ hα₁
    (div_pos hc₂ (rpow_pos_of_pos P.hN α₂)) hα₂ (by simpa using hf)
    (by simpa using isBigO_comp_div_exp_neg_mul_rpow P.hN hg)

/-- With zero constant terms, stretched-exponential decay of `f` and `g` gives a global
logarithmic-exponential bound directly on `Λ` at any positive level. -/
theorem exists_norm_Λ_le_exp_mul_log_of_constants_eq_zero (P : FEPairWithLevel E)
    (hf₀ : P.f₀ = 0) (hg₀ : P.g₀ = 0) {c₁ α₁ c₂ α₂ : ℝ}
    (hc₁ : 0 < c₁) (hα₁ : 0 < α₁) (hc₂ : 0 < c₂) (hα₂ : 0 < α₂)
    (hf : P.f =O[atTop] fun u ↦ exp (-c₁ * u ^ α₁))
    (hg : P.g =O[atTop] fun u ↦ exp (-c₂ * u ^ α₂)) :
    ∃ C > 0, ∀ s : ℂ, ‖P.Λ s‖ ≤ exp (C * (1 + ‖s‖) * log (2 + ‖s‖)) := by
  have hP : IsStrongFEPair P.toWeakFEPair := ⟨by simpa using hf₀, by simpa using hg₀⟩
  simpa only [toWeakFEPair_Λ] using hP.exists_norm_Λ_le_exp_mul_log hc₁ hα₁
    (div_pos hc₂ (rpow_pos_of_pos P.hN α₂)) hα₂ (by simpa using hf)
    (by simpa [Function.comp_def] using isBigO_comp_div_exp_neg_mul_rpow P.hN hg)

/-- With zero constant terms, stretched-exponential decay of `f` and `g` implies that `Λ` has
order at most one at any positive level. -/
theorem orderLE_Λ_of_constants_eq_zero (P : FEPairWithLevel ℂ)
    (hf₀ : P.f₀ = 0) (hg₀ : P.g₀ = 0) {c₁ α₁ c₂ α₂ : ℝ}
    (hc₁ : 0 < c₁) (hα₁ : 0 < α₁) (hc₂ : 0 < c₂) (hα₂ : 0 < α₂)
    (hf : P.f =O[atTop] fun u ↦ exp (-c₁ * u ^ α₁))
    (hg : P.g =O[atTop] fun u ↦ exp (-c₂ * u ^ α₂)) :
    OrderLE P.Λ 1 := by
  have hP : IsStrongFEPair P.toWeakFEPair := ⟨by simpa using hf₀, by simpa using hg₀⟩
  simpa only [toWeakFEPair_Λ] using hP.orderLE_Λ hc₁ hα₁
    (div_pos hc₂ (rpow_pos_of_pos P.hN α₂)) hα₂ (by simpa using hf)
    (by simpa [Function.comp_def] using isBigO_comp_div_exp_neg_mul_rpow P.hN hg)

/-- With zero constant terms, stretched-exponential decay of `f` and `g` implies that `Λ` has
finite order at any positive level. -/
theorem isFiniteOrder_Λ_of_constants_eq_zero (P : FEPairWithLevel ℂ)
    (hf₀ : P.f₀ = 0) (hg₀ : P.g₀ = 0) {c₁ α₁ c₂ α₂ : ℝ}
    (hc₁ : 0 < c₁) (hα₁ : 0 < α₁) (hc₂ : 0 < c₂) (hα₂ : 0 < α₂)
    (hf : P.f =O[atTop] fun u ↦ exp (-c₁ * u ^ α₁))
    (hg : P.g =O[atTop] fun u ↦ exp (-c₂ * u ^ α₂)) :
    IsFiniteOrder P.Λ := by
  have hP : IsStrongFEPair P.toWeakFEPair := ⟨by simpa using hf₀, by simpa using hg₀⟩
  simpa only [toWeakFEPair_Λ] using hP.isFiniteOrder_Λ hc₁ hα₁
    (div_pos hc₂ (rpow_pos_of_pos P.hN α₂)) hα₂ (by simpa using hf)
    (by simpa [Function.comp_def] using isBigO_comp_div_exp_neg_mul_rpow P.hN hg)

/-- With zero constant terms, stretched-exponential decay of `f` and `g` implies that `Λ` is
bounded on every closed vertical strip `a ≤ Re s ≤ b`. -/
theorem exists_norm_Λ_le_of_re_mem_Icc_of_constants_eq_zero (P : FEPairWithLevel E)
    (hf₀ : P.f₀ = 0) (hg₀ : P.g₀ = 0) {c₁ α₁ c₂ α₂ : ℝ}
    (hc₁ : 0 < c₁) (hα₁ : 0 < α₁) (hc₂ : 0 < c₂) (hα₂ : 0 < α₂)
    (hf : P.f =O[atTop] fun u ↦ exp (-c₁ * u ^ α₁))
    (hg : P.g =O[atTop] fun u ↦ exp (-c₂ * u ^ α₂)) (a b : ℝ) :
    ∃ M, ∀ s : ℂ, s.re ∈ Icc a b → ‖P.Λ s‖ ≤ M := by
  have hP : IsStrongFEPair P.toWeakFEPair := ⟨by simpa using hf₀, by simpa using hg₀⟩
  simpa only [toWeakFEPair_Λ] using hP.exists_norm_Λ_le_of_re_mem_Icc hc₁ hα₁
    (div_pos hc₂ (rpow_pos_of_pos P.hN α₂)) hα₂ (by simpa using hf)
    (by simpa [Function.comp_def] using isBigO_comp_div_exp_neg_mul_rpow P.hN hg) a b

/-- With zero constant terms, stretched-exponential decay of `f` and `g` gives vertical-strip
growth of `Λ` at any positive level. -/
theorem hasVerticalStripGrowth_Λ_of_constants_eq_zero (P : FEPairWithLevel ℂ)
    (hf₀ : P.f₀ = 0) (hg₀ : P.g₀ = 0) {c₁ α₁ c₂ α₂ : ℝ}
    (hc₁ : 0 < c₁) (hα₁ : 0 < α₁) (hc₂ : 0 < c₂) (hα₂ : 0 < α₂)
    (hf : P.f =O[atTop] fun u ↦ exp (-c₁ * u ^ α₁))
    (hg : P.g =O[atTop] fun u ↦ exp (-c₂ * u ^ α₂)) :
    HasVerticalStripGrowth P.Λ := by
  have hP : IsStrongFEPair P.toWeakFEPair := ⟨by simpa using hf₀, by simpa using hg₀⟩
  simpa only [toWeakFEPair_Λ] using hP.hasVerticalStripGrowth_Λ hc₁ hα₁
    (div_pos hc₂ (rpow_pos_of_pos P.hN α₂)) hα₂ (by simpa using hf)
    (by simpa [Function.comp_def] using isBigO_comp_div_exp_neg_mul_rpow P.hN hg)

/-- Stretched-exponential decay of both kernel tails gives a global logarithmic-exponential bound
for the pole-cleared entire completion `entireΛ` at level `N`. -/
theorem exists_norm_entireΛ_le_exp_mul_log (P : FEPairWithLevel E)
    {c₁ α₁ c₂ α₂ : ℝ} (hc₁ : 0 < c₁) (hα₁ : 0 < α₁) (hc₂ : 0 < c₂) (hα₂ : 0 < α₂)
    (hf : (fun u ↦ P.f u - P.f₀) =O[atTop] fun u ↦ exp (-c₁ * u ^ α₁))
    (hg : (fun u ↦ P.g u - P.g₀) =O[atTop] fun u ↦ exp (-c₂ * u ^ α₂)) :
    ∃ C > 0, ∀ s : ℂ, ‖P.entireΛ s‖ ≤ exp (C * (1 + ‖s‖) * log (2 + ‖s‖)) := by
  simpa only [toWeakFEPair_entireΛ] using P.toWeakFEPair.exists_norm_entireΛ_le_exp_mul_log hc₁ hα₁
    (div_pos hc₂ (rpow_pos_of_pos P.hN α₂)) hα₂ (by simpa using hf)
    (by simpa using isBigO_comp_div_exp_neg_mul_rpow P.hN hg)

/-- The pole-cleared entire completion `entireΛ` of a complex level-`N` pair has order at most one
when both kernel tails decay stretched-exponentially. -/
theorem orderLE_entireΛ (P : FEPairWithLevel ℂ)
    {c₁ α₁ c₂ α₂ : ℝ} (hc₁ : 0 < c₁) (hα₁ : 0 < α₁) (hc₂ : 0 < c₂) (hα₂ : 0 < α₂)
    (hf : (fun u ↦ P.f u - P.f₀) =O[atTop] fun u ↦ exp (-c₁ * u ^ α₁))
    (hg : (fun u ↦ P.g u - P.g₀) =O[atTop] fun u ↦ exp (-c₂ * u ^ α₂)) :
    OrderLE P.entireΛ 1 := by
  simpa only [toWeakFEPair_entireΛ] using P.toWeakFEPair.orderLE_entireΛ hc₁ hα₁
    (div_pos hc₂ (rpow_pos_of_pos P.hN α₂)) hα₂ (by simpa using hf)
    (by simpa using isBigO_comp_div_exp_neg_mul_rpow P.hN hg)

/-- The pole-cleared entire completion `entireΛ` of a complex level-`N` pair has finite order when
both kernel tails decay stretched-exponentially. -/
theorem isFiniteOrder_entireΛ (P : FEPairWithLevel ℂ)
    {c₁ α₁ c₂ α₂ : ℝ} (hc₁ : 0 < c₁) (hα₁ : 0 < α₁) (hc₂ : 0 < c₂) (hα₂ : 0 < α₂)
    (hf : (fun u ↦ P.f u - P.f₀) =O[atTop] fun u ↦ exp (-c₁ * u ^ α₁))
    (hg : (fun u ↦ P.g u - P.g₀) =O[atTop] fun u ↦ exp (-c₂ * u ^ α₂)) :
    IsFiniteOrder P.entireΛ := by
  simpa only [toWeakFEPair_entireΛ] using P.toWeakFEPair.isFiniteOrder_entireΛ hc₁ hα₁
    (div_pos hc₂ (rpow_pos_of_pos P.hN α₂)) hα₂ (by simpa using hf)
    (by simpa using isBigO_comp_div_exp_neg_mul_rpow P.hN hg)

/-- The pole-cleared entire completion `entireΛ` of a complex level-`N` pair has polynomial
vertical-strip growth when both kernel tails decay stretched-exponentially. -/
theorem hasVerticalStripGrowth_entireΛ (P : FEPairWithLevel ℂ)
    {c₁ α₁ c₂ α₂ : ℝ} (hc₁ : 0 < c₁) (hα₁ : 0 < α₁) (hc₂ : 0 < c₂) (hα₂ : 0 < α₂)
    (hf : (fun u ↦ P.f u - P.f₀) =O[atTop] fun u ↦ exp (-c₁ * u ^ α₁))
    (hg : (fun u ↦ P.g u - P.g₀) =O[atTop] fun u ↦ exp (-c₂ * u ^ α₂)) :
    HasVerticalStripGrowth P.entireΛ := by
  simpa only [toWeakFEPair_entireΛ] using P.toWeakFEPair.hasVerticalStripGrowth_entireΛ hc₁ hα₁
    (div_pos hc₂ (rpow_pos_of_pos P.hN α₂)) hα₂ (by simpa using hf)
    (by simpa using isBigO_comp_div_exp_neg_mul_rpow P.hN hg)

end FEPairWithLevel

end TauCeti
