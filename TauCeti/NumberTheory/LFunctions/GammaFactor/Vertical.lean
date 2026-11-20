/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Archimedean
public import TauCeti.NumberTheory.LFunctions.Data.Basic
import TauCeti.Analysis.SpecialFunctions.Gamma.Archimedean

/-!
# The gamma factor of an L-function record on vertical strips

Let `γ = d.gammaFactor` be the gamma factor of an analytic L-function record `d`, the product of
the shifted factors `Γ_ℝ(s + μ_j)` over the real shifts `μ_j` and `Γ_ℂ(s + ν_k)` over the complex
shifts `ν_k`, of degree `n = #{μ_j} + 2 #{ν_k}`. For every compact interval `[a, b]`,

  `log ‖γ(σ + i t)‖ = -(π n / 4) |t| + A(σ) log |t| + O(1)`,
  `A(σ) = ∑_j (σ + Re μ_j - 1) / 2 + ∑_k (σ + Re ν_k - 1/2)`,

uniformly for `σ ∈ [a, b]` as `|t| → ∞`. The exponential rate depends only on the degree: each
`Γ_ℝ` factor contributes `π / 4` and each `Γ_ℂ` factor `π / 2`. Since the estimate is additive in
`log ‖γ‖`, it follows by summing the shifted Stirling expansions of
`TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Archimedean` over the factors. Above the
imaginary parts of all shifts no factor has a pole, so `log ‖γ‖` is the sum of the logarithms of
the factors there.

For the `ζ` record (`gammaR = {0}`, `gammaC = ∅`) this reads
`log ‖Γ_ℝ(σ + i t)‖ = -(π/4) |t| + ((σ - 1)/2) log |t| + O(1)`.

## Main results

* `TauCeti.LFunctions.AnalyticLFunctionData.exists_abs_log_norm_gammaFactor_vertical_sub_le`: one
  constant and one height threshold for the whole strip `a ≤ Re s ≤ b`.
* `TauCeti.LFunctions.AnalyticLFunctionData.isBigO_log_norm_gammaFactor_vertical_sub`: the same
  as an `O(1)` statement along `𝓟 (Icc a b) ×ˢ cocompact ℝ` in the coordinates `s = σ + i t`.

## References

* H. Iwaniec and E. Kowalski, *Analytic Number Theory* (2004), §5.1, (5.3)–(5.4).
* [DLMF 5.11.9](https://dlmf.nist.gov/5.11.E9).
-/

public section

open Complex Real Filter Set Asymptotics

namespace TauCeti.LFunctions.AnalyticLFunctionData

/-- A factor estimate in additive logarithmic form adds up over a finite product: if each factor
`F μ` is eventually nonzero on a vertical strip with `log ‖F μ‖ = m μ + O(1)` there, so is the
product over a multiset of indices, against the sum of the main terms. -/
private theorem exists_abs_log_norm_multiset_prod_sub_le {F : ℂ → ℂ → ℂ} {m : ℂ → ℂ → ℝ}
    {a b : ℝ} (l : Multiset ℂ)
    (hF : ∀ μ ∈ l, ∃ C T : ℝ, ∀ s : ℂ, s.re ∈ Icc a b → T ≤ |s.im| →
      F μ s ≠ 0 ∧ |Real.log ‖F μ s‖ - m μ s| ≤ C) :
    ∃ C T : ℝ, ∀ s : ℂ, s.re ∈ Icc a b → T ≤ |s.im| →
      (l.map fun μ ↦ F μ s).prod ≠ 0 ∧
        |Real.log ‖(l.map fun μ ↦ F μ s).prod‖ - (l.map fun μ ↦ m μ s).sum| ≤ C := by
  induction l using Multiset.induction_on with
  | empty => exact ⟨0, 0, fun s _ _ ↦ by simp⟩
  | cons μ l ih =>
    obtain ⟨C₁, T₁, h₁⟩ := hF μ (Multiset.mem_cons_self μ l)
    obtain ⟨C₂, T₂, h₂⟩ := ih fun ν hν ↦ hF ν (Multiset.mem_cons_of_mem hν)
    refine ⟨C₁ + C₂, max T₁ T₂, fun s hs hT ↦ ?_⟩
    obtain ⟨hne₁, hb₁⟩ := h₁ s hs ((le_max_left _ _).trans hT)
    obtain ⟨hne₂, hb₂⟩ := h₂ s hs ((le_max_right _ _).trans hT)
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
    refine ⟨mul_ne_zero hne₁ hne₂, ?_⟩
    rw [norm_mul, Real.log_mul (norm_ne_zero_iff.2 hne₁) (norm_ne_zero_iff.2 hne₂)]
    calc _ = |(Real.log ‖F μ s‖ - m μ s) + (Real.log ‖(l.map fun μ ↦ F μ s).prod‖ -
          (l.map fun μ ↦ m μ s).sum)| := by ring_nf
      _ ≤ C₁ + C₂ := (abs_add_le _ _).trans (add_le_add hb₁ hb₂)

/-- Above the imaginary part of a shift, the shifted point is off the real axis. -/
private theorem im_add_ne_zero {s μ : ℂ} (h : |μ.im| + 1 ≤ |s.im|) : (s + μ).im ≠ 0 := by
  rw [add_im]
  intro h0
  rw [eq_neg_of_add_eq_zero_left h0, abs_neg] at h
  linarith

/-- **The gamma factor of a record on vertical strips**: for every strip `a ≤ Re s ≤ b` there are
`C` and `T` with
`|log ‖γ(s)‖ - (A(σ) log |t| - (π n / 4) |t|)| ≤ C` for `s = σ + i t` with `T ≤ |t|`, where `n` is
the degree and `A(σ) = ∑_j (σ + Re μ_j - 1)/2 + ∑_k (σ + Re ν_k - 1/2)`. -/
theorem exists_abs_log_norm_gammaFactor_vertical_sub_le (d : AnalyticLFunctionData) (a b : ℝ) :
    ∃ C T : ℝ, ∀ s : ℂ, s.re ∈ Icc a b → T ≤ |s.im| →
      |Real.log ‖d.gammaFactor s‖ -
          (((d.gammaR.map fun μ ↦ (s.re + μ.re - 1) / 2).sum +
              (d.gammaC.map fun ν ↦ s.re + ν.re - 1 / 2).sum) * Real.log |s.im| -
            π * d.degree / 4 * |s.im|)| ≤ C := by
  obtain ⟨C₁, T₁, h₁⟩ := exists_abs_log_norm_multiset_prod_sub_le
    (F := fun μ s ↦ Gammaℝ (s + μ))
    (m := fun μ s ↦ (s.re + μ.re - 1) / 2 * Real.log |s.im| - π / 4 * |s.im|) (a := a) (b := b)
    d.gammaR fun μ _ ↦ by
      obtain ⟨C, T, h⟩ := exists_abs_log_norm_Gammaℝ_add_vertical_sub_le a b μ
      refine ⟨C, max T (|μ.im| + 1), fun s hs hT ↦
        ⟨fun h0 ↦ ?_, h s hs ((le_max_left _ _).trans hT)⟩⟩
      obtain ⟨n, hn⟩ := Gammaℝ_eq_zero_iff.1 h0
      exact im_add_ne_zero ((le_max_right _ _).trans hT) (by simp [hn])
  obtain ⟨C₂, T₂, h₂⟩ := exists_abs_log_norm_multiset_prod_sub_le
    (F := fun ν s ↦ Gammaℂ (s + ν))
    (m := fun ν s ↦ (s.re + ν.re - 1 / 2) * Real.log |s.im| - π / 2 * |s.im|) (a := a) (b := b)
    d.gammaC fun ν _ ↦ by
      obtain ⟨C, T, h⟩ := exists_abs_log_norm_Gammaℂ_add_vertical_sub_le a b ν
      refine ⟨C, max T (|ν.im| + 1), fun s hs hT ↦
        ⟨fun h0 ↦ ?_, h s hs ((le_max_left _ _).trans hT)⟩⟩
      obtain ⟨n, hn⟩ := (Gammaℂ_eq_zero_iff _).1 h0
      exact im_add_ne_zero ((le_max_right _ _).trans hT) (by simp [hn])
  refine ⟨C₁ + C₂, max T₁ T₂, fun s hs hT ↦ ?_⟩
  obtain ⟨hne₁, hb₁⟩ := h₁ s hs ((le_max_left _ _).trans hT)
  obtain ⟨hne₂, hb₂⟩ := h₂ s hs ((le_max_right _ _).trans hT)
  rw [gammaFactor_def, norm_mul, Real.log_mul (norm_ne_zero_iff.2 hne₁) (norm_ne_zero_iff.2 hne₂)]
  rw [Multiset.sum_map_sub, Multiset.sum_map_mul_right, Multiset.map_const',
    Multiset.sum_replicate, nsmul_eq_mul] at hb₁ hb₂
  calc _ = |(Real.log ‖(d.gammaR.map fun μ ↦ Gammaℝ (s + μ)).prod‖ -
          ((d.gammaR.map fun μ ↦ (s.re + μ.re - 1) / 2).sum * Real.log |s.im| -
            d.gammaR.card * (π / 4 * |s.im|))) +
        (Real.log ‖(d.gammaC.map fun ν ↦ Gammaℂ (s + ν)).prod‖ -
          ((d.gammaC.map fun ν ↦ s.re + ν.re - 1 / 2).sum * Real.log |s.im| -
            d.gammaC.card * (π / 2 * |s.im|)))| := by
        rw [degree_def]
        push_cast
        ring_nf
    _ ≤ C₁ + C₂ := (abs_add_le _ _).trans (add_le_add hb₁ hb₂)

/-- **The gamma factor of a record on vertical strips**:
`log ‖γ(σ + i t)‖ = A(σ) log |t| - (π n / 4) |t| + O(1)` uniformly for `σ ∈ [a, b]` as
`|t| → ∞`, where `n` is the degree and
`A(σ) = ∑_j (σ + Re μ_j - 1)/2 + ∑_k (σ + Re ν_k - 1/2)`. -/
theorem isBigO_log_norm_gammaFactor_vertical_sub (d : AnalyticLFunctionData) (a b : ℝ) :
    (fun p : ℝ × ℝ ↦ Real.log ‖d.gammaFactor (p.1 + p.2 * I)‖ -
        (((d.gammaR.map fun μ ↦ (p.1 + μ.re - 1) / 2).sum +
            (d.gammaC.map fun ν ↦ p.1 + ν.re - 1 / 2).sum) * Real.log |p.2| -
          π * d.degree / 4 * |p.2|))
      =O[𝓟 (Icc a b) ×ˢ cocompact ℝ] fun _ ↦ (1 : ℝ) := by
  obtain ⟨C, T, h⟩ := d.exists_abs_log_norm_gammaFactor_vertical_sub_le a b
  refine IsBigO.of_bound C ?_
  have hT : ∀ᶠ t : ℝ in cocompact ℝ, T ≤ |t| := by
    filter_upwards [(tendsto_norm_cocompact_atTop (E := ℝ)).eventually_ge_atTop T] with t ht
    rwa [Real.norm_eq_abs] at ht
  filter_upwards [(eventually_principal.2 fun _ hσ ↦ hσ).prod_mk hT] with p hp
  rw [Real.norm_eq_abs, norm_one, mul_one]
  simpa using h (p.1 + p.2 * I) (by simpa using hp.1) (by simpa using hp.2)

end TauCeti.LFunctions.AnalyticLFunctionData
