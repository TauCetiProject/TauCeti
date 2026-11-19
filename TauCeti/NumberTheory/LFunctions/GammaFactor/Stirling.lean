/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Archimedean
public import TauCeti.NumberTheory.LFunctions.Data.Basic
import TauCeti.Analysis.Complex.Basic
import TauCeti.Analysis.SpecialFunctions.Gamma.Archimedean

/-!
# The gamma factor of an L-function record on vertical strips

Let `γ(s) = ∏_j Γ_ℝ(s + μ_j) ∏_k Γ_ℂ(s + ν_k)` be the gamma factor of an analytic L-function
record of degree `n = #μ + 2 #ν`. For every compact interval `[a, b]`,
```
log ‖γ(σ + i t)‖ = -(π n / 4) |t| + A(σ) log |t| + O(1),
A(σ) = ∑_j (σ + Re μ_j - 1) / 2 + ∑_k (σ + Re ν_k - 1/2),
```
uniformly for `σ ∈ [a, b]` as `|t| → ∞`. Each real shift contributes `-π |t| / 4` and each
complex shift `-π |t| / 2` to the exponential rate, which is why the rate is read off the degree.
This is the gamma-factor input to the growth of the completed function on vertical strips, to the
convexity bound on the edges of the critical strip, and to the main term of the zero-counting
function.

## Main declarations

* `TauCeti.LFunctions.AnalyticLFunctionData.exists_abs_log_norm_gammaFactor_vertical_sub_le`:
  one constant and one height for the whole strip `a ≤ Re s ≤ b`.
* `TauCeti.LFunctions.AnalyticLFunctionData.isBigO_log_norm_gammaFactor_vertical_sub`: the
  `O(1)` form along `𝓟 (Icc a b) ×ˢ cocompact ℝ`.

## References

* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, AMS Colloquium Publications 53, 2004,
  §5.1.
* [DLMF 5.11.9](https://dlmf.nist.gov/5.11.E9).
-/

public section

open Complex Real Filter Set Asymptotics

namespace TauCeti.LFunctions

namespace AnalyticLFunctionData

variable (d : AnalyticLFunctionData)

/-- The sum of the single-factor main terms is `A(σ) log |t| - (π n / 4) |t|`. -/
private theorem sum_vertical_main_terms (σ L T : ℝ) :
    (d.gammaR.map fun μ ↦ (σ + μ.re - 1) / 2 * L - π * T / 4).sum +
        (d.gammaC.map fun ν ↦ (σ + ν.re - 1 / 2) * L - π * T / 2).sum =
      -(π * d.degree / 4) * T +
        ((d.gammaR.map fun μ ↦ (σ + μ.re - 1) / 2).sum +
          (d.gammaC.map fun ν ↦ σ + ν.re - 1 / 2).sum) * L := by
  simp only [Multiset.sum_map_sub, Multiset.sum_map_mul_right, Multiset.map_const',
    Multiset.sum_replicate, nsmul_eq_mul, degree_def]
  push_cast
  ring

/-- **The gamma factor of a record on vertical strips**, with one constant and one height for the
whole strip `a ≤ Re s ≤ b`: there are `C` and `X` such that for `s = σ + i t` with `σ ∈ [a, b]` and
`X ≤ |t|`,
`|log ‖γ(s)‖ - (-(π n / 4) |t| + A(σ) log |t|)| ≤ C`, where `n` is the degree and
`A(σ) = ∑_j (σ + Re μ_j - 1) / 2 + ∑_k (σ + Re ν_k - 1/2)`. -/
theorem exists_abs_log_norm_gammaFactor_vertical_sub_le (a b : ℝ) :
    ∃ C X : ℝ, ∀ s : ℂ, s.re ∈ Icc a b → X ≤ |s.im| →
      |Real.log ‖d.gammaFactor s‖ -
          (-(π * d.degree / 4) * |s.im| +
            ((d.gammaR.map fun μ ↦ (s.re + μ.re - 1) / 2).sum +
              (d.gammaC.map fun ν ↦ s.re + ν.re - 1 / 2).sum) * Real.log |s.im|)| ≤ C := by
  choose CR XR hR using fun μ ↦ TauCeti.exists_abs_log_norm_Gammaℝ_add_vertical_sub_le a b μ
  choose CC XC hC using fun ν ↦ TauCeti.exists_abs_log_norm_Gammaℂ_add_vertical_sub_le a b ν
  -- One height above every single-factor height and every `|Im μ|`, so no factor vanishes.
  set XR' : ℂ → ℝ := fun μ ↦ |XR μ| + |μ.im| + 1
  set XC' : ℂ → ℝ := fun ν ↦ |XC ν| + |ν.im| + 1
  refine ⟨(d.gammaR.map CR).sum + (d.gammaC.map CC).sum,
    (d.gammaR.map XR').sum + (d.gammaC.map XC').sum, fun s hs ht ↦ ?_⟩
  have hmem {m : Multiset ℂ} {f : ℂ → ℝ} (hf : ∀ x, 0 ≤ f x) :
      0 ≤ (m.map f).sum ∧ ∀ x ∈ m, f x ≤ (m.map f).sum :=
    ⟨Multiset.sum_nonneg (by simpa using fun y _ ↦ hf y), fun x hx ↦
      Multiset.single_le_sum (by simpa using fun y _ ↦ hf y) _ (Multiset.mem_map_of_mem _ hx)⟩
  have hR' := hmem (m := d.gammaR) (f := XR') fun _ ↦ by positivity
  have hC' := hmem (m := d.gammaC) (f := XC') fun _ ↦ by positivity
  have hXR' : ∀ μ ∈ d.gammaR, |XR μ| + |μ.im| + 1 ≤ |s.im| := fun μ hμ ↦ by
    linarith [hR'.2 μ hμ, hC'.1]
  have hXC' : ∀ ν ∈ d.gammaC, |XC ν| + |ν.im| + 1 ≤ |s.im| := fun ν hν ↦ by
    linarith [hC'.2 ν hν, hR'.1]
  -- Away from the real line shifted by `-Im μ`, no factor takes the junk value `0`.
  have hRne : ∀ μ ∈ d.gammaR, Gammaℝ (s + μ) ≠ 0 := fun μ hμ ↦
    Gammaℝ_ne_zero_of_im_ne_zero <| add_im_ne_zero_of_abs_im_lt <| by
      linarith [hXR' μ hμ, abs_nonneg (XR μ)]
  have hCne : ∀ ν ∈ d.gammaC, Gammaℂ (s + ν) ≠ 0 := fun ν hν ↦
    Gammaℂ_ne_zero_of_im_ne_zero <| add_im_ne_zero_of_abs_im_lt <| by
      linarith [hXC' ν hν, abs_nonneg (XC ν)]
  -- The logarithm of the modulus is the sum over the factors.
  have hlog : Real.log ‖d.gammaFactor s‖ =
      (d.gammaR.map fun μ ↦ Real.log ‖Gammaℝ (s + μ)‖).sum +
        (d.gammaC.map fun ν ↦ Real.log ‖Gammaℂ (s + ν)‖).sum := by
    rw [gammaFactor_def, norm_mul, Multiset.norm_prod_map, Multiset.norm_prod_map,
      Real.log_mul (by simpa [Multiset.prod_eq_zero_iff] using hRne)
        (by simpa [Multiset.prod_eq_zero_iff] using hCne),
      Real.log_multiset_prod (by simpa using hRne), Real.log_multiset_prod (by simpa using hCne),
      Multiset.map_map, Multiset.map_map, Function.comp_def, Function.comp_def]
  rw [hlog, ← sum_vertical_main_terms, add_sub_add_comm, ← Multiset.sum_map_sub,
    ← Multiset.sum_map_sub]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · refine Multiset.abs_sum_le_sum_abs.trans ?_
    rw [Multiset.map_map]
    exact Multiset.sum_map_le_sum_map _ _ fun μ hμ ↦
      hR μ s hs (by linarith [hXR' μ hμ, le_abs_self (XR μ), abs_nonneg μ.im])
  · refine Multiset.abs_sum_le_sum_abs.trans ?_
    rw [Multiset.map_map]
    exact Multiset.sum_map_le_sum_map _ _ fun ν hν ↦
      hC ν s hs (by linarith [hXC' ν hν, le_abs_self (XC ν), abs_nonneg ν.im])

/-- **The gamma factor of a record on vertical strips**
([DLMF 5.11.9](https://dlmf.nist.gov/5.11.E9)):
`log ‖γ(σ + i t)‖ = -(π n / 4) |t| + A(σ) log |t| + O(1)` uniformly for `σ ∈ [a, b]` as
`|t| → ∞`, where `n` is the degree and
`A(σ) = ∑_j (σ + Re μ_j - 1) / 2 + ∑_k (σ + Re ν_k - 1/2)`. -/
theorem isBigO_log_norm_gammaFactor_vertical_sub (a b : ℝ) :
    (fun p : ℝ × ℝ ↦ Real.log ‖d.gammaFactor (p.1 + p.2 * I)‖ -
        (-(π * d.degree / 4) * |p.2| +
          ((d.gammaR.map fun μ ↦ (p.1 + μ.re - 1) / 2).sum +
            (d.gammaC.map fun ν ↦ p.1 + ν.re - 1 / 2).sum) * Real.log |p.2|))
      =O[𝓟 (Icc a b) ×ˢ cocompact ℝ] fun _ ↦ (1 : ℝ) := by
  obtain ⟨C, X, h⟩ := d.exists_abs_log_norm_gammaFactor_vertical_sub_le a b
  refine IsBigO.of_bound C ?_
  have hX : ∀ᶠ t : ℝ in cocompact ℝ, X ≤ |t| := by
    filter_upwards [(tendsto_norm_cocompact_atTop (E := ℝ)).eventually_ge_atTop X] with t ht
    rwa [Real.norm_eq_abs] at ht
  filter_upwards [(eventually_principal.2 fun _ hσ ↦ hσ).prod_mk hX] with p hp
  rw [Real.norm_eq_abs, norm_one, mul_one]
  simpa using h (p.1 + p.2 * I) (by simpa using hp.1) (by simpa using hp.2)

end AnalyticLFunctionData

end TauCeti.LFunctions
