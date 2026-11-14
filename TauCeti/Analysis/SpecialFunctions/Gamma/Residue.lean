/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.MellinInversion
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import TauCeti.Analysis.Contour.Residue.Basic
import TauCeti.Analysis.Contour.Residue.SimplePole
import TauCeti.Analysis.MellinInversion
import TauCeti.Analysis.SpecialFunctions.Gamma.Order
import TauCeti.Analysis.SpecialFunctions.Gamma.Vertical

/-!
# Residues of the complex Gamma function and shifted Mellin inversion

The complex Gamma function has simple poles at the nonpositive integers `-n` with residues
`(-1)^n / n!`, as follows from `Complex.tendsto_add_natCast_mul_Gamma` and the simple-pole limit
formula `TauCeti.Contour.residue_eq_of_tendsto_sub_mul`. Multiplying by a weight `w` analytic at
`-n` scales the residue by `w (-n)`.

Shifting the Mellin inversion contour of `Γ` from `Re s = 1` across the pole at `s = 0` into the
strip `-1 < Re s < 0` subtracts the residue `x^0 = 1` and yields the Cauchy–Saalschütz integral

`mellinInv σ Γ x = e⁻ˣ - 1`   for `-1 < σ < 0` and `x ≥ 0`.

## Main results

* `Complex.residue_Gamma_neg_nat`, `Complex.meromorphicTrailingCoeffAt_Gamma_neg_nat`:
  `residue Γ (-n) = meromorphicTrailingCoeffAt Γ (-n) = (-1)^n / n!`.
* `Complex.residue_Gamma_zero`, `Complex.meromorphicTrailingCoeffAt_Gamma_zero`:
  `residue Γ 0 = meromorphicTrailingCoeffAt Γ 0 = 1`.
* `Complex.residue_Gamma_mul_neg_nat`: `residue (fun s ↦ Γ(s) w(s)) (-n) = ((-1)^n / n!) w(-n)`
  for `w` analytic at `-n`.
* `Complex.residue_Gamma_mul_zero`: `residue (fun s ↦ Γ(s) w(s)) 0 = w(0)` for `w` analytic at `0`.
* `Complex.mellinInv_Gamma_of_mem_Ioo`: `mellinInv σ Γ x = e⁻ˣ - 1` for `-1 < σ < 0` and `x ≥ 0`.

## References

* E. C. Titchmarsh, *The Theory of Functions*, §4.41 and §9.5.
* H. Iwaniec, E. Kowalski, *Analytic Number Theory*, §5.1 and §5.9.
-/

public section

open Real Set Filter
open scoped Topology
open Complex hiding exp continuous_exp

namespace Complex

/-- The residue of `Complex.Gamma` at the nonpositive integer `-n` is `(-1)^n / n!`. -/
-- Deliberately not `@[simp]`: `simp` rewrites the LHS to `meromorphicTrailingCoeffAt Gamma (-n)`
-- via `residue_eq_meromorphicTrailingCoeffAt_of_order_eq_neg_one` and
-- `meromorphicOrderAt_Gamma_neg_nat`, then closes via `meromorphicTrailingCoeffAt_Gamma_neg_nat`.
theorem residue_Gamma_neg_nat (n : ℕ) :
    TauCeti.Contour.residue Gamma (-(n : ℂ)) = (-1) ^ n / (n.factorial : ℂ) := by
  have hm : MeromorphicAt Gamma (-(n : ℂ)) :=
    meromorphicAt_of_meromorphicOrderAt_ne_zero (by rw [meromorphicOrderAt_Gamma_neg_nat]; decide)
  refine TauCeti.Contour.residue_eq_of_tendsto_sub_mul hm ?_
  simpa only [sub_neg_eq_add] using tendsto_add_natCast_mul_Gamma n

/-- The leading Laurent coefficient of `Complex.Gamma` at `-n` is `(-1)^n / n!`. -/
@[simp]
theorem meromorphicTrailingCoeffAt_Gamma_neg_nat (n : ℕ) :
    meromorphicTrailingCoeffAt Gamma (-(n : ℂ)) = (-1) ^ n / (n.factorial : ℂ) := by
  rw [← TauCeti.Contour.residue_eq_meromorphicTrailingCoeffAt_of_order_eq_neg_one
    (meromorphicOrderAt_Gamma_neg_nat n), residue_Gamma_neg_nat]

/-- The residue of `Complex.Gamma` at `0` is `1`. -/
@[simp]
theorem residue_Gamma_zero : TauCeti.Contour.residue Gamma 0 = 1 := by
  simpa using residue_Gamma_neg_nat 0

/-- The leading Laurent coefficient of `Complex.Gamma` at `0` is `1`. -/
@[simp]
theorem meromorphicTrailingCoeffAt_Gamma_zero : meromorphicTrailingCoeffAt Gamma 0 = 1 := by
  simpa using meromorphicTrailingCoeffAt_Gamma_neg_nat 0

/-- Multiplying `Complex.Gamma` by a function `w` analytic at `-n` scales the residue at `-n` by
`w (-n)`. -/
theorem residue_Gamma_mul_neg_nat (n : ℕ) {w : ℂ → ℂ} (hw : AnalyticAt ℂ w (-(n : ℂ))) :
    TauCeti.Contour.residue (fun s ↦ Gamma s * w s) (-(n : ℂ)) =
      (-1) ^ n / (n.factorial : ℂ) * w (-(n : ℂ)) := by
  have hm : MeromorphicAt (fun s ↦ Gamma s * w s) (-(n : ℂ)) :=
    (meromorphicAt_of_meromorphicOrderAt_ne_zero
      (by rw [meromorphicOrderAt_Gamma_neg_nat]; decide)).mul hw.meromorphicAt
  refine TauCeti.Contour.residue_eq_of_tendsto_sub_mul hm ?_
  have hlim := (tendsto_add_natCast_mul_Gamma n).mul
    (hw.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  refine hlim.congr fun s ↦ ?_
  ring

/-- Multiplying `Complex.Gamma` by a function `w` analytic at `0` gives residue `w 0` at `0`. -/
theorem residue_Gamma_mul_zero {w : ℂ → ℂ} (hw : AnalyticAt ℂ w 0) :
    TauCeti.Contour.residue (fun s ↦ Gamma s * w s) 0 = w 0 := by
  simpa using residue_Gamma_mul_neg_nat 0 (by simpa using hw)

/-- **Cauchy–Saalschütz Mellin formula for `Γ`.** Shifting the Mellin inversion contour of
`Complex.Gamma` from `Re s = 1` into the strip `-1 < σ < 0` crosses the simple pole at `s = 0` with
residue `1`, giving `mellinInv σ Γ x = e⁻ˣ - 1` for `x ≥ 0`. -/
theorem mellinInv_Gamma_of_mem_Ioo {σ : ℝ} (hσ₀ : -1 < σ) (hσ₁ : σ < 0) {x : ℝ} (hx : 0 ≤ x) :
    mellinInv σ Gamma x = Real.exp (-x) - 1 := by
  rcases hx.eq_or_lt with rfl | hx
  · simp
  obtain ⟨C, _, hC⟩ := exists_norm_Gamma_le_div_pow_of_re_mem_Icc σ 1 1
  have hshift := mellinInv_eq_mellinInv_add_sum_residue_of_norm_le
    (f := Gamma) (S := {0}) (σ₀ := σ) (σ₁ := 1) (B := fun T ↦ C / T)
    (by linarith) hx.le
    (fun z hz hz0 ↦ analyticAt_Gamma fun n hn ↦ by
      rcases n with _ | n
      · exact (Finset.mem_singleton.mpr (by simpa using hn) |> hz0).elim
      · have hre := congrArg re hn
        simp only [neg_re, natCast_re] at hre
        push_cast at hre
        linarith [hz.1, n.cast_nonneg' (α := ℝ)])
    (fun s hs ↦ by
      rw [Finset.mem_singleton.mp hs]
      exact meromorphicAt_of_meromorphicOrderAt_ne_zero
        (by simpa using (by decide : (-1 : WithTop ℤ) ≠ 0) ∘
          (meromorphicOrderAt_Gamma_neg_nat 0).symm.trans))
    (fun s hs ↦ by rw [Finset.mem_singleton.mp hs]; simp [hσ₁])
    (verticalIntegrable_Gamma fun n hn ↦ by
      rcases n with _ | n
      · push_cast at hn; linarith
      · push_cast at hn; linarith [n.cast_nonneg' (α := ℝ)])
    (verticalIntegrable_Gamma fun n hn ↦ by linarith [n.cast_nonneg' (α := ℝ)])
    (tendsto_const_nhds.div_atTop tendsto_id)
    (by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT u hu
      have hT0 : 0 ≤ T := zero_le_one.trans hT
      refine ⟨?_, ?_⟩
      · simpa [abs_of_nonneg hT0] using
          hC ((u : ℂ) + T * I) (by simpa using hu) (by simpa [abs_of_nonneg hT0] using hT)
      · simpa [abs_of_nonneg hT0] using
          hC ((u : ℂ) - T * I) (by simpa using hu) (by simpa [abs_of_nonneg hT0] using hT))
  have hres : TauCeti.Contour.residue (fun z ↦ (x : ℂ) ^ (-z) * Gamma z) 0 = 1 := by
    have hcomm : (fun z ↦ (x : ℂ) ^ (-z) * Gamma z) = fun z ↦ Gamma z * (x : ℂ) ^ (-z) :=
      funext fun z ↦ mul_comm _ _
    rw [hcomm, residue_Gamma_mul_zero
      (analyticAt_const.cpow (by fun_prop) (ofReal_mem_slitPlane.mpr hx))]
    simp
  rw [mellinInv_Gamma one_pos hx, Finset.sum_singleton, hres] at hshift
  linear_combination -hshift

end Complex
