/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Hölder's inequality for a function supported in a set

Let `w` vanish almost everywhere off a set `A` of finite measure. For exponents `r, s > 0` with
`1/r + 1/s ≤ 1`, Hölder's inequality with the three exponents `r`, `s` and
`(1 - 1/r - 1/s)⁻¹`, the last applied to the indicator of `A`, gives

`‖∫ f • w‖ ≤ ‖f‖_{Lʳ} ‖w‖_{Lˢ} μ(A) ^ (1 - 1/r - 1/s)`.

The factor `μ(A) ^ (1 - 1/r - 1/s)` is what makes the inequality useful when `A` is small. In
Stampacchia's and De Giorgi's methods, `w` is a truncation `(u - k)⁺`, `A` is the superlevel set
`{u > k}`, and the power of its measure is the source of the superlinear gain that drives the
iteration.

The same three-exponent argument on a finite measure space, with `A` the whole space, bounds
`∫⁻ ‖f‖ₑ ‖g‖ₑ` for `1/p + 1/q = 1/r` and `1 ≤ r`.

## Main declarations

* `TauCeti.MeasureTheory.norm_integral_smul_le_eLpNorm_mul_eLpNorm_mul_measureReal_rpow`: the
  inequality.
* `TauCeti.MeasureTheory.lintegral_enorm_mul_enorm_le_eLpNorm_mul_eLpNorm_mul_rpow_measure_univ`:
  `∫⁻ ‖f‖ₑ ‖g‖ₑ ≤ ‖f‖_{Lᵖ} ‖g‖_{L^q} μ(univ) ^ (1 - 1/r)` for a Hölder triple `(p, q, r)`.
-/

public section

noncomputable section

open MeasureTheory Set

open scoped ENNReal NNReal

namespace TauCeti

namespace MeasureTheory

variable {Ω 𝕜 E : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [NormedRing 𝕜]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MulActionWithZero 𝕜 E] [IsBoundedSMul 𝕜 E]

/-- **Hölder's inequality for a function vanishing off a set.** Let `0 < r`, `0 < s` with
`1/r + 1/s ≤ 1`, let `f ∈ Lʳ` and `w ∈ Lˢ`, and suppose that `w` vanishes almost everywhere off a
set `A` of finite measure. Then

`‖∫ f • w‖ ≤ ‖f‖_{Lʳ} ‖w‖_{Lˢ} μ(A) ^ (1 - 1/r - 1/s)`. -/
theorem norm_integral_smul_le_eLpNorm_mul_eLpNorm_mul_measureReal_rpow {f : Ω → 𝕜} {w : Ω → E}
    {r s : ℝ≥0} (hr : 0 < r) (hs : 0 < s) (hrs : (r : ℝ)⁻¹ + (s : ℝ)⁻¹ ≤ 1)
    (hf : MemLp f r μ) (hw : MemLp w s μ) {A : Set Ω} (hAfin : μ A ≠ ∞)
    (hwA : ∀ᵐ x ∂μ, x ∉ A → w x = 0) :
    ‖∫ x, f x • w x ∂μ‖ ≤
      (eLpNorm f r μ).toReal * (eLpNorm w s μ).toReal *
        μ.real A ^ (1 - (r : ℝ)⁻¹ - (s : ℝ)⁻¹) := by
  -- The exponent `p` of the product `f • w`, with `1/p = 1/r + 1/s ≤ 1`.
  set p : ℝ≥0∞ := ((r : ℝ≥0∞)⁻¹ + (s : ℝ≥0∞)⁻¹)⁻¹
  have : ENNReal.HolderTriple r s p := .of _ _
  have hp : 1 / p.toReal = (r : ℝ)⁻¹ + (s : ℝ)⁻¹ := by
    simp [p, ENNReal.toReal_add, hr.ne', hs.ne']
  have hp1 : 1 ≤ p := by
    rw [ENNReal.one_le_inv, ← ENNReal.coe_inv hr.ne', ← ENNReal.coe_inv hs.ne']
    exact_mod_cast hrs
  -- Integrate over `A`, and pass from `L¹(A)` to `Lᵖ(A)` at the cost of a power of `μ(A)`.
  have key : ‖∫ x, f x • w x ∂μ‖ₑ ≤
      eLpNorm f r μ * eLpNorm w s μ * μ A ^ (1 - (r : ℝ)⁻¹ - (s : ℝ)⁻¹) := calc
    ‖∫ x, f x • w x ∂μ‖ₑ = ‖∫ x in A, f x • w x ∂μ‖ₑ := by
      rw [setIntegral_eq_integral_of_ae_compl_eq_zero (hwA.mono fun x hx hxA => by
        simp [hx hxA])]
    _ ≤ eLpNorm (f • w) 1 (μ.restrict A) :=
      (eNorm_integral_le_lintegral_eNorm _).trans lintegral_eNorm_le_eLpNorm_one
    _ ≤ eLpNorm (f • w) p (μ.restrict A) * μ A ^ (1 - (r : ℝ)⁻¹ - (s : ℝ)⁻¹) := by
      refine (eLpNorm_le_eLpNorm_mul_rpow_measure_univ_of_pos hp1 one_pos).trans_eq ?_
      rw [Measure.restrict_apply_univ, hp]
      norm_num [sub_sub]
    _ ≤ _ := by
      gcongr
      refine (eLpNorm_smul_le_mul_eLpNorm_of_pos (p := r) (q := s)
        (zero_lt_one.trans_le hp1)).trans ?_
      gcongr <;> exact Measure.restrict_le_self
  have hfin : eLpNorm f r μ * eLpNorm w s μ * μ A ^ (1 - (r : ℝ)⁻¹ - (s : ℝ)⁻¹) ≠ ∞ := by
    have : 0 ≤ 1 - (r : ℝ)⁻¹ - (s : ℝ)⁻¹ := by linarith
    finiteness [hf.eLpNorm_ne_top, hw.eLpNorm_ne_top, hAfin]
  simpa [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← measureReal_def] using
    ENNReal.toReal_mono hfin key

omit [NormedSpace ℝ E] in
/-- **Hölder's inequality for the lower integral of a product.** For a Hölder triple
`1/p + 1/q = 1/r` with `1 ≤ r`,

`∫⁻ ‖f‖ₑ ‖g‖ₑ ≤ ‖f‖_{Lᵖ} ‖g‖_{L^q} μ(univ) ^ (1 - 1/r)`.

The factor `μ(univ) ^ (1 - 1/r)` compares the `L¹` and `Lʳ` seminorms of the product. -/
theorem lintegral_enorm_mul_enorm_le_eLpNorm_mul_eLpNorm_mul_rpow_measure_univ {F : Type*}
    [NormedAddCommGroup F] {p q r : ℝ≥0∞} [ENNReal.HolderTriple p q r] (hr : 1 ≤ r) {f : Ω → E}
    {g : Ω → F} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    ∫⁻ x, ‖f x‖ₑ * ‖g x‖ₑ ∂μ ≤
      eLpNorm f p μ * eLpNorm g q μ * μ univ ^ (1 - 1 / r.toReal) := by
  have hm : AEStronglyMeasurable (fun x => ‖f x‖ * ‖g x‖) μ := hf.norm.mul hg.norm
  have hH := eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm (μ := μ) (p := p) (q := q) (r := r)
    (fun (a : E) (b : F) => ‖a‖ * ‖b‖) (1 : ℝ≥0)
    ((continuous_norm.comp continuous_fst).mul (continuous_norm.comp continuous_snd)) hf hg
    (Filter.Eventually.of_forall fun x => by simp)
  simp only [ENNReal.coe_one, one_mul] at hH
  calc ∫⁻ x, ‖f x‖ₑ * ‖g x‖ₑ ∂μ = eLpNorm (fun x => ‖f x‖ * ‖g x‖) 1 μ := by
        rw [eLpNorm_one_eq_lintegral_eNorm hm]
        refine lintegral_congr fun x => ?_
        simp
    _ ≤ eLpNorm (fun x => ‖f x‖ * ‖g x‖) r μ * μ univ ^ (1 - 1 / r.toReal) := by
        simpa using eLpNorm_le_eLpNorm_mul_rpow_measure_univ hr hm
    _ ≤ _ := by gcongr

end MeasureTheory

end TauCeti
