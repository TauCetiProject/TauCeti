/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Convolution
public import TauCeti.Analysis.BoundedVariation.Slicing.Excess
import TauCeti.Analysis.BoundedVariation.Convolution
import TauCeti.Analysis.Calculus.BumpFunction.Convolution
import TauCeti.Analysis.Distribution.TestFunction.Convolution
import TauCeti.Analysis.Sobolev.WeakDeriv.Divergence
import TauCeti.Analysis.SpecialFunctions.Sqrt
import TauCeti.MeasureTheory.Integral.Bochner.CauchySchwarz

/-!
# Mollified slicing excess inequality

When a finite-volume Lebesgue-measurable set `s` has finite perimeter, testing the localized
joint slicing inequality
(`TauCeti.two_mul_setLIntegral_add_two_mul_setLIntegral_add_ofReal_integral_le_perimeter`)
against mollified regularized gradient vector fields for a radial smooth bump `ρ` on `(ℝ ∙ e)ᗮ`
and applying Cauchy–Schwarz yields the mollified slicing excess bound
(`MeasureTheory.NullMeasurableSet.mul_integral_sqrt_sq_add_norm_fderiv_sq_add_two_mul_sq_le`):
writing `D = {y ∈ H | 0 < |s_y|}`, `v(y) = |s_y|`, `d = ρ ⋆ (2 · 1_D)`, `w = ρ ⋆ v`,
`a = ρ ⋆ 1_A`, and `M = 2 |D| + |Dv|`,

`M ∫ √(d² + ‖Dw‖²) + 2 (∫ a √d)² ≤ M P(s)`.

## References

* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, §3.2 and §3.11, for one-dimensional variation and slicing.
* F. Cagnetti, M. Colombo, G. De Philippis, F. Maggi, *Rigidity of equality cases in Steiner's
  perimeter inequality*, Anal. PDE **7** (2014), §1.2, for the interval-section condition.
-/

public section

open ContinuousLinearMap Filter InnerProductSpace MeasureTheory Metric Set TestFunction
  TopologicalSpace
open scoped Convolution Distributions ENNReal Pointwise RealInnerProductSpace Topology

namespace MeasureTheory.NullMeasurableSet

open TauCeti

section MollifiedExcess

noncomputable section

/-- Smoothness of the regularized gradient-density integrand `√(d² + ‖Dw‖² + δ²)`. -/
private theorem contDiff_sqrt_sq_add_norm_fderiv_sq_add_sq
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    {d w : H → ℝ} (hd : ContDiff ℝ (⊤ : ℕ∞) d) (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    {δ : ℝ} (hδ : 0 < δ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : H ↦ √(d y ^ 2 + ‖fderiv ℝ w y‖ ^ 2 + δ ^ 2)) := by
  let gradW : H → H := fun y ↦ (InnerProductSpace.toDual ℝ H).symm (fderiv ℝ w y)
  have hgradW_smooth : ContDiff ℝ (⊤ : ℕ∞) gradW :=
    (InnerProductSpace.toDual ℝ H).symm.toContinuousLinearMap.contDiff.comp
      (hw.fderiv_right (by simp))
  have hinner : ContDiff ℝ (⊤ : ℕ∞) fun y : H ↦ d y ^ 2 + ⟪gradW y, gradW y⟫_ℝ + δ ^ 2 :=
    ((hd.pow 2).add (hgradW_smooth.inner ℝ hgradW_smooth)).add contDiff_const
  have hrad : (fun y : H ↦ d y ^ 2 + ‖fderiv ℝ w y‖ ^ 2 + δ ^ 2) =
      fun y : H ↦ d y ^ 2 + ⟪gradW y, gradW y⟫_ℝ + δ ^ 2 :=
    funext fun y ↦ by rw [real_inner_self_eq_norm_sq, LinearIsometryEquiv.norm_map]
  rw [contDiff_iff_contDiffAt]
  exact fun y ↦ (Real.contDiffAt_sqrt (by positivity)).comp y (hrad ▸ hinner.contDiffAt)

/-- Normalized component bound `x / √(x² + y² + δ²) ∈ [0, 1]` for `0 ≤ x` and `0 < δ`. -/
private theorem left_div_sqrt_sq_add_sq_add_sq_mem_Icc {x y δ : ℝ} (hx : 0 ≤ x) (hδ : 0 < δ) :
    x / √(x ^ 2 + y ^ 2 + δ ^ 2) ∈ Icc (0 : ℝ) 1 :=
  ⟨div_nonneg hx (Real.sqrt_nonneg _), (div_le_one (Real.sqrt_pos.2 (by positivity))).2
    (Real.le_sqrt_of_sq_le (by linarith [sq_nonneg y, sq_nonneg δ]))⟩

/-- Bounded-test pairing for the regularized slicing estimate against a compactly supported
cutoff `η` on `(ℝ ∙ e)ᗮ`. -/
private theorem integral_cutoff_mul_div_sqrt_add_two_mul_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {s : Set E} (hs : NullMeasurableSet s volume) (hfin : volume s ≠ ∞)
    (hP : perimeter volume ⊤ s ≠ ∞) (e : E) (he : ‖e‖ = 1)
    {A : Set (ℝ ∙ e)ᗮ} (hA : NullMeasurableSet A volume)
    (hbad : ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume, y ∈ A →
      ∀ I : Set ℝ, I.OrdConnected → ¬{t : ℝ | (y : E) + t • e ∈ s} =ᵐ[volume] I)
    (ρ η : ContDiffBump (0 : (ℝ ∙ e)ᗮ)) {δ : ℝ} (hδ : 0 < δ)
    (hD : NullMeasurableSet {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}} volume)
    (hD_ind_int : Integrable
      ({y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}}.indicator (fun _ ↦ (2 : ℝ)))
      volume)
    (hA_ind_int : Integrable (A.indicator (fun _ ↦ (1 : ℝ))) volume)
    (hv_int : Integrable (fun y : (ℝ ∙ e)ᗮ ↦ volume.real {t : ℝ | (y : E) + t • e ∈ s}) volume)
    {d w a : (ℝ ∙ e)ᗮ → ℝ}
    (hd_eq : d = ρ.normed volume ⋆[lsmul ℝ ℝ, volume]
      {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}}.indicator (fun _ ↦ (2 : ℝ)))
    (hw_eq : w = ρ.normed volume ⋆[lsmul ℝ ℝ, volume]
      (fun y : (ℝ ∙ e)ᗮ ↦ volume.real {t : ℝ | (y : E) + t • e ∈ s}))
    (ha_eq : a = ρ.normed volume ⋆[lsmul ℝ ℝ, volume] A.indicator (fun _ ↦ (1 : ℝ)))
    (hd_smooth : ContDiff ℝ (⊤ : ℕ∞) d) (hw_smooth : ContDiff ℝ (⊤ : ℕ∞) w)
    (hd_int : Integrable d volume) (hd_mem : ∀ y, d y ∈ Icc (0 : ℝ) 2)
    (hgradW_int : Integrable (fun y : (ℝ ∙ e)ᗮ ↦ ‖fderiv ℝ w y‖) volume) :
    let g : (ℝ ∙ e)ᗮ → ℝ := fun y ↦ √(d y ^ 2 + ‖fderiv ℝ w y‖ ^ 2 + δ ^ 2)
    (∫ y : (ℝ ∙ e)ᗮ, η y * (d y ^ 2 + ‖fderiv ℝ w y‖ ^ 2) / g y) +
        2 * (∫ y : (ℝ ∙ e)ᗮ, a y * (d y / g y)) ≤
      (perimeter volume ⊤ s).toReal := by
  intro g
  let H := (ℝ ∙ e)ᗮ
  let D : Set H := {y : H | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}}
  let v : H → ℝ := fun y ↦ volume.real {t : ℝ | (y : E) + t • e ∈ s}
  let κ : H → ℝ := ρ.normed volume
  let gradW : H → H := fun y ↦ (InnerProductSpace.toDual ℝ H).symm (fderiv ℝ w y)
  have hgradW_smooth : ContDiff ℝ (⊤ : ℕ∞) gradW :=
    (InnerProductSpace.toDual ℝ H).symm.toContinuousLinearMap.contDiff.comp
      (hw_smooth.fderiv_right (by simp))
  have hgradW_cont : Continuous (fun y : H ↦ ‖fderiv ℝ w y‖) :=
    ((hw_smooth.of_le (by simp)).continuous_fderiv one_ne_zero).norm
  have hgradW_norm (y : H) : ‖gradW y‖ = ‖fderiv ℝ w y‖ := LinearIsometryEquiv.norm_map _ _
  have hg_pos (y : H) : 0 < g y := Real.sqrt_pos.2 (by positivity)
  have hg_smooth : ContDiff ℝ (⊤ : ℕ∞) g :=
    contDiff_sqrt_sq_add_norm_fderiv_sq_add_sq hd_smooth hw_smooth hδ
  have hdg_mem (y : H) : d y / g y ∈ Icc (0 : ℝ) 1 :=
    left_div_sqrt_sq_add_sq_add_sq_mem_Icc (hd_mem y).1 hδ
  let ψ₀ : H → ℝ := fun y ↦ η y * (d y / g y)
  let φ₀_fun : H → H := fun y ↦ (-(η y * (g y)⁻¹)) • gradW y
  let φ₀ : 𝓓(⊤, H) := ⟨φ₀_fun,
    ((η.contDiff.mul (hg_smooth.inv fun y ↦ (hg_pos y).ne')).neg).smul hgradW_smooth,
    (η.hasCompactSupport.mul_right.neg).smul_right, subset_univ _⟩
  have hφ₀_apply (y : H) : φ₀ y = (-(η y * (g y)⁻¹)) • gradW y := by
    simp only [φ₀, φ₀_fun, TestFunction.coe_mk]
  let φ : 𝓓(⊤, H) := TestFunction.mollify φ₀ volume ρ (subset_univ _)
  let ψ : H → ℝ := κ ⋆[lsmul ℝ ℝ, volume] ψ₀
  let α : H → ℝ := κ ⋆[lsmul ℝ ℝ, volume] (fun y ↦ d y / g y)
  have hdg_cont : Continuous (fun y : H ↦ d y / g y) :=
    hd_smooth.continuous.div hg_smooth.continuous fun y ↦ (hg_pos y).ne'
  have hψ₀_cont : Continuous ψ₀ := η.continuous.mul hdg_cont
  have hψ₀_mem (y : H) : ψ₀ y ∈ Icc (0 : ℝ) 1 :=
    ⟨mul_nonneg η.nonneg (hdg_mem y).1,
      (mul_le_mul η.le_one (hdg_mem y).2 (hdg_mem y).1 zero_le_one).trans_eq (one_mul 1)⟩
  have hsq_α (y : H) : (d y / g y) ^ 2 + ‖φ₀ y‖ ^ 2 ≤ 1 := by
    have hnorm : ‖φ₀ y‖ = η y * ‖fderiv ℝ w y‖ / g y := by
      rw [hφ₀_apply, norm_smul, norm_neg,
        Real.norm_of_nonneg (mul_nonneg η.nonneg (inv_nonneg.2 (hg_pos y).le)), hgradW_norm,
        div_eq_mul_inv]
      ring
    rw [hnorm, div_pow, div_pow, mul_pow, ← add_div, div_le_one (sq_pos_of_pos (hg_pos y)),
      Real.sq_sqrt (by positivity)]
    have hη1 : η y ^ 2 ≤ 1 := by nlinarith [η.nonneg (x := y), η.le_one (x := y)]
    nlinarith [sq_nonneg ‖fderiv ℝ w y‖, sq_nonneg δ]
  have hsq_ψ (y : H) : ψ₀ y ^ 2 + ‖φ₀ y‖ ^ 2 ≤ 1 := by
    have hψle : ψ₀ y ^ 2 ≤ (d y / g y) ^ 2 := by
      rw [mul_pow]
      exact mul_le_of_le_one_left (sq_nonneg _)
        (by nlinarith [η.nonneg (x := y), η.le_one (x := y)])
    exact (add_le_add hψle le_rfl).trans (hsq_α y)
  have hφ_le (y : H) : ‖φ y‖ ≤ 1 := by
    rw [TestFunction.mollify_apply]
    exact ρ.norm_normed_convolution_le (fun z ↦ by
      nlinarith [hsq_α z, sq_nonneg (d z / g z), norm_nonneg (φ₀ z)]) y
  have hpair_D : ∫ y : H, D.indicator (fun _ ↦ (2 : ℝ)) y * ψ y =
      ∫ y : H, η y * d y ^ 2 / g y := by
    rw [ρ.integral_mul_normed_convolution_eq_of_bdd hD_ind_int hψ₀_cont.aestronglyMeasurable
      (C := 1) fun y ↦ by rw [Real.norm_of_nonneg (hψ₀_mem y).1]; exact (hψ₀_mem y).2]
    refine integral_congr_ae (.of_forall fun y ↦ ?_)
    dsimp only [ψ₀]
    rw [← hd_eq]
    ring
  have hpair_A : ∫ y : H, A.indicator (fun _ ↦ (1 : ℝ)) y * α y =
      ∫ y : H, a y * (d y / g y) := by
    rw [ha_eq]
    exact ρ.integral_mul_normed_convolution_eq_of_bdd hA_ind_int hdg_cont.aestronglyMeasurable
      (C := 1) fun y ↦ by rw [Real.norm_of_nonneg (hdg_mem y).1]; exact (hdg_mem y).2
  have hpair_div : ∫ y : H, divergenceCLM φ y * v y =
      ∫ y : H, η y * ‖fderiv ℝ w y‖ ^ 2 / g y := by
    obtain ⟨C, hC⟩ := (divergenceCLM φ₀).continuous.bounded_above_of_compact_support
      (divergenceCLM φ₀).hasCompactSupport
    have h1 : ∫ y : H, divergenceCLM φ y * v y =
        ∫ y : H, v y * (κ ⋆[lsmul ℝ ℝ, volume] (divergenceCLM φ₀ : H → ℝ)) y :=
      integral_congr_ae (.of_forall fun y ↦ by
        dsimp only; rw [mul_comm, divergenceCLM_mollify])
    have h2 : ∀ y : H, w y * (divergenceCLM φ₀) y = (divergenceCLM φ₀) y • w y := fun y ↦ by
      rw [mul_comm, smul_eq_mul]
    rw [h1, ρ.integral_mul_normed_convolution_eq_of_bdd hv_int
      (divergenceCLM φ₀).continuous.aestronglyMeasurable hC, ← hw_eq,
      integral_congr_ae (.of_forall h2),
      ((hw_smooth.of_le (by simp)).contDiffOn.hasWeakFDerivOn_fderiv
        (μ := volume) (Ω := ⊤)).integral_divergenceCLM_smul_eq_neg_integral φ₀,
      ← integral_neg]
    refine integral_congr_ae (.of_forall fun y ↦ ?_)
    dsimp only
    rw [(InnerProductSpace.toDual_symm_apply (y := fderiv ℝ w y) (x := φ₀ y)).symm, hφ₀_apply]
    dsimp only [gradW]
    rw [inner_smul_right, real_inner_self_eq_norm_sq, LinearIsometryEquiv.norm_map,
      div_eq_mul_inv]
    ring
  have htermD : ENNReal.ofReal (∫ y : H, D.indicator (fun _ ↦ (2 : ℝ)) y * ψ y) ≤
      2 * ∫⁻ y in D, ENNReal.ofReal √(1 - ‖φ y‖ ^ 2) := by
    simpa only [ENNReal.ofReal_ofNat, φ, ψ, TestFunction.mollify_apply] using
      ρ.ofReal_integral_indicator_mul_convolution_le φ₀.continuous hD zero_le_two hD_ind_int
        hψ₀_cont hψ₀_mem hsq_ψ
  have htermA : ENNReal.ofReal (2 * ∫ y : H, A.indicator (fun _ ↦ (1 : ℝ)) y * α y) ≤
      2 * ∫⁻ y in A, ENNReal.ofReal √(1 - ‖φ y‖ ^ 2) := by
    rw [ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat]
    refine mul_le_mul_right ?_ 2
    simpa only [ENNReal.ofReal_one, one_mul, φ, α, TestFunction.mollify_apply] using
      ρ.ofReal_integral_indicator_mul_convolution_le φ₀.continuous hA zero_le_one hA_ind_int
        hdg_cont hdg_mem hsq_α
  have hI1 : Integrable (fun y : H ↦ η y * d y ^ 2 / g y) volume :=
    hd_int.mono' (((η.continuous.mul (hd_smooth.continuous.pow 2)).div
      hg_smooth.continuous fun y ↦ (hg_pos y).ne').aestronglyMeasurable) (.of_forall fun y ↦ by
        have hfac : η y * d y ^ 2 / g y = ψ₀ y * d y := by dsimp only [ψ₀]; ring
        rw [Real.norm_of_nonneg (div_nonneg (mul_nonneg η.nonneg (sq_nonneg _)) (hg_pos y).le),
          hfac]
        exact mul_le_of_le_one_left (hd_mem y).1 (hψ₀_mem y).2)
  have hI2 : Integrable (fun y : H ↦ η y * ‖fderiv ℝ w y‖ ^ 2 / g y) volume :=
    hgradW_int.mono' (((η.continuous.mul (hgradW_cont.pow 2)).div
      hg_smooth.continuous fun y ↦ (hg_pos y).ne').aestronglyMeasurable) (.of_forall fun y ↦ by
        have hfac : η y * ‖fderiv ℝ w y‖ ^ 2 / g y =
            (η y * (‖fderiv ℝ w y‖ / g y)) * ‖fderiv ℝ w y‖ := by ring
        rw [Real.norm_of_nonneg (div_nonneg (mul_nonneg η.nonneg (sq_nonneg _)) (hg_pos y).le),
          hfac]
        have hle1 : ‖fderiv ℝ w y‖ / g y ≤ 1 := by
          simpa only [add_comm (‖fderiv ℝ w y‖ ^ 2)] using
            (left_div_sqrt_sq_add_sq_add_sq_mem_Icc (x := ‖fderiv ℝ w y‖) (y := d y)
              (opNorm_nonneg _) hδ).2
        exact mul_le_of_le_one_left (opNorm_nonneg _)
          ((mul_le_mul η.le_one hle1 (div_nonneg (opNorm_nonneg _) (hg_pos y).le)
            zero_le_one).trans_eq (one_mul 1)))
  have hsplit : (∫ y : H, η y * (d y ^ 2 + ‖fderiv ℝ w y‖ ^ 2) / g y) =
      (∫ y : H, η y * d y ^ 2 / g y) + ∫ y : H, η y * ‖fderiv ℝ w y‖ ^ 2 / g y := by
    rw [← integral_add hI1 hI2]
    exact integral_congr_ae (.of_forall fun _ ↦ by ring)
  rw [hsplit]
  refine (ENNReal.ofReal_le_iff_le_toReal hP).1 ?_
  rw [add_right_comm]
  exact (ENNReal.ofReal_add_le.trans (add_le_add ENNReal.ofReal_add_le le_rfl)).trans <| by
    rw [← hpair_D, ← hpair_A, ← hpair_div]
    exact (add_le_add (add_le_add htermD htermA) le_rfl).trans
      (two_mul_setLIntegral_add_two_mul_setLIntegral_add_ofReal_integral_le_perimeter
        hs hfin e he hA hbad φ hφ_le)

/-- **Mollified slicing excess inequality.** Let `s` be a Lebesgue-measurable set of finite volume
and finite perimeter, `e` a unit vector with orthogonal hyperplane `H = (ℝ ∙ e)ᗮ`, `A ⊆ H` a
null-measurable family of noninterval line sections of `s`, and `ρ` a radial smooth bump on `H`.
Writing `D = {y ∈ H | 0 < |s_y|}`, `v(y) = |s_y|`, `d = ρ ⋆ (2 · 1_D)`, `w = ρ ⋆ v`,
`a = ρ ⋆ 1_A`, and `M = 2 |D| + |Dv|`, we have

`M ∫ √(d² + ‖Dw‖²) + 2 (∫ a √d)² ≤ M P(s)`. -/
theorem mul_integral_sqrt_sq_add_norm_fderiv_sq_add_two_mul_sq_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {s : Set E} (hs : NullMeasurableSet s volume) (hfin : volume s ≠ ∞)
    (hP : perimeter volume ⊤ s ≠ ∞) (e : E) (he : ‖e‖ = 1)
    {A : Set (ℝ ∙ e)ᗮ} (hA : NullMeasurableSet A volume)
    (hbad : ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume, y ∈ A →
      ∀ I : Set ℝ, I.OrdConnected → ¬{t : ℝ | (y : E) + t • e ∈ s} =ᵐ[volume] I)
    (ρ : ContDiffBump (0 : (ℝ ∙ e)ᗮ)) :
    (2 * volume.real {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}} +
        (totalVariationOn volume ⊤
          (fun y : (ℝ ∙ e)ᗮ ↦ volume.real {t : ℝ | (y : E) + t • e ∈ s})).toReal) *
      (∫ y : (ℝ ∙ e)ᗮ,
        √((ρ.normed volume ⋆[lsmul ℝ ℝ, volume]
            {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}}.indicator
              (fun _ ↦ (2 : ℝ))) y ^ 2 +
          ‖fderiv ℝ (ρ.normed volume ⋆[lsmul ℝ ℝ, volume]
            (fun y : (ℝ ∙ e)ᗮ ↦ volume.real {t : ℝ | (y : E) + t • e ∈ s})) y‖ ^ 2)) +
      2 * (∫ y : (ℝ ∙ e)ᗮ,
        (ρ.normed volume ⋆[lsmul ℝ ℝ, volume] A.indicator (fun _ ↦ (1 : ℝ))) y *
          √((ρ.normed volume ⋆[lsmul ℝ ℝ, volume]
            {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}}.indicator
              (fun _ ↦ (2 : ℝ))) y)) ^ 2 ≤
    (2 * volume.real {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}} +
        (totalVariationOn volume ⊤
          (fun y : (ℝ ∙ e)ᗮ ↦ volume.real {t : ℝ | (y : E) + t • e ∈ s})).toReal) *
      (perimeter volume ⊤ s).toReal := by
  let H := (ℝ ∙ e)ᗮ
  let D : Set H := {y : H | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}}
  let v : H → ℝ := fun y ↦ volume.real {t : ℝ | (y : E) + t • e ∈ s}
  let κ : H → ℝ := ρ.normed volume
  let d : H → ℝ := κ ⋆[lsmul ℝ ℝ, volume] D.indicator (fun _ ↦ (2 : ℝ))
  let w : H → ℝ := κ ⋆[lsmul ℝ ℝ, volume] v
  let a : H → ℝ := κ ⋆[lsmul ℝ ℝ, volume] A.indicator (fun _ ↦ (1 : ℝ))
  let M : ℝ := 2 * volume.real D + (totalVariationOn volume ⊤ v).toReal
  have hD : NullMeasurableSet D volume :=
    nullMeasurableSet_lt aemeasurable_const (aemeasurable_volume_lineSection e he hs)
  have hDfin : volume D ≠ ∞ := hs.volume_setOf_pos_volume_lineSection_ne_top hfin hP e he
  have hAfin : volume A ≠ ∞ := hs.volume_ne_top_of_noninterval_lineSection hfin hP e he hA hbad
  have hv_tv_fin : totalVariationOn volume ⊤ v ≠ ∞ :=
    ne_top_of_le_ne_top hP (totalVariationOn_measureReal_lineSection_le hs hfin e he)
  have hv_int : Integrable v volume := hs.integrable_measureReal_lineSection hfin e he
  have hD_ind_int : Integrable (D.indicator (fun _ ↦ (2 : ℝ))) volume :=
    (integrableOn_const hDfin).integrable_indicator₀ hD
  have hA_ind_int : Integrable (A.indicator (fun _ ↦ (1 : ℝ))) volume :=
    (integrableOn_const hAfin).integrable_indicator₀ hA
  have hcsmooth {f : H → ℝ} (hf : Integrable f volume) :
      ContDiff ℝ (⊤ : ℕ∞) (κ ⋆[lsmul ℝ ℝ, volume] f) :=
    ρ.hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ) ρ.contDiff_normed
      hf.locallyIntegrable
  have hd_smooth : ContDiff ℝ (⊤ : ℕ∞) d := hcsmooth hD_ind_int
  have hw_smooth : ContDiff ℝ (⊤ : ℕ∞) w := hcsmooth hv_int
  have ha_smooth : ContDiff ℝ (⊤ : ℕ∞) a := hcsmooth hA_ind_int
  have hd_int : Integrable d volume := ρ.integrable_normed.integrable_convolution _ hD_ind_int
  have ha_int : Integrable a volume := ρ.integrable_normed.integrable_convolution _ hA_ind_int
  have hd_mem (y : H) : d y ∈ Icc (0 : ℝ) 2 :=
    ρ.normed_convolution_indicator_mem_Icc zero_le_two hD_ind_int.locallyIntegrable y
  have ha_mem (y : H) : a y ∈ Icc (0 : ℝ) 1 :=
    ρ.normed_convolution_indicator_mem_Icc zero_le_one hA_ind_int.locallyIntegrable y
  have hd_int_eq : ∫ y : H, d y = 2 * volume.real D := by
    rw [integral_convolution (lsmul ℝ ℝ) ρ.integrable_normed hD_ind_int, lsmul_apply,
      ρ.integral_normed, one_smul, integral_indicator₀ hD, setIntegral_const, smul_eq_mul, mul_comm]
  have ha_int_eq : ∫ y : H, a y = volume.real A := by
    rw [integral_convolution (lsmul ℝ ℝ) ρ.integrable_normed hA_ind_int, lsmul_apply,
      ρ.integral_normed, one_smul, integral_indicator₀ hA, setIntegral_const, smul_eq_mul, mul_one]
  have hw1 : ContDiff ℝ 1 w := hw_smooth.of_le (by simp)
  have hgradW_cont : Continuous (fun y : H ↦ ‖fderiv ℝ w y‖) :=
    (hw1.continuous_fderiv one_ne_zero).norm
  have hgradW_int : Integrable (fun y : H ↦ ‖fderiv ℝ w y‖) volume :=
    ρ.integrable_norm_fderiv_normed_convolution hv_int.locallyIntegrable hv_tv_fin
  have hgradW_int_le : ∫ y : H, ‖fderiv ℝ w y‖ ≤ (totalVariationOn volume ⊤ v).toReal :=
    ρ.integral_norm_fderiv_normed_convolution_le hv_int.locallyIntegrable hv_tv_fin
  -- For any fixed `δ > 0`, prove the regularized estimate before letting `δ → 0⁺`.
  have hdelta {δ : ℝ} (hδ : 0 < δ) :
      let g : H → ℝ := fun y ↦ √(d y ^ 2 + ‖fderiv ℝ w y‖ ^ 2 + δ ^ 2)
      let Mδ : ℝ := M + δ * volume.real A
      Mδ * (∫ y : H, (d y ^ 2 + ‖fderiv ℝ w y‖ ^ 2) / g y) + 2 * (∫ y : H, a y * √(d y)) ^ 2 ≤
        Mδ * (perimeter volume ⊤ s).toReal := by
    intro g Mδ
    have hg_pos (y : H) : 0 < g y := Real.sqrt_pos.2 (by positivity)
    have hg_smooth : ContDiff ℝ (⊤ : ℕ∞) g :=
      contDiff_sqrt_sq_add_norm_fderiv_sq_add_sq hd_smooth hw_smooth hδ
    -- Exhaust `H` with bumps `ηseq m ↑ 1` by dominated convergence.
    let ηseq : ℕ → ContDiffBump (0 : H) := fun m ↦
      ⟨(m : ℝ) + 1, (m : ℝ) + 2, by positivity, by linarith⟩
    have hη_lim : Tendsto (fun m ↦ ∫ y : H, ηseq m y * (d y ^ 2 + ‖fderiv ℝ w y‖ ^ 2) / g y)
        atTop (𝓝 (∫ y : H, (d y ^ 2 + ‖fderiv ℝ w y‖ ^ 2) / g y)) := by
      refine tendsto_integral_of_dominated_convergence (fun y ↦ d y + ‖fderiv ℝ w y‖)
        (fun m ↦ (((ηseq m).continuous.mul ((hd_smooth.continuous.pow 2).add
          (hgradW_cont.pow 2))).div hg_smooth.continuous
          fun y ↦ (hg_pos y).ne').aestronglyMeasurable)
        (hd_int.add hgradW_int) (fun m ↦ .of_forall fun y ↦ ?_) (.of_forall fun y ↦ ?_)
      · have hq0 : 0 ≤ (d y ^ 2 + ‖fderiv ℝ w y‖ ^ 2) / g y :=
          div_nonneg (by positivity) (hg_pos y).le
        rw [mul_div_assoc, Real.norm_of_nonneg (mul_nonneg (ηseq m).nonneg hq0)]
        refine (mul_le_of_le_one_left hq0 (ηseq m).le_one).trans ?_
        simpa only [abs_of_nonneg (hd_mem y).1, abs_of_nonneg (opNorm_nonneg _)] using
          Real.div_sqrt_sq_add_sq_add_le (d y) ‖fderiv ℝ w y‖ (sq_nonneg δ)
      · refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop (Nat.ceil ‖y‖)] with m hm
        have hball : y ∈ closedBall (0 : H) (ηseq m).rIn := by
          rw [mem_closedBall_zero_iff]
          have h1 : ‖y‖ ≤ (m : ℝ) := (Nat.le_ceil ‖y‖).trans (Nat.cast_le.2 hm)
          dsimp only [ηseq]; linarith
        rw [(ηseq m).one_of_mem_closedBall hball, one_mul]
    have heta (m : ℕ) :
        (∫ y : H, ηseq m y * (d y ^ 2 + ‖fderiv ℝ w y‖ ^ 2) / g y) +
          2 * (∫ y : H, a y * (d y / g y)) ≤ (perimeter volume ⊤ s).toReal :=
      integral_cutoff_mul_div_sqrt_add_two_mul_le hs hfin hP e he hA hbad ρ (ηseq m) hδ hD
        hD_ind_int hA_ind_int hv_int rfl rfl rfl hd_smooth hw_smooth hd_int hd_mem hgradW_int
    have hfull : (∫ y : H, (d y ^ 2 + ‖fderiv ℝ w y‖ ^ 2) / g y) +
        2 * (∫ y : H, a y * (d y / g y)) ≤ (perimeter volume ⊤ s).toReal :=
      le_of_tendsto (hη_lim.add tendsto_const_nhds) (.of_forall heta)
    have hle_M : (∫ y : H, d y) + (∫ y : H, ‖fderiv ℝ w y‖) + δ * ∫ y : H, a y ≤ Mδ := by
      rw [hd_int_eq, ha_int_eq]; dsimp only [Mδ, M]; linarith
    have hadg_int : Integrable (fun y : H ↦ a y * (d y / g y)) volume :=
      ha_int.mul_bdd (c := 1) (hd_smooth.continuous.div hg_smooth.continuous
        fun y ↦ (hg_pos y).ne').aestronglyMeasurable
        (.of_forall fun y ↦ by
          have hm := left_div_sqrt_sq_add_sq_add_sq_mem_Icc (y := ‖fderiv ℝ w y‖) (hd_mem y).1 hδ
          rw [Real.norm_of_nonneg hm.1]; exact hm.2)
    have hdg_int : Integrable (fun y : H ↦ d y + ‖fderiv ℝ w y‖) volume := hd_int.add hgradW_int
    have hag_pt (y : H) : a y * g y ≤ d y + ‖fderiv ℝ w y‖ + δ * a y := by
      have hg_le : g y ≤ d y + ‖fderiv ℝ w y‖ + δ := by
        simpa only [abs_of_nonneg (hd_mem y).1, abs_of_nonneg (opNorm_nonneg _), abs_of_pos hδ]
          using Real.sqrt_sq_add_sq_add_sq_le (d y) ‖fderiv ℝ w y‖ δ
      nlinarith [mul_le_mul_of_nonneg_left hg_le (ha_mem y).1, (ha_mem y).2, (hd_mem y).1,
        opNorm_nonneg (fderiv ℝ w y)]
    have hag_int : Integrable (fun y : H ↦ a y * g y) volume :=
      (hdg_int.add (ha_int.const_mul δ)).mono'
        (ha_smooth.continuous.mul hg_smooth.continuous).aestronglyMeasurable
        (.of_forall fun y ↦ by
          rw [Real.norm_of_nonneg (mul_nonneg (ha_mem y).1 (hg_pos y).le)]; exact hag_pt y)
    have hag_le : ∫ y : H, a y * g y ≤ Mδ := by
      calc ∫ y : H, a y * g y
          ≤ ∫ y : H, (d y + ‖fderiv ℝ w y‖ + δ * a y) :=
            integral_mono hag_int (hdg_int.add (ha_int.const_mul δ)) hag_pt
        _ = (∫ y : H, d y) + (∫ y : H, ‖fderiv ℝ w y‖) + δ * ∫ y : H, a y := by
            rw [integral_add hdg_int (ha_int.const_mul δ), integral_add hd_int hgradW_int,
              integral_const_mul]
        _ ≤ Mδ := hle_M
    have hcs := TauCeti.sq_integral_mul_sqrt_le_integral_mul_div_mul
      (.of_forall fun y ↦ (ha_mem y).1) (.of_forall fun y ↦ (hd_mem y).1)
      (.of_forall hg_pos) hadg_int hag_int
    have hcs' : (∫ y : H, a y * √(d y)) ^ 2 ≤ (∫ y : H, a y * (d y / g y)) * Mδ :=
      hcs.trans (mul_le_mul_of_nonneg_left hag_le (integral_nonneg fun y ↦
        mul_nonneg (ha_mem y).1
          (left_div_sqrt_sq_add_sq_add_sq_mem_Icc (y := ‖fderiv ℝ w y‖) (hd_mem y).1 hδ).1))
    have hMδ_nonneg : 0 ≤ Mδ := by dsimp [Mδ, M]; positivity
    nlinarith [mul_le_mul_of_nonneg_left hfull hMδ_nonneg]
  -- Pass to `δ = 1 / (k + 1) → 0⁺` by dominated convergence.
  let δseq : ℕ → ℝ := fun k ↦ 1 / ((k : ℝ) + 1)
  have hδpos (k : ℕ) : 0 < δseq k := by positivity
  have hδlim : Tendsto δseq atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hM_lim : Tendsto (fun k ↦ M + δseq k * volume.real A) atTop (𝓝 M) := by
    simpa only [zero_mul, add_zero] using (hδlim.mul_const (volume.real A)).const_add M
  have hint_lim : Tendsto
      (fun k ↦ ∫ y : H, (d y ^ 2 + ‖fderiv ℝ w y‖ ^ 2) /
        √(d y ^ 2 + ‖fderiv ℝ w y‖ ^ 2 + δseq k ^ 2))
      atTop (𝓝 (∫ y : H, √(d y ^ 2 + ‖fderiv ℝ w y‖ ^ 2))) := by
    refine tendsto_integral_of_dominated_convergence (fun y ↦ d y + ‖fderiv ℝ w y‖)
      (fun k ↦ (((hd_smooth.continuous.pow 2).add (hgradW_cont.pow 2)).div
        (Real.continuous_sqrt.comp (((hd_smooth.continuous.pow 2).add (hgradW_cont.pow 2)).add
          continuous_const)) fun y ↦ (Real.sqrt_pos.2 (add_pos_of_nonneg_of_pos
            (add_nonneg (sq_nonneg _) (sq_nonneg _))
            (sq_pos_of_pos (hδpos k)))).ne').aestronglyMeasurable)
      (hd_int.add hgradW_int)
      (fun k ↦ .of_forall fun y ↦ by
        rw [Real.norm_of_nonneg (by positivity)]
        simpa only [abs_of_nonneg (hd_mem y).1, abs_of_nonneg (opNorm_nonneg _)] using
          Real.div_sqrt_sq_add_sq_add_le (d y) ‖fderiv ℝ w y‖ (sq_nonneg (δseq k)))
      (.of_forall fun y ↦ ?_)
    set x : ℝ := d y ^ 2 + ‖fderiv ℝ w y‖ ^ 2
    have hx_nonneg : 0 ≤ x := by positivity
    rcases eq_or_lt_of_le hx_nonneg with hx0 | hxpos
    · simp [← hx0]
    · have hden : Tendsto (fun k ↦ √(x + δseq k ^ 2)) atTop (𝓝 √x) :=
        (Real.continuous_sqrt.tendsto x).comp <| by
          simpa only [zero_pow two_ne_zero, add_zero] using (hδlim.pow 2).const_add x
      have hq := (tendsto_const_nhds (x := x)).div hden (Real.sqrt_pos.2 hxpos).ne'
      rwa [Real.div_sqrt] at hq
  exact le_of_tendsto_of_tendsto ((hM_lim.mul hint_lim).add tendsto_const_nhds)
    (hM_lim.mul_const (perimeter volume ⊤ s).toReal) (.of_forall fun k ↦ hdelta (hδpos k))

end

end MollifiedExcess

end MeasureTheory.NullMeasurableSet
