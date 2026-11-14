/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude, The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import TauCeti.Analysis.SpecialFunctions.Complex.Arg

/-!
# Integrability and slit-plane holomorphy of Mellin inversion integrals

Mathlib's `mellinInv σ f y` is `(1 / 2π) ∫ y^{-(σ + i t)} • f(σ + i t) dt`. For positive real `y`
the kernel `t ↦ y^{-(σ + i t)}` has constant norm `y^{-σ}`, so integrability of `f` along the
vertical line `Re s = σ` implies integrability of the Mellin inversion integrand.

When the vertical profile `g y = f(σ + i y)` satisfies an exponential decay bound
`‖g y‖ ≤ C (1 + |y|) ^ R e^{-π |y|}` — the decay produced by Stirling's formula for balanced ratios
of Gamma factors in Mellin–Barnes integrals — the principal power `w ^ (±(σ + i y))` extends the
integral from `(0, ∞)` to the whole cut plane `Complex.slitPlane`: at each `w₀ ∈ slitPlane` we have
`|arg w₀| < π`, so `‖w ^ (±(σ + i y))‖ = O(e^{(π - δ) |y|})` locally near `w₀` for some `δ > 0`,
leaving exponential margin `e^{-δ |y|}` for both integrability and differentiation under the
integral sign.

## Main results

* `Complex.VerticalIntegrable.integrable_cpow_smul`: the integrand of the Mellin inversion
  integral of a vertically integrable function is integrable for `y > 0`.
* `TauCeti.integrable_one_add_abs_rpow_mul_exp_neg_mul_abs`: `y ↦ (1 + |y|) ^ R e^{-c |y|}` is
  integrable on `ℝ` for every `c > 0` and every `R : ℝ`.
* `TauCeti.integrable_cpow_smul_of_norm_le_exp_neg_pi_mul_abs`,
  `TauCeti.integrable_cpow_neg_smul_of_norm_le_exp_neg_pi_mul_abs`: integrability on `ℝ` of
  `y ↦ w ^ (±(σ + i y)) • g y` on `Complex.slitPlane` when `‖g y‖ = O((1 + |y|) ^ R e^{-π |y|})`.
* `TauCeti.hasDerivAt_integral_cpow_smul_slitPlane`: differentiation under the integral sign on
  `Complex.slitPlane`.
* `TauCeti.differentiableOn_integral_cpow_smul_slitPlane`,
  `TauCeti.analyticOnNhd_integral_cpow_smul_slitPlane`,
  `TauCeti.differentiableOn_integral_cpow_neg_smul_slitPlane`,
  `TauCeti.analyticOnNhd_integral_cpow_neg_smul_slitPlane`: complex differentiability and holomorphy
  on `Complex.slitPlane`.
-/

public section

open Real Set MeasureTheory Filter Topology
open Complex hiding exp continuous_exp

namespace Complex

/-- If `f` is integrable on the vertical line `Re s = σ`, then so is the integrand
`t ↦ y^{-(σ + i t)} • f(σ + i t)` of the Mellin inversion integral `mellinInv σ f y`, for
`y > 0`. -/
theorem VerticalIntegrable.integrable_cpow_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f : ℂ → E} {σ : ℝ} (hf : VerticalIntegrable f σ) {y : ℝ} (hy : 0 < y) :
    Integrable fun t : ℝ ↦ (y : ℂ) ^ (-(σ + t * I)) • f (σ + t * I) := by
  -- `t ↦ y^{-(σ + i t)}` is continuous of constant norm `y^{-σ}`
  refine hf.bdd_smul (y ^ (-σ)) ?_ (Eventually.of_forall fun t ↦ ?_)
  · exact (Continuous.const_cpow (by fun_prop)
      (Or.inl (ofReal_ne_zero.mpr hy.ne'))).aestronglyMeasurable
  · rw [norm_cpow_eq_rpow_re_of_pos hy]
    simp

end Complex

namespace TauCeti

/-- Any polynomial-times-exponential weight `y ↦ (1 + |y|) ^ R * exp (-c * |y|)` with `c > 0` and
arbitrary real exponent `R` is integrable on the whole real line. -/
theorem integrable_one_add_abs_rpow_mul_exp_neg_mul_abs {c : ℝ} (hc : 0 < c) (R : ℝ) :
    Integrable fun y : ℝ ↦ (1 + |y|) ^ R * Real.exp (-c * |y|) := by
  have hexp_int : Integrable fun y : ℝ ↦ Real.exp (-(c / 2) * |y|) := by
    rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
    refine IntegrableOn.union ?_ ?_
    · refine (integrableOn_exp_mul_Iic (half_pos hc) 0).congr_fun (fun y hy ↦ ?_) measurableSet_Iic
      rw [abs_of_nonpos hy]
      ring_nf
    · refine (integrableOn_exp_mul_Ioi (neg_lt_zero.2 (half_pos hc)) 0).congr_fun
        (fun y hy ↦ ?_) measurableSet_Ioi
      rw [abs_of_pos hy]
  set M : ℝ := max R 0
  have hM0 : 0 ≤ M := le_max_right R 0
  set δ : ℝ := c / (2 * (M + 1))
  have hδ : 0 < δ := by positivity
  set A : ℝ := max 1 δ⁻¹
  have hA1 : 1 ≤ A := le_max_left _ _
  have hA0 : 0 < A := zero_lt_one.trans_le hA1
  have hcont : Continuous fun y : ℝ ↦ (1 + |y|) ^ R * Real.exp (-c * |y|) := by
    refine Continuous.mul ?_ (by fun_prop)
    exact Continuous.rpow_const (by fun_prop) fun y ↦
      Or.inl (show (0 : ℝ) < 1 + |y| by linarith [abs_nonneg y]).ne'
  refine (hexp_int.const_mul (A ^ M)).mono' hcont.aestronglyMeasurable
    (Eventually.of_forall fun y ↦ ?_)
  have h1y : 1 ≤ 1 + |y| := by linarith [abs_nonneg y]
  have hbase : 1 + |y| ≤ A * Real.exp (δ * |y|) := by
    have hlin : 1 + |y| ≤ A * (1 + δ * |y|) := by
      have h1 : |y| = δ⁻¹ * (δ * |y|) := by field_simp
      have h2 : δ⁻¹ * (δ * |y|) ≤ A * (δ * |y|) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
      linarith
    exact hlin.trans (mul_le_mul_of_nonneg_left
      (by linarith [Real.add_one_le_exp (δ * |y|)]) hA0.le)
  have hrpow : (1 + |y|) ^ R ≤ A ^ M * Real.exp (M * δ * |y|) := by
    calc (1 + |y|) ^ R ≤ (1 + |y|) ^ M := Real.rpow_le_rpow_of_exponent_le h1y (le_max_left _ _)
      _ ≤ (A * Real.exp (δ * |y|)) ^ M := Real.rpow_le_rpow (by positivity) hbase hM0
      _ = A ^ M * (Real.exp (δ * |y|)) ^ M := Real.mul_rpow hA0.le (Real.exp_nonneg _)
      _ = A ^ M * Real.exp (M * δ * |y|) := by
          rw [← Real.exp_mul]
          ring_nf
  have hMδ : M * δ ≤ c / 2 := by
    dsimp [δ]
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) two_pos]
    nlinarith
  rw [Real.norm_of_nonneg (by positivity)]
  calc (1 + |y|) ^ R * Real.exp (-c * |y|)
      ≤ A ^ M * Real.exp (M * δ * |y|) * Real.exp (-c * |y|) :=
        mul_le_mul_of_nonneg_right hrpow (Real.exp_nonneg _)
    _ = A ^ M * Real.exp ((M * δ - c) * |y|) := by
        rw [mul_assoc, ← Real.exp_add]
        ring_nf
    _ ≤ A ^ M * Real.exp (-(c / 2) * |y|) := by
        gcongr
        nlinarith [abs_nonneg y]

/-- Near any `w₀ ∈ slitPlane`, the modulus `‖w‖` stays bounded away from `0` and `∞` while
`|arg w|` stays strictly below `π - δ` for a positive margin `δ`. -/
private theorem exists_mem_nhds_slitPlane_norm_and_arg_bounds {w₀ : ℂ} (hw₀ : w₀ ∈ slitPlane) :
    ∃ δ > 0, ∃ r₀ > 0, ∃ r₁ > 0, ∃ U ∈ 𝓝 w₀, U ⊆ slitPlane ∧
      ∀ w ∈ U, r₀ < ‖w‖ ∧ ‖w‖ < r₁ ∧ |w.arg| < π - δ := by
  have hw₀_pos : 0 < ‖w₀‖ := norm_pos_iff.2 (slitPlane_ne_zero hw₀)
  have harg : |w₀.arg| < π := Complex.abs_arg_lt_pi_of_mem_slitPlane hw₀
  set δ : ℝ := (π - |w₀.arg|) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  set r₀ : ℝ := ‖w₀‖ / 2
  set r₁ : ℝ := 2 * ‖w₀‖
  have hU_nhds : ∀ᶠ w in 𝓝 w₀, w ∈ slitPlane ∧ r₀ < ‖w‖ ∧ ‖w‖ < r₁ ∧ |w.arg| < π - δ := by
    filter_upwards [isOpen_slitPlane.mem_nhds hw₀,
      (continuous_norm.tendsto w₀).eventually
        (Ioo_mem_nhds (show r₀ < ‖w₀‖ by dsimp [r₀]; linarith)
          (show ‖w₀‖ < r₁ by dsimp [r₁]; linarith)),
      (continuous_abs.continuousAt.comp (Complex.continuousAt_arg hw₀)).eventually
        (Iio_mem_nhds (show |w₀.arg| < π - δ by dsimp [δ]; linarith))] with _ h1 h2 h3
    exact ⟨h1, h2.1, h2.2, h3⟩
  exact ⟨δ, hδ, r₀, by positivity, r₁, by positivity,
    {w | w ∈ slitPlane ∧ r₀ < ‖w‖ ∧ ‖w‖ < r₁ ∧ |w.arg| < π - δ}, hU_nhds,
    fun _ hw ↦ hw.1, fun _ hw ↦ hw.2⟩

/-- Pointwise bound on `‖w ^ (ρ + i y)‖` when `r₀ < ‖w‖ < r₁` and `|arg w| < π - δ`. -/
private theorem norm_cpow_add_mul_I_le {w : ℂ} {r₀ r₁ δ : ℝ} (hr₀ : 0 < r₀)
    (hw_lo : r₀ < ‖w‖) (hw_hi : ‖w‖ < r₁) (hw_arg : |w.arg| < π - δ) (ρ y : ℝ) :
    ‖w ^ ((ρ : ℂ) + y * I)‖ ≤ max (r₀ ^ ρ) (r₁ ^ ρ) * Real.exp ((π - δ) * |y|) := by
  have hw_rad : ‖w‖ ^ ρ ≤ max (r₀ ^ ρ) (r₁ ^ ρ) := by
    rcases le_or_gt 0 ρ with hρ | hρ
    · exact (Real.rpow_le_rpow (norm_nonneg w) hw_hi.le hρ).trans (le_max_right _ _)
    · exact (Real.rpow_le_rpow_of_nonpos hr₀ hw_lo.le hρ.le).trans (le_max_left _ _)
  have hw_ang : (Real.exp (w.arg * y))⁻¹ ≤ Real.exp ((π - δ) * |y|) := by
    rw [← Real.exp_neg]
    refine Real.exp_le_exp.2 ?_
    calc -(w.arg * y) ≤ |w.arg * y| := neg_le_abs _
      _ = |w.arg| * |y| := abs_mul _ _
      _ ≤ (π - δ) * |y| := mul_le_mul_of_nonneg_right hw_arg.le (abs_nonneg y)
  have hre : ((ρ : ℂ) + y * I).re = ρ := by simp
  have him : ((ρ : ℂ) + y * I).im = y := by simp
  have hM : 0 ≤ max (r₀ ^ ρ) (r₁ ^ ρ) := (lt_of_lt_of_le (by positivity) (le_max_left _ _)).le
  calc ‖w ^ ((ρ : ℂ) + y * I)‖
      ≤ ‖w‖ ^ ((ρ : ℂ) + y * I).re / Real.exp (w.arg * ((ρ : ℂ) + y * I).im) :=
        Complex.norm_cpow_le _ _
    _ = ‖w‖ ^ ρ * (Real.exp (w.arg * y))⁻¹ := by rw [hre, him, div_eq_mul_inv]
    _ ≤ max (r₀ ^ ρ) (r₁ ^ ρ) * Real.exp ((π - δ) * |y|) :=
        mul_le_mul hw_rad hw_ang (by positivity) hM

/-- If `g : ℝ → E` is strongly measurable and satisfies `‖g y‖ ≤ C (1 + |y|) ^ R e^{-π |y|}`, then
`y ↦ w ^ (σ + i y) • g y` is integrable on `ℝ` for every `σ : ℝ` and `w ∈ Complex.slitPlane`. -/
theorem integrable_cpow_smul_of_norm_le_exp_neg_pi_mul_abs {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {g : ℝ → E} (hg_meas : AEStronglyMeasurable g)
    (hg_bound : ∃ C R : ℝ, ∀ y : ℝ, ‖g y‖ ≤ C * (1 + |y|) ^ R * Real.exp (-π * |y|))
    (σ : ℝ) {w : ℂ} (hw : w ∈ slitPlane) :
    Integrable fun y : ℝ ↦ w ^ ((σ : ℂ) + y * I) • g y := by
  obtain ⟨C, R, hg⟩ := hg_bound
  set C' : ℝ := max C 0
  obtain ⟨δ, hδ, r₀, hr₀, r₁, _, U, hU, _, hU_bounds⟩ :=
    exists_mem_nhds_slitPlane_norm_and_arg_bounds hw
  obtain ⟨hw_lo, hw_hi, hw_arg⟩ := hU_bounds w (mem_of_mem_nhds hU)
  set M : ℝ := max (r₀ ^ σ) (r₁ ^ σ)
  have : 0 < M := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  have hcpow_cont : Continuous fun y : ℝ ↦ w ^ ((σ : ℂ) + y * I) :=
    Continuous.const_cpow (by fun_prop) (Or.inl (slitPlane_ne_zero hw))
  refine ((integrable_one_add_abs_rpow_mul_exp_neg_mul_abs hδ R).const_mul (M * C')).mono'
    (hcpow_cont.aestronglyMeasurable.smul hg_meas) (Eventually.of_forall fun y ↦ ?_)
  have hg' : ‖g y‖ ≤ C' * (1 + |y|) ^ R * Real.exp (-π * |y|) :=
    (hg y).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left C 0) (by positivity)) (Real.exp_nonneg _))
  rw [norm_smul]
  calc ‖w ^ ((σ : ℂ) + y * I)‖ * ‖g y‖
      ≤ (M * Real.exp ((π - δ) * |y|)) * (C' * (1 + |y|) ^ R * Real.exp (-π * |y|)) :=
        mul_le_mul (norm_cpow_add_mul_I_le hr₀ hw_lo hw_hi hw_arg σ y) hg'
          (norm_nonneg _) (by positivity)
    _ = M * C' * (1 + |y|) ^ R * (Real.exp ((π - δ) * |y|) * Real.exp (-π * |y|)) := by ring
    _ = M * C' * ((1 + |y|) ^ R * Real.exp (-δ * |y|)) := by
        rw [← Real.exp_add]
        ring_nf

/-- Negated-exponent companion to `TauCeti.integrable_cpow_smul_of_norm_le_exp_neg_pi_mul_abs`:
`y ↦ w ^ (-(σ + i y)) • g y` is integrable on `ℝ` for every `w ∈ Complex.slitPlane`. -/
theorem integrable_cpow_neg_smul_of_norm_le_exp_neg_pi_mul_abs {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {g : ℝ → E} (hg_meas : AEStronglyMeasurable g)
    (hg_bound : ∃ C R : ℝ, ∀ y : ℝ, ‖g y‖ ≤ C * (1 + |y|) ^ R * Real.exp (-π * |y|))
    (σ : ℝ) {w : ℂ} (hw : w ∈ slitPlane) :
    Integrable fun y : ℝ ↦ w ^ (-((σ : ℂ) + y * I)) • g y := by
  obtain ⟨C, R, hg⟩ := hg_bound
  have hmp := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving
  have h := integrable_cpow_smul_of_norm_le_exp_neg_pi_mul_abs
    (hg_meas.comp_quasiMeasurePreserving hmp)
    ⟨C, R, fun y ↦ by simpa [abs_neg] using hg (-y)⟩ (-σ) hw
  refine (h.comp_neg).congr (Eventually.of_forall fun y ↦ ?_)
  dsimp only [Function.comp_def]
  rw [neg_neg, ofReal_neg, ofReal_neg]
  congr 2
  ring

/-- **Differentiation under a Mellin–Barnes integral on the slit plane.** If `g : ℝ → E` is
strongly measurable and satisfies `‖g y‖ ≤ C (1 + |y|) ^ R e^{-π |y|}`, then
`w ↦ ∫ y : ℝ, w ^ (σ + i y) • g y` has complex derivative
`∫ y : ℝ, ((σ + i y) * w₀ ^ (σ + i y - 1)) • g y` at every `w₀ ∈ Complex.slitPlane`. -/
theorem hasDerivAt_integral_cpow_smul_slitPlane {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {g : ℝ → E} (hg_meas : AEStronglyMeasurable g)
    (hg_bound : ∃ C R : ℝ, ∀ y : ℝ, ‖g y‖ ≤ C * (1 + |y|) ^ R * Real.exp (-π * |y|))
    (σ : ℝ) {w₀ : ℂ} (hw₀ : w₀ ∈ slitPlane) :
    HasDerivAt (fun w : ℂ ↦ ∫ y : ℝ, w ^ ((σ : ℂ) + y * I) • g y)
      (∫ y : ℝ, (((σ : ℂ) + y * I) * w₀ ^ ((σ : ℂ) + y * I - 1)) • g y) w₀ := by
  obtain ⟨C, R, hg⟩ := hg_bound
  set C' : ℝ := max C 0
  obtain ⟨δ, hδ, r₀, hr₀, r₁, _, U, hU, hU_slit, hU_bounds⟩ :=
    exists_mem_nhds_slitPlane_norm_and_arg_bounds hw₀
  set M₁ : ℝ := max (r₀ ^ (σ - 1)) (r₁ ^ (σ - 1))
  have : 0 < M₁ := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  set S : ℝ := max |σ| 1
  have : 0 < S := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hF_meas : ∀ᶠ w in 𝓝 w₀, AEStronglyMeasurable (fun y : ℝ ↦ w ^ ((σ : ℂ) + y * I) • g y) := by
    filter_upwards [hU] with w hw
    exact (Continuous.const_cpow (by fun_prop)
      (Or.inl (slitPlane_ne_zero (hU_slit hw)))).aestronglyMeasurable.smul hg_meas
  have hF'_meas : AEStronglyMeasurable
      (fun y : ℝ ↦ (((σ : ℂ) + y * I) * w₀ ^ ((σ : ℂ) + y * I - 1)) • g y) := by
    have hcont : Continuous fun y : ℝ ↦ ((σ : ℂ) + y * I) * w₀ ^ ((σ : ℂ) + y * I - 1) :=
      Continuous.mul (by fun_prop)
        (Continuous.const_cpow (by fun_prop) (Or.inl (slitPlane_ne_zero hw₀)))
    exact hcont.aestronglyMeasurable.smul hg_meas
  have hbound_int : Integrable fun y : ℝ ↦
      S * M₁ * C' * ((1 + |y|) ^ (R + 1) * Real.exp (-δ * |y|)) :=
    (integrable_one_add_abs_rpow_mul_exp_neg_mul_abs hδ (R + 1)).const_mul (S * M₁ * C')
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun (w : ℂ) (y : ℝ) ↦ w ^ ((σ : ℂ) + y * I) • g y)
    (F' := fun (w : ℂ) (y : ℝ) ↦ (((σ : ℂ) + y * I) * w ^ ((σ : ℂ) + y * I - 1)) • g y)
    (bound := fun y : ℝ ↦ S * M₁ * C' * ((1 + |y|) ^ (R + 1) * Real.exp (-δ * |y|)))
    hU hF_meas (integrable_cpow_smul_of_norm_le_exp_neg_pi_mul_abs hg_meas ⟨C, R, hg⟩ σ hw₀)
    hF'_meas ?_ hbound_int ?_).2
  · refine Eventually.of_forall fun y w hw ↦ ?_
    obtain ⟨hw_lo, hw_hi, hw_arg⟩ := hU_bounds w hw
    have hs_norm : ‖(σ : ℂ) + y * I‖ ≤ S * (1 + |y|) := by
      calc ‖(σ : ℂ) + y * I‖ ≤ ‖(σ : ℂ)‖ + ‖(y : ℂ) * I‖ := norm_add_le _ _
        _ = |σ| + |y| := by simp
        _ ≤ S * 1 + S * |y| := add_le_add ((le_max_left |σ| 1).trans_eq (mul_one S).symm)
            (le_mul_of_one_le_left (abs_nonneg y) (le_max_right |σ| 1))
        _ = S * (1 + |y|) := by ring
    have hw_pow : ‖w ^ ((σ : ℂ) + y * I - 1)‖ ≤ M₁ * Real.exp ((π - δ) * |y|) := by
      have heq : (σ : ℂ) + y * I - 1 = ((σ - 1 : ℝ) : ℂ) + y * I := by push_cast; ring
      rw [heq]
      exact norm_cpow_add_mul_I_le hr₀ hw_lo hw_hi hw_arg (σ - 1) y
    have hg' : ‖g y‖ ≤ C' * (1 + |y|) ^ R * Real.exp (-π * |y|) :=
      (hg y).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left C 0) (by positivity)) (Real.exp_nonneg _))
    have h1y : 0 < 1 + |y| := by linarith [abs_nonneg y]
    rw [norm_smul, norm_mul]
    calc ‖(σ : ℂ) + y * I‖ * ‖w ^ ((σ : ℂ) + y * I - 1)‖ * ‖g y‖
        ≤ (S * (1 + |y|)) * (M₁ * Real.exp ((π - δ) * |y|)) *
            (C' * (1 + |y|) ^ R * Real.exp (-π * |y|)) := by
          refine mul_le_mul (mul_le_mul hs_norm hw_pow (norm_nonneg _) (by positivity)) hg'
            (norm_nonneg _) (by positivity)
      _ = S * M₁ * C' * ((1 + |y|) ^ R * (1 + |y|)) *
            (Real.exp ((π - δ) * |y|) * Real.exp (-π * |y|)) := by ring
      _ = S * M₁ * C' * ((1 + |y|) ^ (R + 1) * Real.exp (-δ * |y|)) := by
          rw [← Real.rpow_add_one h1y.ne', ← Real.exp_add]
          ring_nf
  · exact Eventually.of_forall fun y w hw ↦
      (Complex.hasStrictDerivAt_cpow_const (hU_slit hw)).hasDerivAt.smul_const (g y)

/-- If `g : ℝ → E` is strongly measurable and satisfies `‖g y‖ ≤ C (1 + |y|) ^ R e^{-π |y|}`, then
`w ↦ ∫ y : ℝ, w ^ (σ + i y) • g y` is complex differentiable on `Complex.slitPlane`. -/
theorem differentiableOn_integral_cpow_smul_slitPlane {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {g : ℝ → E} (hg_meas : AEStronglyMeasurable g)
    (hg_bound : ∃ C R : ℝ, ∀ y : ℝ, ‖g y‖ ≤ C * (1 + |y|) ^ R * Real.exp (-π * |y|)) (σ : ℝ) :
    DifferentiableOn ℂ (fun w : ℂ ↦ ∫ y : ℝ, w ^ ((σ : ℂ) + y * I) • g y) slitPlane :=
  fun _ hw ↦ (hasDerivAt_integral_cpow_smul_slitPlane hg_meas hg_bound σ
    hw).differentiableAt.differentiableWithinAt

/-- If `g : ℝ → E` is strongly measurable and satisfies `‖g y‖ ≤ C (1 + |y|) ^ R e^{-π |y|}`, then
`w ↦ ∫ y : ℝ, w ^ (σ + i y) • g y` is holomorphic on `Complex.slitPlane`. -/
theorem analyticOnNhd_integral_cpow_smul_slitPlane {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {g : ℝ → E} (hg_meas : AEStronglyMeasurable g)
    (hg_bound : ∃ C R : ℝ, ∀ y : ℝ, ‖g y‖ ≤ C * (1 + |y|) ^ R * Real.exp (-π * |y|)) (σ : ℝ) :
    AnalyticOnNhd ℂ (fun w : ℂ ↦ ∫ y : ℝ, w ^ ((σ : ℂ) + y * I) • g y) slitPlane :=
  (differentiableOn_integral_cpow_smul_slitPlane hg_meas hg_bound σ).analyticOnNhd isOpen_slitPlane

/-- Negated-exponent companion to `TauCeti.differentiableOn_integral_cpow_smul_slitPlane`:
`w ↦ ∫ y : ℝ, w ^ (-(σ + i y)) • g y` is complex differentiable on `Complex.slitPlane`. -/
theorem differentiableOn_integral_cpow_neg_smul_slitPlane {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {g : ℝ → E} (hg_meas : AEStronglyMeasurable g)
    (hg_bound : ∃ C R : ℝ, ∀ y : ℝ, ‖g y‖ ≤ C * (1 + |y|) ^ R * Real.exp (-π * |y|)) (σ : ℝ) :
    DifferentiableOn ℂ (fun w : ℂ ↦ ∫ y : ℝ, w ^ (-((σ : ℂ) + y * I)) • g y) slitPlane := by
  obtain ⟨C, R, hg⟩ := hg_bound
  have hmp := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving
  have hd := differentiableOn_integral_cpow_smul_slitPlane
    (g := fun y ↦ g (-y)) (hg_meas.comp_quasiMeasurePreserving hmp)
    ⟨C, R, fun y ↦ by simpa [abs_neg] using hg (-y)⟩ (-σ)
  refine hd.congr fun w _ ↦ ?_
  rw [← integral_neg_eq_self]
  refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
  dsimp only
  rw [ofReal_neg, ofReal_neg]
  congr 2
  ring

/-- Negated-exponent companion to `TauCeti.analyticOnNhd_integral_cpow_smul_slitPlane`:
`w ↦ ∫ y : ℝ, w ^ (-(σ + i y)) • g y` is holomorphic on `Complex.slitPlane`. -/
theorem analyticOnNhd_integral_cpow_neg_smul_slitPlane {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {g : ℝ → E} (hg_meas : AEStronglyMeasurable g)
    (hg_bound : ∃ C R : ℝ, ∀ y : ℝ, ‖g y‖ ≤ C * (1 + |y|) ^ R * Real.exp (-π * |y|)) (σ : ℝ) :
    AnalyticOnNhd ℂ (fun w : ℂ ↦ ∫ y : ℝ, w ^ (-((σ : ℂ) + y * I)) • g y) slitPlane :=
  (differentiableOn_integral_cpow_neg_smul_slitPlane hg_meas hg_bound σ).analyticOnNhd
    isOpen_slitPlane

end TauCeti
