/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Pick.Nevanlinna
public import TauCeti.Analysis.CompletelyMonotone.Stieltjes.CompleteBernstein

/-!
# Complete Bernstein functions from a Nevanlinna representation off the positive half-axis

A Nevanlinna representation

`F(z) = c + b z + ∫ x, (1 + x z) / (x - z) ∂ρ`

with a finite measure `ρ` carried by `(-∞, 0]` restricts on `(0, ∞)` to a real function, and this
file converts such data into complete-Bernstein representing data whenever that restriction is
nonnegative.

Reflecting `ρ` to the finite measure `ν` on `ℝ≥0` obtained by pushing forward along `x ↦ -x`, the
kernel becomes `(t y - 1) / (t + y) = t - (1 + t ^ 2) / (t + y)`, so the representation reads

`f(t) = c + (b + ν(ℝ≥0)) t - (1 + t ^ 2) ∫ y, (t + y)⁻¹ ∂ν`.

Nonnegativity of `f` on `(0, ∞)` bounds the Stieltjes transform `∫ y, (t + y)⁻¹ ∂ν` by an affine
function of `t`, and letting `t` decrease to zero turns that bound into the finiteness of
`∫ y, y⁻¹ ∂ν`, the pivot of the whole argument: it forbids an atom of `ν` at `0`, it makes the
weighted measure `μ = (1 + y ^ 2) y⁻¹ ν` satisfy the Stieltjes weight condition, and it makes the
constant `c - ∫ y, y⁻¹ ∂ν` nonnegative.  The pointwise identity

`(1 + y ^ 2) y⁻¹ · t / (t + y) = y⁻¹ + t - (1 + t ^ 2) / (t + y)`  (`y > 0`)

then rewrites the representation as `f(t) = (c - ∫ y, y⁻¹ ∂ν) + b t + ∫ y, t / (t + y) ∂μ`, which
is the complete-Bernstein form.

This is the half of the analytic characterization of complete Bernstein functions that starts from
the Nevanlinna data; the converse, that a complete Bernstein function extends to a Pick function on
the slit plane, is `TauCeti.IsCompleteBernsteinFunction.exists_analyticOnNhd_slitPlane`.

## Main declarations

* `TauCeti.lintegral_inv_le_of_forall_integral_inv_add_le`: an affine bound on the Stieltjes
  transform of a finite measure on `ℝ≥0` near the origin bounds `∫ y, y⁻¹ ∂ν`.
* `TauCeti.exists_isCompleteBernsteinFunction_eqOn_of_eq_integral_div_add`: the reflected form of
  the conversion, for a measure on `ℝ≥0`.
* `TauCeti.exists_isCompleteBernsteinFunction_eqOn_of_eq_integral_nevanlinnaKernel`: the
  conversion, for Nevanlinna data on `ℝ` carried by `(-∞, 0]`.

## References

* R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions: Theory and Applications*,
  de Gruyter, 2nd ed. (2012), Theorem 6.2.
-/

public section

noncomputable section

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal

namespace TauCeti

/-- If the Stieltjes transform of a finite measure on `ℝ≥0` is bounded by `c + C t` at every
positive parameter `t`, then `∫ y, y⁻¹ ∂ν ≤ c`: the parameter may be sent to zero.  The bound is
stated as a lower Lebesgue integral because `y ↦ y⁻¹` is unbounded, and the conclusion carries in
particular the finiteness of that integral. -/
theorem lintegral_inv_le_of_forall_integral_inv_add_le {ν : Measure ℝ≥0} [IsFiniteMeasure ν]
    {c C : ℝ} (h : ∀ t : ℝ, 0 < t → (∫ y : ℝ≥0, (t + (y : ℝ))⁻¹ ∂ν) ≤ c + C * t) :
    ∫⁻ y : ℝ≥0, (y : ℝ≥0∞)⁻¹ ∂ν ≤ ENNReal.ofReal c := by
  set u : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hu
  have hupos : ∀ n, 0 < u n := fun n => by positivity
  have huanti : Antitone u := by
    intro m n hmn
    have hle : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
    simp only [hu]
    gcongr
  have hu0 : Tendsto u atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  set F : ℕ → ℝ≥0 → ℝ≥0∞ := fun n y => (ENNReal.ofReal (u n) + (y : ℝ≥0∞))⁻¹ with hF
  have hFmeas : ∀ n, Measurable (F n) := fun n => by fun_prop
  have hFmono : Monotone F := by
    intro m n hmn y
    exact ENNReal.inv_le_inv' (by gcongr; exact huanti hmn)
  have hsup : ∀ y : ℝ≥0, ⨆ n, F n y = (y : ℝ≥0∞)⁻¹ := by
    intro y
    have htend : Tendsto (fun n => F n y) atTop (𝓝 ((y : ℝ≥0∞))⁻¹) := by
      have h1 : Tendsto (fun n => ENNReal.ofReal (u n) + (y : ℝ≥0∞)) atTop
          (𝓝 (0 + (y : ℝ≥0∞))) := by
        refine Tendsto.add ?_ tendsto_const_nhds
        simpa using ENNReal.tendsto_ofReal hu0
      simpa [hF] using tendsto_inv_iff.2 h1
    exact tendsto_nhds_unique (tendsto_atTop_iSup fun m n hmn => hFmono hmn y) htend
  have hint : ∀ t : ℝ, 0 < t → Integrable (fun y : ℝ≥0 => (t + (y : ℝ))⁻¹) ν :=
    fun t ht => integrable_inv_add (integrable_stieltjesWeight ν) ht
  have hFint : ∀ n, ∫⁻ y : ℝ≥0, F n y ∂ν
      = ENNReal.ofReal (∫ y : ℝ≥0, (u n + (y : ℝ))⁻¹ ∂ν) := by
    intro n
    rw [ofReal_integral_eq_lintegral_ofReal (hint _ (hupos n))
      (.of_forall fun y => by positivity)]
    refine lintegral_congr fun y => ?_
    rw [hF, ENNReal.ofReal_inv_of_pos (by positivity),
      ENNReal.ofReal_add (hupos n).le y.coe_nonneg, ENNReal.ofReal_coe_nnreal]
  have hrw : ∫⁻ y : ℝ≥0, (y : ℝ≥0∞)⁻¹ ∂ν = ⨆ n, ∫⁻ y : ℝ≥0, F n y ∂ν := by
    rw [← lintegral_iSup hFmeas hFmono]
    exact lintegral_congr fun y => (hsup y).symm
  rw [hrw]
  refine le_of_tendsto_of_tendsto'
    (tendsto_atTop_iSup fun m n hmn => lintegral_mono (hFmono hmn))
    (ENNReal.tendsto_ofReal (by simpa using tendsto_const_nhds.add (hu0.const_mul C)))
    fun n => ?_
  rw [hFint n]
  exact ENNReal.ofReal_le_ofReal (h _ (hupos n))

/-- The algebraic identity behind the conversion: the complete-Bernstein kernel weighted by the
Stieltjes density `(1 + y ^ 2) / y` differs from the reflected Nevanlinna kernel by `y⁻¹`. -/
private lemma one_add_sq_div_mul_div_add_eq (t : ℝ) {y : ℝ} (hy : y ≠ 0) (hty : t + y ≠ 0) :
    (1 + y ^ 2) / y * (t / (t + y)) = y⁻¹ + (t * y - 1) / (t + y) := by
  field_simp
  ring

/-- **Complete Bernstein functions from reflected Nevanlinna data.** A function that agrees on
`(0, ∞)` with `c + b t + ∫ y, (t y - 1) / (t + y) ∂ν`, for a finite measure `ν` on `ℝ≥0` and
`b ≥ 0`, and is nonnegative there, agrees on `(0, ∞)` with a complete Bernstein function.

The integrand is the Nevanlinna kernel `(1 + x t) / (x - t)` after the reflection `x = -y` that
carries `(-∞, 0]` onto `ℝ≥0`. -/
theorem exists_isCompleteBernsteinFunction_eqOn_of_eq_integral_div_add {ν : Measure ℝ≥0}
    [IsFiniteMeasure ν] {b c : ℝ} (hb : 0 ≤ b) {f : ℝ → ℝ}
    (hf : ∀ t : ℝ, 0 < t → f t = c + b * t + ∫ y : ℝ≥0, (t * y - 1) / (t + y) ∂ν)
    (hpos : ∀ t : ℝ, 0 < t → 0 ≤ f t) :
    ∃ g : ℝ → ℝ, IsCompleteBernsteinFunction g ∧ EqOn g f (Ioi 0) := by
  have hint : ∀ t : ℝ, 0 < t → Integrable (fun y : ℝ≥0 => (t + (y : ℝ))⁻¹) ν :=
    fun t ht => integrable_inv_add (integrable_stieltjesWeight ν) ht
  have hKnonneg : ∀ t : ℝ, 0 < t → 0 ≤ ∫ y : ℝ≥0, (t + (y : ℝ))⁻¹ ∂ν :=
    fun t ht => integral_nonneg fun y => by positivity
  -- Rewrite the representation with the Stieltjes transform of `ν` as its only integral.
  have hrep : ∀ t : ℝ, 0 < t →
      f t = c + (b + ν.real univ) * t - (1 + t ^ 2) * ∫ y : ℝ≥0, (t + (y : ℝ))⁻¹ ∂ν := by
    intro t ht
    have hsplit : ∫ y : ℝ≥0, (t * y - 1) / (t + y) ∂ν
        = ν.real univ * t - (1 + t ^ 2) * ∫ y : ℝ≥0, (t + (y : ℝ))⁻¹ ∂ν := by
      calc ∫ y : ℝ≥0, (t * y - 1) / (t + y) ∂ν
          = ∫ y : ℝ≥0, (t - (1 + t ^ 2) * (t + (y : ℝ))⁻¹) ∂ν := by
            refine integral_congr_ae (.of_forall fun y => ?_)
            have hty : (0 : ℝ) < t + y := by positivity
            field_simp
            ring
        _ = (∫ _y : ℝ≥0, t ∂ν) - (1 + t ^ 2) * ∫ y : ℝ≥0, (t + (y : ℝ))⁻¹ ∂ν := by
            rw [integral_sub (integrable_const t) ((hint t ht).const_mul _), integral_const_mul]
        _ = ν.real univ * t - (1 + t ^ 2) * ∫ y : ℝ≥0, (t + (y : ℝ))⁻¹ ∂ν := by
            rw [integral_const, smul_eq_mul]
    rw [hf t ht, hsplit]
    ring
  -- Nonnegativity forces an affine bound on the Stieltjes transform of `ν` near the origin.
  have hbound : ∀ t : ℝ, 0 < t →
      (∫ y : ℝ≥0, (t + (y : ℝ))⁻¹ ∂ν) ≤ c + (b + ν.real univ) * t := by
    intro t ht
    have h1 := hpos t ht
    rw [hrep t ht] at h1
    nlinarith [hKnonneg t ht, sq_nonneg t]
  have hc : 0 ≤ c := by
    have hle : ∀ t : ℝ, 0 < t → 0 ≤ c + (b + ν.real univ) * t := fun t ht =>
      le_trans (hKnonneg t ht) (hbound t ht)
    have htend : Tendsto (fun t : ℝ => c + (b + ν.real univ) * t) (𝓝[>] 0) (𝓝 c) := by
      have : Tendsto (fun t : ℝ => c + (b + ν.real univ) * t) (𝓝 0)
          (𝓝 (c + (b + ν.real univ) * 0)) :=
        tendsto_const_nhds.add (tendsto_const_nhds.mul tendsto_id)
      simpa using this.mono_left nhdsWithin_le_nhds
    exact ge_of_tendsto htend (eventually_nhdsWithin_of_forall hle)
  -- The pivot: `∫ y⁻¹ ∂ν` is finite and bounded by `c`.
  have hmeas : AEMeasurable (fun y : ℝ≥0 => (y : ℝ≥0∞)⁻¹) ν := by fun_prop
  have hlint := lintegral_inv_le_of_forall_integral_inv_add_le hbound
  have hlinttop : ∫⁻ y : ℝ≥0, (y : ℝ≥0∞)⁻¹ ∂ν ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hlint
  have hν0 : ν {0} = 0 := by
    have hset : {y : ℝ≥0 | (y : ℝ≥0∞)⁻¹ = ⊤} = {0} := by
      ext y
      simp
    simpa [hset] using measure_eq_top_of_lintegral_ne_top hmeas hlinttop
  have hane : ∀ᵐ y ∂ν, y ≠ 0 := by
    rw [ae_iff]
    simpa using hν0
  have hyint : Integrable (fun y : ℝ≥0 => ((y : ℝ))⁻¹) ν := by
    simpa [ENNReal.toReal_inv] using integrable_toReal_of_lintegral_ne_top hmeas hlinttop
  set I : ℝ := ∫ y : ℝ≥0, ((y : ℝ))⁻¹ ∂ν with hIdef
  have hIc : I ≤ c := by
    have hfin : ∀ᵐ y : ℝ≥0 ∂ν, (y : ℝ≥0∞)⁻¹ < ⊤ := by
      filter_upwards [hane] with y hy
      simpa [pos_iff_ne_zero] using hy
    have hI : I = (∫⁻ y : ℝ≥0, (y : ℝ≥0∞)⁻¹ ∂ν).toReal := by
      rw [hIdef, ← integral_toReal hmeas hfin]
      simp [ENNReal.toReal_inv]
    rw [hI, ← ENNReal.toReal_ofReal hc]
    exact ENNReal.toReal_mono ENNReal.ofReal_ne_top hlint
  -- The weighted measure carrying the complete-Bernstein representation.
  set d : ℝ≥0 → ℝ≥0 := fun y => (1 + y ^ 2) / y with hd
  have hdmeas : Measurable d := by fun_prop
  have hdcoe : ∀ y : ℝ≥0, (d y : ℝ) = (1 + (y : ℝ) ^ 2) / (y : ℝ) := by
    intro y
    rw [hd]
    push_cast
    ring
  set μ : Measure ℝ≥0 := ν.withDensity (fun y => (d y : ℝ≥0∞)) with hμdef
  have hμ0 : μ {0} = 0 := by
    rw [hμdef, withDensity_apply _ (measurableSet_singleton 0),
      setLIntegral_measure_zero _ _ hν0]
  have hμw : Integrable stieltjesWeight μ := by
    rw [hμdef, integrable_withDensity_iff_integrable_smul hdmeas]
    have hmul : Measurable fun y : ℝ≥0 => (d y : ℝ) * stieltjesWeight y :=
      hdmeas.coe_nnreal_real.mul measurable_stieltjesWeight
    have hsm : AEStronglyMeasurable (fun y : ℝ≥0 => d y • stieltjesWeight y) ν :=
      hmul.aestronglyMeasurable.congr
        (.of_forall fun y => by simp only [NNReal.smul_def, smul_eq_mul])
    refine (hyint.add (integrable_const (1 : ℝ))).mono' hsm ?_
    filter_upwards [hane] with y hy
    have hY : (0 : ℝ) < y := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hy)
    have hsub : ((y : ℝ))⁻¹ + 1 - (1 + (y : ℝ) ^ 2) / (y : ℝ) * (1 + (y : ℝ))⁻¹
        = 2 / (1 + (y : ℝ)) := by
      field_simp
      ring
    simp only [Pi.add_apply, NNReal.smul_def, smul_eq_mul, stieltjesWeight_apply, hdcoe,
      Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity), ← sub_nonneg, hsub]
    positivity
  -- The reflected Nevanlinna integral in terms of the weighted measure.
  have hdint : ∀ t : ℝ, 0 < t →
      Integrable (fun y : ℝ≥0 => (d y : ℝ) * (t / (t + y))) ν := by
    intro t ht
    have h := (integrable_inv_add hμw ht).const_mul t
    rw [hμdef, integrable_withDensity_iff_integrable_smul hdmeas] at h
    refine h.congr (.of_forall fun y => ?_)
    simp only [NNReal.smul_def, smul_eq_mul, div_eq_mul_inv]
  have hkey : ∀ t : ℝ, 0 < t →
      ∫ y : ℝ≥0, (t * y - 1) / (t + y) ∂ν
        = (∫ y : ℝ≥0, (d y : ℝ) * (t / (t + y)) ∂ν) - I := by
    intro t ht
    rw [hIdef, ← integral_sub (hdint t ht) hyint]
    refine integral_congr_ae ?_
    filter_upwards [hane] with y hy
    have hY : (0 : ℝ) < y := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hy)
    rw [hdcoe, one_add_sq_div_mul_div_add_eq t hY.ne' (by positivity)]
    ring
  refine ⟨stieltjesBernsteinTransform μ (c - I).toNNReal b.toNNReal,
    isCompleteBernsteinFunction_stieltjesBernsteinTransform hμ0 hμw, fun t ht => ?_⟩
  have htpos : (0 : ℝ) < t := mem_Ioi.mp ht
  rw [stieltjesBernsteinTransform_apply, hf t htpos, hkey t htpos,
    Real.coe_toNNReal _ (sub_nonneg.mpr hIc), Real.coe_toNNReal _ hb, hμdef,
    integral_withDensity_eq_integral_smul hdmeas]
  simp only [NNReal.smul_def, smul_eq_mul]
  ring

/-- **Complete Bernstein functions from a Nevanlinna representation off the positive half-axis.**
A function that agrees on `(0, ∞)` with the Nevanlinna transform `b t + ∫ x, (1 + x t) / (x - t) ∂ρ
+ c` of a nonnegative coefficient `b` and a finite measure `ρ` giving no mass to `(0, ∞)`, and is
nonnegative there, agrees on `(0, ∞)` with a complete Bernstein function. -/
theorem exists_isCompleteBernsteinFunction_eqOn_of_eq_integral_nevanlinnaKernel
    {ρ : Measure ℝ} [IsFiniteMeasure ρ] (hρ : ρ (Ioi 0) = 0) {b c : ℝ} (hb : 0 ≤ b) {f : ℝ → ℝ}
    (hf : ∀ t : ℝ, 0 < t →
      (f t : ℂ) = (b : ℂ) * t + (∫ x : ℝ, nevanlinnaKernel (t : ℂ) x ∂ρ) + c)
    (hpos : ∀ t : ℝ, 0 < t → 0 ≤ f t) :
    ∃ g : ℝ → ℝ, IsCompleteBernsteinFunction g ∧ EqOn g f (Ioi 0) := by
  have hale : ∀ᵐ x ∂ρ, x ≤ 0 := by
    have hset : {x : ℝ | ¬ x ≤ 0} = Ioi 0 := by
      ext x
      simp [not_le]
    rw [ae_iff, hset]
    exact hρ
  set ν : Measure ℝ≥0 := ρ.map (fun x => (-x).toNNReal) with hν
  have : IsFiniteMeasure ν := by
    rw [hν]
    exact ρ.isFiniteMeasure_map fun x => (-x).toNNReal
  refine exists_isCompleteBernsteinFunction_eqOn_of_eq_integral_div_add (ν := ν) (c := c) hb ?_
    hpos
  intro t ht
  have hreal : (∫ x : ℝ, nevanlinnaKernel (t : ℂ) x ∂ρ : ℂ)
      = ((∫ x : ℝ, (1 + x * t) / (x - t) ∂ρ : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    exact integral_congr_ae (.of_forall fun x => nevanlinnaKernel_ofReal t x)
  have htransport : ∫ x : ℝ, (1 + x * t) / (x - t) ∂ρ
      = ∫ y : ℝ≥0, (t * y - 1) / (t + y) ∂ν := by
    have hcont : Continuous fun y : ℝ≥0 => (t * (y : ℝ) - 1) / (t + y) :=
      Continuous.div (by fun_prop) (by fun_prop) fun y => by positivity
    rw [hν, integral_map (by fun_prop) hcont.aestronglyMeasurable]
    refine (integral_congr_ae ?_).symm
    filter_upwards [hale] with x hx
    have hxc : ((-x).toNNReal : ℝ) = -x := Real.coe_toNNReal _ (by linarith)
    rw [hxc]
    rw [show t + -x = -(x - t) by ring, show t * -x - 1 = -(1 + x * t) by ring, neg_div_neg_eq]
  have := hf t ht
  rw [hreal, htransport] at this
  have hcast : (f t : ℂ) = ((c + b * t + ∫ y : ℝ≥0, (t * y - 1) / (t + y) ∂ν : ℝ) : ℂ) := by
    rw [this]
    push_cast
    ring
  exact_mod_cast hcast

end TauCeti

end

end
