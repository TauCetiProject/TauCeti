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

/-- The reflection `x = -y` transporting the Nevanlinna kernel to `ℝ≥0`: negating numerator and
denominator turns the reflected kernel back into `(1 + x t) / (x - t)`. -/
private lemma mul_neg_sub_one_div_add_neg_eq (t : ℝ) {x : ℝ} (hxt : x - t ≠ 0) :
    (t * -x - 1) / (t + -x) = (1 + x * t) / (x - t) := by
  have hx : t + -x ≠ 0 := fun h => hxt (by linarith)
  rw [div_eq_div_iff hx hxt]
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
    have hxt : x - t ≠ 0 := (by linarith : x - t < 0).ne
    rw [hxc, mul_neg_sub_one_div_add_neg_eq t hxt]
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
