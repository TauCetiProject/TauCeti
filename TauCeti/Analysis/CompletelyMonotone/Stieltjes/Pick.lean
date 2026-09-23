/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CompletelyMonotone.Stieltjes.Nevanlinna
import TauCeti.Analysis.CompletelyMonotone.Stieltjes.Holomorphic
import TauCeti.Analysis.Complex.Pick.Boundary

/-!
# The Pick characterization of complete Bernstein functions

A function continuous on `[0, ∞)` is complete Bernstein exactly when it is nonnegative on
`(0, ∞)`, extends holomorphically to the slit plane `ℂ \ (-∞, 0]`, and maps the upper
half-plane into its closure.  This is the analytic characterization of complete Bernstein
functions.

The forward direction is the holomorphic extension constructed from complete-Bernstein
representing data.  For the converse, the Pick function has a Nevanlinna representation whose
measure is carried by `(-∞, 0]`.  The only missing boundary step is to pass that representation
from the upper half-plane to a positive real parameter.  The Nevanlinna kernel is uniformly
bounded near such a parameter on `(-∞, 0]`, so dominated convergence makes its integral
continuous there.  The resulting real-axis representation converts directly into
complete-Bernstein representing data.

## Main declarations

* `TauCeti.continuousAt_integral_nevanlinnaKernel_of_measure_Ioi_eq_zero`: the Nevanlinna
  integral of a measure carried by `(-∞, 0]` is continuous at every positive real parameter.
* `TauCeti.eq_integral_nevanlinnaKernel_add_of_eqOn_upperHalfPlane`: a Nevanlinna
  representation on the upper half-plane extends to the positive real axis.
* `TauCeti.isCompleteBernsteinFunction_iff_exists_pickExtension`: the Pick characterization of
  complete Bernstein functions.

## References

* R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions: Theory and Applications*,
  de Gruyter, 2nd ed. (2012), Theorem 6.2.
-/

public section

noncomputable section

open Complex Filter MeasureTheory Set Topology

namespace TauCeti

/-- The Nevanlinna integral of a finite measure carried by `(-∞, 0]` is continuous at every
positive real parameter.  Although the kernel has a pole on the real axis, that pole stays a
positive distance from the measure's support. -/
theorem continuousAt_integral_nevanlinnaKernel_of_measure_Ioi_eq_zero
    {rho : Measure ℝ} [IsFiniteMeasure rho] (hrho : rho (Ioi 0) = 0) {t : ℝ} (ht : 0 < t) :
    ContinuousAt (fun z : ℂ => ∫ x, nevanlinnaKernel z x ∂rho) t := by
  have hale : ∀ᵐ x ∂rho, x ≤ 0 := by
    have hnot : ∀ᵐ x ∂rho, x ∉ Ioi (0 : ℝ) := by
      rw [ae_iff]
      simpa only [not_not, Set.ofPred_mem_eq] using hrho
    filter_upwards [hnot] with x hx
    simpa only [mem_Ioi, not_lt] using hx
  refine tendsto_integral_filter_of_norm_le_const ?_ ?_ ?_
  · exact Eventually.of_forall fun z => by
      have hkernel : nevanlinnaKernel z =
          fun x : ℝ => (1 + (x : ℂ) * z) / ((x : ℂ) - z) :=
        funext (nevanlinnaKernel_def z)
      rw [hkernel]
      have hcoe : Measurable fun x : ℝ => (x : ℂ) := Complex.measurable_ofReal
      exact ((measurable_const.add (hcoe.mul_const z)).div
        (hcoe.sub measurable_const)).aestronglyMeasurable
  · refine ⟨2 * t + (1 + (2 * t) ^ 2) * (2 / t), ?_⟩
    filter_upwards [Metric.ball_mem_nhds (t : ℂ) (half_pos ht)] with z hz
    filter_upwards [hale] with x hx
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have hzt : ‖z‖ < 2 * t := by
      calc
        ‖z‖ ≤ ‖z - (t : ℂ)‖ + ‖(t : ℂ)‖ := by
          simpa only [sub_add_cancel] using norm_add_le (z - (t : ℂ)) (t : ℂ)
        _ < t / 2 + t := by simpa [Real.norm_eq_abs, abs_of_pos ht] using add_lt_add_right hz t
        _ < 2 * t := by linarith
    have hzre : t / 2 < z.re := by
      have hre : |z.re - t| ≤ ‖z - (t : ℂ)‖ := by
        simpa only [sub_re, ofReal_re] using abs_re_le_norm (z - (t : ℂ))
      have : |z.re - t| < t / 2 := lt_of_le_of_lt hre hz
      have := (abs_lt.mp this).1
      linarith
    have hden : t / 2 ≤ ‖(x : ℂ) - z‖ := by
      have hre : |x - z.re| ≤ ‖(x : ℂ) - z‖ := by
        simpa only [sub_re, ofReal_re] using abs_re_le_norm ((x : ℂ) - z)
      have hneg : x - z.re < 0 := by linarith
      rw [abs_of_neg hneg] at hre
      linarith
    have hden0 : (x : ℂ) - z ≠ 0 := by
      rw [← norm_pos_iff]
      exact lt_of_lt_of_le (half_pos ht) hden
    have hsplit : nevanlinnaKernel z x = z + (1 + z ^ 2) / ((x : ℂ) - z) := by
      rw [nevanlinnaKernel_def]
      field_simp
      ring
    have hinv : ‖((x : ℂ) - z)⁻¹‖ ≤ 2 / t := by
      rw [norm_inv]
      calc
        ‖(x : ℂ) - z‖⁻¹ ≤ (t / 2)⁻¹ := inv_anti₀ (half_pos ht) hden
        _ = 2 / t := by field_simp
    rw [hsplit, div_eq_mul_inv]
    calc
      ‖z + (1 + z ^ 2) * ((x : ℂ) - z)⁻¹‖
          ≤ ‖z‖ + ‖(1 + z ^ 2) * ((x : ℂ) - z)⁻¹‖ := norm_add_le _ _
      _ = ‖z‖ + ‖1 + z ^ 2‖ * ‖((x : ℂ) - z)⁻¹‖ := by rw [norm_mul]
      _ ≤ 2 * t + (1 + (2 * t) ^ 2) * (2 / t) := by
        have hsq : ‖z ^ 2‖ < (2 * t) ^ 2 := by
          simpa only [norm_pow] using pow_lt_pow_left₀ hzt (norm_nonneg z) (by norm_num : 2 ≠ 0)
        have hone : ‖1 + z ^ 2‖ ≤ 1 + ‖z ^ 2‖ := by
          simpa only [norm_one] using norm_add_le (1 : ℂ) (z ^ 2)
        calc
          ‖z‖ + ‖1 + z ^ 2‖ * ‖((x : ℂ) - z)⁻¹‖
              ≤ 2 * t + (1 + ‖z ^ 2‖) * (2 / t) := by
                gcongr
          _ ≤ 2 * t + (1 + (2 * t) ^ 2) * (2 / t) := by
                gcongr
  · filter_upwards [hale] with x hx
    have hne : (x : ℂ) - (t : ℂ) ≠ 0 := by
      exact sub_ne_zero.mpr (ofReal_injective.ne (ne_of_lt (lt_of_le_of_lt hx ht)))
    have hkernel : (fun z : ℂ => nevanlinnaKernel z x) =
        fun z : ℂ => (1 + (x : ℂ) * z) / ((x : ℂ) - z) :=
      funext fun z => nevanlinnaKernel_def z x
    rw [hkernel]
    rw [nevanlinnaKernel_def]
    exact ((continuousAt_const.add (continuousAt_const.mul continuousAt_id)).div
      (continuousAt_const.sub continuousAt_id) hne).tendsto

/-- A Nevanlinna representation valid on the upper half-plane extends to every positive real
parameter when its measure is carried by `(-∞, 0]`. -/
theorem eq_integral_nevanlinnaKernel_add_of_eqOn_upperHalfPlane
    {F : ℂ → ℂ} {rho : Measure ℝ} [IsFiniteMeasure rho] {b c t : ℝ}
    (hF : ContinuousAt F t) (hrho : rho (Ioi 0) = 0) (ht : 0 < t)
    (hrep : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
      F z = (b : ℂ) * z + ∫ x, nevanlinnaKernel z x ∂rho + c) :
    F t = (b : ℂ) * t + ∫ x, nevanlinnaKernel t x ∂rho + c := by
  let u : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let z : ℕ → ℂ := fun n => (t : ℂ) + (u n : ℂ) * I
  have hz : Tendsto z atTop (nhds (t : ℂ)) := by
    have hu : Tendsto u atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have hzero : Tendsto (fun n : ℕ => (u n : ℂ)) atTop (nhds 0) := by
      simpa [Function.comp_def] using (continuous_ofReal.tendsto 0).comp hu
    simpa only [z, add_zero, zero_mul] using
      tendsto_const_nhds.add (hzero.mul_const I)
  have hright : Tendsto
      (fun w : ℂ => (b : ℂ) * w + ∫ x, nevanlinnaKernel w x ∂rho + c)
      (nhds (t : ℂ))
      (nhds ((b : ℂ) * t + ∫ x, nevanlinnaKernel t x ∂rho + c)) :=
    ((continuousAt_const.mul continuousAt_id).add
      (continuousAt_integral_nevanlinnaKernel_of_measure_Ioi_eq_zero hrho ht)).add
      continuousAt_const
  have heq : ∀ n, F (z n) =
      (b : ℂ) * z n + ∫ x, nevanlinnaKernel (z n) x ∂rho + c := by
    intro n
    apply hrep
    rw [UpperHalfPlane.upperHalfPlaneSet]
    have hn : 0 < u n := by
      dsimp only [u]
      positivity
    simpa [z] using hn
  exact tendsto_nhds_unique (hF.tendsto.comp hz)
    ((hright.comp hz).congr' (Eventually.of_forall fun n => (heq n).symm))

/-- **Pick characterization of complete Bernstein functions** (Schilling--Song--Vondraček,
Theorem 6.2).  A real function continuous on `[0, ∞)` is complete Bernstein exactly when it is
nonnegative on `(0, ∞)` and has a holomorphic extension to the slit plane that maps the upper
half-plane into its closure. -/
theorem isCompleteBernsteinFunction_iff_exists_pickExtension (f : ℝ → ℝ) :
    IsCompleteBernsteinFunction f ↔
      ContinuousOn f (Ici 0) ∧ (∀ t : ℝ, 0 < t → 0 ≤ f t) ∧
        ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F slitPlane ∧
          (∀ t : ℝ, 0 < t → F t = f t) ∧
          ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet, 0 ≤ (F z).im := by
  constructor
  · intro hf
    obtain ⟨F, hF, hFf, him⟩ := hf.exists_analyticOnNhd_slitPlane
    refine ⟨hf.isBernsteinFunction.continuousOn,
      fun t ht => hf.isBernsteinFunction.nonneg ht.le, F, hF, hFf, fun z hz => ?_⟩
    have hzim : 0 < z.im := hz
    have hzslit : z ∈ slitPlane := mem_slitPlane_iff.2 (Or.inr hzim.ne')
    have hprod := him z hzslit
    nlinarith
  · rintro ⟨hfcont, hpos, F, hF, hFf, him⟩
    have hzero : ∀ t : ℝ, 0 < t → (F (t : ℂ)).im = 0 := fun t ht => by
      rw [hFf t ht]
      simp
    obtain ⟨rho, b, hrhoFinite, hb, hrho, hrep⟩ :=
      exists_isFiniteMeasure_eq_nevanlinnaKernel_add_of_im_eq_zero
        hF.differentiableOn him hzero
    let _ := hrhoFinite
    obtain ⟨g, hg, hgf⟩ :=
      exists_isCompleteBernsteinFunction_eqOn_of_eq_integral_nevanlinnaKernel
        hrho hb (f := f) (fun t ht => by
          rw [← hFf t ht]
          exact eq_integral_nevanlinnaKernel_add_of_eqOn_upperHalfPlane
            (hF.continuousOn.continuousAt
              (isOpen_slitPlane.mem_nhds (ofReal_mem_slitPlane.mpr ht)))
            hrho ht hrep) hpos
    have hgf' : EqOn g f (Ici 0) := hgf.of_subset_closure
      hg.isBernsteinFunction.continuousOn hfcont Ioi_subset_Ici_self (by rw [closure_Ioi])
    exact hg.congr hgf'.symm

end TauCeti

end
