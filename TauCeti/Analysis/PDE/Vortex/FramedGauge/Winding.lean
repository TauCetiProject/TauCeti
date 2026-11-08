/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Basic
import TauCeti.Analysis.Contour.Argument.Lift
import TauCeti.Analysis.PDE.Vortex.Reference

/-!
# The winding gauge of the degree-`m` reference fields

The unit phase `w / |w|` (`unitPhase`) has logarithmic derivative `dθ`, so its `m`-th power,
the winding gauge of the degree-`m` reference fields, has logarithmic derivative `m dθ` away from
the origin (`gaugeForm_unitPhase_pow`). These gauges are not framed: they do not tend to one at
infinity.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Birkhäuser, 1980, Chapter III.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex ComplexConjugate Filter
open scoped Topology ContDiff

/-- The unit phase `w / |w|` as a circle-valued map, with value `1` at the origin. Its powers
are the winding gauges of the degree-`m` reference fields; they are not framed. -/
def unitPhase (w : ℂ) : Circle := Circle.exp (arg w)

/-- The unit phase is `1` at the origin. -/
@[simp] theorem unitPhase_zero : unitPhase 0 = 1 := by simp [unitPhase]

/-- Away from the origin the unit phase is `w / |w|`. -/
theorem coe_unitPhase {w : ℂ} (hw : w ≠ 0) : (unitPhase w : ℂ) = w / (‖w‖ : ℂ) := by
  rw [unitPhase, Circle.coe_exp, TauCeti.Contour.div_norm_eq_exp_arg_mul_I hw]

private theorem eventuallyEq_unitPhase {w : ℂ} (hw : w ≠ 0) :
    (fun v ↦ (unitPhase v : ℂ)) =ᶠ[𝓝 w] fun v ↦ v / (‖v‖ : ℂ) :=
  eventually_of_mem (isOpen_compl_singleton.mem_nhds hw) fun _ hv ↦ coe_unitPhase hv

/-- The winding gauge `(w / |w|)^m` is smooth away from the origin. -/
theorem contDiffAt_unitPhase_pow (m : ℕ) {w : ℂ} (hw : w ≠ 0) :
    ContDiffAt ℝ ∞ (fun v ↦ ((unitPhase ^ m) v : ℂ)) w := by
  simp only [Pi.pow_apply, Circle.coe_pow]
  exact ((contDiffOn_phase m).contDiffAt (isOpen_compl_singleton.mem_nhds hw)).congr_of_eventuallyEq
    ((eventuallyEq_unitPhase hw).fun_comp (· ^ m))

/-- The logarithmic derivative of the unit phase is `dθ`, `dθ_w (v) = Im (v / w)`. -/
theorem gaugeForm_unitPhase {w : ℂ} (hw : w ≠ 0) (v : ℂ) :
    gaugeForm unitPhase w v = (v / w).im := by
  have hr : DifferentiableAt ℝ (fun v : ℂ ↦ ‖v‖⁻¹) w :=
    ((contDiffAt_norm ℂ (n := 1) hw).differentiableAt one_ne_zero).inv (norm_ne_zero_iff.2 hw)
  -- Write `v / |v|` as `v` times the real factor `|v|⁻¹`, whose derivative is real.
  have hd : HasFDerivAt (fun v : ℂ ↦ ((‖v‖⁻¹ : ℝ) : ℂ))
      (ofRealCLM.comp (fderiv ℝ (fun v : ℂ ↦ ‖v‖⁻¹) w)) w :=
    ofRealCLM.hasFDerivAt.comp w hr.hasFDerivAt
  have hdiv : (fun v : ℂ ↦ v / (‖v‖ : ℂ)) = fun v ↦ v * ((‖v‖⁻¹ : ℝ) : ℂ) := by
    ext v
    rw [ofReal_inv, div_eq_mul_inv]
  rw [gaugeForm_apply, (eventuallyEq_unitPhase hw).fderiv_eq, coe_unitPhase hw, hdiv,
    fderiv_fun_mul differentiableAt_fun_id hd.differentiableAt, hd.fderiv]
  simp only [fderiv_fun_id, add_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ofRealCLM_apply, smul_eq_mul, ContinuousLinearMap.id_apply]
  -- The derivative of the real factor contributes only a real term.
  have key : conj (w / (‖w‖ : ℂ)) * (w * (fderiv ℝ (fun v : ℂ ↦ ‖v‖⁻¹) w v : ℂ) +
      ((‖w‖⁻¹ : ℝ) : ℂ) * v) = ((‖w‖ * fderiv ℝ (fun v : ℂ ↦ ‖v‖⁻¹) w v : ℝ) : ℂ) + v / w := by
    have hn : (‖w‖ : ℂ) ≠ 0 := ofReal_ne_zero.2 (norm_ne_zero_iff.2 hw)
    rw [map_div₀, conj_ofReal, ofReal_inv, ofReal_mul]
    field_simp
    rw [conj_mul']
  rw [key, add_im, ofReal_im, zero_add]

/-- The logarithmic derivative of the winding gauge `(w / |w|)^m` is `m dθ`. -/
theorem gaugeForm_unitPhase_pow (m : ℕ) {w : ℂ} (hw : w ≠ 0) (v : ℂ) :
    gaugeForm (unitPhase ^ m) w v = m * (v / w).im := by
  induction m with
  | zero => simp
  | succ n ih =>
    have hd (k : ℕ) : DifferentiableAt ℝ (fun v ↦ ((unitPhase ^ k) v : ℂ)) w :=
      (contDiffAt_unitPhase_pow k hw).differentiableAt (by simp)
    rw [pow_succ, gaugeForm_mul (hd n) (by simpa using hd 1)]
    simp only [FunLike.coe_add, Pi.add_apply, ih, gaugeForm_unitPhase hw]
    push_cast
    ring

end TauCeti.Vortex
