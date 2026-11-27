/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.BoundedMeanOscillation
public import TauCeti.MeasureTheory.Function.SeparatedVariables
import TauCeti.MeasureTheory.Integral.Average

/-!
# Mean oscillation of a function of fewer variables

Splitting off the first coordinate identifies `ℝⁿ⁺¹` with `ℝ × ℝⁿ`
(`EuclideanSpace.consEquivL ℝ n`). A function `f` on `ℝⁿ` defines the function
`y = (t, x) ↦ f(x)` on `ℝⁿ⁺¹`, constant in `t`. This file shows that its mean oscillation over a
ball of `ℝⁿ⁺¹` is controlled by the mean oscillation of `f` over a ball of `ℝⁿ` of the same radius:

* `TauCeti.vmoModulus_comp_snd_consEquivL_symm_le`: its VMO modulus is at most `2ⁿ⁺²` times that
  of `f`, at every radius;
* `TauCeti.bmoSeminorm_comp_snd_consEquivL_symm_le`: the same for the BMO seminorm;
* `TauCeti.MemVMO.comp_snd_consEquivL_symm`: it has vanishing mean oscillation when `f` has.

The ball `B(c, s)` of `ℝⁿ⁺¹` lies in the cylinder `(t_c - s, t_c + s) × B(x_c, s)` and contains the
cylinder of half the radius, so averages over `B(c, s)` of a function of `x` alone are at most
`2ⁿ⁺¹` times averages over `B(x_c, s)`
(`EuclideanSpace.setLAverage_ball_comp_snd_consEquivL_symm_le`).
Measuring the oscillation about the average of `f` over `B(x_c, s)` instead of the optimal constant
costs a further factor `2`.

These bounds let a coefficient field of vanishing mean oscillation on `ℝⁿ` be extended to `ℝⁿ⁺¹`
without leaving the class, as in Agmon's device of adding a variable to an elliptic operator.
-/

public section

open MeasureTheory Metric Set Filter
open scoped ENNReal Topology

namespace TauCeti

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The VMO modulus of the function `(t, x) ↦ f(x)` on `ℝⁿ⁺¹` is at most `2ⁿ⁺²` times that of `f`
on `ℝⁿ`, at every radius. -/
theorem vmoModulus_comp_snd_consEquivL_symm_le {f : EuclideanSpace ℝ (Fin n) → F}
    (hf : LocallyIntegrable f volume) (r : ℝ) :
    vmoModulus (fun y => f ((EuclideanSpace.consEquivL ℝ n).symm y).2) volume r ≤
      2 ^ (n + 2) * vmoModulus f volume r := by
  refine vmoModulus_le fun c s hs => ?_
  set x₀ := ((EuclideanSpace.consEquivL ℝ n).symm c).2
  set m := ⨍ x in ball x₀ s, f x
  calc ⨍⁻ y in ball c s, ‖f ((EuclideanSpace.consEquivL ℝ n).symm y).2 -
        ⨍ z in ball c s, f ((EuclideanSpace.consEquivL ℝ n).symm z).2‖ₑ
      ≤ 2 * ⨍⁻ y in ball c s, ‖f ((EuclideanSpace.consEquivL ℝ n).symm y).2 - m‖ₑ :=
        setLAverage_enorm_sub_setAverage_le (hf.integrableOn_ball_comp_snd_consEquivL_symm c s) m
    _ ≤ 2 * (2 ^ (n + 1) * ⨍⁻ x in ball x₀ s, ‖f x - m‖ₑ) := by
        gcongr
        exact EuclideanSpace.setLAverage_ball_comp_snd_consEquivL_symm_le
          (G := fun x => ‖f x - m‖ₑ) (hf.aestronglyMeasurable.sub aestronglyMeasurable_const).eNorm
          c s
    _ ≤ 2 * (2 ^ (n + 1) * vmoModulus f volume r) := by
        gcongr
        exact setLAverage_enorm_sub_setAverage_le_vmoModulus f volume x₀ hs
    _ = 2 ^ (n + 2) * vmoModulus f volume r := by ring

/-- The BMO seminorm of the function `(t, x) ↦ f(x)` on `ℝⁿ⁺¹` is at most `2ⁿ⁺²` times that of
`f` on `ℝⁿ`. -/
theorem bmoSeminorm_comp_snd_consEquivL_symm_le {f : EuclideanSpace ℝ (Fin n) → F}
    (hf : LocallyIntegrable f volume) :
    bmoSeminorm (fun y => f ((EuclideanSpace.consEquivL ℝ n).symm y).2) volume ≤
      2 ^ (n + 2) * bmoSeminorm f volume := by
  rw [← iSup_vmoModulus]
  exact iSup_le fun r => (vmoModulus_comp_snd_consEquivL_symm_le hf r).trans
    (mul_le_mul_right (vmoModulus_le_bmoSeminorm f volume r) _)

/-- If `f` has vanishing mean oscillation on `ℝⁿ`, so does the function `(t, x) ↦ f(x)` on
`ℝⁿ⁺¹`. -/
theorem MemVMO.comp_snd_consEquivL_symm {f : EuclideanSpace ℝ (Fin n) → F}
    (hf : MemVMO f volume) :
    MemVMO (fun y => f ((EuclideanSpace.consEquivL ℝ n).symm y).2) volume := by
  have hli := hf.memBMO.locallyIntegrable
  refine memVMO_iff_tendsto.2 ⟨memBMO_iff.2 ⟨fun y => ⟨ball y 1, ball_mem_nhds y one_pos,
    hli.integrableOn_ball_comp_snd_consEquivL_symm y 1⟩, ?_⟩, ?_⟩
  · exact (bmoSeminorm_comp_snd_consEquivL_symm_le hli).trans_lt
      (ENNReal.mul_lt_top (by finiteness) hf.memBMO.bmoSeminorm_lt_top)
  · have h := ENNReal.Tendsto.const_mul hf.tendsto_vmoModulus
      (Or.inr (by finiteness : (2 : ℝ≥0∞) ^ (n + 2) ≠ ∞))
    rw [mul_zero] at h
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => zero_le)
      (vmoModulus_comp_snd_consEquivL_symm_le hli)

end TauCeti
