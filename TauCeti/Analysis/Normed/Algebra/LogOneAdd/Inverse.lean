/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Analysis.Analytic.OfScalars
public import TauCeti.Analysis.Normed.Algebra.LogOneAdd.Basic
public import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Local inverse equations for the Banach algebra logarithm

This file proves that `NormedSpace.logOneAdd` and the exponential are inverse near the origin, in
a complete normed algebra over a characteristic-zero nontrivially normed field on which `ℚ` acts
continuously (the setting of `NormedSpace.exp_hasFPowerSeriesAt_zero`).

## Main results

* `NormedSpace.eventually_logOneAdd_exp_sub_one`: near zero, `logOneAdd (exp x - 1) = x`.
* `NormedSpace.eventually_exp_logOneAdd`: near zero, `exp (logOneAdd x) = 1 + x`.

## Implementation notes

The power series of `logOneAdd` and of the exponential have rational coefficients, and so do their
formal compositions. These rational coefficients are identified over `ℝ`, where `Real.log` and
`Real.exp` are inverse, and the identities then hold over every characteristic-zero field and in
every algebra over it.
-/

public section

open Filter FormalMultilinearSeries
open scoped Nat Topology

noncomputable section

namespace NormedSpace

private def logCoeff (n : ℕ) : ℚ := -(-1) ^ n / n

private def expCoeff (n : ℕ) : ℚ := (n !)⁻¹

private def idCoeff (n : ℕ) : ℚ := if n = 1 then 1 else 0

private def oneAddCoeff (n : ℕ) : ℚ := if n = 0 ∨ n = 1 then 1 else 0

private def compCoeff (c d : ℕ → ℚ) (n : ℕ) : ℚ :=
  ∑ p : Composition n, c p.length * ∏ i, d (p.blocksFun i)

section Algebra

variable (𝕂 A : Type*) [Field 𝕂] [CharZero 𝕂] [Ring A] [Algebra 𝕂 A]
  [TopologicalSpace A] [IsTopologicalRing A]

private def ratSeries (c : ℕ → ℚ) : FormalMultilinearSeries 𝕂 A A :=
  ofScalars A fun n ↦ (c n : 𝕂)

private theorem ratSeries_comp (c d : ℕ → ℚ) :
    (ratSeries 𝕂 A c).comp (ratSeries 𝕂 A d) = ratSeries 𝕂 A (compCoeff c d) := by
  simp [ratSeries, compCoeff, ofScalars_comp_ofScalars]

private theorem logOneAddSeries_eq_ratSeries :
    logOneAddSeries 𝕂 A = ratSeries 𝕂 A logCoeff := by
  ext n v
  simp only [logOneAddSeries_apply, ratSeries, logCoeff, ofScalars, _root_.smul_apply,
    ContinuousMultilinearMap.mkPiAlgebraFin_apply]
  congr 1
  push_cast
  ring

private theorem expSeries_eq_ratSeries : expSeries 𝕂 A = ratSeries 𝕂 A expCoeff := by
  simp [expSeries_eq_ofScalars, ratSeries, expCoeff]

end Algebra

private theorem ratSeries_real_injective :
    Function.Injective (ratSeries ℝ ℝ) := fun c d h ↦ by
  funext n
  exact_mod_cast congrFun (ofScalars_series_injective ℝ ℝ h) n

section Normed

variable (𝕂 A : Type*) [NontriviallyNormedField 𝕂] [NormedRing A] [NormedAlgebra 𝕂 A]

private theorem hasFPowerSeriesAt_id_ratSeries :
    HasFPowerSeriesAt (id : A → A) (ratSeries 𝕂 A idCoeff) 0 := by
  convert (ContinuousLinearMap.id 𝕂 A).hasFPowerSeriesAt 0 using 1
  · simp
  ext n v
  rcases n with _ | _ | n <;>
    simp [ratSeries, idCoeff, ofScalars, ContinuousLinearMap.fpowerSeries]

private theorem hasFPowerSeriesAt_one_add_ratSeries :
    HasFPowerSeriesAt (fun x : A ↦ 1 + x) (ratSeries 𝕂 A oneAddCoeff) 0 := by
  convert (hasFPowerSeriesAt_const (c := (1 : A))).add (hasFPowerSeriesAt_id_ratSeries 𝕂 A)
    using 1
  · ext; simp
  ext n v
  rcases n with _ | _ | n <;> simp [ratSeries, idCoeff, oneAddCoeff, ofScalars]

end Normed

private theorem hasFPowerSeriesAt_real_exp :
    HasFPowerSeriesAt Real.exp (ratSeries ℝ ℝ expCoeff) 0 := by
  simpa only [← Real.exp_eq_exp_ℝ, expSeries_eq_ratSeries] using
    exp_hasFPowerSeriesAt_zero (𝕂 := ℝ) (𝔸 := ℝ)

private theorem compCoeff_logCoeff_expCoeff : compCoeff logCoeff expCoeff = idCoeff := by
  have hlog : HasFPowerSeriesAt Real.log (ratSeries ℝ ℝ logCoeff) (Real.exp 0) := by
    simpa [ratSeries, logCoeff] using hasFPowerSeriesAt_log_one
  apply ratSeries_real_injective
  rw [← ratSeries_comp]
  refine (hlog.comp hasFPowerSeriesAt_real_exp).eq_formalMultilinearSeries_of_eventually
    (hasFPowerSeriesAt_id_ratSeries ℝ ℝ) (.of_forall fun x ↦ ?_)
  simp

private theorem compCoeff_expCoeff_logCoeff : compCoeff expCoeff logCoeff = oneAddCoeff := by
  have hlog : HasFPowerSeriesAt (fun x ↦ Real.log (1 + x)) (ratSeries ℝ ℝ logCoeff) 0 := by
    simpa [ratSeries, logCoeff] using hasFPowerSeriesAt_log_one_add
  have hexp : HasFPowerSeriesAt Real.exp (ratSeries ℝ ℝ expCoeff) (Real.log (1 + 0)) := by
    simpa using hasFPowerSeriesAt_real_exp
  apply ratSeries_real_injective
  rw [← ratSeries_comp]
  refine (hexp.comp (f := fun x ↦ Real.log (1 + x)) hlog).eq_formalMultilinearSeries_of_eventually
    (hasFPowerSeriesAt_one_add_ratSeries ℝ ℝ) ?_
  filter_upwards [lt_mem_nhds (show (-1 : ℝ) < 0 by norm_num)] with x hx
  exact Real.exp_log (by linarith)

variable (𝕂 A : Type*) [NontriviallyNormedField 𝕂] [CharZero 𝕂] [ContinuousSMul ℚ 𝕂]
  [NormedRing A] [NormedAlgebra 𝕂 A] [CompleteSpace A]

/-- Near zero, taking `logOneAdd` after subtracting one from the exponential is the identity. -/
theorem eventually_logOneAdd_exp_sub_one :
    ∀ᶠ x in 𝓝 (0 : A), logOneAdd 𝕂 A (exp x - 1) = x := by
  have hlog : HasFPowerSeriesAt (fun y : A ↦ logOneAdd 𝕂 A (y - 1)) (logOneAddSeries 𝕂 A)
      (exp 0) := by
    simpa only [zero_add, exp_zero] using
      (hasFPowerSeriesOnBall_logOneAdd 𝕂 A).hasFPowerSeriesAt.comp_sub 1
  have h := hlog.comp (exp_hasFPowerSeriesAt_zero (𝕂 := 𝕂) (𝔸 := A))
  rw [logOneAddSeries_eq_ratSeries, expSeries_eq_ratSeries, ratSeries_comp,
    compCoeff_logCoeff_expCoeff] at h
  have hzero := h.sub (hasFPowerSeriesAt_id_ratSeries 𝕂 A)
  rw [sub_self] at hzero
  filter_upwards [hzero.eventually_eq_zero] with x hx
  exact sub_eq_zero.mp hx

/-- Near zero, exponentiating `logOneAdd` recovers one plus the argument. -/
theorem eventually_exp_logOneAdd :
    ∀ᶠ x in 𝓝 (0 : A), exp (logOneAdd 𝕂 A x) = 1 + x := by
  have hexp : HasFPowerSeriesAt (exp : A → A) (expSeries 𝕂 A) (logOneAdd 𝕂 A 0) := by
    simpa only [logOneAdd_zero] using exp_hasFPowerSeriesAt_zero (𝕂 := 𝕂) (𝔸 := A)
  have h := hexp.comp (hasFPowerSeriesOnBall_logOneAdd 𝕂 A).hasFPowerSeriesAt
  rw [logOneAddSeries_eq_ratSeries, expSeries_eq_ratSeries, ratSeries_comp,
    compCoeff_expCoeff_logCoeff] at h
  have hzero := h.sub (hasFPowerSeriesAt_one_add_ratSeries 𝕂 A)
  rw [sub_self] at hzero
  filter_upwards [hzero.eventually_eq_zero] with x hx
  exact sub_eq_zero.mp hx

end NormedSpace
