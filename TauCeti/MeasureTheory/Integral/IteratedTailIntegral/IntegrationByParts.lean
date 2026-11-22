/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import TauCeti.MeasureTheory.Integral.IteratedTailIntegral.Basic

import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.MeasureTheory.Integral.Asymptotics
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Basic
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Primitive

/-!
# Improper integration by parts for iterated tail integrals

This file establishes improper integration by parts on `(a, ∞)` for a possibly conditionally
convergent improper tail integral `TauCeti.iteratedTailIntegral g 1` against a `C¹` scalar weight
`φ` whose derivative is integrable on `(a, ∞)`.

## Main results

* `TauCeti.integral_Ioi_smul_eq_of_tendsto`: if `g` is locally integrable on `[a, ∞)` with
  convergent (possibly only conditionally) improper integral `R ↦ ∫ t in a..R, g t`, `φ` is `C¹`
  with `deriv φ` integrable on `(a, ∞)`, and `t ↦ φ t • g t` is Bochner integrable on `(a, ∞)`,
  then `s ↦ deriv φ s • iteratedTailIntegral g 1 s` is integrable on `(a, ∞)` and
  `∫ t in Ioi a, φ t • g t = φ a • iteratedTailIntegral g 1 a +
    ∫ s in Ioi a, deriv φ s • iteratedTailIntegral g 1 s`.
-/

public section

namespace TauCeti

open Asymptotics Filter MeasureTheory Set Topology
open scoped Interval

/-- Improper integration by parts on `(a, ∞)` for `G := iteratedTailIntegral g 1`: if `g` is
locally integrable on `[a, ∞)` with convergent (possibly only conditionally) improper integral
`R ↦ ∫ t in a..R, g t`, `φ` is `C¹` with `deriv φ` integrable on `(a, ∞)`, and `t ↦ φ t • g t` is
Bochner integrable on `(a, ∞)`, then `s ↦ deriv φ s • G s` is integrable on `(a, ∞)` and
`∫ t in Ioi a, φ t • g t = φ a • G a + ∫ s in Ioi a, deriv φ s • G s`. (When `E` is incomplete,
both integrals and `G` vanish.) -/
theorem integral_Ioi_smul_eq_of_tendsto {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ : ℝ → ℝ} {g : ℝ → E} {a : ℝ}
    (hg_loc : LocallyIntegrableOn g (Ici a))
    (hg_conv : ∃ L, Tendsto (fun R : ℝ ↦ ∫ t in a..R, g t) atTop (𝓝 L))
    (hφ : ContDiff ℝ 1 φ) (hφ'_int : IntegrableOn (deriv φ) (Ioi a))
    (hφg_int : IntegrableOn (fun t ↦ φ t • g t) (Ioi a)) :
    IntegrableOn (fun s ↦ deriv φ s • iteratedTailIntegral g 1 s) (Ioi a) ∧
      ∫ t in Ioi a, φ t • g t =
        φ a • iteratedTailIntegral g 1 a +
          ∫ s in Ioi a, deriv φ s • iteratedTailIntegral g 1 s := by
  by_cases hE : CompleteSpace E
  swap
  · simp only [iteratedTailIntegral_succ_of_not_completeSpace hE g 0, smul_zero,
      integral_of_not_completeSpace hE, add_zero, and_true]
    exact integrableOn_zero
  obtain ⟨L, hL⟩ := hg_conv
  set G := iteratedTailIntegral g 1
  have hG_cont : ContinuousOn G (Ici a) := continuousOn_iteratedTailIntegral_one hg_loc
  have hG_top : Tendsto G atTop (𝓝 0) := tendsto_iteratedTailIntegral_one_atTop hg_loc hL
  have hφ'G_int : IntegrableOn (fun s ↦ deriv φ s • G s) (Ioi a) :=
    hφ'_int.smul_of_continuousOn_of_isBigO_one Ioi_subset_Ici_self hG_cont (hG_top.isBigO_one ℝ)
  have hφ_eq (R : ℝ) : ∫ s in a..R, deriv φ s = φ R - φ a :=
    _root_.intervalIntegral.integral_deriv_eq_sub (fun s _ ↦ hφ.differentiable one_ne_zero s)
      ((hφ.continuous_deriv le_rfl).intervalIntegrable a R)
  have hφ_top : Tendsto φ atTop (𝓝 (φ a + ∫ s in Ioi a, deriv φ s)) := by
    simpa only [id_eq, hφ_eq, add_sub_cancel] using
      (intervalIntegral_tendsto_integral_Ioi a hφ'_int tendsto_id).const_add (φ a)
  have hRHS : Tendsto (fun R : ℝ ↦
      φ a • G a - φ R • G R + ∫ s in a..R, deriv φ s • G s) atTop
      (𝓝 (φ a • G a + ∫ s in Ioi a, deriv φ s • G s)) := by
    simpa using (tendsto_const_nhds.sub (hφ_top.smul hG_top)).add
      (intervalIntegral_tendsto_integral_Ioi a hφ'G_int tendsto_id)
  refine ⟨hφ'G_int, tendsto_nhds_unique (intervalIntegral_tendsto_integral_Ioi a hφg_int tendsto_id)
    (hRHS.congr' ?_)⟩
  filter_upwards [eventually_ge_atTop a] with R hR
  have hibp := TauCeti.intervalIntegral.integral_deriv_smul_primitive_eq_sub_of_le hR hφ
    (hg_loc.intervalIntegrable (ordConnected_Ici.uIcc_subset le_rfl hR))
  have hφ'G_sub : ∫ s in a..R, deriv φ s • (∫ t in a..s, g t) =
      (φ R - φ a) • G a - ∫ s in a..R, deriv φ s • G s := by
    rw [← hφ_eq, ← _root_.intervalIntegral.integral_smul_const,
      ← _root_.intervalIntegral.integral_sub
        ((hφ.continuous_deriv le_rfl).continuousOn.fun_smul continuousOn_const).intervalIntegrable
        (((hφ.continuous_deriv le_rfl).continuousOn.fun_smul
          (hG_cont.mono (Icc_subset_Ici_self))).intervalIntegrable_of_Icc hR)]
    refine _root_.intervalIntegral.integral_congr fun s hs ↦ ?_
    rw [← iteratedTailIntegral_one_sub_eq_intervalIntegral hg_loc le_rfl le_rfl
      (ordConnected_Ici.uIcc_subset le_rfl hR hs) hL, smul_sub]
  have hlhs : ∫ t in a..R, φ t • g t = φ R • (G a - G R) -
      ((φ R - φ a) • G a - ∫ s in a..R, deriv φ s • G s) := by
    rw [iteratedTailIntegral_one_sub_eq_intervalIntegral hg_loc le_rfl le_rfl hR hL, ← hφ'G_sub,
      hibp, sub_sub_cancel]
  rw [id, hlhs, smul_sub, sub_smul]
  abel

end TauCeti
