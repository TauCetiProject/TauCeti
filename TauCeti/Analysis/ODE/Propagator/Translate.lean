/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.Propagator
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Translating the time variable of a propagator

For a coefficient `P` integrable on `[a, b]` and a real `c`, the propagator of the translated
coefficient `u ↦ P (u + c)` is the translate of the propagator of `P`:
`N_{P(· + c)}(t, s) = N_P(t + c, s + c)` for `s, t ∈ [a - c, b - c]`
(`TauCeti.propagator_comp_add_right`). Both sides solve the same operator equation, after the
change of variables `u ↦ u + c` in its integral.
-/

public section

open MeasureTheory Set intervalIntegral

namespace TauCeti

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
  [CompleteSpace E] {P : ℝ → E →L[𝕜] E} {a b s t : ℝ}

/-- **Translating time.** If `P` is integrable on `[a, b]` and `s, t ∈ [a - c, b - c]`, then the
propagator of `u ↦ P (u + c)` is `N_{P(· + c)}(t, s) = N_P(t + c, s + c)`. -/
theorem propagator_comp_add_right (hP : IntegrableOn P (Icc a b)) {c : ℝ}
    (hs : s ∈ Icc (a - c) (b - c)) (ht : t ∈ Icc (a - c) (b - c)) :
    propagator (fun u ↦ P (u + c)) t s = propagator P (t + c) (s + c) := by
  have hmem {r : ℝ} (hr : r ∈ Icc (a - c) (b - c)) : r + c ∈ Icc a b :=
    ⟨by linarith [hr.1], by linarith [hr.2]⟩
  refine propagator_eq_of_forall_mem_Icc (hP.comp_add_right_Icc c) hs ht
    (N := fun r ↦ propagator P (r + c) (s + c)) ?_ fun r hr ↦ ?_
  · exact (continuousOn_propagator_left hP (hmem hs)).comp
      (continuous_id.add continuous_const).continuousOn fun r hr ↦ hmem hr
  · rw [propagator_eq_one_add_integral hP (hmem hs) (hmem hr),
      ← intervalIntegral.integral_comp_add_right (fun u ↦ P u ∘L propagator P u (s + c)) c]

end TauCeti
