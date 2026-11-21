/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.MeasureTheory.Integral.Asymptotics

import TauCeti.Analysis.Asymptotics.Lemmas

/-!
# Integrability from asymptotics at infinity

On a finite-dimensional real normed space of dimension `d`, a locally integrable function which is
`O((1 + ‖x‖) ^ (-r))` at infinity for some `r > d` is integrable, for every additive Haar measure
(`MeasureTheory.LocallyIntegrable.integrable_of_isBigO_one_add_norm_rpow_neg`). This combines
Mathlib's integrability of the Japanese bracket (`integrable_one_add_norm`) with its criterion
`MeasureTheory.LocallyIntegrable.integrable_of_isBigO_cocompact`.

On `ℝ`, `MeasureTheory.IntegrableOn.smul_of_continuousOn_of_isBigO_one` multiplies an integrable
weight on `s ⊆ [a, ∞)` by a function continuous on `[a, ∞)` and bounded at `+∞`.
-/

public section

namespace MeasureTheory

open Asymptotics Filter Module Set

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] {f : E → F}

/-- A locally integrable function on a finite-dimensional real normed space which is
`O((1 + ‖x‖) ^ (-r))` at infinity, with `r` larger than the dimension, is integrable. -/
theorem LocallyIntegrable.integrable_of_isBigO_one_add_norm_rpow_neg
    (hf : LocallyIntegrable f μ) {r : ℝ} (hr : (finrank ℝ E : ℝ) < r)
    (ho : f =O[cocompact E] fun x ↦ (1 + ‖x‖) ^ (-r)) : Integrable f μ :=
  hf.integrable_of_isBigO_cocompact ho ((integrable_one_add_norm hr).integrableAtFilter _)

/-- If `w` is integrable on `s ⊆ [a, ∞)` and `h` is continuous on `[a, ∞)` and bounded at `+∞`
(`h =O[atTop] (1 : ℝ → ℝ)`), then `t ↦ w t • h t` is integrable on `s`. -/
theorem IntegrableOn.smul_of_continuousOn_of_isBigO_one {R E : Type*}
    [NormedRing R] [NormedAddCommGroup E] [Module R E] [IsBoundedSMul R E]
    {μ : Measure ℝ} {w : ℝ → R} {h : ℝ → E} {a : ℝ} {s : Set ℝ}
    (hw : IntegrableOn w s μ) (hs : s ⊆ Ici a)
    (hh_cont : ContinuousOn h (Ici a)) (hh_top : h =O[atTop] (1 : ℝ → ℝ)) :
    IntegrableOn (fun t ↦ w t • h t) s μ := by
  obtain ⟨C, hC⟩ := Asymptotics.isBigO_principal.mp
    (hh_top.isBigO_principal_Ici_of_continuousOn hh_cont continuousOn_const fun _ _ ↦ one_ne_zero)
  exact hw.smul_bdd C ((hh_cont.aestronglyMeasurable measurableSet_Ici).mono_set hs)
    (ae_mono (Measure.restrict_mono hs le_rfl)
      (ae_restrict_of_forall_mem measurableSet_Ici fun t ht ↦ by simpa using hC t ht))

end MeasureTheory
