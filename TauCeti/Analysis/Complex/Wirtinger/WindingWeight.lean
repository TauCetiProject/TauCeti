/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Basic
public import TauCeti.Analysis.Green.WindingWeight.Cycle

/-!
# Integrability of winding weights against Wirtinger derivatives

For a contour cycle `C` lying in an open set `U` (`C.IsIn U`) and null-homologous in `U`
(`C.IsNullHomologous U`), and a map `F : ℂ → E` that is real `C¹` on `U` (`ContDiffOn ℝ 1 F U`),
the trace-zero winding weight `C.windingWeight` multiplied by `∂F` or `\bar∂ F` is integrable on
`U`.

## Main results

* `TauCeti.Contour.Cycle.integrableOn_windingWeight_smul_conjWirtingerDeriv`
* `TauCeti.Contour.Cycle.integrableOn_windingWeight_smul_wirtingerDeriv`
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti.Contour.Cycle

/-- For `C` in an open set `U` and null-homologous in `U`, `z ↦ C.windingWeight z • \bar∂ F(z)` is
integrable on `U` whenever `F` is real `C¹` on `U`. -/
theorem integrableOn_windingWeight_smul_conjWirtingerDeriv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (C : Cycle) {U : Set ℂ} {F : ℂ → E} (hU : IsOpen U) (htrace : C.IsIn U)
    (hnull : C.IsNullHomologous U) (hF : ContDiffOn ℝ 1 F U) :
    IntegrableOn (fun z ↦ C.windingWeight z • conjWirtingerDeriv F z 1) U :=
  C.integrableOn_windingWeight_smul htrace hnull
    (hF.conjWirtingerDeriv_apply_of_isOpen hU (m := 0) (by simp) 1).continuousOn

/-- For `C` in an open set `U` and null-homologous in `U`, `z ↦ C.windingWeight z • ∂ F(z)` is
integrable on `U` whenever `F` is real `C¹` on `U`. -/
theorem integrableOn_windingWeight_smul_wirtingerDeriv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (C : Cycle) {U : Set ℂ} {F : ℂ → E} (hU : IsOpen U) (htrace : C.IsIn U)
    (hnull : C.IsNullHomologous U) (hF : ContDiffOn ℝ 1 F U) :
    IntegrableOn (fun z ↦ C.windingWeight z • wirtingerDeriv F z 1) U :=
  C.integrableOn_windingWeight_smul htrace hnull
    (hF.wirtingerDeriv_apply_of_isOpen hU (m := 0) (by simp) 1).continuousOn

end TauCeti.Contour.Cycle

end
