/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoxIntegral.Oriented.Basic
import TauCeti.Analysis.BoxIntegral.Oriented.Calculus
import TauCeti.Topology.Path.Extend.Basic
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic

/-!
# Agreement of Henstock and Bochner curve integrals

Mathlib's `CurveIntegrable` supplies genuine Bochner integrability of `curveIntegralFun`.
Its Henstock integral therefore has the same value as Mathlib's `curveIntegral`, by the
oriented interval compatibility theorem. The comparison retains the integrability hypothesis.
Constant-projection paths have zero Henstock coordinate integral without regularity assumptions.
-/

public section

open MeasureTheory Set

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  {a b : E} {ω : E → E →L[𝕜] F} {γ : Path a b}

/-- A Bochner-integrable one-form along a path has its actual curve-integral value as a
Henstock integral of Mathlib's curve integrand on the unit parameter interval. -/
theorem CurveIntegrable.hasHenstockIntervalIntegral (h : CurveIntegrable ω γ) :
    let : NormedSpace ℝ F := .restrictScalars ℝ 𝕜 F
    TauCeti.BoxIntegral.HasHenstockIntervalIntegral (curveIntegralFun ω γ) 0 1
      (curveIntegral ω γ) := by
  let : NormedSpace ℝ F := .restrictScalars ℝ 𝕜 F
  rw [curveIntegral_def]
  exact IntervalIntegrable.hasHenstockIntervalIntegral h

/-- Under genuine curve integrability, any Henstock value of Mathlib's curve integrand
agrees with its Bochner curve integral. -/
theorem TauCeti.BoxIntegral.HasHenstockIntervalIntegral.eq_curveIntegral {y : F}
    (h : letI : NormedSpace ℝ F := .restrictScalars ℝ 𝕜 F
      TauCeti.BoxIntegral.HasHenstockIntervalIntegral (curveIntegralFun ω γ) 0 1 y)
    (hω : CurveIntegrable ω γ) : y = curveIntegral ω γ := by
  let : NormedSpace ℝ F := .restrictScalars ℝ 𝕜 F
  exact h.unique hω.hasHenstockIntervalIntegral

/-- Every path with constant selected coordinate has zero gauge coordinate integral. -/
theorem TauCeti.BoxIntegral.hasIntegral_Henstock_of_path_projection_constant {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] (L : V →L[ℝ] ℝ) {p q : V} (γ : Path p q)
    (hγ : ∀ t : unitInterval, L (γ t) = L p) (P : V → ℝ) :
    BoxIntegral.HasIntegral (TauCeti.BoxIntegral.intervalBox 0 1 zero_lt_one)
      BoxIntegral.IntegrationParams.Henstock
      (fun t ↦ P (γ.extend (t 0)) * L (deriv γ.extend (t 0)))
      BoxIntegral.BoxAdditiveMap.volume 0 := by
  have hc (t : ℝ) : L (γ.extend t) = L p :=
    (γ.forall_extend_iff (P := fun z ↦ L z = L p)).mpr hγ t
  have hi := TauCeti.BoxIntegral.hasHenstockIntervalIntegral_of_projection_constant
    L (a := 0) (b := 1)
    (γ := γ.extend) (c := L p) hc P
  rw [TauCeti.BoxIntegral.hasHenstockIntervalIntegral_iff_of_lt zero_lt_one] at hi
  exact hi
