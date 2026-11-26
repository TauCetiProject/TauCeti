/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Involution

/-!
# Restricting families of bounded operators to eigenspaces

An operator `T` intertwining continuous linear endomorphisms `σE` and `σF` of normed spaces
restricts to an operator `ContinuousLinearMap.restrictEigenspace` between their `μ`-eigenspaces.
The restriction does not increase the operator norm, so restricting a continuous family of
intertwining operators gives a continuous family (`ContinuousOn.restrictEigenspace`).
-/

public section

variable {𝕜 E F X : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace X] {σE : E →L[𝕜] E}
  {σF : F →L[𝕜] F} {T : X → E →L[𝕜] F} {s : Set X}

/-- Restricting a family of operators intertwining `σE` and `σF` to `μ`-eigenspaces preserves
continuity: restriction does not increase the operator norm of differences. -/
theorem ContinuousOn.restrictEigenspace (hT : ContinuousOn T s)
    (hTσ : ∀ x, (T x).comp σE = σF.comp (T x)) (μ : 𝕜) :
    ContinuousOn (fun x ↦ (T x).restrictEigenspace (hTσ x) μ) s := by
  have hle (x y : X) : ‖(T x).restrictEigenspace (hTσ x) μ - (T y).restrictEigenspace (hTσ y) μ‖ ≤
      ‖T x - T y‖ :=
    ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v ↦ by
      simpa using (T x - T y).le_opNorm v
  intro x hx
  have hTx := hT x hx
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero] at hTx ⊢
  exact squeeze_zero (fun _ ↦ norm_nonneg _) (fun y ↦ hle y x) hTx
