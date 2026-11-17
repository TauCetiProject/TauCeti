/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.Basic

/-!
# Bump functions with support in a ball

On a real normed space with smooth bump functions, every open ball contains the topological
support of a smooth bump function centred at its centre. This file defines the explicit concentric
bump parameters `TauCeti.ballBump` (`rIn = ρ / 4`, `rOut = ρ / 2`) together with the existential
witness `TauCeti.exists_contDiffBump_tsupport_subset_ball`.

## Main definitions

* `TauCeti.ballBump`: smooth bump parameters centered at `x₀` with `rIn = ρ / 4` and `rOut = ρ / 2`.

## Main results

* `TauCeti.exists_contDiffBump_tsupport_subset_ball`: a bump centred at `c` whose topological
  support lies in the ball of radius `r` around `c`.
-/

public section

open Metric

namespace TauCeti

/-- Smooth bump parameters centered at `x₀` with inner radius `ρ / 4` and outer radius `ρ / 2`, so
`Metric.closedBall x₀ (ρ / 2)` sits strictly inside `Metric.ball x₀ ρ`. -/
noncomputable def ballBump {E : Type*} (x₀ : E) {ρ : ℝ} (hρ : 0 < ρ) : ContDiffBump x₀ :=
  ⟨ρ / 4, ρ / 2, by positivity, by linarith⟩

@[simp]
theorem ballBump_rIn {E : Type*} (x₀ : E) {ρ : ℝ} (hρ : 0 < ρ) :
    (ballBump x₀ hρ).rIn = ρ / 4 :=
  (rfl)

@[simp]
theorem ballBump_rOut {E : Type*} (x₀ : E) {ρ : ℝ} (hρ : 0 < ρ) :
    (ballBump x₀ hρ).rOut = ρ / 2 :=
  (rfl)

/-- A smooth bump function centred at `c` whose topological support lies in the ball of radius
`r > 0` around `c`. -/
theorem exists_contDiffBump_tsupport_subset_ball {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [HasContDiffBump E] (c : E) {r : ℝ} (hr : 0 < r) :
    ∃ b : ContDiffBump c, tsupport b ⊆ ball c r :=
  ⟨ballBump c hr, by
    rw [ContDiffBump.tsupport_eq, ballBump_rOut]
    exact closedBall_subset_ball (half_lt_self hr)⟩

end TauCeti
