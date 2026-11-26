/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.Flow
public import TauCeti.RepresentationTheory.Continuous.LpKoopman

/-!
# The `Lᵖ` pullback representation of a measure-preserving real flow

A continuous real flow `ϕ : Flow ℝ X` is an action of the additive group `ℝ`, hence of the
multiplicative group `Multiplicative ℝ`. When every time-`t` map preserves a measure `μ`, the
`Lᵖ` pullback representation `TauCeti.lpKoopman` of this action is
`Flow.lpKoopman 𝕜 E p μ ϕ hϕ : ContRepresentation 𝕜 (Multiplicative ℝ) (Lp E p μ)`, with
`U_t f = f ∘ ϕ (-t)` almost everywhere (`Flow.coeFn_lpKoopman`), `U_0 = 1`
(`Flow.lpKoopman_zero`), `U_(s + t) = U_s U_t` (`Flow.lpKoopman_add`) and `‖U_t f‖ = ‖f‖`
(`Flow.norm_lpKoopman_apply`). For a Borel measure on an R₁ space that is inner regular for
compact sets on sets of finite measure and locally finite, and `p ≠ ∞`, the orbits
`t ↦ U_t f` are continuous (`Flow.continuous_lpKoopman_apply`).

## Main definitions

* `Flow.lpKoopman 𝕜 E p μ ϕ hϕ`: the representation `ofAdd t ↦ (f ↦ f ∘ ϕ (-t))` on `Lp E p μ`.
-/

public section

namespace Flow

open MeasureTheory TauCeti
open scoped ENNReal

variable {X 𝕜 E : Type*} [TopologicalSpace X] [MeasurableSpace X] [NormedRing 𝕜]
  [NormedAddCommGroup E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
  (p : ℝ≥0∞) [Fact (1 ≤ p)] (μ : Measure X) (ϕ : Flow ℝ X)
  (hϕ : ∀ t, MeasurePreserving (ϕ t) μ μ)

variable (𝕜 E) in
/-- The `Lᵖ` pullback representation of a measure-preserving real flow, as a representation of
`Multiplicative ℝ`: `U_t f = f ∘ ϕ (-t)`. -/
noncomputable def lpKoopman : ContRepresentation 𝕜 (Multiplicative ℝ) (Lp E p μ) :=
  letI := ϕ.toAddAction
  TauCeti.lpKoopman 𝕜 E p μ fun g ↦ hϕ (Multiplicative.toAdd g)

variable {p μ ϕ hϕ}

/-- `U_t` is the pullback along `ϕ (-t)`. -/
theorem lpKoopman_apply (t : ℝ) (f : Lp E p μ) :
    lpKoopman 𝕜 E p μ ϕ hϕ (Multiplicative.ofAdd t) f =
      Lp.compMeasurePreserving (ϕ (-t)) (hϕ (-t)) f :=
  letI := ϕ.toAddAction
  TauCeti.lpKoopman_apply (Multiplicative.ofAdd t) f

/-- `(U_t f)(x) = f (ϕ (-t) x)` for almost every `x`. -/
theorem coeFn_lpKoopman (t : ℝ) (f : Lp E p μ) :
    lpKoopman 𝕜 E p μ ϕ hϕ (Multiplicative.ofAdd t) f =ᵐ[μ] fun x ↦ f (ϕ (-t) x) := by
  rw [lpKoopman_apply]
  exact Lp.coeFn_compMeasurePreserving f (hϕ (-t))

/-- `U_0` is the identity. -/
theorem lpKoopman_zero : lpKoopman 𝕜 E p μ ϕ hϕ (Multiplicative.ofAdd 0) = 1 := by
  rw [ofAdd_zero, map_one]

/-- `U_(s + t) = U_s U_t`. -/
theorem lpKoopman_add (s t : ℝ) :
    lpKoopman 𝕜 E p μ ϕ hϕ (Multiplicative.ofAdd (s + t)) =
      lpKoopman 𝕜 E p μ ϕ hϕ (Multiplicative.ofAdd s) *
        lpKoopman 𝕜 E p μ ϕ hϕ (Multiplicative.ofAdd t) := by
  rw [ofAdd_add, map_mul]

/-- Each `U_t` is an isometry. -/
@[simp]
theorem norm_lpKoopman_apply (g : Multiplicative ℝ) (f : Lp E p μ) :
    ‖lpKoopman 𝕜 E p μ ϕ hϕ g f‖ = ‖f‖ :=
  letI := ϕ.toAddAction
  TauCeti.norm_lpKoopman_apply g f

/-- For a Borel measure on an R₁ space, inner regular for compact sets on sets of finite measure
and locally finite, and `p ≠ ∞`, the orbit `t ↦ U_t f` of a continuous measure-preserving flow is
continuous. -/
theorem continuous_lpKoopman_apply [BorelSpace X] [R1Space X] [μ.InnerRegularCompactLTTop]
    [IsLocallyFiniteMeasure μ] (hp : p ≠ ∞) (f : Lp E p μ) :
    Continuous fun t : ℝ ↦ lpKoopman 𝕜 E p μ ϕ hϕ (Multiplicative.ofAdd t) f := by
  let := ϕ.toAddAction
  have : ContinuousSMul (Multiplicative ℝ) X :=
    ⟨ϕ.cont'.comp (continuous_toAdd.prodMap continuous_id)⟩
  exact (TauCeti.continuous_lpKoopman_apply hp f).comp continuous_ofAdd

end Flow
