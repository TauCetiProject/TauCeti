/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.Flow
public import TauCeti.RepresentationTheory.Continuous.LpKoopman

/-!
# The `Lᵖ` pullback representation of a measure-preserving flow

A continuous flow `ϕ : Flow τ X` of an additive group `τ` (for instance a real flow, `τ = ℝ`)
is an action of `τ`, hence of the multiplicative group `Multiplicative τ`. When every time-`t`
map preserves a measure `μ`, the `Lᵖ` pullback representation `TauCeti.lpKoopman` of this action
is `Flow.lpKoopman 𝕜 E p μ ϕ hϕ : ContRepresentation 𝕜 (Multiplicative τ) (Lp E p μ)`, with
`U_t f = f ∘ ϕ (-t)` almost everywhere (`Flow.coeFn_lpKoopman`), `U_0 = 1`
(`Flow.lpKoopman_zero`), `U_(s + t) = U_s U_t` (`Flow.lpKoopman_add`) and `‖U_t f‖ = ‖f‖`
(`Flow.norm_lpKoopman_apply`). For `p = 2` and a Hilbert space `E` it is unitary
(`Flow.isUnitary_lpKoopman`, `Flow.star_lpKoopman`). If negation on `τ` is continuous, then for
a Borel measure on an R₁ space that is inner regular for compact sets on sets of finite measure
and locally finite, and `p ≠ ∞`, the orbits `t ↦ U_t f` are continuous
(`Flow.continuous_lpKoopman_apply`).

## Main definitions

* `Flow.lpKoopman 𝕜 E p μ ϕ hϕ`: the representation `ofAdd t ↦ (f ↦ f ∘ ϕ (-t))` on `Lp E p μ`.
-/

public section

namespace Flow

open MeasureTheory TauCeti
open scoped ENNReal

variable {τ X 𝕜 E : Type*} [TopologicalSpace τ] [AddGroup τ] [TopologicalSpace X]
  [MeasurableSpace X] [NormedRing 𝕜] [NormedAddCommGroup E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
  (p : ℝ≥0∞) [Fact (1 ≤ p)] (μ : Measure X) (ϕ : Flow τ X)
  (hϕ : ∀ t, MeasurePreserving (ϕ t) μ μ)

variable (𝕜 E) in
/-- The `Lᵖ` pullback representation of a measure-preserving flow, as a representation of
`Multiplicative τ`: `U_t f = f ∘ ϕ (-t)`. -/
noncomputable def lpKoopman : ContRepresentation 𝕜 (Multiplicative τ) (Lp E p μ) :=
  letI := ϕ.toAddAction
  TauCeti.lpKoopman 𝕜 E p μ fun g ↦ hϕ (Multiplicative.toAdd g)

variable {p μ ϕ hϕ}

/-- `U_t` is the pullback along `ϕ (-t)`. -/
theorem lpKoopman_apply (t : τ) (f : Lp E p μ) :
    lpKoopman 𝕜 E p μ ϕ hϕ (Multiplicative.ofAdd t) f =
      Lp.compMeasurePreserving (ϕ (-t)) (hϕ (-t)) f :=
  letI := ϕ.toAddAction
  -- `(ofAdd t)⁻¹ • x` is `ϕ (-t) x` by definition of `Multiplicative` and `Flow.toAddAction`.
  TauCeti.lpKoopman_apply (Multiplicative.ofAdd t) f

/-- `(U_t f)(x) = f (ϕ (-t) x)` for almost every `x`. -/
theorem coeFn_lpKoopman (t : τ) (f : Lp E p μ) :
    lpKoopman 𝕜 E p μ ϕ hϕ (Multiplicative.ofAdd t) f =ᵐ[μ] fun x ↦ f (ϕ (-t) x) := by
  rw [lpKoopman_apply]
  exact Lp.coeFn_compMeasurePreserving f (hϕ (-t))

/-- `U_0` is the identity. -/
theorem lpKoopman_zero : lpKoopman 𝕜 E p μ ϕ hϕ (Multiplicative.ofAdd 0) = 1 := by
  rw [ofAdd_zero, map_one]

/-- `U_(s + t) = U_s U_t`. -/
theorem lpKoopman_add (s t : τ) :
    lpKoopman 𝕜 E p μ ϕ hϕ (Multiplicative.ofAdd (s + t)) =
      lpKoopman 𝕜 E p μ ϕ hϕ (Multiplicative.ofAdd s) *
        lpKoopman 𝕜 E p μ ϕ hϕ (Multiplicative.ofAdd t) := by
  rw [ofAdd_add, map_mul]

/-- Each `U_t` is an isometry. -/
@[simp]
theorem norm_lpKoopman_apply (g : Multiplicative τ) (f : Lp E p μ) :
    ‖lpKoopman 𝕜 E p μ ϕ hϕ g f‖ = ‖f‖ :=
  letI := ϕ.toAddAction
  TauCeti.norm_lpKoopman_apply g f

/-- The `L²` pullback representation of a measure-preserving flow is unitary. -/
theorem isUnitary_lpKoopman {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] : (lpKoopman 𝕜 E 2 μ ϕ hϕ).IsUnitary :=
  letI := ϕ.toAddAction
  TauCeti.isUnitary_lpKoopman

/-- On a Hilbert space `E`, the operator `star` of the `L²` pullback by `g` is the pullback by
`g⁻¹`. -/
@[simp]
theorem star_lpKoopman {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [CompleteSpace E] (g : Multiplicative τ) :
    star (lpKoopman 𝕜 E 2 μ ϕ hϕ g) = lpKoopman 𝕜 E 2 μ ϕ hϕ g⁻¹ :=
  letI := ϕ.toAddAction
  TauCeti.star_lpKoopman g

/-- If negation on `τ` is continuous, then for a Borel measure on an R₁ space, inner regular for
compact sets on sets of finite measure and locally finite, and `p ≠ ∞`, the orbit `t ↦ U_t f` of
a continuous measure-preserving flow is continuous. -/
theorem continuous_lpKoopman_apply [ContinuousNeg τ] [BorelSpace X] [R1Space X]
    [μ.InnerRegularCompactLTTop] [IsLocallyFiniteMeasure μ] (hp : p ≠ ∞) (f : Lp E p μ) :
    Continuous fun t : τ ↦ lpKoopman 𝕜 E p μ ϕ hϕ (Multiplicative.ofAdd t) f := by
  let := ϕ.toAddAction
  -- `g • x` is `ϕ (toAdd g) x` by definition of `Multiplicative` and `Flow.toAddAction`.
  have : ContinuousSMul (Multiplicative τ) X :=
    ⟨ϕ.cont'.comp (continuous_toAdd.prodMap continuous_id)⟩
  exact (TauCeti.continuous_lpKoopman_apply hp f).comp continuous_ofAdd

end Flow
