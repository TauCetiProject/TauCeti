/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Realizing compactly supported continuous functions in `Lᵖ`

Every compactly supported continuous function `f : C_c(X, E)` belongs to `ℒp(X, μ; E)` whenever the
measure `μ` is finite on compact sets (`IsFiniteMeasureOnCompacts μ`) and open sets are measurable
(`OpensMeasurableSpace X`). This file packages the resulting canonical linear map
`CompactlySupportedContinuousMap.toLp p μ 𝕜 : C_c(X, E) →ₗ[𝕜] Lp E p μ`, together with its
almost-everywhere representative, `Lᵖ` norm formula, and injectivity under `μ.IsOpenPosMeasure`.

None of these basic constructions require local compactness, `R₁` separation, regularity, or
Urysohn's lemma; density of the range in `Lp E p μ` for `p < ∞` on locally compact `R₁` spaces is
proved separately in `TauCeti.MeasureTheory.Function.Lp.LocallyCompact`.

## Main definitions

* `CompactlySupportedContinuousMap.toLp`: realize a compactly supported continuous function in
  `C_c(X, E)` as an `Lᵖ` class.

## Main results

* `CompactlySupportedContinuousMap.memLp`: every `f : C_c(X, E)` belongs to `MemLp f p μ`.
* `CompactlySupportedContinuousMap.coeFn_toLp`: `toLp p μ 𝕜 f` is represented a.e. by `f`.
* `CompactlySupportedContinuousMap.norm_toLp`: `‖toLp p μ 𝕜 f‖ = ENNReal.toReal (eLpNorm f p μ)`.
* `CompactlySupportedContinuousMap.toLp_injective` and `CompactlySupportedContinuousMap.toLp_inj`:
  `toLp` is injective when `μ` gives positive measure to every nonempty open set.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal CompactlySupported

namespace CompactlySupportedContinuousMap

variable {X E : Type*} [TopologicalSpace X] [MeasurableSpace X] [NormedAddCommGroup E]

/-- Every compactly supported continuous function belongs to `ℒp` for a measure that is finite on
compact sets. -/
theorem memLp [OpensMeasurableSpace X] (f : C_c(X, E)) (p : ℝ≥0∞) (μ : Measure X)
    [IsFiniteMeasureOnCompacts μ] : MemLp f p μ :=
  f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport

/-- Realize a compactly supported continuous function as an `Lᵖ` class. -/
def toLp [OpensMeasurableSpace X] (p : ℝ≥0∞) (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
    (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] :
    C_c(X, E) →ₗ[𝕜] Lp E p μ where
  toFun f := (f.memLp p μ).toLp f
  map_add' f g := by
    simpa only [coe_add] using MemLp.toLp_add (f.memLp p μ) (g.memLp p μ)
  map_smul' c f := by
    simpa only [coe_smul, RingHom.id_apply] using MemLp.toLp_const_smul c (f.memLp p μ)

/-- `toLp p μ 𝕜 f` is the `Lᵖ` class `(f.memLp p μ).toLp f`. -/
theorem toLp_apply [OpensMeasurableSpace X] {p : ℝ≥0∞} {μ : Measure X}
    [IsFiniteMeasureOnCompacts μ] (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
    (f : C_c(X, E)) :
    toLp p μ 𝕜 f = (f.memLp p μ).toLp f :=
  (rfl)

/-- The `Lᵖ` class of a compactly supported continuous function is represented by that function. -/
theorem coeFn_toLp [OpensMeasurableSpace X] {p : ℝ≥0∞} {μ : Measure X}
    [IsFiniteMeasureOnCompacts μ] (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
    (f : C_c(X, E)) :
    toLp p μ 𝕜 f =ᵐ[μ] f :=
  (f.memLp p μ).coeFn_toLp

/-- The `Lᵖ` norm of `toLp p μ 𝕜 f` is the `ℒp` seminorm of `f`. -/
@[simp]
theorem norm_toLp [OpensMeasurableSpace X] {p : ℝ≥0∞} {μ : Measure X}
    [IsFiniteMeasureOnCompacts μ] (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
    (f : C_c(X, E)) :
    ‖toLp p μ 𝕜 f‖ = ENNReal.toReal (eLpNorm f p μ) :=
  Lp.norm_toLp f (f.memLp p μ)

/-- For a measure giving positive mass to nonempty open sets, `toLp` is injective on `C_c(X, E)`. -/
theorem toLp_injective [OpensMeasurableSpace X] (p : ℝ≥0∞) (μ : Measure X)
    [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure] (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E]
    [IsBoundedSMul 𝕜 E] :
    Function.Injective (toLp (X := X) (E := E) p μ 𝕜) := by
  intro f g hfg
  apply DFunLike.coe_injective
  exact Measure.eq_of_ae_eq
    ((coeFn_toLp 𝕜 f).symm.trans ((Lp.ext_iff.1 hfg).trans (coeFn_toLp 𝕜 g)))
    f.continuous g.continuous

@[simp]
theorem toLp_inj [OpensMeasurableSpace X] {p : ℝ≥0∞} {μ : Measure X}
    [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure] (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E]
    [IsBoundedSMul 𝕜 E] {f g : C_c(X, E)} :
    toLp p μ 𝕜 f = toLp p μ 𝕜 g ↔ f = g :=
  (toLp_injective p μ 𝕜).eq_iff

end CompactlySupportedContinuousMap
