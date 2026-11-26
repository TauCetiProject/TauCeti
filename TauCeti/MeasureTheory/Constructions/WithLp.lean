/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Product measures on `PiLp`

Transporting a finite product of probability measures `Measure.pi μ` along `WithLp.toLp p` equips
`PiLp p α` with the product law while preserving its `L^p` metric structure. Reading off coordinate
`i` is then measure-preserving onto the marginal `μ i`, both for raw evaluation
(`PiLp.measurePreserving_eval_map_toLp`) and for the continuous linear projection `PiLp.proj`
(`PiLp.measurePreserving_proj_map_toLp`).
-/

public section

open MeasureTheory

open scoped ENNReal

namespace PiLp

/-- Coordinate evaluation `x ↦ x i` on `PiLp p α` pushes the `toLp`-transported product of
probability measures `(Measure.pi μ).map (WithLp.toLp p)` to the `i`-th marginal `μ i`. -/
theorem measurePreserving_eval_map_toLp {ι : Type*} [Fintype ι] {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)] (p : ℝ≥0∞) (μ : ∀ i, Measure (α i))
    [∀ i, IsProbabilityMeasure (μ i)] (i : ι) :
    MeasurePreserving (fun x : PiLp p α ↦ x i) ((Measure.pi μ).map (WithLp.toLp p)) (μ i) :=
  (measurePreserving_eval μ i).comp ((MeasurableEquiv.toLp p (∀ j, α j)).measurePreserving_symm _)

/-- The continuous linear coordinate projection `PiLp.proj p α i` pushes the `toLp`-transported
product of probability measures `(Measure.pi μ).map (WithLp.toLp p)` to the `i`-th marginal
`μ i`. -/
theorem measurePreserving_proj_map_toLp {ι 𝕜 : Type*} [Fintype ι] [Semiring 𝕜]
    {α : ι → Type*} [∀ i, NormedAddCommGroup (α i)] [∀ i, Module 𝕜 (α i)]
    [∀ i, MeasurableSpace (α i)] (p : ℝ≥0∞) (μ : ∀ i, Measure (α i))
    [∀ i, IsProbabilityMeasure (μ i)] (i : ι) :
    MeasurePreserving (PiLp.proj p α i : PiLp p α →L[𝕜] α i)
      ((Measure.pi μ).map (WithLp.toLp p)) (μ i) := by
  have hcoe : ⇑(PiLp.proj p α i : PiLp p α →L[𝕜] α i) = fun x : PiLp p α ↦ x i := by
    ext x
    exact PiLp.proj_apply p α i x
  rw [hcoe]
  exact measurePreserving_eval_map_toLp p μ i

end PiLp
