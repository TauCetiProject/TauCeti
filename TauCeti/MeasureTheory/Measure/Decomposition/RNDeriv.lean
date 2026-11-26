/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import TauCeti.Analysis.Real.Sqrt

/-!
# Square roots of Radon–Nikodym derivatives

The square root `√(dμ/dν)` of the density of a finite measure `μ` is square-integrable with
respect to any reference measure `ν`
(`MeasureTheory.Measure.memLp_two_sqrt_toReal_rnDeriv`), since its square integrates to at most
the mass of `μ`. Square roots of densities are the objects compared in `L²(ν)` by the Hellinger
distance.

For finite `μ` and `ν` and any reference measure `κ`, the geometric mean `√(dμ/dκ · dν/dκ)` of
the two densities is integrable, being dominated by their arithmetic mean, and so is the squared
difference `(√(dμ/dκ) - √(dν/dκ))²` of their square roots.

## Main results

* `MeasureTheory.Measure.ae_sqrt_toReal_rnDeriv_pos`: `√(dμ/dν) > 0` `μ`-almost everywhere when
  `μ ≪ ν` for σ-finite `μ` admitting a Lebesgue decomposition with respect to `ν`.
* `MeasureTheory.Measure.memLp_two_sqrt_toReal_rnDeriv`: `√(dμ/dν) ∈ L²(ν)` for finite `μ`.
* `MeasureTheory.Measure.integrable_sqrt_toReal_rnDeriv_mul`: `√(dμ/dκ · dν/dκ)` is
  `κ`-integrable for finite `μ` and `ν`.
* `MeasureTheory.Measure.integrable_sq_sqrt_toReal_rnDeriv_sub`: `(√(dμ/dκ) - √(dν/dκ))²` is
  `κ`-integrable for finite `μ` and `ν`.
-/

public section

open MeasureTheory

namespace MeasureTheory.Measure

variable {α : Type*} [MeasurableSpace α]

/-- For `μ ≪ ν` with `μ` σ-finite and admitting a Lebesgue decomposition with respect to `ν`,
the square-root Radon–Nikodym derivative `√(dμ/dν)` is `μ`-almost everywhere positive. -/
theorem ae_sqrt_toReal_rnDeriv_pos {μ ν : Measure α} [μ.HaveLebesgueDecomposition ν]
    [SigmaFinite μ] (hμν : μ ≪ ν) : ∀ᵐ x ∂μ, 0 < √(μ.rnDeriv ν x).toReal := by
  filter_upwards [rnDeriv_pos hμν, hμν (μ.rnDeriv_lt_top ν)] with x hpos hlt
  exact Real.sqrt_pos.mpr (ENNReal.toReal_pos hpos.ne' hlt.ne)

/-- The square root `√(dμ/dν)` of the density of a finite measure `μ` is square-integrable,
whatever the reference measure `ν`: its square integrates to at most the mass of `μ`. -/
theorem memLp_two_sqrt_toReal_rnDeriv (μ ν : Measure α) [IsFiniteMeasure μ] :
    MemLp (fun x ↦ √(μ.rnDeriv ν x).toReal) 2 ν := by
  refine (memLp_two_iff_integrable_sq
    (μ.measurable_rnDeriv _).ennreal_toReal.sqrt.aestronglyMeasurable).mpr ?_
  simpa only [Real.sq_sqrt ENNReal.toReal_nonneg] using integrable_toReal_rnDeriv

/-- The geometric mean `√(dμ/dκ · dν/dκ)` of the densities of finite measures `μ` and `ν` is
integrable, whatever the reference measure `κ`. -/
theorem integrable_sqrt_toReal_rnDeriv_mul (μ ν κ : Measure α) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] :
    Integrable (fun x ↦ √((μ.rnDeriv κ x).toReal * (ν.rnDeriv κ x).toReal)) κ := by
  have hpq : Integrable (fun x ↦ ((μ.rnDeriv κ x).toReal + (ν.rnDeriv κ x).toReal) / 2) κ :=
    (integrable_toReal_rnDeriv.add integrable_toReal_rnDeriv).div_const 2
  refine hpq.mono ?_ (ae_of_all _ fun x ↦ ?_)
  · exact ((μ.measurable_rnDeriv κ).ennreal_toReal.mul
      (ν.measurable_rnDeriv κ).ennreal_toReal).sqrt.aestronglyMeasurable
  · rw [Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.norm_of_nonneg (by positivity)]
    exact Real.sqrt_mul_le_half_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg

/-- The squared difference `(√(dμ/dκ) - √(dν/dκ))²` of the square roots of the densities of
finite measures `μ` and `ν` is integrable, whatever the reference measure `κ`. -/
theorem integrable_sq_sqrt_toReal_rnDeriv_sub (μ ν κ : Measure α) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] :
    Integrable (fun x ↦ (√(μ.rnDeriv κ x).toReal - √(ν.rnDeriv κ x).toReal) ^ 2) κ := by
  simp only [Real.sq_sqrt_sub_sqrt ENNReal.toReal_nonneg ENNReal.toReal_nonneg]
  exact (integrable_toReal_rnDeriv.add integrable_toReal_rnDeriv).sub
    ((integrable_sqrt_toReal_rnDeriv_mul μ ν κ).const_mul 2)

end MeasureTheory.Measure
