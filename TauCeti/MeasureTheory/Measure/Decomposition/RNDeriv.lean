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
# Square roots and bounds of Radon–Nikodym derivatives

The square root `√(dμ/dν)` of the density of a finite measure `μ` is square-integrable with
respect to any reference measure `ν`
(`MeasureTheory.Measure.memLp_two_sqrt_toReal_rnDeriv`), since its square integrates to at most
the mass of `μ`. Square roots of densities are the objects compared in `L²(ν)` by the Hellinger
distance.

For finite `μ` and `ν` and any reference measure `κ`, the geometric mean `√(dμ/dκ · dν/dκ)` of
the two densities is integrable, being dominated by their arithmetic mean, and so is the squared
difference `(√(dμ/dκ) - √(dν/dκ))²` of their square roots.

A measure dominated by a multiple of a σ-finite measure, `μ ≤ c • ν`, has density at most `c`:
`dμ/dν ≤ c` holds `ν`-almost everywhere. For `c = ENNReal.ofReal M` this gives a measurable
real density `f` with `0 ≤ f ≤ M` everywhere and `μ = f ν`.

## Main results

* `MeasureTheory.Measure.memLp_two_sqrt_toReal_rnDeriv`: `√(dμ/dν) ∈ L²(ν)` for finite `μ`.
* `MeasureTheory.Measure.integrable_sqrt_toReal_rnDeriv_mul`: `√(dμ/dκ · dν/dκ)` is
  `κ`-integrable for finite `μ` and `ν`.
* `MeasureTheory.Measure.integrable_sq_sqrt_toReal_rnDeriv_sub`: `(√(dμ/dκ) - √(dν/dκ))²` is
  `κ`-integrable for finite `μ` and `ν`.
* `MeasureTheory.Measure.rnDeriv_le_of_le_smul`: `dμ/dν ≤ c` almost everywhere if `μ ≤ c • ν`.
* `MeasureTheory.Measure.exists_eq_withDensity_of_le_smul`: `μ ≤ M • ν` is `f ν` for a measurable
  `f` with values in `[0, M]`.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace MeasureTheory.Measure

variable {α : Type*} [MeasurableSpace α]

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

/-- If `μ ≤ c • ν` for a σ-finite `ν`, the Radon–Nikodym derivative `dμ/dν` is at most `c`
`ν`-almost everywhere. -/
theorem rnDeriv_le_of_le_smul {μ ν : Measure α} [SigmaFinite ν] {c : ℝ≥0∞} (h : μ ≤ c • ν) :
    μ.rnDeriv ν ≤ᵐ[ν] fun _ ↦ c := by
  refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite (μ.measurable_rnDeriv ν) fun s _ _ ↦ ?_
  rw [setLIntegral_const, ← smul_eq_mul, ← smul_apply]
  exact (setLIntegral_rnDeriv_le s).trans (h s)

/-- A measure with `μ ≤ M • ν`, for a σ-finite `ν` and `0 ≤ M`, is `f ν` for a measurable density
`f` with `0 ≤ f ≤ M` everywhere. -/
theorem exists_eq_withDensity_of_le_smul {μ ν : Measure α} [SigmaFinite ν] {M : ℝ} (hM : 0 ≤ M)
    (h : μ ≤ ENNReal.ofReal M • ν) :
    ∃ f : α → ℝ, Measurable f ∧ (∀ x, 0 ≤ f x) ∧ (∀ x, f x ≤ M) ∧
      μ = ν.withDensity fun x ↦ ENNReal.ofReal (f x) := by
  have : SigmaFinite μ := sigmaFinite_of_le (M.toNNReal • ν) h
  refine ⟨fun x ↦ min (μ.rnDeriv ν x).toReal M,
    (μ.measurable_rnDeriv ν).ennreal_toReal.min measurable_const,
    fun x ↦ le_min ENNReal.toReal_nonneg hM, fun x ↦ min_le_right _ _, ?_⟩
  conv_lhs => rw [← withDensity_rnDeriv_eq μ ν (absolutelyContinuous_of_le_smul h)]
  refine withDensity_congr_ae ?_
  filter_upwards [rnDeriv_le_of_le_smul h] with x hx
  rw [min_eq_left (ENNReal.toReal_le_of_le_ofReal hM hx),
    ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hx)]

end MeasureTheory.Measure
