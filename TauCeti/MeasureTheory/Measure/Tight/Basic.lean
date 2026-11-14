/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Tight
public import Mathlib.Topology.Metrizable.CompletelyMetrizable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.TightNormed
import TauCeti.Probability.Moments.Chebyshev

/-!
# Basic tightness criteria for measures

Mathlib's `MeasureTheory.isTightMeasureSet_singleton` says that a single finite measure on a
complete second-countable pseudo-metrizable space is tight, and `IsTightMeasureSet.union` says
that tightness survives a binary union. Together they give tightness of any *finite* set of
finite measures, which is the form the Prokhorov extraction arguments need in order to discard
the finitely many exceptional members of a family for which a uniform tail bound is unavailable.
On a proper seminormed group, uniformly bounded second norm moments also imply tightness.

## Main declarations

* `TauCeti.isTightMeasureSet_of_finite`: a finite set of finite measures is tight.
* `TauCeti.isTightMeasureSet_range_of_finite`: a family of finite measures indexed by a finite type
  has tight range.
* `TauCeti.isTightMeasureSet_range_of_eventually_eq`: a family of finite measures that is equal to
  a fixed measure off finitely many indices has tight range.
* `TauCeti.isTightMeasureSet_of_integral_norm_sq_le`: measures on a proper seminormed group
  with uniformly bounded second norm moments form a tight set.
* `TauCeti.isTightMeasureSet_of_integral_sq_le`: real measures with uniformly bounded
  second moments form a tight set.
-/

public section

open Filter MeasureTheory Set
open scoped Topology

namespace TauCeti

variable {α : Type*} [MeasurableSpace α] [TopologicalSpace α]
  [TopologicalSpace.IsCompletelyPseudoMetrizableSpace α] [SecondCountableTopology α]
  [BorelSpace α]

/-- **A finite set of finite measures is tight.** Singletons are tight and tightness is closed
under unions; the empty case routes through an arbitrary singleton, as Mathlib has no dedicated
empty-set tightness lemma. -/
theorem isTightMeasureSet_of_finite {S : Set (Measure α)} (hS : S.Finite)
    (hfin : ∀ ν ∈ S, IsFiniteMeasure ν) : IsTightMeasureSet S := by
  induction S, hS using Set.Finite.induction_on with
  | empty => exact (isTightMeasureSet_singleton (μ := (0 : Measure α))).subset (empty_subset _)
  | @insert ν S _ _ ih =>
      have := hfin ν (mem_insert _ _)
      exact isTightMeasureSet_singleton.union (ih fun ρ hρ ↦ hfin ρ (mem_insert_of_mem _ hρ))

/-- **A family of finite measures indexed by a finite type has tight range.** -/
theorem isTightMeasureSet_range_of_finite {ι : Type*} [Finite ι] (μ : ι → Measure α)
    [∀ i, IsFiniteMeasure (μ i)] : IsTightMeasureSet (range μ) :=
  isTightMeasureSet_of_finite (finite_range μ) (by rintro _ ⟨i, rfl⟩; infer_instance)

/-- **Eventually constant families of finite measures are tight.** A family of finite measures
that equals a fixed measure `ν` off finitely many indices has finite range, so it is tight. No
finiteness assumption on `ν` is needed: `ν` lies in the range only if it is one of the `μ i`. -/
theorem isTightMeasureSet_range_of_eventually_eq {ι : Type*} {μ : ι → Measure α}
    [∀ i, IsFiniteMeasure (μ i)] {ν : Measure α} (h : ∀ᶠ i in cofinite, μ i = ν) :
    IsTightMeasureSet (range μ) := by
  refine isTightMeasureSet_of_finite (((eventually_cofinite.1 h).image μ).insert ν |>.subset ?_)
    (by rintro _ ⟨i, rfl⟩; infer_instance)
  rintro _ ⟨i, rfl⟩
  exact (em (μ i = ν)).imp id fun hi ↦ ⟨i, hi, rfl⟩

/-- Measures on a proper seminormed group with uniformly bounded second norm moment are tight. -/
theorem isTightMeasureSet_of_integral_norm_sq_le {E : Type*} [MeasurableSpace E]
    [SeminormedAddCommGroup E] [ProperSpace E] {S : Set (Measure E)} {B : ℝ}
    (hS : ∀ ρ ∈ S, Integrable (fun x : E => ‖x‖ ^ 2) ρ ∧
      ∫ x, ‖x‖ ^ 2 ∂ρ ≤ B) : IsTightMeasureSet S := by
  have htail : Tendsto (fun R : ℝ => ⨆ ρ ∈ S, ρ {x | R < ‖x‖}) atTop (𝓝 0) := by
    have hlim : Tendsto (fun R : ℝ => B / R ^ 2) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop two_ne_zero)
    have hlim' : Tendsto (fun R : ℝ => ENNReal.ofReal (B / R ^ 2)) atTop (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal hlim
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim'
      (Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    refine iSup_le fun ρ => iSup_le fun hρ => ?_
    obtain ⟨hint, hB⟩ := hS ρ hρ
    exact meas_gt_le_div_sq_of_integral_sq_le (Y := fun x : E => ‖x‖) hint hB hR
  refine isTightMeasureSet_of_tendsto_measure_compl_closedBall (x := (0 : E)) ?_
  convert! htail using 6 with R
  ext x
  simp

/-- A set of measures on `ℝ` with uniformly bounded second moment is tight. -/
theorem isTightMeasureSet_of_integral_sq_le {S : Set (Measure ℝ)} {B : ℝ}
    (hS : ∀ ρ ∈ S, Integrable (fun x : ℝ => x ^ 2) ρ ∧
      ∫ x, x ^ 2 ∂ρ ≤ B) : IsTightMeasureSet S := by
  refine isTightMeasureSet_of_integral_norm_sq_le (B := B) ?_
  intro ρ hρ
  simpa only [Real.norm_eq_abs, sq_abs] using hS ρ hρ

end TauCeti

end
