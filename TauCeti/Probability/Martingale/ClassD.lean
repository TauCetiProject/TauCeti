/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.UniformIntegrable
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.Process.Stopping
public import Mathlib.Topology.Order.Cadlag
import TauCeti.MeasureTheory.Function.ConditionalExpectation.UniformIntegrable
import TauCeti.MeasureTheory.Function.UniformIntegrable
import TauCeti.Probability.Martingale.ContinuousStopping

/-!
# Processes of class D and class DL

A process `X` is of class D when its values `X_τ` at bounded stopping times `τ` form a uniformly
integrable family, and of class DL when, for every horizon `T`, its values at stopping times
`τ ≤ T` do. Class D implies class DL. On a filtration satisfying the usual conditions, class DL is
the hypothesis under which a right-continuous submartingale has a Doob–Meyer decomposition, and
the compactness step of that construction uses it in the form that values at stopping times
bounded by one horizon are uniformly integrable.

Stopping times take values in `WithTop ι`; only bounded ones are used, so the junk value of
`MeasureTheory.stoppedValue` at an infinite time never enters. Class D is defined here over
bounded stopping times, for every time domain; Karatzas and Shreve use all almost surely finite
stopping times on `[0, ∞)`.

* `TauCeti.BoundedStoppingTime`: stopping times bounded by a horizon `T`, the index set of the
  class DL family, with deterministic times `TauCeti.BoundedStoppingTime.const`, at which a
  process stops at its value there (`TauCeti.BoundedStoppingTime.stoppedValue_const`).
* `TauCeti.IsClassD`, `TauCeti.IsClassDL`: the two classes, with the characterizations
  `TauCeti.isClassD_iff` and `TauCeti.isClassDL_iff` and the eliminations
  `TauCeti.IsClassD.uniformIntegrable`, `TauCeti.IsClassDL.uniformIntegrable` and
  `TauCeti.IsClassDL.integrable_stoppedValue`.
* `TauCeti.IsClassD.isClassDL`: class D implies class DL.
* `MeasureTheory.Martingale.isClassDL_of_ae_isRightContinuous`: a strongly progressive martingale
  indexed by `ℝ≥0` with almost surely right-continuous paths is of class DL.
* `TauCeti.isClassD_of_ae_eq_condExp`: a strongly progressive process with almost surely
  right-continuous paths of the form `M_t = E[ξ | ℱ_t]` for an integrable `ξ` is of class D.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §1.4, Definition 1.4.8.
-/

public section

open Filter
open scoped NNReal ENNReal

namespace TauCeti

open MeasureTheory

variable {Ω ι E : Type*} {mΩ : MeasurableSpace Ω} [Preorder ι] [Nonempty ι]
  [NormedAddCommGroup E] {X : ι → Ω → E} {ℱ : Filtration ι mΩ} {μ : Measure Ω}

/-- Stopping times bounded by `T`, the index set of the class DL family at horizon `T`. -/
abbrev BoundedStoppingTime (ℱ : Filtration ι mΩ) (T : ι) :=
  {τ : Ω → WithTop ι // IsStoppingTime ℱ τ ∧ ∀ ω, τ ω ≤ T}

/-- A deterministic time bounded by `T`, as a stopping time bounded by `T`. -/
def BoundedStoppingTime.const {T t : ι} (ht : t ≤ T) : BoundedStoppingTime ℱ T :=
  ⟨fun _ ↦ t, isStoppingTime_const ℱ t, fun _ ↦ WithTop.coe_le_coe.2 ht⟩

omit [NormedAddCommGroup E] in
/-- Stopping a process at a deterministic time `t ≤ T` gives its value at `t`. -/
@[simp]
theorem BoundedStoppingTime.stoppedValue_const {T t : ι} (ht : t ≤ T) :
    stoppedValue X (BoundedStoppingTime.const (ℱ := ℱ) ht).1 = X t :=
  MeasureTheory.stoppedValue_const X t

/-- A process is of **class D** when its values at bounded stopping times form a uniformly
integrable family. -/
def IsClassD (X : ι → Ω → E) (ℱ : Filtration ι mΩ) (μ : Measure Ω) : Prop :=
  UniformIntegrable
    (fun τ : {τ : Ω → WithTop ι // IsStoppingTime ℱ τ ∧ ∃ T : ι, ∀ ω, τ ω ≤ T} ↦
      stoppedValue X τ.1) 1 μ

/-- A process is of **class DL** when, for every horizon `T`, its values at stopping times
bounded by `T` form a uniformly integrable family. -/
def IsClassDL (X : ι → Ω → E) (ℱ : Filtration ι mΩ) (μ : Measure Ω) : Prop :=
  ∀ T : ι, UniformIntegrable (fun τ : BoundedStoppingTime ℱ T ↦ stoppedValue X τ.1) 1 μ

/-- Unfolding class D: the values at bounded stopping times are uniformly integrable. -/
theorem isClassD_iff : IsClassD X ℱ μ ↔ UniformIntegrable
    (fun τ : {τ : Ω → WithTop ι // IsStoppingTime ℱ τ ∧ ∃ T : ι, ∀ ω, τ ω ≤ T} ↦
      stoppedValue X τ.1) 1 μ :=
  Iff.rfl

/-- Unfolding class DL: for each horizon, the values at stopping times bounded by it are
uniformly integrable. -/
theorem isClassDL_iff : IsClassDL X ℱ μ ↔
    ∀ T : ι, UniformIntegrable (fun τ : BoundedStoppingTime ℱ T ↦ stoppedValue X τ.1) 1 μ :=
  Iff.rfl

/-- The values of a process of class D at bounded stopping times are uniformly integrable. -/
theorem IsClassD.uniformIntegrable (h : IsClassD X ℱ μ) : UniformIntegrable
    (fun τ : {τ : Ω → WithTop ι // IsStoppingTime ℱ τ ∧ ∃ T : ι, ∀ ω, τ ω ≤ T} ↦
      stoppedValue X τ.1) 1 μ :=
  h

/-- The values of a process of class DL at stopping times bounded by `T` are uniformly
integrable. -/
theorem IsClassDL.uniformIntegrable (h : IsClassDL X ℱ μ) (T : ι) :
    UniformIntegrable (fun τ : BoundedStoppingTime ℱ T ↦ stoppedValue X τ.1) 1 μ :=
  h T

/-- The value of a process of class DL at a stopping time bounded by a constant is
integrable. -/
theorem IsClassDL.integrable_stoppedValue (h : IsClassDL X ℱ μ) {τ : Ω → WithTop ι} {T : ι}
    (hτ : IsStoppingTime ℱ τ) (hτT : ∀ ω, τ ω ≤ T) : Integrable (stoppedValue X τ) μ :=
  memLp_one_iff_integrable.1 ((h.uniformIntegrable T).memLp ⟨τ, hτ, hτT⟩)

/-- A process of class D is of class DL. -/
theorem IsClassD.isClassDL (h : IsClassD X ℱ μ) : IsClassDL X ℱ μ := fun T ↦
  (h.uniformIntegrable.comp fun τ : BoundedStoppingTime ℱ T ↦ ⟨τ.1, τ.2.1, T, τ.2.2⟩ :)

end TauCeti

namespace MeasureTheory.Martingale

open TauCeti

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {ℱ : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → E}

/-- A strongly progressive martingale with almost surely right-continuous paths is of class DL:
at a stopping time `τ ≤ T` its value is the conditional expectation of `M_T` given `ℱ_τ`. -/
theorem isClassDL_of_ae_isRightContinuous (hM : Martingale M ℱ μ)
    (hprog : IsStronglyProgressive ℱ M)
    (hcont : ∀ᵐ ω ∂μ, IsRightContinuous (fun t ↦ M t ω)) : IsClassDL M ℱ μ := by
  intro T
  exact ((memLp_one_iff_integrable.2 (hM.integrable T)).uniformIntegrable_condExp le_rfl
    ENNReal.one_ne_top (fun τ ↦ τ.2.1.measurableSpace_le)).ae_eq fun τ ↦
      (hM.stoppedValue_ae_eq_condExp_of_le_const_of_ae_isRightContinuous hprog hcont τ.2.1
        τ.2.2).symm

end MeasureTheory.Martingale

namespace TauCeti

open MeasureTheory

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {ℱ : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → E}

/-- A strongly progressive process with almost surely right-continuous paths that is the
conditional expectation `M_t = E[ξ | ℱ_t]` of one integrable variable `ξ` is of class D. -/
theorem isClassD_of_ae_eq_condExp (hprog : IsStronglyProgressive ℱ M)
    (hcont : ∀ᵐ ω ∂μ, IsRightContinuous (fun t ↦ M t ω)) {ξ : Ω → E}
    (hξ : Integrable ξ μ) (hMξ : ∀ t, M t =ᵐ[μ] μ[ξ | ℱ t]) : IsClassD M ℱ μ := by
  have hM : Martingale M ℱ μ := by
    refine ⟨hprog.stronglyAdapted, fun s t hst ↦ ?_⟩
    exact (condExp_congr_ae (hMξ t)).trans
      ((condExp_condExp_of_le (ℱ.mono hst) (ℱ.le t)).trans (hMξ s).symm)
  refine ((memLp_one_iff_integrable.2 hξ).uniformIntegrable_condExp le_rfl ENNReal.one_ne_top
    (fun τ ↦ τ.2.1.measurableSpace_le)).ae_eq fun τ ↦ ?_
  obtain ⟨T, hT⟩ := τ.2.2
  refine (condExp_condExp_of_le (τ.2.1.measurableSpace_le_of_le_const hT) (ℱ.le T)).symm.trans ?_
  exact (condExp_congr_ae (hMξ T)).symm.trans
    (hM.stoppedValue_ae_eq_condExp_of_le_const_of_ae_isRightContinuous hprog hcont τ.2.1 hT).symm

end TauCeti
