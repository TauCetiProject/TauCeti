/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Lower semicontinuity and local mean bounds for Lebesgue integrals

This file records two general results combining lower semicontinuity with extended-real Lebesgue
integration:

* `TauCeti.lowerSemicontinuousAt_lintegral`: a parameter-dependent Fatou lemma showing that
  `x ↦ ∫⁻ p, F x p ∂ρ` is lower semicontinuous at `x₀` whenever `𝓝 x₀` is countably generated,
  each `F x` is a.e. measurable, and `F · p` is a.e. lower semicontinuous at `x₀`.
* `LowerSemicontinuousAt.le_of_setLIntegral_le`: if `ν` is finite on some neighborhood of `b` and
  positive on nonempty open sets, and a function `A` lower semicontinuous at `b` satisfies
  `∫⁻ t in S, A t ∂ν ≤ C * ν S` for all sufficiently small open neighborhoods `S` of `b`,
  then `A b ≤ C`.

## References

* L. Alpöge, Lean formalization of the Riemann hypothesis for Dirichlet `L`-functions,
  `New.lowerSemicontinuousAt_lintegral` and `New.le_of_setLIntegral_le` in
  `src/Lib/General/Measure/FibreMeasure.lean`,
  <https://github.com/leanprover-community/riemann-hypothesis/tree/dba5aded4bf7>.
-/

public section

open MeasureTheory Measure Filter Topology Set ENNReal

namespace TauCeti

/-- Fatou's lemma with a parameter: if `𝓝 x₀` is countably generated, `F x` is a.e. measurable for
every `x`, and `F · p` is lower semicontinuous at `x₀` for almost every `p`, then
`x ↦ ∫⁻ p, F x p ∂ρ` is lower semicontinuous at `x₀`. -/
theorem lowerSemicontinuousAt_lintegral {X P : Type*} [TopologicalSpace X] [MeasurableSpace P]
    {ρ : Measure P} {F : X → P → ℝ≥0∞} {x₀ : X} [IsCountablyGenerated (𝓝 x₀)]
    (h_meas : ∀ x : X, AEMeasurable (F x) ρ)
    (h_lsc : ∀ᵐ p : P ∂ρ, LowerSemicontinuousAt (F · p) x₀) :
    LowerSemicontinuousAt (fun x : X ↦ ∫⁻ p : P, F x p ∂ρ) x₀ := by
  rw [lowerSemicontinuousAt_iff_le_liminf]
  calc
    ∫⁻ p, F x₀ p ∂ρ ≤ ∫⁻ p, liminf (F · p) (𝓝 x₀) ∂ρ :=
      lintegral_mono_ae (h_lsc.mono fun _ ↦ lowerSemicontinuousAt_iff_le_liminf.1)
    _ ≤ liminf (fun x ↦ ∫⁻ p, F x p ∂ρ) (𝓝 x₀) := lintegral_liminf_le' h_meas

/-- Let `ν` be finite on some neighborhood of `b` and positive on nonempty open sets.
A function that is lower semicontinuous at `b`, and whose mean for `ν` over every open set
contained in some fixed neighborhood of `b` is at most `C`, is at most `C` at `b`. -/
theorem _root_.LowerSemicontinuousAt.le_of_setLIntegral_le {B : Type*} [TopologicalSpace B]
    [MeasurableSpace B] [OpensMeasurableSpace B] {ν : Measure B} [ν.IsOpenPosMeasure]
    {A : B → ℝ≥0∞} {b : B} {C : ℝ≥0∞} (hA : LowerSemicontinuousAt A b)
    (hν : ν.FiniteAtFilter (𝓝 b))
    (h_mean : ∀ᶠ S : Set B in (𝓝 b).smallSets, IsOpen S → ∫⁻ t : B in S, A t ∂ν ≤ C * ν S) :
    A b ≤ C := by
  refine le_of_forall_lt_imp_le_of_dense fun c hc ↦ ?_
  obtain ⟨S, ⟨hb, hS_open⟩, hS_mean, hS_lt, hS_fin⟩ : ∃ S : Set B, (b ∈ S ∧ IsOpen S) ∧
      (IsOpen S → ∫⁻ t in S, A t ∂ν ≤ C * ν S) ∧ S ⊆ {t | c < A t} ∧ ν S < ∞ :=
    (h_mean.and ((eventually_smallSets_subset.2 (hA c hc)).and
      hν.eventually)).exists_mem_basis_of_smallSets (nhds_basis_opens b)
  refine (ENNReal.mul_le_mul_iff_left (hS_open.measure_ne_zero ν ⟨b, hb⟩) hS_fin.ne).1 ?_
  calc
    c * ν S = ∫⁻ _ in S, c ∂ν := (setLIntegral_const S c).symm
    _ ≤ ∫⁻ t in S, A t ∂ν := setLIntegral_mono' hS_open.measurableSet fun t ht ↦ (hS_lt ht).le
    _ ≤ C * ν S := hS_mean hS_open

end TauCeti
