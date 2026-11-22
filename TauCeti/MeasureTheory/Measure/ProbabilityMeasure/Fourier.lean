/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import TauCeti.MeasureTheory.Measure.Haar.UnitAddTorus
import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.DenseSpan

/-!
# Fourier criteria for weak convergence on circles and tori

Applying Stone–Weierstrass density of trigonometric polynomials (`span_fourier_closure_eq_top`,
`UnitAddTorus.span_mFourier_closure_eq_top`) to `DenseSpan`, probability measures on `AddCircle T`
or `UnitAddTorus d` converge weakly iff all Fourier moments converge, and are determined by them.
-/

public section

noncomputable section

open Filter MeasureTheory Set Topology

namespace MeasureTheory.ProbabilityMeasure

section AddCircle

variable {T : ℝ} [Fact (0 < T)] {ι : Type*} {L : Filter ι}
  {μs : ι → ProbabilityMeasure (AddCircle T)} {μ : ProbabilityMeasure (AddCircle T)}

/-- Weak convergence of circle probability measures iff convergence of all Fourier moments. -/
theorem tendsto_iff_forall_integral_fourier_tendsto :
    Tendsto μs L (𝓝 μ) ↔ ∀ n : ℤ,
      Tendsto (fun i ↦ ∫ x, fourier n x ∂(μs i : Measure (AddCircle T))) L
        (𝓝 (∫ x, fourier n x ∂(μ : Measure (AddCircle T)))) := by
  rw [tendsto_iff_forall_integral_tendsto_of_span_closure_eq_top ℂ (span_fourier_closure_eq_top)]
  simp

/-- Circle probability measures tend weakly to Haar probability iff every nonzero Fourier moment
tends to zero. -/
theorem tendsto_haarAddCircle_iff :
    Tendsto μs L (𝓝 AddCircle.haarAddCircle.toProbabilityMeasure) ↔ ∀ n : ℤ, n ≠ 0 →
      Tendsto (fun i ↦ ∫ x, fourier n x ∂(μs i : Measure (AddCircle T))) L (𝓝 0) := by
  have hhaar (n : ℤ) : ∫ x, fourier n x ∂(AddCircle.haarAddCircle (T := T)) =
      if n = 0 then 1 else 0 := by
    simpa [fourierCoeff, fourier_zero, Pi.single_apply, eq_comm] using
      congrFun (fourierCoeff_fourier (T := T) n) 0
  rw [tendsto_iff_forall_integral_fourier_tendsto]
  simp only [Measure.coe_toProbabilityMeasure, hhaar]
  refine ⟨fun h n hn ↦ by simpa [hn] using h n, fun h n ↦ ?_⟩
  by_cases hn : n = 0
  · subst n; simpa using (tendsto_const_nhds : Tendsto (fun _ : ι ↦ (1 : ℂ)) L (𝓝 1))
  · simpa [hn] using h n hn

/-- A probability measure on an additive circle is determined by its integer Fourier moments. -/
theorem ext_of_forall_integral_fourier_eq {ν : ProbabilityMeasure (AddCircle T)}
    (h : ∀ n : ℤ, ∫ x, fourier n x ∂(μ : Measure (AddCircle T)) =
      ∫ x, fourier n x ∂(ν : Measure (AddCircle T))) : μ = ν :=
  ext_of_forall_integral_eq_of_span_closure_eq_top ℂ span_fourier_closure_eq_top (by simpa using h)

end AddCircle

section UnitAddTorus

variable {d : Type*} [Fintype d] {ι : Type*} {L : Filter ι}
  {μs : ι → ProbabilityMeasure (UnitAddTorus d)} {μ : ProbabilityMeasure (UnitAddTorus d)}

/-- Weak convergence on `UnitAddTorus d` iff convergence of all integer Fourier moments. -/
theorem tendsto_iff_forall_integral_mFourier_tendsto :
    Tendsto μs L (𝓝 μ) ↔ ∀ k : d → ℤ,
      Tendsto (fun i ↦ ∫ x, UnitAddTorus.mFourier k x ∂(μs i : Measure (UnitAddTorus d))) L
        (𝓝 (∫ x, UnitAddTorus.mFourier k x ∂(μ : Measure (UnitAddTorus d)))) := by
  rw [tendsto_iff_forall_integral_tendsto_of_span_closure_eq_top ℂ
    UnitAddTorus.span_mFourier_closure_eq_top]; simp

/-- Measures on `UnitAddTorus d` tend weakly to Haar (`volume`) iff nonzero Fourier moments → 0. -/
theorem tendsto_volume_unitAddTorus_iff :
    Tendsto μs L (𝓝 (volume : Measure (UnitAddTorus d)).toProbabilityMeasure) ↔ ∀ k : d → ℤ,
      k ≠ 0 → Tendsto (fun i ↦ ∫ x, UnitAddTorus.mFourier k x ∂(μs i : Measure (UnitAddTorus d)))
        L (𝓝 0) := by
  rw [tendsto_iff_forall_integral_mFourier_tendsto]
  simp only [Measure.coe_toProbabilityMeasure, TauCeti.UnitAddTorus.integral_mFourier]
  refine ⟨fun h k hk ↦ by simpa [hk] using h k, fun h k ↦ ?_⟩
  by_cases hk : k = 0
  · subst hk; simpa [UnitAddTorus.mFourier_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ι ↦ (1 : ℂ)) L (𝓝 1))
  · simpa [hk] using h k hk

/-- A probability measure on `UnitAddTorus d` is determined by its integer Fourier moments. -/
theorem ext_of_forall_integral_mFourier_eq {ν : ProbabilityMeasure (UnitAddTorus d)}
    (h : ∀ k : d → ℤ, ∫ x, UnitAddTorus.mFourier k x ∂(μ : Measure (UnitAddTorus d)) =
      ∫ x, UnitAddTorus.mFourier k x ∂(ν : Measure (UnitAddTorus d))) : μ = ν :=
  ext_of_forall_integral_eq_of_span_closure_eq_top ℂ UnitAddTorus.span_mFourier_closure_eq_top
    (by simpa using h)

end UnitAddTorus

end MeasureTheory.ProbabilityMeasure
