/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.ApproximateIdentity
import TauCeti.MeasureTheory.Function.Lp.MollificationBridge

/-!
# Smooth density in whole-space Sobolev spaces

For `1 ≤ p < ∞`, the elements of `W^{k,p}(ℝⁿ)` with a smooth representative are dense in
the full Sobolev norm, at every natural order `k`. The ambient space can be any finite-dimensional
real inner product space with an additive Haar measure.

The Sobolev mollifier averages translations of the entire weak-derivative graph. Its value is
represented by the classical convolution with a smooth compactly supported kernel, even when
the original function has no compact support. Thus its smoothness and its convergence hold
simultaneously: the approximation controls every recorded weak derivative, rather than only
the value in `Lᵖ`.

The approximating smooth functions need not have compact support. Density of test functions
in the higher-order spaces and smooth density on arbitrary open domains are separate results.

## Main declarations

* `TauCeti.Wkp.exists_contDiff_ae_eq_value_normedBumpL`: a smooth representative of each
  whole-space Sobolev mollification.
* `TauCeti.Wkp.exists_contDiff_approximation`: a sequence of smooth representatives whose
  Sobolev classes converge in the full graph norm.
* `TauCeti.Wkp.dense_contDiff_representatives`: smooth density in the whole-space Sobolev norm.

## References

L. C. Evans, *Partial Differential Equations*, §5.3.1. The formal construction uses
`TauCeti.Wkp.normedBumpL` and `TauCeti.normedBumpLp_ae_eq_convolution`, together with Mathlib's
`HasCompactSupport.contDiff_convolution_left`.
-/

public section

noncomputable section

namespace TauCeti.Wkp

open Filter MeasureTheory Set TopologicalSpace
open scoped Convolution ENNReal Topology

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {p : ENNReal} [Fact (1 ≤ p)]

local instance : (mu.restrict ((⊤ : Opens E) : Set E)).IsAddHaarMeasure := by
  rw [Opens.coe_top, Measure.restrict_univ]
  infer_instance

/-- Every whole-space Sobolev mollification has a smooth representative, without any
compact-support assumption on the original function. -/
theorem exists_contDiff_ae_eq_value_normedBumpL (hp : p ≠ ∞)
    (phi : ContDiffBump (0 : E)) (k : ℕ) (u : Wkp mu ⊤ p k) :
    ∃ f : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧
      (value k (normedBumpL hp phi k u) : E → ℝ) =ᵐ[mu.restrict (⊤ : Opens E)] f := by
  let nu := mu.restrict ((⊤ : Opens E) : Set E)
  let f := phi.normed nu ⋆[ContinuousLinearMap.lsmul ℝ ℝ, nu] (value k u : E → ℝ)
  refine ⟨f, ?_, ?_⟩
  · exact phi.hasCompactSupport_normed.contDiff_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) phi.contDiff_normed
      ((Lp.memLp (value k u)).locallyIntegrable Fact.out)
  · rw [value_normedBumpL]
    simpa only [Lp.toLp_coeFn] using
      normedBumpLp_ae_eq_convolution hp phi (Lp.memLp (value k u))

/-- Every whole-space `W^{k,p}` element, for finite `p`, is a Sobolev-norm limit of elements
with smooth representatives. No boundedness or support condition is imposed on the element. -/
theorem exists_contDiff_approximation (hp : p ≠ ∞) (k : ℕ) (u : Wkp mu ⊤ p k) :
    ∃ (v : ℕ → Wkp mu ⊤ p k) (f : ℕ → E → ℝ),
      (∀ j, ContDiff ℝ (⊤ : ℕ∞) (f j)) ∧
      (∀ j, (value k (v j) : E → ℝ) =ᵐ[mu.restrict (⊤ : Opens E)] f j) ∧
      Tendsto v atTop (𝓝 u) := by
  let phi : ℕ → ContDiffBump (0 : E) := fun j ↦
    ⟨1 / ((j : ℝ) + 1) / 2, 1 / ((j : ℝ) + 1), by positivity,
      half_lt_self (by positivity)⟩
  have hphi : Tendsto (fun j ↦ (phi j).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  choose f hf hae using fun j ↦ exists_contDiff_ae_eq_value_normedBumpL hp (phi j) k u
  exact ⟨fun j ↦ normedBumpL hp (phi j) k u, f, hf, hae,
    tendsto_normedBumpL hp hphi k u⟩

/-- Smooth representatives are dense in `W^{k,p}(ℝⁿ)` for `1 ≤ p < ∞`, with density measured
in the full Sobolev norm, including every recorded weak derivative. -/
theorem dense_contDiff_representatives (hp : p ≠ ∞) (k : ℕ) :
    Dense {u : Wkp mu ⊤ p k | ∃ f : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧
      (value k u : E → ℝ) =ᵐ[mu.restrict (⊤ : Opens E)] f} := by
  intro u
  obtain ⟨v, f, hf, hae, hv⟩ := exists_contDiff_approximation hp k u
  exact mem_closure_of_tendsto hv (Eventually.of_forall fun j ↦ ⟨f j, hf j, hae j⟩)

end TauCeti.Wkp
