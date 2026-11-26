/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.D1p0.Basic
public import TauCeti.Analysis.Sobolev.W1p.Restriction
import TauCeti.Analysis.Sobolev.Poincare.Wirtinger.W1p
import TauCeti.Analysis.Sobolev.W1p.Zero

/-!
# Restricting `D^{1,p}_0(Ω)` to bounded convex subsets

An element of the homogeneous Sobolev space `D^{1,p}_0(Ω)` (`TauCeti.D1p0`) is recorded by its
gradient field in `Lᵖ(Ω, E)`, a limit of gradients of test functions. It need not be the gradient
of a function in `Lᵖ(Ω)`: on the whole space the potential of an element of `D^{1,2}_0(ℝⁿ)` is in
general not square integrable. This file shows that it is nevertheless locally the gradient of a
Sobolev function: on every bounded convex open set `U ⊆ Ω`, the restriction of `u ∈ D^{1,p}_0(Ω)`
to `U` is the weak gradient of an element of `W^{1,p}(U)`
(`TauCeti.D1p0.exists_w1p_gradient_ae_eq`). This lets local estimates stated for `W^{1,p}`
functions, such as mean oscillation estimates on balls, apply to elements of `D^{1,p}_0(Ω)`.

## The argument

On the bounded convex set `U` the weak gradients of the elements of `W^{1,p}(U)` form a closed
subset of `Lᵖ(U, E)` (`TauCeti.W1p.isClosed_range_gradientL_of_convex`, from the Poincaré–Wirtinger
inequality). It contains the restriction to `U` of the gradient of every test function on `Ω`, and
restriction from `Lᵖ(Ω, E)` to `Lᵖ(U, E)` is continuous, so it contains the restriction of every
element of their closure `D^{1,p}_0(Ω)`.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Metric Module Set TopologicalSpace
open scoped Distributions ENNReal NNReal

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

/-- **Elements of `D^{1,p}_0(Ω)` are locally gradients of Sobolev functions.** On a bounded convex
open set `U ⊆ Ω`, every `u ∈ D^{1,p}_0(Ω)` agrees almost everywhere on `U` with the weak gradient
of some `v ∈ W^{1,p}(U)`. -/
theorem D1p0.exists_w1p_gradient_ae_eq {U : Opens E} (hU : U ≤ Omega)
    (hconv : Convex ℝ (U : Set E)) (hb : Bornology.IsBounded (U : Set E)) (u : D1p0 mu Omega p) :
    ∃ v : W1p mu U p, W1p.gradient v =ᵐ[mu.restrict U] (u : Lp E p (mu.restrict Omega)) := by
  -- Restriction of `Lᵖ` classes from `Ω` to `U`.
  have hle : mu.restrict (U : Set E) ≤ (1 : ℝ≥0∞) • mu.restrict Omega := by
    simpa only [one_smul] using Measure.restrict_mono_set mu (SetLike.coe_subset_coe.mpr hU)
  set ρ : Lp E p (mu.restrict Omega) →L[ℝ] Lp E p (mu.restrict U) :=
    Lp.LpToLpOfMeasureLeSMul (by simp) hle
  -- The gradients of `W^{1,p}(U)` form a closed set, which contains the restricted gradient of
  -- every test function.
  have hclosed := W1p.isClosed_range_gradientL_of_convex (mu := mu) (p := p) hconv hb
  have htest : ∀ φ : 𝓓(Omega, ℝ), ρ (gradientTestFunctionLp p φ) ∈ range
      (W1p.gradientL : W1p mu U p →L[ℝ] Lp E p (mu.restrict U)) := by
    intro φ
    refine ⟨W1p.restrictL hU (W1p.ofTestFunctionₗ mu Omega p φ), Lp.ext ?_⟩
    have hφU : ∀ᵐ x ∂mu.restrict U, gradientTestFunctionLp (mu := mu) p φ x =
        _root_.gradient (φ : E → ℝ) x :=
      ae_restrict_of_ae_restrict_of_subset (SetLike.coe_subset_coe.mpr hU)
        (gradientTestFunctionLp_apply_ae p φ)
    filter_upwards [W1p.gradient_restrictL_ofTestFunctionₗ_ae (mu := mu) (p := p) hU φ,
      Lp.coeFn_LpToLpOfMeasureLeSMul (by simp) hle (gradientTestFunctionLp (mu := mu) p φ), hφU]
      with x hw hρ hφ
    rw [W1p.gradientL_apply, hw, hρ, hφ]
  -- So does the restriction of every element of `D^{1,p}_0(Ω)`, their limits.
  have hu : (u : Lp E p (mu.restrict Omega)) ∈
      ρ ⁻¹' range (W1p.gradientL : W1p mu U p →L[ℝ] Lp E p (mu.restrict U)) := by
    have hsub : closure (range (gradientTestFunctionLp (mu := mu) (Omega := Omega) p)) ⊆
        ρ ⁻¹' range (W1p.gradientL : W1p mu U p →L[ℝ] Lp E p (mu.restrict U)) :=
      closure_minimal (range_subset_iff.2 htest) (hclosed.preimage ρ.continuous)
    exact hsub (coe_d1p0Submodule (mu := mu) (Omega := Omega) (p := p) ▸ u.property)
  obtain ⟨v, hv⟩ := hu
  refine ⟨v, ?_⟩
  rw [← W1p.gradientL_apply, hv]
  exact Lp.coeFn_LpToLpOfMeasureLeSMul (by simp) hle _

end TauCeti
