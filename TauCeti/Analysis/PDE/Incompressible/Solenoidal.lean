/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.Divergence.Basic
public import Mathlib.Topology.Algebra.Module.ClosedSubmodule
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.TangentSpace
import TauCeti.Analysis.Distribution.TestFunction.Gradient
import TauCeti.MeasureTheory.Function.Lp.Duality

/-!
# Solenoidal subspaces

In `Lᵖ`, the solenoidal fields form the intersection of the kernels of the
continuous pairings with scalar test gradients. At `p = 2`, these pairings are Hilbert space inner
products, so the closed subspace is the orthogonal complement of the closed span of the test
gradients, given by `TauCeti.wassersteinTangentSpace`.
-/

public section

open MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal Gradient InnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [OpensMeasurableSpace E]

section Lp

variable [CompleteSpace E] (E) (p : ℝ≥0∞) [Fact (1 ≤ p)]
  (μ : Measure E) [IsFiniteMeasureOnCompacts μ]

/-- The closed subspace of `Lᵖ(μ; E)` annihilating scalar test gradients.
It is defined by continuous pairings with test gradients, including at `p = 1` and `p = ∞`. -/
noncomputable def solenoidalLp : ClosedSubmodule ℝ (Lp E p μ) :=
  haveI : (ENNReal.conjExponent p).HolderConjugate p :=
    (ENNReal.HolderConjugate.conjExponent Fact.out).symm
  ⨅ φ : 𝓓((⊤ : Opens E), ℝ), (⊥ : ClosedSubmodule ℝ ℝ).comap
    (MemLp.innerLpCLM ℝ ((TestFunction.gradientCLM φ).continuous.memLp_of_hasCompactSupport
      (p := p.conjExponent) (μ := μ) (TestFunction.gradientCLM φ).hasCompactSupport))

variable {E p μ}

/-- Membership in the closed solenoidal subspace is equivalent to annihilating every test
gradient. -/
theorem mem_solenoidalLp_iff_integral_inner_eq_zero {u : Lp E p μ} :
    u ∈ solenoidalLp E p μ ↔
      ∀ φ : 𝓓((⊤ : Opens E), ℝ), ∫ x, ⟪u x, ∇ (φ : E → ℝ) x⟫_ℝ ∂μ = 0 := by
  simp only [solenoidalLp, ClosedSubmodule.mem_iInf, ClosedSubmodule.mem_comap,
    ClosedSubmodule.mem_bot, MemLp.innerLpCLM_apply]
  simp_rw [← TestFunction.gradientCLM_apply, real_inner_comm]

end Lp

/-- The closed solenoidal subspace consists of precisely the fields whose representatives
have weak divergence zero on the whole space. -/
@[simp]
theorem mem_solenoidalLp_iff [CompleteSpace E] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {μ : Measure E} [IsLocallyFiniteMeasure μ] {u : Lp E p μ} :
    u ∈ solenoidalLp E p μ ↔ IsSolenoidalOn μ ⊤ (u : E → E) := by
  have hu : LocallyIntegrableOn (u : E → E) (⊤ : Opens E) μ :=
    ((Lp.memLp u).locallyIntegrable Fact.out).locallyIntegrableOn _
  rw [mem_solenoidalLp_iff_integral_inner_eq_zero, isSolenoidalOn_iff, and_iff_right hu]

/-- The solenoidal `L²(μ)` fields are orthogonal to the closed span of the test gradients,
which is `wassersteinTangentSpace μ`. -/
theorem solenoidalLp_two_eq_orthogonal_wassersteinTangentSpace [FiniteDimensional ℝ E]
    (μ : Measure E) [IsFiniteMeasureOnCompacts μ] :
    (solenoidalLp E 2 μ).toSubmodule = (wassersteinTangentSpace μ)ᗮ := by
  ext u
  rw [ClosedSubmodule.mem_toSubmodule_iff, mem_solenoidalLp_iff_integral_inner_eq_zero,
    mem_orthogonal_wassersteinTangentSpace_iff]
  constructor
  · intro h φ hφ hc
    let ψ : 𝓓((⊤ : Opens E), ℝ) := ⟨φ, hφ, hc, by simp⟩
    simpa [inner_gradient_right, ψ] using h ψ
  · intro h φ
    simpa [inner_gradient_right] using h φ φ.contDiff φ.hasCompactSupport

end TauCeti
