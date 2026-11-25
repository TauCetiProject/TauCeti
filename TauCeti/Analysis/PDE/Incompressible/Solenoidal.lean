/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Incompressible.WeakDivergence
public import Mathlib.Topology.Algebra.Module.ClosedSubmodule
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.TangentSpace
import TauCeti.Analysis.Distribution.TestFunction.Gradient
import TauCeti.MeasureTheory.Function.Lp.Duality

/-!
# Solenoidal subspaces

The submodule `TestFunction.solenoidalSubmodule` consists exactly of weakly solenoidal test
fields. In `Lᵖ`, the solenoidal fields form the intersection of the kernels of the
continuous pairings with scalar test gradients. At `p = 2`, these pairings are Hilbert space inner
products, so the closed subspace is the orthogonal complement of the closed span of the test
gradients, given by `TauCeti.wassersteinTangentSpace`.
-/

public section

open MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal Gradient InnerProductSpace

namespace TestFunction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Ω : Opens E}

variable [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- A test field belongs to the kernel of divergence exactly when its underlying field is
weakly solenoidal. -/
theorem mem_solenoidalSubmodule_iff_isSolenoidalOn {φ : 𝓓(Ω, E)} :
    φ ∈ solenoidalSubmodule Ω ↔ TauCeti.IsSolenoidalOn μ Ω (φ : E → E) := by
  have hφ : ContDiffOn ℝ 1 (φ : E → E) Ω := (φ.contDiff.of_le (by simp)).contDiffOn
  rw [hφ.isSolenoidalOn_iff, mem_solenoidalSubmodule_iff]
  constructor
  · intro h x _
    simpa only [divergenceCLM_apply, FunLike.coe_zero, Pi.zero_apply] using congrArg (· x) h
  · intro h
    ext x
    by_cases hx : x ∈ (Ω : Set E)
    · simpa only [divergenceCLM_apply, FunLike.coe_zero, Pi.zero_apply] using h x hx
    · rw [(divergenceCLM φ).zero_on_compl hx, FunLike.coe_zero, Pi.zero_apply]

end TestFunction

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

section Lp

variable (E) (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- The closed subspace of `Lᵖ(E; E)` consisting of fields with zero weak divergence.
It is defined by continuous pairings with test gradients, including at `p = 1` and `p = ∞`. -/
noncomputable def solenoidalLp : ClosedSubmodule ℝ (Lp E p (volume : Measure E)) :=
  haveI : (ENNReal.conjExponent p).HolderConjugate p :=
    (ENNReal.HolderConjugate.conjExponent Fact.out).symm
  ⨅ φ : 𝓓((⊤ : Opens E), ℝ), (⊥ : ClosedSubmodule ℝ ℝ).comap
    (MemLp.innerLpCLM ℝ ((TestFunction.gradientCLM φ).continuous.memLp_of_hasCompactSupport
      (p := p.conjExponent) (μ := volume) (TestFunction.gradientCLM φ).hasCompactSupport))

variable {E p}

/-- Membership in the closed solenoidal subspace is equivalent to annihilating every test
gradient. -/
theorem mem_solenoidalLp_iff_integral_inner_eq_zero {u : Lp E p (volume : Measure E)} :
    u ∈ solenoidalLp E p ↔ ∀ φ : 𝓓((⊤ : Opens E), ℝ), ∫ x, ⟪u x, ∇ (φ : E → ℝ) x⟫_ℝ = 0 := by
  simp only [solenoidalLp, ClosedSubmodule.mem_iInf, ClosedSubmodule.mem_comap,
    ClosedSubmodule.mem_bot, MemLp.innerLpCLM_apply]
  simp_rw [← TestFunction.gradientCLM_apply, real_inner_comm]

/-- The closed solenoidal subspace consists of precisely the fields whose representatives
have weak divergence zero on the whole space. -/
@[simp]
theorem mem_solenoidalLp_iff {u : Lp E p (volume : Measure E)} :
    u ∈ solenoidalLp E p ↔ IsSolenoidalOn volume ⊤ (u : E → E) := by
  have hu : LocallyIntegrableOn (u : E → E) (⊤ : Opens E) volume :=
    ((Lp.memLp u).locallyIntegrable Fact.out).locallyIntegrableOn _
  rw [mem_solenoidalLp_iff_integral_inner_eq_zero, isSolenoidalOn_iff, and_iff_right hu]

end Lp

/-- The solenoidal `L²` fields are orthogonal to the closed span of the test gradients,
which is `wassersteinTangentSpace` at Lebesgue measure. -/
theorem solenoidalLp_two_eq_orthogonal_wassersteinTangentSpace :
    (solenoidalLp E 2).toSubmodule = (wassersteinTangentSpace (volume : Measure E))ᗮ := by
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
