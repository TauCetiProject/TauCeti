module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.LinearAlgebra.FixedSubmodule

/-!
# Fixed points of a measure-preserving transformation on `Lᵖ`

This file relates membership in Mathlib's fixed submodule for the `Lᵖ` composition isometry to
almost-everywhere invariance of representatives. This is the closed subspace onto which the mean
ergodic projection in the Koopman route to de Finetti's theorem will project.
-/

public section

noncomputable section

open Function MeasureTheory
open scoped ENNReal

namespace TauCeti.Probability

variable {Ω 𝕜 E : Type*} [MeasurableSpace Ω] [NormedRing 𝕜] [NormedAddCommGroup E]
  [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
variable {p : ℝ≥0∞} {μ : Measure Ω}

/-- Characterization of fixed points of the `Lᵖ` composition isometry using representatives. -/
@[simp]
theorem mem_fixedSubmodule_iff_comp_ae_eq_self {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) (g : Lp E p μ) :
    g ∈ (Lp.compMeasurePreservingₗ 𝕜 T hT).fixedSubmodule ↔
      (g : Ω → E) ∘ T =ᵐ[μ] g := by
  rw [LinearMap.mem_fixedSubmodule_iff]
  constructor
  · intro hg
    have hcomp : Lp.compMeasurePreserving T hT g = g := hg
    simpa only [hcomp] using (Lp.coeFn_compMeasurePreserving g hT).symm
  · intro hg
    apply Lp.ext
    exact (Lp.coeFn_compMeasurePreserving g hT).trans hg

end TauCeti.Probability
