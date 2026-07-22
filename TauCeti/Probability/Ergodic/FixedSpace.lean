module

public import Mathlib.MeasureTheory.Function.LpSpace.Complete
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

variable {Ω 𝕜 E : Type*} [MeasurableSpace Ω] [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure Ω}

/-- A fixed `Lᵖ` observable is represented by a function invariant under `T` almost
everywhere. -/
theorem comp_ae_eq_self_of_mem_fixedSubmodule {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {g : Lp E p μ}
    (hg : g ∈ (Lp.compMeasurePreservingₗᵢ 𝕜 T hT).toLinearMap.fixedSubmodule) :
    (g : Ω → E) ∘ T =ᵐ[μ] g := by
  have hcomp : Lp.compMeasurePreserving T hT g = g := LinearMap.mem_fixedSubmodule_iff.mp hg
  simpa only [hcomp] using (Lp.coeFn_compMeasurePreserving g hT).symm

/-- An `Lᵖ` observable represented by a function invariant under `T` almost everywhere belongs
to the fixed submodule of the composition isometry. -/
theorem mem_fixedSubmodule_of_comp_ae_eq_self {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {g : Lp E p μ} (hg : (g : Ω → E) ∘ T =ᵐ[μ] g) :
    g ∈ (Lp.compMeasurePreservingₗᵢ 𝕜 T hT).toLinearMap.fixedSubmodule := by
  rw [LinearMap.mem_fixedSubmodule_iff]
  apply Lp.ext
  exact (Lp.coeFn_compMeasurePreserving g hT).trans hg

/-- Characterization of fixed points of the `Lᵖ` composition isometry using representatives. -/
theorem mem_fixedSubmodule_iff_comp_ae_eq_self {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) (g : Lp E p μ) :
    g ∈ (Lp.compMeasurePreservingₗᵢ 𝕜 T hT).toLinearMap.fixedSubmodule ↔
      (g : Ω → E) ∘ T =ᵐ[μ] g :=
  ⟨comp_ae_eq_self_of_mem_fixedSubmodule hT, mem_fixedSubmodule_of_comp_ae_eq_self hT⟩

end TauCeti.Probability
