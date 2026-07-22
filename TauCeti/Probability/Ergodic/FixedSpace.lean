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

section Generic

variable {Ω 𝕜 E : Type*} [MeasurableSpace Ω] [NormedRing 𝕜] [NormedAddCommGroup E]
  [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
variable {p : ℝ≥0∞} {μ : Measure Ω}

/-- The submodule of `Lᵖ` observables fixed by composition with a measure-preserving
transformation. -/
def fixedSpace (T : Ω → Ω) (hT : MeasurePreserving T μ μ) : Submodule 𝕜 (Lp E p μ) :=
  (Lp.compMeasurePreservingₗ 𝕜 T hT).fixedSubmodule

/-- Characterization of fixed points of the `Lᵖ` composition isometry using representatives. -/
@[simp]
theorem mem_fixedSpace_iff_comp_ae_eq_self {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) (g : Lp E p μ) :
    g ∈ fixedSpace (𝕜 := 𝕜) T hT ↔ (g : Ω → E) ∘ T =ᵐ[μ] g := by
  change Lp.compMeasurePreserving T hT g = g ↔ _
  constructor
  · intro hg
    simpa only [hg] using (Lp.coeFn_compMeasurePreserving g hT).symm
  · intro hg
    apply Lp.ext
    exact (Lp.coeFn_compMeasurePreserving g hT).trans hg

/-- The fixed space of the identity transformation is all of `Lᵖ`. -/
@[simp]
theorem fixedSpace_id :
    fixedSpace (μ := μ) (𝕜 := 𝕜) (E := E) (p := p) id (MeasurePreserving.id μ) = ⊤ := by
  ext g
  simp [mem_fixedSpace_iff_comp_ae_eq_self]

/-- Every observable fixed by `T` is fixed by every iterate of `T`. -/
theorem mem_fixedSpace_iterate {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {g : Lp E p μ} (hg : g ∈ fixedSpace (𝕜 := 𝕜) T hT) (n : ℕ) :
    g ∈ fixedSpace (𝕜 := 𝕜) (T^[n]) (hT.iterate n) := by
  rw [fixedSpace, LinearMap.mem_fixedSubmodule_iff] at hg ⊢
  change Lp.compMeasurePreserving T hT g = g at hg
  change Lp.compMeasurePreserving (T^[n]) (hT.iterate n) g = g
  rw [← Lp.compMeasurePreserving_iterate]
  exact IsFixedPt.iterate hg n

end Generic

section Complete

variable {Ω 𝕜 E : Type*} [MeasurableSpace Ω] [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure Ω}

/-- The fixed space is closed in `Lᵖ`. -/
theorem isClosed_fixedSpace (T : Ω → Ω) (hT : MeasurePreserving T μ μ) :
    IsClosed (fixedSpace (𝕜 := 𝕜) (E := E) (p := p) T hT : Set (Lp E p μ)) := by
  change IsClosed
    (((Lp.compMeasurePreservingₗᵢ 𝕜 T hT).toContinuousLinearMap.eqLocus 1 :
      Submodule 𝕜 (Lp E p μ)) : Set (Lp E p μ))
  exact (Lp.compMeasurePreservingₗᵢ 𝕜 T hT).toContinuousLinearMap.isClosed_eqLocus
    (1 : Lp E p μ →L[𝕜] Lp E p μ)

variable [CompleteSpace E]

instance fixedSpace.completeSpace (T : Ω → Ω) (hT : MeasurePreserving T μ μ) :
    CompleteSpace (fixedSpace (𝕜 := 𝕜) (E := E) (p := p) T hT) := by
  change CompleteSpace
    ((Lp.compMeasurePreservingₗᵢ 𝕜 T hT).toContinuousLinearMap.toLinearMap.eqLocus
      (1 : Lp E p μ →L[𝕜] Lp E p μ).toLinearMap)
  infer_instance

end Complete

end TauCeti.Probability
