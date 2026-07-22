module

public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# Fixed space of a measure-preserving transformation

This file packages the fixed-point subspace for the composition operator of a
measure-preserving transformation on `Lᵖ`. This is the closed subspace onto which the mean
ergodic projection in the Koopman route to de Finetti's theorem will project.

Mathlib already supplies the composition linear isometry
`MeasureTheory.Lp.compMeasurePreservingₗᵢ` and the abstract mean ergodic theorem. We use those
directly: `fixedSpace` is the equality locus of the composition operator and the identity.
-/

public section

noncomputable section

open Function MeasureTheory
open scoped ENNReal

namespace TauCeti.Probability

variable {Ω 𝕜 E : Type*} [MeasurableSpace Ω] [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure Ω}

/-- The continuous linear composition operator on `Lᵖ` associated to a measure-preserving
transformation. This packages Mathlib's linear isometry as a continuous linear map. -/
def compMeasurePreservingLp (T : Ω → Ω) (hT : MeasurePreserving T μ μ) :
    Lp E p μ →L[𝕜] Lp E p μ :=
  (Lp.compMeasurePreservingₗᵢ 𝕜 T hT).toContinuousLinearMap

/-- Applying the continuous linear composition operator agrees with Mathlib's composition map. -/
@[simp]
theorem compMeasurePreservingLp_apply (T : Ω → Ω) (hT : MeasurePreserving T μ μ)
    (g : Lp E p μ) :
    compMeasurePreservingLp (𝕜 := 𝕜) T hT g = Lp.compMeasurePreserving T hT g := by
  rfl

/-- The composition operator is a contraction. -/
theorem norm_compMeasurePreservingLp_le (T : Ω → Ω) (hT : MeasurePreserving T μ μ) :
    ‖compMeasurePreservingLp (𝕜 := 𝕜) (E := E) (p := p) T hT‖ ≤ 1 :=
  LinearIsometry.norm_toContinuousLinearMap_le _

/-- The subspace of `Lᵖ` observables fixed by composition with a measure-preserving
transformation. -/
def fixedSpace (T : Ω → Ω) (hT : MeasurePreserving T μ μ) : Submodule 𝕜 (Lp E p μ) :=
  (compMeasurePreservingLp T hT).eqLocus 1

/-- Membership in `fixedSpace` means invariance under the composition operator. -/
@[simp]
theorem mem_fixedSpace_iff {T : Ω → Ω} (hT : MeasurePreserving T μ μ) (g : Lp E p μ) :
    g ∈ fixedSpace (𝕜 := 𝕜) T hT ↔ Lp.compMeasurePreserving T hT g = g := by
  rw [fixedSpace, LinearMap.mem_eqLocus]
  simp

/-- A fixed `Lᵖ` observable is represented by a function invariant under `T` almost
everywhere. -/
theorem comp_ae_eq_self_of_mem_fixedSpace {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {g : Lp E p μ} (hg : g ∈ fixedSpace (𝕜 := 𝕜) T hT) :
    (g : Ω → E) ∘ T =ᵐ[μ] g := by
  have hcomp : Lp.compMeasurePreserving T hT g = g := (mem_fixedSpace_iff hT g).mp hg
  simpa only [hcomp] using (Lp.coeFn_compMeasurePreserving g hT).symm

/-- An `Lᵖ` observable represented by a function invariant under `T` almost everywhere belongs
to `fixedSpace`. -/
theorem mem_fixedSpace_of_comp_ae_eq_self {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {g : Lp E p μ} (hg : (g : Ω → E) ∘ T =ᵐ[μ] g) :
    g ∈ fixedSpace (𝕜 := 𝕜) T hT := by
  rw [mem_fixedSpace_iff]
  apply Lp.ext
  exact (Lp.coeFn_compMeasurePreserving g hT).trans hg

/-- Characterization of the fixed space using representatives of `Lᵖ` classes. -/
theorem mem_fixedSpace_iff_comp_ae_eq_self {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    (g : Lp E p μ) :
    g ∈ fixedSpace (𝕜 := 𝕜) T hT ↔ (g : Ω → E) ∘ T =ᵐ[μ] g :=
  ⟨comp_ae_eq_self_of_mem_fixedSpace hT, mem_fixedSpace_of_comp_ae_eq_self hT⟩

/-- The fixed space of the identity transformation is all of `Lᵖ`. -/
@[simp]
theorem fixedSpace_id :
    fixedSpace (μ := μ) (𝕜 := 𝕜) (E := E) (p := p) id (MeasurePreserving.id μ) = ⊤ := by
  rw [eq_top_iff]
  intro g _
  rw [mem_fixedSpace_iff]
  exact Lp.compMeasurePreserving_id_apply g

/-- Every observable fixed by `T` is fixed by every iterate of `T`. -/
theorem mem_fixedSpace_iterate {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {g : Lp E p μ} (hg : g ∈ fixedSpace (𝕜 := 𝕜) T hT) (n : ℕ) :
    g ∈ fixedSpace (𝕜 := 𝕜) (T^[n]) (hT.iterate n) := by
  rw [mem_fixedSpace_iff, ← Lp.compMeasurePreserving_iterate]
  exact IsFixedPt.iterate (mem_fixedSpace_iff hT g |>.mp hg) n

instance fixedSpace.completeSpace [CompleteSpace E] (T : Ω → Ω)
    (hT : MeasurePreserving T μ μ) :
    CompleteSpace (fixedSpace (𝕜 := 𝕜) (E := E) (p := p) T hT) := by
  rw [fixedSpace]
  change CompleteSpace ((compMeasurePreservingLp (𝕜 := 𝕜) T hT).toLinearMap.eqLocus
    (1 : Lp E p μ →L[𝕜] Lp E p μ).toLinearMap)
  infer_instance

/-- The fixed space is closed in `Lᵖ`. -/
theorem isClosed_fixedSpace (T : Ω → Ω) (hT : MeasurePreserving T μ μ) :
    IsClosed (fixedSpace (𝕜 := 𝕜) (E := E) (p := p) T hT : Set (Lp E p μ)) := by
  rw [fixedSpace]
  exact ContinuousLinearMap.isClosed_eqLocus (compMeasurePreservingLp T hT)
    (1 : Lp E p μ →L[𝕜] Lp E p μ)

end TauCeti.Probability
