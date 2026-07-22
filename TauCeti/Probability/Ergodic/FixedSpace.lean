module

public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Fixed space of a measure-preserving transformation

This file packages the fixed-point subspace for the composition operator of a
measure-preserving transformation on `L²`.  This is the closed subspace onto which the mean
ergodic projection in the Koopman route to de Finetti's theorem will project.

Mathlib already supplies the composition linear isometry
`MeasureTheory.Lp.compMeasurePreservingₗᵢ` and the abstract mean ergodic theorem.  We use those
directly: `fixedSpace` is the equality locus of the composition operator and the identity.
-/

public section

noncomputable section

open Function MeasureTheory

namespace TauCeti.Probability

variable {Ω 𝕜 : Type*} [MeasurableSpace Ω] [RCLike 𝕜] {μ : Measure Ω}

/-- The continuous linear composition operator on `L²` associated to a measure-preserving
transformation.  This is a change-of-presentation accessor for Mathlib's linear isometry, used
to feed the continuous-linear-map mean ergodic API. -/
abbrev compMeasurePreservingL2 (T : Ω → Ω) (hT : MeasurePreserving T μ μ) :
    Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 2 μ :=
  (Lp.compMeasurePreservingₗᵢ 𝕜 T hT).toContinuousLinearMap

/-- The subspace of `L²` observables fixed by composition with a measure-preserving
transformation. -/
abbrev fixedSpace (T : Ω → Ω) (hT : MeasurePreserving T μ μ) : Submodule 𝕜 (Lp 𝕜 2 μ) :=
  (compMeasurePreservingL2 T hT).eqLocus 1

/-- Membership in `fixedSpace` means invariance under the composition operator. -/
@[simp]
theorem mem_fixedSpace_iff {T : Ω → Ω} (hT : MeasurePreserving T μ μ) (g : Lp 𝕜 2 μ) :
    g ∈ fixedSpace T hT ↔ Lp.compMeasurePreserving T hT g = g := by
  rfl

/-- A fixed `L²` observable is represented by a function invariant under `T` almost
everywhere. -/
theorem comp_ae_eq_of_mem_fixedSpace {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {g : Lp 𝕜 2 μ} (hg : g ∈ fixedSpace T hT) :
    (g : Ω → 𝕜) ∘ T =ᵐ[μ] g := by
  have hcomp : Lp.compMeasurePreserving T hT g = g := (mem_fixedSpace_iff hT g).mp hg
  simpa only [hcomp] using (Lp.coeFn_compMeasurePreserving g hT).symm

/-- An `L²` observable represented by a function invariant under `T` almost everywhere belongs
to `fixedSpace`. -/
theorem mem_fixedSpace_of_comp_ae_eq {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {g : Lp 𝕜 2 μ} (hg : (g : Ω → 𝕜) ∘ T =ᵐ[μ] g) :
    g ∈ fixedSpace T hT := by
  rw [mem_fixedSpace_iff]
  apply Lp.ext
  exact (Lp.coeFn_compMeasurePreserving g hT).trans hg

/-- Characterization of the fixed space using representatives of `L²` classes. -/
theorem mem_fixedSpace_iff_comp_ae_eq {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    (g : Lp 𝕜 2 μ) :
    g ∈ fixedSpace T hT ↔ (g : Ω → 𝕜) ∘ T =ᵐ[μ] g :=
  ⟨comp_ae_eq_of_mem_fixedSpace hT, mem_fixedSpace_of_comp_ae_eq hT⟩

/-- The fixed space of the identity transformation is all of `L²`. -/
@[simp]
theorem fixedSpace_id :
    fixedSpace (μ := μ) (𝕜 := 𝕜) id (MeasurePreserving.id μ) = ⊤ := by
  rw [eq_top_iff]
  intro g _
  rw [mem_fixedSpace_iff]
  exact Lp.compMeasurePreserving_id_apply g

/-- Every observable fixed by `T` is fixed by every iterate of `T`. -/
theorem mem_fixedSpace_iterate {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {g : Lp 𝕜 2 μ} (hg : g ∈ fixedSpace T hT) (n : ℕ) :
    g ∈ fixedSpace (T^[n]) (hT.iterate n) := by
  rw [mem_fixedSpace_iff, ← Lp.compMeasurePreserving_iterate]
  exact IsFixedPt.iterate (mem_fixedSpace_iff hT g |>.mp hg) n

instance fixedSpace.completeSpace (T : Ω → Ω) (hT : MeasurePreserving T μ μ) :
    CompleteSpace (fixedSpace (𝕜 := 𝕜) T hT) := by
  rw [fixedSpace]
  exact (ContinuousLinearMap.isComplete_eqLocus (compMeasurePreservingL2 T hT)
    (1 : Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 2 μ)).completeSpace_coe

/-- The fixed space is closed in `L²`. -/
theorem isClosed_fixedSpace (T : Ω → Ω) (hT : MeasurePreserving T μ μ) :
    IsClosed (fixedSpace (𝕜 := 𝕜) T hT : Set (Lp 𝕜 2 μ)) :=
  ContinuousLinearMap.isClosed_eqLocus (compMeasurePreservingL2 T hT)
    (1 : Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 2 μ)

end TauCeti.Probability
