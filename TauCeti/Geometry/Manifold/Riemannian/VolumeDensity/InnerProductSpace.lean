/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giada Franz, The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Basic
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Volume
import TauCeti.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# The Riemannian volume of a Euclidean space

For a finite-dimensional real inner product space `E`, viewed as a Riemannian manifold modelled
on itself with its standard metric, the chart Gram matrix in the identity chart is the Gram matrix
of the model basis, so the chart volume is the volume measure of `E`. Hence the Riemannian volume
of a Euclidean space is its volume measure.

Ported from Giada Franz's `ForTauCeti` formalization.

## Main results

* `TauCeti.riemannianVolume_eq_volume`: the Riemannian volume of `E` is `volume`.
-/

public section

open Bundle FiberBundle MeasureTheory Riemannian.Tensor Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The standard metric of a Euclidean space is a continuous Riemannian bundle. -/
local instance instIsContinuousRiemannianBundleInnerProductSpace :
    IsContinuousRiemannianBundle E (fun x : E ↦ TangentSpace 𝓘(ℝ, E) x) :=
  IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := 𝓘(ℝ, E)) (n := ∞)

omit [MeasurableSpace E] [BorelSpace E] in
/-- In the identity chart of `E`, the Gram matrix of the standard metric is that of the model
basis. -/
private theorem chartGramMatrix_innerProductSpace (α z : E) :
    chartGramMatrix (I := 𝓘(ℝ, E)) α z = Matrix.gram ℝ (Module.finBasis ℝ E) := by
  ext i j
  have hz : z ∈ (chartAt E α).source := by simp
  rw [chartGramMatrix_apply, chartLocalFrame_apply_of_mem_chart_source α hz,
    chartLocalFrame_apply_of_mem_chart_source α hz]
  have hsymm (v : E) : (trivializationAt E (TangentSpace 𝓘(ℝ, E)) α).symm z v = v := by
    rw [← Trivialization.symmL_apply (R := ℝ) (trivializationAt E (TangentSpace 𝓘(ℝ, E)) α)
      (mem_univ z), TangentBundle.symmL_model_space]
    rfl
  rw [Matrix.gram_apply]
  simp only [Trivialization.basisAt, Module.Basis.map_apply,
    Trivialization.linearEquivAt_symm_apply, hsymm]
  rfl

/-- The Riemannian volume of a Euclidean space is its volume measure. -/
@[simp] theorem riemannianVolume_eq_volume :
    riemannianVolume 𝓘(ℝ, E) E = (volume : Measure E) := by
  obtain rfl : ‹MeasurableSpace E› = borel E := BorelSpace.measurable_eq
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  symm
  rw [eq_riemannianVolume_iff]
  intro α
  ext s hs
  rw [chartRiemannianVolume_apply α hs, Measure.restrict_apply hs,
    (Module.finBasis ℝ E).volume_eq_smul_addHaar]
  simp only [chartVolumeDensity_def, chartGramMatrix_innerProductSpace, inter_univ,
    chartAt_self_eq, OpenPartialHomeomorph.refl_source, extChartAt_model_space_eq_id,
    PartialEquiv.refl_coe, PartialEquiv.refl_source, image_id, setLIntegral_const,
    smul_apply, smul_eq_mul]

end TauCeti
