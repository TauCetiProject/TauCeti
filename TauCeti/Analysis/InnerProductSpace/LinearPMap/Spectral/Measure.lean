/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5, OpenAI gpt-6.1-terra, OpenAI gpt-6.1-sol
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Cayley
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Cayley
public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Map
public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Representation.OfRepresentation

/-!
# The spectral measure of a self-adjoint partial operator

The Cayley transform of a self-adjoint partial operator is a bounded unitary operator.
Its continuous functional calculus has a projection-valued measure on its spectrum.
Pushing that measure forward by the real inverse Cayley coordinate gives a projection-valued
measure on the real line.

Adapted from `ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean`
in the Kitware DKPS formalization (Jon Crall and Claude Opus 5; Apache-2.0). The original
construction uses a local bounded Borel calculus; here `TauCeti.ProjValMeasure.ofRepresentation` and
`TauCeti.ProjValMeasure.map` give the construction directly.

## References

* M. Reed and B. Simon, *Methods of Modern Mathematical Physics I*, §VIII.3.
* K. Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*, §13.1.
-/

public section

noncomputable section

open MeasureTheory TauCeti

namespace IsSelfAdjoint

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)

/-- The spectral projection-valued measure of a self-adjoint partial operator, obtained by
reindexing the spectral measure of its Cayley transform. -/
def spectralPVM : ProjValMeasure ℝ H :=
  (ProjValMeasure.ofRepresentation (cfcHom hA.isStarNormal_cayley)).map
    (Complex.inverseCayleyCoord ∘ Subtype.val)
    (Complex.measurable_inverseCayleyCoord.comp measurable_subtype_coe)

/-- The spectral measure is the pushforward of the Cayley representation measure. -/
theorem spectralPVM_def :
    spectralPVM hA =
      (ProjValMeasure.ofRepresentation (cfcHom hA.isStarNormal_cayley)).map
        (Complex.inverseCayleyCoord ∘ Subtype.val)
        (Complex.measurable_inverseCayleyCoord.comp measurable_subtype_coe) := (rfl)

/-- Its projection of a Borel set is the Cayley spectral projection of the inverse image. -/
theorem spectralPVM_proj (B : Set ℝ) (hB : MeasurableSet B) :
    (spectralPVM hA).proj B hB =
      (ProjValMeasure.ofRepresentation (cfcHom hA.isStarNormal_cayley)).proj
        ((Complex.inverseCayleyCoord ∘ Subtype.val) ⁻¹' B)
        ((Complex.measurable_inverseCayleyCoord.comp measurable_subtype_coe) hB) := by
  rw [spectralPVM_def, ProjValMeasure.map_proj]

/-- The diagonal scalar measures are the pushforwards of the Cayley representation measures. -/
theorem spectralPVM_diag (ξ : H) :
    (spectralPVM hA).diag ξ =
      Measure.map (Complex.inverseCayleyCoord ∘ Subtype.val)
        ((cfcHom hA.isStarNormal_cayley).representationDiagMeasure ξ) := by
  rw [spectralPVM_def, ProjValMeasure.map_diag, ProjValMeasure.ofRepresentation_diag]

end IsSelfAdjoint
