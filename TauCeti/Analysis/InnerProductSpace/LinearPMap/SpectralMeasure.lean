/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5, OpenAI gpt-6.1-terra
-/
module

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
construction uses a local bounded Borel calculus; here the accepted projection-valued measure
of a representation and measurable reindexing give the construction directly.

## References

* M. Reed and B. Simon, *Methods of Modern Mathematical Physics I*, §VIII.3.
* K. Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*, §13.1.
-/

public section

noncomputable section

open MeasureTheory TauCeti

namespace LinearPMap

/-- The real inverse Cayley coordinate, with value zero at the singular point `1`. -/
def inverseCayleyCoord (w : ℂ) : ℝ := (Complex.I * (1 + w) / (1 - w)).re

/-- Formula for the real inverse Cayley coordinate. -/
theorem inverseCayleyCoord_def (w : ℂ) :
    inverseCayleyCoord w = (Complex.I * (1 + w) / (1 - w)).re := (rfl)

/-- The inverse Cayley coordinate is measurable. -/
theorem measurable_inverseCayleyCoord : Measurable inverseCayleyCoord := by
  unfold inverseCayleyCoord
  fun_prop

/-- The inverse Cayley coordinate has value zero at `1`. -/
@[simp] theorem inverseCayleyCoord_one : inverseCayleyCoord 1 = 0 := by
  simp [inverseCayleyCoord]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)

/-- The spectral projection-valued measure of a self-adjoint partial operator, obtained by
reindexing the spectral measure of its Cayley transform. -/
def spectralPVM : ProjValMeasure ℝ H :=
  (ProjValMeasure.ofRepresentation (cfcHom hA.isStarNormal_cayley)).map
    (inverseCayleyCoord ∘ Subtype.val) (measurable_inverseCayleyCoord.comp measurable_subtype_coe)

/-- The spectral measure is the pushforward of the Cayley representation measure. -/
theorem spectralPVM_def :
    spectralPVM hA =
      (ProjValMeasure.ofRepresentation (cfcHom hA.isStarNormal_cayley)).map
        (inverseCayleyCoord ∘ Subtype.val)
        (measurable_inverseCayleyCoord.comp measurable_subtype_coe) := (rfl)

/-- Its projection of a Borel set is the Cayley spectral projection of the inverse image. -/
theorem spectralPVM_proj (B : Set ℝ) (hB : MeasurableSet B) :
    (spectralPVM hA).proj B hB =
      (ProjValMeasure.ofRepresentation (cfcHom hA.isStarNormal_cayley)).proj
        ((inverseCayleyCoord ∘ Subtype.val) ⁻¹' B)
        ((measurable_inverseCayleyCoord.comp measurable_subtype_coe) hB) := by
  rw [spectralPVM_def, ProjValMeasure.map_proj]

/-- The diagonal scalar measures are the pushforwards of the Cayley representation measures. -/
theorem spectralPVM_diag (ξ : H) :
    (spectralPVM hA).diag ξ =
      Measure.map (inverseCayleyCoord ∘ Subtype.val)
        ((cfcHom hA.isStarNormal_cayley).representationDiagMeasure ξ) := by
  rw [spectralPVM_def, ProjValMeasure.map_diag, ProjValMeasure.ofRepresentation_diag]

end LinearPMap
