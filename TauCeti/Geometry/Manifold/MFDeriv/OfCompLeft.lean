/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft

/-!
# Lifting a manifold derivative through a map with a continuous linear left inverse

Let `φ : N → N'` have derivative `φ'` at `f x`, and let `L` be a continuous linear left inverse of
`φ'`. If `f` is continuous at `x` within `s` and `φ ∘ f` has derivative `h'` at `x` within `s`,
then `f` has derivative `L ∘ h'` at `x` within `s`. This is the manifold version of Mathlib's
`HasFDerivWithinAt.of_comp_of_leftInverse`, the easy half of the inverse function theorem, to which
it reduces in the extended charts at `x`, `f x` and `φ (f x)`. Only the derivative of `φ` at the
single point `f x` is used.

Continuity of `f` cannot be dropped: without it, `f` could jump between points with the same
image under `φ`.

## Main results

* `HasMFDerivWithinAt.of_comp_of_leftInverse`: a map that is continuous at `x` within `s` has
  derivative `L ∘ h'` there, if its composite with `φ` has derivative `h'` and `L` is a continuous
  linear left inverse of the derivative of `φ` at the image point.
-/

public section

open Function Filter Set
open scoped Manifold Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type*} [TopologicalSpace G]
  {J : ModelWithCorners 𝕜 F G} {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] {G' : Type*} [TopologicalSpace G']
  {J' : ModelWithCorners 𝕜 F' G'} {N' : Type*} [TopologicalSpace N'] [ChartedSpace G' N']
  {f : M → N} {φ : N → N'} {s : Set M} {x : M}

/-- **Lifting a derivative through a map whose differential has a continuous linear left
inverse.** If `φ` has derivative `φ'` at `f x`, `L` is a continuous linear left inverse of `φ'`,
`f` is continuous at `x` within `s`, and `φ ∘ f` has derivative `h'` at `x` within `s`, then `f` has
derivative `L ∘ h'` at `x` within `s`. This is the manifold version of
`HasFDerivWithinAt.of_comp_of_leftInverse`. -/
theorem HasMFDerivWithinAt.of_comp_of_leftInverse
    {φ' : TangentSpace J (f x) →L[𝕜] TangentSpace J' (φ (f x))}
    {h' : TangentSpace I x →L[𝕜] TangentSpace J' (φ (f x))}
    {L : TangentSpace J' (φ (f x)) →L[𝕜] TangentSpace J (f x)}
    (hφ : HasMFDerivAt J J' φ (f x) φ') (hf : ContinuousWithinAt f s x)
    (hh : HasMFDerivWithinAt I J' (φ ∘ f) s x h') (hL : LeftInverse L φ') :
    HasMFDerivWithinAt I J f s x (L ∘L h') := by
  -- Adding `x` to `s` changes none of the statements.
  rw [← continuousWithinAt_insert_self] at hf
  refine HasMFDerivWithinAt.of_insert (y := x) ⟨hf, ?_⟩
  -- Read in the extended charts, `f` is continuous into the range of the model at its image
  -- point, and `φ ∘ f` is `φ` after `f` near the base point.
  have hb : writtenInExtChartAt I J x f (extChartAt I x x) = extChartAt J (f x) (f x) :=
    writtenInExtChartAt_apply_extChartAt (mem_extChartAt_source x)
  have hst : Tendsto (writtenInExtChartAt I J x f)
      (𝓝[(extChartAt I x).symm ⁻¹' insert x s ∩ range I] extChartAt I x x)
      (𝓝[range J] writtenInExtChartAt I J x f (extChartAt I x x)) := by
    rw [hb]
    exact Tendsto.comp (map_extChartAt_nhds (I := J) (f x)).le
      (hf.tendsto.comp (map_extChartAt_symm_nhdsWithin (I := I) x).le)
  have hφ' := hφ.2
  rw [← hb] at hφ'
  -- The left inverse of `φ'`, read through the identifications of tangent spaces with models.
  have hL' : LeftInverse
      ((tangentSpaceCastModel J (f x)).toContinuousLinearMap ∘L L ∘L
        (tangentSpaceCastModel J' (φ (f x))).symm.toContinuousLinearMap)
      ((tangentSpaceCastModel J' (φ (f x))).toContinuousLinearMap ∘L φ' ∘L
        (tangentSpaceCastModel J (f x)).symm.toContinuousLinearMap) := fun y ↦ by
    simp [hL _]
  refine (hφ'.of_comp_of_leftInverse hst hh.insert.2 (writtenInExtChartAt_comp hf).symm hL'
    ⟨by simp, mem_range_self _⟩).congr_fderiv ?_
  ext y
  simp
