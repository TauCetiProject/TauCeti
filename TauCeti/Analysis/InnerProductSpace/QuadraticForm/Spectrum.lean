/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 4.8, GPT 5.6 High
-/
module

public import TauCeti.Analysis.InnerProductSpace.ContinuousFunctionalCalculus
public import TauCeti.Analysis.InnerProductSpace.Projection.Completeness
public import TauCeti.Analysis.InnerProductSpace.QuadraticForm.Bounds

/-!
# Spectral bounds and quadratic forms

For bounded self-adjoint operators on complete Hilbert spaces over `RCLike`, a spectral
half-line gives the corresponding quadratic-form bound. Applied to an invariant orthogonally
complemented subspace, this turns the spectrum of the actual restriction into a form bound on
that subspace. These bridges allow spectral separation hypotheses to be used in form estimates.

## Provenance

Adapted from `ForTauCeti/Analysis/InnerProductSpace/SpectralOrder.lean` in the Kitware DKPS
formalization, Jon Crall, Claude Opus 4.8 and GPT 5.6 High, Apache-2.0. The original spectral-order
and restriction argument is retained; the continuous functional calculus and form-bound
predicates are the native APIs.
-/

public section

open scoped InnerProductSpace

namespace ContinuousLinearMap

attribute [local instance] realAlgebra realIsScalarTower

variable {𝕜 H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- A spectral upper bound implies a quadratic-form upper bound. -/
theorem re_inner_le_of_spectrum_subset_Iic
    (T : H →L[𝕜] H) (hT : IsSelfAdjoint T) {c : ℝ}
    (hσ : spectrum ℝ T ⊆ Set.Iic c) (x : H) :
    RCLike.re ⟪T x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2 := by
  have hle : T ≤ algebraMap ℝ (H →L[𝕜] H) c :=
    le_algebraMap_of_spectrum_le (fun r hr => hσ hr) hT
  have hpos : (algebraMap ℝ (H →L[𝕜] H) c - T).IsPositive := by
    rw [← ContinuousLinearMap.nonneg_iff_isPositive]
    exact sub_nonneg.mpr hle
  have hx := hpos.re_inner_nonneg_left x
  simp only [sub_apply, inner_sub_left, map_sub, re_inner_algebraMap_apply] at hx
  linarith

/-- A spectral lower bound implies a quadratic-form lower bound. -/
theorem le_re_inner_of_spectrum_subset_Ici
    (T : H →L[𝕜] H) (hT : IsSelfAdjoint T) {c : ℝ}
    (hσ : spectrum ℝ T ⊆ Set.Ici c) (x : H) :
    c * ‖x‖ ^ 2 ≤ RCLike.re ⟪T x, x⟫_𝕜 := by
  have hle : algebraMap ℝ (H →L[𝕜] H) c ≤ T :=
    algebraMap_le_of_le_spectrum (fun r hr => hσ hr) hT
  have hpos : (T - algebraMap ℝ (H →L[𝕜] H) c).IsPositive := by
    rw [← ContinuousLinearMap.nonneg_iff_isPositive]
    exact sub_nonneg.mpr hle
  have hx := hpos.re_inner_nonneg_left x
  simp only [sub_apply, inner_sub_left, map_sub, re_inner_algebraMap_apply] at hx
  linarith


/-- A spectral lower half-line for the restriction of a symmetric operator gives a lower
quadratic-form bound on the invariant subspace. -/
theorem lowerFormBoundOn_of_restriction_spectrum_subset_Ici
    {A : H →L[𝕜] H} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 H} [U.HasOrthogonalProjection]
    (hU : ∀ x ∈ U, A x ∈ U) {c : ℝ}
    (hσ : spectrum ℝ (A.restrict hU) ⊆ Set.Ici c) : A.LowerFormBoundOn U c := by
  let : CompleteSpace U :=
    completeSpace_coe_iff_isComplete.mpr U.isComplete_coe_of_hasOrthogonalProjection
  have hres : IsSelfAdjoint (A.restrict hU) :=
    isSelfAdjoint_iff_isSymmetric.mpr (hA.restrict_invariant hU)
  apply (lowerFormBoundOn_iff A U c).2
  intro x hx
  simpa only [Submodule.coe_inner, ContinuousLinearMap.coe_restrict_apply,
    ← Submodule.norm_coe, Subtype.coe_mk] using
    le_re_inner_of_spectrum_subset_Ici (A.restrict hU) hres hσ (⟨x, hx⟩ : U)

/-- A spectral upper half-line for the restriction of a symmetric operator gives an upper
quadratic-form bound on the invariant subspace. -/
theorem upperFormBoundOn_of_restriction_spectrum_subset_Iic
    {A : H →L[𝕜] H} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 H} [U.HasOrthogonalProjection]
    (hU : ∀ x ∈ U, A x ∈ U) {c : ℝ}
    (hσ : spectrum ℝ (A.restrict hU) ⊆ Set.Iic c) : A.UpperFormBoundOn U c := by
  let : CompleteSpace U :=
    completeSpace_coe_iff_isComplete.mpr U.isComplete_coe_of_hasOrthogonalProjection
  have hres : IsSelfAdjoint (A.restrict hU) :=
    isSelfAdjoint_iff_isSymmetric.mpr (hA.restrict_invariant hU)
  apply (upperFormBoundOn_iff A U c).2
  intro x hx
  simpa only [Submodule.coe_inner, ContinuousLinearMap.coe_restrict_apply,
    ← Submodule.norm_coe, Subtype.coe_mk] using
    re_inner_le_of_spectrum_subset_Iic (A.restrict hU) hres hσ (⟨x, hx⟩ : U)

end ContinuousLinearMap
