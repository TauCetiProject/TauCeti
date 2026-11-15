/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.ContinuousInverse
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Lifting the velocity of a curve through a map with injective differential

Let `e : M → F` be a map from a manifold into a normed space whose differential at `γ t` has a
continuous left inverse, and let `γ` be a curve in `M` which is continuous at `t` within a
parameter set `s`. If the image curve `e ∘ γ` is differentiable at `t` within `s` with derivative
`d e (γ t) w`, then `γ` itself is differentiable at `t` within `s`, with velocity `w`
(`ContinuousWithinAt.hasMFDerivWithinAt_of_hasDerivWithinAt_comp`). When `F` is
finite-dimensional over a complete field, an injective differential has a continuous left inverse
(`ContinuousAt.hasMFDerivAt_of_hasDerivAt_comp`).

Read in the extended chart `φ` at `γ t`, the map `e` becomes a map `g` on the model space with
derivative `d e (γ t)` within the range of the model, and `g ∘ φ ∘ γ = e ∘ γ` near `t`. Mathlib's
easy half of the inverse function theorem, `HasFDerivWithinAt.of_comp_of_leftInverse`, then
differentiates `φ ∘ γ`.

This is the converse of the chain rule along a curve,
`TauCeti.Manifold.hasDerivWithinAt_comp_curve`. It is how a curve in a manifold is recognized as
an integral curve from its image in an ambient vector space, for instance after an embedding of a
compact manifold into Euclidean space: there the curve is obtained as a limit, and only its image
is known to be differentiable. Mathlib's `ContMDiffAt.iff_comp_isImmersionAt` lifts `C^n`
regularity of `e ∘ γ` on a neighbourhood of `t` through an immersion `e` near `γ t`; here only
differentiability of `e ∘ γ` at the single parameter `t`, and a left inverse of the differential
of `e` at the single point `γ t`, are used. Continuity of `γ` cannot be dropped, since without it
`γ` could jump between points with the same image near `e (γ t)`, which an injective differential
only excludes locally.

## Main results

* `ContinuousWithinAt.hasMFDerivWithinAt_of_hasDerivWithinAt_comp`: the velocity of a continuous
  curve is determined by the derivative of its image under a map whose differential has a
  continuous left inverse.
* `ContinuousAt.hasMFDerivAt_of_hasDerivAt_comp`: the unrestricted case, for a map with injective
  differential into a finite-dimensional space.
-/

public section

noncomputable section

open Function Set Filter
open scoped Manifold Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {e : M → F} {γ : 𝕜 → M} {s : Set 𝕜} {t : 𝕜} {w : TangentSpace I (γ t)}

/-- **Lifting a velocity through a map whose differential has a left inverse.** Let `e : M → F` be
a map into a normed space whose differential at `γ t` has a continuous left inverse. If the curve
`γ` is continuous at `t` within `s` and `e ∘ γ` has derivative `d e (γ t) w` at `t` within `s`,
then `γ` has velocity `w` at `t` within `s`. -/
theorem ContinuousWithinAt.hasMFDerivWithinAt_of_hasDerivWithinAt_comp
    (hγ : ContinuousWithinAt γ s t) (he : (mvfderiv I e (γ t)).HasLeftInverse)
    (h : HasDerivWithinAt (e ∘ γ) (mvfderiv I e (γ t) w) s t) :
    HasMFDerivWithinAt 𝓘(𝕜, 𝕜) I γ s t ((1 : 𝕜 →L[𝕜] 𝕜).smulRight w) := by
  -- Adding `t` to `s` changes none of the three statements.
  rw [← continuousWithinAt_insert_self] at hγ
  replace h := hasFDerivWithinAt_insert_self.2 h.hasFDerivWithinAt
  refine HasMFDerivWithinAt.of_insert (y := t) ?_
  set φ := extChartAt I (γ t)
  obtain ⟨L, hL⟩ := he
  have hd : MDifferentiableAt I 𝓘(𝕜, F) e (γ t) :=
    mdifferentiableAt_of_mfderiv_injective (TauCeti.injective_mvfderiv_iff.1 hL.injective)
  -- The map `e` read in the chart at `γ t` has derivative `d e (γ t)` within the range of `I`.
  have hg : HasFDerivWithinAt (writtenInExtChartAt I 𝓘(𝕜, F) (γ t) e) (mvfderiv I e (γ t))
      (range I) (φ (γ t)) := by
    rw [hd.mvfderiv]
    exact hd.differentiableWithinAt_writtenInExtChartAt.hasFDerivWithinAt
  have hst : Tendsto (φ ∘ γ) (𝓝[insert t s] t) (𝓝[range I] (φ (γ t))) :=
    tendsto_nhdsWithin_iff.2 ⟨(continuousAt_extChartAt (γ t)).comp_continuousWithinAt hγ,
      Eventually.of_forall fun y ↦ by rw [comp_apply, extChartAt_coe]; exact mem_range_self _⟩
  -- Near `t`, reading `e` in the charts recovers `e ∘ γ`, since the chart of `F` is the identity.
  have hcomp : writtenInExtChartAt I 𝓘(𝕜, F) (γ t) e ∘ (φ ∘ γ) =ᶠ[𝓝[insert t s] t] e ∘ γ := by
    filter_upwards [hγ (extChartAt_source_mem_nhds (I := I) (γ t))] with y hy
    rw [comp_apply, comp_apply, writtenInExtChartAt_apply_extChartAt hy,
      ext_chart_model_space_apply, comp_apply]
  -- `HasMFDerivWithinAt` reads `γ` in the charts, which is `φ ∘ γ` since the chart of `𝕜` is the
  -- identity, and its derivative through the identifications of the tangent spaces with `𝕜`
  -- and `E` is the one obtained by cancelling the left inverse `L`.
  have hderiv : HasFDerivWithinAt (φ ∘ γ) ((tangentSpaceCastModel I (γ t)).toContinuousLinearMap ∘L
      (1 : 𝕜 →L[𝕜] 𝕜).smulRight w ∘L (tangentSpaceCastModel 𝓘(𝕜, 𝕜) t).symm.toContinuousLinearMap)
      (insert t s) t := by
    refine (hg.of_comp_of_leftInverse hst h hcomp hL (mem_insert t s)).congr_fderiv ?_
    ext
    -- Both identifications of tangent spaces with model spaces are the identity on vectors.
    change L ((1 : 𝕜) • mvfderiv I e (γ t) w) = (1 : 𝕜) • w
    rw [one_smul, one_smul, hL w]
  refine ⟨hγ, ?_⟩
  simp only [writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_symm,
    PartialEquiv.refl_coe, comp_id, preimage_id, modelWithCornersSelf_coe, range_id,
    inter_univ, id_eq] at hderiv ⊢
  exact hderiv

/-- **Lifting a velocity through a map with injective differential.** Let `e : M → F` be a map
into a finite-dimensional normed space over a complete field, with injective differential at
`γ t`. If the curve `γ` is continuous at `t` and `e ∘ γ` has derivative `d e (γ t) w` at `t`,
then `γ` has velocity `w` at `t`. -/
theorem ContinuousAt.hasMFDerivAt_of_hasDerivAt_comp [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]
    (hγ : ContinuousAt γ t) (hinj : Injective (mvfderiv I e (γ t)))
    (h : HasDerivAt (e ∘ γ) (mvfderiv I e (γ t) w) t) :
    HasMFDerivAt 𝓘(𝕜, 𝕜) I γ t ((1 : 𝕜 →L[𝕜] 𝕜).smulRight w) := by
  refine hasMFDerivWithinAt_univ.1 ?_
  exact hγ.continuousWithinAt.hasMFDerivWithinAt_of_hasDerivWithinAt_comp
    (.of_injective_of_finiteDimensional hinj) h.hasDerivWithinAt
