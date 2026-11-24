/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.ContinuousInverse
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.MFDeriv.OfCompLeft

/-!
# Lifting the velocity of a curve through a map with injective differential

Let `e : M → F` be a map from a manifold into a normed space whose differential at `γ t` has a
continuous left inverse, and let `γ` be a curve in `M` which is continuous at `t` within a
parameter set `s`. If the image curve `e ∘ γ` is differentiable at `t` within `s` with derivative
`d e (γ t) w`, then `γ` itself is differentiable at `t` within `s`, with velocity `w`
(`ContinuousWithinAt.hasMFDerivWithinAt_of_hasDerivWithinAt_comp`). When `F` is
finite-dimensional over a complete field, an injective differential has a continuous left inverse
(`ContinuousAt.hasMFDerivAt_of_hasDerivAt_comp`).

The first result is the special case, for a curve and a map into a normed space, of
`HasMFDerivWithinAt.of_comp_of_leftInverse`, which lifts a manifold derivative through any map
whose differential has a continuous linear left inverse; that lemma reads both maps in the
extended charts and applies Mathlib's easy half of the inverse function theorem,
`HasFDerivWithinAt.of_comp_of_leftInverse`.

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

/-- **Lifting a velocity through a map whose differential has a continuous left inverse.** Let
`e : M → F` be a map into a normed space whose differential at `γ t` has a continuous left
inverse. If the curve `γ` is continuous at `t` within `s` and `e ∘ γ` has derivative
`d e (γ t) w` at `t` within `s`, then `γ` has velocity `w` at `t` within `s`. -/
theorem ContinuousWithinAt.hasMFDerivWithinAt_of_hasDerivWithinAt_comp
    (hγ : ContinuousWithinAt γ s t) (he : (mvfderiv I e (γ t)).HasLeftInverse)
    (h : HasDerivWithinAt (e ∘ γ) (mvfderiv I e (γ t) w) s t) :
    HasMFDerivWithinAt 𝓘(𝕜, 𝕜) I γ s t ((1 : 𝕜 →L[𝕜] 𝕜).smulRight w) := by
  obtain ⟨L, hL⟩ := he
  have hd : MDifferentiableAt I 𝓘(𝕜, F) e (γ t) :=
    mdifferentiableAt_of_mfderiv_injective (TauCeti.injective_mvfderiv_iff.1 hL.injective)
  -- `mvfderiv` is `mfderiv` followed by the identification of the tangent space of `F` with `F`,
  -- so `L` after that identification is a left inverse of `mfderiv`.
  refine (HasMFDerivWithinAt.of_comp_of_leftInverse
    (L := L ∘L (NormedSpace.fromTangentSpace (e (γ t))).toContinuousLinearMap) hd.hasMFDerivAt hγ
    h.hasFDerivWithinAt.hasMFDerivWithinAt hL).congr_mfderiv ?_
  -- Both sides are linear in the parameter, so they agree once they agree at `1`.
  ext
  -- The tangent space of `F` at `e (γ t)` and of `𝕜` at `t` are `F` and `𝕜` by definition, but
  -- `simp` lemmas for composition and `toSpanSingleton` do not fire across these identifications.
  -- `change` unfolds both composites at `1`, where `NormedSpace.fromTangentSpace` is the identity
  -- on vectors, so that the goal becomes the left inverse property `hL w`.
  change L (NormedSpace.fromTangentSpace (e (γ t)) ((1 : 𝕜) • mvfderiv I e (γ t) w)) = (1 : 𝕜) • w
  rw [one_smul, one_smul]
  exact hL w

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
