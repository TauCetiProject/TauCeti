/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Analysis.Normed.Module.ContinuousInverse
public import Mathlib.Geometry.Manifold.ContMDiff.Defs
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Lifting the velocity of a curve through a map with injective differential

Let `e : M → F` be a `C¹` map from a manifold without boundary into a finite-dimensional normed
space, with injective differential at `γ t`, and let `γ` be a curve in `M` which is continuous at
`t`. If the image curve `e ∘ γ` is differentiable at `t` with derivative `d e (γ t) w`, then `γ`
itself is differentiable at `t`, with velocity `w`
(`ContMDiffAt.hasMFDerivAt_of_hasDerivAt_comp`).

Read in the extended chart `φ` at `γ t`, the map `e` becomes a `C¹` map `g` with injective
derivative `D`. A continuous left inverse `L` of `D` turns `L ∘ g` into a map with invertible
derivative, so it has a local inverse `ψ` by the inverse function theorem, and
`φ ∘ γ = ψ ∘ L ∘ e ∘ γ` near `t` because `γ` is continuous there. Differentiating the right side
gives the velocity.

This is the converse of the chain rule along a curve,
`TauCeti.Manifold.hasDerivAt_comp_curve`. It is how a curve in a manifold is recognized as an
integral curve from its image in an ambient vector space, for instance after an embedding of a
compact manifold into Euclidean space: there the curve is obtained as a limit, and only its image
is known to be differentiable. Mathlib's `ContMDiffAt.iff_comp_isImmersionAt` lifts `C^n`
regularity of `e ∘ γ` on a neighbourhood through an immersion; here only differentiability of
`e ∘ γ` at the single parameter `t` and the regularity of `e` at the single point `γ t` are used.
Continuity of `γ` cannot be dropped, since without it `γ` could jump between points with the same
image near `e (γ t)`, which an injective differential only excludes locally.

## Main results

* `ContMDiffAt.hasMFDerivAt_of_hasDerivAt_comp`: the velocity of a continuous curve is
  determined by the derivative of its image under a map with injective differential.
-/

public section

noncomputable section

open Function Set Filter
open scoped Manifold Topology

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- **Lifting a velocity through a map with injective differential.** Let `e : M → F` be `C¹` at
`γ t`, with injective differential there, from a manifold without boundary into a
finite-dimensional normed space. If the curve `γ` is continuous at `t` and `e ∘ γ` has derivative
`d e (γ t) w` at `t`, then `γ` has velocity `w` at `t`. -/
theorem ContMDiffAt.hasMFDerivAt_of_hasDerivAt_comp {e : M → F} {γ : 𝕜 → M} {t : 𝕜}
    {w : TangentSpace I (γ t)} (he : ContMDiffAt I 𝓘(𝕜, F) 1 e (γ t))
    (hinj : Injective (mvfderiv I e (γ t))) (hγ : ContinuousAt γ t)
    (h : HasDerivAt (e ∘ γ) (mvfderiv I e (γ t) w) t) :
    HasMFDerivAt 𝓘(𝕜, 𝕜) I γ t ((1 : 𝕜 →L[𝕜] 𝕜).smulRight w) := by
  set φ := extChartAt I (γ t)
  -- The map `e` read in the chart at `γ t`.
  set g : E → F := writtenInExtChartAt I 𝓘(𝕜, F) (γ t) e
  have hg : ContDiffAt 𝕜 1 g (φ (γ t)) := by
    have h := (contMDiffAt_iff.1 he).2
    rwa [I.range_eq_univ, contDiffWithinAt_univ] at h
  have hD (v : E) : mvfderiv I e (γ t) v = fderiv 𝕜 g (φ (γ t)) v := by
    rw [(he.mdifferentiableAt one_ne_zero).mvfderiv, I.range_eq_univ, fderivWithin_univ]
    rfl
  have hinj' : Injective (fderiv 𝕜 g (φ (γ t))) := fun a b hab ↦ hinj (by rwa [hD, hD])
  replace h : HasDerivAt (e ∘ γ) (fderiv 𝕜 g (φ (γ t)) w) t := h.congr_deriv (hD w)
  obtain ⟨L, hL⟩ := ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional hinj'
  -- `L ∘ g` has the identity as its strict derivative, hence a local inverse.
  have hstrict : HasStrictFDerivAt (L ∘ g)
      ((ContinuousLinearEquiv.refl 𝕜 E : E ≃L[𝕜] E) : E →L[𝕜] E) (φ (γ t)) := by
    refine (L.hasStrictFDerivAt.comp (φ (γ t))
      (hg.hasStrictFDerivAt_fderiv one_ne_zero)).congr_fderiv ?_
    ext v
    simp [hL v]
  -- Near `t`, the chart reading of `γ` is the local inverse applied to `L ∘ e ∘ γ`.
  have hev : φ ∘ γ =ᶠ[𝓝 t] hstrict.localInverse ∘ L ∘ (e ∘ γ) := by
    have h₁ := ((continuousAt_extChartAt (γ t)).comp hγ).eventually hstrict.eventually_left_inverse
    have h₂ := hγ.eventually (extChartAt_source_mem_nhds (I := I) (γ t))
    filter_upwards [h₁, h₂] with s hs₁ hs₂
    have hgs : g (φ (γ s)) = e (γ s) := by
      -- The chart of the model space `F` is the identity, so `g = e ∘ φ.symm`.
      rw [show g (φ (γ s)) = e (φ.symm (φ (γ s))) from rfl, φ.left_inv hs₂]
    simp only [comp_apply] at hs₁ ⊢
    rw [← hgs]
    exact hs₁.symm
  have hderiv : HasDerivAt (φ ∘ γ) w t := by
    have hpt : L (g (φ (γ t))) = (L ∘ (e ∘ γ)) t := by
      simp [g, writtenInExtChartAt, φ]
    have h' := hstrict.to_localInverse.hasFDerivAt.comp_hasDerivAt_of_eq t
      (L.hasFDerivAt.comp_hasDerivAt t h) hpt
    have hw : L (fderiv 𝕜 g (φ (γ t)) w) = w := hL w
    have h'' := h'.congr_of_eventuallyEq hev
    rwa [ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.coe_refl,
      ContinuousLinearMap.id_apply, hw] at h''
  -- By definition, `HasMFDerivAt` reads `γ` in the extended charts, which are the identity on the
  -- model space `𝕜` and `φ` on `M`, and identifies tangent spaces with model spaces by the
  -- identity; so the remaining goals hold by definition.
  refine ⟨hγ, ?_⟩
  have h' := hderiv.hasFDerivAt.hasFDerivWithinAt (s := range 𝓘(𝕜, 𝕜))
  convert h' using 1
  · rfl
  · ext
    rfl
  · rfl

