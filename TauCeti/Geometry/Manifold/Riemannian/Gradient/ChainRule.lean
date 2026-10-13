/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Gradient.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Chain rules for Riemannian gradients

The gradient within a subset is the fibrewise Riesz dual of `mvfderivWithin`. This gives a
relative gradient calculus on manifolds with boundary or corners, with unique differentiability
required by the chain rules rather than by the definition.

For a map between Riemannian manifolds, the gradient of a composite is obtained by pulling the
metric dual of the target gradient back along the differential, then taking the Riesz dual in
the source. Thus the metric adjoint of the differential transports the target gradient to the
source gradient. Scalar postcomposition gives `grad (g ∘ f) = g'(f) • grad f`.

The construction uses `Riemannian.Tensor.rieszDual`; the chain rules use Mathlib's
`mvfderivWithin_comp` and its unrestricted specialization. No regularity of the metric beyond its
pointwise Riemannian bundle structure is needed.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 13.
-/

public section

noncomputable section

open Bundle Set Filter Topology
open scoped Manifold

namespace TauCeti.Manifold

open Riemannian.Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {f : M → ℝ} {s : Set M} {x : M}

section Composition

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' 1 N]
  [RiemannianBundle (fun y : N ↦ TangentSpace I' y)]
  {φ : M → N} {g : N → ℝ} {t : Set N}

/-- The relative gradient chain rule in inner-product form. -/
theorem inner_mgradientWithin_comp (hg : MDifferentiableWithinAt I' 𝓘(ℝ) g t (φ x))
    (hφ : MDifferentiableWithinAt I I' φ s x) (hφt : MapsTo φ s t)
    (hs : UniqueMDiffWithinAt I s x) (v : TangentSpace I x) :
    inner ℝ (mgradientWithin I (g ∘ φ) s x) v =
      inner ℝ (mgradientWithin I' g t (φ x)) (mfderivWithin I I' φ s x v) := by
  simp only [inner_mgradientWithin_left]
  rw [mvfderivWithin_comp x hg hφ hφt hs, ContinuousLinearMap.comp_apply]

/-- The relative gradient of a composite is the source Riesz dual of the pullback of the
metric dual of the target gradient. This is the metric-adjoint chain rule. -/
theorem mgradientWithin_comp (hg : MDifferentiableWithinAt I' 𝓘(ℝ) g t (φ x))
    (hφ : MDifferentiableWithinAt I I' φ s x) (hφt : MapsTo φ s t)
    (hs : UniqueMDiffWithinAt I s x) :
    mgradientWithin I (g ∘ φ) s x =
      rieszDual x ((innerSL ℝ (mgradientWithin I' g t (φ x))).comp
        (mfderivWithin I I' φ s x)) := by
  apply eq_rieszDual_iff_inner_eq.mpr
  intro v
  simpa only [ContinuousLinearMap.comp_apply, innerSL_apply_apply] using
    inner_mgradientWithin_comp hg hφ hφt hs v

/-- The gradient chain rule in inner-product form on the whole manifold. -/
theorem inner_mgradient_comp (hg : MDifferentiableAt I' 𝓘(ℝ) g (φ x))
    (hφ : MDifferentiableAt I I' φ x) (v : TangentSpace I x) :
    inner ℝ (mgradient I (g ∘ φ) x) v =
      inner ℝ (mgradient I' g (φ x)) (mfderiv I I' φ x v) := by
  simpa only [mgradientWithin_univ, mfderivWithin_univ] using
    inner_mgradientWithin_comp hg.mdifferentiableWithinAt
      hφ.mdifferentiableWithinAt (mapsTo_univ φ univ) (uniqueMDiffWithinAt_univ I) v

/-- The metric-adjoint gradient chain rule on the whole manifold. -/
theorem mgradient_comp (hg : MDifferentiableAt I' 𝓘(ℝ) g (φ x))
    (hφ : MDifferentiableAt I I' φ x) :
    mgradient I (g ∘ φ) x =
      rieszDual x ((innerSL ℝ (mgradient I' g (φ x))).comp (mfderiv I I' φ x)) := by
  simpa only [mgradientWithin_univ, mfderivWithin_univ] using
    mgradientWithin_comp hg.mdifferentiableWithinAt hφ.mdifferentiableWithinAt
      (mapsTo_univ φ univ) (uniqueMDiffWithinAt_univ I)

end Composition

/-- Scalar postcomposition multiplies the relative gradient by the scalar derivative.
The outer derivative may itself be taken within a subset of the real line. -/
theorem mgradientWithin_comp_hasDerivWithinAt {g : ℝ → ℝ} {g' : ℝ} {t : Set ℝ}
    (hg : HasDerivWithinAt g g' t (f x)) (hf : MDifferentiableWithinAt I 𝓘(ℝ) f s x)
    (hst : MapsTo f s t) (hs : UniqueMDiffWithinAt I s x) :
    mgradientWithin I (g ∘ f) s x = g' • mgradientWithin I f s x := by
  apply ext_inner_right ℝ
  intro v
  have hcomp := (hg.hasFDerivWithinAt.hasMFDerivWithinAt.comp x
    hf.hasMFDerivWithinAt hst).mfderivWithin hs
  simp only [inner_mgradientWithin_left, real_inner_smul_left]
  -- On a scalar target, `mvfderivWithin`'s tangent identification is the identity.
  have hcomp' := congrArg (fun L ↦ NormedSpace.fromTangentSpace (g (f x)) (L v)) hcomp
  convert! hcomp' using 1
  erw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply]
  erw [smul_eq_mul]
  rw [mul_comm]
  rfl

/-- Scalar postcomposition multiplies the relative gradient by the ordinary scalar derivative. -/
theorem mgradientWithin_comp_hasDerivAt {g : ℝ → ℝ} {g' : ℝ}
    (hg : HasDerivAt g g' (f x)) (hf : MDifferentiableWithinAt I 𝓘(ℝ) f s x)
    (hs : UniqueMDiffWithinAt I s x) :
    mgradientWithin I (g ∘ f) s x = g' • mgradientWithin I f s x :=
  mgradientWithin_comp_hasDerivWithinAt hg.hasDerivWithinAt hf
    (mapsTo_univ f s) hs

/-- Scalar postcomposition multiplies the gradient by the scalar derivative. -/
theorem mgradient_comp_hasDerivAt {g : ℝ → ℝ} {g' : ℝ}
    (hg : HasDerivAt g g' (f x)) (hf : MDifferentiableAt I 𝓘(ℝ) f x) :
    mgradient I (g ∘ f) x = g' • mgradient I f x := by
  simpa only [mgradientWithin_univ] using
    mgradientWithin_comp_hasDerivAt hg hf.mdifferentiableWithinAt
      (uniqueMDiffWithinAt_univ I)

/-- The relative gradient chain rule for differentiable scalar postcomposition. -/
theorem mgradientWithin_comp_deriv {g : ℝ → ℝ} (hg : DifferentiableAt ℝ g (f x))
    (hf : MDifferentiableWithinAt I 𝓘(ℝ) f s x) (hs : UniqueMDiffWithinAt I s x) :
    mgradientWithin I (g ∘ f) s x = deriv g (f x) • mgradientWithin I f s x :=
  mgradientWithin_comp_hasDerivAt hg.hasDerivAt hf hs

/-- The gradient chain rule for differentiable scalar postcomposition. -/
theorem mgradient_comp_deriv {g : ℝ → ℝ} (hg : DifferentiableAt ℝ g (f x))
    (hf : MDifferentiableAt I 𝓘(ℝ) f x) :
    mgradient I (g ∘ f) x = deriv g (f x) • mgradient I f x :=
  mgradient_comp_hasDerivAt hg.hasDerivAt hf

end TauCeti.Manifold
