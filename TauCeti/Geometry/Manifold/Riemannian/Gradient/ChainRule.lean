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

variable (I) in
/-- The Riemannian gradient within a set, obtained by taking the fibrewise Riesz dual of the
manifold derivative within that set. Like the derivative, it is total. -/
def riemannianGradientWithin (f : M → ℝ) (s : Set M)
    (x : M) : TangentSpace I x :=
  rieszDual x (mvfderivWithin I f s x)

/-- The gradient within a set is the Riesz dual of the relative differential. -/
theorem riemannianGradientWithin_def (f : M → ℝ) (s : Set M) (x : M) :
    riemannianGradientWithin I f s x = rieszDual x (mvfderivWithin I f s x) := (rfl)

/-- Pairing the relative gradient with a tangent vector evaluates the relative differential. -/
@[simp]
theorem inner_riemannianGradientWithin_left (v : TangentSpace I x) :
    inner ℝ (riemannianGradientWithin I f s x) v = mvfderivWithin I f s x v := by
  rw [riemannianGradientWithin_def, inner_rieszDual]

/-- The symmetric form of the relative gradient's characteristic equation. -/
@[simp]
theorem inner_riemannianGradientWithin_right (v : TangentSpace I x) :
    inner ℝ v (riemannianGradientWithin I f s x) = mvfderivWithin I f s x v := by
  rw [real_inner_comm, inner_riemannianGradientWithin_left]

/-- On the whole manifold the relative gradient is the gradient. -/
@[simp]
theorem riemannianGradientWithin_univ (f : M → ℝ) :
    riemannianGradientWithin I f univ = riemannianGradient I f := by
  funext x
  apply ext_inner_right ℝ
  intro v
  simp only [inner_riemannianGradientWithin_left, inner_riemannianGradient_left,
    mvfderivWithin_univ]

/-- The relative gradient is uniquely characterized by its inner products. -/
theorem eq_riemannianGradientWithin_iff {w : TangentSpace I x} :
    w = riemannianGradientWithin I f s x ↔
      ∀ v, inner ℝ w v = mvfderivWithin I f s x v := by
  rw [riemannianGradientWithin_def]
  exact eq_rieszDual_iff_inner_eq

/-- The relative gradient vanishes exactly where the relative differential vanishes. -/
@[simp]
theorem riemannianGradientWithin_eq_zero_iff :
    riemannianGradientWithin I f s x = 0 ↔ mvfderivWithin I f s x = 0 := by
  rw [riemannianGradientWithin_def, LinearIsometryEquiv.map_eq_zero_iff]

/-- Restriction to a neighbourhood does not change the gradient. -/
theorem riemannianGradientWithin_of_mem_nhds (hs : s ∈ 𝓝 x) :
    riemannianGradientWithin I f s x = riemannianGradient I f x := by
  apply ext_inner_right ℝ
  intro v
  simp only [inner_riemannianGradientWithin_left, inner_riemannianGradient_left,
    mvfderivWithin, mvfderiv, mfderivWithin_of_mem_nhds hs]

section Composition

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' 1 N]
  [RiemannianBundle (fun y : N ↦ TangentSpace I' y)]
  {φ : M → N} {g : N → ℝ} {t : Set N}

/-- The relative gradient chain rule in inner-product form. -/
theorem inner_riemannianGradientWithin_comp (hg : MDifferentiableWithinAt I' 𝓘(ℝ) g t (φ x))
    (hφ : MDifferentiableWithinAt I I' φ s x) (hφt : MapsTo φ s t)
    (hs : UniqueMDiffWithinAt I s x) (v : TangentSpace I x) :
    inner ℝ (riemannianGradientWithin I (g ∘ φ) s x) v =
      inner ℝ (riemannianGradientWithin I' g t (φ x)) (mfderivWithin I I' φ s x v) := by
  simp only [inner_riemannianGradientWithin_left]
  rw [mvfderivWithin_comp x hg hφ hφt hs, ContinuousLinearMap.comp_apply]

/-- The relative gradient of a composite is the source Riesz dual of the pullback of the
metric dual of the target gradient. This is the metric-adjoint chain rule. -/
theorem riemannianGradientWithin_comp (hg : MDifferentiableWithinAt I' 𝓘(ℝ) g t (φ x))
    (hφ : MDifferentiableWithinAt I I' φ s x) (hφt : MapsTo φ s t)
    (hs : UniqueMDiffWithinAt I s x) :
    riemannianGradientWithin I (g ∘ φ) s x =
      rieszDual x ((innerSL ℝ (riemannianGradientWithin I' g t (φ x))).comp
        (mfderivWithin I I' φ s x)) := by
  apply eq_rieszDual_iff_inner_eq.mpr
  intro v
  simpa only [ContinuousLinearMap.comp_apply, innerSL_apply_apply] using
    inner_riemannianGradientWithin_comp hg hφ hφt hs v

/-- The gradient chain rule in inner-product form on the whole manifold. -/
theorem inner_riemannianGradient_comp (hg : MDifferentiableAt I' 𝓘(ℝ) g (φ x))
    (hφ : MDifferentiableAt I I' φ x) (v : TangentSpace I x) :
    inner ℝ (riemannianGradient I (g ∘ φ) x) v =
      inner ℝ (riemannianGradient I' g (φ x)) (mfderiv I I' φ x v) := by
  simpa only [riemannianGradientWithin_univ, mfderivWithin_univ] using
    inner_riemannianGradientWithin_comp hg.mdifferentiableWithinAt
      hφ.mdifferentiableWithinAt (mapsTo_univ φ univ) (uniqueMDiffWithinAt_univ I) v

/-- The metric-adjoint gradient chain rule on the whole manifold. -/
theorem riemannianGradient_comp (hg : MDifferentiableAt I' 𝓘(ℝ) g (φ x))
    (hφ : MDifferentiableAt I I' φ x) :
    riemannianGradient I (g ∘ φ) x =
      rieszDual x ((innerSL ℝ (riemannianGradient I' g (φ x))).comp (mfderiv I I' φ x)) := by
  simpa only [riemannianGradientWithin_univ, mfderivWithin_univ] using
    riemannianGradientWithin_comp hg.mdifferentiableWithinAt hφ.mdifferentiableWithinAt
      (mapsTo_univ φ univ) (uniqueMDiffWithinAt_univ I)

end Composition

/-- Scalar postcomposition multiplies the relative gradient by the scalar derivative.
The outer derivative may itself be taken within a subset of the real line. -/
theorem riemannianGradientWithin_comp_hasDerivWithinAt {g : ℝ → ℝ} {g' : ℝ} {t : Set ℝ}
    (hg : HasDerivWithinAt g g' t (f x)) (hf : MDifferentiableWithinAt I 𝓘(ℝ) f s x)
    (hst : MapsTo f s t) (hs : UniqueMDiffWithinAt I s x) :
    riemannianGradientWithin I (g ∘ f) s x = g' • riemannianGradientWithin I f s x := by
  apply ext_inner_right ℝ
  intro v
  have hcomp := (hg.hasFDerivWithinAt.hasMFDerivWithinAt.comp x
    hf.hasMFDerivWithinAt hst).mfderivWithin hs
  simp only [inner_riemannianGradientWithin_left, real_inner_smul_left]
  -- On a scalar target, `mvfderivWithin`'s tangent identification is the identity.
  have hcomp' := congrArg (fun L ↦ NormedSpace.fromTangentSpace (g (f x)) (L v)) hcomp
  convert! hcomp' using 1
  erw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply]
  erw [smul_eq_mul]
  rw [mul_comm]
  rfl

/-- Scalar postcomposition multiplies the relative gradient by the ordinary scalar derivative. -/
theorem riemannianGradientWithin_comp_hasDerivAt {g : ℝ → ℝ} {g' : ℝ}
    (hg : HasDerivAt g g' (f x)) (hf : MDifferentiableWithinAt I 𝓘(ℝ) f s x)
    (hs : UniqueMDiffWithinAt I s x) :
    riemannianGradientWithin I (g ∘ f) s x = g' • riemannianGradientWithin I f s x :=
  riemannianGradientWithin_comp_hasDerivWithinAt hg.hasDerivWithinAt hf
    (mapsTo_univ f s) hs

/-- Scalar postcomposition multiplies the gradient by the scalar derivative. -/
theorem riemannianGradient_comp_hasDerivAt {g : ℝ → ℝ} {g' : ℝ}
    (hg : HasDerivAt g g' (f x)) (hf : MDifferentiableAt I 𝓘(ℝ) f x) :
    riemannianGradient I (g ∘ f) x = g' • riemannianGradient I f x := by
  simpa only [riemannianGradientWithin_univ] using
    riemannianGradientWithin_comp_hasDerivAt hg hf.mdifferentiableWithinAt
      (uniqueMDiffWithinAt_univ I)

/-- The relative gradient chain rule for differentiable scalar postcomposition. -/
theorem riemannianGradientWithin_comp_deriv {g : ℝ → ℝ} (hg : DifferentiableAt ℝ g (f x))
    (hf : MDifferentiableWithinAt I 𝓘(ℝ) f s x) (hs : UniqueMDiffWithinAt I s x) :
    riemannianGradientWithin I (g ∘ f) s x = deriv g (f x) • riemannianGradientWithin I f s x :=
  riemannianGradientWithin_comp_hasDerivAt hg.hasDerivAt hf hs

/-- The gradient chain rule for differentiable scalar postcomposition. -/
theorem riemannianGradient_comp_deriv {g : ℝ → ℝ} (hg : DifferentiableAt ℝ g (f x))
    (hf : MDifferentiableAt I 𝓘(ℝ) f x) :
    riemannianGradient I (g ∘ f) x = deriv g (f x) • riemannianGradient I f x :=
  riemannianGradient_comp_hasDerivAt hg.hasDerivAt hf

end TauCeti.Manifold
