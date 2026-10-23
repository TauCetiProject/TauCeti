/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.Comparison.Boundary.Components

/-!
# Manifold Stokes as closed-loop Green

Oriented parametrization computes the canonical integral of a one-dimensional manifold.
For a smooth boundary, this identifies outward-first Stokes with the existing closed-path
curve integral and, under an oriented embedding, with planar image area.
-/

public section

noncomputable section

open Set MeasureTheory
open scoped Manifold Topology ContDiff

namespace TauCeti.Green

local notation "E" => EuclideanSpace ℝ (Fin 1)

variable {N : Type*} [TopologicalSpace N] [ChartedSpace E N] [IsManifold 𝓘(ℝ, E) 1 N]

/-- A positively oriented closed path covering an actual compact one-dimensional manifold
once gives its canonical planar circulation integral. The path may have a seam at its base
point; all derivatives and orientation conditions concern the open parameter interval. -/
theorem integralTopForm_mpullback_eq_curveIntegral [CompactSpace N]
    (o : Manifold.Orientation 𝓘(ℝ, E) N (Fin 1)) {p : N} (q : Path p p)
    (f : N → ℂ) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) 1 f)
    (P Q : ℂ → ℝ) (U : Set ℂ) (hU : IsOpen U) (hrange : range f ⊆ U)
    (hP : ContinuousOn P U) (hQ : ContinuousOn Q U)
    (hqimage : q.extend '' Ioo (0 : ℝ) 1 = {p}ᶜ)
    (hqinj : InjOn q.extend (Ioo (0 : ℝ) 1))
    (e : ∀ z : E, E ≃L[ℝ] TangentSpace 𝓘(ℝ, E) (q.extend (z 0)))
    (hqd : ∀ z : E, z 0 ∈ Ioo (0 : ℝ) 1 →
      HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, E) (fun z : E ↦ q.extend (z 0)) z
        ((e z).toContinuousLinearMap.comp (NormedSpace.fromTangentSpace z).toContinuousLinearMap))
    (hqo : ∀ z : E, z 0 ∈ Ioo (0 : ℝ) 1 →
      Orientation.map (Fin 1) (e z).toLinearEquiv
        (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis.orientation =
          o.orientationAt (q.extend (z 0))) :
    IntegrableTopForm (mpullback 𝓘(ℝ, E) 𝓘(ℝ, ℂ) f (manifoldOneForm P Q)) ∧
      CurveIntegrable (oneForm P Q) (q.map hf.continuous) ∧
      integralTopForm o
        (mpullback 𝓘(ℝ, E) 𝓘(ℝ, ℂ) f (manifoldOneForm P Q)) =
          curveIntegral (oneForm P Q) (q.map hf.continuous) := by
  have h := integralTopForm_mpullback_eq_sum_curveIntegral o
    (fun _ : Unit ↦ p) (fun _ ↦ p) (fun _ ↦ q) f hf P Q U hU hrange hP hQ
    {p} (finite_singleton p) (by simpa only [iUnion_const] using hqimage)
    (fun i j hij ↦ False.elim (hij (Subsingleton.elim i j)))
    (fun _ ↦ hqinj) (fun _ ↦ e) (fun _ ↦ hqd) (fun _ ↦ hqo)
  simpa using h

section SmoothBoundary

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (1 + 1)) M]
  [IsManifold (𝓡∂ (1 + 1)) ∞ M] [T2Space M] [CompactSpace M]

local instance boundaryLoopIsManifold : IsManifold 𝓘(ℝ, E) ∞ ((𝓡∂ (1 + 1)).boundary M) :=
  isManifold_boundary M (by simp)

local instance boundaryLoopCompactSpace : CompactSpace ((𝓡∂ (1 + 1)).boundary M) :=
  isCompact_iff_compactSpace.mp
    ((𝓡∂ (1 + 1)).isClosed_boundary (M := M)
      (by simp : (∞ : WithTop ℕ∞) ≠ 0)).isCompact

/-- Global Stokes on an actual smooth boundary agrees with the existing closed-path curve
integral. The area form is the actual pullback of planar area, weighted by curl. -/
theorem integralTopForm_curl_area_eq_boundary_curveIntegral
    (o : Manifold.Orientation (𝓡∂ (1 + 1)) M (Fin (1 + 1)))
    (f : M → ℂ) (hf : ContMDiff (𝓡∂ (1 + 1)) 𝓘(ℝ, ℂ) 2 f)
    (P Q : ℂ → ℝ) (U : Set ℂ) (hU : IsOpen U) (hrange : range f ⊆ U)
    (hP : ContDiffOn ℝ 1 P U) (hQ : ContDiffOn ℝ 1 Q U)
    {p : (𝓡∂ (1 + 1)).boundary M} (q : Path p p)
    (hqimage : q.extend '' Ioo (0 : ℝ) 1 = {p}ᶜ)
    (hqinj : InjOn q.extend (Ioo (0 : ℝ) 1))
    (e : ∀ z : E, E ≃L[ℝ] TangentSpace 𝓘(ℝ, E) (q.extend (z 0)))
    (hqd : ∀ z : E, z 0 ∈ Ioo (0 : ℝ) 1 →
      HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, E) (fun z : E ↦ q.extend (z 0)) z
        ((e z).toContinuousLinearMap.comp (NormedSpace.fromTangentSpace z).toContinuousLinearMap))
    (hqo : ∀ z : E, z 0 ∈ Ioo (0 : ℝ) 1 →
      Orientation.map (Fin 1) (e z).toLinearEquiv
        (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis.orientation =
          (boundaryOrientation o).orientationAt (q.extend (z 0))) :
    let g := fun x : (𝓡∂ (1 + 1)).boundary M ↦ f x
    let hg : Continuous g := hf.continuous.comp continuous_subtype_val
    IntegrableTopForm (fun x ↦ curl P Q (f x) •
      mpullback (𝓡∂ (1 + 1)) 𝓘(ℝ, ℂ) f manifoldAreaForm x) ∧
      CurveIntegrable (oneForm P Q) (q.map hg) ∧
      integralTopForm o (fun x ↦ curl P Q (f x) •
        mpullback (𝓡∂ (1 + 1)) 𝓘(ℝ, ℂ) f manifoldAreaForm x) =
          curveIntegral (oneForm P Q) (q.map hg) := by
  have h := integralTopForm_curl_area_eq_boundary_sum_curveIntegral o f hf P Q U hU hrange hP hQ
    (fun _ : Unit ↦ p) (fun _ ↦ p) (fun _ ↦ q)
    {p} (finite_singleton p) (by simpa only [iUnion_const] using hqimage)
    (fun i j hij ↦ False.elim (hij (Subsingleton.elim i j)))
    (fun _ ↦ hqinj) (fun _ ↦ e) (fun _ ↦ hqd) (fun _ ↦ hqo)
  simpa using h

/-- The genuine smooth-boundary comparison with coordinate area: for an injective positively
oriented planar immersion, Stokes is Green over its actual image and the actual closed boundary
path. Both planar area and boundary curve integrabilities are conclusions. -/
theorem integral_image_curl_eq_boundary_curveIntegral
    (o : Manifold.Orientation (𝓡∂ (1 + 1)) M (Fin (1 + 1)))
    (f : M → ℂ) (hf : ContMDiff (𝓡∂ (1 + 1)) 𝓘(ℝ, ℂ) 2 f)
    (hinj : Function.Injective f)
    (F : M → EuclideanSpace ℝ (Fin (1 + 1)) ≃L[ℝ] ℂ)
    (hF : ∀ x, (F x).toContinuousLinearMap =
      (NormedSpace.fromTangentSpace (f x)).toContinuousLinearMap.comp
        (mfderiv (𝓡∂ (1 + 1)) 𝓘(ℝ, ℂ) f x))
    (hFo : ∀ x, Orientation.map (Fin (1 + 1)) (F x).toLinearEquiv
      -- Fix the shared Euclidean tangent model before transporting its pointwise orientation.
      (show Orientation ℝ (EuclideanSpace ℝ (Fin (1 + 1))) (Fin (1 + 1)) from
        o.orientationAt x) = Complex.orientation)
    (P Q : ℂ → ℝ) (U : Set ℂ) (hU : IsOpen U) (hrange : range f ⊆ U)
    (hP : ContDiffOn ℝ 1 P U) (hQ : ContDiffOn ℝ 1 Q U)
    {p : (𝓡∂ (1 + 1)).boundary M} (q : Path p p)
    (hqimage : q.extend '' Ioo (0 : ℝ) 1 = {p}ᶜ)
    (hqinj : InjOn q.extend (Ioo (0 : ℝ) 1))
    (e : ∀ z : E, E ≃L[ℝ] TangentSpace 𝓘(ℝ, E) (q.extend (z 0)))
    (hqd : ∀ z : E, z 0 ∈ Ioo (0 : ℝ) 1 →
      HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, E) (fun z : E ↦ q.extend (z 0)) z
        ((e z).toContinuousLinearMap.comp (NormedSpace.fromTangentSpace z).toContinuousLinearMap))
    (hqo : ∀ z : E, z 0 ∈ Ioo (0 : ℝ) 1 →
      Orientation.map (Fin 1) (e z).toLinearEquiv
        (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis.orientation =
          (boundaryOrientation o).orientationAt (q.extend (z 0))) :
    let g := fun x : (𝓡∂ (1 + 1)).boundary M ↦ f x
    let hg : Continuous g := hf.continuous.comp continuous_subtype_val
    IntegrableOn (curl P Q) (range f) ∧
      CurveIntegrable (oneForm P Q) (q.map hg) ∧
      (∫ z in range f, curl P Q z) =
          curveIntegral (oneForm P Q) (q.map hg) := by
  have h := integral_image_curl_eq_boundary_sum_curveIntegral
    o f hf hinj F hF hFo P Q U hU hrange hP hQ
    (fun _ : Unit ↦ p) (fun _ ↦ p) (fun _ ↦ q)
    {p} (finite_singleton p) (by simpa only [iUnion_const] using hqimage)
    (fun i j hij ↦ False.elim (hij (Subsingleton.elim i j)))
    (fun _ ↦ hqinj) (fun _ ↦ e) (fun _ ↦ hqd) (fun _ ↦ hqo)
  simpa using h

end SmoothBoundary

end TauCeti.Green
