/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import TauCeti.Geometry.Euclidean.Circle
public import TauCeti.Probability.Distributions.Uniform.Sphere.Basic

import Mathlib.Analysis.Complex.Isometry
public import Mathlib.MeasureTheory.Group.Circle

/-!
# Uniform angles and uniform planar directions

The cosine-sine parametrization `circleSphereHomeomorph` identifies the additive circle
with the unit sphere in the Euclidean plane. It carries normalized Haar measure to
`uniformSphereMeasure`, so a uniform angle gives exactly a uniform planar direction.
The intermediate complex-circle identity follows from uniqueness of Haar probability
and the rotation invariance of the uniform sphere law.

The construction uses Mathlib's `AddCircle.homeomorphCircle'`, the real orthonormal basis
`Complex.orthonormalBasisOneI`, and `LinearIsometryEquiv.map_uniformSphereMeasure`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Metric Set Real AddCircle
open scoped InnerProductSpace

namespace TauCeti.Probability

local instance factTwoPiPosUniformCircle : Fact (0 < 2 * π) := ⟨two_pi_pos⟩

/-- On the complex unit circle, the uniform sphere law is multiplicative Haar measure. -/
instance isHaarMeasure_uniformSphereMeasure_complex :
    Measure.IsHaarMeasure (uniformSphereMeasure ℂ) := by
  have : Measure.IsMulLeftInvariant (uniformSphereMeasure ℂ) := ⟨fun z ↦ by
    have h := (rotation z).map_uniformSphereMeasure
    convert h using 1
    exact congrArg (fun f : sphere (0 : ℂ) 1 → sphere (0 : ℂ) 1 ↦
      (uniformSphereMeasure ℂ).map f) (funext fun x ↦ Subtype.ext (rotation_apply z x).symm)⟩
  exact Measure.isHaarMeasure_of_isCompact_nonempty_interior _ univ isCompact_univ
    (by simp) (by simp) (by simp)

/-- Exponentiating a uniform angle gives the normalized surface law on the complex circle. -/
theorem map_homeomorphCircle'_haarAddCircle :
    haarAddCircle.map (AddCircle.homeomorphCircle' : AddCircle (2 * π) → sphere (0 : ℂ) 1) =
      uniformSphereMeasure ℂ := by
  let h : AddCircle (2 * π) ≃ₜ sphere (0 : ℂ) 1 := AddCircle.homeomorphCircle'
  let ν := (uniformSphereMeasure ℂ).map h.symm
  have hadd (a b : AddCircle (2 * π)) : h (a + b) = h a * h b :=
    Real.Angle.toCircle_add a b
  have : IsProbabilityMeasure ν := inferInstance
  have : Measure.IsAddLeftInvariant ν := ⟨fun a ↦ by
    have heq : (a + ·) ∘ h.symm = h.symm ∘ (h a * ·) := by
      funext z
      apply h.injective
      simp only [Function.comp_apply, hadd, h.apply_symm_apply]
    dsimp only [ν]
    rw [Measure.map_map (measurable_const_add a) h.symm.measurable, heq,
      ← Measure.map_map h.symm.measurable (measurable_const_mul (h a)), map_mul_left_eq_self]⟩
  have : Measure.IsAddHaarMeasure ν :=
    Measure.isAddHaarMeasure_of_isCompact_nonempty_interior _ univ isCompact_univ
      (by simp) (by simp) (by simp)
  have hν : ν = haarAddCircle := Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure _ _
  rw [← hν]
  exact MeasurableEquiv.map_map_symm h.toMeasurableEquiv

/-- The cosine-sine map carries Haar probability to the uniform planar sphere law. -/
theorem map_circleSphereHomeomorph_haarAddCircle :
    haarAddCircle.map circleSphereHomeomorph = uniformSphereMeasure (EuclideanSpace ℝ (Fin 2)) := by
  let h : AddCircle (2 * π) ≃ₜ sphere (0 : ℂ) 1 := AddCircle.homeomorphCircle'
  let g : sphere (0 : ℂ) 1 ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
    EuclideanSpace.sphereHomeomorphCircle.symm
  have hfun : (circleSphereHomeomorph : AddCircle (2 * π) →
      sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) = g ∘ h := by
    funext t
    apply Subtype.ext
    exact (coe_circleSphereHomeomorph t).trans
      (EuclideanSpace.coe_sphereHomeomorphCircle_symm_apply (h t)).symm
  rw [hfun, ← Measure.map_map g.measurable h.measurable]
  have hh : haarAddCircle.map h = uniformSphereMeasure ℂ := map_homeomorphCircle'_haarAddCircle
  rw [hh]
  convert Complex.orthonormalBasisOneI.repr.map_uniformSphereMeasure using 1
  congr 1
  funext x
  exact Subtype.ext (EuclideanSpace.coe_sphereHomeomorphCircle_symm_apply x)

end TauCeti.Probability

namespace ProbabilityTheory

open TauCeti TauCeti.Probability

local instance factTwoPiPosUniformCircle : Fact (0 < 2 * π) := ⟨two_pi_pos⟩

/-- A uniform random angle gives a uniform planar unit vector under cosine and sine. -/
theorem HasLaw.circleSphereHomeomorph_haarAddCircle {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → AddCircle (2 * π)} (hX : HasLaw X haarAddCircle P) :
    HasLaw (fun ω ↦ circleSphereHomeomorph (X ω))
      (uniformSphereMeasure (EuclideanSpace ℝ (Fin 2))) P := by
  rw [← map_circleSphereHomeomorph_haarAddCircle]
  exact (hasLaw_map circleSphereHomeomorph.measurable.aemeasurable).comp hX

end ProbabilityTheory
