/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.MappingTorus.Orientation
public import TauCeti.Geometry.Manifold.Orientation.Sphere
import Mathlib.Analysis.Complex.OperatorNorm
import TauCeti.Analysis.InnerProductSpace.Reflection
import TauCeti.Geometry.Sphere.Connected

/-!
# An oriented mapping torus of `S² × S¹` built from two reflections

Let `E` be a three-dimensional real inner product space with unit sphere `S²`, let `v ≠ 0` be a
vector of `E`, and let `S¹` be the unit circle of `ℂ`. The diffeomorphism

`τ (p, w) = (ρ p, conj w)`

of `S² × S¹` (`TauCeti.sphereCircleReflection v`) reflects the sphere across the plane `v^⊥`
(`ρ = (ℝ ∙ v)ᗮ.reflection`) and conjugates the circle. For `E = ℝ³` and `v` the second
coordinate vector this is `((x, y, z), e^{iθ}) ↦ ((x, -y, z), e^{-iθ})`. It is an involution.

Each factor of `τ` reverses the orientation of its sphere: both are restrictions of linear
isometries of determinant `-1` (`Orientation.isOrientationReversingAt_unitSphereEquiv`). So `τ`
preserves the product orientation of `S² × S¹`
(`TauCeti.isOrientationPreservingAt_sphereCircleReflection`), and its smooth mapping torus

`X = (ℝ × S² × S¹) / ((t, q) ∼ (t + 1, τ q))`

carries the orientation `dt` followed by the product orientation
(`TauCeti.sphereCircleReflection.torusOrientation`). It is compact, since `S² × S¹` is, so `X` is an
oriented closed four-manifold. Reflecting only the sphere factor would not do: the mapping torus of
`ρ × id` is not orientable (`TauCeti.not_orientable_smoothMappingTorus_prodCongr_refl`).

This is the ambient manifold of a classical example in Morse–Bott theory, not developed in this
file: for a unit vector `u` orthogonal to `v` (for `E = ℝ³` and `v` the second coordinate vector,
the third one, giving the height `z`), the height `⟪u, p⟫` and the real part of `w` are invariant
under `τ`, so for `0 < ε < 1` the function `[t, p, w] ↦ ⟪u, p⟫ + ε Re w` is defined on `X`, with
four critical circles, and the space of its gradient trajectories between two of them is a Klein
bottle. So a Morse–Bott function on an
oriented manifold can have nonorientable trajectory spaces between oriented critical submanifolds.

## Main definitions

* `TauCeti.sphereCircleReflection v`: the diffeomorphism `(p, w) ↦ (ρ p, conj w)` of `S² × S¹`.
* `TauCeti.sphereCircleReflection.torusOrientation`: the orientation of its mapping torus.

## Main results

* `TauCeti.isOrientationPreservingAt_sphereCircleReflection`: `τ` preserves the product
  orientation of `S² × S¹`.
* `TauCeti.orientable_smoothMappingTorus_sphereCircleReflection`: its mapping torus is
  orientable; it is compact by `TauCeti.SmoothMappingTorus.instCompactSpace`.
* `TauCeti.not_orientable_smoothMappingTorus_prodCongr_refl`: the mapping torus of the reflection
  of the sphere factor alone is not orientable.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, Section 6.2 (orientations of Morse–Bott trajectory spaces).
* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 15 (orientations of products and of quotients).
-/

public section

noncomputable section

open Metric Module Submodule
open scoped Manifold ContDiff

namespace TauCeti

attribute [local instance] finrank_real_complex_fact'

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fact (finrank ℝ E = 2 + 1)]

/-- A space of dimension `2 + 1` is finite-dimensional, so its unit sphere is compact. -/
local instance finiteDimensional_sphereCircleAmbient : FiniteDimensional ℝ E :=
  .of_fact_finrank_eq_succ 2

variable (v : E)

/-- The diffeomorphism `τ (p, w) = (ρ p, conj w)` of `S² × S¹`, where `ρ` is the reflection of `E`
across the plane `v^⊥` and `S¹` is the unit circle of `ℂ`. -/
def sphereCircleReflection :
    (sphere (0 : E) 1 × sphere (0 : ℂ) 1) ≃ₘ⟮(𝓡 2).prod (𝓡 1), (𝓡 2).prod (𝓡 1)⟯
      (sphere (0 : E) 1 × sphere (0 : ℂ) 1) :=
  ((ℝ ∙ v)ᗮ.reflection.unitSphereDiffeomorph ∞).prodCongr
    (Complex.conjLIE.unitSphereDiffeomorph ∞)

/-- `τ` is the product of the restrictions to the unit spheres of the reflection across `v^⊥` and
of complex conjugation. -/
theorem coe_sphereCircleReflection :
    ⇑(sphereCircleReflection v) =
      Prod.map (ℝ ∙ v)ᗮ.reflection.unitSphereEquiv Complex.conjLIE.unitSphereEquiv := by
  rw [sphereCircleReflection, Diffeomorph.coe_prodCongr,
    LinearIsometryEquiv.coe_unitSphereDiffeomorph, LinearIsometryEquiv.coe_unitSphereDiffeomorph]

/-- The sphere coordinate of `τ (p, w)` is the reflection `ρ p` of `p` across `v^⊥`. -/
@[simp]
theorem coe_sphereCircleReflection_apply_fst (x : sphere (0 : E) 1 × sphere (0 : ℂ) 1) :
    ((sphereCircleReflection v x).1 : E) = (ℝ ∙ v)ᗮ.reflection (x.1 : E) :=
  LinearIsometryEquiv.coe_unitSphereDiffeomorph_apply _ _

/-- The circle coordinate of `τ (p, w)` is the conjugate of `w`. -/
@[simp]
theorem coe_sphereCircleReflection_apply_snd (x : sphere (0 : E) 1 × sphere (0 : ℂ) 1) :
    ((sphereCircleReflection v x).2 : ℂ) = (starRingEnd ℂ) (x.2 : ℂ) :=
  LinearIsometryEquiv.coe_unitSphereDiffeomorph_apply _ _

/-- `τ` is an involution. -/
@[simp]
theorem sphereCircleReflection_sphereCircleReflection
    (x : sphere (0 : E) 1 × sphere (0 : ℂ) 1) :
    sphereCircleReflection v (sphereCircleReflection v x) = x := by
  ext <;> simp

variable {v}

/-- **`τ` preserves the orientation of `S² × S¹`.** Both of its factors reverse orientation, so it
preserves the product of the outward-normal orientations, for every orientation `o` of `E`. -/
theorem isOrientationPreservingAt_sphereCircleReflection (hv : v ≠ 0)
    (o : Orientation ℝ E (Fin (2 + 1))) (x : sphere (0 : E) 1 × sphere (0 : ℂ) 1) :
    Manifold.Orientation.IsOrientationPreservingAt
      (o.sphereOrientation.prod Complex.orientation.sphereOrientation)
      (o.sphereOrientation.prod Complex.orientation.sphereOrientation)
      (sphereCircleReflection v) x := by
  have hρ := o.isOrientationReversingAt_unitSphereEquiv
    (by rw [← LinearEquiv.coe_det, linearEquiv_det_reflection_orthogonal_singleton hv]
        exact neg_one_lt_zero) x.1
  have hκ := Complex.orientation.isOrientationReversingAt_unitSphereEquiv
    (e := Complex.conjLIE) (by rw [Complex.det_conjLIE]; exact neg_one_lt_zero) x.2
  rw [coe_sphereCircleReflection]
  exact hρ.prodMap hκ

namespace sphereCircleReflection

variable (hv : v ≠ 0) (o : Orientation ℝ E (Fin (2 + 1)))

/-- The orientation of the four-dimensional mapping torus of `τ`: the time direction `dt` followed
by the product orientation of `S² × S¹` induced by an orientation `o` of `E` and the standard
orientation of `ℂ`. The quotient map `(t, q) ↦ [t, q]` preserves orientation from the product
orientation of `ℝ × S² × S¹` (`TauCeti.SmoothMappingTorus.isOrientationPreservingAt_uncurry_mk`). -/
def torusOrientation :
    Manifold.Orientation (𝓘(ℝ).prod ((𝓡 2).prod (𝓡 1)))
      (SmoothMappingTorus (sphereCircleReflection v)) (Fin (1 + (2 + 1))) :=
  SmoothMappingTorus.orientation _ _ (isOrientationPreservingAt_sphereCircleReflection hv o)

/-- The orientation of the mapping torus of `τ` is the mapping-torus orientation
`TauCeti.SmoothMappingTorus.orientation` induced by the `τ`-invariant product orientation, so its
lemmas, such as `TauCeti.SmoothMappingTorus.isOrientationPreservingAt_uncurry_mk`, apply to it. -/
theorem torusOrientation_def :
    torusOrientation hv o =
      SmoothMappingTorus.orientation _ _ (isOrientationPreservingAt_sphereCircleReflection hv o) :=
  (rfl)

end sphereCircleReflection

/-- **The mapping torus of `τ` is orientable.** It is also compact
(`TauCeti.SmoothMappingTorus.instCompactSpace`), so it is an oriented closed four-manifold. -/
theorem orientable_smoothMappingTorus_sphereCircleReflection (hv : v ≠ 0) :
    Orientable (𝓘(ℝ).prod ((𝓡 2).prod (𝓡 1)))
      (SmoothMappingTorus (sphereCircleReflection v)) := by
  let b := finBasisOfFinrankEq ℝ E (Fact.out : finrank ℝ E = 2 + 1)
  exact ⟨⟨(sphereCircleReflection.torusOrientation hv b.orientation).reindex
    (finCongr (by simp))⟩⟩

/-- **Reflecting only the sphere factor gives a nonorientable mapping torus.** The diffeomorphism
`(p, w) ↦ (ρ p, w)` of `S² × S¹` reverses its orientation, and `S² × S¹` is connected. -/
theorem not_orientable_smoothMappingTorus_prodCongr_refl (hv : v ≠ 0) :
    ¬ Orientable (𝓘(ℝ).prod ((𝓡 2).prod (𝓡 1)))
      (SmoothMappingTorus (((ℝ ∙ v)ᗮ.reflection.unitSphereDiffeomorph (n := 2) (k := 2) ∞).prodCongr
        (Diffeomorph.refl (𝓡 1) (sphere (0 : ℂ) 1) ∞))) := by
  have := connectedSpace_sphere (E := E) 2
  have := connectedSpace_sphere (E := ℂ) 1
  let o := (finBasisOfFinrankEq ℝ E (Fact.out : finrank ℝ E = 2 + 1)).orientation
  let w : sphere (0 : ℂ) 1 := ⟨1, by simp⟩
  have hρ := o.isOrientationReversingAt_unitSphereEquiv
    (by rw [← LinearEquiv.coe_det, linearEquiv_det_reflection_orthogonal_singleton hv]
        exact neg_one_lt_zero) (Classical.arbitrary _)
  refine SmoothMappingTorus.not_orientable_of_isOrientationReversingAt _
    (o.sphereOrientation.prod Complex.orientation.sphereOrientation)
    (x := (Classical.arbitrary _, w)) ?_
  rw [← Manifold.Orientation.isOrientationPreservingAt_neg_right,
    ← Manifold.Orientation.prod_neg_left, Diffeomorph.coe_prodCongr,
    LinearIsometryEquiv.coe_unitSphereDiffeomorph, Diffeomorph.coe_refl]
  exact ((Manifold.Orientation.isOrientationPreservingAt_neg_right _ _ _ _).2 hρ).prodMap
    (Manifold.Orientation.isOrientationPreservingAt_id _ w)

end TauCeti
