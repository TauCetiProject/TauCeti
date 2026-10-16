/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Analytic.Cone.FaceLocalization
public import TauCeti.Geometry.Toric.Analytic.Cone.Orbit.Basic

/-!
# Orbit strata under face localization

If `τ` is a face of `σ`, every face `F` of `τ` is also a face of `σ`, and the restriction of
complex points along the face inclusion maps the stratum of `F` in the affine chart of `τ` into
the stratum of `F` in the affine chart of `σ`. In particular it maps distinguished points to
distinguished points. These are the compatibilities that let the affine orbit strata of the cones
of a fan be glued into torus orbits of the fan realization.

## Main declarations

* `TauCeti.Toric.faceAffinePointMap_mem_affineConeOrbit`: face localization preserves strata.
* `TauCeti.Toric.faceAffinePointMap_distinguishedPoint`: face localization preserves
  distinguished points.

## References

* W. Fulton, *Introduction to Toric Varieties*, §3.1.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §3.2.
-/

public section

open Multiplicative

namespace TauCeti.Toric

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {σ τ : PointedCone ℝ V} (hi : IsIntegralLattice i) (hτσ : τ.IsFaceOf σ)

/-- Restriction along a face inclusion `τ ≼ σ` maps the stratum of a face `F` of `τ` into the
stratum of the same cone `F`, viewed as a face `G` of `σ`. -/
theorem faceAffinePointMap_mem_affineConeOrbit {F : τ.Face} {G : σ.Face}
    (hFG : (F : PointedCone ℝ V) = G) {x : AffineSemigroupComplexPoint (dualSemigroup hi τ)}
    (hx : x ∈ affineConeOrbit hi F) :
    faceAffinePointMap hi hτσ x ∈ affineConeOrbit hi G := by
  have hmem : ∀ y, y ∈ G ↔ y ∈ F := (SetLike.ext_iff.mp hFG · |>.symm)
  rw [mem_affineConeOrbit] at hx ⊢
  intro m
  simp only [faceAffinePointMap_apply_single, hmem]
  exact hx _

/-- Restriction along a face inclusion `τ ≼ σ` sends the distinguished point of a face `F` of `τ`
to the distinguished point of the same cone `F`, viewed as a face `G` of `σ`. -/
theorem faceAffinePointMap_distinguishedPoint {F : τ.Face} {G : σ.Face}
    (hFG : (F : PointedCone ℝ V) = G) :
    faceAffinePointMap hi hτσ (distinguishedPoint hi F) = distinguishedPoint hi G := by
  have hmem : ∀ y, y ∈ F ↔ y ∈ G := SetLike.ext_iff.mp hFG
  refine AffineSemigroupComplexPoint.ext fun m ↦ ?_
  rw [faceAffinePointMap_apply_single, distinguishedPoint_apply_single,
    distinguishedPoint_apply_single]
  split_ifs with hF hG hG
  · rfl
  · exact absurd (fun y hy ↦ hF y ((hmem y).2 hy)) hG
  · exact absurd (fun y hy ↦ hG y ((hmem y).1 hy)) hF
  · rfl

end TauCeti.Toric
