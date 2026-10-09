/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Geodesic.FromTo
public import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Affine
import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Translation

/-!
# Rays to points of `ℍ ∪ ∂ℍ`

`UpperHalfPlane.rayToward A p` is the geodesic line leaving `A ∈ ℍ` at parameter `0` towards a
point `p ≠ A` of `ℍ ∪ ∂ℍ`: `geodesicBetween A B` for `p = B ∈ ℍ`, and for an ideal point `ξ` the
unique geodesic line with `A` at parameter `0` and forward endpoint `ξ`. For `p = A` it is an
arbitrary geodesic line through `A`, and the ray interpretation needs `.inl A ≠ p`. The ray
towards `∞` is the upward vertical `UpperHalfPlane.toPoint A` through `A`, a ray runs from its
base point to its target, and rays are equivariant under `PSL(2, ℝ)`.

## Main declarations

* `UpperHalfPlane.rayToward A p`: the geodesic ray from `A ∈ ℍ` towards `p ∈ ℍ ∪ ∂ℍ`, `p ≠ A`.
* `UpperHalfPlane.rayToward_inr_infty`, `UpperHalfPlane.isGeodesicFromTo_rayToward`,
  `TauCeti.UpperHalfPlane.rayToward_smul`: the ray towards `∞` is the upward vertical; a ray runs
  from its base point to its target; rays are equivariant.
* `UpperHalfPlane.rayToward_eq_geodesicBetween`: a ray is the geodesic from its base point to its
  point at parameter `1`.
* `TauCeti.UpperHalfPlane.rayToward_geodesicLine_inr_smul_infty`: the ray from a point of a
  geodesic line towards its forward endpoint is that line, reparametrised.

## Source

Walkden, *Hyperbolic geometry* (MATH32051 lecture notes, Manchester 2019), §7.1 (the unique
geodesic through two points of `ℍ ∪ ∂ℍ`).
-/

public section

noncomputable section

open UpperHalfPlane TauCeti.UpperHalfPlane
open scoped MatrixGroups Pointwise OnePoint

namespace UpperHalfPlane


/-- The geodesic line leaving `A` at parameter `0` towards a point `p ≠ A` of `ℍ ∪ ∂ℍ`:
`geodesicBetween A B` for `p = B ∈ ℍ`, and for an ideal point `ξ` the geodesic line with `A` at
parameter `0` and forward endpoint `ξ`. For `p = A` it is `geodesicBetween A A`, an arbitrary
geodesic line through `A`, with no direction towards the target. -/
def rayToward (A : ℍ) (p : ℍ ⊕ OnePoint ℝ) : PSL(2, ℝ) :=
  Sum.elim (geodesicBetween A) (fun ξ ↦ (exists_geodesicLine_zero_eq_and_smul_infty_eq A ξ).choose)
    p

@[simp]
theorem rayToward_inl (A B : ℍ) : rayToward A (.inl B) = geodesicBetween A B := by
  rfl

/-- A ray starts at its base point. -/
@[simp]
theorem geodesicLine_rayToward_zero (A : ℍ) (p : ℍ ⊕ OnePoint ℝ) :
    geodesicLine (rayToward A p) 0 = A := by
  rcases p with B | ξ
  · exact geodesicLine_geodesicBetween_zero A B
  · exact (exists_geodesicLine_zero_eq_and_smul_infty_eq A ξ).choose_spec.1

/-- A ray towards an ideal point has it as forward endpoint. -/
@[simp]
theorem rayToward_inr_smul_infty (A : ℍ) (ξ : OnePoint ℝ) :
    rayToward A (.inr ξ) • (∞ : OnePoint ℝ) = ξ :=
  (exists_geodesicLine_zero_eq_and_smul_infty_eq A ξ).choose_spec.2

/-- The ray from `A` towards `∞` is the upward vertical through `A`. -/
@[simp]
theorem rayToward_inr_infty (A : ℍ) : rayToward A (.inr ∞) = toPoint A :=
  eq_of_geodesicLine_zero_eq_of_smul_infty_eq
    (by rw [geodesicLine_rayToward_zero, geodesicLine_zero, toPoint_smul_I])
    (by rw [rayToward_inr_smul_infty, toPoint_smul_infty])

/-- A ray from `A` towards `p ≠ A` runs from `A` to `p`. -/
theorem isGeodesicFromTo_rayToward {A : ℍ} {p : ℍ ⊕ OnePoint ℝ} (hAp : .inl A ≠ p) :
    IsGeodesicFromTo (rayToward A p) (.inl A) p := by
  rcases p with B | ξ
  · exact isGeodesicFromTo_geodesicBetween fun h ↦ hAp (congrArg _ h)
  · exact isGeodesicFromTo_inl_inr.2
      ⟨⟨0, geodesicLine_rayToward_zero A _⟩, rayToward_inr_smul_infty A ξ⟩

/-- A ray is the geodesic from its base point to its point at parameter `1`. -/
theorem rayToward_eq_geodesicBetween (A : ℍ) (p : ℍ ⊕ OnePoint ℝ) :
    rayToward A p = geodesicBetween A (geodesicLine (rayToward A p) 1) := by
  have h₀ := geodesicLine_rayToward_zero A p
  have hne : A ≠ geodesicLine (rayToward A p) 1 := fun h ↦
    zero_ne_one (geodesicLine_injective _ (h₀.trans h))
  have hd : dist A (geodesicLine (rayToward A p) 1) = 1 := by
    simpa [h₀] using dist_geodesicLine (rayToward A p) 0 1
  exact eq_geodesicBetween_of_geodesicLine_eq hne h₀ (by rw [hd])

end UpperHalfPlane

namespace TauCeti.UpperHalfPlane

/-- Rays transform naturally under the action. -/
theorem rayToward_smul (h : PSL(2, ℝ)) {A : ℍ} {p : ℍ ⊕ OnePoint ℝ} (hAp : .inl A ≠ p) :
    rayToward (h • A) (h • p) = h * rayToward A p := by
  rcases p with B | ξ
  · rw [Sum.smul_inl, rayToward_inl, rayToward_inl,
      geodesicBetween_smul h fun hAB ↦ hAp (congrArg _ hAB)]
  · rw [Sum.smul_inr]
    refine eq_of_geodesicLine_zero_eq_of_smul_infty_eq ?_ ?_
    · rw [geodesicLine_rayToward_zero, ← smul_geodesicLine, geodesicLine_rayToward_zero]
    · rw [rayToward_inr_smul_infty, mul_smul, rayToward_inr_smul_infty]

/-- The ray from the point of a geodesic line at parameter `s` towards its forward endpoint is
that line, reparametrised to start at `s`. -/
theorem rayToward_geodesicLine_inr_smul_infty (g : PSL(2, ℝ)) (s : ℝ) :
    rayToward (geodesicLine g s) (.inr (g • (∞ : OnePoint ℝ))) =
      g * ↑(Matrix.SpecialLinearGroup.dilation s) :=
  eq_of_geodesicLine_zero_eq_of_smul_infty_eq
    (by rw [geodesicLine_rayToward_zero, geodesicLine_mul_dilation, add_zero])
    (by rw [rayToward_inr_smul_infty, mul_smul, dilation_smul_infty])

end TauCeti.UpperHalfPlane
