/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Boundary
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Infinity
public import TauCeti.Topology.JordanCurve.OnePoint

/-!
# The compactified Schwarz--Christoffel boundary

When the total Schwarz--Christoffel exponent is less than `-1`, the two ends of the real boundary
have the same finite image.  This file therefore joins the ordinary boundary map on `ℝ` with its
value at infinity to give a map on the real projective line `OnePoint ℝ`.

If every finite prevertex is integrable, the compactified boundary map is continuous.  Its exact
injectivity criterion separates the remaining global simplicity problem into two concrete claims:
the finite boundary map has no self-intersections, and it never passes through the vertex at
infinity.  Once those claims hold, its range is a Jordan curve.  This is the topological boundary
object used to identify the image of a Schwarz--Christoffel primitive with a polygonal domain.

## Main definitions

* `TauCeti.schwarzChristoffelCompactifiedBoundary` -- the Schwarz--Christoffel boundary on
  `OnePoint ℝ`.

## Main results

* `TauCeti.continuous_schwarzChristoffelCompactifiedBoundary` -- integrable finite prevertices and
  decay at infinity make the compactified boundary continuous.
* `TauCeti.schwarzChristoffelCompactifiedBoundary_injective_iff` -- exact global simplicity
  criterion in terms of the finite boundary and the vertex at infinity.
* `TauCeti.isJordanCurve_range_schwarzChristoffelCompactifiedBoundary` -- an injective
  compactified boundary traces a Jordan curve.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
-/

public section

noncomputable section

open Complex Filter Set Topology UpperHalfPlane
open scoped OnePoint

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- The Schwarz--Christoffel boundary on the real projective line.  It agrees with
`schwarzChristoffelBoundary` at every finite real point and sends the compactifying point to the
common boundary value `schwarzChristoffelVertexAtInfinity`. -/
def schwarzChristoffelCompactifiedBoundary (a e : ι → ℝ) (z₀ : UpperHalfPlane) :
    OnePoint ℝ → ℂ :=
  fun x => x.elim (schwarzChristoffelVertexAtInfinity a e z₀)
    (schwarzChristoffelBoundary a e z₀)

/-- The compactified Schwarz--Christoffel boundary takes the prescribed value at infinity. -/
@[simp]
theorem schwarzChristoffelCompactifiedBoundary_infty (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) :
    schwarzChristoffelCompactifiedBoundary a e z₀ ∞ =
      schwarzChristoffelVertexAtInfinity a e z₀ :=
  (rfl)

/-- At a finite point, the compactified Schwarz--Christoffel boundary is the ordinary boundary
value. -/
@[simp]
theorem schwarzChristoffelCompactifiedBoundary_coe (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) (x : ℝ) :
    schwarzChristoffelCompactifiedBoundary a e z₀ (x : OnePoint ℝ) =
      schwarzChristoffelBoundary a e z₀ x :=
  (rfl)

/-- The compactified Schwarz--Christoffel boundary is continuous when every prevertex has
integrable total exponent and the primitive has a finite limit at infinity.

The first hypothesis supplies continuity of the boundary map on `ℝ`.  The inequality on the
total exponent supplies convergence to the same vertex along the cocompact filter, which is
exactly continuity at the added point of `OnePoint ℝ`. -/
theorem continuous_schwarzChristoffelCompactifiedBoundary (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) (hfinite : ∀ j, -1 < ∑ i with a i = a j, e i)
    (hinfty : ∑ i, e i < -1) :
    Continuous (schwarzChristoffelCompactifiedBoundary a e z₀) := by
  classical
  have hfinite' : ∀ x, -1 < ∑ i with a i = x, e i := by
    intro x
    by_cases hx : x ∈ Set.range a
    · obtain ⟨j, rfl⟩ := hx
      exact hfinite j
    · have hzero : ∑ i with a i = x, e i = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        exact (hx ⟨i, (Finset.mem_filter.mp hi).2⟩).elim
      rw [hzero]
      norm_num
  rw [OnePoint.continuous_iff]
  constructor
  · apply tendsto_schwarzChristoffelBoundaryValue_atInfinity a e z₀ hinfty
    · have habs : (fun x : ℝ => |x|) = norm :=
        funext fun x => (Real.norm_eq_abs x).symm
      rw [habs, Filter.coclosedCompact_eq_cocompact]
      exact tendsto_norm_cocompact_atTop
    · exact Filter.Eventually.of_forall fun x =>
        tendsto_schwarzChristoffelPrimitive_boundary a e z₀ x (hfinite' x)
  · rw [← continuousOn_univ]
    exact continuousOn_schwarzChristoffelBoundary_of_exponent_sum_gt_neg_one a e z₀
      fun x _ => hfinite' x

/-- The compactified boundary is injective exactly when its finite part is injective and no finite
boundary value equals the vertex at infinity.  Thus the global boundary-simplicity problem has no
hidden condition at the compactification point. -/
theorem schwarzChristoffelCompactifiedBoundary_injective_iff (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) :
    Function.Injective (schwarzChristoffelCompactifiedBoundary a e z₀) ↔
      Function.Injective (schwarzChristoffelBoundary a e z₀) ∧
        ∀ x, schwarzChristoffelBoundary a e z₀ x ≠
          schwarzChristoffelVertexAtInfinity a e z₀ := by
  -- `OnePoint ℝ` is implemented by `Option ℝ`; expose that representation here to use
  -- Mathlib's exact injectivity criterion for an option-valued domain.
  change Function.Injective (fun x : Option ℝ =>
      x.elim (schwarzChristoffelVertexAtInfinity a e z₀)
        (schwarzChristoffelBoundary a e z₀)) ↔ _
  rw [Option.injective_iff]
  simp only [Function.comp_def, Option.elim_none, Option.elim_some, Set.mem_range,
    not_exists, ne_eq]

/-- An injective compactified Schwarz--Christoffel boundary traces a Jordan curve.  Continuity is
supplied by integrability at every finite prevertex and decay at infinity; injectivity is left in
the exact form characterized by `schwarzChristoffelCompactifiedBoundary_injective_iff`. -/
theorem isJordanCurve_range_schwarzChristoffelCompactifiedBoundary (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) (hfinite : ∀ j, -1 < ∑ i with a i = a j, e i)
    (hinfty : ∑ i, e i < -1)
    (hinj : Function.Injective (schwarzChristoffelCompactifiedBoundary a e z₀)) :
    IsJordanCurve (Set.range (schwarzChristoffelCompactifiedBoundary a e z₀)) := by
  have h := isJordanCurve_univ_onePoint_real.image
    (continuous_schwarzChristoffelCompactifiedBoundary a e z₀ hfinite hinfty).continuousOn
    hinj.injOn
  simpa only [image_univ] using h

end TauCeti
