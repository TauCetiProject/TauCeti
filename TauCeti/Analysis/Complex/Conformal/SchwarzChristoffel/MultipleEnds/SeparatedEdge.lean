/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.MultipleEnds.BoundarySheet
import TauCeti.Algebra.BigOperators.Finset.Fiber

/-!
# A separated boundary side determines one Schwarz--Christoffel sheet

For Schwarz--Christoffel data with logarithmic ends, the sphere-valued boundary sends every
logarithmic prevertex to infinity and may therefore fail to be globally injective.  Global
univalence of the primitive needs much less: one finite value on a regular side must have a
unique boundary parameter.

This file turns geometric separation of one regular side from the remaining finite boundary
trace into that uniqueness statement.  Injectivity along the chosen side is automatic.  The
only checks left to the caller are that the open side is disjoint from the other finite sides
and, when the parameter at infinity has a finite value, does not contain that value.  The
resulting criterion feeds directly into the single-boundary-sheet mapping theorem.

## References

* L. Ahlfors, *Complex Analysis*, Chapter 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Chapter 2.
-/

public section

noncomputable section

open Complex Set UpperHalfPlane
open scoped OnePoint

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- A finite value in the interior of a regular boundary side has a unique parameter in the
sphere-valued boundary if it occurs on no other integrable side and is different from the
finite value at parameter infinity.  Values on the chosen side are already unique there by
strict monotonicity of the boundary parametrization.

The second separation hypothesis matters only when the total exponent is less than `-1`,
which is exactly when the parameter at infinity has a finite boundary value. -/
theorem eq_coe_of_schwarzChristoffelSphereBoundary_eq_of_separated_edge
    (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    (hfinite : ∀ j, -1 ≤ ∑ i with a i = a j, e i) {p q x : ℝ}
    (ha : ∀ i, e i ≠ 0 → a i ∉ Ioo p q) (hx : x ∈ Ioo p q)
    (hother : Disjoint (schwarzChristoffelBoundary a e z₀ '' Ioo p q)
      (schwarzChristoffelBoundary a e z₀ ''
        ({y | -1 < ∑ i with a i = y, e i} \ Ioo p q)))
    (hinfty : ∑ i, e i < -1 →
      schwarzChristoffelVertexAtInfinity a e z₀ ∉
        schwarzChristoffelBoundary a e z₀ '' Ioo p q)
    {t : OnePoint ℝ}
    (ht : schwarzChristoffelSphereBoundary a e z₀ t =
      schwarzChristoffelSphereBoundary a e z₀ (x : OnePoint ℝ)) :
    t = (x : OnePoint ℝ) := by
  classical
  have hxsum : -1 < ∑ i with a i = x, e i := by
    rw [sum_filter_eq_zero_of_mem_Ioo a e ha hx]
    norm_num
  have hxvalue : schwarzChristoffelSphereBoundary a e z₀ (x : OnePoint ℝ) =
      (schwarzChristoffelBoundary a e z₀ x : OnePoint ℂ) :=
    schwarzChristoffelSphereBoundary_coe_of_exponent_sum_gt_neg_one a e z₀ x hxsum
  induction t using OnePoint.rec with
  | infty =>
      by_cases hsum : ∑ i, e i < -1
      · rw [schwarzChristoffelSphereBoundary_infty, ite_eq_left hsum, hxvalue] at ht
        exact False.elim (hinfty hsum ⟨x, hx, (OnePoint.coe_injective ht).symm⟩)
      · rw [schwarzChristoffelSphereBoundary_infty, ite_eq_right hsum, hxvalue] at ht
        exact False.elim (OnePoint.infty_ne_coe _ ht)
  | coe y =>
      have hysum : -1 ≤ ∑ i with a i = y, e i :=
        le_sum_filter_eq_of_forall_apply (by norm_num) hfinite y
      rcases hysum.eq_or_lt with hysum | hysum
      · rw [schwarzChristoffelSphereBoundary_coe_of_exponent_sum_eq_neg_one
          a e z₀ y hysum.symm, hxvalue] at ht
        exact False.elim (OnePoint.infty_ne_coe _ ht)
      · rw [schwarzChristoffelSphereBoundary_coe_of_exponent_sum_gt_neg_one
          a e z₀ y hysum, hxvalue] at ht
        have hboundary : schwarzChristoffelBoundary a e z₀ y =
            schwarzChristoffelBoundary a e z₀ x := OnePoint.coe_injective ht
        have hy : y ∈ Ioo p q := by
          by_contra hy
          exact disjoint_left.mp hother ⟨x, hx, rfl⟩ ⟨y, ⟨hysum, hy⟩, hboundary⟩
        exact congrArg ((↑) : ℝ → OnePoint ℝ)
          (schwarzChristoffelBoundary_injOn a e z₀ ha hy hx hboundary)

/-- **Univalence from a separated regular side.**  If the primitive image avoids its finite
boundary trace, a regular side disjoint from all other finite sides and from the finite value
at parameter infinity forces global injectivity. -/
theorem injOn_schwarzChristoffelPrimitive_of_separated_edge
    (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    (hfinite : ∀ j, -1 ≤ ∑ i with a i = a j, e i)
    (havoid : Disjoint (schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet)
      (schwarzChristoffelFiniteBoundary a e z₀)) {p q : ℝ} (hpq : p < q)
    (ha : ∀ i, e i ≠ 0 → a i ∉ Ioo p q)
    (hother : Disjoint (schwarzChristoffelBoundary a e z₀ '' Ioo p q)
      (schwarzChristoffelBoundary a e z₀ ''
        ({y | -1 < ∑ i with a i = y, e i} \ Ioo p q)))
    (hinfty : ∑ i, e i < -1 →
      schwarzChristoffelVertexAtInfinity a e z₀ ∉
        schwarzChristoffelBoundary a e z₀ '' Ioo p q) :
    InjOn (schwarzChristoffelPrimitive a e z₀) upperHalfPlaneSet := by
  have hx : (p + q) / 2 ∈ Ioo p q := by constructor <;> linarith
  apply injOn_schwarzChristoffelPrimitive_of_unique_boundary_value a e z₀ hfinite havoid ha hx
  intro t ht
  exact eq_coe_of_schwarzChristoffelSphereBoundary_eq_of_separated_edge
    a e z₀ hfinite ha hx hother hinfty ht

/-- **Component mapping from a separated regular side.**  Under boundary avoidance, the
primitive maps the upper half-plane bijectively onto the complementary component of its finite
boundary trace containing the base-point image as soon as one regular side is disjoint from the
remaining finite boundary. -/
theorem bijOn_schwarzChristoffelPrimitive_connectedComponentIn_of_separated_edge
    (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    (hfinite : ∀ j, -1 ≤ ∑ i with a i = a j, e i)
    (havoid : Disjoint (schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet)
      (schwarzChristoffelFiniteBoundary a e z₀)) {p q : ℝ} (hpq : p < q)
    (ha : ∀ i, e i ≠ 0 → a i ∉ Ioo p q)
    (hother : Disjoint (schwarzChristoffelBoundary a e z₀ '' Ioo p q)
      (schwarzChristoffelBoundary a e z₀ ''
        ({y | -1 < ∑ i with a i = y, e i} \ Ioo p q)))
    (hinfty : ∑ i, e i < -1 →
      schwarzChristoffelVertexAtInfinity a e z₀ ∉
        schwarzChristoffelBoundary a e z₀ '' Ioo p q) :
    BijOn (schwarzChristoffelPrimitive a e z₀) upperHalfPlaneSet
      (connectedComponentIn (schwarzChristoffelFiniteBoundary a e z₀)ᶜ
        (schwarzChristoffelPrimitive a e z₀ z₀)) := by
  have hx : (p + q) / 2 ∈ Ioo p q := by constructor <;> linarith
  apply bijOn_schwarzChristoffelPrimitive_connectedComponentIn_of_unique_boundary_value
    a e z₀ hfinite havoid ha hx
  intro t ht
  exact eq_coe_of_schwarzChristoffelSphereBoundary_eq_of_separated_edge
    a e z₀ hfinite ha hx hother hinfty ht

end TauCeti
