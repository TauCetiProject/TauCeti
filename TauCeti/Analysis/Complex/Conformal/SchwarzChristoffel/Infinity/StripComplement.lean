/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Infinity.Quadratic
import TauCeti.Algebra.BigOperators.Finset.Fiber
import TauCeti.Analysis.Complex.HorizontalStrip
import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Infinity.ExteriorPoint
import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Infinity.SimpleBoundary

/-!
# The strip-complement end of a quadratic Schwarz--Christoffel image

When the total turning exponent is `1`, the two outer boundary rays are horizontal, point to
the right, and have heights `im c` and `im c + π * C`. Here `c` is the quadratic constant at
infinity and `C = ((∑ i, e i * a i) ^ 2 - ∑ i, e i * a i ^ 2) / 2` is the logarithmic
coefficient. The boundary agrees with these two lines sufficiently far to the right, without
any simplicity assumption.

If the boundary is simple and `C < 0`, the image of the upper half-plane agrees there with the
complement of the closed strip between those lines. Thus the direct mapping theorem gives a
polygonal domain whose end is the exterior of a half-strip, an end of opening `2π`, rather than
only a complementary-component description. This is the counterpart of the half-strip end at
total exponent `-1`.

## Main results

* `TauCeti.exists_mem_range_schwarzChristoffelBoundary_iff_of_sum_eq_one`: far to the right,
  the boundary range is the pair of horizontal lines at the two outer heights.
* `TauCeti.exists_mem_image_schwarzChristoffelPrimitive_iff_of_sum_eq_one`: for a simple
  boundary with `C < 0`, the image far to the right is the complement of the closed strip
  between those lines.

## References

* L. Ahlfors, *Complex Analysis*, Chapter 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Chapter 2.
-/

public section

open Complex Metric Set
open UpperHalfPlane hiding I

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- With total exponent `1`, sufficiently far to the right the real boundary range is exactly
the pair of horizontal lines at heights `im c` and `im c + π * C`, where `c` is the quadratic
constant at infinity and `C = ((∑ i, e i * a i) ^ 2 - ∑ i, e i * a i ^ 2) / 2`. Repeated
prevertices and nonsimple boundary chains are allowed. -/
theorem exists_mem_range_schwarzChristoffelBoundary_iff_of_sum_eq_one
    (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    (hfinite : ∀ j, -1 < ∑ i with a i = a j, e i) (hsum : ∑ i, e i = 1) :
    ∃ R : ℝ, ∀ w : ℂ, R < w.re →
      (w ∈ range (schwarzChristoffelBoundary a e z₀) ↔
        w.im = (schwarzChristoffelQuadraticConstantAtInfinity a e z₀).im ∨
        w.im = (schwarzChristoffelQuadraticConstantAtInfinity a e z₀).im +
          Real.pi * (((∑ i, e i * a i) ^ 2 - ∑ i, e i * a i ^ 2) / 2)) := by
  obtain ⟨A, _, ha⟩ := (finite_range a).isBounded.exists_pos_norm_le
  have ha' (i : ι) : -A ≤ a i ∧ a i ≤ A :=
    abs_le.mp (by simpa using ha (a i) (mem_range_self i))
  obtain ⟨R, hR⟩ := exists_mem_range_schwarzChristoffelBoundary_iff_of_sum_eq_neg_one_or_eq_one
    a e z₀ hfinite (fun i _ => (ha' i).1) (fun i _ => (ha' i).2) (Or.inr hsum)
  rw [im_schwarzChristoffelBoundary_of_forall_le_of_sum_eq_one a e z₀
      (lt_sum_filter_eq_of_forall_apply neg_one_lt_zero hfinite A) (fun i _ => (ha' i).2) hsum,
    im_schwarzChristoffelBoundary_of_forall_ge_of_sum_eq_one a e z₀
      (lt_sum_filter_eq_of_forall_apply neg_one_lt_zero hfinite (-A)) (fun i _ => (ha' i).1)
      hsum] at hR
  exact ⟨R, hR⟩

/-- **The strip-complement end of a simple quadratic Schwarz--Christoffel map.** Suppose the
finite prevertices are integrable, the total exponent is `1`, the real boundary parametrization
is injective, and the logarithmic coefficient `C = ((∑ i, e i * a i) ^ 2 - ∑ i, e i * a i ^ 2) / 2`
is negative. Then sufficiently far to the right the image is exactly the set of points below
height `im c + π * C` or above height `im c`, where `c` is the quadratic constant at infinity:
the complement of the closed strip between the two outer sides. No ordering assumption on the
finite data is needed. -/
theorem exists_mem_image_schwarzChristoffelPrimitive_iff_of_sum_eq_one
    (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    (hfinite : ∀ j, -1 < ∑ i with a i = a j, e i) (hsum : ∑ i, e i = 1)
    (hC : (∑ i, e i * a i) ^ 2 < ∑ i, e i * a i ^ 2)
    (hinj : Function.Injective (schwarzChristoffelBoundary a e z₀)) :
    ∃ R : ℝ, ∀ w : ℂ, R < w.re →
      (w ∈ schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet ↔
        w.im < (schwarzChristoffelQuadraticConstantAtInfinity a e z₀).im +
            Real.pi * (((∑ i, e i * a i) ^ 2 - ∑ i, e i * a i ^ 2) / 2) ∨
          (schwarzChristoffelQuadraticConstantAtInfinity a e z₀).im < w.im) := by
  have hπC : Real.pi * (((∑ i, e i * a i) ^ 2 - ∑ i, e i * a i ^ 2) / 2) < 0 :=
    mul_neg_of_pos_of_neg Real.pi_pos (by linarith)
  obtain ⟨R₁, hboundary⟩ :=
    exists_mem_range_schwarzChristoffelBoundary_iff_of_sum_eq_one a e z₀ hfinite hsum
  obtain ⟨R₂, hband⟩ :=
    exists_forall_notMem_closure_image_schwarzChristoffelPrimitive_of_sum_eq_one a e z₀
      hfinite hsum hC (δ := -(Real.pi * (((∑ i, e i * a i) ^ 2 - ∑ i, e i * a i ^ 2) / 2)) / 4)
      (by linarith)
  set U := schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet
  set hi := (schwarzChristoffelQuadraticConstantAtInfinity a e z₀).im
  set d := Real.pi * (((∑ i, e i * a i) ^ 2 - ∑ i, e i * a i ^ 2) / 2)
  set lo := hi + d
  have hgap : lo < hi := by linarith
  set R := max R₁ R₂
  have hUo : IsOpen U :=
    isOpen_image_schwarzChristoffelPrimitive a e z₀ isOpen_upperHalfPlaneSet subset_rfl
  have hfrontier : frontier U = range (schwarzChristoffelBoundary a e z₀) :=
    frontier_image_schwarzChristoffelPrimitive_eq_range_of_neg_one_le_sum a e z₀ hfinite
      (by rw [hsum]; norm_num) (Or.inr ⟨hsum, hC⟩) hinj
  -- To the right of `R`, the frontier of the image lies on the two lines.
  have hline (w : ℂ) (hw : R < w.re) : w ∈ frontier U ↔ w.im = hi ∨ w.im = lo := by
    rw [hfrontier]
    exact hboundary w ((le_max_left _ _).trans_lt hw)
  -- The midpoint of the band far to the right is an exterior point.
  have hext : (⟨R + 1, (lo + hi) / 2⟩ : ℂ) ∉ closure U :=
    hband _ ((le_max_right R₁ R₂).trans_lt (lt_add_one R)) (by dsimp only; linarith)
      (by dsimp only; linarith)
  exact ⟨R, fun w hwR => mem_iff_im_lt_or_lt_im_of_frontier_eq hUo hgap hline hext hwR⟩

end TauCeti
