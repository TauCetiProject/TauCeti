/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.MultipleEnds.Covering
import TauCeti.Algebra.BigOperators.Finset.Fiber

/-!
# Finite boundary values of a Schwarz--Christoffel map with several ends

A logarithmic prevertex is a boundary parameter whose image in the Riemann sphere is infinity.
When every finite prevertex exponent sum is at least `-1`, the finite spherical boundary values
are precisely the ordinary values at integrable real parameters, together with the value at
parameter infinity when the total exponent is less than `-1`. This description makes the
exceptional set in the multiple-end covering theorem explicit in the complex plane.

## References

* L. Ahlfors, *Complex Analysis*, Chapter 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Chapter 2.
-/

public section

noncomputable section

open Complex Set Topology UpperHalfPlane
open scoped OnePoint

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- The finite boundary trace: ordinary boundary values at integrable real parameters, with
the vertex at parameter infinity included exactly when it is finite. -/
def schwarzChristoffelFiniteBoundary (a e : ι → ℝ) (z₀ : UpperHalfPlane) : Set ℂ :=
  schwarzChristoffelBoundary a e z₀ '' {p | -1 < ∑ i with a i = p, e i} ∪
    if ∑ i, e i < -1 then {schwarzChristoffelVertexAtInfinity a e z₀} else ∅

/-- Membership in the finite boundary trace is an ordinary boundary value at an integrable
parameter, or the vertex at infinity when that vertex is finite. -/
@[simp]
theorem mem_schwarzChristoffelFiniteBoundary (a e : ι → ℝ) (z₀ : UpperHalfPlane) (w : ℂ) :
    w ∈ schwarzChristoffelFiniteBoundary a e z₀ ↔
      (∃ p, -1 < ∑ i with a i = p, e i ∧ schwarzChristoffelBoundary a e z₀ p = w) ∨
        (∑ i, e i < -1 ∧ w = schwarzChristoffelVertexAtInfinity a e z₀) := by
  simp [schwarzChristoffelFiniteBoundary]

/-- Changing the base point translates every finite boundary value by the same constant. -/
theorem schwarzChristoffelFiniteBoundary_change_base (a e : ι → ℝ)
    (b c : UpperHalfPlane) :
    schwarzChristoffelFiniteBoundary a e b =
      (fun w : ℂ => w - schwarzChristoffelPrimitive a e c b) ''
        schwarzChristoffelFiniteBoundary a e c := by
  ext w
  simp only [mem_schwarzChristoffelFiniteBoundary, Set.mem_image]
  constructor
  · rintro (⟨p, hp, rfl⟩ | ⟨hsum, rfl⟩)
    · refine ⟨schwarzChristoffelBoundary a e c p, ?_, ?_⟩
      · exact Or.inl ⟨p, hp, rfl⟩
      · rw [← schwarzChristoffelBoundary_change_base a e b c p hp]
    · refine ⟨schwarzChristoffelVertexAtInfinity a e c, ?_, ?_⟩
      · exact Or.inr ⟨hsum, rfl⟩
      · rw [← schwarzChristoffelVertexAtInfinity_change_base a e b c hsum]
  · rintro ⟨u, (⟨p, hp, rfl⟩ | ⟨hsum, rfl⟩), rfl⟩
    · exact Or.inl ⟨p, hp, schwarzChristoffelBoundary_change_base a e b c p hp⟩
    · exact Or.inr ⟨hsum,
        (schwarzChristoffelVertexAtInfinity_change_base a e b c hsum).symm⟩

/-- The finite trace is exactly the preimage in `ℂ` of the sphere-valued boundary range.
Logarithmic prevertices contribute no finite value. -/
theorem schwarzChristoffelFiniteBoundary_eq_preimage_range (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) (hfinite : ∀ j, -1 ≤ ∑ i with a i = a j, e i) :
    schwarzChristoffelFiniteBoundary a e z₀ =
      ((↑) : ℂ → OnePoint ℂ) ⁻¹' range (schwarzChristoffelSphereBoundary a e z₀) := by
  ext w
  constructor
  · intro hw
    rcases hw with ⟨p, hp, rfl⟩ | hw
    · exact ⟨p, schwarzChristoffelSphereBoundary_coe_of_exponent_sum_gt_neg_one
        a e z₀ p hp⟩
    · by_cases hsum : ∑ i, e i < -1
      · simp only [ite_eq_left hsum, mem_singleton_iff] at hw
        subst w
        exact ⟨∞, by simp [hsum]⟩
      · simp [hsum] at hw
  · rintro ⟨x, hx⟩
    induction x using OnePoint.rec with
    | infty =>
      by_cases hsum : ∑ i, e i < -1
      · simp only [schwarzChristoffelSphereBoundary_infty, ite_eq_left hsum] at hx
        exact Or.inr (by simp [hsum, OnePoint.coe_injective hx.symm])
      · simp [hsum] at hx
    | coe p =>
      have hp : -1 ≤ ∑ i with a i = p, e i :=
        le_sum_filter_eq_of_forall_apply (by norm_num) hfinite p
      rcases hp.eq_or_lt with hp | hp
      · simp [schwarzChristoffelSphereBoundary_coe_of_exponent_sum_eq_neg_one
          a e z₀ p hp.symm] at hx
      · left
        exact ⟨p, hp, OnePoint.coe_injective (by
          simpa only [schwarzChristoffelSphereBoundary_coe_of_exponent_sum_gt_neg_one
            a e z₀ p hp] using hx)⟩

/-- The finite boundary trace is closed, even when several real parameters map to infinity. -/
theorem isClosed_schwarzChristoffelFiniteBoundary (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) (hfinite : ∀ j, -1 ≤ ∑ i with a i = a j, e i) :
    IsClosed (schwarzChristoffelFiniteBoundary a e z₀) := by
  rw [schwarzChristoffelFiniteBoundary_eq_preimage_range a e z₀ hfinite]
  exact (isCompact_range (continuous_schwarzChristoffelSphereBoundary a e z₀ hfinite)).isClosed
    |>.preimage OnePoint.continuous_coe

/-- The closure of the primitive image consists of the image and its finite boundary trace.
This holds with any number of logarithmic prevertices, including when the parameter at infinity
also maps to infinity. -/
theorem closure_image_schwarzChristoffelPrimitive_eq_union_finiteBoundary
    (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    (hfinite : ∀ j, -1 ≤ ∑ i with a i = a j, e i) :
    closure (schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet) =
      schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet ∪
        schwarzChristoffelFiniteBoundary a e z₀ := by
  have hcl := closure_coe_image_schwarzChristoffelPrimitive a e z₀ hfinite
  rw [OnePoint.isOpenEmbedding_coe.isEmbedding.closure_eq_preimage_closure_image]
  rw [hcl, preimage_union, ← schwarzChristoffelFiniteBoundary_eq_preimage_range a e z₀ hfinite]
  congr 1
  exact Set.preimage_image_eq _ OnePoint.coe_injective

/-- The frontier consists of finite boundary values that the primitive does not also take in
the open upper half-plane. Thus an image-avoidance theorem makes the entire finite trace the
frontier, including for polygons with several ends. -/
theorem frontier_image_schwarzChristoffelPrimitive_eq_finiteBoundary_diff_image
    (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    (hfinite : ∀ j, -1 ≤ ∑ i with a i = a j, e i) :
    frontier (schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet) =
      schwarzChristoffelFiniteBoundary a e z₀ \
        (schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet) := by
  rw [(isOpen_image_schwarzChristoffelPrimitive a e z₀
    isOpen_upperHalfPlaneSet subset_rfl).frontier_eq,
    closure_image_schwarzChristoffelPrimitive_eq_union_finiteBoundary a e z₀ hfinite,
    union_sdiff_left]

end TauCeti
