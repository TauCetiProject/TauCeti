/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.ClosedEdge
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Compactification
import TauCeti.Algebra.BigOperators.Finset.Fiber

/-!
# Local straightness of a simple Schwarz--Christoffel boundary

At a real parameter away from the prevertices, the compactified boundary of a simple
Schwarz--Christoffel polygon agrees, in a neighbourhood of its image, with an open straight
segment. The global injectivity assumption matters: it prevents another part of the boundary
from entering every neighbourhood of the chosen edge point. This local description is an input
for identifying the complementary component mapped from the upper half-plane.

## References

* L. Ahlfors, *Complex Analysis*, Chapter 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Chapter 2.
-/

public section

noncomputable section

open Set UpperHalfPlane
open scoped OnePoint

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- Near a regular point of a simple compactified Schwarz--Christoffel boundary, the entire
boundary curve agrees with the open segment traced by that edge. In particular no other edge
enters this ball. -/
theorem exists_ball_inter_range_schwarzChristoffelCompactifiedBoundary_eq_openSegment
    (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    (hfinite : ∀ j, -1 < ∑ i with a i = a j, e i)
    (hinfty : ∑ i, e i < -1)
    (hinj : Function.Injective (schwarzChristoffelCompactifiedBoundary a e z₀))
    {p q x : ℝ} (hpq : p < q)
    (ha : ∀ i, e i ≠ 0 → a i ∉ Ioo p q) (hx : x ∈ Ioo p q) :
    ∃ ε : ℝ, 0 < ε ∧
      Metric.ball (schwarzChristoffelBoundary a e z₀ x) ε ∩
          range (schwarzChristoffelCompactifiedBoundary a e z₀) =
        Metric.ball (schwarzChristoffelBoundary a e z₀ x) ε ∩
          openSegment ℝ (schwarzChristoffelBoundary a e z₀ p)
            (schwarzChristoffelBoundary a e z₀ q) := by
  let Γ := schwarzChristoffelCompactifiedBoundary a e z₀
  let T : Set (OnePoint ℝ) := ((↑) : ℝ → OnePoint ℝ) '' Ioo p q
  have hTopen : IsOpen T := OnePoint.isOpen_image_coe.mpr isOpen_Ioo
  have hΓcont : Continuous Γ :=
    continuous_schwarzChristoffelCompactifiedBoundary a e z₀ hfinite hinfty
  have hKclosed : IsClosed (Γ '' Tᶜ) :=
    (hTopen.isClosed_compl.isCompact.image hΓcont).isClosed
  have hxT : (x : OnePoint ℝ) ∈ T := ⟨x, hx, rfl⟩
  have hxU : Γ (x : OnePoint ℝ) ∈ (Γ '' Tᶜ)ᶜ := by
    rintro ⟨t, ht, htx⟩
    exact ht (hinj htx ▸ hxT)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hKclosed.isOpen_compl _ hxU
  have hxΓ : Γ (x : OnePoint ℝ) = schwarzChristoffelBoundary a e z₀ x := by
    simp only [Γ, schwarzChristoffelCompactifiedBoundary_coe]
  rw [hxΓ] at hball
  have hend (y : ℝ) : -1 < ∑ i with a i = y, e i :=
    lt_sum_filter_eq_of_forall_apply neg_one_lt_zero hfinite y
  have hseg := schwarzChristoffelBoundary_image_Ioo a e z₀ hpq ha (hend p) (hend q)
  refine ⟨ε, hε, ?_⟩
  ext w
  constructor
  · rintro ⟨hw, ⟨t, rfl⟩⟩
    have ht : t ∈ T := by
      by_contra hnot
      exact (hball (by simpa only [Γ] using hw)) ⟨t, hnot, rfl⟩
    rcases ht with ⟨y, hy, rfl⟩
    refine ⟨hw, ?_⟩
    rw [← hseg]
    exact ⟨y, hy, (schwarzChristoffelCompactifiedBoundary_coe a e z₀ y).symm⟩
  · rintro ⟨hw, hsegmem⟩
    rw [← hseg] at hsegmem
    rcases hsegmem with ⟨y, hy, rfl⟩
    exact ⟨hw, ⟨(y : OnePoint ℝ), schwarzChristoffelCompactifiedBoundary_coe a e z₀ y⟩⟩

end TauCeti
