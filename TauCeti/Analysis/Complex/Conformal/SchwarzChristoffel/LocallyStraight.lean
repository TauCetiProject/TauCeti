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
# A simple Schwarz--Christoffel boundary is locally straight at regular edges

On an interval free of turning prevertices, the Schwarz--Christoffel boundary traces an open
line segment. If the compactified boundary is simple, compactness prevents any other part of
the curve from accumulating at an interior point of that segment. Thus, in a small ball, the
entire curve agrees with the open segment. This identifies the local geometry needed to select
the bounded component of the polygonal complement.

The argument follows the polygonal-boundary viewpoint of Driscoll and Trefethen,
*Schwarz--Christoffel Mapping*, Chapter 2.
-/

public section

noncomputable section

open Set Metric

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- Near the image of a point strictly inside a regular edge, a simple compactified
Schwarz--Christoffel boundary consists precisely of that open straight edge. -/
theorem schwarzChristoffelCompactifiedBoundary_locally_openSegment
    (a e : ι → ℝ) (z₀ : UpperHalfPlane) {p q x : ℝ}
    (ha : ∀ i, e i ≠ 0 → a i ∉ Ioo p q)
    (hfinite : ∀ j, -1 < ∑ i with a i = a j, e i)
    (hinfty : ∑ i, e i < -1)
    (hinj : Function.Injective (schwarzChristoffelCompactifiedBoundary a e z₀))
    (hx : x ∈ Ioo p q) :
    ∃ ε : ℝ, 0 < ε ∧
      range (schwarzChristoffelCompactifiedBoundary a e z₀) ∩
          ball (schwarzChristoffelBoundary a e z₀ x) ε =
        openSegment ℝ (schwarzChristoffelBoundary a e z₀ p)
          (schwarzChristoffelBoundary a e z₀ q) ∩
            ball (schwarzChristoffelBoundary a e z₀ x) ε := by
  let f := schwarzChristoffelCompactifiedBoundary a e z₀
  let s : Set (OnePoint ℝ) := ((↑) : ℝ → OnePoint ℝ) '' Ioo p q
  have hs : IsOpen s := OnePoint.isOpen_image_coe.mpr isOpen_Ioo
  have hxS : (x : OnePoint ℝ) ∈ s := ⟨x, hx, rfl⟩
  have hc : IsCompact (sᶜ : Set (OnePoint ℝ)) :=
    isCompact_univ.of_isClosed_subset hs.isClosed_compl (subset_univ _)
  have hf : Continuous f := continuous_schwarzChristoffelCompactifiedBoundary a e z₀
    hfinite hinfty
  have hclosed : IsClosed (f '' sᶜ) := (hc.image hf).isClosed
  have hnot : f (x : OnePoint ℝ) ∉ f '' sᶜ := by
    rintro ⟨y, hy, heq⟩
    exact hy (hinj heq ▸ hxS)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    (hclosed.isOpen_compl.mem_nhds hnot)
  have hball' : ball (schwarzChristoffelBoundary a e z₀ x) ε ⊆ (f '' sᶜ)ᶜ := by
    simpa only [f, schwarzChristoffelCompactifiedBoundary_coe] using hball
  refine ⟨ε, hε, ?_⟩
  have hend := lt_sum_filter_eq_of_forall_apply neg_one_lt_zero hfinite
  rw [← schwarzChristoffelBoundary_image_Ioo a e z₀ (hx.1.trans hx.2) ha
    (hend p) (hend q)]
  ext z
  constructor
  · rintro ⟨⟨t, rfl⟩, hz⟩
    have ht : t ∈ s := by
      by_contra hts
      exact (hball' hz) ⟨t, hts, rfl⟩
    obtain ⟨y, hy, rfl⟩ := ht
    exact ⟨⟨y, hy, (schwarzChristoffelCompactifiedBoundary_coe a e z₀ y).symm⟩, hz⟩
  · rintro ⟨⟨y, hy, rfl⟩, hz⟩
    exact ⟨⟨(y : OnePoint ℝ), schwarzChristoffelCompactifiedBoundary_coe a e z₀ y⟩, hz⟩

end TauCeti
