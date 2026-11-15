/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Residue.Cycle
public import TauCeti.Analysis.Contour.Curve.Rectangle
import TauCeti.Analysis.Contour.Winding.Number.Rectangle

/-!
# The classical residue theorem on a rectangle

For a closed rectangle `R = Complex.Rectangle z w` with `z` its lower left corner, and a function
`f` analytic at every point of `R \ S` and meromorphic at every point of `S ∩ R` for a finite set
`S` avoiding the frontier of `R`, the contour integral of `f` along the counterclockwise boundary
`Complex.rectBoundary z w` is

`∫ t in 0..4, γ' t • f (γ t) = 2πi · ∑_{s ∈ S ∩ R} Res_s f`.

Equivalently, the signed sum of the four edge integrals equals `2πi` times the sum of the residues
at the points of `S` inside the rectangle. This evaluates the winding numbers in
`TauCeti.Contour.classicalResidueTheorem_nullHomologous` on the open neighborhood where `f` is
analytic off `S ∩ R`: `1` on the interior of `R` and `0` outside `R`. Shifting a Mellin or
Dirichlet vertical line of integration applies the four-edge form to `[σ₁, σ₂] × [-T, T]` and sends
`T → ∞`.

## Main results

* `TauCeti.Contour.classicalResidueTheorem_rectBoundary`: the residue theorem for
  `Complex.rectBoundary z w`.
* `TauCeti.Contour.integral_boundary_rect_eq_sum_residue`: the four-edge expansion of the rectangle
  residue theorem, generalizing `Complex.integral_boundary_rect_eq_zero_of_differentiableOn`.

## References

* L. Ahlfors, *Complex Analysis*, 3rd ed., Chapter 4, §5.
-/

public section

open Set Complex Filter
open scoped Real Topology

namespace TauCeti.Contour

variable {f : ℂ → ℂ} {S : Finset ℂ} {z w : ℂ}

open scoped Classical in
/-- **The classical residue theorem on a rectangle.** Let `z` be the lower left corner of a closed
rectangle `Rectangle z w`, and let `f` be analytic at every point of `Rectangle z w \ S` and
meromorphic at every point of `S ∩ Rectangle z w`, where `S` avoids `frontier (Rectangle z w)`.
Then the contour integral of `f` along the counterclockwise boundary `rectBoundary z w` equals
`2πi` times the sum of `residue f s` over `s ∈ S` lying in the rectangle. -/
theorem classicalResidueTheorem_rectBoundary (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hf : ∀ p ∈ Rectangle z w, p ∉ S → AnalyticAt ℂ f p)
    (hmero : ∀ s ∈ S, s ∈ Rectangle z w → MeromorphicAt f s)
    (hS : ∀ s ∈ S, s ∉ frontier (Rectangle z w)) :
    ∫ t in (0 : ℝ)..4, deriv (rectBoundary z w) t • f (rectBoundary z w t) =
      2 * π * I * ∑ s ∈ S with s ∈ Rectangle z w, residue f s := by
  set S₀ : Finset ℂ := S.filter (· ∈ Rectangle z w)
  set U : Set ℂ := {p | p ∈ S₀ ∨ AnalyticAt ℂ f p}
  have hU : IsOpen U := isOpen_iff_mem_nhds.mpr fun p hp ↦ by
    rcases hp with hp | hp
    · obtain ⟨hsS, hsR⟩ := Finset.mem_filter.mp hp
      filter_upwards [eventually_nhdsWithin_iff.mp (hmero p hsS hsR).eventually_analyticAt]
        with q hq
      rcases eq_or_ne q p with rfl | hne
      · exact Or.inl hp
      · exact Or.inr (hq hne)
    · exact hp.eventually_analyticAt.mono fun _ ↦ Or.inr
  have hRU : Rectangle z w ⊆ U := fun p hp ↦
    if hpS : p ∈ S then Or.inl (Finset.mem_filter.mpr ⟨hpS, hp⟩) else Or.inr (hf p hp hpS)
  have hfU : DifferentiableOn ℂ f (U \ (↑S₀ : Set ℂ)) := fun p hp ↦
    (hp.1.resolve_left hp.2).differentiableAt.differentiableWithinAt
  have hmeroU : ∀ s ∈ S₀, s ∈ U → MeromorphicAt f s := fun s hs _ ↦
    hmero s (Finset.mem_filter.mp hs).1 (Finset.mem_filter.mp hs).2
  have hS₀ : ∀ s ∈ S₀, s ∉ frontier (Rectangle z w) := fun s hs ↦
    hS s (Finset.mem_filter.mp hs).1
  rw [classicalResidueTheorem_nullHomologous hU hfU hmeroU (isPiecewiseC1On_rectBoundary z w)
    (fun t _ ↦ hRU (rectBoundary_mem_rectangle t)) (by simp)
    (fun _ _ hmem ↦ hS₀ _ hmem (rectBoundary_mem_frontier _))
    (isNullHomologous_rectBoundary hRU)]
  refine congrArg _ (Finset.sum_congr rfl fun s hs ↦ ?_)
  obtain ⟨hsS, hsR⟩ := Finset.mem_filter.mp hs
  rw [windingNumber_rectBoundary_eq_one (mem_Ioo_reProdIm_of_mem_rectangle hre him hsR (hS s hsS)),
    one_mul]

open scoped Classical in
/-- **The four-edge residue formula on a rectangle.** Under the hypotheses of
`classicalResidueTheorem_rectBoundary`, the signed sum of the horizontal and vertical edge integrals
of `f` around `Rectangle z w` equals `2πi` times the sum of `residue f s` over
`s ∈ S ∩ Rectangle z w`. -/
theorem integral_boundary_rect_eq_sum_residue (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hf : ∀ p ∈ Rectangle z w, p ∉ S → AnalyticAt ℂ f p)
    (hmero : ∀ s ∈ S, s ∈ Rectangle z w → MeromorphicAt f s)
    (hS : ∀ s ∈ S, s ∉ frontier (Rectangle z w)) :
    (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
        I * (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) -
        I * (∫ y : ℝ in z.im..w.im, f (z.re + y * I)) =
      2 * π * I * ∑ s ∈ S with s ∈ Rectangle z w, residue f s := by
  have hcont : ContinuousOn f (frontier (Rectangle z w)) := fun p hp ↦
    (hf p ((isClosed_rectangle z w).frontier_subset hp)
      fun hpS ↦ hS p hpS hp).continuousAt.continuousWithinAt
  simpa [smul_eq_mul] using
    (integral_rectBoundary hcont).symm.trans
      (classicalResidueTheorem_rectBoundary hre him hf hmero hS)

end TauCeti.Contour
