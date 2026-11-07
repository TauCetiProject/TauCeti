/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import TauCeti.Geometry.Manifold.RegularValue
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Index
import TauCeti.Analysis.Fredholm.SardSmale
import TauCeti.Geometry.Manifold.Meagre

/-!
# The Sard--Smale theorem for Fredholm maps between Banach manifolds

A map `f : M → N` between manifolds modelled on real Banach spaces is a *Fredholm map* when its
manifold derivative `mfderiv I J f x` is a Fredholm operator at every point. This file proves
Smale's theorem for such maps at his sharp regularity, in index at most two: if the derivative at
each point `x` has index `i x ≤ 2` and `f` is `C^k` at `x` with `k > max (i x, 0)`, then the
critical values of `f` form a meagre set, so its regular values form a residual set. More
locally, the image of a Lindelöf set of critical points at which these hypotheses hold is meagre;
for the global statements the source is hereditarily Lindelöf, for instance second countable.
Both manifolds are without boundary and need only be `C¹`. The models need not be
finite-dimensional.

The proof reads `f` near each point `x` in the extended charts at `x` and `f x`. At the chart
image of `x` the Fréchet derivative of the coordinate expression is the manifold derivative of
`f`, so the local Sard--Smale theorem on Banach spaces
(`TauCeti.exists_mem_nhds_isClosed_isNowhereDense_image_criticalPoints_of_index_le_two`) gives a
neighbourhood there on which the critical values are nowhere dense. Within the chart sources the
critical points of `f` are those of its coordinate expression
(`TauCeti.isRegularPoint_iff_surjective_fderiv_extChartAt`). Meagre images in these charts give a
meagre image in `N`, by a countable cover of the Lindelöf set of critical points
(`TauCeti.isMeagre_image_of_forall_isMeagre_image_extChartAt`).

The bound on the index enters only through the finite-dimensional slices of the local argument:
they are maps from a space of dimension `dim ker` to one of dimension `dim coker`, and the sharp
Morse--Sard theorem `TauCeti.interior_image_criticalPoints_eq_empty_of_finrank_le_add_two` applied
to them assumes `dim ker ≤ dim coker + 2`, which is exactly index at most two. This range covers
the moduli spaces of index one and two that are counted by Morse and Floer differentials and their
squares.

## Main results

* `TauCeti.isMeagre_image_of_not_isRegularPoint_of_index_le_two`: the image of a Lindelöf set of
  critical points at which `f` is Fredholm of index at most two and sharply regular is meagre.
* `ContMDiff.isMeagre_image_criticalPoints_of_index_le_two`: the critical values of a sharply
  regular Fredholm map of index at most two are meagre.
* `ContMDiff.mem_residual_setOf_isRegularValue_of_index_le_two`: its regular values form a
  residual set.

## References

* S. Smale, *An infinite dimensional version of Sard's theorem*, Amer. J. Math. 87 (1965),
  861--866, Theorem 1.3.
* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Appendix A.5.
-/

public section

open Function Set Filter
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {n : ℕ∞ω}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [J.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J 1 N]
  {f : M → N} {s : Set M}

/-- **The Sard--Smale theorem on Banach manifolds, at the sharp regularity, in index at most two.**
Let `s` be a set of critical points of `f` at each of which `mfderiv I J f x` is a Fredholm
operator of index `i x ≤ 2` and `f` is `C^k` with `k > max (i x, 0)`. If `s` is Lindelöf, then
`f '' s` is meagre. Both manifolds are without boundary; the regularity is required in the ambient
manifold at the points of `s`. -/
theorem isMeagre_image_of_not_isRegularPoint_of_index_le_two [LindelofSpace s]
    (hf : ∀ x ∈ s, ContMDiffAt I J n f x) (hFred : ∀ x ∈ s, (mfderiv I J f x).IsFredholm)
    (hindex : ∀ x ∈ s, (mfderiv I J f x).index ≤ 2)
    (hn : ∀ x ∈ s, (((mfderiv I J f x).index.toNat + 1 : ℕ) : ℕ∞ω) ≤ n)
    (hs : ∀ x ∈ s, ¬ IsRegularPoint I J f x) : IsMeagre (f '' s) := by
  refine isMeagre_image_of_forall_isMeagre_image_extChartAt (I := I) (J := J)
    (fun x hx ↦ (hf x hx).continuousAt) fun x hx ↦ ?_
  -- The regularity is at least `C¹`, so `f` is differentiable at the points of `s`.
  have hn0 : n ≠ 0 := fun h ↦ by
    have := (hn x hx).trans_eq h
    norm_cast at this
  -- Read `f` in the charts at `x` and `f x`. Its Fréchet derivative at the chart image of `x` is
  -- the manifold derivative, so the local Sard--Smale theorem applies there.
  let g : E → E' := extChartAt J (f x) ∘ f ∘ (extChartAt I x).symm
  have hfd : fderiv ℝ g (extChartAt I x x) = mfderiv I J f x := by
    rw [((hf x hx).mdifferentiableAt hn0).mfderiv_abuse, I.range_eq_univ, fderivWithin_univ,
      writtenInExtChartAt]
  have hg : ContDiffAt ℝ n g (extChartAt I x x) := (hf x hx).contDiffAt_writtenInExtChartAt
  obtain ⟨V, hV, -, -, hVnd⟩ :=
    exists_mem_nhds_isClosed_isNowhereDense_image_criticalPoints_of_index_le_two hg
      (by rw [hfd]; exact hFred x hx) (by rw [hfd]; exact hindex x hx)
      (by rw [hfd]; exact hn x hx) univ_mem
  -- Its pull-back to `M` is a neighbourhood of `x` whose points of `s` in the chart sources are
  -- critical points of `g` in `V`.
  refine ⟨extChartAt I x ⁻¹' V, (continuousAt_extChartAt x).preimage_mem_nhds hV,
    hVnd.isMeagre.mono ?_⟩
  rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
  exact ⟨extChartAt I x z, ⟨hz.1.1.2, (isRegularPoint_iff_surjective_fderiv_extChartAt
    ((hf z hz.1.1.1).mdifferentiableAt hn0) hz.1.2 hz.2).not.mp (hs z hz.1.1.1)⟩, rfl⟩

/-- **The Sard--Smale theorem on Banach manifolds, at the sharp regularity, in index at most two.**
The critical values of a `C^n` Fredholm map whose derivative at each point `x` has index
`i x ≤ 2`, with `n > max (i x, 0)`, form a meagre set. The source is hereditarily Lindelöf, for
instance second countable, and both manifolds are without boundary. -/
theorem _root_.ContMDiff.isMeagre_image_criticalPoints_of_index_le_two
    [HereditarilyLindelofSpace M] (hf : ContMDiff I J n f)
    (hFred : ∀ x, (mfderiv I J f x).IsFredholm) (hindex : ∀ x, (mfderiv I J f x).index ≤ 2)
    (hn : ∀ x, (((mfderiv I J f x).index.toNat + 1 : ℕ) : ℕ∞ω) ≤ n) :
    IsMeagre (f '' {x | ¬ IsRegularPoint I J f x}) :=
  have : LindelofSpace {x | ¬ IsRegularPoint I J f x} :=
    isLindelof_iff_lindelofSpace.1 (HereditarilyLindelofSpace.isLindelof _)
  isMeagre_image_of_not_isRegularPoint_of_index_le_two (fun x _ ↦ hf x) (fun x _ ↦ hFred x)
    (fun x _ ↦ hindex x) (fun x _ ↦ hn x) fun _ hx ↦ hx

/-- The regular values of a `C^n` Fredholm map of index at most two between Banach manifolds, with
`n` greater than the index and positive, form a residual set; in particular they are dense when
the target is a Baire space. The hypotheses are those of
`ContMDiff.isMeagre_image_criticalPoints_of_index_le_two`. -/
theorem _root_.ContMDiff.mem_residual_setOf_isRegularValue_of_index_le_two
    [HereditarilyLindelofSpace M] (hf : ContMDiff I J n f)
    (hFred : ∀ x, (mfderiv I J f x).IsFredholm) (hindex : ∀ x, (mfderiv I J f x).index ≤ 2)
    (hn : ∀ x, (((mfderiv I J f x).index.toNat + 1 : ℕ) : ℕ∞ω) ≤ n) :
    {y | IsRegularValue I J f y} ∈ residual N := by
  rw [setOf_isRegularValue_eq_compl_image]
  exact hf.isMeagre_image_criticalPoints_of_index_le_two hFred hindex hn

end TauCeti

end
