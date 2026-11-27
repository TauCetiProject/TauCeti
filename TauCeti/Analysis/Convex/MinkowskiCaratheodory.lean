/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Exposed
public import Mathlib.Analysis.Convex.Intrinsic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
-- Proof-only: Carathéodory's theorem, nontrivial support, rays to the relative frontier, and
-- the dimension drop for convex subsets of the relative frontier.
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import TauCeti.Analysis.Convex.Exposed
import TauCeti.Analysis.Convex.Intrinsic
import TauCeti.Analysis.Convex.Separation

/-!
# The Minkowski–Carathéodory theorem

A compact convex set `K` in a finite-dimensional real normed space is the convex hull of its
extreme points (`IsCompact.convexHull_extremePoints`), and every point of `K` is a convex
combination of at most `dim K + 1` extreme points, where `dim K` is the dimension of the vector
span of `K` (`IsCompact.exists_finset_subset_extremePoints_card_le_mem_convexHull`). In finite
dimension this removes the closure from the Krein–Milman theorem
(`closure_convexHull_extremePoints`).

The proof is an induction on `dim K`. A point `x ∈ K` outside the intrinsic interior of `K` has a
nontrivial supporting functional
(`Convex.exists_strongDual_nontrivial_support_of_notMem_intrinsicInterior`), which exposes a face
of `K` through `x` that is a proper subset, hence of smaller dimension
(`Convex.exists_isExposed_mem_finrank_vectorSpan_lt`); the extreme points of an exposed face are
extreme points of `K`. A point of the intrinsic interior lies on a segment between two points of
the intrinsic frontier, found by following a line through it to the frontier in both directions.
The count then follows from Carathéodory's theorem (`convexHull_eq_union`) and the bound on
affinely independent families inside the vector span of `K`.

## Main results

* `Convex.exists_isExposed_mem_finrank_vectorSpan_lt`: a point of a convex set outside its
  intrinsic interior lies in an exposed face of strictly smaller dimension.
* `IsCompact.convexHull_extremePoints`: a compact convex set in finite dimension is the convex hull
  of its extreme points.
* `IsCompact.exists_finset_subset_extremePoints_card_le_mem_convexHull`: each of its points is in
  the convex hull of at most `dim K + 1` extreme points.

## References

* B. Simon, *Convexity: An Analytic Viewpoint*, Cambridge Tracts in Mathematics 187, 2011,
  Theorem 8.11.
* J.-B. Hiriart-Urruty and C. Lemaréchal, *Convex Analysis and Minimization Algorithms I*,
  Springer, 1993, Chapter III, Theorem 2.3.4.
* J. M. Borwein and A. S. Lewis, *Convex Analysis and Nonlinear Optimization*, second edition,
  Springer, 2006, Theorem 4.1.8.
-/

public section

open Set Module

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- A point `x` of a convex set `C` in a finite-dimensional real normed space which is not in the
intrinsic interior of `C` lies in an exposed face `F` of `C` whose vector span has strictly
smaller dimension than that of `C`. -/
theorem Convex.exists_isExposed_mem_finrank_vectorSpan_lt {C : Set V} (hC : Convex ℝ C) {x : V}
    (hx : x ∈ C) (hxi : x ∉ intrinsicInterior ℝ C) :
    ∃ F, IsExposed ℝ C F ∧ x ∈ F ∧ finrank ℝ (vectorSpan ℝ F) < finrank ℝ (vectorSpan ℝ C) := by
  obtain ⟨l, hle, c, hc, hlt⟩ :=
    hC.exists_strongDual_nontrivial_support_of_notMem_intrinsicInterior hx hxi
  have hF : IsExposed ℝ C (l.toExposed C) := ContinuousLinearMap.toExposed.isExposed
  have hxF : x ∈ l.toExposed C := ⟨hx, hle⟩
  -- the exposed face misses `c`, so it lies in the intrinsic frontier of `C`
  have hne : l.toExposed C ≠ C := fun h => hlt.not_ge ((h.symm ▸ hc : c ∈ l.toExposed C).2 x hx)
  refine ⟨_, hF, hxF, TauCeti.finrank_vectorSpan_lt_of_disjoint_intrinsicInterior (hF.convex hC)
    ⟨x, hxF⟩ hF.subset ?_⟩
  exact Disjoint.mono_left (intrinsicInterior_subset.trans (hF.subset_intrinsicFrontier hne))
    (by rw [← intrinsicClosure_sdiff_intrinsicInterior]; exact disjoint_sdiff_left)

/-- **Minkowski's theorem** (Simon, Theorem 8.11; Hiriart-Urruty–Lemaréchal I, Chapter III,
Theorem 2.3.4; Borwein–Lewis, Theorem 4.1.8). A compact convex set in a finite-dimensional real
normed space is the convex hull of its extreme points; no closure is needed, unlike in the
Krein–Milman theorem `closure_convexHull_extremePoints`. -/
theorem IsCompact.convexHull_extremePoints {K : Set V} (hK : IsCompact K) (hKc : Convex ℝ K) :
    convexHull ℝ (K.extremePoints ℝ) = K := by
  refine (convexHull_min extremePoints_subset hKc).antisymm ?_
  induction hn : finrank ℝ (vectorSpan ℝ K) using Nat.strong_induction_on generalizing K with
  | _ n ih =>
  -- a point outside the intrinsic interior lies in an exposed face of smaller dimension
  have hfront (x : V) (hx : x ∈ K) (hxi : x ∉ intrinsicInterior ℝ K) :
      x ∈ convexHull ℝ (K.extremePoints ℝ) := by
    obtain ⟨F, hF, hxF, hlt⟩ := hKc.exists_isExposed_mem_finrank_vectorSpan_lt hx hxi
    exact convexHull_mono hF.isExtreme.extremePoints_subset_extremePoints
      (ih _ (hn ▸ hlt) (hF.isCompact hK) (hF.convex hKc) rfl hxF)
  have hfr (y : V) (hy : y ∈ intrinsicFrontier ℝ K) : y ∈ K ∧ y ∉ intrinsicInterior ℝ K := by
    rwa [← hK.isClosed.sdiff_intrinsicInterior] at hy
  intro x hx
  by_cases hxi : x ∉ intrinsicInterior ℝ K
  · exact hfront x hx hxi
  push Not at hxi
  by_cases hsing : ∀ p ∈ K, p = x
  · -- `K = {x}`, so `x` is extreme
    exact subset_convexHull ℝ _
      (mem_extremePoints.2 ⟨hx, fun y hy z hz _ => ⟨hsing y hy, hsing z hz⟩⟩)
  · -- an intrinsic interior point lies between two points of the intrinsic frontier
    push Not at hsing
    obtain ⟨p, hp, hpx⟩ := hsing
    obtain ⟨T, -, ha⟩ := hK.exists_lineMap_mem_intrinsicFrontier hp hx hpx.symm
    obtain ⟨haK, hai⟩ := hfr _ ha
    have hxa : x ≠ AffineMap.lineMap p x T := fun h => hai (h ▸ hxi)
    obtain ⟨T', hT', hb⟩ := hK.exists_lineMap_mem_intrinsicFrontier haK hx hxa
    obtain ⟨hbK, hbi⟩ := hfr _ hb
    refine (convex_convexHull ℝ _).segment_subset (hfront _ haK hai) (hfront _ hbK hbi) ?_
    rw [segment_eq_image_lineMap]
    refine ⟨T'⁻¹, ⟨by positivity, inv_le_one_of_one_le₀ hT'⟩, ?_⟩
    rw [AffineMap.lineMap_lineMap_right, inv_mul_cancel₀ (by linarith),
      AffineMap.lineMap_apply_one]

/-- **The Minkowski–Carathéodory theorem** (Simon, Theorem 8.11; Hiriart-Urruty–Lemaréchal I,
Chapter III, Theorem 2.3.4). Every point of a compact convex set `K` in a finite-dimensional real
normed space is in the convex hull of at most `dim K + 1` extreme points of `K`, where `dim K` is
the dimension of the vector span of `K`. -/
theorem IsCompact.exists_finset_subset_extremePoints_card_le_mem_convexHull {K : Set V}
    (hK : IsCompact K) (hKc : Convex ℝ K) {x : V} (hx : x ∈ K) :
    ∃ t : Finset V, (t : Set V) ⊆ K.extremePoints ℝ ∧
      t.card ≤ finrank ℝ (vectorSpan ℝ K) + 1 ∧ x ∈ convexHull ℝ (t : Set V) := by
  rw [← hK.convexHull_extremePoints hKc, convexHull_eq_union] at hx
  simp only [mem_iUnion] at hx
  obtain ⟨t, hts, hti, hxt⟩ := hx
  refine ⟨t, hts, ?_, hxt⟩
  have := hti.card_le_finrank_succ
  rw [Fintype.card_coe, Subtype.range_coe_subtype, Finset.setOfPred_mem] at this
  exact this.trans (Nat.add_le_add_right (Submodule.finrank_mono
    (vectorSpan_mono ℝ (hts.trans extremePoints_subset))) 1)
