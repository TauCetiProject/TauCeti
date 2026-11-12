/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.DegreeOne
public import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
public import TauCeti.Topology.VectorBundle.ZeroSection

/-!
# Intersections of the zero section with graphs of differentials

A smooth one-form `α` on a manifold `M` is a section `s_α : x ↦ α_x` of the cotangent bundle
`T*M`, whose image is the graph of `α`. Two sections of a bundle meet only over the points where
they agree, so the graph of `α` meets the zero section of `T*M` exactly over the zeros of `α`
(`Bundle.range_mk_inter_range_zeroSection`). For the differential `df` of a smooth function these
zeros are the critical points of `f`
(`TauCeti.CotangentBundle.range_section_mextDerivₗ_inter_range_zeroSection`), and since the zero
section is injective, the number of intersection points, in `ℕ∞`, is the number of critical
points of `f` (`TauCeti.CotangentBundle.encard_range_section_mextDerivₗ_inter_range_zeroSection`).

On a finite-dimensional manifold the zero section and the graph of `df` are both exact Lagrangian
(`TauCeti.CotangentBundle.isExactLagrangianMap_zeroSection`,
`TauCeti.CotangentBundle.isExactLagrangianMap_section_iff`). When `M` is compact, boundaryless
and has at least two points, they meet in at least two distinct points
(`TauCeti.CotangentBundle.two_le_encard_range_section_mextDerivₗ_inter_range_zeroSection`): if `f`
is not constant, over a point of maximum and a different point of minimum, and if `f` is constant,
over every point of `M`. This is the elementary lower bound for the intersections of the zero
section with the graph of an exact one-form. It needs neither finite dimension nor
nondegeneracy of the critical points, and it fails on manifolds with boundary: the graph of
`d(t)` on `[0, 1]` misses the zero section.

## Main results

* `TauCeti.CotangentBundle.range_section_mextDerivₗ_inter_range_zeroSection`: the graph of `df`
  meets the zero section over the critical points of `f`.
* `TauCeti.CotangentBundle.encard_range_section_mextDerivₗ_inter_range_zeroSection`: the number
  of these intersection points is the number of critical points of `f`.
* `TauCeti.CotangentBundle.two_le_encard_range_section_mextDerivₗ_inter_range_zeroSection`: on a
  compact boundaryless manifold with at least two points there are at least two of them.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 3 (Lagrangian graphs of one-forms in cotangent bundles).
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Chapter 9 (the intersections of the graph of `df` with the zero section are the critical points
  of `f`).
-/

public section

noncomputable section

open Bundle Set
open scoped Manifold ContDiff

namespace TauCeti

namespace CotangentBundle

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

variable [IsManifold I 2 M]

/-- **The graph of `df` meets the zero section over the critical points of `f`.** The image of the
section of the cotangent bundle defined by the differential of a smooth function `f` meets the
image of the zero section exactly in the zero covectors over the critical points of `f`. -/
theorem range_section_mextDerivₗ_inter_range_zeroSection (f : SmoothForm I M ℝ 0) :
    range (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) x
          (SmoothForm.degreeOneEquiv (mextDerivₗ I 0 f) x)) ∩
        range (zeroSection (E →L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ)) =
      zeroSection (E →L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) ''
        criticalPoints I (fun y ↦ f.1 y 0) := by
  rw [range_mk_inter_range_zeroSection]
  simp_rw [SmoothForm.degreeOneEquiv_mextDerivₗ, ← mem_criticalPoints, ofPred_mem_eq]

/-- **The graph of `df` meets the zero section once for each critical point of `f`.** The
extended number of intersection points of the graph of the differential of a smooth function `f`
with the zero section of the cotangent bundle is the number of critical points of `f`. -/
theorem encard_range_section_mextDerivₗ_inter_range_zeroSection (f : SmoothForm I M ℝ 0) :
    (range (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) x
          (SmoothForm.degreeOneEquiv (mextDerivₗ I 0 f) x)) ∩
        range (zeroSection (E →L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ))).encard =
      totalCriticalCount I (fun y ↦ f.1 y 0) := by
  rw [range_section_mextDerivₗ_inter_range_zeroSection, totalCriticalCount_def]
  exact (zeroSection_injective _ _).encard_image _

/-- **The graph of `df` meets the zero section at least twice.** On a compact boundaryless
manifold with at least two points, the graph of the differential of a smooth function `f` meets
the zero section of the cotangent bundle in at least two distinct points: over a maximum and a
minimum of `f` when `f` is not constant, and over every point when it is. -/
theorem two_le_encard_range_section_mextDerivₗ_inter_range_zeroSection [I.Boundaryless]
    [CompactSpace M] [Nontrivial M] (f : SmoothForm I M ℝ 0) :
    2 ≤ (range (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) x
          (SmoothForm.degreeOneEquiv (mextDerivₗ I 0 f) x)) ∩
        range (zeroSection (E →L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ))).encard := by
  rw [encard_range_section_mextDerivₗ_inter_range_zeroSection]
  refine two_le_totalCriticalCount (ContMDiff.continuous (I := I) (I' := 𝓘(ℝ)) (n := ∞) ?_)
  -- The function of a smooth `0`-form is smooth.
  rw [← isSmoothForm_ofFunction_iff, ← RoughForm.eq_ofFunction]
  exact f.isSmoothForm

end CotangentBundle

end TauCeti
