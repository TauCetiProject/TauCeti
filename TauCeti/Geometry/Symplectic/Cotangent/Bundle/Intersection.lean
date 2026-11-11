/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.DegreeOne
public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
import TauCeti.Topology.VectorBundle.ZeroSection

/-!
# Intersections of the zero section with the graph of a differential

A smooth one-form `α` on a manifold `M` is a section `x ↦ α_x` of the cotangent bundle
`T*M = TauCeti.CotangentBundle I M`, and its graph meets the zero section exactly over the zeros of
`α` (`Bundle.range_section_inter_range_zeroSection`). For the differential `df` of a smooth function
`f`, whose value at `x` is the manifold derivative of `f`
(`TauCeti.SmoothForm.degreeOneEquiv_mextDerivₗ`), these zeros are the critical points of `f`
(`TauCeti.criticalPoints`). So the zero section of `T*M` meets the graph of `df` exactly in the
zero covectors over the critical points of `f`
(`TauCeti.CotangentBundle.range_section_mextDerivₗ_inter_range_zeroSection`), and the number of
intersection points, in `ℕ∞`, is the number of critical points of `f`
(`TauCeti.CotangentBundle.encard_range_section_mextDerivₗ_inter_range_zeroSection`).

The zero section and the graph of `df` are both exact Lagrangian maps into `T*M`
(`TauCeti.CotangentBundle.isExactLagrangianMap_zeroSection`,
`TauCeti.CotangentBundle.isExactLagrangianMap_section_iff`), and the graph of `df` is a Hamiltonian
deformation of the zero section. When `M` is compact and boundaryless with at least two points,
`f` attains its maximum and its minimum, both critical, and if these coincide then `f` is constant
and every point is critical. So the graph of `df` meets the zero section in at least two distinct
points (`TauCeti.CotangentBundle.two_le_encard_range_section_mextDerivₗ_inter_range_zeroSection`).

## Main results

* `TauCeti.CotangentBundle.range_section_mextDerivₗ_inter_range_zeroSection`: the graph of `df`
  meets the zero section exactly over the critical points of `f`.
* `TauCeti.CotangentBundle.encard_range_section_mextDerivₗ_inter_range_zeroSection`: the number
  of intersection points is the number of critical points of `f`.
* `TauCeti.CotangentBundle.two_le_encard_range_section_mextDerivₗ_inter_range_zeroSection`: on a
  compact boundaryless manifold with at least two points, the graph of `df` meets the zero section
  in at least two distinct points.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 3 (Lagrangian graphs of closed one-forms and the zero section).
-/

public section

noncomputable section

open Bundle Set
open scoped Manifold ContDiff

namespace TauCeti

namespace CotangentBundle

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 2 M]

/-- **The intersection of the graph of `df` with the zero section.** The graph of the differential
of a smooth function `f` meets the zero section of the cotangent bundle in the zero covectors over
the critical points of `f`. -/
theorem range_section_mextDerivₗ_inter_range_zeroSection (f : SmoothForm I M ℝ 0) :
    range (fun x ↦
        TotalSpace.mk' (E →L[ℝ] ℝ) x (SmoothForm.degreeOneEquiv (mextDerivₗ I 0 f) x)) ∩
        range (zeroSection (E →L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ)) =
      zeroSection (E →L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) ''
        criticalPoints I (fun y ↦ f.1 y 0) := by
  rw [range_section_inter_range_zeroSection]
  simp_rw [SmoothForm.degreeOneEquiv_mextDerivₗ, ← mem_criticalPoints, ofPred_mem_eq]

/-- **Counting the intersections of the graph of `df` with the zero section.** The number of
points in which the graph of the differential of a smooth function `f` meets the zero section of
the cotangent bundle, in `ℕ∞`, is the number of critical points of `f`. -/
theorem encard_range_section_mextDerivₗ_inter_range_zeroSection (f : SmoothForm I M ℝ 0) :
    (range (fun x ↦
        TotalSpace.mk' (E →L[ℝ] ℝ) x (SmoothForm.degreeOneEquiv (mextDerivₗ I 0 f) x)) ∩
        range (zeroSection (E →L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ))).encard =
      totalCriticalCount I (fun y ↦ f.1 y 0) := by
  rw [range_section_mextDerivₗ_inter_range_zeroSection, totalCriticalCount_def,
    (zeroSection_injective _ _).encard_image]

/-- **The graph of `df` meets the zero section twice.** On a compact boundaryless manifold with at
least two points, the graph of the differential of a smooth function `f` meets the zero section of
the cotangent bundle in at least two distinct points: over a maximum and a minimum of `f`, or over
any two points when `f` is constant. -/
theorem two_le_encard_range_section_mextDerivₗ_inter_range_zeroSection [I.Boundaryless]
    [CompactSpace M] [Nontrivial M] (f : SmoothForm I M ℝ 0) :
    2 ≤ (range (fun x ↦
        TotalSpace.mk' (E →L[ℝ] ℝ) x (SmoothForm.degreeOneEquiv (mextDerivₗ I 0 f) x)) ∩
        range (zeroSection (E →L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ))).encard := by
  rw [encard_range_section_mextDerivₗ_inter_range_zeroSection]
  refine two_le_totalCriticalCount ?_
  -- A smooth `0`-form is a smooth function.
  have hf := SmoothForm.isSmoothForm f
  rw [RoughForm.eq_ofFunction f.1, isSmoothForm_ofFunction_iff] at hf
  exact hf.continuous

end CotangentBundle

end TauCeti
