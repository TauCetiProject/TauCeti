/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.PlaneSeparation.Inside
public import TauCeti.Analysis.Contour.Cycle.Reverse
public import TauCeti.Analysis.Contour.Cycle.Winding
public import TauCeti.Analysis.Contour.Winding.AbsolutelyContinuous.Jordan
import TauCeti.Analysis.Calculus.ContDiff.PiecewiseC1On.AbsolutelyContinuous
import TauCeti.Topology.JordanCurve.Path

/-!
# Oriented boundary cycles of finitely connected Jordan regions

Let `C₀ ⊆ ℂ` be an outer Jordan curve and let `C i` (`i ∈ s`, `s : Finset ι`) be finitely many
inner Jordan curves whose closed hulls `filledHull (C i)` are pairwise disjoint and lie inside the
bounded interior `filledHull C₀ \ C₀`. Deleting those closed hulls produces the finitely connected
planar Jordan region

`Δ := (filledHull C₀ \ C₀) \ ⋃ i ∈ s, filledHull (C i)`.

This file establishes the topological boundary structure of `Δ` and packages the positively
oriented boundary cycle of any piecewise-`C¹` parametrization `(γ₀, s, γ)` of `(C₀, (C i)_{i ∈ s})`
as an element `TauCeti.Contour.jordanBoundaryCycle γ₀ s γ` of the existing `FreeAbelianGroup`
carrier `TauCeti.Contour.Cycle`.

Each curve `γⱼ` is first oriented counterclockwise via
`PiecewiseC1ClosedCurve.positivelyOrient` (reversing `γⱼ` via `PiecewiseC1ClosedCurve.symm` when
`Contour.jordanSign γⱼ γⱼ.a γⱼ.b = -1`), and the boundary cycle is formed as
`[γ₀⁺] - ∑ i ∈ s, [γᵢ⁺]`. Because the component curves are nonempty and pairwise disjoint, no
generators cancel in `FreeAbelianGroup`, so the geometric trace of the boundary cycle equals
`frontier Δ = C₀ ∪ ⋃ i ∈ s, C i` and its cycle winding number off that trace is `1` on `Δ` and `0`
everywhere else (cancelling `1 - 1 = 0` inside every hole and vanishing outside `filledHull C₀`).

## Main definitions

* `TauCeti.Contour.PiecewiseC1ClosedCurve.positivelyOrient`: orient a closed piecewise-`C¹` curve
  so that its `jordanSign` is `1` when simple.
* `TauCeti.Contour.jordanBoundaryCycle`: the oriented boundary cycle `[γ₀⁺] - ∑ i ∈ s, [γᵢ⁺]` of a
  finitely connected Jordan region.

## Main results

* `TauCeti.IsJordanCurve.isOpen_filledHull_sdiff_biUnion`,
  `isBounded_filledHull_sdiff_biUnion`, `closure_filledHull_sdiff_biUnion`,
  `frontier_filledHull_sdiff_biUnion`: topology of a finitely connected Jordan region `Δ`.
* `TauCeti.Contour.Cycle.trace_jordanBoundaryCycle`: `trace (jordanBoundaryCycle γ₀ s γ) = ∂Δ`.
* `TauCeti.Contour.Cycle.windingNumber_jordanBoundaryCycle` and
  `windingWeight_jordanBoundaryCycle`: off `∂Δ`, the boundary cycle has winding number `1` on `Δ`
  and `0` outside `Δ`, so its trace-zero `windingWeight` is `Δ.indicator 1`.
* `TauCeti.Contour.Cycle.isIn_jordanBoundaryCycle` and `isNullHomologous_jordanBoundaryCycle`: any
  ambient set `Ω` containing `closure Δ` contains the trace of `jordanBoundaryCycle` and makes it
  null-homologous.

## References

* L. Ahlfors, *Complex Analysis*, 3rd ed., McGraw-Hill, 1979, Chapter 4, §2 and §4.
* A. Rainer, *Advanced Complex Analysis*, Proposition 10.1.
-/

public section

noncomputable section

open Bornology Complex Filter MeasureTheory Metric Set
open scoped Interval Topology

namespace TauCeti

/-! ### Topology of finitely connected Jordan regions -/

section JordanRegionTopology

variable {ι : Type*} {C₀ : Set ℂ} {s : Finset ι} {C : ι → Set ℂ}

/-- Since `closure (filledHull (C i) \ C i) = filledHull (C i)` for each Jordan curve `C i`,
deleting the closures of the hole insides is the same as deleting their filled hulls. -/
theorem IsJordanCurve.sdiff_biUnion_closure_filledHull_sdiff (C₀ : Set ℂ)
    (hC : ∀ i ∈ s, IsJordanCurve (C i)) :
    (filledHull C₀ \ C₀) \ (⋃ i ∈ s, closure (filledHull (C i) \ C i)) =
      (filledHull C₀ \ C₀) \ ⋃ i ∈ s, filledHull (C i) := by
  congr 1
  exact iUnion₂_congr fun i hi ↦ (hC i hi).closure_filledHull_sdiff

/-- A finitely connected Jordan region `(filledHull C₀ \ C₀) \ ⋃ i ∈ s, filledHull (C i)` is
open. -/
theorem IsJordanCurve.isOpen_filledHull_sdiff_biUnion (hC₀ : IsJordanCurve C₀)
    (hC : ∀ i ∈ s, IsJordanCurve (C i)) :
    IsOpen ((filledHull C₀ \ C₀) \ ⋃ i ∈ s, filledHull (C i)) := by
  rw [← hC₀.interior_filledHull]
  exact isOpen_interior.sdiff
    (s.finite_toSet.isClosed_biUnion fun i hi ↦ (hC i hi).isClosed.isClosed_filledHull)

/-- A finitely connected Jordan region is bounded. -/
theorem IsJordanCurve.isBounded_filledHull_sdiff_biUnion (hC₀ : IsJordanCurve C₀)
    (s : Finset ι) (C : ι → Set ℂ) :
    IsBounded ((filledHull C₀ \ C₀) \ ⋃ i ∈ s, filledHull (C i)) :=
  (isBounded_filledHull.mpr hC₀.isCompact.isBounded).subset (sdiff_subset.trans sdiff_subset)

private theorem subset_closure_filledHull_sdiff_biUnion_of_mem_outer
    (hC₀ : IsJordanCurve C₀) (hC : ∀ i ∈ s, IsJordanCurve (C i))
    (hsub : ∀ i ∈ s, filledHull (C i) ⊆ filledHull C₀ \ C₀) {z : ℂ} (hz : z ∈ C₀) :
    z ∈ closure ((filledHull C₀ \ C₀) \ ⋃ i ∈ s, filledHull (C i)) := by
  have hK : IsClosed (⋃ i ∈ s, filledHull (C i)) :=
    s.finite_toSet.isClosed_biUnion fun i hi ↦ (hC i hi).isClosed.isClosed_filledHull
  have hzK : z ∉ ⋃ i ∈ s, filledHull (C i) :=
    fun hmem ↦ (iUnion₂_subset hsub hmem).2 hz
  have hzcl : z ∈ closure (filledHull C₀ \ C₀) := by
    rw [hC₀.closure_filledHull_sdiff]
    exact subset_filledHull hz
  rw [_root_.mem_closure_iff] at hzcl ⊢
  intro O hO hzO
  obtain ⟨w, ⟨hwO, hwK⟩, hwU⟩ :=
    hzcl (O ∩ (⋃ i ∈ s, filledHull (C i))ᶜ) (hO.inter hK.isOpen_compl) ⟨hzO, hzK⟩
  exact ⟨w, hwO, hwU, hwK⟩

private theorem subset_closure_filledHull_sdiff_biUnion_of_mem_hole
    (hC₀ : IsJordanCurve C₀) (hC : ∀ i ∈ s, IsJordanCurve (C i))
    (hsub : ∀ i ∈ s, filledHull (C i) ⊆ filledHull C₀ \ C₀)
    (hdisj : (s : Set ι).PairwiseDisjoint fun i ↦ filledHull (C i))
    {i : ι} (hi : i ∈ s) {z : ℂ} (hz : z ∈ C i) :
    z ∈ closure ((filledHull C₀ \ C₀) \ ⋃ j ∈ s, filledHull (C j)) := by
  classical
  have hU₀ : IsOpen (filledHull C₀ \ C₀) := by
    rw [← hC₀.interior_filledHull]
    exact isOpen_interior
  have hK' : IsClosed (⋃ j ∈ s.erase i, filledHull (C j)) :=
    (s.erase i).finite_toSet.isClosed_biUnion fun j hj ↦
      (hC j (Finset.mem_of_mem_erase hj)).isClosed.isClosed_filledHull
  have hzU₀ : z ∈ filledHull C₀ \ C₀ := hsub i hi (subset_filledHull hz)
  have hzK' : z ∉ ⋃ j ∈ s.erase i, filledHull (C j) := by
    rw [mem_iUnion₂]
    rintro ⟨j, hj, hzj⟩
    exact Set.disjoint_left.mp
      (hdisj hi (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj).symm)
      (subset_filledHull hz) hzj
  have hzcl : z ∈ closure (filledHull (C i))ᶜ := by
    have hf : z ∈ frontier (filledHull (C i))ᶜ := by
      rw [frontier_compl, (hC i hi).frontier_filledHull]
      exact hz
    exact hf.1
  rw [_root_.mem_closure_iff] at hzcl ⊢
  intro O hO hzO
  obtain ⟨w, ⟨⟨hwO, hwU₀⟩, hwK'⟩, hwi⟩ :=
    hzcl (O ∩ (filledHull C₀ \ C₀) ∩ (⋃ j ∈ s.erase i, filledHull (C j))ᶜ)
      ((hO.inter hU₀).inter hK'.isOpen_compl) ⟨⟨hzO, hzU₀⟩, hzK'⟩
  refine ⟨w, hwO, hwU₀, ?_⟩
  rw [mem_iUnion₂]
  rintro ⟨j, hj, hzj⟩
  by_cases hji : j = i
  · exact hwi (hji ▸ hzj)
  · exact hwK' (mem_iUnion₂.mpr ⟨j, Finset.mem_erase.mpr ⟨hji, hj⟩, hzj⟩)

/-- The closure of `(filledHull C₀ \ C₀) \ ⋃ i ∈ s, filledHull (C i)` is `filledHull C₀` minus the
open hole interiors `filledHull (C i) \ C i`. -/
theorem IsJordanCurve.closure_filledHull_sdiff_biUnion (hC₀ : IsJordanCurve C₀)
    (hC : ∀ i ∈ s, IsJordanCurve (C i))
    (hsub : ∀ i ∈ s, filledHull (C i) ⊆ filledHull C₀ \ C₀)
    (hdisj : (s : Set ι).PairwiseDisjoint fun i ↦ filledHull (C i)) :
    closure ((filledHull C₀ \ C₀) \ ⋃ i ∈ s, filledHull (C i)) =
      filledHull C₀ \ ⋃ i ∈ s, (filledHull (C i) \ C i) := by
  refine Subset.antisymm ?_ ?_
  · refine subset_sdiff.mpr ⟨?_, ?_⟩
    · exact closure_minimal (sdiff_subset.trans sdiff_subset) hC₀.isClosed.isClosed_filledHull
    · rw [Set.disjoint_iUnion₂_right]
      intro i hi
      have hopen : IsOpen (filledHull (C i) \ C i) := by
        rw [← (hC i hi).interior_filledHull]
        exact isOpen_interior
      exact Disjoint.closure_left
        (Set.disjoint_left.mpr fun z hz hzi ↦ hz.2 (mem_iUnion₂.mpr ⟨i, hi, hzi.1⟩)) hopen
  · intro z ⟨hz₀, hzh⟩
    by_cases hzC₀ : z ∈ C₀
    · exact subset_closure_filledHull_sdiff_biUnion_of_mem_outer hC₀ hC hsub hzC₀
    · by_cases hzK : z ∈ ⋃ i ∈ s, filledHull (C i)
      · obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp hzK
        have hzCi : z ∈ C i := by
          by_contra hzCi
          exact hzh (mem_iUnion₂.mpr ⟨i, hi, hzi, hzCi⟩)
        exact subset_closure_filledHull_sdiff_biUnion_of_mem_hole hC₀ hC hsub hdisj hi hzCi
      · exact subset_closure ⟨⟨hz₀, hzC₀⟩, hzK⟩

/-- **Frontier of a finitely connected Jordan region.** The frontier of
`(filledHull C₀ \ C₀) \ ⋃ i ∈ s, filledHull (C i)` is the union `C₀ ∪ ⋃ i ∈ s, C i` of the outer
and inner Jordan curves. -/
theorem IsJordanCurve.frontier_filledHull_sdiff_biUnion (hC₀ : IsJordanCurve C₀)
    (hC : ∀ i ∈ s, IsJordanCurve (C i))
    (hsub : ∀ i ∈ s, filledHull (C i) ⊆ filledHull C₀ \ C₀)
    (hdisj : (s : Set ι).PairwiseDisjoint fun i ↦ filledHull (C i)) :
    frontier ((filledHull C₀ \ C₀) \ ⋃ i ∈ s, filledHull (C i)) = C₀ ∪ ⋃ i ∈ s, C i := by
  rw [frontier, (hC₀.isOpen_filledHull_sdiff_biUnion hC).interior_eq,
    hC₀.closure_filledHull_sdiff_biUnion hC hsub hdisj]
  ext z
  constructor
  · rintro ⟨⟨hz₀, hzh⟩, hzΔ⟩
    by_cases hzC₀ : z ∈ C₀
    · exact Or.inl hzC₀
    · refine Or.inr (mem_iUnion₂.mpr ?_)
      have hzK : z ∈ ⋃ i ∈ s, filledHull (C i) := by
        by_contra hzK
        exact hzΔ ⟨⟨hz₀, hzC₀⟩, hzK⟩
      obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp hzK
      refine ⟨i, hi, ?_⟩
      by_contra hzCi
      exact hzh (mem_iUnion₂.mpr ⟨i, hi, hzi, hzCi⟩)
  · rintro (hzC₀ | hzCi)
    · refine ⟨⟨subset_filledHull hzC₀, ?_⟩, fun h ↦ h.1.2 hzC₀⟩
      rw [mem_iUnion₂]
      rintro ⟨i, hi, hzi, -⟩
      exact (hsub i hi hzi).2 hzC₀
    · obtain ⟨i, hi, hzCi⟩ := mem_iUnion₂.mp hzCi
      refine ⟨⟨(hsub i hi (subset_filledHull hzCi)).1, ?_⟩,
        fun h ↦ h.2 (mem_iUnion₂.mpr ⟨i, hi, subset_filledHull hzCi⟩)⟩
      rw [mem_iUnion₂]
      rintro ⟨j, hj, hzj, hzjC⟩
      by_cases hji : j = i
      · exact hzjC (hji ▸ hzCi)
      · exact Set.disjoint_left.mp (hdisj hi hj (Ne.symm hji)) (subset_filledHull hzCi) hzj

end JordanRegionTopology

end TauCeti

namespace TauCeti.Contour

/-! ### Positive orientation of a closed piecewise-`C¹` curve -/

namespace PiecewiseC1ClosedCurve

/-- Orient a closed piecewise-`C¹` curve positively: keep `γ` if `jordanSign γ γ.a γ.b = 1`, and
reverse it via `γ.symm` otherwise. For a simple closed curve (`γ.a < γ.b`,
`InjOn γ (Ico γ.a γ.b)`), `positivelyOrient γ` always has orientation sign `1`. -/
def positivelyOrient (γ : PiecewiseC1ClosedCurve) : PiecewiseC1ClosedCurve :=
  if jordanSign γ γ.a γ.b = 1 then γ else γ.symm

/-- Defining formula for `PiecewiseC1ClosedCurve.positivelyOrient`. -/
theorem positivelyOrient_def (γ : PiecewiseC1ClosedCurve) :
    γ.positivelyOrient = if jordanSign γ γ.a γ.b = 1 then γ else γ.symm :=
  (rfl)

/-- A curve that already has `jordanSign = 1` is unchanged by `positivelyOrient`. -/
@[simp]
theorem positivelyOrient_of_jordanSign_eq_one {γ : PiecewiseC1ClosedCurve}
    (h : jordanSign γ γ.a γ.b = 1) : γ.positivelyOrient = γ := by
  rw [positivelyOrient_def, ite_eq_left h]

/-- A curve with `jordanSign ≠ 1` is reversed by `positivelyOrient`. -/
theorem positivelyOrient_of_jordanSign_ne_one {γ : PiecewiseC1ClosedCurve}
    (h : jordanSign γ γ.a γ.b ≠ 1) : γ.positivelyOrient = γ.symm := by
  rw [positivelyOrient_def, ite_eq_right h]

/-- `positivelyOrient` leaves the canonical extension to `ℝ` unchanged. -/
@[simp]
theorem coe_positivelyOrient (γ : PiecewiseC1ClosedCurve) :
    (γ.positivelyOrient : ℝ → ℂ) = γ := by
  by_cases h : jordanSign γ γ.a γ.b = 1
  · rw [positivelyOrient_of_jordanSign_eq_one h]
  · rw [positivelyOrient_of_jordanSign_ne_one h, coe_symm]

/-- `positivelyOrient` leaves the interval image unchanged. -/
theorem image_positivelyOrient (γ : PiecewiseC1ClosedCurve) :
    γ.positivelyOrient '' uIcc γ.positivelyOrient.a γ.positivelyOrient.b =
      γ '' uIcc γ.a γ.b := by
  by_cases h : jordanSign γ γ.a γ.b = 1
  · rw [positivelyOrient_of_jordanSign_eq_one h]
  · rw [positivelyOrient_of_jordanSign_ne_one h, γ.image_symm]

/-- A simple closed piecewise-`C¹` curve on `[γ.a, γ.b]` (`γ.a < γ.b`) traces a planar Jordan
curve. -/
theorem isJordanCurve_image {γ : PiecewiseC1ClosedCurve} (hab : γ.a < γ.b)
    (hinj : InjOn γ (Ico γ.a γ.b)) : TauCeti.IsJordanCurve (γ '' uIcc γ.a γ.b) := by
  have heq : (γ : ℝ → ℂ) '' uIcc γ.a γ.b = (γ : ℝ → ℂ) '' Icc γ.a γ.b :=
    congrArg ((γ : ℝ → ℂ) '' ·) (uIcc_of_le hab.le)
  have hcont : ContinuousOn (γ : ℝ → ℂ) (Icc γ.a γ.b) := by
    have hu := uIcc_of_le hab.le
    exact hu ▸ γ.continuousOn
  rw [heq]
  exact TauCeti.isJordanCurve_image_Icc hab hcont γ.source_eq_target hinj

/-- The orientation sign of a simple closed piecewise-`C¹` curve (`γ.a < γ.b`) is `1` or `-1`. -/
theorem jordanSign_eq_one_or_neg_one {γ : PiecewiseC1ClosedCurve} (hab : γ.a < γ.b)
    (hinj : InjOn γ (Ico γ.a γ.b)) :
    jordanSign γ γ.a γ.b = 1 ∨ jordanSign γ γ.a γ.b = -1 :=
  γ.isPiecewiseC1On.absolutelyContinuousOnInterval.jordanSign_eq_one_or_neg_one
    hab γ.source_eq_target hinj

/-- After `positivelyOrient`, every simple closed piecewise-`C¹` curve (`γ.a < γ.b`) has
`jordanSign` equal to `1`. -/
theorem jordanSign_positivelyOrient {γ : PiecewiseC1ClosedCurve} (hab : γ.a < γ.b)
    (hinj : InjOn γ (Ico γ.a γ.b)) :
    jordanSign γ.positivelyOrient γ.positivelyOrient.a γ.positivelyOrient.b = 1 := by
  rcases γ.jordanSign_eq_one_or_neg_one hab hinj with h | h
  · rw [positivelyOrient_of_jordanSign_eq_one h]
    exact h
  · rw [positivelyOrient_of_jordanSign_ne_one (by omega)]
    have hs : jordanSign (γ.symm : ℝ → ℂ) γ.symm.a γ.symm.b = jordanSign γ γ.b γ.a := by
      rw [coe_symm, symm_a, symm_b]
    rw [hs, γ.isPiecewiseC1On.absolutelyContinuousOnInterval.jordanSign_symm, h]
    rfl

end PiecewiseC1ClosedCurve

namespace Cycle

/-- `positivelyOrient` preserves the cycle trace of a generator. -/
theorem trace_of_positivelyOrient (γ : PiecewiseC1ClosedCurve) :
    trace (FreeAbelianGroup.of γ.positivelyOrient) = trace (FreeAbelianGroup.of γ) := by
  rw [trace_of, trace_of]
  exact γ.image_positivelyOrient

/-- `positivelyOrient` preserves containment of a generator in any target set. -/
theorem isIn_of_positivelyOrient_iff {γ : PiecewiseC1ClosedCurve} {Ω : Set ℂ} :
    IsIn (FreeAbelianGroup.of γ.positivelyOrient) Ω ↔ IsIn (FreeAbelianGroup.of γ) Ω := by
  rw [isIn_iff, isIn_iff, trace_of_positivelyOrient]

/-- `positivelyOrient` preserves vanishing of a generator's cycle winding number. -/
theorem windingNumber_of_positivelyOrient_eq_zero_iff (γ : PiecewiseC1ClosedCurve) (z : ℂ) :
    windingNumber z (FreeAbelianGroup.of γ.positivelyOrient) = 0 ↔
      windingNumber z (FreeAbelianGroup.of γ) = 0 := by
  by_cases h : jordanSign γ γ.a γ.b = 1
  · rw [PiecewiseC1ClosedCurve.positivelyOrient_of_jordanSign_eq_one h]
  · rw [PiecewiseC1ClosedCurve.positivelyOrient_of_jordanSign_ne_one h,
      windingNumber_of_symm_eq_zero_iff]

/-- `positivelyOrient` preserves null-homology of a generator. -/
theorem isNullHomologous_of_positivelyOrient_iff {γ : PiecewiseC1ClosedCurve} {Ω : Set ℂ} :
    IsNullHomologous (FreeAbelianGroup.of γ.positivelyOrient) Ω ↔
      IsNullHomologous (FreeAbelianGroup.of γ) Ω := by
  simp only [isNullHomologous_iff, windingNumber_of_positivelyOrient_eq_zero_iff]

/-- Outside `filledHull (γ '' uIcc γ.a γ.b)`, the cycle winding number of `γ.positivelyOrient`
vanishes. -/
theorem windingNumber_of_positivelyOrient_eq_zero_of_notMem_filledHull
    (γ : PiecewiseC1ClosedCurve) {z : ℂ} (hz : z ∉ filledHull (γ '' uIcc γ.a γ.b)) :
    windingNumber z (FreeAbelianGroup.of γ.positivelyOrient) = 0 := by
  rw [windingNumber_of_positivelyOrient_eq_zero_iff, windingNumber_of]
  exact γ.isPiecewiseC1On.absolutelyContinuousOnInterval.windingNumber_eq_zero_of_notMem_filledHull
    γ.source_eq_target hz

/-- For a simple closed piecewise-`C¹` curve (`γ.a < γ.b`), integrating over `γ.positivelyOrient`
multiplies the integral over `γ` by `jordanSign γ γ.a γ.b ∈ {1, -1}`. -/
theorem integral_of_positivelyOrient {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {γ : PiecewiseC1ClosedCurve} (hab : γ.a < γ.b) (hinj : InjOn γ (Ico γ.a γ.b))
    (f : ℂ → E) :
    integral f (FreeAbelianGroup.of γ.positivelyOrient) =
      jordanSign γ γ.a γ.b • integral f (FreeAbelianGroup.of γ) := by
  rcases γ.jordanSign_eq_one_or_neg_one hab hinj with h | h
  · rw [PiecewiseC1ClosedCurve.positivelyOrient_of_jordanSign_eq_one h, h, one_smul]
  · rw [PiecewiseC1ClosedCurve.positivelyOrient_of_jordanSign_ne_one (by omega),
      integral_of_symm, h, neg_one_smul]

/-- Inside `filledHull (γ '' uIcc γ.a γ.b) \ (γ '' uIcc γ.a γ.b)`, a positively oriented simple
closed piecewise-`C¹` curve (`γ.a < γ.b`) has cycle winding number `1`. -/
theorem windingNumber_of_positivelyOrient_of_mem_filledHull_sdiff
    {γ : PiecewiseC1ClosedCurve} (hab : γ.a < γ.b) (hinj : InjOn γ (Ico γ.a γ.b)) {z : ℂ}
    (hz : z ∈ filledHull (γ '' uIcc γ.a γ.b) \ (γ '' uIcc γ.a γ.b)) :
    windingNumber z (FreeAbelianGroup.of γ.positivelyOrient) = 1 := by
  have hw := γ.isPiecewiseC1On.absolutelyContinuousOnInterval
    |>.windingNumber_eq_jordanSign_of_mem_filledHull_sdiff hab γ.source_eq_target hinj hz
  rcases γ.jordanSign_eq_one_or_neg_one hab hinj with h | h
  · rw [PiecewiseC1ClosedCurve.positivelyOrient_of_jordanSign_eq_one h, windingNumber_of, hw, h,
      Int.cast_one]
  · rw [PiecewiseC1ClosedCurve.positivelyOrient_of_jordanSign_ne_one (by omega),
      windingNumber_of_symm γ hz.2, windingNumber_of, hw, h, Int.cast_neg, Int.cast_one, neg_neg]

end Cycle

/-! ### The oriented boundary cycle of a finitely connected Jordan region -/

section JordanBoundaryCycle

variable {ι : Type*}

/-- **Oriented boundary cycle of a finitely connected Jordan region.** Given an outer closed
piecewise-`C¹` curve `γ₀` and a finite family `(γ i)_{i ∈ s}` of hole curves, each curve is
positively oriented via `PiecewiseC1ClosedCurve.positivelyOrient` and assembled into the formal sum
`[γ₀⁺] - ∑ i ∈ s, [γᵢ⁺]` in `TauCeti.Contour.Cycle`. -/
def jordanBoundaryCycle (γ₀ : PiecewiseC1ClosedCurve) (s : Finset ι)
    (γ : ι → PiecewiseC1ClosedCurve) : Cycle :=
  FreeAbelianGroup.of γ₀.positivelyOrient - ∑ i ∈ s, FreeAbelianGroup.of (γ i).positivelyOrient

/-- Defining formula for `TauCeti.Contour.jordanBoundaryCycle`. -/
theorem jordanBoundaryCycle_def (γ₀ : PiecewiseC1ClosedCurve) (s : Finset ι)
    (γ : ι → PiecewiseC1ClosedCurve) :
    jordanBoundaryCycle γ₀ s γ =
      FreeAbelianGroup.of γ₀.positivelyOrient -
        ∑ i ∈ s, FreeAbelianGroup.of (γ i).positivelyOrient :=
  (rfl)

/-- With no holes (`s = ∅`), `jordanBoundaryCycle` is `[γ₀⁺]`. -/
@[simp]
theorem jordanBoundaryCycle_empty (γ₀ : PiecewiseC1ClosedCurve)
    (γ : ι → PiecewiseC1ClosedCurve) :
    jordanBoundaryCycle γ₀ ∅ γ = FreeAbelianGroup.of γ₀.positivelyOrient := by
  simp [jordanBoundaryCycle]

/-- Inserting a new hole subtracts its positively oriented generator from `jordanBoundaryCycle`. -/
theorem jordanBoundaryCycle_insert [DecidableEq ι] (γ₀ : PiecewiseC1ClosedCurve) {i : ι}
    {s : Finset ι} (hi : i ∉ s) (γ : ι → PiecewiseC1ClosedCurve) :
    jordanBoundaryCycle γ₀ (insert i s) γ =
      jordanBoundaryCycle γ₀ s γ - FreeAbelianGroup.of (γ i).positivelyOrient := by
  rw [jordanBoundaryCycle, jordanBoundaryCycle, Finset.sum_insert hi, sub_sub, add_comm]

/-- When `γ₀` and every `γ i` (`i ∈ s`) already have `jordanSign = 1`, `jordanBoundaryCycle` is
simply `[γ₀] - ∑ i ∈ s, [γ i]`. -/
theorem jordanBoundaryCycle_of_jordanSign_eq_one {γ₀ : PiecewiseC1ClosedCurve} {s : Finset ι}
    {γ : ι → PiecewiseC1ClosedCurve} (h₀ : jordanSign γ₀ γ₀.a γ₀.b = 1)
    (h : ∀ i ∈ s, jordanSign (γ i) (γ i).a (γ i).b = 1) :
    jordanBoundaryCycle γ₀ s γ =
      FreeAbelianGroup.of γ₀ - ∑ i ∈ s, FreeAbelianGroup.of (γ i) := by
  rw [jordanBoundaryCycle, PiecewiseC1ClosedCurve.positivelyOrient_of_jordanSign_eq_one h₀]
  congr 1
  exact Finset.sum_congr rfl fun i hi ↦ by
    rw [PiecewiseC1ClosedCurve.positivelyOrient_of_jordanSign_eq_one (h i hi)]

namespace Cycle

/-- Integrating over `jordanBoundaryCycle γ₀ s γ` combines the `jordanSign`-weighted contour
integrals of `γ₀` and of the hole curves `γ i` (`i ∈ s`). -/
theorem integral_jordanBoundaryCycle {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {γ₀ : PiecewiseC1ClosedCurve} {s : Finset ι} {γ : ι → PiecewiseC1ClosedCurve}
    (hab₀ : γ₀.a < γ₀.b) (hinj₀ : InjOn γ₀ (Ico γ₀.a γ₀.b))
    (hab : ∀ i ∈ s, (γ i).a < (γ i).b)
    (hinj : ∀ i ∈ s, InjOn (γ i) (Ico (γ i).a (γ i).b)) (f : ℂ → E) :
    integral f (jordanBoundaryCycle γ₀ s γ) =
      jordanSign γ₀ γ₀.a γ₀.b • integral f (FreeAbelianGroup.of γ₀) -
        ∑ i ∈ s, jordanSign (γ i) (γ i).a (γ i).b • integral f (FreeAbelianGroup.of (γ i)) := by
  rw [jordanBoundaryCycle, map_sub, map_sum, integral_of_positivelyOrient hab₀ hinj₀]
  congr 1
  exact Finset.sum_congr rfl fun i hi ↦ integral_of_positivelyOrient (hab i hi) (hinj i hi) f

private theorem ne_positivelyOrient_outer_of_hole {γ₀ : PiecewiseC1ClosedCurve} {s : Finset ι}
    {γ : ι → PiecewiseC1ClosedCurve} (hab : ∀ i ∈ s, (γ i).a < (γ i).b)
    (hinj : ∀ i ∈ s, InjOn (γ i) (Ico (γ i).a (γ i).b))
    (hsub : ∀ i ∈ s,
      filledHull (γ i '' uIcc (γ i).a (γ i).b) ⊆
        filledHull (γ₀ '' uIcc γ₀.a γ₀.b) \ (γ₀ '' uIcc γ₀.a γ₀.b))
    {i : ι} (hi : i ∈ s) :
    γ₀.positivelyOrient ≠ (γ i).positivelyOrient := by
  intro heq
  obtain ⟨z, hz⟩ := ((γ i).isJordanCurve_image (hab i hi) (hinj i hi)).nonempty
  have hz₀ : z ∈ γ₀ '' uIcc γ₀.a γ₀.b := by
    rw [← trace_of, ← trace_of_positivelyOrient, heq, trace_of_positivelyOrient, trace_of]
    exact hz
  exact (hsub i hi (subset_filledHull hz)).2 hz₀

private theorem ne_positivelyOrient_hole_of_ne {s : Finset ι} {γ : ι → PiecewiseC1ClosedCurve}
    (hab : ∀ i ∈ s, (γ i).a < (γ i).b)
    (hinj : ∀ i ∈ s, InjOn (γ i) (Ico (γ i).a (γ i).b))
    (hdisj : (s : Set ι).PairwiseDisjoint fun i ↦ filledHull (γ i '' uIcc (γ i).a (γ i).b))
    {i j : ι} (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j) :
    (γ i).positivelyOrient ≠ (γ j).positivelyOrient := by
  intro heq
  obtain ⟨z, hz⟩ := ((γ i).isJordanCurve_image (hab i hi) (hinj i hi)).nonempty
  have hzj : z ∈ γ j '' uIcc (γ j).a (γ j).b := by
    rw [← trace_of, ← trace_of_positivelyOrient, ← heq, trace_of_positivelyOrient, trace_of]
    exact hz
  exact Set.disjoint_left.mp (hdisj hi hj hij) (subset_filledHull hz) (subset_filledHull hzj)

/-- The trace of `jordanBoundaryCycle γ₀ s γ` is the union of the outer curve and the hole
curves. -/
theorem trace_jordanBoundaryCycle_eq_union {γ₀ : PiecewiseC1ClosedCurve} {s : Finset ι}
    {γ : ι → PiecewiseC1ClosedCurve}
    (hab : ∀ i ∈ s, (γ i).a < (γ i).b)
    (hinj : ∀ i ∈ s, InjOn (γ i) (Ico (γ i).a (γ i).b))
    (hsub : ∀ i ∈ s,
      filledHull (γ i '' uIcc (γ i).a (γ i).b) ⊆
        filledHull (γ₀ '' uIcc γ₀.a γ₀.b) \ (γ₀ '' uIcc γ₀.a γ₀.b))
    (hdisj : (s : Set ι).PairwiseDisjoint fun i ↦ filledHull (γ i '' uIcc (γ i).a (γ i).b)) :
    trace (jordanBoundaryCycle γ₀ s γ) =
      (γ₀ '' uIcc γ₀.a γ₀.b) ∪ ⋃ i ∈ s, γ i '' uIcc (γ i).a (γ i).b := by
  refine Subset.antisymm ?_ ?_
  · rw [jordanBoundaryCycle, sub_eq_add_neg]
    refine (trace_add_subset _ _).trans (union_subset_union ?_ ?_)
    · rw [trace_of_positivelyOrient, trace_of]
    · rw [trace_neg]
      refine (trace_sum_subset s _).trans (iUnion₂_mono fun i _ ↦ ?_)
      rw [trace_of_positivelyOrient, trace_of]
  · rintro z (hz₀ | hzi)
    · rw [mem_trace_iff]
      refine ⟨γ₀.positivelyOrient, ?_, by rwa [γ₀.image_positivelyOrient]⟩
      rw [FreeAbelianGroup.mem_support_iff, jordanBoundaryCycle, map_sub, map_sum,
        FreeAbelianGroup.coeff_of_self, Finset.sum_eq_zero fun i hi ↦
          FreeAbelianGroup.coeff_of_of_ne (ne_positivelyOrient_outer_of_hole hab hinj hsub hi),
        sub_zero]
      exact one_ne_zero
    · obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp hzi
      rw [mem_trace_iff]
      refine ⟨(γ i).positivelyOrient, ?_, by rwa [(γ i).image_positivelyOrient]⟩
      rw [FreeAbelianGroup.mem_support_iff, jordanBoundaryCycle, map_sub, map_sum,
        FreeAbelianGroup.coeff_of_of_ne
          (ne_positivelyOrient_outer_of_hole hab hinj hsub hi).symm,
        Finset.sum_eq_single i
          (fun j hj hji ↦ FreeAbelianGroup.coeff_of_of_ne
            (ne_positivelyOrient_hole_of_ne hab hinj hdisj hi hj hji.symm))
          (fun hnot ↦ (hnot hi).elim),
        FreeAbelianGroup.coeff_of_self, zero_sub]
      exact neg_ne_zero.mpr one_ne_zero

/-- **Trace identification for `jordanBoundaryCycle`.** The trace of the oriented boundary cycle of
a finitely connected Jordan region `Δ` equals `frontier Δ`. -/
theorem trace_jordanBoundaryCycle {γ₀ : PiecewiseC1ClosedCurve} {s : Finset ι}
    {γ : ι → PiecewiseC1ClosedCurve}
    (hab₀ : γ₀.a < γ₀.b) (hinj₀ : InjOn γ₀ (Ico γ₀.a γ₀.b))
    (hab : ∀ i ∈ s, (γ i).a < (γ i).b)
    (hinj : ∀ i ∈ s, InjOn (γ i) (Ico (γ i).a (γ i).b))
    (hsub : ∀ i ∈ s,
      filledHull (γ i '' uIcc (γ i).a (γ i).b) ⊆
        filledHull (γ₀ '' uIcc γ₀.a γ₀.b) \ (γ₀ '' uIcc γ₀.a γ₀.b))
    (hdisj : (s : Set ι).PairwiseDisjoint fun i ↦ filledHull (γ i '' uIcc (γ i).a (γ i).b)) :
    trace (jordanBoundaryCycle γ₀ s γ) =
      frontier ((filledHull (γ₀ '' uIcc γ₀.a γ₀.b) \ (γ₀ '' uIcc γ₀.a γ₀.b)) \
        ⋃ i ∈ s, filledHull (γ i '' uIcc (γ i).a (γ i).b)) := by
  rw [trace_jordanBoundaryCycle_eq_union hab hinj hsub hdisj,
    (γ₀.isJordanCurve_image hab₀ hinj₀).frontier_filledHull_sdiff_biUnion
      (fun i hi ↦ (γ i).isJordanCurve_image (hab i hi) (hinj i hi)) hsub hdisj]

open scoped Classical in
/-- **Winding-number adapter for `jordanBoundaryCycle`.** Off its trace `frontier Δ`, the oriented
boundary cycle of a finitely connected Jordan region `Δ` has winding number `1` on `Δ` and `0`
everywhere else. -/
theorem windingNumber_jordanBoundaryCycle {γ₀ : PiecewiseC1ClosedCurve} {s : Finset ι}
    {γ : ι → PiecewiseC1ClosedCurve}
    (hab₀ : γ₀.a < γ₀.b) (hinj₀ : InjOn γ₀ (Ico γ₀.a γ₀.b))
    (hab : ∀ i ∈ s, (γ i).a < (γ i).b)
    (hinj : ∀ i ∈ s, InjOn (γ i) (Ico (γ i).a (γ i).b))
    (hsub : ∀ i ∈ s,
      filledHull (γ i '' uIcc (γ i).a (γ i).b) ⊆
        filledHull (γ₀ '' uIcc γ₀.a γ₀.b) \ (γ₀ '' uIcc γ₀.a γ₀.b))
    (hdisj : (s : Set ι).PairwiseDisjoint fun i ↦ filledHull (γ i '' uIcc (γ i).a (γ i).b))
    {z : ℂ} (hz : z ∉ trace (jordanBoundaryCycle γ₀ s γ)) :
    windingNumber z (jordanBoundaryCycle γ₀ s γ) =
      if z ∈ (filledHull (γ₀ '' uIcc γ₀.a γ₀.b) \ (γ₀ '' uIcc γ₀.a γ₀.b)) \
          ⋃ i ∈ s, filledHull (γ i '' uIcc (γ i).a (γ i).b) then 1 else 0 := by
  rw [trace_jordanBoundaryCycle_eq_union hab hinj hsub hdisj] at hz
  have hz₀ : z ∉ γ₀ '' uIcc γ₀.a γ₀.b := fun h ↦ hz (Or.inl h)
  have hzi : ∀ i ∈ s, z ∉ γ i '' uIcc (γ i).a (γ i).b :=
    fun i hi h ↦ hz (Or.inr (mem_iUnion₂.mpr ⟨i, hi, h⟩))
  rw [jordanBoundaryCycle, map_sub, map_sum]
  split_ifs with hzΔ
  · rw [windingNumber_of_positivelyOrient_of_mem_filledHull_sdiff hab₀ hinj₀ hzΔ.1,
      Finset.sum_eq_zero fun i hi ↦
        windingNumber_of_positivelyOrient_eq_zero_of_notMem_filledHull (γ i)
          (fun h ↦ hzΔ.2 (mem_iUnion₂.mpr ⟨i, hi, h⟩)),
      sub_zero]
  · by_cases hzF₀ : z ∈ filledHull (γ₀ '' uIcc γ₀.a γ₀.b)
    · have hzK : z ∈ ⋃ i ∈ s, filledHull (γ i '' uIcc (γ i).a (γ i).b) := by
        by_contra hzK
        exact hzΔ ⟨⟨hzF₀, hz₀⟩, hzK⟩
      obtain ⟨i, hi, hzFi⟩ := mem_iUnion₂.mp hzK
      rw [windingNumber_of_positivelyOrient_of_mem_filledHull_sdiff hab₀ hinj₀ ⟨hzF₀, hz₀⟩,
        Finset.sum_eq_single i
          (fun j hj hji ↦ windingNumber_of_positivelyOrient_eq_zero_of_notMem_filledHull (γ j)
            (Set.disjoint_left.mp (hdisj hi hj hji.symm) hzFi))
          (fun hnot ↦ (hnot hi).elim),
        windingNumber_of_positivelyOrient_of_mem_filledHull_sdiff (hab i hi) (hinj i hi)
          ⟨hzFi, hzi i hi⟩,
        sub_self]
    · rw [windingNumber_of_positivelyOrient_eq_zero_of_notMem_filledHull γ₀ hzF₀,
        Finset.sum_eq_zero fun i hi ↦
          windingNumber_of_positivelyOrient_eq_zero_of_notMem_filledHull (γ i)
            (fun h ↦ hzF₀ (hsub i hi h).1),
        sub_zero]

/-- The trace-zero real `windingWeight` of `jordanBoundaryCycle γ₀ s γ` is the indicator of `Δ`. -/
theorem windingWeight_jordanBoundaryCycle {γ₀ : PiecewiseC1ClosedCurve} {s : Finset ι}
    {γ : ι → PiecewiseC1ClosedCurve}
    (hab₀ : γ₀.a < γ₀.b) (hinj₀ : InjOn γ₀ (Ico γ₀.a γ₀.b))
    (hab : ∀ i ∈ s, (γ i).a < (γ i).b)
    (hinj : ∀ i ∈ s, InjOn (γ i) (Ico (γ i).a (γ i).b))
    (hsub : ∀ i ∈ s,
      filledHull (γ i '' uIcc (γ i).a (γ i).b) ⊆
        filledHull (γ₀ '' uIcc γ₀.a γ₀.b) \ (γ₀ '' uIcc γ₀.a γ₀.b))
    (hdisj : (s : Set ι).PairwiseDisjoint fun i ↦ filledHull (γ i '' uIcc (γ i).a (γ i).b)) :
    (jordanBoundaryCycle γ₀ s γ).windingWeight =
      ((filledHull (γ₀ '' uIcc γ₀.a γ₀.b) \ (γ₀ '' uIcc γ₀.a γ₀.b)) \
        ⋃ i ∈ s, filledHull (γ i '' uIcc (γ i).a (γ i).b)).indicator 1 := by
  classical
  set Δ := (filledHull (γ₀ '' uIcc γ₀.a γ₀.b) \ (γ₀ '' uIcc γ₀.a γ₀.b)) \
    ⋃ i ∈ s, filledHull (γ i '' uIcc (γ i).a (γ i).b)
  have hΔ_open : IsOpen Δ :=
    (γ₀.isJordanCurve_image hab₀ hinj₀).isOpen_filledHull_sdiff_biUnion
      fun i hi ↦ (γ i).isJordanCurve_image (hab i hi) (hinj i hi)
  ext z
  by_cases htr : z ∈ trace (jordanBoundaryCycle γ₀ s γ)
  · rw [windingWeight_eq_zero_of_mem _ htr]
    rw [trace_jordanBoundaryCycle hab₀ hinj₀ hab hinj hsub hdisj] at htr
    have hzΔ : z ∉ Δ := fun hzΔ ↦ htr.2 (hΔ_open.interior_eq.symm ▸ hzΔ)
    rw [indicator_of_notMem hzΔ]
  · rw [windingWeight_eq_of_notMem _ htr,
      windingNumber_jordanBoundaryCycle hab₀ hinj₀ hab hinj hsub hdisj htr]
    by_cases hzΔ : z ∈ Δ <;> simp [Δ, hzΔ]

/-- Whenever `closure Δ ⊆ Ω`, the trace of `jordanBoundaryCycle γ₀ s γ` lies in `Ω`. -/
theorem isIn_jordanBoundaryCycle {γ₀ : PiecewiseC1ClosedCurve} {s : Finset ι}
    {γ : ι → PiecewiseC1ClosedCurve} {Ω : Set ℂ}
    (hab₀ : γ₀.a < γ₀.b) (hinj₀ : InjOn γ₀ (Ico γ₀.a γ₀.b))
    (hab : ∀ i ∈ s, (γ i).a < (γ i).b)
    (hinj : ∀ i ∈ s, InjOn (γ i) (Ico (γ i).a (γ i).b))
    (hsub : ∀ i ∈ s,
      filledHull (γ i '' uIcc (γ i).a (γ i).b) ⊆
        filledHull (γ₀ '' uIcc γ₀.a γ₀.b) \ (γ₀ '' uIcc γ₀.a γ₀.b))
    (hdisj : (s : Set ι).PairwiseDisjoint fun i ↦ filledHull (γ i '' uIcc (γ i).a (γ i).b))
    (hΩ : closure ((filledHull (γ₀ '' uIcc γ₀.a γ₀.b) \ (γ₀ '' uIcc γ₀.a γ₀.b)) \
      ⋃ i ∈ s, filledHull (γ i '' uIcc (γ i).a (γ i).b)) ⊆ Ω) :
    IsIn (jordanBoundaryCycle γ₀ s γ) Ω := by
  rw [isIn_iff, trace_jordanBoundaryCycle hab₀ hinj₀ hab hinj hsub hdisj]
  exact frontier_subset_closure.trans hΩ

/-- Whenever `closure Δ ⊆ Ω`, `jordanBoundaryCycle γ₀ s γ` is null-homologous in `Ω`. -/
theorem isNullHomologous_jordanBoundaryCycle {γ₀ : PiecewiseC1ClosedCurve} {s : Finset ι}
    {γ : ι → PiecewiseC1ClosedCurve} {Ω : Set ℂ}
    (hab₀ : γ₀.a < γ₀.b) (hinj₀ : InjOn γ₀ (Ico γ₀.a γ₀.b))
    (hab : ∀ i ∈ s, (γ i).a < (γ i).b)
    (hinj : ∀ i ∈ s, InjOn (γ i) (Ico (γ i).a (γ i).b))
    (hsub : ∀ i ∈ s,
      filledHull (γ i '' uIcc (γ i).a (γ i).b) ⊆
        filledHull (γ₀ '' uIcc γ₀.a γ₀.b) \ (γ₀ '' uIcc γ₀.a γ₀.b))
    (hdisj : (s : Set ι).PairwiseDisjoint fun i ↦ filledHull (γ i '' uIcc (γ i).a (γ i).b))
    (hΩ : closure ((filledHull (γ₀ '' uIcc γ₀.a γ₀.b) \ (γ₀ '' uIcc γ₀.a γ₀.b)) \
      ⋃ i ∈ s, filledHull (γ i '' uIcc (γ i).a (γ i).b)) ⊆ Ω) :
    IsNullHomologous (jordanBoundaryCycle γ₀ s γ) Ω := by
  rw [isNullHomologous_iff]
  intro z hzΩ
  have htr : z ∉ trace (jordanBoundaryCycle γ₀ s γ) :=
    fun h ↦ hzΩ (isIn_iff.mp (isIn_jordanBoundaryCycle hab₀ hinj₀ hab hinj hsub hdisj hΩ) h)
  have hzΔ : z ∉ (filledHull (γ₀ '' uIcc γ₀.a γ₀.b) \ (γ₀ '' uIcc γ₀.a γ₀.b)) \
      ⋃ i ∈ s, filledHull (γ i '' uIcc (γ i).a (γ i).b) :=
    fun h ↦ hzΩ (hΩ (subset_closure h))
  rw [windingNumber_jordanBoundaryCycle hab₀ hinj₀ hab hinj hsub hdisj htr, ite_eq_right hzΔ]

end Cycle

end JordanBoundaryCycle

end TauCeti.Contour

end
