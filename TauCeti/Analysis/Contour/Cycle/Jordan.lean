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
import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.JordanCurve
import TauCeti.Topology.JordanCurve.Interval

/-!
# Oriented boundary cycles of finitely connected Jordan regions

Given an outer simple closed piecewise-`C¹` curve `γ₀` and finitely many inner simple closed
piecewise-`C¹` curves `γ i` (`i ∈ s`) whose closed filled hulls are pairwise disjoint inside the
inside of `γ₀`, this file packages the positively oriented boundary cycle
`TauCeti.Contour.jordanBoundaryCycle γ₀ s γ := [γ₀⁺] - ∑ i ∈ s, [γᵢ⁺]` on the existing
`TauCeti.Contour.Cycle` carrier and proves its trace, winding-number, winding-weight, containment,
and null-homology adapters for the finitely connected Jordan region
`Δ := (filledHull C₀ \ C₀) \ ⋃ i ∈ s, filledHull (C i)`.

## Main definitions

* `TauCeti.Contour.PiecewiseC1ClosedCurve.positivelyOrient`: orient a closed piecewise-`C¹` curve
  positively (reversing it when `jordanSign = -1`, leaving it unchanged otherwise).
* `TauCeti.Contour.jordanBoundaryCycle`: oriented boundary cycle `[γ₀⁺] - ∑ i ∈ s, [γᵢ⁺]`.

## Main results

* `TauCeti.Contour.PiecewiseC1ClosedCurve.positivelyOrient_positivelyOrient`,
  `positivelyOrient_symm`, `uIcc_positivelyOrient`, `jordanSign_positivelyOrient`: algebraic and
  orientation properties of `positivelyOrient`.
* `TauCeti.Contour.Cycle.windingNumber_of_positivelyOrient_eq_one_of_mem_filledHull_sdiff`: a
  positively oriented simple closed piecewise-`C¹` curve has winding number `1` on its inside.
* `TauCeti.Contour.Cycle.trace_jordanBoundaryCycle`, `windingNumber_jordanBoundaryCycle`,
  `windingWeight_jordanBoundaryCycle`, `isIn_jordanBoundaryCycle`,
  `isNullHomologous_jordanBoundaryCycle`: trace, winding, and null-homology adapters.

## References

* L. Ahlfors, *Complex Analysis*, 3rd ed., McGraw-Hill, 1979, Chapter 4, §2 and §4.
* A. Rainer, *Advanced Complex Analysis*, Proposition 10.1.
-/

public section

noncomputable section

open Bornology Complex Filter MeasureTheory Metric Set
open scoped Interval Topology

namespace TauCeti.Contour

/-! ### Positive orientation of a closed piecewise-`C¹` curve -/

namespace PiecewiseC1ClosedCurve

/-- Orient a closed piecewise-`C¹` curve positively: reverse `γ` via `γ.symm` if
`jordanSign γ γ.a γ.b = -1`, and keep `γ` otherwise. In particular, `positivelyOrient` is
idempotent on every curve, and for a simple closed curve (`γ.a ≠ γ.b`,
`InjOn γ (Ico (min γ.a γ.b) (max γ.a γ.b))`), `positivelyOrient γ` always has orientation
sign `1`. -/
def positivelyOrient (γ : PiecewiseC1ClosedCurve) : PiecewiseC1ClosedCurve :=
  if jordanSign γ γ.a γ.b = -1 then γ.symm else γ

/-- Defining formula for `PiecewiseC1ClosedCurve.positivelyOrient`. -/
theorem positivelyOrient_def (γ : PiecewiseC1ClosedCurve) :
    γ.positivelyOrient = if jordanSign γ γ.a γ.b = -1 then γ.symm else γ :=
  (rfl)

/-- A curve with `jordanSign = -1` is reversed by `positivelyOrient`. -/
@[simp]
theorem positivelyOrient_of_jordanSign_eq_neg_one {γ : PiecewiseC1ClosedCurve}
    (h : jordanSign γ γ.a γ.b = -1) : γ.positivelyOrient = γ.symm := by
  simp [positivelyOrient, h]

/-- A curve with `jordanSign ≠ -1` is unchanged by `positivelyOrient`. -/
theorem positivelyOrient_of_jordanSign_ne_neg_one {γ : PiecewiseC1ClosedCurve}
    (h : jordanSign γ γ.a γ.b ≠ -1) : γ.positivelyOrient = γ := by
  simp [positivelyOrient, h]

/-- A curve that already has `jordanSign = 1` is unchanged by `positivelyOrient`. -/
@[simp]
theorem positivelyOrient_of_jordanSign_eq_one {γ : PiecewiseC1ClosedCurve}
    (h : jordanSign γ γ.a γ.b = 1) : γ.positivelyOrient = γ :=
  positivelyOrient_of_jordanSign_ne_neg_one (by omega)

/-- `positivelyOrient` leaves the canonical extension to `ℝ` unchanged. -/
@[simp]
theorem coe_positivelyOrient (γ : PiecewiseC1ClosedCurve) :
    (γ.positivelyOrient : ℝ → ℂ) = γ := by
  by_cases h : jordanSign γ γ.a γ.b = -1
  · rw [positivelyOrient_of_jordanSign_eq_neg_one h, coe_symm]
  · rw [positivelyOrient_of_jordanSign_ne_neg_one h]

/-- `positivelyOrient` leaves the unordered parameter interval `uIcc` unchanged. -/
@[simp]
theorem uIcc_positivelyOrient (γ : PiecewiseC1ClosedCurve) :
    uIcc γ.positivelyOrient.a γ.positivelyOrient.b = uIcc γ.a γ.b := by
  by_cases h : jordanSign γ γ.a γ.b = -1
  · rw [positivelyOrient_of_jordanSign_eq_neg_one h, symm_a, symm_b, uIcc_comm]
  · rw [positivelyOrient_of_jordanSign_ne_neg_one h]

/-- Reversing a bundled closed piecewise-`C¹` curve negates its `jordanSign`. -/
theorem jordanSign_symm (γ : PiecewiseC1ClosedCurve) :
    jordanSign γ.symm γ.symm.a γ.symm.b = -jordanSign γ γ.a γ.b := by
  simp only [coe_symm, symm_a, symm_b,
    γ.isPiecewiseC1On.absolutelyContinuousOnInterval.jordanSign_symm]

/-- `positivelyOrient` is unconditionally idempotent. -/
@[simp]
theorem positivelyOrient_positivelyOrient (γ : PiecewiseC1ClosedCurve) :
    γ.positivelyOrient.positivelyOrient = γ.positivelyOrient := by
  by_cases h : jordanSign γ γ.a γ.b = -1
  · rw [positivelyOrient_of_jordanSign_eq_neg_one h]
    exact positivelyOrient_of_jordanSign_eq_one (by rw [jordanSign_symm, h, neg_neg])
  · rw [positivelyOrient_of_jordanSign_ne_neg_one h, positivelyOrient_of_jordanSign_ne_neg_one h]

/-- On any curve with nonzero `jordanSign`, `positivelyOrient` is invariant under orientation
reversal. -/
theorem positivelyOrient_symm {γ : PiecewiseC1ClosedCurve} (h : jordanSign γ γ.a γ.b ≠ 0) :
    γ.symm.positivelyOrient = γ.positivelyOrient := by
  rcases jordanSign_eq_one_or_neg_one_or_zero γ γ.a γ.b with h1 | h1 | h1
  · rw [positivelyOrient_of_jordanSign_eq_one h1,
      positivelyOrient_of_jordanSign_eq_neg_one (by rw [jordanSign_symm, h1]), symm_symm]
  · rw [positivelyOrient_of_jordanSign_eq_neg_one h1,
      positivelyOrient_of_jordanSign_eq_one (by rw [jordanSign_symm, h1, neg_neg])]
  · exact (h h1).elim

/-- `positivelyOrient` leaves the interval image unchanged. -/
theorem image_positivelyOrient (γ : PiecewiseC1ClosedCurve) :
    γ.positivelyOrient '' uIcc γ.positivelyOrient.a γ.positivelyOrient.b =
      γ '' uIcc γ.a γ.b := by
  simp

/-- After `positivelyOrient`, every simple closed piecewise-`C¹` curve (`γ.a ≠ γ.b`,
`InjOn γ (Ico (min γ.a γ.b) (max γ.a γ.b))`) has `jordanSign` equal to `1`. -/
theorem jordanSign_positivelyOrient {γ : PiecewiseC1ClosedCurve} (hab : γ.a ≠ γ.b)
    (hinj : InjOn γ (Ico (min γ.a γ.b) (max γ.a γ.b))) :
    jordanSign γ.positivelyOrient γ.positivelyOrient.a γ.positivelyOrient.b = 1 := by
  have hlt_case : ∀ {η : PiecewiseC1ClosedCurve}, η.a < η.b → InjOn η (Ico η.a η.b) →
      jordanSign η.positivelyOrient η.positivelyOrient.a η.positivelyOrient.b = 1 := by
    intro η hη hηinj
    rcases η.isPiecewiseC1On.absolutelyContinuousOnInterval.jordanSign_eq_one_or_neg_one
        hη η.source_eq_target hηinj with h | h
    · rwa [positivelyOrient_of_jordanSign_eq_one h]
    · rw [positivelyOrient_of_jordanSign_eq_neg_one h, jordanSign_symm, h, neg_neg]
  rcases lt_or_gt_of_ne hab with hlt | hlt
  · rw [min_eq_left hlt.le, max_eq_right hlt.le] at hinj
    exact hlt_case hlt hinj
  · rw [min_eq_right hlt.le, max_eq_left hlt.le] at hinj
    have hηlt : γ.symm.a < γ.symm.b := by simpa using hlt
    have hηinj : InjOn γ.symm (Ico γ.symm.a γ.symm.b) := by simpa using hinj
    have hsign : jordanSign γ.symm γ.symm.a γ.symm.b ≠ 0 :=
      γ.symm.isPiecewiseC1On.absolutelyContinuousOnInterval.jordanSign_ne_zero
        hηlt γ.symm.source_eq_target hηinj
    have hne : jordanSign γ γ.a γ.b ≠ 0 := by
      rwa [← neg_ne_zero, ← jordanSign_symm]
    rw [← positivelyOrient_symm hne]
    exact hlt_case hηlt hηinj

end PiecewiseC1ClosedCurve

namespace Cycle

/-- `positivelyOrient` preserves the cycle trace of a generator. -/
theorem trace_of_positivelyOrient (γ : PiecewiseC1ClosedCurve) :
    trace (FreeAddCommGroup.of γ.positivelyOrient) = trace (FreeAddCommGroup.of γ) := by
  simp

/-- `positivelyOrient` preserves containment of a generator in any target set. -/
theorem isIn_of_positivelyOrient_iff {γ : PiecewiseC1ClosedCurve} {Ω : Set ℂ} :
    IsIn (FreeAddCommGroup.of γ.positivelyOrient) Ω ↔ IsIn (FreeAddCommGroup.of γ) Ω := by
  rw [isIn_iff, isIn_iff, trace_of_positivelyOrient]

/-- `positivelyOrient` preserves vanishing of a generator's cycle winding number. -/
theorem windingNumber_of_positivelyOrient_eq_zero_iff (γ : PiecewiseC1ClosedCurve) (z : ℂ) :
    windingNumber z (FreeAddCommGroup.of γ.positivelyOrient) = 0 ↔
      windingNumber z (FreeAddCommGroup.of γ) = 0 := by
  unfold PiecewiseC1ClosedCurve.positivelyOrient
  split_ifs
  · exact windingNumber_of_symm_eq_zero_iff γ z
  · rfl

/-- `positivelyOrient` preserves null-homology of a generator. -/
theorem isNullHomologous_of_positivelyOrient_iff {γ : PiecewiseC1ClosedCurve} {Ω : Set ℂ} :
    IsNullHomologous (FreeAddCommGroup.of γ.positivelyOrient) Ω ↔
      IsNullHomologous (FreeAddCommGroup.of γ) Ω := by
  simp only [isNullHomologous_iff, windingNumber_of_positivelyOrient_eq_zero_iff]

/-- Outside `filledHull (γ '' uIcc γ.a γ.b)`, the cycle winding number of `γ.positivelyOrient`
vanishes. -/
theorem windingNumber_of_positivelyOrient_eq_zero_of_notMem_filledHull
    (γ : PiecewiseC1ClosedCurve) {z : ℂ} (hz : z ∉ filledHull (γ '' uIcc γ.a γ.b)) :
    windingNumber z (FreeAddCommGroup.of γ.positivelyOrient) = 0 := by
  rw [windingNumber_of_positivelyOrient_eq_zero_iff, windingNumber_of]
  exact γ.isPiecewiseC1On.absolutelyContinuousOnInterval.windingNumber_eq_zero_of_notMem_filledHull
    γ.source_eq_target hz

/-- For any curve with nonzero `jordanSign`, integrating over `γ.positivelyOrient` multiplies the
integral over `γ` by `jordanSign γ γ.a γ.b ∈ {1, -1}`. -/
theorem integral_of_positivelyOrient {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {γ : PiecewiseC1ClosedCurve} (h : jordanSign γ γ.a γ.b ≠ 0) (f : ℂ → E) :
    integral f (FreeAddCommGroup.of γ.positivelyOrient) =
      jordanSign γ γ.a γ.b • integral f (FreeAddCommGroup.of γ) := by
  rcases jordanSign_eq_one_or_neg_one_or_zero γ γ.a γ.b with h1 | h1 | h1
  · rw [PiecewiseC1ClosedCurve.positivelyOrient_of_jordanSign_eq_one h1, h1, one_smul]
  · rw [PiecewiseC1ClosedCurve.positivelyOrient_of_jordanSign_eq_neg_one h1,
      integral_of_symm, h1, neg_one_smul]
  · exact (h h1).elim

/-- Inside `filledHull (γ '' uIcc γ.a γ.b) \ (γ '' uIcc γ.a γ.b)`, a positively oriented simple
closed piecewise-`C¹` curve (`γ.a ≠ γ.b`, `InjOn γ (Ico (min γ.a γ.b) (max γ.a γ.b))`) has
cycle winding number `1`. -/
theorem windingNumber_of_positivelyOrient_eq_one_of_mem_filledHull_sdiff
    {γ : PiecewiseC1ClosedCurve} (hab : γ.a ≠ γ.b)
    (hinj : InjOn γ (Ico (min γ.a γ.b) (max γ.a γ.b))) {z : ℂ}
    (hz : z ∈ filledHull (γ '' uIcc γ.a γ.b) \ (γ '' uIcc γ.a γ.b)) :
    windingNumber z (FreeAddCommGroup.of γ.positivelyOrient) = 1 := by
  have hlt_case : ∀ {η : PiecewiseC1ClosedCurve}, η.a < η.b → InjOn η (Ico η.a η.b) →
      z ∈ filledHull (η '' uIcc η.a η.b) \ (η '' uIcc η.a η.b) →
      windingNumber z (FreeAddCommGroup.of η.positivelyOrient) = 1 := by
    intro η hη hηinj hzη
    have hw := η.isPiecewiseC1On.absolutelyContinuousOnInterval
      |>.windingNumber_eq_jordanSign_of_mem_filledHull_sdiff hη η.source_eq_target hηinj hzη
    rcases η.isPiecewiseC1On.absolutelyContinuousOnInterval.jordanSign_eq_one_or_neg_one
        hη η.source_eq_target hηinj with h | h
    · rw [PiecewiseC1ClosedCurve.positivelyOrient_of_jordanSign_eq_one h, windingNumber_of, hw, h,
        Int.cast_one]
    · rw [PiecewiseC1ClosedCurve.positivelyOrient_of_jordanSign_eq_neg_one h,
        windingNumber_of_symm η hzη.2, windingNumber_of, hw, h, Int.cast_neg, Int.cast_one,
        neg_neg]
  rcases lt_or_gt_of_ne hab with hlt | hlt
  · rw [min_eq_left hlt.le, max_eq_right hlt.le] at hinj
    exact hlt_case hlt hinj hz
  · rw [min_eq_right hlt.le, max_eq_left hlt.le] at hinj
    have hηlt : γ.symm.a < γ.symm.b := by simpa using hlt
    have hηinj : InjOn γ.symm (Ico γ.symm.a γ.symm.b) := by simpa using hinj
    have hsign : jordanSign γ.symm γ.symm.a γ.symm.b ≠ 0 :=
      γ.symm.isPiecewiseC1On.absolutelyContinuousOnInterval.jordanSign_ne_zero
        hηlt γ.symm.source_eq_target hηinj
    have hne : jordanSign γ γ.a γ.b ≠ 0 := by
      rwa [← neg_ne_zero, ← PiecewiseC1ClosedCurve.jordanSign_symm]
    rw [← PiecewiseC1ClosedCurve.positivelyOrient_symm hne]
    exact hlt_case hηlt hηinj (by simpa only [γ.image_symm] using hz)

end Cycle

/-! ### The oriented boundary cycle of a finitely connected Jordan region -/

section JordanBoundaryCycle

variable {ι : Type*}

/-- **Oriented boundary cycle of a finitely connected Jordan region.** Given an outer closed
piecewise-`C¹` curve `γ₀` and a finite family `(γ i)_{i ∈ s}` of hole curves, each curve is
positively oriented via `PiecewiseC1ClosedCurve.positivelyOrient` and assembled into the formal sum
`[γ₀⁺] - ∑ i ∈ s, [γᵢ⁺]` in `TauCeti.Contour.Cycle`. For arbitrary inputs this is only a formal
cycle; it represents the geometric boundary when `γ₀` and the `γ i` (`i ∈ s`) are simple closed
curves and the hole filled hulls `filledHull (γ i '' uIcc (γ i).a (γ i).b)` are pairwise disjoint
and contained in the inside of `γ₀`. -/
def jordanBoundaryCycle (γ₀ : PiecewiseC1ClosedCurve) (s : Finset ι)
    (γ : ι → PiecewiseC1ClosedCurve) : Cycle :=
  FreeAddCommGroup.of γ₀.positivelyOrient - ∑ i ∈ s, FreeAddCommGroup.of (γ i).positivelyOrient

/-- Defining formula for `TauCeti.Contour.jordanBoundaryCycle`. -/
theorem jordanBoundaryCycle_def (γ₀ : PiecewiseC1ClosedCurve) (s : Finset ι)
    (γ : ι → PiecewiseC1ClosedCurve) :
    jordanBoundaryCycle γ₀ s γ =
      FreeAddCommGroup.of γ₀.positivelyOrient -
        ∑ i ∈ s, FreeAddCommGroup.of (γ i).positivelyOrient :=
  (rfl)

/-- With no holes (`s = ∅`), `jordanBoundaryCycle` is `[γ₀⁺]`. -/
@[simp]
theorem jordanBoundaryCycle_empty (γ₀ : PiecewiseC1ClosedCurve)
    (γ : ι → PiecewiseC1ClosedCurve) :
    jordanBoundaryCycle γ₀ ∅ γ = FreeAddCommGroup.of γ₀.positivelyOrient := by
  simp [jordanBoundaryCycle]

/-- Inserting a new hole subtracts its positively oriented generator from `jordanBoundaryCycle`. -/
@[simp]
theorem jordanBoundaryCycle_insert [DecidableEq ι] (γ₀ : PiecewiseC1ClosedCurve) {i : ι}
    {s : Finset ι} (hi : i ∉ s) (γ : ι → PiecewiseC1ClosedCurve) :
    jordanBoundaryCycle γ₀ (insert i s) γ =
      jordanBoundaryCycle γ₀ s γ - FreeAddCommGroup.of (γ i).positivelyOrient := by
  rw [jordanBoundaryCycle, jordanBoundaryCycle, Finset.sum_insert hi, sub_sub, add_comm]

/-- When `γ₀` and every `γ i` (`i ∈ s`) already have `jordanSign = 1`, `jordanBoundaryCycle` is
simply `[γ₀] - ∑ i ∈ s, [γ i]`. -/
theorem jordanBoundaryCycle_of_jordanSign_eq_one {γ₀ : PiecewiseC1ClosedCurve} {s : Finset ι}
    {γ : ι → PiecewiseC1ClosedCurve} (h₀ : jordanSign γ₀ γ₀.a γ₀.b = 1)
    (h : ∀ i ∈ s, jordanSign (γ i) (γ i).a (γ i).b = 1) :
    jordanBoundaryCycle γ₀ s γ =
      FreeAddCommGroup.of γ₀ - ∑ i ∈ s, FreeAddCommGroup.of (γ i) := by
  rw [jordanBoundaryCycle, PiecewiseC1ClosedCurve.positivelyOrient_of_jordanSign_eq_one h₀]
  exact congrArg _ (Finset.sum_congr rfl fun i hi ↦ by
    rw [PiecewiseC1ClosedCurve.positivelyOrient_of_jordanSign_eq_one (h i hi)])

namespace Cycle

/-- For curves with nonzero `jordanSign`, integrating over `jordanBoundaryCycle γ₀ s γ` combines
the `jordanSign`-weighted contour integrals of `γ₀` and of the hole curves `γ i` (`i ∈ s`). -/
theorem integral_jordanBoundaryCycle {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {γ₀ : PiecewiseC1ClosedCurve} {s : Finset ι} {γ : ι → PiecewiseC1ClosedCurve}
    (h₀ : jordanSign γ₀ γ₀.a γ₀.b ≠ 0)
    (h : ∀ i ∈ s, jordanSign (γ i) (γ i).a (γ i).b ≠ 0) (f : ℂ → E) :
    integral f (jordanBoundaryCycle γ₀ s γ) =
      jordanSign γ₀ γ₀.a γ₀.b • integral f (FreeAddCommGroup.of γ₀) -
        ∑ i ∈ s, jordanSign (γ i) (γ i).a (γ i).b • integral f (FreeAddCommGroup.of (γ i)) := by
  rw [jordanBoundaryCycle, map_sub, map_sum, integral_of_positivelyOrient h₀]
  exact congrArg _ (Finset.sum_congr rfl fun i hi ↦
    integral_of_positivelyOrient (h i hi) f)

variable {γ₀ : PiecewiseC1ClosedCurve} {s : Finset ι} {γ : ι → PiecewiseC1ClosedCurve}

private theorem ne_positivelyOrient_outer_of_hole
    (hsub : ∀ i ∈ s, filledHull (γ i '' uIcc (γ i).a (γ i).b) ⊆
      filledHull (γ₀ '' uIcc γ₀.a γ₀.b) \ (γ₀ '' uIcc γ₀.a γ₀.b))
    {i : ι} (hi : i ∈ s) : γ₀.positivelyOrient ≠ (γ i).positivelyOrient := fun heq ↦ by
  have hz : (γ i) (γ i).a ∈ γ i '' uIcc (γ i).a (γ i).b :=
    Set.mem_image_of_mem (γ i) Set.left_mem_uIcc
  have hz₀ : (γ i) (γ i).a ∈ γ₀ '' uIcc γ₀.a γ₀.b := by
    rwa [← trace_of, ← trace_of_positivelyOrient, heq, trace_of_positivelyOrient, trace_of]
  exact (hsub i hi (subset_filledHull hz)).2 hz₀

/-- When each hole's filled hull is contained in the inside of `γ₀`, the trace of
`jordanBoundaryCycle γ₀ s γ` is the union of the outer curve and the hole curves. -/
theorem trace_jordanBoundaryCycle_eq_union
    (hsub : ∀ i ∈ s, filledHull (γ i '' uIcc (γ i).a (γ i).b) ⊆
      filledHull (γ₀ '' uIcc γ₀.a γ₀.b) \ (γ₀ '' uIcc γ₀.a γ₀.b)) :
    trace (jordanBoundaryCycle γ₀ s γ) =
      (γ₀ '' uIcc γ₀.a γ₀.b) ∪ ⋃ i ∈ s, γ i '' uIcc (γ i).a (γ i).b := by
  classical
  refine Subset.antisymm ?_ ?_
  · rw [jordanBoundaryCycle]
    refine (trace_sub_subset _ _).trans (union_subset_union
      (by rw [trace_of_positivelyOrient, trace_of]) ?_)
    exact (trace_sum_subset s _).trans (iUnion₂_mono fun i _ ↦ by
      rw [trace_of_positivelyOrient, trace_of])
  · rintro z (hz₀ | hzi)
    · refine mem_trace_iff.mpr ⟨γ₀.positivelyOrient, ?_, by rwa [γ₀.image_positivelyOrient]⟩
      rw [FreeAddCommGroup.mem_support_iff, jordanBoundaryCycle, map_sub, map_sum,
        FreeAddCommGroup.coeff_of_self, Finset.sum_eq_zero fun i hi ↦
          FreeAddCommGroup.coeff_of_of_ne (ne_positivelyOrient_outer_of_hole hsub hi),
        sub_zero]
      exact one_ne_zero
    · obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp hzi
      refine mem_trace_iff.mpr ⟨(γ i).positivelyOrient, ?_, by rwa [(γ i).image_positivelyOrient]⟩
      have hneg : FreeAddCommGroup.coeff (γ i).positivelyOrient
          (jordanBoundaryCycle γ₀ s γ) < 0 := by
        rw [jordanBoundaryCycle, map_sub, map_sum,
          FreeAddCommGroup.coeff_of_of_ne (ne_positivelyOrient_outer_of_hole hsub hi).symm,
          zero_sub, neg_lt_zero]
        have hnonneg : ∀ j ∈ s,
            (0 : ℤ) ≤ FreeAddCommGroup.coeff (γ i).positivelyOrient
              (FreeAddCommGroup.of (γ j).positivelyOrient) := fun j _ ↦ by
          by_cases heq : (γ i).positivelyOrient = (γ j).positivelyOrient
          · simp [heq]
          · simp [FreeAddCommGroup.coeff_of_of_ne heq]
        calc
          (0 : ℤ) < 1 := zero_lt_one
          _ = FreeAddCommGroup.coeff (γ i).positivelyOrient
                (FreeAddCommGroup.of (γ i).positivelyOrient) := by
              rw [FreeAddCommGroup.coeff_of_self]
          _ ≤ ∑ j ∈ s, FreeAddCommGroup.coeff (γ i).positivelyOrient
                (FreeAddCommGroup.of (γ j).positivelyOrient) :=
              Finset.single_le_sum hnonneg hi
      rw [FreeAddCommGroup.mem_support_iff]
      exact hneg.ne

private theorem isJordanCurve_image_of_ne {η : PiecewiseC1ClosedCurve} (hab : η.a ≠ η.b)
    (hinj : InjOn η (Ico (min η.a η.b) (max η.a η.b))) :
    TauCeti.IsJordanCurve (η '' uIcc η.a η.b) := by
  rcases lt_or_gt_of_ne hab with hlt | hlt
  · rw [min_eq_left hlt.le, max_eq_right hlt.le] at hinj
    exact η.isPiecewiseC1On.absolutelyContinuousOnInterval.isJordanCurve_image_uIcc
      hlt η.source_eq_target hinj
  · rw [min_eq_right hlt.le, max_eq_left hlt.le] at hinj
    rw [← η.image_symm]
    exact η.symm.isPiecewiseC1On.absolutelyContinuousOnInterval.isJordanCurve_image_uIcc
      (by simpa using hlt : η.symm.a < η.symm.b) η.symm.source_eq_target (by simpa using hinj)

/-- **Trace identification for `jordanBoundaryCycle`.** The trace of the oriented boundary cycle of
a finitely connected Jordan region `Δ` equals `frontier Δ`. -/
theorem trace_jordanBoundaryCycle (hab₀ : γ₀.a ≠ γ₀.b)
    (hinj₀ : InjOn γ₀ (Ico (min γ₀.a γ₀.b) (max γ₀.a γ₀.b)))
    (hab : ∀ i ∈ s, (γ i).a ≠ (γ i).b)
    (hinj : ∀ i ∈ s, InjOn (γ i) (Ico (min (γ i).a (γ i).b) (max (γ i).a (γ i).b)))
    (hsub : ∀ i ∈ s, filledHull (γ i '' uIcc (γ i).a (γ i).b) ⊆
      filledHull (γ₀ '' uIcc γ₀.a γ₀.b) \ (γ₀ '' uIcc γ₀.a γ₀.b))
    (hdisj : (s : Set ι).PairwiseDisjoint fun i ↦ filledHull (γ i '' uIcc (γ i).a (γ i).b)) :
    trace (jordanBoundaryCycle γ₀ s γ) =
      frontier ((filledHull (γ₀ '' uIcc γ₀.a γ₀.b) \ (γ₀ '' uIcc γ₀.a γ₀.b)) \
        ⋃ i ∈ s, filledHull (γ i '' uIcc (γ i).a (γ i).b)) := by
  rw [trace_jordanBoundaryCycle_eq_union hsub,
    (isJordanCurve_image_of_ne hab₀ hinj₀).frontier_filledHull_sdiff_biUnion
      (fun i hi ↦ isJordanCurve_image_of_ne (hab i hi) (hinj i hi)) hsub hdisj]

open scoped Classical in
/-- **Winding-number adapter for `jordanBoundaryCycle`.** Off its trace `frontier Δ`, the oriented
boundary cycle of a finitely connected Jordan region `Δ` has winding number `1` on `Δ` and `0`
everywhere else. -/
theorem windingNumber_jordanBoundaryCycle (hab₀ : γ₀.a ≠ γ₀.b)
    (hinj₀ : InjOn γ₀ (Ico (min γ₀.a γ₀.b) (max γ₀.a γ₀.b)))
    (hab : ∀ i ∈ s, (γ i).a ≠ (γ i).b)
    (hinj : ∀ i ∈ s, InjOn (γ i) (Ico (min (γ i).a (γ i).b) (max (γ i).a (γ i).b)))
    (hsub : ∀ i ∈ s, filledHull (γ i '' uIcc (γ i).a (γ i).b) ⊆
      filledHull (γ₀ '' uIcc γ₀.a γ₀.b) \ (γ₀ '' uIcc γ₀.a γ₀.b))
    (hdisj : (s : Set ι).PairwiseDisjoint fun i ↦ filledHull (γ i '' uIcc (γ i).a (γ i).b))
    {z : ℂ} (hz : z ∉ trace (jordanBoundaryCycle γ₀ s γ)) :
    windingNumber z (jordanBoundaryCycle γ₀ s γ) =
      if z ∈ (filledHull (γ₀ '' uIcc γ₀.a γ₀.b) \ (γ₀ '' uIcc γ₀.a γ₀.b)) \
          ⋃ i ∈ s, filledHull (γ i '' uIcc (γ i).a (γ i).b) then 1 else 0 := by
  rw [trace_jordanBoundaryCycle_eq_union hsub] at hz
  rw [jordanBoundaryCycle, map_sub, map_sum]
  split_ifs with hzΔ
  · rw [windingNumber_of_positivelyOrient_eq_one_of_mem_filledHull_sdiff hab₀ hinj₀ hzΔ.1,
      Finset.sum_eq_zero fun i hi ↦
        windingNumber_of_positivelyOrient_eq_zero_of_notMem_filledHull (γ i)
          (fun h ↦ hzΔ.2 (mem_iUnion₂.mpr ⟨i, hi, h⟩)), sub_zero]
  · by_cases hzF₀ : z ∈ filledHull (γ₀ '' uIcc γ₀.a γ₀.b)
    · obtain ⟨i, hi, hzFi⟩ := mem_iUnion₂.mp
        (by_contra fun h ↦ hzΔ ⟨⟨hzF₀, fun h₀ ↦ hz (Or.inl h₀)⟩, h⟩)
      rw [windingNumber_of_positivelyOrient_eq_one_of_mem_filledHull_sdiff hab₀ hinj₀
            ⟨hzF₀, fun h₀ ↦ hz (Or.inl h₀)⟩,
        Finset.sum_eq_single i (fun j hj hji ↦
            windingNumber_of_positivelyOrient_eq_zero_of_notMem_filledHull (γ j)
              (Set.disjoint_left.mp (hdisj hi hj hji.symm) hzFi))
          (fun hnot ↦ (hnot hi).elim),
        windingNumber_of_positivelyOrient_eq_one_of_mem_filledHull_sdiff (hab i hi) (hinj i hi)
          ⟨hzFi, fun h ↦ hz (Or.inr (mem_iUnion₂.mpr ⟨i, hi, h⟩))⟩, sub_self]
    · rw [windingNumber_of_positivelyOrient_eq_zero_of_notMem_filledHull γ₀ hzF₀,
        Finset.sum_eq_zero fun i hi ↦
          windingNumber_of_positivelyOrient_eq_zero_of_notMem_filledHull (γ i)
            (fun h ↦ hzF₀ (hsub i hi h).1), sub_zero]

/-- The trace-zero real `windingWeight` of `jordanBoundaryCycle γ₀ s γ` is the indicator of `Δ`. -/
theorem windingWeight_jordanBoundaryCycle (hab₀ : γ₀.a ≠ γ₀.b)
    (hinj₀ : InjOn γ₀ (Ico (min γ₀.a γ₀.b) (max γ₀.a γ₀.b)))
    (hab : ∀ i ∈ s, (γ i).a ≠ (γ i).b)
    (hinj : ∀ i ∈ s, InjOn (γ i) (Ico (min (γ i).a (γ i).b) (max (γ i).a (γ i).b)))
    (hsub : ∀ i ∈ s, filledHull (γ i '' uIcc (γ i).a (γ i).b) ⊆
      filledHull (γ₀ '' uIcc γ₀.a γ₀.b) \ (γ₀ '' uIcc γ₀.a γ₀.b))
    (hdisj : (s : Set ι).PairwiseDisjoint fun i ↦ filledHull (γ i '' uIcc (γ i).a (γ i).b)) :
    (jordanBoundaryCycle γ₀ s γ).windingWeight =
      ((filledHull (γ₀ '' uIcc γ₀.a γ₀.b) \ (γ₀ '' uIcc γ₀.a γ₀.b)) \
        ⋃ i ∈ s, filledHull (γ i '' uIcc (γ i).a (γ i).b)).indicator 1 := by
  classical
  set Δ := (filledHull (γ₀ '' uIcc γ₀.a γ₀.b) \ (γ₀ '' uIcc γ₀.a γ₀.b)) \
    ⋃ i ∈ s, filledHull (γ i '' uIcc (γ i).a (γ i).b)
  have hΔ_open : IsOpen Δ :=
    (isJordanCurve_image_of_ne hab₀ hinj₀).isClosed.isOpen_filledHull_sdiff_biUnion s fun i hi ↦
      (isJordanCurve_image_of_ne (hab i hi) (hinj i hi)).isClosed
  ext z
  by_cases htr : z ∈ trace (jordanBoundaryCycle γ₀ s γ)
  · rw [windingWeight_eq_zero_of_mem _ htr]
    rw [trace_jordanBoundaryCycle hab₀ hinj₀ hab hinj hsub hdisj] at htr
    rw [indicator_of_notMem fun hzΔ ↦ htr.2 (hΔ_open.interior_eq.symm ▸ hzΔ)]
  · rw [windingWeight_eq_of_notMem _ htr,
      windingNumber_jordanBoundaryCycle hab₀ hinj₀ hab hinj hsub hdisj htr]
    by_cases hzΔ : z ∈ Δ <;> simp [Δ, hzΔ]

/-- Whenever `closure Δ ⊆ Ω`, the trace of `jordanBoundaryCycle γ₀ s γ` lies in `Ω`. -/
theorem isIn_jordanBoundaryCycle {Ω : Set ℂ} (hab₀ : γ₀.a ≠ γ₀.b)
    (hinj₀ : InjOn γ₀ (Ico (min γ₀.a γ₀.b) (max γ₀.a γ₀.b)))
    (hab : ∀ i ∈ s, (γ i).a ≠ (γ i).b)
    (hinj : ∀ i ∈ s, InjOn (γ i) (Ico (min (γ i).a (γ i).b) (max (γ i).a (γ i).b)))
    (hsub : ∀ i ∈ s, filledHull (γ i '' uIcc (γ i).a (γ i).b) ⊆
      filledHull (γ₀ '' uIcc γ₀.a γ₀.b) \ (γ₀ '' uIcc γ₀.a γ₀.b))
    (hdisj : (s : Set ι).PairwiseDisjoint fun i ↦ filledHull (γ i '' uIcc (γ i).a (γ i).b))
    (hΩ : closure ((filledHull (γ₀ '' uIcc γ₀.a γ₀.b) \ (γ₀ '' uIcc γ₀.a γ₀.b)) \
      ⋃ i ∈ s, filledHull (γ i '' uIcc (γ i).a (γ i).b)) ⊆ Ω) :
    IsIn (jordanBoundaryCycle γ₀ s γ) Ω := by
  rw [isIn_iff, trace_jordanBoundaryCycle hab₀ hinj₀ hab hinj hsub hdisj]
  exact frontier_subset_closure.trans hΩ

/-- Whenever `closure Δ ⊆ Ω`, `jordanBoundaryCycle γ₀ s γ` is null-homologous in `Ω`. -/
theorem isNullHomologous_jordanBoundaryCycle {Ω : Set ℂ} (hab₀ : γ₀.a ≠ γ₀.b)
    (hinj₀ : InjOn γ₀ (Ico (min γ₀.a γ₀.b) (max γ₀.a γ₀.b)))
    (hab : ∀ i ∈ s, (γ i).a ≠ (γ i).b)
    (hinj : ∀ i ∈ s, InjOn (γ i) (Ico (min (γ i).a (γ i).b) (max (γ i).a (γ i).b)))
    (hsub : ∀ i ∈ s, filledHull (γ i '' uIcc (γ i).a (γ i).b) ⊆
      filledHull (γ₀ '' uIcc γ₀.a γ₀.b) \ (γ₀ '' uIcc γ₀.a γ₀.b))
    (hdisj : (s : Set ι).PairwiseDisjoint fun i ↦ filledHull (γ i '' uIcc (γ i).a (γ i).b))
    (hΩ : closure ((filledHull (γ₀ '' uIcc γ₀.a γ₀.b) \ (γ₀ '' uIcc γ₀.a γ₀.b)) \
      ⋃ i ∈ s, filledHull (γ i '' uIcc (γ i).a (γ i).b)) ⊆ Ω) :
    IsNullHomologous (jordanBoundaryCycle γ₀ s γ) Ω := by
  rw [isNullHomologous_iff]
  intro z hzΩ
  have htr : z ∉ trace (jordanBoundaryCycle γ₀ s γ) :=
    fun h ↦ hzΩ (isIn_iff.mp (isIn_jordanBoundaryCycle hab₀ hinj₀ hab hinj hsub hdisj hΩ) h)
  rw [windingNumber_jordanBoundaryCycle hab₀ hinj₀ hab hinj hsub hdisj htr,
    ite_eq_right fun h ↦ hzΩ (hΩ (subset_closure h))]

end Cycle

end JordanBoundaryCycle

end TauCeti.Contour

end
