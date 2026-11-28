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
import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.JordanCurve

/-!
# Oriented boundary cycles of finitely connected Jordan regions

Given an outer simple closed absolutely continuous curve `γ₀` and finitely many inner simple closed
absolutely continuous curves `γ i` (`i ∈ s`) whose closed filled hulls are pairwise disjoint inside
the inside of `γ₀`, this file packages the finitely connected Jordan region
`TauCeti.Contour.jordanRegion γ₀ s γ` and its positively oriented boundary cycle
`TauCeti.Contour.jordanBoundaryCycle γ₀ s γ := [γ₀⁺] - ∑ i ∈ s, [γᵢ⁺]` on the existing
`TauCeti.Contour.Cycle` carrier, and proves its trace, winding-number, winding-weight, containment,
and null-homology adapters.

## Main definitions

* `TauCeti.Contour.AbsolutelyContinuousClosedCurve.positivelyOrient`: orient a closed absolutely
  continuous curve positively (reversing it when `jordanSign = -1`, leaving it unchanged otherwise).
* `TauCeti.Contour.jordanBoundaryCycle`: oriented boundary cycle `[γ₀⁺] - ∑ i ∈ s, [γᵢ⁺]`.
* `TauCeti.Contour.jordanRegion`: finitely connected Jordan region bounded externally by `γ₀` and
  internally by the holes `γ i` (`i ∈ s`).

## Main results

* `TauCeti.Contour.AbsolutelyContinuousClosedCurve.positivelyOrient_positivelyOrient`,
  `positivelyOrient_symm`, `uIcc_positivelyOrient`, `jordanSign_ne_zero_of_ne`,
  `jordanSign_positivelyOrient`: algebraic and orientation properties of `positivelyOrient`.
* `TauCeti.Contour.Cycle.windingNumber_of_positivelyOrient_eq_one_of_mem_filledHull_sdiff`: a
  closed absolutely continuous curve with nonzero `jordanSign` has winding number `1` on its
  inside after `positivelyOrient`.
* `TauCeti.Contour.jordanRegion_def`, `TauCeti.Contour.mem_jordanRegion_iff`,
  `TauCeti.Contour.jordanRegion_empty`, `TauCeti.Contour.jordanRegion_insert`,
  `TauCeti.Contour.isOpen_jordanRegion`, `TauCeti.Contour.isBounded_jordanRegion`,
  `TauCeti.Contour.closure_jordanRegion`, `TauCeti.Contour.Cycle.trace_jordanBoundaryCycle`,
  `notMem_trace_jordanBoundaryCycle_of_mem`, `windingNumber_jordanBoundaryCycle`,
  `windingWeight_jordanBoundaryCycle`, `isIn_jordanBoundaryCycle`,
  `isNullHomologous_jordanBoundaryCycle`: region, openness, boundedness, closure, trace, winding,
  and null-homology adapters.

## References

* L. Ahlfors, *Complex Analysis*, 3rd ed., McGraw-Hill, 1979, Chapter 4, §2 and §4.
* A. Rainer, *Advanced Complex Analysis*, Proposition 10.1.
-/

public section

noncomputable section

open Bornology Complex Filter MeasureTheory Metric Set
open scoped Interval Topology

namespace TauCeti.Contour

/-! ### Positive orientation of a closed absolutely continuous curve -/

namespace AbsolutelyContinuousClosedCurve

/-- Orient a closed absolutely continuous curve positively: reverse `γ` via `γ.symm` if
`jordanSign γ γ.a γ.b = -1`, and keep `γ` otherwise. In particular, `positivelyOrient` is
idempotent on every curve, and for a simple closed curve (`γ.a ≠ γ.b`,
`InjOn γ (Ico (min γ.a γ.b) (max γ.a γ.b))`), `positivelyOrient γ` always has orientation
sign `1`. -/
def positivelyOrient (γ : AbsolutelyContinuousClosedCurve) : AbsolutelyContinuousClosedCurve :=
  if jordanSign γ γ.a γ.b = -1 then γ.symm else γ

/-- Defining formula for `AbsolutelyContinuousClosedCurve.positivelyOrient`. -/
theorem positivelyOrient_def (γ : AbsolutelyContinuousClosedCurve) :
    γ.positivelyOrient = if jordanSign γ γ.a γ.b = -1 then γ.symm else γ :=
  (rfl)

/-- A curve with `jordanSign = -1` is reversed by `positivelyOrient`. -/
@[simp]
theorem positivelyOrient_of_jordanSign_eq_neg_one {γ : AbsolutelyContinuousClosedCurve}
    (h : jordanSign γ γ.a γ.b = -1) : γ.positivelyOrient = γ.symm := by
  simp [positivelyOrient, h]

/-- A curve with `jordanSign ≠ -1` is unchanged by `positivelyOrient`. -/
theorem positivelyOrient_of_jordanSign_ne_neg_one {γ : AbsolutelyContinuousClosedCurve}
    (h : jordanSign γ γ.a γ.b ≠ -1) : γ.positivelyOrient = γ := by
  simp [positivelyOrient, h]

/-- A curve that already has `jordanSign = 1` is unchanged by `positivelyOrient`. -/
@[simp]
theorem positivelyOrient_of_jordanSign_eq_one {γ : AbsolutelyContinuousClosedCurve}
    (h : jordanSign γ γ.a γ.b = 1) : γ.positivelyOrient = γ :=
  positivelyOrient_of_jordanSign_ne_neg_one (by omega)

/-- `positivelyOrient` leaves the canonical extension to `ℝ` unchanged. -/
@[simp]
theorem coe_positivelyOrient (γ : AbsolutelyContinuousClosedCurve) :
    (γ.positivelyOrient : ℝ → ℂ) = γ := by
  by_cases h : jordanSign γ γ.a γ.b = -1
  · rw [positivelyOrient_of_jordanSign_eq_neg_one h, coe_symm]
  · rw [positivelyOrient_of_jordanSign_ne_neg_one h]

/-- `positivelyOrient` leaves the unordered parameter interval `uIcc` unchanged. -/
@[simp]
theorem uIcc_positivelyOrient (γ : AbsolutelyContinuousClosedCurve) :
    uIcc γ.positivelyOrient.a γ.positivelyOrient.b = uIcc γ.a γ.b := by
  by_cases h : jordanSign γ γ.a γ.b = -1
  · rw [positivelyOrient_of_jordanSign_eq_neg_one h, symm_a, symm_b, uIcc_comm]
  · rw [positivelyOrient_of_jordanSign_ne_neg_one h]

/-- Reversing a bundled closed absolutely continuous curve negates its `jordanSign`. -/
theorem jordanSign_symm (γ : AbsolutelyContinuousClosedCurve) :
    jordanSign γ.symm γ.symm.a γ.symm.b = -jordanSign γ γ.a γ.b := by
  simp only [coe_symm, symm_a, symm_b,
    γ.absolutelyContinuousOnInterval.jordanSign_symm]

/-- `positivelyOrient` is unconditionally idempotent. -/
@[simp]
theorem positivelyOrient_positivelyOrient (γ : AbsolutelyContinuousClosedCurve) :
    γ.positivelyOrient.positivelyOrient = γ.positivelyOrient := by
  by_cases h : jordanSign γ γ.a γ.b = -1
  · rw [positivelyOrient_of_jordanSign_eq_neg_one h]
    exact positivelyOrient_of_jordanSign_eq_one (by rw [jordanSign_symm, h, neg_neg])
  · rw [positivelyOrient_of_jordanSign_ne_neg_one h, positivelyOrient_of_jordanSign_ne_neg_one h]

/-- On any curve with nonzero `jordanSign`, `positivelyOrient` is invariant under orientation
reversal. -/
theorem positivelyOrient_symm {γ : AbsolutelyContinuousClosedCurve} (h : jordanSign γ γ.a γ.b ≠ 0) :
    γ.symm.positivelyOrient = γ.positivelyOrient := by
  rcases jordanSign_eq_one_or_neg_one_or_zero γ γ.a γ.b with h1 | h1 | h1
  · rw [positivelyOrient_of_jordanSign_eq_one h1,
      positivelyOrient_of_jordanSign_eq_neg_one (by rw [jordanSign_symm, h1]), symm_symm]
  · rw [positivelyOrient_of_jordanSign_eq_neg_one h1,
      positivelyOrient_of_jordanSign_eq_one (by rw [jordanSign_symm, h1, neg_neg])]
  · exact (h h1).elim

/-- `positivelyOrient` leaves the interval image unchanged. -/
theorem image_positivelyOrient (γ : AbsolutelyContinuousClosedCurve) :
    γ.positivelyOrient '' uIcc γ.positivelyOrient.a γ.positivelyOrient.b =
      γ '' uIcc γ.a γ.b := by
  simp

/-- Every simple closed absolutely continuous curve (`γ.a ≠ γ.b`,
`InjOn γ (Ico (min γ.a γ.b) (max γ.a γ.b))`) has nonzero `jordanSign`. -/
theorem jordanSign_ne_zero_of_ne {γ : AbsolutelyContinuousClosedCurve} (hab : γ.a ≠ γ.b)
    (hinj : InjOn γ (Ico (min γ.a γ.b) (max γ.a γ.b))) :
    jordanSign γ γ.a γ.b ≠ 0 :=
  induction_on_lt hab hinj (P := fun η ↦ jordanSign η η.a η.b ≠ 0)
    (fun {η} hlt hinj' ↦ η.absolutelyContinuousOnInterval.jordanSign_ne_zero
      hlt η.source_eq_target hinj')
    fun h ↦ by rwa [← neg_ne_zero, ← jordanSign_symm]

/-- After `positivelyOrient`, every curve with nonzero `jordanSign` has `jordanSign` equal to
`1`. -/
theorem jordanSign_positivelyOrient {γ : AbsolutelyContinuousClosedCurve}
    (h : jordanSign γ γ.a γ.b ≠ 0) :
    jordanSign γ.positivelyOrient γ.positivelyOrient.a γ.positivelyOrient.b = 1 := by
  rcases jordanSign_eq_one_or_neg_one_or_zero γ γ.a γ.b with h1 | h1 | h1
  · rwa [positivelyOrient_of_jordanSign_eq_one h1]
  · rw [positivelyOrient_of_jordanSign_eq_neg_one h1, jordanSign_symm, h1, neg_neg]
  · exact (h h1).elim

/-- A simple closed absolutely continuous curve (`γ.a ≠ γ.b`,
`InjOn γ (Ico (min γ.a γ.b) (max γ.a γ.b))`) has a Jordan curve as its interval image. -/
theorem isJordanCurve_image_of_ne (γ : AbsolutelyContinuousClosedCurve) (hab : γ.a ≠ γ.b)
    (hinj : InjOn γ (Ico (min γ.a γ.b) (max γ.a γ.b))) :
    TauCeti.IsJordanCurve (γ '' uIcc γ.a γ.b) :=
  induction_on_lt hab hinj (P := fun η ↦ TauCeti.IsJordanCurve (η '' uIcc η.a η.b))
    (fun {η} hlt hinj' ↦ η.absolutelyContinuousOnInterval.isJordanCurve_image_uIcc
      hlt η.source_eq_target hinj')
    fun h ↦ by rwa [← γ.image_symm]

end AbsolutelyContinuousClosedCurve

namespace Cycle

/-- `positivelyOrient` preserves the cycle trace of a generator. -/
theorem trace_of_positivelyOrient (γ : AbsolutelyContinuousClosedCurve) :
    trace (FreeAddCommGroup.of γ.positivelyOrient) = trace (FreeAddCommGroup.of γ) := by
  simp

/-- `positivelyOrient` preserves containment of a generator in any target set. -/
theorem isIn_of_positivelyOrient_iff {γ : AbsolutelyContinuousClosedCurve} {Ω : Set ℂ} :
    IsIn (FreeAddCommGroup.of γ.positivelyOrient) Ω ↔ IsIn (FreeAddCommGroup.of γ) Ω := by
  rw [isIn_iff, isIn_iff, trace_of_positivelyOrient]

/-- `positivelyOrient` preserves vanishing of a generator's cycle winding number. -/
theorem windingNumber_of_positivelyOrient_eq_zero_iff (γ : AbsolutelyContinuousClosedCurve)
    (z : ℂ) :
    windingNumber z (FreeAddCommGroup.of γ.positivelyOrient) = 0 ↔
      windingNumber z (FreeAddCommGroup.of γ) = 0 := by
  unfold AbsolutelyContinuousClosedCurve.positivelyOrient
  split_ifs
  · exact windingNumber_of_symm_eq_zero_iff γ z
  · rfl

/-- `positivelyOrient` preserves null-homology of a generator. -/
theorem isNullHomologous_of_positivelyOrient_iff {γ : AbsolutelyContinuousClosedCurve}
    {Ω : Set ℂ} :
    IsNullHomologous (FreeAddCommGroup.of γ.positivelyOrient) Ω ↔
      IsNullHomologous (FreeAddCommGroup.of γ) Ω := by
  simp only [isNullHomologous_iff, windingNumber_of_positivelyOrient_eq_zero_iff]

/-- Outside `filledHull (γ '' uIcc γ.a γ.b)`, the cycle winding number of `γ.positivelyOrient`
vanishes. -/
theorem windingNumber_of_positivelyOrient_eq_zero_of_notMem_filledHull
    (γ : AbsolutelyContinuousClosedCurve) {z : ℂ} (hz : z ∉ filledHull (γ '' uIcc γ.a γ.b)) :
    windingNumber z (FreeAddCommGroup.of γ.positivelyOrient) = 0 := by
  rw [windingNumber_of_positivelyOrient_eq_zero_iff, windingNumber_of]
  exact γ.absolutelyContinuousOnInterval.windingNumber_eq_zero_of_notMem_filledHull
    γ.source_eq_target hz

/-- For any curve with nonzero `jordanSign`, integrating over `γ.positivelyOrient` multiplies the
integral over `γ` by `jordanSign γ γ.a γ.b ∈ {1, -1}`. -/
theorem integral_of_positivelyOrient {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {γ : AbsolutelyContinuousClosedCurve} (h : jordanSign γ γ.a γ.b ≠ 0) (f : ℂ → E) :
    integral f (FreeAddCommGroup.of γ.positivelyOrient) =
      jordanSign γ γ.a γ.b • integral f (FreeAddCommGroup.of γ) := by
  rcases jordanSign_eq_one_or_neg_one_or_zero γ γ.a γ.b with h1 | h1 | h1
  · rw [AbsolutelyContinuousClosedCurve.positivelyOrient_of_jordanSign_eq_one h1, h1, one_smul]
  · rw [AbsolutelyContinuousClosedCurve.positivelyOrient_of_jordanSign_eq_neg_one h1,
      integral_of_symm, h1, neg_one_smul]
  · exact (h h1).elim

/-- Inside `filledHull (γ '' uIcc γ.a γ.b) \ (γ '' uIcc γ.a γ.b)`, any closed absolutely
continuous curve with nonzero `jordanSign` has cycle winding number `1` after
`positivelyOrient`. -/
theorem windingNumber_of_positivelyOrient_eq_one_of_mem_filledHull_sdiff
    {γ : AbsolutelyContinuousClosedCurve} (h : jordanSign γ γ.a γ.b ≠ 0) {z : ℂ}
    (hz : z ∈ filledHull (γ '' uIcc γ.a γ.b) \ (γ '' uIcc γ.a γ.b)) :
    windingNumber z (FreeAddCommGroup.of γ.positivelyOrient) = 1 := by
  rcases jordanSign_eq_one_or_neg_one_or_zero γ γ.a γ.b with h1 | h1 | h1
  · rw [AbsolutelyContinuousClosedCurve.positivelyOrient_of_jordanSign_eq_one h1,
      windingNumber_of, (jordanSign_eq_one_iff.mp h1).2 z hz]
  · rw [AbsolutelyContinuousClosedCurve.positivelyOrient_of_jordanSign_eq_neg_one h1,
      windingNumber_of_symm γ hz.2, windingNumber_of,
      (jordanSign_eq_neg_one_iff.mp h1).2 z hz, neg_neg]
  · exact (h h1).elim

end Cycle

/-! ### The oriented boundary cycle of a finitely connected Jordan region -/

section JordanBoundaryCycle

variable {ι : Type*}

/-- **Oriented boundary cycle of a finitely connected Jordan region.** Given an outer closed
absolutely continuous curve `γ₀` and a finite family `(γ i)_{i ∈ s}` of hole curves, each curve is
positively oriented via `AbsolutelyContinuousClosedCurve.positivelyOrient` and assembled into the
formal sum `[γ₀⁺] - ∑ i ∈ s, [γᵢ⁺]` in `TauCeti.Contour.Cycle`. For arbitrary inputs this is only
a formal cycle; it represents the geometric boundary when `γ₀` and the `γ i` (`i ∈ s`) are simple
closed curves and the hole filled hulls `filledHull (γ i '' uIcc (γ i).a (γ i).b)` are pairwise
disjoint and contained in the inside of `γ₀`. -/
def jordanBoundaryCycle (γ₀ : AbsolutelyContinuousClosedCurve) (s : Finset ι)
    (γ : ι → AbsolutelyContinuousClosedCurve) : Cycle :=
  FreeAddCommGroup.of γ₀.positivelyOrient - ∑ i ∈ s, FreeAddCommGroup.of (γ i).positivelyOrient

/-- Defining formula for `TauCeti.Contour.jordanBoundaryCycle`. -/
theorem jordanBoundaryCycle_def (γ₀ : AbsolutelyContinuousClosedCurve) (s : Finset ι)
    (γ : ι → AbsolutelyContinuousClosedCurve) :
    jordanBoundaryCycle γ₀ s γ =
      FreeAddCommGroup.of γ₀.positivelyOrient -
        ∑ i ∈ s, FreeAddCommGroup.of (γ i).positivelyOrient :=
  (rfl)

/-- With no holes (`s = ∅`), `jordanBoundaryCycle` is `[γ₀⁺]`. -/
@[simp]
theorem jordanBoundaryCycle_empty (γ₀ : AbsolutelyContinuousClosedCurve)
    (γ : ι → AbsolutelyContinuousClosedCurve) :
    jordanBoundaryCycle γ₀ ∅ γ = FreeAddCommGroup.of γ₀.positivelyOrient := by
  simp [jordanBoundaryCycle]

/-- Inserting a new hole subtracts its positively oriented generator from `jordanBoundaryCycle`. -/
@[simp]
theorem jordanBoundaryCycle_insert [DecidableEq ι] (γ₀ : AbsolutelyContinuousClosedCurve) {i : ι}
    {s : Finset ι} (hi : i ∉ s) (γ : ι → AbsolutelyContinuousClosedCurve) :
    jordanBoundaryCycle γ₀ (insert i s) γ =
      jordanBoundaryCycle γ₀ s γ - FreeAddCommGroup.of (γ i).positivelyOrient := by
  rw [jordanBoundaryCycle, jordanBoundaryCycle, Finset.sum_insert hi, sub_sub, add_comm]

/-- When `γ₀` and every `γ i` (`i ∈ s`) already have `jordanSign = 1`, `jordanBoundaryCycle` is
simply `[γ₀] - ∑ i ∈ s, [γ i]`. -/
theorem jordanBoundaryCycle_of_jordanSign_eq_one {γ₀ : AbsolutelyContinuousClosedCurve}
    {s : Finset ι} {γ : ι → AbsolutelyContinuousClosedCurve} (h₀ : jordanSign γ₀ γ₀.a γ₀.b = 1)
    (h : ∀ i ∈ s, jordanSign (γ i) (γ i).a (γ i).b = 1) :
    jordanBoundaryCycle γ₀ s γ =
      FreeAddCommGroup.of γ₀ - ∑ i ∈ s, FreeAddCommGroup.of (γ i) := by
  rw [jordanBoundaryCycle,
    AbsolutelyContinuousClosedCurve.positivelyOrient_of_jordanSign_eq_one h₀]
  exact congrArg _ (Finset.sum_congr rfl fun i hi ↦ by
    rw [AbsolutelyContinuousClosedCurve.positivelyOrient_of_jordanSign_eq_one (h i hi)])

/-- **Finitely connected Jordan region** bounded externally by `γ₀ '' uIcc γ₀.a γ₀.b` and
internally by the filled hulls of `γ i '' uIcc (γ i).a (γ i).b` (`i ∈ s`). When `γ₀` and the
`γ i` (`i ∈ s`) are simple closed curves whose hole filled hulls are pairwise disjoint and contained
in the inside of `γ₀`, this open set has oriented boundary cycle `jordanBoundaryCycle γ₀ s γ`. -/
def jordanRegion (γ₀ : AbsolutelyContinuousClosedCurve) (s : Finset ι)
    (γ : ι → AbsolutelyContinuousClosedCurve) : Set ℂ :=
  (filledHull (γ₀ '' uIcc γ₀.a γ₀.b) \ (γ₀ '' uIcc γ₀.a γ₀.b)) \
    ⋃ i ∈ s, filledHull (γ i '' uIcc (γ i).a (γ i).b)

/-- Defining formula for `TauCeti.Contour.jordanRegion`. -/
theorem jordanRegion_def (γ₀ : AbsolutelyContinuousClosedCurve) (s : Finset ι)
    (γ : ι → AbsolutelyContinuousClosedCurve) :
    jordanRegion γ₀ s γ =
      (filledHull (γ₀ '' uIcc γ₀.a γ₀.b) \ (γ₀ '' uIcc γ₀.a γ₀.b)) \
        ⋃ i ∈ s, filledHull (γ i '' uIcc (γ i).a (γ i).b) :=
  (rfl)

/-- Membership in `TauCeti.Contour.jordanRegion`. -/
theorem mem_jordanRegion_iff {γ₀ : AbsolutelyContinuousClosedCurve} {s : Finset ι}
    {γ : ι → AbsolutelyContinuousClosedCurve} {z : ℂ} :
    z ∈ jordanRegion γ₀ s γ ↔
      z ∈ filledHull (γ₀ '' uIcc γ₀.a γ₀.b) \ (γ₀ '' uIcc γ₀.a γ₀.b) ∧
        ∀ i ∈ s, z ∉ filledHull (γ i '' uIcc (γ i).a (γ i).b) := by
  simp only [jordanRegion, Set.mem_sdiff, mem_iUnion₂, not_exists]

/-- With no holes (`s = ∅`), `jordanRegion` is the inside of `γ₀`. -/
@[simp]
theorem jordanRegion_empty (γ₀ : AbsolutelyContinuousClosedCurve)
    (γ : ι → AbsolutelyContinuousClosedCurve) :
    jordanRegion γ₀ ∅ γ = filledHull (γ₀ '' uIcc γ₀.a γ₀.b) \ (γ₀ '' uIcc γ₀.a γ₀.b) := by
  simp [jordanRegion]

/-- Inserting a hole removes its filled hull from `jordanRegion`. -/
@[simp]
theorem jordanRegion_insert [DecidableEq ι] (γ₀ : AbsolutelyContinuousClosedCurve) (i : ι)
    (s : Finset ι) (γ : ι → AbsolutelyContinuousClosedCurve) :
    jordanRegion γ₀ (insert i s) γ =
      jordanRegion γ₀ s γ \ filledHull (γ i '' uIcc (γ i).a (γ i).b) := by
  ext z
  simp only [Set.mem_sdiff, mem_jordanRegion_iff, Finset.mem_insert, forall_eq_or_imp]
  tauto

/-- The region `jordanRegion γ₀ s γ` determined by closed absolutely continuous curves `γ₀` and
`γ i` (`i ∈ s`) is open. -/
theorem isOpen_jordanRegion {γ₀ : AbsolutelyContinuousClosedCurve} {s : Finset ι}
    {γ : ι → AbsolutelyContinuousClosedCurve} :
    IsOpen (jordanRegion γ₀ s γ) :=
  (isCompact_uIcc.image_of_continuousOn γ₀.continuousOn).isClosed.isOpen_filledHull_sdiff_biUnion
    s fun i _ ↦ (isCompact_uIcc.image_of_continuousOn (γ i).continuousOn).isClosed

/-- The region `jordanRegion γ₀ s γ` determined by closed absolutely continuous curves `γ₀` and
`γ i` (`i ∈ s`) is bounded. -/
theorem isBounded_jordanRegion {γ₀ : AbsolutelyContinuousClosedCurve} {s : Finset ι}
    {γ : ι → AbsolutelyContinuousClosedCurve} :
    IsBounded (jordanRegion γ₀ s γ) :=
  (isBounded_filledHull.mpr (isCompact_uIcc.image_of_continuousOn γ₀.continuousOn).isBounded).subset
    (sdiff_subset.trans sdiff_subset)

/-- **Closure identification for `jordanRegion`.** When `γ₀` and `γ i` (`i ∈ s`) are simple
closed curves whose filled hulls are pairwise disjoint and contained in the inside of `γ₀`, the
closure of `jordanRegion γ₀ s γ` is `filledHull (γ₀ '' uIcc γ₀.a γ₀.b)` minus the open hole
interiors `filledHull (γ i '' uIcc (γ i).a (γ i).b) \ (γ i '' uIcc (γ i).a (γ i).b)`. -/
theorem closure_jordanRegion {γ₀ : AbsolutelyContinuousClosedCurve} {s : Finset ι}
    {γ : ι → AbsolutelyContinuousClosedCurve} (hab₀ : γ₀.a ≠ γ₀.b)
    (hinj₀ : InjOn γ₀ (Ico (min γ₀.a γ₀.b) (max γ₀.a γ₀.b)))
    (hab : ∀ i ∈ s, (γ i).a ≠ (γ i).b)
    (hinj : ∀ i ∈ s, InjOn (γ i) (Ico (min (γ i).a (γ i).b) (max (γ i).a (γ i).b)))
    (hsub : ∀ i ∈ s, filledHull (γ i '' uIcc (γ i).a (γ i).b) ⊆
      filledHull (γ₀ '' uIcc γ₀.a γ₀.b) \ (γ₀ '' uIcc γ₀.a γ₀.b))
    (hdisj : (s : Set ι).PairwiseDisjoint fun i ↦ filledHull (γ i '' uIcc (γ i).a (γ i).b)) :
    closure (jordanRegion γ₀ s γ) =
      filledHull (γ₀ '' uIcc γ₀.a γ₀.b) \
        ⋃ i ∈ s, (filledHull (γ i '' uIcc (γ i).a (γ i).b) \ (γ i '' uIcc (γ i).a (γ i).b)) :=
  (γ₀.isJordanCurve_image_of_ne hab₀ hinj₀).closure_filledHull_sdiff_biUnion
    (fun i hi ↦ (γ i).isJordanCurve_image_of_ne (hab i hi) (hinj i hi)) hsub hdisj

namespace Cycle

/-- For curves with nonzero `jordanSign`, integrating over `jordanBoundaryCycle γ₀ s γ` combines
the `jordanSign`-weighted contour integrals of `γ₀` and of the hole curves `γ i` (`i ∈ s`). -/
theorem integral_jordanBoundaryCycle {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {γ₀ : AbsolutelyContinuousClosedCurve} {s : Finset ι}
    {γ : ι → AbsolutelyContinuousClosedCurve} (h₀ : jordanSign γ₀ γ₀.a γ₀.b ≠ 0)
    (h : ∀ i ∈ s, jordanSign (γ i) (γ i).a (γ i).b ≠ 0) (f : ℂ → E) :
    integral f (jordanBoundaryCycle γ₀ s γ) =
      jordanSign γ₀ γ₀.a γ₀.b • integral f (FreeAddCommGroup.of γ₀) -
        ∑ i ∈ s, jordanSign (γ i) (γ i).a (γ i).b • integral f (FreeAddCommGroup.of (γ i)) := by
  rw [jordanBoundaryCycle, map_sub, map_sum, integral_of_positivelyOrient h₀]
  exact congrArg _ (Finset.sum_congr rfl fun i hi ↦
    integral_of_positivelyOrient (h i hi) f)

variable {γ₀ : AbsolutelyContinuousClosedCurve} {s : Finset ι}
  {γ : ι → AbsolutelyContinuousClosedCurve}

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

/-- **Trace identification for `jordanBoundaryCycle`.** The trace of the oriented boundary cycle of
`jordanRegion γ₀ s γ` equals `frontier (jordanRegion γ₀ s γ)`. -/
theorem trace_jordanBoundaryCycle (hab₀ : γ₀.a ≠ γ₀.b)
    (hinj₀ : InjOn γ₀ (Ico (min γ₀.a γ₀.b) (max γ₀.a γ₀.b)))
    (hab : ∀ i ∈ s, (γ i).a ≠ (γ i).b)
    (hinj : ∀ i ∈ s, InjOn (γ i) (Ico (min (γ i).a (γ i).b) (max (γ i).a (γ i).b)))
    (hsub : ∀ i ∈ s, filledHull (γ i '' uIcc (γ i).a (γ i).b) ⊆
      filledHull (γ₀ '' uIcc γ₀.a γ₀.b) \ (γ₀ '' uIcc γ₀.a γ₀.b))
    (hdisj : (s : Set ι).PairwiseDisjoint fun i ↦ filledHull (γ i '' uIcc (γ i).a (γ i).b)) :
    trace (jordanBoundaryCycle γ₀ s γ) = frontier (jordanRegion γ₀ s γ) := by
  rw [trace_jordanBoundaryCycle_eq_union hsub, jordanRegion,
    (γ₀.isJordanCurve_image_of_ne hab₀ hinj₀).frontier_filledHull_sdiff_biUnion
      (fun i hi ↦ (γ i).isJordanCurve_image_of_ne (hab i hi) (hinj i hi)) hsub hdisj]

/-- Any point of `jordanRegion γ₀ s γ` lies off the trace of `jordanBoundaryCycle γ₀ s γ`. -/
theorem notMem_trace_jordanBoundaryCycle_of_mem {z : ℂ} (hz : z ∈ jordanRegion γ₀ s γ) :
    z ∉ trace (jordanBoundaryCycle γ₀ s γ) := by
  intro htr
  rw [mem_jordanRegion_iff] at hz
  rw [jordanBoundaryCycle] at htr
  rcases trace_sub_subset _ _ htr with h₀ | hi
  · rw [trace_of, AbsolutelyContinuousClosedCurve.image_positivelyOrient] at h₀
    exact hz.1.2 h₀
  · obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp (trace_sum_subset s _ hi)
    rw [trace_of, AbsolutelyContinuousClosedCurve.image_positivelyOrient] at hzi
    exact hz.2 i hi (subset_filledHull hzi)

open scoped Classical in
/-- **Winding-number adapter for `jordanBoundaryCycle`.** Off its trace
`frontier (jordanRegion γ₀ s γ)`, the oriented boundary cycle of `jordanRegion γ₀ s γ` has winding
number `1` on `jordanRegion γ₀ s γ` and `0` everywhere else. -/
theorem windingNumber_jordanBoundaryCycle (hab₀ : γ₀.a ≠ γ₀.b)
    (hinj₀ : InjOn γ₀ (Ico (min γ₀.a γ₀.b) (max γ₀.a γ₀.b)))
    (hab : ∀ i ∈ s, (γ i).a ≠ (γ i).b)
    (hinj : ∀ i ∈ s, InjOn (γ i) (Ico (min (γ i).a (γ i).b) (max (γ i).a (γ i).b)))
    (hsub : ∀ i ∈ s, filledHull (γ i '' uIcc (γ i).a (γ i).b) ⊆
      filledHull (γ₀ '' uIcc γ₀.a γ₀.b) \ (γ₀ '' uIcc γ₀.a γ₀.b))
    (hdisj : (s : Set ι).PairwiseDisjoint fun i ↦ filledHull (γ i '' uIcc (γ i).a (γ i).b))
    {z : ℂ} (hz : z ∉ trace (jordanBoundaryCycle γ₀ s γ)) :
    windingNumber z (jordanBoundaryCycle γ₀ s γ) =
      if z ∈ jordanRegion γ₀ s γ then 1 else 0 := by
  rw [trace_jordanBoundaryCycle_eq_union hsub] at hz
  rw [jordanBoundaryCycle, map_sub, map_sum]
  split_ifs with hzΔ
  · rw [windingNumber_of_positivelyOrient_eq_one_of_mem_filledHull_sdiff
          (AbsolutelyContinuousClosedCurve.jordanSign_ne_zero_of_ne hab₀ hinj₀) hzΔ.1,
      Finset.sum_eq_zero fun i hi ↦
        windingNumber_of_positivelyOrient_eq_zero_of_notMem_filledHull (γ i)
          (fun h ↦ hzΔ.2 (mem_iUnion₂.mpr ⟨i, hi, h⟩)), sub_zero]
  · by_cases hzF₀ : z ∈ filledHull (γ₀ '' uIcc γ₀.a γ₀.b)
    · obtain ⟨i, hi, hzFi⟩ := mem_iUnion₂.mp
        (by_contra fun h ↦ hzΔ ⟨⟨hzF₀, fun h₀ ↦ hz (Or.inl h₀)⟩, h⟩)
      rw [windingNumber_of_positivelyOrient_eq_one_of_mem_filledHull_sdiff
            (AbsolutelyContinuousClosedCurve.jordanSign_ne_zero_of_ne hab₀ hinj₀)
            ⟨hzF₀, fun h₀ ↦ hz (Or.inl h₀)⟩,
        Finset.sum_eq_single i (fun j hj hji ↦
            windingNumber_of_positivelyOrient_eq_zero_of_notMem_filledHull (γ j)
              (Set.disjoint_left.mp (hdisj hi hj hji.symm) hzFi))
          (fun hnot ↦ (hnot hi).elim),
        windingNumber_of_positivelyOrient_eq_one_of_mem_filledHull_sdiff
          (AbsolutelyContinuousClosedCurve.jordanSign_ne_zero_of_ne (hab i hi) (hinj i hi))
          ⟨hzFi, fun h ↦ hz (Or.inr (mem_iUnion₂.mpr ⟨i, hi, h⟩))⟩, sub_self]
    · rw [windingNumber_of_positivelyOrient_eq_zero_of_notMem_filledHull γ₀ hzF₀,
        Finset.sum_eq_zero fun i hi ↦
          windingNumber_of_positivelyOrient_eq_zero_of_notMem_filledHull (γ i)
            (fun h ↦ hzF₀ (hsub i hi h).1), sub_zero]

/-- The trace-zero real `windingWeight` of `jordanBoundaryCycle γ₀ s γ` is the indicator of
`jordanRegion γ₀ s γ`. -/
theorem windingWeight_jordanBoundaryCycle (hab₀ : γ₀.a ≠ γ₀.b)
    (hinj₀ : InjOn γ₀ (Ico (min γ₀.a γ₀.b) (max γ₀.a γ₀.b)))
    (hab : ∀ i ∈ s, (γ i).a ≠ (γ i).b)
    (hinj : ∀ i ∈ s, InjOn (γ i) (Ico (min (γ i).a (γ i).b) (max (γ i).a (γ i).b)))
    (hsub : ∀ i ∈ s, filledHull (γ i '' uIcc (γ i).a (γ i).b) ⊆
      filledHull (γ₀ '' uIcc γ₀.a γ₀.b) \ (γ₀ '' uIcc γ₀.a γ₀.b))
    (hdisj : (s : Set ι).PairwiseDisjoint fun i ↦ filledHull (γ i '' uIcc (γ i).a (γ i).b)) :
    (jordanBoundaryCycle γ₀ s γ).windingWeight = (jordanRegion γ₀ s γ).indicator 1 := by
  classical
  ext z
  by_cases htr : z ∈ trace (jordanBoundaryCycle γ₀ s γ)
  · rw [windingWeight_eq_zero_of_mem _ htr,
      indicator_of_notMem fun hzΔ ↦ notMem_trace_jordanBoundaryCycle_of_mem hzΔ htr]
  · rw [windingWeight_eq_of_notMem _ htr,
      windingNumber_jordanBoundaryCycle hab₀ hinj₀ hab hinj hsub hdisj htr]
    by_cases hzΔ : z ∈ jordanRegion γ₀ s γ <;> simp [hzΔ]

/-- Whenever `closure (jordanRegion γ₀ s γ) ⊆ Ω`, the trace of `jordanBoundaryCycle γ₀ s γ` lies in
`Ω`. -/
theorem isIn_jordanBoundaryCycle {Ω : Set ℂ} (hab₀ : γ₀.a ≠ γ₀.b)
    (hinj₀ : InjOn γ₀ (Ico (min γ₀.a γ₀.b) (max γ₀.a γ₀.b)))
    (hab : ∀ i ∈ s, (γ i).a ≠ (γ i).b)
    (hinj : ∀ i ∈ s, InjOn (γ i) (Ico (min (γ i).a (γ i).b) (max (γ i).a (γ i).b)))
    (hsub : ∀ i ∈ s, filledHull (γ i '' uIcc (γ i).a (γ i).b) ⊆
      filledHull (γ₀ '' uIcc γ₀.a γ₀.b) \ (γ₀ '' uIcc γ₀.a γ₀.b))
    (hdisj : (s : Set ι).PairwiseDisjoint fun i ↦ filledHull (γ i '' uIcc (γ i).a (γ i).b))
    (hΩ : closure (jordanRegion γ₀ s γ) ⊆ Ω) :
    IsIn (jordanBoundaryCycle γ₀ s γ) Ω := by
  rw [isIn_iff, trace_jordanBoundaryCycle hab₀ hinj₀ hab hinj hsub hdisj]
  exact frontier_subset_closure.trans hΩ

/-- Whenever `closure (jordanRegion γ₀ s γ) ⊆ Ω`, `jordanBoundaryCycle γ₀ s γ` is null-homologous
in `Ω`. -/
theorem isNullHomologous_jordanBoundaryCycle {Ω : Set ℂ} (hab₀ : γ₀.a ≠ γ₀.b)
    (hinj₀ : InjOn γ₀ (Ico (min γ₀.a γ₀.b) (max γ₀.a γ₀.b)))
    (hab : ∀ i ∈ s, (γ i).a ≠ (γ i).b)
    (hinj : ∀ i ∈ s, InjOn (γ i) (Ico (min (γ i).a (γ i).b) (max (γ i).a (γ i).b)))
    (hsub : ∀ i ∈ s, filledHull (γ i '' uIcc (γ i).a (γ i).b) ⊆
      filledHull (γ₀ '' uIcc γ₀.a γ₀.b) \ (γ₀ '' uIcc γ₀.a γ₀.b))
    (hdisj : (s : Set ι).PairwiseDisjoint fun i ↦ filledHull (γ i '' uIcc (γ i).a (γ i).b))
    (hΩ : closure (jordanRegion γ₀ s γ) ⊆ Ω) :
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
