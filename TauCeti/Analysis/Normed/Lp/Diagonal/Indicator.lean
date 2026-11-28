/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarProjection
public import TauCeti.Analysis.Normed.Lp.Diagonal.Basic
public import TauCeti.Analysis.Normed.Lp.Diagonal.Positive

/-!
# Indicator multipliers and coordinate projections on `ℓᵖ`

A subset `s : Set ι` defines a bounded indicator sequence `lp.indicator 𝕜 s : ℓ^∞(ι, 𝕜)` taking the
value `1` on `s` and `0` on `sᶜ`, and its diagonal multiplier
`lp.indicatorCLM p 𝕜 s : ℓ^p(ι, 𝕜) →L[𝕜] ℓ^p(ι, 𝕜)` restricts sequences to `s`.

Over `RCLike 𝕜`, `lp.indicatorCLM 2 𝕜 s` is an orthogonal projection (`IsStarProjection`) on
`ℓ²(ι, 𝕜)`, projections on disjoint sets have product `0`, and `lp.indicatorCLM 2 𝕜 sᶜ` is the
complementary projection `1 - lp.indicatorCLM 2 𝕜 s`.

## Main definitions

* `lp.indicator 𝕜 s`: the indicator sequence of `s` in `ℓ^∞(ι, 𝕜)`.
* `lp.indicatorCLM p 𝕜 s`: coordinate restriction to `s` on `ℓ^p(ι, 𝕜)`.

## Main results

* `lp.norm_indicator_of_nonempty`, `lp.norm_indicatorCLM_of_nonempty`: the norm of a nonempty
  indicator multiplier is `1`.
* `lp.indicator_mul`, `lp.indicatorCLM_mul`: indicators multiply by intersecting their sets,
  yielding `lp.indicatorCLM_mul_of_disjoint` for disjoint sets.
* `lp.indicatorCLM_compl`: the indicator of `sᶜ` is `1 - lp.indicatorCLM p 𝕜 s`.
* `lp.isStarProjection_indicatorCLM`: on `ℓ²`, `lp.indicatorCLM 2 𝕜 s` is a star projection.
-/

public section

open scoped lp ENNReal ComplexOrder

namespace lp

section Indicator

variable {ι : Type*}

/-- The bounded indicator sequence of a set `s : Set ι` in `ℓ^∞(ι, 𝕜)`, taking the value `1` on
`s` and `0` elsewhere. -/
noncomputable def indicator (𝕜 : Type*) [NormedAddCommGroup 𝕜] [One 𝕜] (s : Set ι) :
    ℓ^∞(ι, 𝕜) :=
  ⟨s.indicator (fun _ ↦ (1 : 𝕜)),
    memℓp_infty ⟨‖(1 : 𝕜)‖, by
      rintro _ ⟨i, rfl⟩
      classical
      by_cases hi : i ∈ s <;> simp [hi]⟩⟩

variable {𝕜 : Type*} [NormedAddCommGroup 𝕜] [One 𝕜] {s : Set ι}

/-- The underlying function of `indicator 𝕜 s` is `s.indicator (fun _ ↦ 1)`. -/
@[simp]
theorem coeFn_indicator : ⇑(indicator 𝕜 s) = s.indicator (fun _ ↦ (1 : 𝕜)) :=
  (rfl)

/-- Evaluating `indicator 𝕜 s` at `i` gives `s.indicator (fun _ ↦ 1) i`. -/
@[simp]
theorem indicator_apply (i : ι) : indicator 𝕜 s i = s.indicator (fun _ ↦ (1 : 𝕜)) i :=
  (rfl)

/-- On `i ∈ s`, `indicator 𝕜 s i` equals `1`. -/
theorem indicator_apply_mem {i : ι} (hi : i ∈ s) : indicator 𝕜 s i = 1 := by
  rw [indicator_apply, Set.indicator_of_mem hi]

/-- On `i ∉ s`, `indicator 𝕜 s i` equals `0`. -/
theorem indicator_apply_notMem {i : ι} (hi : i ∉ s) : indicator 𝕜 s i = 0 := by
  rw [indicator_apply, Set.indicator_of_notMem hi]

/-- The indicator sequence of the empty set is `0`. -/
@[simp]
theorem indicator_empty : indicator 𝕜 (∅ : Set ι) = 0 := by
  ext i
  simp

/-- The supremum norm of an indicator sequence is at most `1`. -/
@[simp]
theorem norm_indicator_le_one [NormOneClass 𝕜] : ‖indicator 𝕜 s‖ ≤ 1 := by
  refine norm_le_of_forall_le zero_le_one fun i ↦ ?_
  classical
  by_cases hi : i ∈ s <;> simp [hi]

/-- The supremum norm of the indicator sequence of a nonempty set is `1`. -/
theorem norm_indicator_of_nonempty [NormOneClass 𝕜] (hs : s.Nonempty) : ‖indicator 𝕜 s‖ = 1 := by
  refine le_antisymm norm_indicator_le_one ?_
  obtain ⟨i, hi⟩ := hs
  calc (1 : ℝ) = ‖indicator 𝕜 s i‖ := by rw [indicator_apply_mem hi, norm_one]
    _ ≤ ‖indicator 𝕜 s‖ := norm_apply_le_norm ENNReal.top_ne_zero _ i

end Indicator

section IndicatorRing

variable {ι 𝕜 : Type*} [NormedRing 𝕜] {s : Set ι}

/-- The product of indicator sequences is the indicator sequence of the intersection. -/
@[simp]
theorem indicator_mul (t : Set ι) : indicator 𝕜 s * indicator 𝕜 t = indicator 𝕜 (s ∩ t) := by
  ext i
  classical
  by_cases his : i ∈ s <;> by_cases hit : i ∈ t <;> simp [lp.infty_coeFn_mul, his, hit]

/-- Indicator sequences are idempotent under multiplication. -/
theorem indicator_mul_self : indicator 𝕜 s * indicator 𝕜 s = indicator 𝕜 s := by
  rw [indicator_mul, Set.inter_self]

/-- The product of indicator sequences of disjoint sets is `0`. -/
theorem indicator_mul_of_disjoint {t : Set ι} (hst : Disjoint s t) :
    indicator 𝕜 s * indicator 𝕜 t = 0 := by
  rw [indicator_mul, hst.inter_eq, indicator_empty]

section NormOneClass

variable [NormOneClass 𝕜]

/-- The indicator sequence of `Set.univ` is `1`. -/
@[simp]
theorem indicator_univ : indicator 𝕜 (Set.univ : Set ι) = 1 := by
  ext i
  simp [lp.infty_coeFn_one]

/-- The indicator sequence of `sᶜ` is `1 - indicator 𝕜 s`. -/
theorem indicator_compl : indicator 𝕜 sᶜ = 1 - indicator 𝕜 s := by
  ext i
  rw [lp.coeFn_sub, Pi.sub_apply, lp.infty_coeFn_one]
  by_cases hi : i ∈ s <;> simp [hi]

end NormOneClass

end IndicatorRing

section IndicatorCLM

variable {ι : Type*}

/-- The bounded coordinate-restriction operator on `ℓ^p(ι, 𝕜)` associated to a set `s : Set ι`. -/
noncomputable def indicatorCLM (p : ℝ≥0∞) [Fact (1 ≤ p)] (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (s : Set ι) : ℓ^p(ι, 𝕜) →L[𝕜] ℓ^p(ι, 𝕜) :=
  diagonalCLM (indicator 𝕜 s)

/-- Unfolding lemma for `indicatorCLM`. -/
theorem indicatorCLM_def (p : ℝ≥0∞) [Fact (1 ≤ p)] (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (s : Set ι) : indicatorCLM p 𝕜 s = diagonalCLM (indicator 𝕜 s) :=
  (rfl)

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {𝕜 : Type*} [NontriviallyNormedField 𝕜] {s : Set ι}

/-- Coordinate restriction multiplies coordinates by `s.indicator`. -/
@[simp]
theorem indicatorCLM_apply (x : ℓ^p(ι, 𝕜)) (i : ι) :
    indicatorCLM p 𝕜 s x i = s.indicator (⇑x) i := by
  by_cases hi : i ∈ s <;> simp [indicatorCLM_def, hi]

/-- On `i ∈ s`, `indicatorCLM p 𝕜 s x i` equals `x i`. -/
theorem indicatorCLM_apply_mem (x : ℓ^p(ι, 𝕜)) {i : ι} (hi : i ∈ s) :
    indicatorCLM p 𝕜 s x i = x i := by
  simp [hi]

/-- On `i ∉ s`, `indicatorCLM p 𝕜 s x i` equals `0`. -/
theorem indicatorCLM_apply_notMem (x : ℓ^p(ι, 𝕜)) {i : ι} (hi : i ∉ s) :
    indicatorCLM p 𝕜 s x i = 0 := by
  simp [hi]

/-- Evaluating `indicatorCLM p 𝕜 s` on a coordinate basis vector `lp.single p i a`. -/
@[simp]
theorem indicatorCLM_single [DecidableEq ι] (i : ι) (a : 𝕜) :
    indicatorCLM p 𝕜 s (lp.single p i a) = s.indicator (fun j ↦ lp.single p j a) i := by
  by_cases hi : i ∈ s <;> simp [indicatorCLM_def, hi]

/-- The indicator operator of the empty set is `0`. -/
@[simp]
theorem indicatorCLM_empty : indicatorCLM p 𝕜 (∅ : Set ι) = 0 := by
  simp [indicatorCLM_def]

/-- The indicator operator of `Set.univ` is the identity operator. -/
@[simp]
theorem indicatorCLM_univ :
    indicatorCLM p 𝕜 (Set.univ : Set ι) = ContinuousLinearMap.id 𝕜 ℓ^p(ι, 𝕜) := by
  simp [indicatorCLM_def]

/-- Indicator operators compose by intersecting their sets. -/
@[simp]
theorem indicatorCLM_mul (t : Set ι) :
    indicatorCLM p 𝕜 s * indicatorCLM p 𝕜 t = indicatorCLM p 𝕜 (s ∩ t) := by
  rw [indicatorCLM_def, indicatorCLM_def, ContinuousLinearMap.mul_def, ← diagonalCLM_mul,
    indicator_mul, ← indicatorCLM_def]

/-- Indicator operators are idempotent. -/
theorem indicatorCLM_mul_self :
    indicatorCLM p 𝕜 s * indicatorCLM p 𝕜 s = indicatorCLM p 𝕜 s := by
  rw [indicatorCLM_mul, Set.inter_self]

/-- Indicator operators of disjoint sets compose to `0`. -/
theorem indicatorCLM_mul_of_disjoint {t : Set ι} (hst : Disjoint s t) :
    indicatorCLM p 𝕜 s * indicatorCLM p 𝕜 t = 0 := by
  rw [indicatorCLM_mul, hst.inter_eq, indicatorCLM_empty]

/-- The indicator operator of `sᶜ` is `1 - indicatorCLM p 𝕜 s`. -/
theorem indicatorCLM_compl :
    indicatorCLM p 𝕜 sᶜ = 1 - indicatorCLM p 𝕜 s := by
  ext x i
  by_cases hi : i ∈ s <;> simp [hi]

/-- The operator norm of an indicator multiplier is at most `1`. -/
@[simp]
theorem norm_indicatorCLM_le_one : ‖indicatorCLM p 𝕜 s‖ ≤ 1 := by
  rw [indicatorCLM_def, norm_diagonalCLM]
  exact norm_indicator_le_one

/-- The operator norm of the indicator multiplier of a nonempty set is `1`. -/
theorem norm_indicatorCLM_of_nonempty (hs : s.Nonempty) : ‖indicatorCLM p 𝕜 s‖ = 1 := by
  rw [indicatorCLM_def, norm_diagonalCLM]
  exact norm_indicator_of_nonempty hs

end IndicatorCLM

section Hilbert

variable {ι : Type*} (𝕜 : Type*) [RCLike 𝕜] (s : Set ι)

/-- Coordinate restriction to `s` on `ℓ²(ι, 𝕜)` is self-adjoint. -/
theorem isSelfAdjoint_indicatorCLM : IsSelfAdjoint (indicatorCLM 2 𝕜 s) := by
  rw [indicatorCLM_def, isSelfAdjoint_diagonalCLM_iff]
  intro i
  by_cases hi : i ∈ s <;> simp [hi]

/-- Coordinate restriction to `s` on `ℓ²(ι, 𝕜)` is a star projection. -/
theorem isStarProjection_indicatorCLM : IsStarProjection (indicatorCLM 2 𝕜 s) where
  isIdempotentElem := indicatorCLM_mul_self
  isSelfAdjoint := isSelfAdjoint_indicatorCLM 𝕜 s

/-- Coordinate restriction to `s` on `ℓ²(ι, 𝕜)` is a positive operator. -/
theorem isPositive_indicatorCLM : (indicatorCLM 2 𝕜 s).IsPositive := by
  rw [indicatorCLM_def, isPositive_diagonalCLM_iff]
  intro i
  by_cases hi : i ∈ s <;> simp [hi]

end Hilbert

end lp
