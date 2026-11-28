/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Order.Filter.AtTopBot.Basic
import TauCeti.Algebra.GroupWithZero.Action.Units
import TauCeti.Analysis.Normed.Ring.Units

/-!
# Stable sequences and condition numbers in normed rings

A sequence `aₙ` of elements of normed rings is *stable* (`TauCeti.IsStableSequence`) when its
members are eventually invertible and their inverses are uniformly bounded in norm. This is the
notion that governs approximation methods such as the finite-section method: a stable sequence of
approximating matrices has uniformly bounded condition numbers
`κ(aₙ) = ‖aₙ‖ ‖aₙ⁻¹‖` (`TauCeti.conditionNumber`) as soon as its norms are bounded.

Stability is invariant under `star`. The operator-level characterization of stability by
uniform lower bounds is in `TauCeti.Analysis.Normed.Operator.StableSequence`.

## Main definitions

* `TauCeti.conditionNumber a`: the condition number `‖a‖ ‖a⁻¹‖`, with value `0` at a non-unit.
* `TauCeti.IsStableSequence a`: eventual invertibility with uniformly bounded inverse norms.

## Main results

* `TauCeti.one_le_conditionNumber`: units have condition number at least one.
* `TauCeti.conditionNumber_ringInverse`, `TauCeti.conditionNumber_star`,
  `TauCeti.conditionNumber_smul`, `TauCeti.conditionNumber_mul_le`: algebraic laws for the
  condition number.
* `TauCeti.IsStableSequence.exists_conditionNumber_le`: a bounded stable sequence has uniformly
  bounded condition numbers.
* `TauCeti.isStableSequence_star_iff`: a sequence in normed star rings is stable exactly when the
  sequence of its stars is.
* `TauCeti.isStableSequence_iff_of_tendsto_sub_zero`: in normed rings with summable geometric
  series, stability is invariant under perturbations tending to zero in norm.

## References

* A. Böttcher, *C\*-Algebras in Numerical Analysis*, Irish Math. Soc. Bull. 45 (2000), 57–101,
  Sections 1 and 7.
* A. Böttcher and B. Silbermann, *Introduction to Large Truncated Toeplitz Matrices*,
  Section 1.4, for stability of approximating sequences.
* R. Hagen, S. Roch and B. Silbermann, *C\*-Algebras and Numerical Analysis*, Section 1.2.
-/

public section

open Filter Topology

namespace TauCeti

section ConditionNumber

variable {R : Type*} [NormedRing R]

/-- The condition number `‖a‖ ‖a⁻¹‖` of an element of a normed ring. Since `Ring.inverse` sends
non-units to zero, a non-unit has condition number `0`. -/
noncomputable def conditionNumber (a : R) : ℝ :=
  ‖a‖ * ‖Ring.inverse a‖

theorem conditionNumber_def (a : R) : conditionNumber a = ‖a‖ * ‖Ring.inverse a‖ := (rfl)

theorem conditionNumber_nonneg (a : R) : 0 ≤ conditionNumber a :=
  mul_nonneg (norm_nonneg _) (norm_nonneg _)

@[simp]
theorem conditionNumber_of_not_isUnit {a : R} (ha : ¬IsUnit a) : conditionNumber a = 0 := by
  simp [conditionNumber, Ring.inverse_non_unit a ha]

@[simp]
theorem conditionNumber_one [NormOneClass R] : conditionNumber (1 : R) = 1 := by
  simp [conditionNumber]

/-- A unit of a normed ring with `‖1‖ = 1` has condition number at least one. -/
theorem one_le_conditionNumber [NormOneClass R] {a : R} (ha : IsUnit a) :
    1 ≤ conditionNumber a := by
  calc
    (1 : ℝ) = ‖a * Ring.inverse a‖ := by rw [Ring.mul_inverse_cancel a ha, norm_one]
    _ ≤ conditionNumber a := norm_mul_le _ _

/-- Inversion preserves the condition number. -/
@[simp]
theorem conditionNumber_ringInverse (a : R) :
    conditionNumber (Ring.inverse a) = conditionNumber a := by
  by_cases ha : IsUnit a
  · simp [conditionNumber, Ring.inverse_inverse ha, mul_comm]
  · simp [conditionNumber, Ring.inverse_non_unit a ha]

/-- The star operation preserves the condition number in a normed star ring. -/
@[simp]
theorem conditionNumber_star [StarRing R] [NormedStarGroup R] (a : R) :
    conditionNumber (star a) = conditionNumber a := by
  simp [conditionNumber, Ring.inverse_star]

/-- Scaling by a nonzero scalar over a normed field leaves the condition number unchanged. -/
theorem conditionNumber_smul {𝕜 : Type*} [NormedField 𝕜] [Module 𝕜 R] [NormSMulClass 𝕜 R]
    [IsScalarTower 𝕜 R R] [SMulCommClass 𝕜 R R] {c : 𝕜} (hc : c ≠ 0) (a : R) :
    conditionNumber (c • a) = conditionNumber a := by
  have hcn : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  rw [conditionNumber, ringInverse_smul, norm_smul, norm_smul, norm_inv, conditionNumber]
  field_simp [hcn]

/-- Submultiplicativity of the condition number when at least one factor is a unit. In a
noncommutative ring, some unit hypothesis is needed: a unilateral shift and its adjoint can satisfy
`a * b = 1` with neither factor invertible, giving `conditionNumber (a * b) = 1` while both factor
condition numbers vanish. -/
theorem conditionNumber_mul_le {a b : R} (h : IsUnit a ∨ IsUnit b) :
    conditionNumber (a * b) ≤ conditionNumber a * conditionNumber b := by
  rw [conditionNumber, Ring.inverse_mul h]
  calc
    ‖a * b‖ * ‖Ring.inverse b * Ring.inverse a‖ ≤
        (‖a‖ * ‖b‖) * (‖Ring.inverse b‖ * ‖Ring.inverse a‖) :=
      mul_le_mul (norm_mul_le _ _) (norm_mul_le _ _) (norm_nonneg _)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = conditionNumber a * conditionNumber b := by
      simp only [conditionNumber]
      ring

end ConditionNumber

section StableSequence

variable {R : ℕ → Type*} [∀ n, NormedRing (R n)]

/-- A sequence `aₙ` in normed rings is *stable* when, for all sufficiently large `n`, `aₙ` is
invertible and the norms `‖aₙ⁻¹‖` are bounded uniformly in `n`. -/
def IsStableSequence (a : ∀ n, R n) : Prop :=
  ∃ M : ℝ, ∀ᶠ n in atTop, IsUnit (a n) ∧ ‖Ring.inverse (a n)‖ ≤ M

theorem isStableSequence_def (a : ∀ n, R n) :
    IsStableSequence a ↔ ∃ M : ℝ, ∀ᶠ n in atTop, IsUnit (a n) ∧ ‖Ring.inverse (a n)‖ ≤ M :=
  (Iff.rfl)

/-- The members of a stable sequence are eventually invertible. -/
theorem IsStableSequence.eventually_isUnit {a : ∀ n, R n} (ha : IsStableSequence a) :
    ∀ᶠ n in atTop, IsUnit (a n) := by
  obtain ⟨M, hM⟩ := ha
  exact hM.mono fun _ h ↦ h.1

/-- Stability depends only on the tail of the sequence: changing finitely many initial terms
leaves stability unchanged. -/
theorem IsStableSequence.congr {a b : ∀ n, R n} (ha : IsStableSequence a)
    (h : ∀ᶠ n in atTop, a n = b n) : IsStableSequence b := by
  obtain ⟨M, hM⟩ := ha
  exact ⟨M, (hM.and h).mono fun _ ⟨hn, hab⟩ ↦ hab ▸ hn⟩

/-- Sequences that agree eventually are simultaneously stable or unstable. -/
theorem isStableSequence_congr {a b : ∀ n, R n} (h : ∀ᶠ n in atTop, a n = b n) :
    IsStableSequence a ↔ IsStableSequence b :=
  ⟨fun ha ↦ ha.congr h, fun hb ↦ hb.congr (h.mono fun _ hn ↦ hn.symm)⟩

/-- Coordinatewise products of stable sequences are stable. -/
theorem IsStableSequence.mul {a b : ∀ n, R n} (ha : IsStableSequence a) (hb : IsStableSequence b) :
    IsStableSequence (fun n ↦ a n * b n) := by
  obtain ⟨M₁, hM₁⟩ := ha
  obtain ⟨M₂, hM₂⟩ := hb
  refine ⟨M₂ * M₁, (hM₁.and hM₂).mono fun n ⟨⟨hua, hna⟩, ⟨hub, hnb⟩⟩ ↦ ⟨hua.mul hub, ?_⟩⟩
  rw [Ring.inverse_mul (.inl hua)]
  exact (norm_mul_le _ _).trans (mul_le_mul hnb hna (norm_nonneg _) ((norm_nonneg _).trans hnb))

/-- A stable sequence whose norms are eventually bounded has eventually bounded condition
numbers. -/
theorem IsStableSequence.exists_conditionNumber_le {a : ∀ n, R n} (ha : IsStableSequence a)
    {C : ℝ} (hC : ∀ᶠ n in atTop, ‖a n‖ ≤ C) :
    ∃ K : ℝ, ∀ᶠ n in atTop, conditionNumber (a n) ≤ K := by
  obtain ⟨M, hM⟩ := ha
  refine ⟨C * M, (hM.and hC).mono fun n ⟨⟨_, hn⟩, hCn⟩ ↦ ?_⟩
  exact mul_le_mul hCn hn (norm_nonneg _) ((norm_nonneg _).trans hCn)

/-- A sequence in normed star rings is stable exactly when the sequence of its stars is. -/
@[simp]
theorem isStableSequence_star_iff [∀ n, StarRing (R n)] [∀ n, NormedStarGroup (R n)]
    {a : ∀ n, R n} : IsStableSequence (fun n ↦ star (a n)) ↔ IsStableSequence a := by
  simp only [IsStableSequence, isUnit_star, Ring.inverse_star, norm_star]

/-- In normed rings with summable geometric series (in particular, complete normed rings), a
perturbation whose norm tends to zero preserves stability. -/
theorem IsStableSequence.of_tendsto_sub_zero [∀ n, HasSummableGeomSeries (R n)] {a b : ∀ n, R n}
    (ha : IsStableSequence a) (hab : Tendsto (fun n ↦ ‖b n - a n‖) atTop (𝓝 0)) :
    IsStableSequence b := by
  obtain ⟨M, hM⟩ := ha
  set M' : ℝ := max M 1
  have hM' : 0 < M' := by positivity
  have hd : ∀ᶠ n in atTop, ‖b n - a n‖ < (2 * M')⁻¹ :=
    (tendsto_order.mp hab).2 _ (by positivity)
  refine ⟨2 * M', (hM.and hd).mono fun n ⟨⟨hu, hn⟩, hdn⟩ ↦ ?_⟩
  have hinv : ‖Ring.inverse (a n)‖ ≤ M' := hn.trans (le_max_left M 1)
  have hmul : ‖a n - b n‖ * ‖Ring.inverse (a n)‖ < 1 / 2 := by
    rw [norm_sub_rev]
    calc
      ‖b n - a n‖ * ‖Ring.inverse (a n)‖ ≤ ‖b n - a n‖ * M' :=
        mul_le_mul_of_nonneg_left hinv (norm_nonneg _)
      _ < (2 * M')⁻¹ * M' := mul_lt_mul_of_pos_right hdn hM'
      _ = 1 / 2 := by field_simp
  have hr : ‖1 - b n * Ring.inverse (a n)‖ < 1 / 2 := by
    rw [← Ring.mul_inverse_cancel (a n) hu, ← sub_mul]
    exact (norm_mul_le _ _).trans_lt hmul
  have hl : ‖1 - Ring.inverse (a n) * b n‖ < 1 / 2 := by
    rw [← Ring.inverse_mul_cancel (a n) hu, ← mul_sub]
    exact (norm_mul_le _ _).trans_lt (by rwa [mul_comm])
  obtain ⟨hub, hnb⟩ :=
    NormedRing.isUnit_and_norm_inverse_le_two_mul_of_norm_one_sub_mul_lt hr hl
  exact ⟨hub, hnb.trans (mul_le_mul_of_nonneg_left hinv zero_le_two)⟩

/-- Two sequences in normed rings with summable geometric series whose difference tends to zero in
norm are simultaneously stable or unstable. -/
theorem isStableSequence_iff_of_tendsto_sub_zero [∀ n, HasSummableGeomSeries (R n)]
    {a b : ∀ n, R n} (h : Tendsto (fun n ↦ ‖a n - b n‖) atTop (𝓝 0)) :
    IsStableSequence a ↔ IsStableSequence b :=
  ⟨fun ha ↦ ha.of_tendsto_sub_zero (h.congr fun _ ↦ norm_sub_rev _ _),
    fun hb ↦ hb.of_tendsto_sub_zero h⟩

end StableSequence

end TauCeti
