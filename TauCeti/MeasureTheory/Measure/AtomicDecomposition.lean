/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

/-!
# Countability of the point atoms of a finite measure

For a finite measure with measurable singletons, the points of positive singleton mass form a
countable set. This is the elementary source-side step needed to separate atomic obstructions
from the nonatomic feasibility theorem in the Monge problem.
-/

public section

noncomputable section

open MeasureTheory Set

namespace MeasureTheory.Measure

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]

/-- The set of points carrying positive singleton mass. -/
def positiveSingletons (μ : Measure X) : Set X := {x | μ {x} ≠ 0}

omit [MeasurableSingletonClass X] in
/-- Membership in `positiveSingletons` means that the singleton has nonzero mass. -/
@[simp]
theorem mem_positiveSingletons_iff (μ : Measure X) (x : X) :
    x ∈ positiveSingletons μ ↔ μ {x} ≠ 0 := Iff.rfl

/-- A finite measure has at most countably many positive-mass singleton sets. -/
theorem countable_positiveSingletons (μ : Measure X) [IsFiniteMeasure μ] :
    (positiveSingletons μ).Countable := by
  classical
  let A : ℕ → Set X := fun n ↦ {x | (1 / (n + 1 : ℝ) : ℝ) ≤ μ.real {x}}
  have hfinite (n : ℕ) : (A n).Finite := by
    by_contra h
    have hinf : (A n).Infinite := h
    let k := ⌊μ.real univ * (n + 1 : ℝ)⌋₊ + 1
    obtain ⟨t, ht, hcard⟩ := hinf.exists_subset_card_eq k
    have hsum : (∑ x ∈ t, μ.real {x}) ≤ μ.real univ := by
      rw [sum_measureReal_singleton]
      exact measureReal_mono (by simp)
    have hlower : (t.card : ℝ) / (n + 1) ≤ ∑ x ∈ t, μ.real {x} := by
      calc
        (t.card : ℝ) / (n + 1 : ℝ) = ∑ x ∈ t, (1 / (n + 1 : ℝ)) := by
          simp [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
        _ ≤ ∑ x ∈ t, μ.real {x} := by
          apply Finset.sum_le_sum
          intro x hx
          exact ht hx
    have hk : μ.real univ * (n + 1 : ℝ) < (k : ℝ) := by
      dsimp [k]
      exact_mod_cast Nat.lt_floor_add_one _
    rw [hcard] at hlower
    have hn : (0 : ℝ) < n + 1 := by positivity
    have hupper : (k : ℝ) ≤ μ.real univ * (n + 1 : ℝ) :=
      (div_le_iff₀ hn).1 (hlower.trans hsum)
    dsimp [k] at hk
    nlinarith
  have hcover : positiveSingletons μ ⊆ ⋃ n, A n := by
    intro x hx
    have hxne : μ.real {x} ≠ 0 :=
      (measureReal_ne_zero_iff (by finiteness)).2 hx
    have hxpos : 0 < μ.real {x} := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hxne)
    obtain ⟨n, hn⟩ := exists_nat_gt (μ.real {x})⁻¹
    refine mem_iUnion.mpr ⟨n, ?_⟩
    -- Unfold the local set `A` to expose its threshold condition at this point.
    change (1 / (n + 1 : ℝ) : ℝ) ≤ μ.real {x}
    have hn' : (μ.real {x})⁻¹ < (n + 1 : ℝ) := by
      have hncast : (μ.real {x})⁻¹ < (n : ℝ) := by exact_mod_cast hn
      linarith
    have hrec : (n + 1 : ℝ)⁻¹ ≤ μ.real {x} := by
      simpa [one_div, inv_inv] using
        (one_div_le_one_div_of_le (by positivity : 0 < (μ.real {x})⁻¹) hn'.le)
    simpa [one_div] using hrec
  exact (countable_iUnion fun n ↦ (hfinite n).countable).mono hcover

/-- The positive-mass singleton points form a measurable set for a finite measure. -/
theorem measurableSet_positiveSingletons (μ : Measure X) [IsFiniteMeasure μ] :
    MeasurableSet (positiveSingletons μ) :=
  (countable_positiveSingletons μ).measurableSet

/-- The restriction of a finite measure to all of its positive-mass singleton points. -/
def atomicPart (μ : Measure X) : Measure X := μ.restrict (positiveSingletons μ)

omit [MeasurableSingletonClass X] in
/-- The atomic part is the restriction to the positive-mass singleton points. -/
theorem atomicPart_def (μ : Measure X) :
    atomicPart μ = μ.restrict (positiveSingletons μ) := by
  rw [atomicPart]

omit [MeasurableSingletonClass X] in
/-- Evaluate the atomic part on a measurable set. -/
@[simp]
theorem atomicPart_apply (μ : Measure X) (s : Set X) (hs : MeasurableSet s) :
    atomicPart μ s = μ (s ∩ positiveSingletons μ) := by
  rw [atomicPart, restrict_apply hs]

/-- The atomic part preserves the mass of every singleton. -/
theorem atomicPart_apply_singleton (μ : Measure X) (x : X) :
    atomicPart μ {x} = μ {x} := by
  rw [atomicPart, restrict_apply (measurableSet_singleton x)]
  by_cases hx : μ {x} = 0
  · have hx' : x ∉ positiveSingletons μ := by simpa [positiveSingletons] using hx
    simpa [hx'] using hx.symm
  · have hx' : x ∈ positiveSingletons μ := hx
    simp [hx']

/-- The complementary restriction to the points with zero singleton mass. -/
def diffusePart (μ : Measure X) : Measure X := μ.restrict (positiveSingletons μ)ᶜ

omit [MeasurableSingletonClass X] in
/-- The diffuse part is the restriction to the complement of the positive-mass points. -/
theorem diffusePart_def (μ : Measure X) :
    diffusePart μ = μ.restrict (positiveSingletons μ)ᶜ := by
  rw [diffusePart]

omit [MeasurableSingletonClass X] in
/-- Evaluate the diffuse part on a measurable set. -/
@[simp]
theorem diffusePart_apply (μ : Measure X) (s : Set X) (hs : MeasurableSet s) :
    diffusePart μ s = μ (s ∩ (positiveSingletons μ)ᶜ) := by
  rw [diffusePart, restrict_apply hs]

/-- The point-mass part and the diffuse remainder sum to the original finite measure. -/
theorem atomicPart_add_diffusePart (μ : Measure X) [IsFiniteMeasure μ] :
    atomicPart μ + diffusePart μ = μ := by
  rw [atomicPart, diffusePart, restrict_add_restrict_compl (measurableSet_positiveSingletons μ)]

/-- The diffuse remainder has zero mass on every singleton. -/
instance diffusePart_nullSingletonClass (μ : Measure X) :
    NullSingletonClass (diffusePart μ) := by
  refine ⟨fun x ↦ ?_⟩
  rw [diffusePart, restrict_apply (measurableSet_singleton x)]
  by_cases hx : x ∈ positiveSingletons μ
  · simp [hx]
  · have hzero : μ {x} = 0 := by
      by_contra hne
      exact hx hne
    simp [hx, hzero]

end MeasureTheory.Measure

end
