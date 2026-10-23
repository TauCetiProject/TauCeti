/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Estimates

/-!
# Bounds for individual norm fibres

The linear bound for the number of nonzero integral ideals of norm at most `x` also bounds
each individual norm fibre. Consequently the norm coefficient of any ideal arithmetic function
bounded by one grows at most linearly in its index, including unitary ideal weights. These
pointwise bounds complement the partial-sum estimates used
to locate the abscissa of convergence.

The counting input is `TauCeti.idealCount_linearBounds`, which follows from Mathlib's
`NumberField.Ideal.tendsto_norm_le_div_atTop₀`.
-/

public section

namespace TauCeti

open Asymptotics Filter
open NumberField
open scoped nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

/-- A norm fibre has at most the linear ideal-count bound at the same cutoff. -/
theorem IdealCountingLinearBounds.card_normFiber_le (b : IdealCountingLinearBounds K)
    (n : ℕ) : ((normFiber K n).card : ℝ) ≤ b.upper * n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [normFiber_zero]
  have hsingle : ‖normCoeff K (1 : IdealArithmeticFunction K) n‖ ≤
      ∑ k ∈ Finset.Icc 1 n, ‖normCoeff K (1 : IdealArithmeticFunction K) k‖ :=
    Finset.single_le_sum (fun k _ ↦ norm_nonneg (normCoeff K
      (1 : IdealArithmeticFunction K) k)) (Finset.mem_Icc.mpr ⟨hn, le_refl n⟩)
  rw [norm_normCoeff_one K n] at hsingle
  rw [sum_norm_normCoeff_one K n] at hsingle
  exact hsingle.trans (b.card_le n (by exact_mod_cast hn))

/-- The norm coefficient of an ideal arithmetic function bounded by one is bounded by the
linear ideal-count constant. -/
theorem IdealCountingLinearBounds.norm_normCoeff_le_of_bounded (b : IdealCountingLinearBounds K)
    (f : IdealArithmeticFunction K) (hf : ∀ I, ‖f I‖ ≤ 1) (n : ℕ) :
    ‖normCoeff K f n‖ ≤ b.upper * n := by
  calc
    ‖normCoeff K f n‖ ≤ ∑ I ∈ normFiber K n, ‖f I‖ := by
      rw [normCoeff_eq_sum_normFiber]
      exact norm_sum_le _ _
    _ ≤ ((normFiber K n).card : ℝ) := by
      simpa using Finset.sum_le_sum fun I (_ : I ∈ normFiber K n) ↦ hf I
    _ ≤ b.upper * n := b.card_normFiber_le n

/-- The norm coefficient of a unitary ideal weight is bounded by the linear ideal-count
constant. -/
theorem IdealCountingLinearBounds.norm_normCoeff_le (b : IdealCountingLinearBounds K)
    (χ : UnitaryIdealWeight K) (n : ℕ) :
    ‖normCoeff K χ.toIdealArithmeticFunction n‖ ≤ b.upper * n :=
  b.norm_normCoeff_le_of_bounded χ.toIdealArithmeticFunction
    (fun I ↦ by simpa using χ.norm_le_one (I : Ideal (𝓞 K))) n

/-- The number of ideals in a single norm fibre grows at most linearly. -/
theorem card_normFiber_isBigO :
    (fun n : ℕ ↦ ((normFiber K n).card : ℝ)) =O[atTop] fun n : ℕ ↦ (n : ℝ) := by
  obtain ⟨b⟩ := idealCount_linearBounds K
  refine IsBigO.of_bound b.upper ?_
  filter_upwards [] with n
  simpa only [Real.norm_natCast, Real.norm_of_nonneg (Nat.cast_nonneg _)] using
    b.card_normFiber_le (K := K) n

/-- The norm coefficients of an ideal arithmetic function bounded by one grow at most linearly. -/
theorem normCoeff_isBigO_of_bounded (f : IdealArithmeticFunction K) (hf : ∀ I, ‖f I‖ ≤ 1) :
    (fun n : ℕ ↦ normCoeff K f n) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) := by
  obtain ⟨b⟩ := idealCount_linearBounds K
  refine IsBigO.of_bound b.upper ?_
  filter_upwards [] with n
  simpa only [Real.norm_natCast] using b.norm_normCoeff_le_of_bounded f hf n

/-- The norm coefficients of a unitary ideal weight grow at most linearly. -/
theorem UnitaryIdealWeight.normCoeff_isBigO (χ : UnitaryIdealWeight K) :
    (fun n : ℕ ↦ normCoeff K χ.toIdealArithmeticFunction n) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) :=
  normCoeff_isBigO_of_bounded χ.toIdealArithmeticFunction
    (fun I ↦ by simpa using χ.norm_le_one (I : Ideal (𝓞 K)))

end TauCeti
