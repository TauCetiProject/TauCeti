/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Probability.IdentDistrib
public import Mathlib.MeasureTheory.Function.L2Space

import TauCeti.Analysis.Matrix.Frobenius

/-!
# Mean squared Frobenius norms of random matrices

Square-integrability of the entries controls the expected squared Frobenius norm.
For entries with the same law, the mean squared Frobenius norm is the number of entries
times the second absolute moment of that law, regardless of dependence.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.Frobenius

namespace TauCeti.Probability

variable {Ω p n E : Type*} [MeasurableSpace Ω] [Fintype p] [Fintype n]
  [SeminormedAddCommGroup E] {P : Measure Ω} {X : Ω → Matrix p n E}

/-- The squared Frobenius norm of a matrix with square-integrable entries is integrable. -/
theorem integrable_frobenius_norm_sq (hX : ∀ i j, MemLp (fun ω ↦ X ω i j) 2 P) :
    Integrable (fun ω ↦ ‖X ω‖ ^ 2) P := by
  simp_rw [Matrix.frobenius_norm_sq_eq_sum_norm_sq]
  refine integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ ?_
  have hnorm : MemLp (fun ω ↦ ‖X ω i j‖) 2 P :=
    (hX i j).of_le_eNorm (hX i j).aestronglyMeasurable.norm (.of_forall fun _ ↦ by simp)
  exact hnorm.integrable_sq

/-- With a common entry law the expected squared Frobenius norm is the entry count times
the second absolute moment. For non-square-integrable data both Bochner integrals are zero. -/
theorem integral_frobenius_norm_sq_of_identDistrib [MeasurableSpace E] [OpensMeasurableSpace E]
    {Ω' : Type*} [MeasurableSpace Ω'] {Q : Measure Ω'} {Z : Ω' → E}
    (hid : ∀ i j, IdentDistrib (fun ω ↦ X ω i j) Z P Q) :
    (∫ ω, ‖X ω‖ ^ 2 ∂P) =
      (Fintype.card p * Fintype.card n : ℝ) * ∫ ω, ‖Z ω‖ ^ 2 ∂Q := by
  have hsq (i : p) (j : n) : IdentDistrib (fun ω ↦ ‖X ω i j‖ ^ 2) (fun ω ↦ ‖Z ω‖ ^ 2) P Q :=
    (hid i j).comp (by fun_prop : Measurable (fun z : E ↦ ‖z‖ ^ 2))
  by_cases hZ : Integrable (fun ω ↦ ‖Z ω‖ ^ 2) Q
  · have hint (i : p) (j : n) := (hsq i j).integrable_iff.2 hZ
    simp_rw [Matrix.frobenius_norm_sq_eq_sum_norm_sq]
    rw [integral_finsetSum _ (fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hint i j)]
    simp_rw [integral_finsetSum _ (fun j _ ↦ hint _ j), fun i j ↦ (hsq i j).integral_eq]
    simp [mul_assoc]
  rw [integral_undef hZ, mul_zero]
  rcases isEmpty_or_nonempty p with hp | hp
  · simp [Matrix.frobenius_norm_sq_eq_sum_norm_sq]
  rcases isEmpty_or_nonempty n with hn | hn
  · simp [Matrix.frobenius_norm_sq_eq_sum_norm_sq]
  apply integral_undef
  obtain ⟨i⟩ := hp
  obtain ⟨j⟩ := hn
  intro hX
  apply hZ
  refine (hsq i j).integrable_iff.1 (hX.mono' (hsq i j).aemeasurable_fst.aestronglyMeasurable ?_)
  refine .of_forall fun ω ↦ ?_
  rw [Real.norm_of_nonneg (sq_nonneg _), Matrix.frobenius_norm_sq_eq_sum_norm_sq]
  exact (Finset.single_le_sum (fun k _ ↦ sq_nonneg (‖X ω i k‖)) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (fun k _ ↦ Finset.sum_nonneg fun l _ ↦ sq_nonneg (‖X ω k l‖))
      (Finset.mem_univ i))

end TauCeti.Probability
