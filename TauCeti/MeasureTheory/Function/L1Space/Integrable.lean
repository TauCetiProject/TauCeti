/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Tactic.NormNum

/-!
# Integrability under signed real coefficients

Taking the absolute value of an almost everywhere measurable real coefficient does not change
integrability of its scalar product with a real normed-space-valued function, even when that
function is not measurable by itself. The equivalence permits signed Jacobians in oriented
change of variables for arbitrary rough-form coefficients.
-/

public section

namespace MeasureTheory

/-- Multiplication by an almost everywhere measurable real coefficient preserves integrability
exactly when its absolute value does, without assuming measurability of the vector-valued `f`. -/
theorem integrable_smul_iff_abs_smul {X F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : Measure X} {d : X → ℝ} {f : X → F} (hd : AEStronglyMeasurable d μ) :
    Integrable (fun x ↦ d x • f x) μ ↔ Integrable (fun x ↦ |d x| • f x) μ := by
  let u : X → ℝ := fun x ↦ if 0 ≤ hd.mk d x then 1 else -1
  have hu : AEStronglyMeasurable u μ :=
    (StronglyMeasurable.ite (stronglyMeasurable_const.measurableSet_le hd.stronglyMeasurable_mk)
      stronglyMeasurable_const stronglyMeasurable_const).aestronglyMeasurable
  have hb : ∀ᵐ x ∂μ, ‖u x‖ ≤ (1 : ℝ) := Filter.Eventually.of_forall fun x ↦ by
    dsimp only [u]
    split_ifs <;> norm_num
  have hmul : (fun x ↦ u x • (d x • f x)) =ᵐ[μ] fun x ↦ |d x| • f x := by
    filter_upwards [hd.ae_eq_mk] with x hx
    dsimp only [u]
    rw [← hx]
    by_cases hx' : 0 ≤ d x
    · rw [ite_eq_left hx', abs_of_nonneg hx', one_smul]
    · rw [ite_eq_right hx', abs_of_neg (lt_of_not_ge hx'), smul_smul, neg_one_mul]
  have hinv : (fun x ↦ u x • (|d x| • f x)) =ᵐ[μ] fun x ↦ d x • f x := by
    filter_upwards [hd.ae_eq_mk] with x hx
    dsimp only [u]
    rw [← hx]
    by_cases hx' : 0 ≤ d x
    · rw [ite_eq_left hx', abs_of_nonneg hx', one_smul]
    · rw [ite_eq_right hx', abs_of_neg (lt_of_not_ge hx'), smul_smul, neg_one_mul, neg_neg]
  exact ⟨fun h ↦ (h.bdd_smul 1 hu hb).congr hmul,
    fun h ↦ (h.bdd_smul 1 hu hb).congr hinv⟩

end MeasureTheory
