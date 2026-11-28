/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.Basic
public import TauCeti.Algebra.TypeAHeckeAlgebra.AtomicModel.CycleWord.Basic

/-!
# Norm bounds for cycle words in the signed checked representation

Over any normed commutative ring `R`, the diagonal entry of the cycle word `cycleWord q (m + 1)` in
`signedChecked pos q` grows at most exponentially with base `max 1 (max ‖q ^ 2‖ ‖q ^ 2 - 1‖)`
(`TauCeti.TypeAHeckeAlgebra.norm_signedChecked_cycleWord_single_apply_le`), yielding the finite
atomic trace norm estimate `TauCeti.TypeAHeckeAlgebra.norm_atomicTrace_cycleWord_le`.
-/

public section

open Finsupp

namespace TauCeti.TypeAHeckeAlgebra

variable {R : Type*} [NormedCommRing R] {ι : Type*} [LinearOrder ι] (pos : ι → Prop)
  [DecidablePred pos] (q : Rˣ)

/-- **Sharp diagonal norm bound on cycle words.** -/
theorem norm_signedChecked_cycleWord_single_apply_le : ∀ {m : ℕ} (w : Fin (m + 1) → ι),
      ‖signedChecked pos q (cycleWord q (m + 1)) (single w 1) w‖ ≤
        ‖(1 : R)‖ * max 1 (max ‖(q : R) ^ 2‖ ‖(q : R) ^ 2 - 1‖) ^ m
  | 0, w => by rw [cycleWord_one, map_one, one_apply_eq_self, single_eq_same, pow_zero, mul_one]
  | m + 1, w => by
    set M : ℝ := max 1 (max ‖(q : R) ^ 2‖ ‖(q : R) ^ 2 - 1‖)
    conv_lhs => rw [← Fin.snoc_init_self w]
    rw [signedChecked_cycleWord_succ_snoc_apply, pow_succ M m, ← mul_assoc]
    have ih := norm_signedChecked_cycleWord_single_apply_le (Fin.init w)
    set z := signedChecked pos q (cycleWord q (m + 1)) (single (Fin.init w) 1) (Fin.init w)
    refine le_trans ?_ (mul_le_mul_of_nonneg_right ih (by positivity)); split_ifs
    · exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left ((le_max_left _ _).trans
        (le_max_right _ _)) (norm_nonneg z))
    · rw [mul_neg, mul_one, norm_neg]; exact le_mul_of_one_le_right (norm_nonneg z) (le_max_left ..)
    · exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left ((le_max_right _ _).trans
        (le_max_right _ _)) (norm_nonneg z))
    · rw [mul_zero, norm_zero]; positivity

/-- Norm bound on the finite atomic trace of a cycle word `cycleWord (m + 1)`. -/
theorem norm_atomicTrace_cycleWord_le [Fintype ι] (p : ι → R) (m : ℕ) :
    ‖atomicTrace pos q p (m + 1) (cycleWord q (m + 1))‖ ≤
      ‖(1 : R)‖ * max 1 (max ‖(q : R) ^ 2‖ ‖(q : R) ^ 2 - 1‖) ^ m * (∑ a, ‖p a‖) ^ (m + 1) := by
  rw [atomicTrace_eq_sum]; refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun w _ ↦
    (norm_mul_le _ _).trans <| mul_le_mul (norm_signedChecked_cycleWord_single_apply_le pos q w)
      (Finset.norm_prod_le' _ Finset.univ_nonempty _) (norm_nonneg _) (by positivity)).trans_eq ?_)
  rw [← Finset.mul_sum, ← Fintype.prod_sum (fun (_ : Fin (m + 1)) a ↦ ‖p a‖), Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

end TauCeti.TypeAHeckeAlgebra
