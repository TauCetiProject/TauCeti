/-
Copyright (c) 2026 Vincent Quenneville-Belair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Quenneville-Belair
-/
module

public import TauCeti.Probability.Amplification
public import Mathlib.Data.Fintype.BigOperators

/-!
# Exact failure amplification for independent uniform finite seeds

Uniform probability is defined directly by cardinalities. A uniformly drawn
function `Fin r → S` is the finite product model of independent uniform seeds.
These theorems do not use an unproved independence hypothesis.
-/

@[expose] public section

namespace TauCeti.FiniteSeeds

variable (S : Type*) [Fintype S]

/-- The real probability of an event under the uniform law on a finite nonempty seed type. -/
noncomputable def uniformProbability (event : S → Prop) : ℝ := by
  classical
  exact (Fintype.card {s : S // event s} : ℝ) / Fintype.card S

theorem uniformProbability_nonneg (event : S → Prop) :
    0 ≤ uniformProbability S event := by
  classical
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem uniformProbability_le_one [Nonempty S] (event : S → Prop) :
    uniformProbability S event ≤ 1 := by
  classical
  apply (div_le_one (Nat.cast_pos.mpr Fintype.card_pos)).mpr
  exact Nat.cast_le.mpr (Fintype.card_subtype_le event)

theorem uniformProbability_complement [Nonempty S] (event : S → Prop) :
    uniformProbability S (fun s => ¬event s) = 1 - uniformProbability S event := by
  classical
  have hne : (Fintype.card S : ℝ) ≠ 0 :=
    (Nat.cast_pos.mpr Fintype.card_pos).ne'
  unfold uniformProbability
  rw [Fintype.card_subtype_compl, Nat.cast_sub (Fintype.card_subtype_le event),
    sub_div, div_self hne]

omit [Fintype S] in
theorem all_fail_card (accepts : S → Prop) (r : ℕ) :
    Nat.card {seeds : Fin r → S // ∀ i, ¬accepts (seeds i)} =
      Nat.card {s : S // ¬accepts s} ^ r := by
  classical
  let equiv : {seeds : Fin r → S // ∀ i, ¬accepts (seeds i)} ≃
      (Fin r → {s : S // ¬accepts s}) :=
    { toFun := fun seeds i => ⟨seeds.val i, seeds.prop i⟩
      invFun := fun seeds => ⟨fun i => (seeds i).val, fun i => (seeds i).prop⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr equiv, Nat.card_fun, Nat.card_fin]

/-- The exact independent-trial failure formula, including zero trials. -/
theorem uniformProbability_all_fail [Nonempty S] (accepts : S → Prop) (r : ℕ) :
    uniformProbability (Fin r → S) (fun seeds => ∀ i, ¬accepts (seeds i)) =
      (1 - uniformProbability S accepts) ^ r := by
  classical
  calc
    uniformProbability (Fin r → S) (fun seeds => ∀ i, ¬accepts (seeds i)) =
        (uniformProbability S (fun s => ¬accepts s)) ^ r := by
      unfold uniformProbability
      simp only [← Nat.card_eq_fintype_card]
      rw [all_fail_card, Nat.card_fun, Nat.card_fin]
      push_cast
      exact (div_pow _ _ _).symm
    _ = (1 - uniformProbability S accepts) ^ r := by
      rw [uniformProbability_complement]

/-- An explicit inverse-budget success bound implies failure at most `2⁻ᵏ`. -/
theorem uniformProbability_failure_le_half_pow [Nonempty S] (accepts : S → Prop)
    (R k : ℕ) (hR : 0 < R)
    (haccepts : 1 / (R : ℝ) ≤ uniformProbability S accepts) :
    uniformProbability (Fin (k * R) → S) (fun seeds => ∀ i, ¬accepts (seeds i)) ≤
      (1 / 2 : ℝ) ^ k := by
  rw [uniformProbability_all_fail]
  exact TauCeti.failure_pow_mul_le_half_pow
    (uniformProbability_le_one S accepts) R k hR haccepts


end TauCeti.FiniteSeeds
