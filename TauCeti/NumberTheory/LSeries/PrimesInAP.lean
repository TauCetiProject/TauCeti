/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.PrimesInAP
import TauCeti.Analysis.PSeries.Sparse

/-!
# Avoiding sparse exceptional sets in arithmetic progressions

The divergent logarithmically weighted sum over the primes in a reduced residue class
remains divergent after discarding a set with a power saving in its counting function.
-/

public section

open Filter Asymptotics Set
open ArithmeticFunction.vonMangoldt

namespace Nat

/-- An invertible residue class contains infinitely many primes outside any set whose
counting function is `O(x ^ B)` for `B < 1`. -/
theorem infinite_setOf_prime_and_eq_mod_and_notMem_of_ncard_isBigO
    {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) {S : Set ℕ} {B : ℝ} (hB : B < 1)
    (hcount : (fun x : ℝ ↦ ({n ∈ S | (n : ℝ) ≤ x}.ncard : ℝ)) =O[atTop] (· ^ B)) :
    {p : ℕ | p.Prime ∧ (p : ZMod q) = a ∧ p ∉ S}.Infinite := by
  classical
  let f (n : ℕ) : ℝ := (if n.Prime then residueClass a n else 0) / n
  have hf : ¬ Summable f := not_summable_residueClass_prime_div ha
  have hsupp : Function.support f = {n : ℕ | n.Prime ∧ (n : ZMod q) = a} :=
    support_residueClass_prime_div a
  have hS : Summable (S.indicator f) := by
    rw [← summable_subtype_iff_indicator]
    refine (S.summable_log_div_of_ncard_isBigO hB hcount).of_nonneg_of_le ?_ ?_
    · intro n
      exact div_nonneg (by split_ifs <;> simp [residueClass_nonneg]) (Nat.cast_nonneg _)
    · intro n
      by_cases hp : n.val.Prime
      · simpa only [f, Function.comp_apply, ite_eq_left hp,
          ArithmeticFunction.vonMangoldt_apply_prime hp] using
          div_le_div_of_nonneg_right (residueClass_le a n.val) (Nat.cast_nonneg n.val)
      · simpa only [f, Function.comp_apply, ite_eq_right hp, zero_div] using
          div_nonneg (Real.log_natCast_nonneg n.val) (Nat.cast_nonneg n.val)
  intro hfinite
  have hSc : Summable (Sᶜ.indicator f) := by
    apply summable_of_hasFiniteSupport
    rw [Function.HasFiniteSupport, support_indicator, hsupp]
    exact hfinite.subset fun _ hn ↦ ⟨hn.2.1, hn.2.2, hn.1⟩
  exact hf (by simpa [indicator_add_compl_eq_piecewise] using hS.add hSc)

end Nat
