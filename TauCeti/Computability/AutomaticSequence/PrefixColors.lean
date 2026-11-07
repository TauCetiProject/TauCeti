/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.AutomaticSequence.ReadingDirection
import TauCeti.Data.Nat.Digits
import TauCeti.Data.Nat.Digits.Redundant

/-!
# Finite prefix colours for wide radix blocks

An automatic sequence admits a finite colouring of prefixes such that equal colours force
agreement on the whole doubled block at every positive radix scale. The colour is the state
reached by a most-significant-first automaton with redundant digits. Equal output values alone
would not suffice: equal states remain equal after appending any common suffix.

The same colouring works simultaneously for all lengths and includes both endpoints of the
suffix interval. This provides the finite-state comparisons used to construct local periods
for sequences automatic in two bases.

## References

* Thijmen J. P. Krebs, *A more reasonable proof of Cobham's theorem* (2018), §3, equation (1).
-/

public section

namespace TauCeti

/-- A `k`-automatic sequence has finitely many prefix colours, equality of which controls
all blocks `xk^n + [0, 2k^n]` at once. Colours are reached states, not merely output values. -/
theorem IsAutomatic.exists_prefix_coloring {k : ℕ} [NeZero k] {Δ : Type*} {f : ℕ → Δ}
    (hf : IsAutomatic k f) (hk : 2 ≤ k) :
    ∃ q : ℕ, 0 < q ∧ ∃ C : ℕ → Fin q, ∀ x y, C x = C y →
      ∀ n, 0 < n → ∀ z ≤ 2 * k ^ n, f (x * k ^ n + z) = f (y * k ^ n + z) := by
  classical
  obtain ⟨σ, _, M, hM⟩ :=
    (isAutomatic_iff_exists_dfao_output_eval_eq_ofDigits_reverse (d := 2 * k) hk
      (by omega)).mp hf
  let word (x : ℕ) : List (Fin (2 * k + 1)) :=
    (((Nat.digits k x).map (Fin.ofNat k)).map
      (Fin.castLE (by omega : k ≤ 2 * k + 1))).reverse
  have hword (x : ℕ) : Nat.ofDigits k ((word x).map Fin.val).reverse = x := by
    simp only [word, List.map_reverse, List.reverse_reverse, List.map_map,
      Function.comp_def, Fin.val_castLE]
    have h := Nat.map_val_map_ofNat_digits hk x
    simp only [List.map_map, Function.comp_def] at h
    rw [h, Nat.ofDigits_digits]
  refine ⟨Fintype.card σ, Fintype.card_pos_iff.mpr ⟨M.start⟩,
    fun x ↦ Fintype.equivFin σ (M.eval (word x)), ?_⟩
  intro x y hxy n hn z hz
  have hstates : M.eval (word x) = M.eval (word y) := (Fintype.equivFin σ).injective hxy
  obtain ⟨w, hw, hval⟩ := Nat.exists_redundant_word_of_le_two_mul_pow (by omega) hn hz
  have happend (x : ℕ) :
      Nat.ofDigits k (((word x ++ w).map Fin.val).reverse) = x * k ^ n + z := by
    simp only [List.map_append, List.reverse_append, Nat.ofDigits_append,
      List.length_reverse, List.length_map, hw, hval, hword]
    ac_rfl
  rw [← happend x, ← happend y, ← hM, ← hM, DFAO.eval_append, DFAO.eval_append, hstates]

-- Constant sequences admit a single colour at every radix scale, including the endpoint.
example {Δ : Type*} (c : Δ) (k : ℕ) :
    ∃ C : ℕ → Fin 1, ∀ x y, C x = C y → ∀ n z, z ≤ 2 * k ^ n →
      (fun _ : ℕ ↦ c) (x * k ^ n + z) = (fun _ ↦ c) (y * k ^ n + z) := by
  exact ⟨fun _ ↦ 0, fun _ _ _ _ _ _ ↦ rfl⟩

end TauCeti
