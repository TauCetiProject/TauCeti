/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.AutomaticSequence.BoundedDigits
import Mathlib.Data.Set.Finite.Range
import Mathlib.Basic.Finite.Prod
import TauCeti.Data.Nat.Digits

/-!
# Most-significant-first automatic sequences

Automaticity is unchanged by reversing the canonical radix words. For bases at least two,
finite carry normalization gives a stronger statement: an automatic sequence can be computed
most significant digit first on every word over any bounded alphabet containing the ordinary
digits. This includes leading zeros and digits greater than the base. Such all-word correctness
allows a common suffix to be appended to two prefixes without checking that either extended
word is a canonical expansion.

* `TauCeti.isAutomatic_iff_exists_dfao_reverse`: the canonical reading-direction equivalence.
* `TauCeti.isAutomatic_iff_exists_dfao_output_eval_eq_ofDigits_reverse`: the all-word,
  bounded-digit characterization.

## References

* Andrew Bridy, *Automatic sequences and curves over finite fields*, Algebra & Number Theory
  11 (2017), Section 2.1.
* Thijmen J. P. Krebs, *A more reasonable proof of Cobham's theorem*, 2018,
  arXiv:1801.06704, Lemma 5 and Section 3.
-/

public section

universe u

namespace TauCeti

variable {k d : ℕ} [NeZero k] {Δ : Type u} {a : ℕ → Δ}

/-- Automaticity is equivalent to computation by a finite automaton on the reversed canonical
radix words, that is, reading most significant digit first. This also holds for unary base one.
Zero is represented by the empty word in both conventions. -/
theorem isAutomatic_iff_exists_dfao_reverse :
    IsAutomatic k a ↔
      ∃ (σ : Type) (_ : Fintype σ) (M : DFAO (Fin k) σ Δ),
        ∀ n, a n = M.output (M.eval (((Nat.digits k n).map (Fin.ofNat k)).reverse)) := by
  constructor
  · intro ha
    obtain ⟨σ, _, M, hM⟩ := isAutomatic_iff.mp ha
    obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin (σ → Set.range M.output)
    refine ⟨Fin m, inferInstance, DFAO.reindex e M.reverse, fun n ↦ ?_⟩
    simpa using hM n
  · rintro ⟨σ, _, M, hM⟩
    simpa only [DFAO.output_eval_reverse, ← hM] using M.reverse.isAutomatic

/-- For `2 ≤ k` and `k ≤ d + 1`, a sequence is `k`-automatic exactly when a finite automaton
computes it most significant digit first on **every** word with digits at most `d`.
Noncanonical digits, leading zeros and the empty word are all allowed. -/
theorem isAutomatic_iff_exists_dfao_output_eval_eq_ofDigits_reverse (hk : 2 ≤ k)
    (hd : k ≤ d + 1) :
    IsAutomatic k a ↔
      ∃ (σ : Type) (_ : Fintype σ) (M : DFAO (Fin (d + 1)) σ Δ),
        ∀ w : List (Fin (d + 1)),
          M.output (M.eval w) = a (Nat.ofDigits k (w.map Fin.val).reverse) := by
  constructor
  · intro ha
    obtain ⟨σ, _, M, hM⟩ := ha.exists_dfao_output_eval_eq_ofDigits hk d
    obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin (σ → Set.range M.output)
    refine ⟨Fin m, inferInstance, DFAO.reindex e M.reverse, fun w ↦ ?_⟩
    simpa [List.map_reverse] using hM w.reverse
  · rintro ⟨σ, _, M, hM⟩
    apply isAutomatic_iff_exists_dfao_reverse.mpr
    refine ⟨σ, inferInstance, M.comap (Fin.castLE hd), fun n ↦ ?_⟩
    rw [DFAO.comap_output, DFAO.eval_comap, hM]
    simp only [List.map_reverse, List.reverse_reverse]
    rw [List.map_map]
    simp only [Function.comp_def, Fin.val_castLE]
    rw [Nat.map_val_map_ofNat_digits hk, Nat.ofDigits_digits]

/-! ### Checks -/

/-- Most-significant-first representations `[3]` and `[1, 0]` of three give the same value,
and adding a leading zero does not change it. -/
example (ha : IsAutomatic 3 a) :
    ∃ (σ : Type) (_ : Fintype σ) (M : DFAO (Fin 4) σ Δ),
      M.output (M.eval [3]) = a 3 ∧ M.output (M.eval [1, 0]) = a 3 ∧
        M.output (M.eval [0, 1, 0]) = a 3 := by
  obtain ⟨σ, _, M, hM⟩ :=
    (isAutomatic_iff_exists_dfao_output_eval_eq_ofDigits_reverse (d := 3)
      (by norm_num) (by norm_num)).mp ha
  exact ⟨σ, inferInstance, M, by simpa using hM [3],
    by simpa [Nat.ofDigits] using hM [1, 0], by simpa [Nat.ofDigits] using hM [0, 1, 0]⟩

/-- Leading zeros are harmless on every word, not only on canonical expansions. -/
example (hk : 2 ≤ k) (hd : k ≤ d + 1) (ha : IsAutomatic k a) :
    ∃ (σ : Type) (_ : Fintype σ) (M : DFAO (Fin (d + 1)) σ Δ),
      ∀ w, M.output (M.eval (0 :: w)) = M.output (M.eval w) := by
  obtain ⟨σ, _, M, hM⟩ :=
    (isAutomatic_iff_exists_dfao_output_eval_eq_ofDigits_reverse hk hd).mp ha
  refine ⟨σ, inferInstance, M, fun w ↦ ?_⟩
  rw [hM, hM]
  simp [Nat.ofDigits_append]

/-- The alphabet up to `2k` includes the noncanonical one-letter representation of `2k`. -/
example (hk : 2 ≤ k) (ha : IsAutomatic k a) :
    ∃ (σ : Type) (_ : Fintype σ) (M : DFAO (Fin (2 * k + 1)) σ Δ),
      M.output (M.eval [⟨2 * k, by omega⟩]) = a (2 * k) := by
  obtain ⟨σ, _, M, hM⟩ :=
    (isAutomatic_iff_exists_dfao_output_eval_eq_ofDigits_reverse (d := 2 * k) hk
      (by omega)).mp ha
  exact ⟨σ, inferInstance, M, by simpa using hM [⟨2 * k, by omega⟩]⟩

end TauCeti
