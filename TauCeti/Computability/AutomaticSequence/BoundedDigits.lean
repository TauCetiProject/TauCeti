/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.AutomaticSequence.Kernel
import Mathlib.Basic.Finite.Prod
import Mathlib.Tactic.LinearCombination

/-!
# Automatic sequences read with bounded digits

Let `k ≥ 2` and `d : ℕ`. A word `w` on the alphabet `Fin (d + 1)` has the value
`Nat.ofDigits k (w.map Fin.val)` in base `k`, read least significant digit first; its digits may
exceed `k - 1`, so a natural number has many such representations. If `a` is `k`-automatic, then
some automaton with finitely many states outputs `a` at the value of every word on `Fin (d + 1)`
(`TauCeti.IsAutomatic.exists_dfao_output_eval_eq_ofDigits`). This normalisation lets automata
read noncanonical radix words, as in Krebs's proof of Cobham's theorem, where words with digits
up to `2 k` cover the doubled interval `[0, 2 k ^ n]`.

The automaton keeps a state `g` of the `k`-kernel of `a`, which is finite by Eilenberg's theorem,
together with a pending carry `c ≤ d`, and outputs `g c`. On the digit `e` it writes
`c + e = k c' + r` with `r < k`, moves to the kernel element `n ↦ g (k * n + r)` and to the carry
`c'`, which is again at most `d` because `c + e ≤ 2 d ≤ k d`. After reading a word of length `L`
and value `V` from the initial state `(a, 0)`, the state `(g, c)` satisfies
`g (n + c) = a (k ^ L * n + V)` for every `n`; at `n = 0` the output is `a V`, including the
contribution of a carry that has not yet been written out.

## Main results

* `TauCeti.IsAutomatic.exists_dfao_output_eval_eq_ofDigits`: a `k`-automatic sequence is computed
  by a finite automaton on every word of digits at most `d`, read least significant digit first.

## References

* Thijmen J. P. Krebs, *A more reasonable proof of Cobham's theorem*, 2018,
  arXiv:1801.06704, Lemma 5 and Section 3.
-/

public section

universe u

namespace TauCeti

variable {k d : ℕ} {Δ : Type u} {a : ℕ → Δ}

/-- The carry automaton on digits at most `d`: its states are pairs of an element `g` of the
`k`-kernel of `a` and a carry `c ≤ d`, it starts at `(a, 0)` and outputs `g c`. On the digit `e`
it moves to the kernel element `n ↦ g (k * n + (c + e) % k)` and to the carry `(c + e) / k`. -/
private def carryDFAO (hk : 2 ≤ k) (a : ℕ → Δ) (d : ℕ) :
    DFAO (Fin (d + 1)) (kernel k a × Fin (d + 1)) Δ where
  step q e :=
    (⟨fun n ↦ q.1.1 (k * n + (q.2 + e : ℕ) % k),
        kernel_subset q.1.2 (apply_mul_add_mem_kernel (Nat.mod_lt _ (by omega)))⟩,
      ⟨(q.2 + e : ℕ) / k, Nat.lt_succ_of_le <| Nat.div_le_of_le_mul <| by
        have := Nat.mul_le_mul_right d hk
        omega⟩)
  start := (⟨a, self_mem_kernel k a⟩, 0)
  output q := q.1.1 q.2

/-- From the state `(g, c)`, after reading the word `w` of length `L` and value `V` the carry
automaton is in a state `(g', c')` with `g' (n + c') = g (k ^ L * n + V + c)` for every `n`. -/
private theorem carryDFAO_evalFrom (hk : 2 ≤ k) (g : kernel k a) (c : Fin (d + 1))
    (w : List (Fin (d + 1))) (n : ℕ) :
    ((carryDFAO hk a d).evalFrom (g, c) w).1.1 (n + ((carryDFAO hk a d).evalFrom (g, c) w).2) =
      g.1 (k ^ w.length * n + Nat.ofDigits k (w.map Fin.val) + c) := by
  induction w generalizing g c with
  | nil => simp
  | cons e w ih =>
    rw [DFAO.evalFrom_cons, ih]
    simp only [carryDFAO, List.length_cons, List.map_cons, Nat.ofDigits_cons]
    refine congrArg g.1 ?_
    rw [pow_succ]
    linear_combination Nat.div_add_mod (c + e : ℕ) k

/-- **Automaticity with bounded digits.** For `2 ≤ k`, a `k`-automatic sequence `a` is computed
by a finite automaton on the alphabet `Fin (d + 1)`: on every word `w`, read least significant
digit first, it outputs `a` at the base-`k` value of `w`. The digits may exceed `k - 1`, and
the word may have trailing zeros. -/
theorem IsAutomatic.exists_dfao_output_eval_eq_ofDigits [NeZero k] (hk : 2 ≤ k)
    (ha : IsAutomatic k a) (d : ℕ) :
    ∃ (σ : Type) (_ : Fintype σ) (M : DFAO (Fin (d + 1)) σ Δ),
      ∀ w : List (Fin (d + 1)), M.output (M.eval w) = a (Nat.ofDigits k (w.map Fin.val)) := by
  have := ha.finite_kernel.to_subtype
  obtain ⟨m, ⟨g⟩⟩ := Finite.exists_equiv_fin (kernel k a × Fin (d + 1))
  refine ⟨Fin m, inferInstance, DFAO.reindex g (carryDFAO hk a d), fun w ↦ ?_⟩
  rw [DFAO.output_eval_reindex, DFAO.eval_eq_evalFrom]
  simpa [carryDFAO] using carryDFAO_evalFrom hk ⟨a, self_mem_kernel k a⟩ 0 w 0

/-! ### Checks -/

/-- In base `3`, with digits at most `3`, the words `[3]` and `[0, 1]` both represent `3`. -/
example (ha : IsAutomatic 3 a) :
    ∃ (σ : Type) (_ : Fintype σ) (M : DFAO (Fin 4) σ Δ),
      M.output (M.eval [3]) = a 3 ∧ M.output (M.eval [0, 1]) = a 3 := by
  obtain ⟨σ, _, M, hM⟩ := ha.exists_dfao_output_eval_eq_ofDigits (by norm_num) 3
  exact ⟨σ, inferInstance, M, by simpa using hM [3], by simpa [Nat.ofDigits] using hM [0, 1]⟩

/-- In base `2`, with digits at most `4`, the empty word outputs `a 0` and the one-letter word
`[4]` outputs `a 4`, although `4` is not a binary digit. -/
example (ha : IsAutomatic 2 a) :
    ∃ (σ : Type) (_ : Fintype σ) (M : DFAO (Fin 5) σ Δ),
      M.output (M.eval []) = a 0 ∧ M.output (M.eval [4]) = a 4 := by
  obtain ⟨σ, _, M, hM⟩ := ha.exists_dfao_output_eval_eq_ofDigits (by norm_num) 4
  exact ⟨σ, inferInstance, M, by simpa using hM [], by simpa using hM [4]⟩

end TauCeti
