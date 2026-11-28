/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Dynamics.SymbolicDynamics.Basic
public import TauCeti.Dynamics.SymbolicDynamics.Language
public import TauCeti.LinearAlgebra.Matrix.PathWeight
import Mathlib.Data.Fintype.Pigeonhole

/-!
# One-sided one-step subshifts of finite type

For a relation `A : α → α → Bool` on an alphabet `α`, the one-sided one-step subshift of finite
type `TauCeti.sftOneSided A ⊆ ℕ → α` consists of the sequences `x` with `A (x k) (x (k + 1))` for
every `k`; it is mapped into itself by the shift. Its `0`-`1` transition matrix
`TauCeti.sftTransitionMatrix R A` has path weight `1` on the admissible words and `0` on the others,
so the admissible words of length `n + 1` number `∑ i, (M ^ n *ᵥ 1) i`.

Every word read off `sftOneSided A` is admissible. Conversely, if every symbol has a successor,
every admissible word extends to a point of `sftOneSided A`. Without that hypothesis, an admissible
path that revisits a symbol still extends, by repeating the cycle it closes; for a finite alphabet,
any admissible word of length at least `n + 1 + card α` revisits a symbol after position `n`, so its
prefix of length `n + 1` is a word of `sftOneSided A` (pruning). Hence the language counts and the
counts of admissible words differ by at most the factor `card α ^ card α` after a shift of
`card α`.

## Main definitions

* `TauCeti.sftTransitionMatrix R A`: the `0`-`1` matrix of a relation `A`, with entries in `R`.
* `TauCeti.sftOneSided A`: the one-sided one-step subshift of finite type of `A`.
* `TauCeti.sftAdmissibleWords A n`: the admissible words of length `n + 1`, as a `Finset`.

## Main results

* `TauCeti.pathWeight_sftTransitionMatrix`: the path weight of a word for the transition matrix is
  the indicator of its admissibility.
* `TauCeti.sftOneSided_true`: the relation that is always true defines the full shift.
* `TauCeti.mapsTo_shift_sftOneSided`: the shift maps `sftOneSided A` into itself.
* `TauCeti.exists_mem_sftOneSided_of_admissible`: if every symbol has a successor, every
  admissible word extends to a point of `sftOneSided A`.
* `TauCeti.admissible_of_mem_wordsOf_sftOneSided`: every word read off `sftOneSided A` is
  admissible.
* `TauCeti.mem_wordsOf_sftOneSided`: if every symbol has a successor, the words read off
  `sftOneSided A` are exactly the admissible words.
* `TauCeti.exists_mem_sftOneSided_of_cycle`: an admissible path that revisits a symbol extends to
  a point of `sftOneSided A`.
* `TauCeti.comp_castLE_mem_wordsOf_sftOneSided_of_admissible`: for a finite alphabet and any
  relation, the first `n + 1` symbols of an admissible word of length at least `n + 1 + card α`
  are a word of `sftOneSided A`.
* `TauCeti.card_sftAdmissibleWords`: the admissible words of length `n + 1` number
  `∑ i, (M ^ n *ᵥ 1) i`.
* `TauCeti.languageCount_sftOneSided_le`,
  `TauCeti.card_sftAdmissibleWords_le_mul_languageCount`: `L(n + 1) ≤ N(n)` and
  `N(n + card α) ≤ card α ^ card α * L(n + 1)` for the language counts `L` and the counts `N` of
  admissible words.

## References

* D. Lind and B. Marcus, *An Introduction to Symbolic Dynamics and Coding*, Cambridge University
  Press, 1995, §2.2 (essential graphs and the pruning of stranded vertices) and §2.3 (one-step
  shifts of finite type and their graphs).
-/

public section

open Set SymbolicDynamics.FullShift

namespace TauCeti

variable {α : Type*}

section TransitionMatrix

variable (R : Type*)

/-- The `0`-`1` transition matrix of a relation `A`: its `(i, j)` entry is `1` if `A i j` holds
and `0` otherwise. -/
def sftTransitionMatrix [Zero R] [One R] (A : α → α → Bool) : Matrix α α R :=
  Matrix.of fun i j ↦ if A i j then 1 else 0

@[simp]
theorem sftTransitionMatrix_apply [Zero R] [One R] (A : α → α → Bool) (i j : α) :
    sftTransitionMatrix R A i j = if A i j then 1 else 0 :=
  (rfl)

variable {R}

/-- The entries of a transition matrix are nonnegative. -/
theorem sftTransitionMatrix_nonneg [Zero R] [One R] [Preorder R] [ZeroLEOneClass R]
    (A : α → α → Bool) (i j : α) : 0 ≤ sftTransitionMatrix R A i j := by
  rw [sftTransitionMatrix_apply]
  split_ifs
  exacts [zero_le_one, le_rfl]

/-- The path weight of a word for a transition matrix is the indicator of its admissibility. -/
theorem pathWeight_sftTransitionMatrix [CommMonoidWithZero R] (A : α → α → Bool) {n : ℕ}
    (w : Fin (n + 1) → α) :
    (sftTransitionMatrix R A).pathWeight w =
      if ∀ k : Fin n, A (w k.castSucc) (w k.succ) then 1 else 0 := by
  rw [Matrix.pathWeight_def]
  split_ifs with h
  · exact Finset.prod_eq_one fun k _ ↦ by simp [h k]
  · push Not at h
    obtain ⟨k, hk⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hk])

end TransitionMatrix

/-- The one-sided one-step subshift of finite type of a relation `A`: the sequences `x` with
`A (x k) (x (k + 1))` for every `k`. -/
def sftOneSided (A : α → α → Bool) : Set (ℕ → α) :=
  {x | ∀ k, A (x k) (x (k + 1))}

@[simp]
theorem mem_sftOneSided {A : α → α → Bool} {x : ℕ → α} :
    x ∈ sftOneSided A ↔ ∀ k, A (x k) (x (k + 1)) :=
  Iff.rfl

/-- The relation that is always true defines the full shift. -/
@[simp]
theorem sftOneSided_true : sftOneSided (fun _ _ ↦ true : α → α → Bool) = univ := by
  ext x
  simp

/-- The shift maps a subshift of finite type into itself. -/
theorem mapsTo_shift_sftOneSided (A : α → α → Bool) :
    MapsTo (shift (1 : ℕ)) (sftOneSided A) (sftOneSided A) := by
  intro x hx
  rw [mem_sftOneSided] at hx ⊢
  intro k
  simpa [shift_apply, add_assoc] using hx (1 + k)

/-- If every symbol has a successor, every admissible word extends to a point of
`sftOneSided A`. -/
theorem exists_mem_sftOneSided_of_admissible {A : α → α → Bool} (hrow : ∀ i, ∃ j, A i j)
    {n : ℕ} {w : Fin (n + 1) → α} (hw : ∀ k : Fin n, A (w k.castSucc) (w k.succ)) :
    ∃ x ∈ sftOneSided A, ∀ i : Fin (n + 1), x i = w i := by
  choose f hf using hrow
  let x : ℕ → α := fun k ↦
    if h : k ≤ n then w ⟨k, Nat.lt_succ_of_le h⟩ else f^[k - n] (w (Fin.last n))
  have hxw (k : ℕ) (hk : k ≤ n) : x k = w ⟨k, Nat.lt_succ_of_le hk⟩ := by
    simp [x, hk]
  have hx (k : ℕ) (hk : n ≤ k) : x k = f^[k - n] (w (Fin.last n)) := by
    rcases hk.eq_or_lt with rfl | hk
    · simp [hxw n le_rfl, Fin.last]
    · simp [x, hk.not_ge]
  refine ⟨x, mem_sftOneSided.2 fun k ↦ ?_, fun i ↦ by simpa using hxw i i.is_le⟩
  rcases lt_or_ge k n with hk | hk
  · rw [hxw k hk.le, hxw (k + 1) hk]
    simpa using hw ⟨k, hk⟩
  · rw [hx k hk, hx (k + 1) (by omega), show k + 1 - n = k - n + 1 by omega,
      Function.iterate_succ_apply']
    exact hf _

/-- Every word read off `sftOneSided A` is admissible. -/
theorem admissible_of_mem_wordsOf_sftOneSided {A : α → α → Bool} {n : ℕ} {w : Fin (n + 1) → α}
    (hw : w ∈ wordsOf (sftOneSided A) (n + 1)) : ∀ k : Fin n, A (w k.castSucc) (w k.succ) := by
  intro k
  obtain ⟨x, hx, hxw⟩ := mem_wordsOf.1 hw
  rw [← hxw, ← hxw]
  simpa using mem_sftOneSided.1 hx k

/-- If every symbol has a successor, the words of length `n + 1` read off `sftOneSided A` are
exactly the admissible words. -/
theorem mem_wordsOf_sftOneSided {A : α → α → Bool} (hrow : ∀ i, ∃ j, A i j) {n : ℕ}
    {w : Fin (n + 1) → α} :
    w ∈ wordsOf (sftOneSided A) (n + 1) ↔ ∀ k : Fin n, A (w k.castSucc) (w k.succ) :=
  ⟨admissible_of_mem_wordsOf_sftOneSided,
    fun hw ↦ mem_wordsOf.2 (exists_mem_sftOneSided_of_admissible hrow hw)⟩

/-- **Closing a cycle.** An admissible path `v 0, …, v q` that revisits a symbol, `v p = v q` with
`p < q`, extends to a point of `sftOneSided A` by repeating the cycle `v p, …, v (q - 1)`. -/
theorem exists_mem_sftOneSided_of_cycle {A : α → α → Bool} {v : ℕ → α} {p q : ℕ} (hpq : p < q)
    (hv : ∀ k < q, A (v k) (v (k + 1))) (hcyc : v p = v q) :
    ∃ x ∈ sftOneSided A, ∀ k ≤ q, x k = v k := by
  -- `x` follows `v` up to `p`, then repeats `v p, …, v (q - 1)` with period `q - p`.
  let x : ℕ → α := fun k ↦ if k < p then v k else v (p + (k - p) % (q - p))
  have hxv (k : ℕ) (hk : k ≤ q) : x k = v k := by
    rcases lt_or_ge k p with hkp | hkp
    · simp [x, hkp]
    rcases hk.lt_or_eq with hkq | rfl
    · simp only [x, ite_eq_right hkp.not_gt, Nat.mod_eq_of_lt (show k - p < q - p by omega),
        Nat.add_sub_cancel' hkp]
    · simp [x, hkp.not_gt, hcyc]
  have hper (k : ℕ) (hk : p ≤ k) : x (k + (q - p)) = x k := by
    simp only [x, ite_eq_right (show ¬k + (q - p) < p by omega), ite_eq_right hk.not_gt,
      show k + (q - p) - p = k - p + (q - p) by omega, Nat.add_mod_right]
  refine ⟨x, mem_sftOneSided.2 fun k ↦ ?_, hxv⟩
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases lt_or_ge k q with hk | hk
    · rw [hxv k hk.le, hxv (k + 1) hk]
      exact hv k hk
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + (q - p) := ⟨k - (q - p), by omega⟩
      rw [hper j (by omega), show j + (q - p) + 1 = j + 1 + (q - p) by omega,
        hper (j + 1) (by omega)]
      exact ih j (by omega)

/-- **Pruning.** For a finite alphabet, the first `n + 1` symbols of an admissible word of length
`m + 1 ≥ n + 1 + card α` form a word of `sftOneSided A`: two of the symbols in positions
`n, …, n + card α` coincide, closing a cycle. No symbol needs a successor. -/
theorem comp_castLE_mem_wordsOf_sftOneSided_of_admissible [Fintype α] {A : α → α → Bool}
    {n m : ℕ} (hnm : n + Fintype.card α ≤ m) {w : Fin (m + 1) → α}
    (hw : ∀ k : Fin m, A (w k.castSucc) (w k.succ)) :
    w ∘ Fin.castLE (by omega) ∈ wordsOf (sftOneSided A) (n + 1) := by
  let v : ℕ → α := fun k ↦ if h : k < m + 1 then w ⟨k, h⟩ else w 0
  have hvw (k : ℕ) (hk : k < m + 1) : v k = w ⟨k, hk⟩ := by
    simp [v, Nat.le_of_lt_succ hk]
  obtain ⟨i, j, hij, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin (Fintype.card α + 1) ↦ v (n + i)) (by simp)
  wlog hlt : i < j generalizing i j
  · exact this j i hij.symm heq.symm (lt_of_le_of_ne (not_lt.1 hlt) hij.symm)
  have := j.isLt
  obtain ⟨x, hx, hxv⟩ := exists_mem_sftOneSided_of_cycle (A := A) (v := v) (p := n + i)
    (q := n + j) (by simpa using hlt) (fun k hk ↦ by
      rw [hvw k (by omega), hvw (k + 1) (by omega)]
      exact hw ⟨k, by omega⟩) heq
  refine mem_wordsOf.2 ⟨x, hx, fun l ↦ ?_⟩
  rw [hxv l (by omega), hvw l (by omega), Function.comp_apply]
  exact congrArg w (Fin.ext (Fin.val_castLE _ l).symm)

section Admissible

open scoped Matrix

variable [Fintype α]

/-- The admissible words of length `n + 1` for a relation `A`: the words `w` with
`A (w k) (w (k + 1))` for every `k < n`. -/
def sftAdmissibleWords (A : α → α → Bool) (n : ℕ) : Finset (Fin (n + 1) → α) :=
  Finset.univ.filter fun w ↦ ∀ k : Fin n, A (w k.castSucc) (w k.succ)

@[simp]
theorem mem_sftAdmissibleWords {A : α → α → Bool} {n : ℕ} {w : Fin (n + 1) → α} :
    w ∈ sftAdmissibleWords A n ↔ ∀ k : Fin n, A (w k.castSucc) (w k.succ) := by
  simp [sftAdmissibleWords]

/-- The admissible words of length `n + 1` are counted by `∑ i, (M ^ n *ᵥ 1) i` for the transition
matrix `M` of `A`. -/
theorem card_sftAdmissibleWords [DecidableEq α] {R : Type*} [CommSemiring R] (A : α → α → Bool)
    (n : ℕ) :
    ((sftAdmissibleWords A n).card : R) = ∑ i, (sftTransitionMatrix R A ^ n *ᵥ 1) i := by
  rw [← Matrix.sum_pathWeight, sftAdmissibleWords, Finset.card_filter]
  push_cast
  exact Finset.sum_congr rfl fun w _ ↦ (pathWeight_sftTransitionMatrix A w).symm

/-- The words of length `n + 1` read off `sftOneSided A` are at most the admissible ones. -/
theorem languageCount_sftOneSided_le (A : α → α → Bool) (n : ℕ) :
    languageCount (sftOneSided A) (n + 1) ≤ (sftAdmissibleWords A n).card := by
  rw [languageCount_def, ← ncard_coe_finset]
  refine ncard_le_ncard (fun w hw ↦ ?_) (Finset.finite_toSet _)
  simpa using admissible_of_mem_wordsOf_sftOneSided hw

/-- **Pruning, counting form.** The admissible words of length `n + card α + 1` are at most
`card α ^ card α` times the words of length `n + 1` read off `sftOneSided A`: such a word is its
last `card α` symbols together with its prefix of length `n + 1`, a word of `sftOneSided A`. -/
theorem card_sftAdmissibleWords_le_mul_languageCount (A : α → α → Bool) (n : ℕ) :
    (sftAdmissibleWords A (n + Fintype.card α)).card ≤
      Fintype.card α ^ Fintype.card α * languageCount (sftOneSided A) (n + 1) := by
  set c := Fintype.card α
  let f : (Fin (n + c + 1) → α) → (Fin c → α) × (Fin (n + 1) → α) := fun w ↦
    (fun j ↦ w ⟨n + 1 + j, by omega⟩, w ∘ Fin.castLE (by omega))
  have hf : Function.Injective f := fun w w' h ↦ by
    simp only [f, Prod.mk.injEq, funext_iff, Function.comp_apply] at h
    funext i
    rcases lt_or_ge (i : ℕ) (n + 1) with hi | hi
    · simpa using h.2 ⟨i, hi⟩
    · simpa [show n + 1 + (i - (n + 1)) = i by omega] using h.1 ⟨i - (n + 1), by omega⟩
  rw [← ncard_coe_finset, languageCount_def,
    show c ^ c = (univ : Set (Fin c → α)).ncard by simp [c], ← ncard_prod]
  refine ncard_le_ncard_of_injOn f (fun w hw ↦ ⟨mem_univ _, ?_⟩) hf.injOn
    ((toFinite _).prod (toFinite _))
  exact comp_castLE_mem_wordsOf_sftOneSided_of_admissible le_rfl (by simpa using hw)

end Admissible

end TauCeti
