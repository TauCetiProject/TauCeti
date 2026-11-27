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
and if every symbol has a successor, every admissible word extends to a point of `sftOneSided A`.

## Main definitions

* `TauCeti.sftTransitionMatrix R A`: the `0`-`1` matrix of a relation `A`, with entries in `R`.
* `TauCeti.sftOneSided A`: the one-sided one-step subshift of finite type of `A`.

## Main results

* `TauCeti.pathWeight_sftTransitionMatrix`: the path weight of a word for the transition matrix is
  the indicator of its admissibility.
* `TauCeti.sftOneSided_true`: the relation that is always true defines the full shift.
* `TauCeti.mapsTo_shift_sftOneSided`: the shift maps `sftOneSided A` into itself.
* `TauCeti.exists_mem_sftOneSided_of_admissible`: if every symbol has a successor, every
  admissible word extends to a point of `sftOneSided A`.
* `TauCeti.mem_wordsOf_sftOneSided`: if every symbol has a successor, the words read off
  `sftOneSided A` are exactly the admissible words.
* `TauCeti.mem_wordsOf_sftOneSided_of_admissible`: for a finite alphabet and any relation, the
  first `n + 1` symbols of an admissible word of length at least `n + 1 + card α` are a word of
  `sftOneSided A`.
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
  have hd : 0 < q - p := by omega
  let x : ℕ → α := fun k ↦ if k ≤ q then v k else v (p + (k - p) % (q - p))
  have hx_le (k : ℕ) (hk : k ≤ q) : x k = v k := by simp [x, hk]
  have hx_ge (k : ℕ) (hk : q ≤ k) : x k = v (p + (k - p) % (q - p)) := by
    rcases hk.eq_or_lt with h | hk
    · subst h
      rw [hx_le _ le_rfl, Nat.mod_self, add_zero, hcyc]
    · simp [x, hk.not_ge]
  refine ⟨x, mem_sftOneSided.2 fun k ↦ ?_, hx_le⟩
  rcases lt_or_ge k q with hk | hk
  · rw [hx_le k hk.le, hx_le (k + 1) hk]
    exact hv k hk
  rw [hx_ge k hk, hx_ge (k + 1) (by omega), show k + 1 - p = k - p + 1 by omega,
    Nat.add_mod (k - p) 1, ← Nat.mod_mod (k - p) (q - p), ← Nat.add_mod, Nat.mod_mod]
  set r := (k - p) % (q - p)
  have hr : r < q - p := Nat.mod_lt _ hd
  rcases (Nat.succ_le_of_lt hr).lt_or_eq with hr' | hr'
  · rw [Nat.mod_eq_of_lt hr']
    simpa [add_assoc] using hv (p + r) (by omega)
  · have h := hv (p + r) (by omega)
    rw [show p + r + 1 = q by omega, ← hcyc] at h
    rw [Nat.succ_eq_add_one] at hr'
    rw [hr', Nat.mod_self, add_zero]
    exact h

/-- **Pruning.** For a finite alphabet, the first `n + 1` symbols of an admissible word of length
`m + 1 ≥ n + 1 + card α` form a word of `sftOneSided A`: two of the symbols in positions
`n, …, n + card α` coincide, closing a cycle. No symbol needs a successor. -/
theorem mem_wordsOf_sftOneSided_of_admissible [Fintype α] {A : α → α → Bool} {n m : ℕ}
    (hnm : n + Fintype.card α ≤ m) {w : Fin (m + 1) → α}
    (hw : ∀ k : Fin m, A (w k.castSucc) (w k.succ)) :
    (fun i : Fin (n + 1) ↦ w (Fin.castLE (by omega) i)) ∈ wordsOf (sftOneSided A) (n + 1) := by
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
  rw [hxv l (by omega), hvw l (by omega)]
  rfl

end TauCeti
