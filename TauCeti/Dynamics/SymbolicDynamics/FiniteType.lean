/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Dynamics.SymbolicDynamics.Basic
public import TauCeti.LinearAlgebra.Matrix.PathWeight

/-!
# One-sided one-step subshifts of finite type

For a relation `A : α → α → Bool` on an alphabet `α`, the one-sided one-step subshift of finite
type `TauCeti.sftOneSided A ⊆ ℕ → α` consists of the sequences `x` with `A (x k) (x (k + 1))` for
every `k`; it is mapped into itself by the shift. Its `0`-`1` transition matrix
`TauCeti.transitionMatrix R A` has path weight `1` on the admissible words and `0` on the others,
and if every symbol has a successor, every admissible word extends to a point of `sftOneSided A`.

## Main definitions

* `TauCeti.transitionMatrix R A`: the `0`-`1` matrix of a relation `A`, with entries in `R`.
* `TauCeti.sftOneSided A`: the one-sided one-step subshift of finite type of `A`.

## Main results

* `TauCeti.pathWeight_transitionMatrix`: the path weight of a word for the transition matrix is
  the indicator of its admissibility.
* `TauCeti.mapsTo_shift_sftOneSided`: the shift maps `sftOneSided A` into itself.
* `TauCeti.exists_mem_sftOneSided_of_admissible`: if every symbol has a successor, every
  admissible word extends to a point of `sftOneSided A`.
-/

public section

open Set SymbolicDynamics.FullShift

namespace TauCeti

variable {α : Type*}

section TransitionMatrix

variable (R : Type*)

/-- The `0`-`1` transition matrix of a relation `A`: its `(i, j)` entry is `1` if `A i j` holds
and `0` otherwise. -/
def transitionMatrix [Zero R] [One R] (A : α → α → Bool) : Matrix α α R :=
  Matrix.of fun i j ↦ if A i j then 1 else 0

@[simp]
theorem transitionMatrix_apply [Zero R] [One R] (A : α → α → Bool) (i j : α) :
    transitionMatrix R A i j = if A i j then 1 else 0 :=
  (rfl)

variable {R}

/-- The entries of a transition matrix are nonnegative. -/
theorem transitionMatrix_nonneg [Zero R] [One R] [Preorder R] [ZeroLEOneClass R]
    (A : α → α → Bool) (i j : α) : 0 ≤ transitionMatrix R A i j := by
  rw [transitionMatrix_apply]
  split_ifs
  exacts [zero_le_one, le_rfl]

/-- The path weight of a word for a transition matrix is the indicator of its admissibility. -/
theorem pathWeight_transitionMatrix [CommMonoidWithZero R] (A : α → α → Bool) {n : ℕ}
    (w : Fin (n + 1) → α) :
    (transitionMatrix R A).pathWeight w =
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

end TauCeti
