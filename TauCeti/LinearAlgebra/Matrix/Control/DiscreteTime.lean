/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Control.Reachable

/-!
# Reachability for the discrete-time linear system

The discrete-time linear time-invariant system with state matrix `A : Matrix n n R` and input
matrix `B : Matrix n m R` evolves by `x(k+1) = A x(k) + B u(k)`. Its state at time `k`, started at
`x₀` and driven by the input sequence `u : ℕ → m → R`, is
`A ^ k x₀ + ∑_{j < k} A ^ j B u(k - 1 - j)`.

The states reached from the origin in exactly `k` steps are the span of the columns of `A ^ j * B`
for `j < k`. Combined with the Cayley–Hamilton reduction of the reachable subspace, this shows
that `(A, B)` is controllable exactly when every state can be steered to every other state in
`Fintype.card n` steps.

## Main definitions

* `Matrix.discreteState A B x₀ u k`: the state at time `k` of the discrete-time system.

## Main results

* `Matrix.discreteState_eq`: the variation-of-constants formula for the state.
* `Matrix.setOf_discreteState_zero`: the states reached from `0` in `k` steps are the span of the
  columns of `A ^ j * B` for `j < k`.
* `Matrix.isControllable_iff_forall_exists_discreteState`: `(A, B)` is controllable if and only if
  every state can be steered to every state in `Fintype.card n` steps.

## References

* Eduardo D. Sontag, *Mathematical Control Theory: Deterministic Finite Dimensional Systems*,
  second edition, Springer, 1998: Corollary 3.2.10 (a) and Theorem 2 (p. 88).
-/

public section

open Finset

namespace Matrix

variable {R : Type*} {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]

section CommSemiring

variable [CommSemiring R] (A : Matrix n n R) (B : Matrix n m R) (x₀ : n → R) (u : ℕ → m → R)

/-- The state at time `k` of the discrete-time system `x(k+1) = A x(k) + B u(k)` with initial
state `x₀` and input sequence `u`. -/
def discreteState : ℕ → n → R
  | 0 => x₀
  | k + 1 => A *ᵥ discreteState k + B *ᵥ u k

omit [DecidableEq n] in
@[simp]
theorem discreteState_zero : discreteState A B x₀ u 0 = x₀ := by
  simp [discreteState]

omit [DecidableEq n] in
@[simp]
theorem discreteState_succ (k : ℕ) :
    discreteState A B x₀ u (k + 1) = A *ᵥ discreteState A B x₀ u k + B *ᵥ u k := by
  simp [discreteState]

/-- The variation-of-constants formula for the discrete-time system: the state at time `k` is
`A ^ k x₀ + ∑_{j < k} A ^ j B u(k - 1 - j)`. -/
theorem discreteState_eq (k : ℕ) :
    discreteState A B x₀ u k = A ^ k *ᵥ x₀ + ∑ j ∈ range k, (A ^ j * B) *ᵥ u (k - 1 - j) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [discreteState_succ, ih, sum_range_succ']
    simp [mulVec_add, mulVec_sum, mulVec_mulVec, ← Matrix.mul_assoc, ← pow_succ', Nat.sub_sub,
      add_assoc, Nat.add_comm 1]

/-- The state started at `0` is the input response `∑_{j < k} A ^ j B u(k - 1 - j)`. -/
theorem discreteState_zero_initial (k : ℕ) :
    discreteState A B 0 u k = ∑ j ∈ range k, (A ^ j * B) *ᵥ u (k - 1 - j) := by
  rw [discreteState_eq, mulVec_zero, zero_add]

/-- The state started at `x₀` is the free motion `A ^ k x₀` plus the state started at `0` with
the same input. -/
theorem discreteState_eq_pow_mulVec_add (k : ℕ) :
    discreteState A B x₀ u k = A ^ k *ᵥ x₀ + discreteState A B 0 u k := by
  rw [discreteState_eq, discreteState_zero_initial]

/-- The states reached from `0` in exactly `k` steps are the span of the columns of `A ^ j * B`
for `j < k`. -/
theorem setOf_discreteState_zero (k : ℕ) :
    {x | ∃ u : ℕ → m → R, discreteState A B 0 u k = x} =
      ((⨆ j : Fin k, LinearMap.range (A ^ (j : ℕ) * B).mulVecLin : Submodule R (n → R)) :
        Set (n → R)) := by
  ext x
  simp only [Set.mem_ofPred_eq, SetLike.mem_coe]
  constructor
  · rintro ⟨u, rfl⟩
    rw [discreteState_zero_initial]
    exact Submodule.sum_mem _ fun j hj =>
      Submodule.mem_iSup_of_mem ⟨j, mem_range.1 hj⟩ ⟨u (k - 1 - j), rfl⟩
  · intro hx
    refine Submodule.iSup_induction (fun j : Fin k => LinearMap.range (A ^ (j : ℕ) * B).mulVecLin)
      (motive := fun x => ∃ u : ℕ → m → R, discreteState A B 0 u k = x) hx ?_
      ⟨0, by simp [discreteState_zero_initial]⟩ ?_
    · -- the input `v` applied at the single time `k - 1 - j` produces the column `A ^ j B v`
      rintro j _ ⟨v, rfl⟩
      refine ⟨Pi.single (k - 1 - j) v, ?_⟩
      rw [discreteState_zero_initial, sum_eq_single (j : ℕ)]
      · simp
      · intro i hi hij
        rw [Pi.single_eq_of_ne (by have := mem_range.1 hi; omega), mulVec_zero]
      · exact fun h => absurd (mem_range.2 j.isLt) h
    · rintro _ _ ⟨u, rfl⟩ ⟨u', rfl⟩
      refine ⟨u + u', ?_⟩
      simp only [discreteState_zero_initial, Pi.add_apply, mulVec_add, sum_add_distrib]

end CommSemiring

section CommRing

variable [CommRing R] (A : Matrix n n R) (B : Matrix n m R)

/-- The pair `(A, B)` is controllable if and only if the discrete-time system can be steered from
every state to every state in `Fintype.card n` steps. -/
theorem isControllable_iff_forall_exists_discreteState :
    IsControllable A B ↔
      ∀ x₀ x₁ : n → R, ∃ u : ℕ → m → R, discreteState A B x₀ u (Fintype.card n) = x₁ := by
  have hset := setOf_discreteState_zero A B (Fintype.card n)
  rw [← reachableSubspace_eq_iSup_fin_card, Set.ext_iff] at hset
  simp only [Set.mem_ofPred_eq, SetLike.mem_coe] at hset
  rw [isControllable_iff, Submodule.eq_top_iff']
  refine ⟨fun h x₀ x₁ => ?_, fun h x => ?_⟩
  · obtain ⟨u, hu⟩ := (hset _).2 (h (x₁ - A ^ Fintype.card n *ᵥ x₀))
    exact ⟨u, by rw [discreteState_eq_pow_mulVec_add, hu, add_sub_cancel]⟩
  · obtain ⟨u, hu⟩ := h 0 x
    exact (hset x).1 ⟨u, hu⟩

end CommRing

end Matrix
