module

public import Mathlib.GroupTheory.Perm.ClosureSwap
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Finitely supported permutations

This file records the generic finite-support predicate for permutations, together with the
basic closure API used by exchangeability constructions.
-/

public section

namespace TauCeti

namespace Probability

variable {ι : Type*}

/-- A permutation is finitely supported if it moves only finitely many indices. -/
def IsFinitelySupportedPerm (π : Equiv.Perm ι) : Prop :=
  Set.Finite {i : ι | π i ≠ i}

/-- Constructor for finitely supported permutations from an eventual fixedness bound. -/
theorem isFinitelySupportedPerm_of_eventually_eq_self {π : Equiv.Perm ℕ}
    (hπ : ∃ N, ∀ n, N ≤ n → π n = n) : IsFinitelySupportedPerm π := by
  rcases hπ with ⟨N, hN⟩
  exact (Set.finite_Iio N).subset fun n hn => by
    by_contra hnN
    exact hn (hN n (not_lt.mp hnN))

/-- The identity permutation is finitely supported. -/
theorem isFinitelySupportedPerm_one : IsFinitelySupportedPerm (1 : Equiv.Perm ι) := by
  rw [IsFinitelySupportedPerm]
  simp

/-- A finitely supported permutation fixes every sufficiently large index. -/
theorem IsFinitelySupportedPerm.eventually_eq_self {π : Equiv.Perm ℕ}
    (hπ : IsFinitelySupportedPerm π) : ∃ N, ∀ n, N ≤ n → π n = n := by
  rcases hπ.bddAbove with ⟨N, hN⟩
  refine ⟨N + 1, fun n hn => ?_⟩
  by_contra hne
  have hn_support : n ∈ {k : ℕ | π k ≠ k} := hne
  exact (not_lt_of_ge hn) (Nat.lt_succ_of_le (hN hn_support))

/-- A permutation of `ℕ` is finitely supported iff it fixes all sufficiently large indices. -/
theorem isFinitelySupportedPerm_iff_eventually_eq_self {π : Equiv.Perm ℕ} :
    IsFinitelySupportedPerm π ↔ ∃ N, ∀ n, N ≤ n → π n = n :=
  ⟨IsFinitelySupportedPerm.eventually_eq_self, isFinitelySupportedPerm_of_eventually_eq_self⟩

/-- A transposition is finitely supported. -/
theorem isFinitelySupportedPerm_swap [DecidableEq ι] (a b : ι) :
    IsFinitelySupportedPerm (Equiv.swap a b) := by
  rw [IsFinitelySupportedPerm]
  simpa only [MulAction.fixedBy, Equiv.Perm.smul_def, Set.compl_setOf] using
    (finite_compl_fixedBy_swap (x := a) (y := b))

/-- The product of finitely supported permutations is finitely supported. -/
theorem IsFinitelySupportedPerm.mul {π σ : Equiv.Perm ι}
    (hπ : IsFinitelySupportedPerm π) (hσ : IsFinitelySupportedPerm σ) :
    IsFinitelySupportedPerm (π * σ) := by
  rw [IsFinitelySupportedPerm] at hπ hσ ⊢
  exact (hπ.union hσ).subset (Equiv.Perm.set_support_mul_subset π σ)

/-- The inverse of a finitely supported permutation is finitely supported. -/
theorem IsFinitelySupportedPerm.symm {π : Equiv.Perm ι}
    (hπ : IsFinitelySupportedPerm π) : IsFinitelySupportedPerm π.symm := by
  rw [IsFinitelySupportedPerm] at hπ ⊢
  simpa [Equiv.Perm.set_support_symm_eq π] using hπ

end Probability

end TauCeti
