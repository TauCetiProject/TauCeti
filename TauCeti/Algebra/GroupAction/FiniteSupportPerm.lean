module

public import Mathlib.GroupTheory.GroupAction.FixedPoints
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Finitely supported permutations

This file records small bridges for Mathlib's finite-support predicate for permutations,
`(MulAction.fixedBy ι π)ᶜ.Finite`.
-/

public section

namespace TauCeti

variable {ι : Type*}

/-- Constructor for Mathlib's finite-support predicate from an eventual fixedness bound. -/
theorem finite_compl_fixedBy_of_eventually_eq_self {π : Equiv.Perm ℕ}
    (hπ : ∃ N, ∀ n, N ≤ n → π n = n) : (MulAction.fixedBy ℕ π)ᶜ.Finite := by
  rcases hπ with ⟨N, hN⟩
  exact (Set.finite_Iio N).subset fun n hn => by
    by_contra hnN
    have hfixed : n ∈ MulAction.fixedBy ℕ π := by
      simpa [MulAction.mem_fixedBy, Equiv.Perm.smul_def] using hN n (not_lt.mp hnN)
    exact hn hfixed

/-- A permutation of `ℕ` with finite Mathlib support fixes every sufficiently large index. -/
theorem finite_compl_fixedBy_eventually_eq_self {π : Equiv.Perm ℕ}
    (hπ : (MulAction.fixedBy ℕ π)ᶜ.Finite) : ∃ N, ∀ n, N ≤ n → π n = n := by
  rcases hπ.bddAbove with ⟨N, hN⟩
  refine ⟨N + 1, fun n hn => ?_⟩
  by_contra hne
  have hn_support : n ∈ (MulAction.fixedBy ℕ π)ᶜ := by
    simpa [MulAction.mem_fixedBy, Equiv.Perm.smul_def] using hne
  exact (not_lt_of_ge hn) (Nat.lt_succ_of_le (hN hn_support))

/-- A permutation of `ℕ` is finitely supported iff it fixes all sufficiently large indices. -/
theorem finite_compl_fixedBy_iff_eventually_eq_self {π : Equiv.Perm ℕ} :
    (MulAction.fixedBy ℕ π)ᶜ.Finite ↔ ∃ N, ∀ n, N ≤ n → π n = n :=
  ⟨finite_compl_fixedBy_eventually_eq_self, finite_compl_fixedBy_of_eventually_eq_self⟩

/-- Conjugating a permutation preserves Mathlib's finite-support predicate. -/
theorem finite_compl_fixedBy_conj {π σ : Equiv.Perm ι}
    (hσ : (MulAction.fixedBy ι σ)ᶜ.Finite) :
    (MulAction.fixedBy ι (π⁻¹ * σ * π))ᶜ.Finite := by
  refine (hσ.image π.symm).subset fun n hn => ?_
  refine ⟨π n, ?_, by simp⟩
  have hn' : π.symm (σ (π n)) ≠ n := by
    simpa [MulAction.mem_fixedBy, Equiv.Perm.smul_def, Equiv.Perm.mul_apply] using hn
  rw [Set.mem_compl_iff, MulAction.mem_fixedBy, Equiv.Perm.smul_def]
  intro hfixed
  exact hn' (by simp [hfixed])

end TauCeti
