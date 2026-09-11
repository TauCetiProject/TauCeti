/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.Ring.Idempotent

/-!
# Eigenvalues of sums of commuting idempotents

A finite family of pairwise commuting idempotents has a particularly rigid spectrum. If its sum
scales a nonzero vector in a torsion-free module over a cancellation ring, then the scalar is the
image of a natural number no larger than the size of the family. This bounds the possible
eigenvalues without requiring finite-dimensionality or a simultaneous eigenspace decomposition.

## Main results

* `Finset.exists_eq_natCast_of_sum_smul_eq_smul`: an eigenvalue of a finite sum of
  commuting idempotents is a bounded natural-number cast.
-/

public section

open scoped BigOperators

namespace Finset

variable {K A M ι : Type*} [Ring K] [IsCancelMulZero K] [Semiring A]
  [AddCommGroup M] [Module K M] [Module A M] [SMulCommClass A K M]
  [Module.IsTorsionFree K M]

/-- If a finite sum of pairwise commuting idempotents scales a nonzero vector, its eigenvalue is
the cast of a natural number bounded by the number of idempotents.

No finite-dimensionality or splitting hypothesis is needed. The torsion-free assumption is exactly
what makes a scalar determined by its action on the nonzero vector. -/
theorem exists_eq_natCast_of_sum_smul_eq_smul
    (s : Finset ι) (p : ι → A)
    (hp : ∀ i ∈ s, IsIdempotentElem (p i))
    (hcomm : (s : Set ι).Pairwise fun i j => Commute (p i) (p j))
    {x : M} (hx : x ≠ 0) {μ : K}
    (heigen : (∑ i ∈ s, p i) • x = μ • x) :
    ∃ m : ℕ, m ≤ s.card ∧ μ = (m : K) := by
  classical
  induction s using Finset.induction_on generalizing μ x with
  | empty =>
      have hμ : μ = 0 := by
        apply smul_left_injective K hx
        simpa using heigen.symm
      exact ⟨0, by simp, by simpa using hμ⟩
  | @insert a s ha ih =>
      have hpa : IsIdempotentElem (p a) := hp a (by simp)
      have hp_s : ∀ i ∈ s, IsIdempotentElem (p i) := fun i hi => hp i (by simp [hi])
      have hcomm_s : (s : Set ι).Pairwise fun i j => Commute (p i) (p j) :=
        hcomm.mono (by simp)
      have hcomm_sum : Commute (p a) (∑ i ∈ s, p i) :=
        Commute.sum_right s p (p a) fun i hi =>
          hcomm (by simp) (by simp [hi]) (by exact fun hai => ha (hai ▸ hi))
      by_cases hpx : p a • x = 0
      · obtain ⟨m, hm, hμ⟩ := ih hp_s hcomm_s hx (μ := μ) (by
          rw [Finset.sum_insert ha, add_smul, hpx, zero_add] at heigen
          exact heigen)
        exact ⟨m, hm.trans (by simp [Finset.card_insert_of_notMem ha]), hμ⟩
      · obtain ⟨m, hm, hμ⟩ := ih hp_s hcomm_s hpx (μ := μ - 1) (by
          have hrest : (∑ i ∈ s, p i) • x = μ • x - p a • x := by
            rw [Finset.sum_insert ha, add_smul] at heigen
            exact eq_sub_of_add_eq' heigen
          calc
            (∑ i ∈ s, p i) • (p a • x) =
                ((∑ i ∈ s, p i) * p a) • x := (mul_smul _ _ _).symm
            _ = (p a * ∑ i ∈ s, p i) • x := by rw [hcomm_sum.eq]
            _ = p a • ((∑ i ∈ s, p i) • x) := mul_smul _ _ _
            _ = p a • (μ • x - p a • x) := by rw [hrest]
            _ = (μ - 1) • (p a • x) := by
              rw [smul_sub, smul_comm, ← mul_smul, hpa.eq, sub_smul, one_smul])
        refine ⟨m + 1, ?_, ?_⟩
        · simpa [Finset.card_insert_of_notMem ha] using Nat.add_le_add_right hm 1
        · rw [Nat.cast_add, Nat.cast_one]
          exact eq_add_of_sub_eq hμ

end Finset
