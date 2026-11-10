/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.Ring.Idempotent
public import TauCeti.Algebra.Ring.Commute

/-!
# Eigenvalues of sums of commuting idempotents

A finite family of pairwise commuting idempotents has a particularly rigid spectrum. If its sum
scales a nonzero vector in a torsion-free module over a domain, then the scalar is the image of a
natural number no larger than the size of the family. This bounds the possible eigenvalues without
requiring finite-dimensionality or a simultaneous eigenspace decomposition.

## Main results

* `Finset.exists_eq_natCast_of_sum_smul_eq_smul`: an eigenvalue of a finite sum of
  commuting idempotents is a bounded natural-number cast.
* `Finset.sum_smul_eq_card_smul_iff`: in characteristic zero, that sum acts on a vector by the
  number of idempotents exactly when every idempotent in the family fixes the vector.
-/

public section

namespace Finset

variable {K A M ι : Type*} [Ring K] [IsDomain K] [Semiring A]
  [AddCommGroup M] [Module K M] [Module A M] [SMulCommClass A K M]
  [Module.IsTorsionFree K M]

/-- If a finite sum of pairwise commuting idempotents scales a nonzero vector, its eigenvalue is
the cast of a natural number bounded by the number of idempotents.

No finite-dimensionality or splitting hypothesis is needed. Torsion-freeness over the domain `K`
is exactly what makes a scalar determined by its action on the nonzero vector. -/
theorem exists_eq_natCast_of_sum_smul_eq_smul
    (s : Finset ι) (p : ι → A)
    (hp : ∀ i ∈ s, IsIdempotentElem (p i))
    (hcomm : (s : Set ι).Pairwise fun i j => Commute (p i) (p j))
    {x : M} (hx : x ≠ 0) {μ : K}
    (heigen : (∑ i ∈ s, p i) • x = μ • x) :
    ∃ m : ℕ, m ≤ s.card ∧ μ = (m : K) := by
  classical
  induction s using Finset.induction_on generalizing μ x with
  | empty => exact ⟨0, Nat.zero_le _, by simpa [eq_comm, hx] using heigen⟩
  | @insert a s ha ih =>
    have hpa := hp a (mem_insert_self a s)
    have hp_s : ∀ i ∈ s, IsIdempotentElem (p i) := fun i hi => hp i (mem_insert_of_mem hi)
    have hcomm_s : (s : Set ι).Pairwise fun i j => Commute (p i) (p j) := hcomm.mono (by simp)
    -- The whole sum scales `p a • x` by `μ`. The idempotent `p a` fixes `p a • x`, so the sum
    -- over `s` scales it by `μ - 1`.
    have hpx_eigen := sum_smul_smul_eq_smul_smul _ p hcomm (mem_insert_self a s) heigen
    rw [sum_insert ha, add_smul, smul_smul (p a) (p a), hpa.eq] at hpx_eigen
    rw [sum_insert ha, add_smul] at heigen
    rw [card_insert_of_notMem ha]
    by_cases hpx : p a • x = 0
    · obtain ⟨m, hm, hμ⟩ := ih hp_s hcomm_s hx (by rwa [hpx, zero_add] at heigen)
      exact ⟨m, by omega, hμ⟩
    · obtain ⟨m, hm, hμ⟩ := ih hp_s hcomm_s hpx (μ := μ - 1) <| by
        rw [sub_smul, one_smul, ← hpx_eigen, add_sub_cancel_left]
      exact ⟨m + 1, by omega, by rw [Nat.cast_succ, ← hμ, sub_add_cancel]⟩

/-- In characteristic zero, a sum of pairwise commuting idempotents acts on a vector by the
cardinality of the family if and only if every idempotent in the family fixes that vector. The
vector may be zero. -/
theorem sum_smul_eq_card_smul_iff [CharZero K]
    (s : Finset ι) (p : ι → A)
    (hp : ∀ i ∈ s, IsIdempotentElem (p i))
    (hcomm : (s : Set ι).Pairwise fun i j => Commute (p i) (p j)) {x : M} :
    (∑ i ∈ s, p i) • x = (s.card : K) • x ↔ ∀ a ∈ s, p a • x = x := by
  classical
  refine ⟨fun heigen a ha => ?_, fun h => ?_⟩
  · -- Otherwise `x - p a • x` would be a nonzero eigenvector of the sum over `s.erase a` with
    -- eigenvalue `s.card`, exceeding the bound of `exists_eq_natCast_of_sum_smul_eq_smul`.
    by_contra hfix
    have hsum : (∑ i ∈ s, p i) • (x - p a • x) = (s.card : K) • (x - p a • x) := by
      rw [smul_sub, smul_sub, heigen, sum_smul_smul_eq_smul_smul s p hcomm ha heigen]
    have hpa : p a • (x - p a • x) = 0 := by rw [smul_sub, smul_smul, (hp a ha).eq, sub_self]
    rw [← sum_erase_add _ _ ha, add_smul, hpa, add_zero] at hsum
    obtain ⟨m, hm, hcast⟩ := (s.erase a).exists_eq_natCast_of_sum_smul_eq_smul p
      (fun i hi => hp i (mem_of_mem_erase hi)) (hcomm.mono (coe_subset.2 (erase_subset a s)))
      (sub_ne_zero.2 (Ne.symm hfix)) hsum
    have := Nat.cast_injective (R := K) hcast
    have := card_erase_of_mem ha ▸ hm
    have := card_pos.2 ⟨a, ha⟩
    omega
  · rw [sum_smul, sum_congr rfl h, sum_const, Nat.cast_smul_eq_nsmul]

end Finset
