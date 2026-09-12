/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.NoZeroSMulDivisors.Basic
public import Mathlib.Algebra.Ring.Idempotent

/-!
# Eigenvalues of sums of commuting idempotents

A finite family of pairwise commuting idempotents has a particularly rigid spectrum. If its sum
scales a nonzero vector in a module with no zero scalar divisors, then the scalar is the image of a
natural number no larger than the size of the family. This bounds the possible eigenvalues without
requiring finite-dimensionality or a simultaneous eigenspace decomposition.

## Main results

* `Finset.exists_eq_natCast_of_sum_smul_eq_smul`: an eigenvalue of a finite sum of
  commuting idempotents is a bounded natural-number cast.
* `Finset.smul_eq_self_of_sum_smul_eq_card_smul`: if that eigenvalue is the number of
  idempotents, every idempotent in the family fixes the vector.
-/

public section

open scoped BigOperators

namespace Finset

variable {K A M ι : Type*} [Ring K] [Semiring A]
  [AddCommGroup M] [Module K M] [Module A M] [SMulCommClass A K M]
  [NoZeroSMulDivisors K M]

/-- If a finite sum of pairwise commuting idempotents scales a nonzero vector, its eigenvalue is
the cast of a natural number bounded by the number of idempotents.

No finite-dimensionality or splitting hypothesis is needed. The no-zero-scalar-divisors assumption
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
  | empty =>
      have hμ : μ = 0 := by
        exact (eq_zero_or_eq_zero_of_smul_eq_zero (by simpa using heigen.symm)).resolve_right hx
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

/-- If a sum of commuting idempotents acts on a vector by the cardinality of the family, then
every idempotent in the family fixes that vector.

The statement includes the zero vector, where the conclusion is immediate. For a nonzero vector,
apply `Finset.exists_eq_natCast_of_sum_smul_eq_smul` after projecting to the zero eigenspace of the
chosen idempotent; the resulting eigenvalue would have to be both `s.card` and at most one less. -/
theorem smul_eq_self_of_sum_smul_eq_card_smul
    {K A ι : Type*} [DivisionRing K] [CharZero K] [Ring A]
    [Module K A] [SMulCommClass A K A]
    (s : Finset ι) (p : ι → A)
    (hp : ∀ i ∈ s, IsIdempotentElem (p i))
    (hcomm : (s : Set ι).Pairwise fun i j => Commute (p i) (p j))
    {x : A} (heigen : (∑ i ∈ s, p i) • x = (s.card : K) • x)
    {a : ι} (ha : a ∈ s) : p a • x = x := by
  classical
  let y := (1 - p a) • x
  have hpa := hp a ha
  have hpa_y : p a • y = 0 := by
    dsimp only [y]
    rw [← mul_smul, mul_sub, mul_one, hpa.eq, sub_self, zero_smul]
  have hsumcomm : Commute (∑ i ∈ s, p i) (1 - p a) := by
    apply Commute.sum_left
    intro i hi
    rcases eq_or_ne i a with rfl | hia
    · exact (Commute.one_right _).sub_right (Commute.refl _)
    · exact (Commute.one_right _).sub_right (hcomm hi ha hia)
  have hsum_y : (∑ i ∈ s, p i) • y = (s.card : K) • y := by
    dsimp only [y]
    calc
      (∑ i ∈ s, p i) • ((1 - p a) • x) =
          (1 - p a) • ((∑ i ∈ s, p i) • x) := by
        rw [← mul_smul, ← mul_smul, hsumcomm.eq]
      _ = (1 - p a) • ((s.card : K) • x) := by rw [heigen]
      _ = (s.card : K) • ((1 - p a) • x) := smul_comm _ _ _
  have hrest_y : (∑ i ∈ s.erase a, p i) • y = (s.card : K) • y := by
    rw [← Finset.sum_erase_add _ _ ha, add_smul, hpa_y] at hsum_y
    simpa using hsum_y
  by_contra hfix
  have hy : y ≠ 0 := by
    intro hy
    apply hfix
    dsimp only [y] at hy
    rw [sub_smul, one_smul, sub_eq_zero] at hy
    exact hy.symm
  obtain ⟨m, hm, hcast⟩ := (s.erase a).exists_eq_natCast_of_sum_smul_eq_smul p
    (fun i hi => hp i (Finset.mem_of_mem_erase hi))
    (hcomm.mono fun i hi => Finset.mem_of_mem_erase hi) hy hrest_y
  have hcard : s.card = m := Nat.cast_injective (R := K) hcast
  have hpos : 0 < s.card := Finset.card_pos.mpr ⟨a, ha⟩
  rw [Finset.card_erase_of_mem ha] at hm
  omega

end Finset
