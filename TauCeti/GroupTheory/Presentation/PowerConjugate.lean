/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Subgroup.CyclicExtension
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Upper bounds from power-conjugate relations

A triangular power-conjugate presentation gives an upper bound without a consistency or
uniqueness assumption. If each generator has a positive power in the subgroup on later
generators, and conjugating later generators by it stays in that subgroup, the generated
group is finite, of order at most the product of the power bounds.

Only one direction of conjugation is required: induction first proves the later subgroup
finite, so conjugation into it is automatically onto. No finiteness of the ambient group
is assumed. Consequently these results apply inside an abstract presented group, where the
power and conjugation relations must be proved, not merely checked in a finite image.

`finite_and_card_closure_le_of_power_conjugate` supplies both finiteness and the order bound.
The resulting expressions need not be unique, and the power bounds need not be exact orders.

## References

* D. F. Holt, B. Eick and E. A. O'Brien, *Handbook of Computational Group Theory*,
  Chapter 8, for power-conjugate presentations and collection.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G]

/-- The subgroup on a suffix of an ordered generator family. Using a natural cut also
includes the empty suffix at `n`. -/
def generatorSuffix {n : ℕ} (x : Fin n → G) (k : ℕ) : Subgroup G :=
  Subgroup.closure (x '' {i | k ≤ (i : ℕ)})

/-- The suffix subgroup is the closure of the generators at or beyond the cut. -/
theorem generatorSuffix_def {n : ℕ} (x : Fin n → G) (k : ℕ) :
    generatorSuffix x k = Subgroup.closure (x '' {i | k ≤ (i : ℕ)}) := (rfl)

/-- Membership of a generator in a suffix. -/
theorem mem_generatorSuffix {n : ℕ} (x : Fin n → G) {k : ℕ} (i : Fin n)
    (hi : k ≤ (i : ℕ)) : x i ∈ generatorSuffix x k :=
  Subgroup.subset_closure ⟨i, hi, rfl⟩

@[simp]
theorem generatorSuffix_zero {n : ℕ} (x : Fin n → G) :
    generatorSuffix x 0 = Subgroup.closure (Set.range x) := by
  simp [generatorSuffix]

@[simp]
theorem generatorSuffix_self {n : ℕ} (x : Fin n → G) : generatorSuffix x n = ⊥ := by
  have h : x '' {i : Fin n | n ≤ (i : ℕ)} = ∅ := by
    ext g
    simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists]
    intro i hi
    omega
  simp [generatorSuffix, h]

/-- Removing the first generator shifts every suffix by one. -/
theorem generatorSuffix_succ {n : ℕ} (x : Fin (n + 1) → G) (k : ℕ) :
    generatorSuffix x (k + 1) = generatorSuffix (fun i : Fin n ↦ x i.succ) k := by
  simp only [generatorSuffix_def]
  apply congrArg Subgroup.closure
  ext g
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hi0 : i ≠ 0 := by intro h; simp [h] at hi
    obtain ⟨j, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hi0
    exact ⟨j, by simpa using hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i.succ, by simpa using hi, rfl⟩

/-- The full generated subgroup is obtained by adjoining the first generator to its suffix. -/
theorem closure_range_eq_generatorSuffix_sup_zpowers {n : ℕ} (x : Fin (n + 1) → G) :
    Subgroup.closure (Set.range x) = generatorSuffix x 1 ⊔ Subgroup.zpowers (x 0) := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨i, rfl⟩
    by_cases hi : i = 0
    · exact Subgroup.mem_sup_right (hi ▸ Subgroup.mem_zpowers (x 0))
    · have hi' : (i : ℕ) ≠ 0 := fun h ↦ hi (Fin.ext h)
      exact Subgroup.mem_sup_left (mem_generatorSuffix x i (by omega))
  · refine sup_le (Subgroup.closure_mono (by rintro _ ⟨i, _, rfl⟩; exact ⟨i, rfl⟩)) ?_
    exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure ⟨0, rfl⟩)

/-- Triangular power and conjugation relations certify finiteness and the product upper bound.
For each `i`, certify a positive power in the later-generator subgroup, and certify that
conjugation by `x i` sends each later generator into that same subgroup. Relations are required
in the actual ambient group; no consistency, exact-order or uniqueness hypothesis is needed. -/
theorem finite_and_card_closure_le_of_power_conjugate {n : ℕ} (x : Fin n → G)
    (m : Fin n → ℕ) (hm : ∀ i, 0 < m i)
    (hpow : ∀ i : Fin n, x i ^ m i ∈ generatorSuffix x ((i : ℕ) + 1))
    (hconj : ∀ i j : Fin n, i < j →
      x i * x j * (x i)⁻¹ ∈ generatorSuffix x ((i : ℕ) + 1)) :
    Finite (Subgroup.closure (Set.range x)) ∧
      Nat.card (Subgroup.closure (Set.range x)) ≤ ∏ i, m i := by
  induction n with
  | zero =>
    have h : Subgroup.closure (Set.range x) = ⊥ := by simp
    rw [h]
    exact ⟨inferInstance, by simp⟩
  | succ n ih =>
    have htail := ih (fun i ↦ x i.succ) (fun i ↦ m i.succ) (fun i ↦ hm i.succ)
      (fun i ↦ by simpa only [← generatorSuffix_succ, Fin.val_succ] using hpow i.succ)
      (fun i j hij ↦ by simpa only [← generatorSuffix_succ, Fin.val_succ] using
        (hconj i.succ j.succ (by simpa using hij)))
    have heq : generatorSuffix x 1 = Subgroup.closure (Set.range (fun i : Fin n ↦ x i.succ)) := by
      rw [generatorSuffix_succ, generatorSuffix_zero]
    have : Finite (generatorSuffix x 1) := heq ▸ htail.1
    have hnorm : x 0 ∈ Subgroup.normalizer (generatorSuffix x 1) := by
      apply Subgroup.mem_normalizer_fintype
      have hle : generatorSuffix x 1 ≤
          (generatorSuffix x 1).comap (MulAut.conj (x 0)).toMonoidHom := by
        rw [generatorSuffix_def]
        apply (Subgroup.closure_le _).mpr
        rintro _ ⟨j, hj, rfl⟩
        have hj' : 1 ≤ (j : ℕ) := hj
        exact hconj 0 j (by
          simp only [Fin.lt_def, Fin.val_zero]
          omega)
      exact fun g hg ↦ hle hg
    obtain ⟨hf, hc⟩ := (generatorSuffix x 1).finite_and_card_sup_zpowers_le (hm 0) hnorm
      (hpow 0)
    rw [closure_range_eq_generatorSuffix_sup_zpowers]
    refine ⟨hf, hc.trans ?_⟩
    rw [heq, Fin.prod_univ_succ]
    simpa only [mul_comm] using Nat.mul_le_mul_right (m 0) htail.2

end TauCeti
