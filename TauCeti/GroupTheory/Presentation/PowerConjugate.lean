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

`finite_closure_of_power_conjugate` supplies finiteness, and
`card_closure_le_of_power_conjugate` supplies the order bound. The resulting expressions
need not be unique, and the power bounds need not be exact orders.

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

/-- A suffix subgroup lies in a subgroup exactly when each of its generators does. -/
@[simp]
theorem generatorSuffix_le_iff {n : ℕ} (x : Fin n → G) (k : ℕ) (H : Subgroup G) :
    generatorSuffix x k ≤ H ↔ ∀ i : Fin n, k ≤ (i : ℕ) → x i ∈ H := by
  simp [generatorSuffix_def, Subgroup.closure_le, Set.subset_def]

/-- Each generator at or beyond the cut belongs to the suffix subgroup. -/
theorem apply_mem_generatorSuffix {n : ℕ} (x : Fin n → G) {k : ℕ} (i : Fin n)
    (hi : k ≤ (i : ℕ)) : x i ∈ generatorSuffix x k :=
  Subgroup.subset_closure ⟨i, hi, rfl⟩

@[simp]
theorem generatorSuffix_zero {n : ℕ} (x : Fin n → G) :
    generatorSuffix x 0 = Subgroup.closure (Set.range x) := by
  simp [generatorSuffix]

/-- Increasing the cut shrinks the suffix subgroup. -/
theorem generatorSuffix_antitone {n : ℕ} (x : Fin n → G) : Antitone (generatorSuffix x) := by
  intro k l hkl
  simp only [generatorSuffix_def]
  exact Subgroup.closure_mono (Set.image_mono (fun _ hi ↦ hkl.trans hi))

/-- Every suffix at or beyond the length of the family is trivial. -/
theorem generatorSuffix_eq_bot_of_le {n : ℕ} (x : Fin n → G) {k : ℕ} (hnk : n ≤ k) :
    generatorSuffix x k = ⊥ := by
  have h : x '' {i : Fin n | k ≤ (i : ℕ)} = ∅ := by
    ext g
    simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists]
    intro i hi
    omega
  simp [generatorSuffix, h]

@[simp]
theorem generatorSuffix_self {n : ℕ} (x : Fin n → G) : generatorSuffix x n = ⊥ :=
  generatorSuffix_eq_bot_of_le x le_rfl

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
  rw [Fin.range_fin_succ, Set.insert_eq, Subgroup.closure_union,
    ← Subgroup.zpowers_eq_closure, sup_comm, generatorSuffix_succ, generatorSuffix_zero,
    Fin.tail_def]

-- The induction establishes finiteness before using it to turn one-sided conjugation
-- into normalization. Its two conclusions are exposed separately below.
private theorem power_conjugate_bound {n : ℕ} (x : Fin n → G)
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
      have h : (generatorSuffix x 1).map (MulAut.conj (x 0)).toMonoidHom ≤
          generatorSuffix x 1 := by
        rw [Subgroup.map_le_iff_le_comap, generatorSuffix_le_iff]
        intro j hj
        simpa using hconj 0 j (by
          simp only [Fin.lt_def, Fin.val_zero]
          omega)
      exact fun g hg ↦ h ⟨g, hg, rfl⟩
    have hf := (generatorSuffix x 1).finite_sup_zpowers (hm 0) hnorm (hpow 0)
    have hc := (generatorSuffix x 1).card_sup_zpowers_le (hm 0) hnorm (hpow 0)
    rw [closure_range_eq_generatorSuffix_sup_zpowers]
    refine ⟨hf, hc.trans ?_⟩
    rw [heq, Fin.prod_univ_succ]
    simpa only [mul_comm] using Nat.mul_le_mul_right (m 0) htail.2

/-- Triangular power and conjugation relations certify finiteness of the generated subgroup.
The relations must hold in the actual ambient group. Only conjugation of later generators
by earlier ones is required; no consistency or uniqueness hypothesis is needed. -/
theorem finite_closure_of_power_conjugate {n : ℕ} (x : Fin n → G)
    (m : Fin n → ℕ) (hm : ∀ i, 0 < m i)
    (hpow : ∀ i : Fin n, x i ^ m i ∈ generatorSuffix x ((i : ℕ) + 1))
    (hconj : ∀ i j : Fin n, i < j →
      x i * x j * (x i)⁻¹ ∈ generatorSuffix x ((i : ℕ) + 1)) :
    Finite (Subgroup.closure (Set.range x)) :=
  (power_conjugate_bound x m hm hpow hconj).1

/-- Triangular power and conjugation relations bound the order by the product of the positive
power bounds. The relations must hold in the actual ambient group; the bounds need not be
exact relative orders, and expressions in the generators need not be unique. -/
theorem card_closure_le_of_power_conjugate {n : ℕ} (x : Fin n → G)
    (m : Fin n → ℕ) (hm : ∀ i, 0 < m i)
    (hpow : ∀ i : Fin n, x i ^ m i ∈ generatorSuffix x ((i : ℕ) + 1))
    (hconj : ∀ i j : Fin n, i < j →
      x i * x j * (x i)⁻¹ ∈ generatorSuffix x ((i : ℕ) + 1)) :
    Nat.card (Subgroup.closure (Set.range x)) ≤ ∏ i, m i :=
  (power_conjugate_bound x m hm hpow hconj).2

end TauCeti
