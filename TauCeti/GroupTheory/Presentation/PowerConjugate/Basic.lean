/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Subgroup.CyclicExtension
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Bounded normal forms and upper bounds from power-conjugate relations

A triangular power-conjugate presentation gives an upper bound without a consistency or
uniqueness assumption. If each generator has a positive power in the subgroup on later
generators, and conjugating later generators by it stays in that subgroup, the generated
group is finite, of order at most the product of the power bounds.

Only one direction of conjugation is required: induction first proves the later subgroup
finite, so conjugation into it is automatically onto. No finiteness of the ambient group
is assumed. Consequently these results apply inside an abstract presented group, where the
power and conjugation relations must be proved, not merely checked in a finite image.

`powerConjugateNormalForm` evaluates bounded exponent tuples as descending products
in the generated subgroup. `powerConjugateNormalForm_surjective` proves that these
expressions cover it, using the cyclic-extension convention `h * x ^ k` of
`Subgroup.mem_sup_zpowers_iff_exists_mul_pow`.

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

/-- For a finite suffix subgroup, to normalize it it suffices to conjugate each suffix generator
back into it. Finiteness supplies the reverse inclusion, so no inverse conjugation relations
are required. -/
theorem mem_normalizer_generatorSuffix {n : ℕ} (x : Fin n → G) (k : ℕ)
    [Finite (generatorSuffix x k)] {g : G}
    (hconj : ∀ i : Fin n, k ≤ (i : ℕ) → g * x i * g⁻¹ ∈ generatorSuffix x k) :
    g ∈ Subgroup.normalizer (generatorSuffix x k) := by
  apply Subgroup.mem_normalizer_fintype
  have h : (generatorSuffix x k).map (MulAut.conj g).toMonoidHom ≤ generatorSuffix x k := by
    rw [Subgroup.map_le_iff_le_comap, generatorSuffix_le_iff]
    exact hconj
  exact fun y hy ↦ h ⟨y, hy, rfl⟩

/-- Evaluate bounded exponents in descending generator order, as an element of the subgroup
generated by `x`. This map is defined even without power-conjugate relations; those relations
ensure that it is surjective. -/
def powerConjugateNormalForm {n : ℕ} (x : Fin n → G) (m : Fin n → ℕ)
    (e : ∀ i, Fin (m i)) : Subgroup.closure (Set.range x) :=
  ⟨(List.ofFn fun i ↦ x i ^ (e i : ℕ)).reverse.prod, by
    apply Subgroup.list_prod_mem
    intro g hg
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (List.mem_reverse.mp hg)
    exact Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_range_self i)) _⟩

/-- The underlying element is the product of the bounded powers in descending order. -/
@[simp]
theorem coe_powerConjugateNormalForm {n : ℕ} (x : Fin n → G) (m : Fin n → ℕ)
    (e : ∀ i, Fin (m i)) :
    (powerConjugateNormalForm x m e : G) =
      (List.ofFn fun i ↦ x i ^ (e i : ℕ)).reverse.prod := (rfl)

/-- Separate the power of the first generator from the normal form on the remaining generators.
The first generator occurs on the right. -/
theorem coe_powerConjugateNormalForm_succ {n : ℕ} (x : Fin (n + 1) → G)
    (m : Fin (n + 1) → ℕ) (e : ∀ i, Fin (m i)) :
    (powerConjugateNormalForm x m e : G) =
      (powerConjugateNormalForm (fun i ↦ x i.succ) (fun i ↦ m i.succ)
        (fun i ↦ e i.succ) : G) * x 0 ^ (e 0 : ℕ) := by
  simp [List.ofFn_succ]

/-- **Existence of bounded power-conjugate normal forms.** Positive triangular power bounds and
one-sided conjugation relations imply that every element of the generated subgroup is the
descending product of powers with the given exponent bounds. No uniqueness is assumed. -/
theorem powerConjugateNormalForm_surjective {n : ℕ} (x : Fin n → G)
    (m : Fin n → ℕ) (hm : ∀ i, 0 < m i)
    (hpow : ∀ i : Fin n, x i ^ m i ∈ generatorSuffix x ((i : ℕ) + 1))
    (hconj : ∀ i j : Fin n, i < j →
      x i * x j * (x i)⁻¹ ∈ generatorSuffix x ((i : ℕ) + 1)) :
    Function.Surjective (powerConjugateNormalForm x m) := by
  induction n with
  | zero =>
    intro g
    refine ⟨(fun i ↦ i.elim0), Subtype.ext ?_⟩
    have hg : (g : G) = 1 := by simpa using g.property
    simp [hg]
  | succ n ih =>
    have hpow' (i : Fin n) :
        x i.succ ^ m i.succ ∈ generatorSuffix (fun j ↦ x j.succ) ((i : ℕ) + 1) := by
      simpa only [← generatorSuffix_succ, Fin.val_succ] using hpow i.succ
    have hconj' (i j : Fin n) (hij : i < j) :
        x i.succ * x j.succ * (x i.succ)⁻¹ ∈
          generatorSuffix (fun j ↦ x j.succ) ((i : ℕ) + 1) := by
      simpa only [← generatorSuffix_succ, Fin.val_succ] using
        hconj i.succ j.succ (by simpa using hij)
    have htail := ih (fun i ↦ x i.succ) (fun i ↦ m i.succ) (fun i ↦ hm i.succ)
      hpow' hconj'
    have heq : generatorSuffix x 1 = Subgroup.closure (Set.range (fun i : Fin n ↦ x i.succ)) := by
      rw [generatorSuffix_succ, generatorSuffix_zero]
    have : Finite (generatorSuffix x 1) := heq ▸
      Finite.of_surjective _ htail
    -- Finiteness of the suffix turns the one-sided conjugation relations into normalization.
    have hnorm : x 0 ∈ Subgroup.normalizer (generatorSuffix x 1) := by
      apply mem_normalizer_generatorSuffix
      intro j hj
      simpa using hconj 0 j (by
        simp only [Fin.lt_def, Fin.val_zero]
        omega)
    intro g
    have hg : (g : G) ∈ generatorSuffix x 1 ⊔ Subgroup.zpowers (x 0) :=
      closure_range_eq_generatorSuffix_sup_zpowers x ▸ g.property
    obtain ⟨h, k, hk⟩ :=
      ((generatorSuffix x 1).mem_sup_zpowers_iff_exists_mul_pow (hm 0) hnorm (hpow 0)).mp hg
    obtain ⟨e, he⟩ := htail ⟨h, heq ▸ h.property⟩
    refine ⟨Fin.cons k e, Subtype.ext ?_⟩
    rw [coe_powerConjugateNormalForm_succ]
    simpa only [Fin.cons_zero, Fin.cons_succ, he] using hk

/-- Triangular power and conjugation relations certify finiteness of the generated subgroup.
The relations must hold in the actual ambient group. Only conjugation of later generators
by earlier ones is required; no consistency or uniqueness hypothesis is needed. -/
theorem finite_closure_of_power_conjugate {n : ℕ} (x : Fin n → G)
    (m : Fin n → ℕ) (hm : ∀ i, 0 < m i)
    (hpow : ∀ i : Fin n, x i ^ m i ∈ generatorSuffix x ((i : ℕ) + 1))
    (hconj : ∀ i j : Fin n, i < j →
      x i * x j * (x i)⁻¹ ∈ generatorSuffix x ((i : ℕ) + 1)) :
    Finite (Subgroup.closure (Set.range x)) :=
  Finite.of_surjective _ (powerConjugateNormalForm_surjective x m hm hpow hconj)

/-- Triangular power and conjugation relations bound the order by the product of the positive
power bounds. The relations must hold in the actual ambient group; the bounds need not be
exact relative orders, and expressions in the generators need not be unique. -/
theorem card_closure_le_of_power_conjugate {n : ℕ} (x : Fin n → G)
    (m : Fin n → ℕ) (hm : ∀ i, 0 < m i)
    (hpow : ∀ i : Fin n, x i ^ m i ∈ generatorSuffix x ((i : ℕ) + 1))
    (hconj : ∀ i j : Fin n, i < j →
      x i * x j * (x i)⁻¹ ∈ generatorSuffix x ((i : ℕ) + 1)) :
    Nat.card (Subgroup.closure (Set.range x)) ≤ ∏ i, m i := by
  simpa using Nat.card_le_card_of_surjective _
    (powerConjugateNormalForm_surjective x m hm hpow hconj)

end TauCeti
