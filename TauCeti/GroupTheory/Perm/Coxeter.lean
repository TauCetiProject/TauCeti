/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Perm.Cycle.Concrete
public import Mathlib.Logic.Equiv.Fin.Rotate
public import TauCeti.GroupTheory.Coxeter.ExchangeCondition
public import TauCeti.GroupTheory.SpecificGroups.Braid.Basic
import TauCeti.Data.List.Rotate

/-!
# The symmetric group as the Coxeter group of type `A`

The symmetric group on `n` letters is the Coxeter group of type `A_{n-1}`: with the adjacent
transpositions `s i = (i i+1)`, `i < n - 1`, as simple reflections, `Equiv.Perm (Fin n)` is
presented by the Coxeter matrix `CoxeterMatrix.A (n - 1)`. This file constructs that Coxeter
system, `TauCeti.permCoxeterSystem n`, and identifies its combinatorics:

* a simple reflection `s i` is a right descent of `σ` exactly when `σ` reverses the order of the
  two letters `i` and `i + 1`;
* the Coxeter length of `σ` is its number of inversions, the pairs `x < y` with `σ y < σ x`;
* a Coxeter element, a product of all the adjacent transpositions each taken once in any order, is
  an `n`-cycle, so the Coxeter number of type `A_{n-1}` is `n`. In the natural order the product
  `s 0 * s 1 * ⋯ * s (n - 2)` is the cycle `(0 1 ⋯ n-1)`.

The indexing follows `TauCeti.BraidGroup`: the simple reflection `s i` is
`TauCeti.BraidGroup.transposition i`, which swaps the strands `TauCeti.BraidGroup.strand i` and
`TauCeti.BraidGroup.strandSucc i`, so that the canonical map from the braid group onto this
Coxeter group is the strand permutation `TauCeti.BraidGroup.permHom`.

With the Coxeter system in place, the general Coxeter theory applies to permutations: reduced
words and the length API of `Mathlib.GroupTheory.Coxeter.Length`, and Matsumoto's theorem
`TauCeti.matsumoto`, which evaluates braid-relation-satisfying generators of any monoid along
reduced words of a permutation. That is the form in which the standard basis `T_w` of a type-`A`
Iwahori–Hecke algebra is defined.

## Main definitions

* `TauCeti.permCoxeterSystem n`: the Coxeter system of type `A_{n-1}` on `Equiv.Perm (Fin n)`.

## Main results

* `TauCeti.permCoxeterSystem_simple`: its simple reflections are the adjacent transpositions.
* `TauCeti.isRightDescent_permCoxeterSystem_iff` and `TauCeti.isLeftDescent_permCoxeterSystem_iff`:
  descents are the reversed adjacent pairs of `σ` and of `σ⁻¹`.
* `TauCeti.permCoxeterSystem_length_eq_card_inversion`: the Coxeter length is the number of
  inversions.
* `TauCeti.isCycle_wordProd_permCoxeterSystem`, `TauCeti.cycleType_wordProd_permCoxeterSystem`
  and `TauCeti.orderOf_wordProd_permCoxeterSystem`: every Coxeter element is a cycle through all
  `n` letters, of order `n`.
* `TauCeti.permCoxeterSystem_wordProd_finRange`: the Coxeter element in the natural order is
  `finRotate n`.
* `TauCeti.BraidGroup.permHom_eq_toCoxeterGroup`: the strand permutation of a braid is the
  canonical map from the Artin group of type `A` onto its Coxeter group.

## Implementation notes

The Coxeter system is produced by `CoxeterSystem.ofExchange`, the characterization of Coxeter
systems by the exchange condition. The exchange condition for adjacent transpositions comes from
one observation: along a word `s_{a₁} ⋯ s_{aₖ}` for `σ`, follow the two values taken at the letters
`i` and `i + 1` by the suffix products `s_{aⱼ} ⋯ s_{aₖ}`. An adjacent transposition reverses the
relative order of exactly one pair of values, so if `σ` reverses the order of `i` and `i + 1`, some
letter `s_{aⱼ}` reverses that pair, and deleting it spells `σ * s i`.

That a Coxeter element is an `n`-cycle is proved for all orderings at once, by induction on `k`: a
word using each of `s 0, …, s (k - 1)` exactly once spells a cycle through the letters `0, …, k`.
Cutting a word that uses each of `s 0, …, s k` once at its letter `s k` writes it as `a * s k * b`,
which is conjugate by `a` to `s k * (b * a)`. The word for `b * a` uses each of
`s 0, …, s (k - 1)` once, so it spells a cycle through `0, …, k`, and composing with `s k`, the
transposition of `k` with the new letter `k + 1`, inserts `k + 1` into that cycle.

## References

* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Springer GTM 231 (2005),
  Sections 1.5 and 1.6.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, CUP (1990), Section 1.9.
-/

public section

open TauCeti TauCeti.BraidGroup

namespace TauCeti

variable {n : ℕ}

/-- The product of two adjacent transpositions has the order prescribed by the type-`A` Coxeter
matrix. -/
private theorem orderOf_transposition_mul_transposition (i j : Fin (n - 1)) :
    orderOf (transposition i * transposition j) = CoxeterMatrix.A (n - 1) i j := by
  rcases eq_or_ne i j with rfl | hij
  · simp
  have hne : transposition i * transposition j ≠ 1 := fun h ↦
    hij (transposition_injective (mul_eq_one_iff_eq_inv.mp h |>.trans
      (inv_eq_of_mul_eq_one_right (transposition_mul_self j))))
  have hv : (i : ℕ) ≠ j := fun hv ↦ hij (Fin.ext hv)
  by_cases hadj : (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i
  · rw [coxeterMatrixA_eq_three hadj]
    refine orderOf_eq_prime ?_ hne
    calc (transposition i * transposition j) ^ 3
        = (transposition i * transposition j * transposition i) *
            (transposition j * transposition i * transposition j) := by
          simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = (transposition i * transposition j * transposition i) *
            (transposition i * transposition j * transposition i) := by
          rw [transposition_braid hadj]
      _ = 1 := by
          simp only [← mul_assoc, mul_transposition_mul_self, transposition_mul_self]
  · have h2 : (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i := by omega
    rw [coxeterMatrixA_eq_two h2]
    refine orderOf_eq_prime ?_ hne
    rw [pow_two, mul_assoc, ← mul_assoc (transposition j),
      ← transposition_mul_transposition_comm h2, mul_assoc, transposition_mul_self, mul_one,
      transposition_mul_self]

/-- **Exchange for adjacent transpositions.** If the product `σ` of a word in the adjacent
transpositions reverses the order of the letters `i` and `i + 1`, then deleting one letter of the
word spells `σ * s i`. The word need not be reduced. -/
private theorem exists_prod_eraseIdx_eq_mul_transposition (ω : List (Fin (n - 1)))
    {i : Fin (n - 1)} (h : (ω.map transposition).prod (strandSucc i) <
      (ω.map transposition).prod (strand i)) :
    ∃ j < ω.length, ((ω.eraseIdx j).map transposition).prod =
      (ω.map transposition).prod * transposition i := by
  induction ω with
  | nil =>
    simp only [List.map_nil, List.prod_nil, Equiv.Perm.coe_one, id_eq,
      Fin.lt_def, val_strand, val_strandSucc] at h
    omega
  | cons a ω ih =>
    simp only [List.map_cons, List.prod_cons, Equiv.Perm.coe_mul, Function.comp_apply] at h ⊢
    set τ := (ω.map transposition).prod
    rcases (τ.injective.ne (strand_ne_strandSucc i).symm).lt_or_gt with hτ | hlt
    · obtain ⟨j, hj, he⟩ := ih hτ
      exact ⟨j + 1, by simpa using hj, by simp [he, mul_assoc]⟩
    · obtain ⟨h₁, h₂⟩ := eq_strand_of_transposition_lt hlt h
      have hcomm : τ * transposition i = transposition a * τ := by
        rw [transposition_eq_swap, Equiv.mul_swap_eq_swap_mul, h₁, h₂, ← transposition_eq_swap]
      refine ⟨0, by simp, ?_⟩
      rw [List.eraseIdx_cons_zero, mul_assoc, hcomm, ← mul_assoc, transposition_mul_self, one_mul]

/-- The homomorphism from the Coxeter group of type `A_{n-1}` to the symmetric group sending each
simple reflection to the corresponding adjacent transposition. -/
private noncomputable def toPerm (n : ℕ) : (CoxeterMatrix.A (n - 1)).Group →* Equiv.Perm (Fin n) :=
  (CoxeterMatrix.A (n - 1)).toCoxeterSystem.lift
    ⟨transposition, fun i j ↦ by
      rw [← orderOf_transposition_mul_transposition]
      exact pow_orderOf_eq_one _⟩

private theorem toPerm_simple (i : Fin (n - 1)) :
    toPerm n ((CoxeterMatrix.A (n - 1)).toCoxeterSystem.simple i) = transposition i :=
  CoxeterSystem.lift_apply_simple _ _ i

private theorem toPerm_wordProd (ω : List (Fin (n - 1))) :
    toPerm n ((CoxeterMatrix.A (n - 1)).toCoxeterSystem.wordProd ω) =
      (ω.map transposition).prod := by
  rw [CoxeterSystem.wordProd, map_list_prod, List.map_map]
  exact congrArg List.prod (List.map_congr_left fun i _ ↦ CoxeterSystem.lift_apply_simple _ _ i)

private theorem toPerm_surjective (n : ℕ) : Function.Surjective (toPerm n) := by
  have h : (toPerm n).comp (ArtinGroup.toCoxeterGroup (CoxeterMatrix.A (n - 1)).toCoxeterSystem) =
      permHom n := BraidGroup.hom_ext fun i ↦ by
    rw [MonoidHom.comp_apply, sigma_eq_gen, ArtinGroup.toCoxeterGroup_gen, ← sigma_eq_gen,
      permHom_sigma]
    exact CoxeterSystem.lift_apply_simple _ _ i
  have hs := permHom_surjective n
  rw [← h, MonoidHom.coe_comp] at hs
  exact hs.of_comp

/-- The least number of adjacent transpositions whose product is `σ`. -/
private noncomputable def wordLength (n : ℕ) (σ : Equiv.Perm (Fin n)) : ℕ :=
  sInf {k | ∃ ω : List (Fin (n - 1)),
    toPerm n ((CoxeterMatrix.A (n - 1)).toCoxeterSystem.wordProd ω) = σ ∧ ω.length = k}

private theorem isLeast_wordLength (σ : Equiv.Perm (Fin n)) :
    IsLeast {k | ∃ ω : List (Fin (n - 1)),
      toPerm n ((CoxeterMatrix.A (n - 1)).toCoxeterSystem.wordProd ω) = σ ∧ ω.length = k}
      (wordLength n σ) := by
  obtain ⟨w, rfl⟩ := toPerm_surjective n σ
  obtain ⟨ω, rfl⟩ := (CoxeterMatrix.A (n - 1)).toCoxeterSystem.wordProd_surjective w
  exact ⟨Nat.sInf_mem ⟨_, ω, rfl, rfl⟩, fun _ hk ↦ Nat.sInf_le hk⟩

private theorem exchange_toPerm (ω : List (Fin (n - 1))) (i : Fin (n - 1))
    (hω : wordLength n (toPerm n ((CoxeterMatrix.A (n - 1)).toCoxeterSystem.wordProd ω)) =
      ω.length)
    (hi : wordLength n (toPerm n ((CoxeterMatrix.A (n - 1)).toCoxeterSystem.wordProd ω *
      (CoxeterMatrix.A (n - 1)).toCoxeterSystem.simple i)) ≤ ω.length) :
    ∃ j < ω.length, toPerm n ((CoxeterMatrix.A (n - 1)).toCoxeterSystem.wordProd (ω.eraseIdx j)) =
      toPerm n ((CoxeterMatrix.A (n - 1)).toCoxeterSystem.wordProd ω *
        (CoxeterMatrix.A (n - 1)).toCoxeterSystem.simple i) := by
  simp only [map_mul, toPerm_simple, toPerm_wordProd] at hω hi ⊢
  set σ := (ω.map transposition).prod
  rcases (σ.injective.ne (strand_ne_strandSucc i).symm).lt_or_gt with hd | hlt
  · exact exists_prod_eraseIdx_eq_mul_transposition ω hd
  -- Otherwise `σ * s i` reverses the pair, and deleting a letter from one of its shortest words
  -- would spell `σ` with fewer than `ω.length` letters.
  exfalso
  obtain ⟨ω', hω', hlen⟩ := (isLeast_wordLength (σ * transposition i)).1
  rw [toPerm_wordProd] at hω'
  have hrev : (ω'.map transposition).prod (strandSucc i) <
      (ω'.map transposition).prod (strand i) := by
    simpa [hω'] using hlt
  obtain ⟨j, hj, he⟩ := exists_prod_eraseIdx_eq_mul_transposition ω' hrev
  rw [hω', mul_transposition_mul_self] at he
  have hle := (isLeast_wordLength σ).2 ⟨ω'.eraseIdx j, by rw [toPerm_wordProd, he], rfl⟩
  rw [List.length_eraseIdx_of_lt hj] at hle
  omega

/-- The symmetric group `Equiv.Perm (Fin n)` as the Coxeter group of type `A_{n-1}`, with the
adjacent transpositions `TauCeti.BraidGroup.transposition i` as simple reflections. -/
noncomputable def permCoxeterSystem (n : ℕ) :
    CoxeterSystem (CoxeterMatrix.A (n - 1)) (Equiv.Perm (Fin n)) :=
  (CoxeterMatrix.A (n - 1)).toCoxeterSystem.ofExchange (toPerm n) (wordLength n)
    (fun i j ↦ by
      rw [toPerm_simple, toPerm_simple]
      exact orderOf_transposition_mul_transposition i j)
    isLeast_wordLength exchange_toPerm

/-- The simple reflections of the type-`A` Coxeter system on `Equiv.Perm (Fin n)` are the
adjacent transpositions. -/
@[simp]
theorem permCoxeterSystem_simple (i : Fin (n - 1)) :
    (permCoxeterSystem n).simple i = transposition i := by
  rw [permCoxeterSystem, CoxeterSystem.ofExchange_simple, toPerm_simple]

/-- A word in the type-`A` Coxeter system on `Equiv.Perm (Fin n)` spells the product of the
corresponding adjacent transpositions. -/
@[simp]
theorem permCoxeterSystem_wordProd (ω : List (Fin (n - 1))) :
    (permCoxeterSystem n).wordProd ω = (ω.map transposition).prod := by
  rw [CoxeterSystem.wordProd, funext permCoxeterSystem_simple]

/-- Right multiplication by `s i` shortens a permutation that reverses the order of the letters
`i` and `i + 1`. -/
private theorem length_mul_transposition_lt {σ : Equiv.Perm (Fin n)} {i : Fin (n - 1)}
    (h : σ (strandSucc i) < σ (strand i)) :
    (permCoxeterSystem n).length (σ * transposition i) < (permCoxeterSystem n).length σ := by
  obtain ⟨ω, hω, rfl⟩ := (permCoxeterSystem n).exists_isReduced σ
  rw [permCoxeterSystem_wordProd] at h
  obtain ⟨j, hj, he⟩ := exists_prod_eraseIdx_eq_mul_transposition ω h
  have hle := (permCoxeterSystem n).length_wordProd_le (ω.eraseIdx j)
  rw [permCoxeterSystem_wordProd, he, List.length_eraseIdx_of_lt hj] at hle
  rw [hω.eq, permCoxeterSystem_wordProd]
  omega

/-- **Right descents of a permutation.** The simple reflection `s i` is a right descent of `σ`
exactly when `σ` reverses the order of the letters `i` and `i + 1`. -/
theorem isRightDescent_permCoxeterSystem_iff {σ : Equiv.Perm (Fin n)} {i : Fin (n - 1)} :
    (permCoxeterSystem n).IsRightDescent σ i ↔ σ (strandSucc i) < σ (strand i) := by
  refine ⟨fun hd ↦ ?_, fun h ↦ by
    simpa [CoxeterSystem.IsRightDescent] using length_mul_transposition_lt h⟩
  rcases (σ.injective.ne (strand_ne_strandSucc i).symm).lt_or_gt with h | hlt
  · exact h
  exfalso
  have hlen := length_mul_transposition_lt (σ := σ * transposition i) (i := i)
    (by simpa using hlt)
  rw [mul_transposition_mul_self] at hlen
  rw [CoxeterSystem.IsRightDescent, permCoxeterSystem_simple] at hd
  omega

/-- **Left descents of a permutation.** The simple reflection `s i` is a left descent of `σ`
exactly when `σ⁻¹` reverses the order of the letters `i` and `i + 1`. -/
theorem isLeftDescent_permCoxeterSystem_iff {σ : Equiv.Perm (Fin n)} {i : Fin (n - 1)} :
    (permCoxeterSystem n).IsLeftDescent σ i ↔ σ⁻¹ (strandSucc i) < σ⁻¹ (strand i) := by
  rw [← CoxeterSystem.isRightDescent_inv_iff, isRightDescent_permCoxeterSystem_iff]

/-- Right multiplication by `s i` adds one inversion to a permutation that keeps the letters `i`
and `i + 1` in order. -/
private theorem card_inversions_mul_transposition {σ : Equiv.Perm (Fin n)} {i : Fin (n - 1)}
    (h : σ (strand i) < σ (strandSucc i)) :
    (Finset.univ.filter fun p : Fin n × Fin n =>
        p.1 < p.2 ∧ (σ * transposition i) p.2 < (σ * transposition i) p.1).card =
      (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ σ p.2 < σ p.1).card + 1 := by
  set τ := transposition i
  set e : Fin n × Fin n ≃ Fin n × Fin n := Equiv.prodCongr τ τ
  have hτ : τ.symm = τ := by simp [τ, transposition_eq_swap]
  have hset : (Finset.univ.filter fun p : Fin n × Fin n =>
        p.1 < p.2 ∧ (σ * τ) p.2 < (σ * τ) p.1) =
      insert (strand i, strandSucc i) ((Finset.univ.filter fun p : Fin n × Fin n =>
        p.1 < p.2 ∧ σ p.2 < σ p.1).map e.toEmbedding) := by
    ext ⟨x, y⟩
    rw [Finset.mem_insert, Finset.mem_map_equiv, Finset.mem_filter, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, Prod.mk.injEq, e, Equiv.prodCongr_symm,
      Equiv.prodCongr_apply, Prod.map_apply, hτ, Equiv.Perm.coe_mul, Function.comp_apply]
    constructor
    · rintro ⟨hxy, hσ⟩
      rcases (τ.injective.ne hxy.ne).lt_or_gt with hτxy | hyx
      · exact .inr ⟨hτxy, hσ⟩
      · exact .inl (eq_strand_of_transposition_lt hxy hyx)
    · rintro (⟨rfl, rfl⟩ | ⟨hτxy, hσ⟩)
      · refine ⟨Fin.lt_def.mpr (by simp), ?_⟩
        simpa [τ] using h
      · refine ⟨?_, hσ⟩
        by_contra hxy
        have hyx : y < x := lt_of_le_of_ne (not_lt.mp hxy) fun hyx ↦ by
          simp [hyx] at hτxy
        obtain ⟨rfl, rfl⟩ := eq_strand_of_transposition_lt hyx hτxy
        simp only [τ, transposition_apply_strand, transposition_apply_strandSucc] at hσ
        exact lt_asymm hσ h
  rw [hset, Finset.card_insert_of_notMem, Finset.card_map]
  rw [Finset.mem_map_equiv, Finset.mem_filter]
  simp only [e, Equiv.prodCongr_symm, Equiv.prodCongr_apply, Prod.map_apply, hτ, τ,
    transposition_apply_strand, transposition_apply_strandSucc]
  rintro ⟨-, hlt, -⟩
  exact lt_asymm hlt (Fin.lt_def.mpr (by simp))

/-- **The Coxeter length of a permutation is its number of inversions**, the pairs of letters
`x < y` with `σ y < σ x`. -/
theorem permCoxeterSystem_length_eq_card_inversion (σ : Equiv.Perm (Fin n)) :
    (permCoxeterSystem n).length σ =
      (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ σ p.2 < σ p.1).card := by
  induction hk : (permCoxeterSystem n).length σ generalizing σ with
  | zero =>
    rw [(permCoxeterSystem n).length_eq_zero_iff] at hk
    subst hk
    rw [eq_comm, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro p - ⟨h₁, h₂⟩
    exact lt_asymm h₁ h₂
  | succ k ih =>
    have hσ : σ ≠ 1 := fun h ↦ by simp [h] at hk
    obtain ⟨i, hi⟩ := (permCoxeterSystem n).exists_rightDescent_of_ne_one hσ
    have hdesc := isRightDescent_permCoxeterSystem_iff.mp hi
    have hlen : (permCoxeterSystem n).length (σ * transposition i) = k := by
      have := (permCoxeterSystem n).length_mul_simple σ i
      rw [CoxeterSystem.IsRightDescent] at hi
      rw [permCoxeterSystem_simple] at this hi
      omega
    have hcard := card_inversions_mul_transposition (σ := σ * transposition i) (i := i)
      (by simpa using hdesc)
    rw [mul_transposition_mul_self] at hcard
    rw [hcard, ← ih _ hlen]

/-! ### Coxeter elements -/

/-- A product of adjacent transpositions `s i` with `i < k` preserves the letters `≤ k`. -/
private theorem val_prod_map_transposition_le_iff {k : ℕ} {ω : List (Fin (n - 1))}
    (hω : ∀ i ∈ ω, (i : ℕ) < k) (y : Fin n) :
    ((ω.map transposition).prod y : ℕ) ≤ k ↔ (y : ℕ) ≤ k := by
  induction ω with
  | nil => simp
  | cons a ω ih =>
    have ha := hω a (List.mem_cons_self ..)
    rw [List.map_cons, List.prod_cons, Equiv.Perm.mul_apply, val_transposition_apply,
      ← ih fun i hi ↦ hω i (List.mem_cons_of_mem a hi)]
    split_ifs <;> omega

/-- The core induction: a product of the adjacent transpositions `s i`, `i < k`, each taken once
in any order, is the cycle through the letters `0, …, k` in some order. -/
private theorem exists_formPerm_eq_prod_map_transposition (k : ℕ) (hk : k < n)
    (ω : List (Fin (n - 1))) (hω : ω.Nodup) (hmem : ∀ i, i ∈ ω ↔ (i : ℕ) < k) :
    ∃ L : List (Fin n), L.Nodup ∧ (∀ x, x ∈ L ↔ (x : ℕ) ≤ k) ∧
      (ω.map transposition).prod = L.formPerm := by
  induction k generalizing ω with
  | zero =>
    obtain rfl : ω = [] := List.eq_nil_iff_forall_not_mem.mpr fun i hi ↦ by
      simpa using (hmem i).1 hi
    exact ⟨[⟨0, hk⟩], List.nodup_singleton _, fun x ↦ by simp [Fin.ext_iff], by simp⟩
  | succ k ih =>
    -- Split the word at its letter `s k`.
    let m : Fin (n - 1) := ⟨k, by omega⟩
    obtain ⟨ω₁, ω₂, rfl⟩ := List.append_of_mem ((hmem m).2 (Nat.lt_succ_self k))
    obtain ⟨hmn, hnd⟩ := List.nodup_cons.mp (List.nodup_middle.mp hω)
    have hlt : ∀ i ∈ ω₁ ++ ω₂, (i : ℕ) < k := fun i hi ↦ by
      have h₁ := (hmem i).1 (by simp only [List.mem_append, List.mem_cons] at hi ⊢; tauto)
      have h₂ : i ≠ m := fun h ↦ hmn (h ▸ hi)
      simp only [ne_eq, Fin.ext_iff, m] at h₂
      omega
    obtain ⟨L, hLnd, hLmem, hL⟩ := ih (by omega) (ω₂ ++ ω₁) (List.nodup_append_comm.mp hnd)
      fun i ↦ ⟨fun hi ↦ hlt i (by simp only [List.mem_append] at hi ⊢; tauto), fun hi ↦ by
        have h := (hmem i).2 (by omega)
        have h' : i ≠ m := fun h ↦ by simp [h, m] at hi
        simp only [List.mem_append, List.mem_cons] at h ⊢
        tauto⟩
    -- Rotate the cycle so that it starts at the letter `k`.
    obtain ⟨p, hp⟩ : ∃ p : Fin n, (p : ℕ) = k := ⟨⟨k, by omega⟩, rfl⟩
    obtain ⟨q, hq⟩ : ∃ q : Fin n, (q : ℕ) = k + 1 := ⟨⟨k + 1, hk⟩, rfl⟩
    obtain ⟨L₁, L₂, rfl⟩ := List.append_of_mem ((hLmem p).2 hp.le)
    have hrot : (L₁ ++ p :: L₂) ~r (p :: (L₂ ++ L₁)) := by
      simpa using List.isRotated_append (l := L₁) (l' := p :: L₂)
    have hmemq : ∀ y, y ∈ q :: p :: (L₂ ++ L₁) ↔ (y : ℕ) ≤ k + 1 := fun y ↦ by
      rw [List.mem_cons, ← hrot.mem_iff, hLmem, Fin.ext_iff]
      omega
    obtain ⟨A, hAdef⟩ : ∃ A, (ω₁.map transposition).prod = A := ⟨_, rfl⟩
    have hA : ∀ y, (A y : ℕ) ≤ k + 1 ↔ (y : ℕ) ≤ k + 1 :=
      hAdef ▸ val_prod_map_transposition_le_iff fun i hi ↦ (hmem i).1 (by simp [hi])
    refine ⟨(q :: p :: (L₂ ++ L₁)).map A, ?_, fun x ↦ ?_, ?_⟩
    · refine List.Nodup.map A.injective (List.nodup_cons.mpr ⟨fun h ↦ ?_, hrot.nodup_iff.mp hLnd⟩)
      have := (hLmem q).1 (hrot.mem_iff.mpr h)
      omega
    · rw [List.mem_map]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact (hA y).2 ((hmemq y).1 hy)
      · intro hx
        exact ⟨A.symm x, (hmemq _).2 ((hA _).1 (by simpa using hx)), by simp⟩
    · rw [List.formPerm_map_equiv, List.formPerm_cons_cons,
        ← List.formPerm_eq_of_isRotated hLnd hrot, ← hL]
      have hm : transposition m = Equiv.swap q p := by
        rw [transposition_eq_swap, Equiv.swap_comm]
        congr 1 <;> exact Fin.ext (by simp [m, hp, hq])
      simp only [List.map_append, List.map_cons, List.prod_append, List.prod_cons, hm, hAdef]
      ext x
      simp

/-- A word using each simple reflection of `S_n` exactly once spells a single cycle through all `n`
letters. -/
private theorem exists_formPerm_eq_wordProd_permCoxeterSystem {ω : List (Fin (n - 1))}
    (hω : ω.Perm (List.finRange (n - 1))) (hn : n ≠ 0) :
    ∃ L : List (Fin n), L.Nodup ∧ L.length = n ∧ (permCoxeterSystem n).wordProd ω = L.formPerm := by
  obtain ⟨L, hLnd, hLmem, hL⟩ := exists_formPerm_eq_prod_map_transposition (n - 1) (by omega) ω
    (hω.nodup_iff.mpr (List.nodup_finRange _)) fun i ↦ by simp [hω.mem_iff]
  refine ⟨L, hLnd, ?_, by rw [permCoxeterSystem_wordProd, hL]⟩
  have huniv : L.toFinset = Finset.univ :=
    Finset.eq_univ_of_forall fun x ↦ List.mem_toFinset.mpr ((hLmem x).2 (by omega))
  rw [← List.toFinset_card_of_nodup hLnd, huniv, Finset.card_univ, Fintype.card_fin]

/-- **A Coxeter element of `S_n` is an `n`-cycle.** A product of all the adjacent transpositions,
each taken once in any order, is a cycle. -/
theorem isCycle_wordProd_permCoxeterSystem {ω : List (Fin (n - 1))}
    (hω : ω.Perm (List.finRange (n - 1))) (hn : 2 ≤ n) :
    ((permCoxeterSystem n).wordProd ω).IsCycle := by
  obtain ⟨L, hLnd, hLlen, hL⟩ := exists_formPerm_eq_wordProd_permCoxeterSystem hω (by omega)
  exact hL ▸ List.isCycle_formPerm hLnd (by rw [hLlen]; exact hn)

/-- A Coxeter element of `S_n`, for `n ≥ 2`, moves every letter. -/
theorem support_wordProd_permCoxeterSystem {ω : List (Fin (n - 1))}
    (hω : ω.Perm (List.finRange (n - 1))) (hn : 2 ≤ n) :
    ((permCoxeterSystem n).wordProd ω).support = Finset.univ := by
  obtain ⟨L, hLnd, hLlen, hL⟩ := exists_formPerm_eq_wordProd_permCoxeterSystem hω (by omega)
  rw [hL, List.support_formPerm_of_nodup L hLnd fun x hx ↦ by simp [hx] at hLlen; omega]
  refine Finset.eq_univ_of_card _ ?_
  rw [List.toFinset_card_of_nodup hLnd, hLlen, Fintype.card_fin]

/-- The cycle type of a Coxeter element of `S_n`, for `n ≥ 2`, is `{n}`. -/
theorem cycleType_wordProd_permCoxeterSystem {ω : List (Fin (n - 1))}
    (hω : ω.Perm (List.finRange (n - 1))) (hn : 2 ≤ n) :
    ((permCoxeterSystem n).wordProd ω).cycleType = {n} := by
  rw [(isCycle_wordProd_permCoxeterSystem hω hn).cycleType,
    support_wordProd_permCoxeterSystem hω hn, Finset.card_univ, Fintype.card_fin]

/-- Any two letters lie in the same cycle of a Coxeter element of `S_n`. -/
theorem sameCycle_wordProd_permCoxeterSystem {ω : List (Fin (n - 1))}
    (hω : ω.Perm (List.finRange (n - 1))) (x y : Fin n) :
    ((permCoxeterSystem n).wordProd ω).SameCycle x y := by
  rcases lt_or_ge n 2 with hn | hn
  · obtain rfl : x = y := Fin.ext (by omega)
    exact Equiv.Perm.SameCycle.refl _ _
  · have hsupp := support_wordProd_permCoxeterSystem hω hn
    exact (isCycle_wordProd_permCoxeterSystem hω hn).sameCycle
      (Equiv.Perm.mem_support.mp (hsupp ▸ Finset.mem_univ x))
      (Equiv.Perm.mem_support.mp (hsupp ▸ Finset.mem_univ y))

/-- **The Coxeter number of type `A_{n-1}` is `n`.** Every Coxeter element of `S_n`, a product of
all the adjacent transpositions each taken once in any order, has order `n`. -/
theorem orderOf_wordProd_permCoxeterSystem {ω : List (Fin (n - 1))}
    (hω : ω.Perm (List.finRange (n - 1))) (hn : n ≠ 0) :
    orderOf ((permCoxeterSystem n).wordProd ω) = n := by
  rcases lt_or_ge n 2 with hn' | hn'
  · obtain rfl : n = 1 := by omega
    rw [Subsingleton.elim ((permCoxeterSystem 1).wordProd ω) 1, orderOf_one]
  · rw [(isCycle_wordProd_permCoxeterSystem hω hn').orderOf,
      support_wordProd_permCoxeterSystem hω hn', Finset.card_univ, Fintype.card_fin]

/-- The product `s 0 * ⋯ * s (k - 1)` of the first `k` adjacent transpositions is the cycle
`(0 1 ⋯ k)`. -/
private theorem val_prod_map_transposition_take_finRange {k : ℕ} (hk : k ≤ n - 1) (x : Fin n) :
    ((((List.finRange (n - 1)).take k).map transposition).prod x : ℕ) =
      if (x : ℕ) < k then (x : ℕ) + 1 else if (x : ℕ) = k then 0 else x := by
  induction k generalizing x with
  | zero =>
    simp only [List.take_zero, List.map_nil, List.prod_nil, Equiv.Perm.coe_one, id_eq]
    split_ifs <;> omega
  | succ k ih =>
    rw [List.take_add_one, List.getElem?_eq_getElem (by simp; omega), List.getElem_finRange,
      Option.toList_some, List.map_append,
      List.prod_append, List.map_singleton, List.prod_singleton, Equiv.Perm.mul_apply,
      ih (by omega), val_transposition_apply]
    simp only [Fin.val_cast]
    split_ifs <;> omega

/-- **The Coxeter cycle of `S_n`.** The Coxeter element `s 0 * s 1 * ⋯ * s (n - 2)`, the product
of the adjacent transpositions in their natural order, is the cycle `(0 1 ⋯ n-1)`, that is
`finRotate n : i ↦ i + 1` modulo `n`. -/
theorem permCoxeterSystem_wordProd_finRange :
    (permCoxeterSystem n).wordProd (List.finRange (n - 1)) = finRotate n := by
  ext x
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := x.pos; omega⟩
  have h := val_prod_map_transposition_take_finRange (n := m + 1) (k := m) le_rfl x
  rw [List.take_of_length_le (by simp)] at h
  rw [permCoxeterSystem_wordProd, h, coe_finRotate]
  simp only [Fin.ext_iff, Fin.val_last]
  split_ifs <;> omega

end TauCeti

namespace TauCeti.BraidGroup

/-- The strand permutation of a braid is the canonical map from the Artin group of type `A` onto
its Coxeter group, realized as the symmetric group. -/
theorem permHom_eq_toCoxeterGroup (n : ℕ) :
    permHom n = ArtinGroup.toCoxeterGroup (TauCeti.permCoxeterSystem n) :=
  hom_ext fun i ↦ by
    rw [permHom_sigma, sigma_eq_gen, ArtinGroup.toCoxeterGroup_gen, permCoxeterSystem_simple]

end TauCeti.BraidGroup
