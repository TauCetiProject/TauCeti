/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Coxeter.ExchangeCondition
public import TauCeti.GroupTheory.SpecificGroups.Braid.Basic

/-!
# The symmetric group as the Coxeter group of type `A`

The symmetric group on `n` letters is the Coxeter group of type `A_{n-1}`: with the adjacent
transpositions `s i = (i i+1)`, `i < n - 1`, as simple reflections, `Equiv.Perm (Fin n)` is
presented by the Coxeter matrix `CoxeterMatrix.A (n - 1)`. This file constructs that Coxeter
system, `Equiv.Perm.coxeterSystem n`, and identifies its combinatorics:

* a simple reflection `s i` is a right descent of `σ` exactly when `σ` reverses the order of the
  two letters `i` and `i + 1`;
* the Coxeter length of `σ` is its number of inversions, the pairs `x < y` with `σ y < σ x`.

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

* `Equiv.Perm.coxeterSystem n`: the Coxeter system of type `A_{n-1}` on `Equiv.Perm (Fin n)`.

## Main results

* `Equiv.Perm.coxeterSystem_simple`: its simple reflections are the adjacent transpositions.
* `Equiv.Perm.isRightDescent_coxeterSystem_iff` and `Equiv.Perm.isLeftDescent_coxeterSystem_iff`:
  descents are the reversed adjacent pairs of `σ` and of `σ⁻¹`.
* `Equiv.Perm.length_coxeterSystem`: the Coxeter length is the number of inversions.
* `TauCeti.BraidGroup.permHom_eq_toCoxeterGroup`: the strand permutation of a braid is the
  canonical map from the Artin group of type `A` onto its Coxeter group.

## Implementation notes

The Coxeter system is produced by `CoxeterSystem.ofExchange`, the characterization of Coxeter
systems by the exchange condition. The exchange condition for adjacent transpositions comes from
one observation: along a word `s_{a₁} ⋯ s_{aₖ}` for `σ`, follow the two values taken at the letters
`i` and `i + 1` by the suffix products `s_{aⱼ} ⋯ s_{aₖ}`. An adjacent transposition reverses the
relative order of exactly one pair of values, so if `σ` reverses the order of `i` and `i + 1`, some
letter `s_{aⱼ}` reverses that pair, and deleting it spells `σ * s i`.

## References

* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Springer GTM 231 (2005),
  Sections 1.5 and 1.6.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, CUP (1990), Section 1.9.
-/

public section

open TauCeti TauCeti.BraidGroup

namespace Equiv.Perm

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
          simp only [← mul_assoc, mul_transposition_mul_transposition, transposition_mul_self]
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
  rw [hω', mul_transposition_mul_transposition] at he
  have hle := (isLeast_wordLength σ).2 ⟨ω'.eraseIdx j, by rw [toPerm_wordProd, he], rfl⟩
  rw [List.length_eraseIdx_of_lt hj] at hle
  omega

/-- The symmetric group `Equiv.Perm (Fin n)` as the Coxeter group of type `A_{n-1}`, with the
adjacent transpositions `TauCeti.BraidGroup.transposition i` as simple reflections. -/
noncomputable def coxeterSystem (n : ℕ) :
    CoxeterSystem (CoxeterMatrix.A (n - 1)) (Equiv.Perm (Fin n)) :=
  (CoxeterMatrix.A (n - 1)).toCoxeterSystem.ofExchange (toPerm n) (wordLength n)
    (fun i j ↦ by
      rw [toPerm_simple, toPerm_simple]
      exact orderOf_transposition_mul_transposition i j)
    isLeast_wordLength exchange_toPerm

/-- The simple reflections of the type-`A` Coxeter system on `Equiv.Perm (Fin n)` are the
adjacent transpositions. -/
@[simp]
theorem coxeterSystem_simple (i : Fin (n - 1)) :
    (coxeterSystem n).simple i = transposition i := by
  rw [coxeterSystem, CoxeterSystem.ofExchange_simple, toPerm_simple]

/-- A word in the type-`A` Coxeter system on `Equiv.Perm (Fin n)` spells the product of the
corresponding adjacent transpositions. -/
@[simp]
theorem coxeterSystem_wordProd (ω : List (Fin (n - 1))) :
    (coxeterSystem n).wordProd ω = (ω.map transposition).prod := by
  rw [CoxeterSystem.wordProd, funext coxeterSystem_simple]

/-- Right multiplication by `s i` shortens a permutation that reverses the order of the letters
`i` and `i + 1`. -/
private theorem length_mul_transposition_lt {σ : Equiv.Perm (Fin n)} {i : Fin (n - 1)}
    (h : σ (strandSucc i) < σ (strand i)) :
    (coxeterSystem n).length (σ * transposition i) < (coxeterSystem n).length σ := by
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem n).exists_isReduced σ
  rw [coxeterSystem_wordProd] at h
  obtain ⟨j, hj, he⟩ := exists_prod_eraseIdx_eq_mul_transposition ω h
  have hle := (coxeterSystem n).length_wordProd_le (ω.eraseIdx j)
  rw [coxeterSystem_wordProd, he, List.length_eraseIdx_of_lt hj] at hle
  rw [hω.eq, coxeterSystem_wordProd]
  omega

/-- **Right descents of a permutation.** The simple reflection `s i` is a right descent of `σ`
exactly when `σ` reverses the order of the letters `i` and `i + 1`. -/
theorem isRightDescent_coxeterSystem_iff {σ : Equiv.Perm (Fin n)} {i : Fin (n - 1)} :
    (coxeterSystem n).IsRightDescent σ i ↔ σ (strandSucc i) < σ (strand i) := by
  refine ⟨fun hd ↦ ?_, fun h ↦ by
    simpa [CoxeterSystem.IsRightDescent] using length_mul_transposition_lt h⟩
  rcases (σ.injective.ne (strand_ne_strandSucc i).symm).lt_or_gt with h | hlt
  · exact h
  exfalso
  have hlen := length_mul_transposition_lt (σ := σ * transposition i) (i := i)
    (by simpa using hlt)
  rw [mul_transposition_mul_transposition] at hlen
  rw [CoxeterSystem.IsRightDescent, coxeterSystem_simple] at hd
  omega

/-- **Left descents of a permutation.** The simple reflection `s i` is a left descent of `σ`
exactly when `σ⁻¹` reverses the order of the letters `i` and `i + 1`. -/
theorem isLeftDescent_coxeterSystem_iff {σ : Equiv.Perm (Fin n)} {i : Fin (n - 1)} :
    (coxeterSystem n).IsLeftDescent σ i ↔ σ⁻¹ (strandSucc i) < σ⁻¹ (strand i) := by
  rw [← CoxeterSystem.isRightDescent_inv_iff, isRightDescent_coxeterSystem_iff]

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
theorem length_coxeterSystem (σ : Equiv.Perm (Fin n)) :
    (coxeterSystem n).length σ =
      (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ σ p.2 < σ p.1).card := by
  induction hk : (coxeterSystem n).length σ generalizing σ with
  | zero =>
    rw [(coxeterSystem n).length_eq_zero_iff] at hk
    subst hk
    rw [eq_comm, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro p - ⟨h₁, h₂⟩
    exact lt_asymm h₁ h₂
  | succ k ih =>
    have hσ : σ ≠ 1 := fun h ↦ by simp [h] at hk
    obtain ⟨i, hi⟩ := (coxeterSystem n).exists_rightDescent_of_ne_one hσ
    have hdesc := isRightDescent_coxeterSystem_iff.mp hi
    have hlen : (coxeterSystem n).length (σ * transposition i) = k := by
      have := (coxeterSystem n).length_mul_simple σ i
      rw [CoxeterSystem.IsRightDescent] at hi
      rw [coxeterSystem_simple] at this hi
      omega
    have hcard := card_inversions_mul_transposition (σ := σ * transposition i) (i := i)
      (by simpa using hdesc)
    rw [mul_transposition_mul_transposition] at hcard
    rw [hcard, ← ih _ hlen]

end Equiv.Perm

namespace TauCeti.BraidGroup

/-- The strand permutation of a braid is the canonical map from the Artin group of type `A` onto
its Coxeter group, realized as the symmetric group. -/
theorem permHom_eq_toCoxeterGroup (n : ℕ) :
    permHom n = ArtinGroup.toCoxeterGroup (Equiv.Perm.coxeterSystem n) :=
  hom_ext fun i ↦ by
    rw [permHom_sigma, sigma_eq_gen, ArtinGroup.toCoxeterGroup_gen, Equiv.Perm.coxeterSystem_simple]

end TauCeti.BraidGroup
