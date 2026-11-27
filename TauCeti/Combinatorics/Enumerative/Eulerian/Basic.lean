/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fin.Rev
public import Mathlib.Data.Nat.Choose.Basic
public import TauCeti.RingTheory.Polynomial.Eulerian
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Eulerian numbers and basic identities

This file defines the descent and ascent counts of permutations of `Fin n` and the
descent-indexed Eulerian numbers `TauCeti.eulerianNumber n q`, counting permutations of `Fin n`
with `q` descents.

By convention, `eulerianNumber 0 0 = 1` and `eulerianNumber 0 (q + 1) = 0`, while for `n ≥ 1`,
`eulerianNumber n q = 0` for `q ≥ n`. This matches Stanley's `A(n, q + 1)` for `n ≥ 1` (whereas
Stanley sets `A(0, k) = δ_{0, k}` separately at `n = 0`, matching `eulerianNumber 0 k`),
Lawrence–Sawin's `A(n, q)` (extended by zero outside `0 ≤ q < n` for `n ≥ 1`), and the
coefficients of `TauCeti.eulerianPolynomial n`.

## Main definitions

* `Equiv.Perm.descentCount`: the number of positions `i` with `i + 1 < n` and `σ (i + 1) < σ i`.
* `Equiv.Perm.ascentCount`: the number of positions `i` with `i + 1 < n` and `σ i < σ (i + 1)`.
* `TauCeti.eulerianNumber`: `eulerianNumber n q` is the number of permutations of `Fin n` with
  `q` descents.
* `TauCeti.eulerianRec`: the computable Pascal-style recurrence agreeing with `eulerianNumber`.

## Main results

* `TauCeti.sum_range_eulerianNumber`: `∑ q ∈ Finset.range (n + 1), eulerianNumber n q = n !`.
* `TauCeti.eulerianNumber_symm`: `eulerianNumber n q = eulerianNumber n (n - 1 - q)` for `q < n`.
* `TauCeti.eulerianNumber_succ_succ`:
  `eulerianNumber (n + 1) (q + 1) =`
  `(q + 2) * eulerianNumber n (q + 1) + (n - q) * eulerianNumber n q`.
* `TauCeti.pow_eq_sum_eulerianNumber_mul_choose` (Worpitzky's identity):
  `(q + 1) ^ n = ∑ j ∈ Finset.range (q + 1), eulerianNumber n j * (n + q - j).choose n`.
* `TauCeti.eulerianNumber_one_right`: `eulerianNumber n 1 = 2 ^ n - n - 1`.
* `TauCeti.eulerianPolynomial_coeff`: `(eulerianPolynomial n).coeff q = eulerianNumber n q`.
* `TauCeti.eulerianNumber_monotoneOn`, `TauCeti.eulerianNumber_antitoneOn`: unimodality of the
  rows of Eulerian numbers.

## References

* R. P. Stanley, *Enumerative Combinatorics, Volume 1*, 2nd ed., §1.4, Propositions 1.4.3–1.4.4,
  and Exercise 1.50(e).
* B. Lawrence and W. Sawin, *The Shafarevich conjecture for hypersurfaces in abelian varieties*,
  Annals of Mathematics 202 (2025), §3 and Appendix B–C.
-/

public section

open Finset

namespace Equiv.Perm

/-- The number of descents of a permutation `σ` of `Fin n`, i.e., positions `i` with
`i + 1 < n` and `σ (i + 1) < σ i`. -/
def descentCount {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun i : Fin n =>
    if h : i.val + 1 < n then σ ⟨i.val + 1, h⟩ < σ i else False).card

/-- The number of ascents of a permutation `σ` of `Fin n`, i.e., positions `i` with
`i + 1 < n` and `σ i < σ (i + 1)`. -/
def ascentCount {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun i : Fin n =>
    if h : i.val + 1 < n then σ i < σ ⟨i.val + 1, h⟩ else False).card

@[simp]
theorem descentCount_zero (σ : Equiv.Perm (Fin 0)) : σ.descentCount = 0 := by
  simp [descentCount]

@[simp]
theorem ascentCount_zero (σ : Equiv.Perm (Fin 0)) : σ.ascentCount = 0 := by
  simp [ascentCount]

@[simp]
theorem descentCount_one (σ : Equiv.Perm (Fin 1)) : σ.descentCount = 0 := by
  simp [descentCount]

@[simp]
theorem ascentCount_one (σ : Equiv.Perm (Fin 1)) : σ.ascentCount = 0 := by
  simp [ascentCount]

@[simp]
theorem descentCount_one_perm (n : ℕ) : (1 : Equiv.Perm (Fin n)).descentCount = 0 := by
  rw [descentCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i _
  split_ifs with h
  · simp [Fin.lt_def]
  · simp

theorem descentCount_succ {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) :
    σ.descentCount = (Finset.univ.filter fun i : Fin n => σ i.succ < σ i.castSucc).card := by
  rw [descentCount]
  refine Finset.card_bij (fun i hi => ⟨i.val, by
    have hmem := (Finset.mem_filter.mp hi).2
    by_cases h : i.val + 1 < n + 1
    · exact Nat.lt_of_succ_lt_succ h
    · simp [h] at hmem⟩) ?_ ?_ ?_
  · intro i hi
    have hmem := (Finset.mem_filter.mp hi).2
    by_cases h : i.val + 1 < n + 1
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simp only [h, ↓reduceDIte] at hmem
      exact hmem
    · simp [h] at hmem
  · intro i₁ _ i₂ _ h
    exact Fin.ext (Fin.mk.inj h)
  · intro j hj
    refine ⟨j.castSucc, ?_, rfl⟩
    have hlt : j.val + 1 < n + 1 := Nat.succ_lt_succ j.isLt
    have hmem : σ ⟨j.val + 1, hlt⟩ < σ j.castSucc := (Finset.mem_filter.mp hj).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hlt, hmem]⟩

theorem ascentCount_succ {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) :
    σ.ascentCount = (Finset.univ.filter fun i : Fin n => σ i.castSucc < σ i.succ).card := by
  rw [ascentCount]
  refine Finset.card_bij (fun i hi => ⟨i.val, by
    have hmem := (Finset.mem_filter.mp hi).2
    by_cases h : i.val + 1 < n + 1
    · exact Nat.lt_of_succ_lt_succ h
    · simp [h] at hmem⟩) ?_ ?_ ?_
  · intro i hi
    have hmem := (Finset.mem_filter.mp hi).2
    by_cases h : i.val + 1 < n + 1
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simp only [h, ↓reduceDIte] at hmem
      exact hmem
    · simp [h] at hmem
  · intro i₁ _ i₂ _ h
    exact Fin.ext (Fin.mk.inj h)
  · intro j hj
    refine ⟨j.castSucc, ?_, rfl⟩
    have hlt : j.val + 1 < n + 1 := Nat.succ_lt_succ j.isLt
    have hmem : σ j.castSucc < σ ⟨j.val + 1, hlt⟩ := (Finset.mem_filter.mp hj).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hlt, hmem]⟩

theorem descentCount_add_ascentCount {n : ℕ} (hn : 0 < n) (σ : Equiv.Perm (Fin n)) :
    σ.descentCount + σ.ascentCount = n - 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [descentCount_succ, ascentCount_succ, Nat.succ_sub_one]
  have hdisj : Disjoint
      (Finset.univ.filter fun i : Fin m => σ i.succ < σ i.castSucc)
      (Finset.univ.filter fun i : Fin m => σ i.castSucc < σ i.succ) := by
    rw [Finset.disjoint_filter]
    intro i _ h1 h2
    exact lt_asymm h1 h2
  have hunion :
      (Finset.univ.filter fun i : Fin m => σ i.succ < σ i.castSucc) ∪
        (Finset.univ.filter fun i : Fin m => σ i.castSucc < σ i.succ) = Finset.univ := by
    ext i
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact lt_or_gt_of_ne (σ.injective.ne i.castSucc_lt_succ.ne')
  rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_fin]

theorem descentCount_lt_of_pos {n : ℕ} (hn : 0 < n) (σ : Equiv.Perm (Fin n)) :
    σ.descentCount < n := by
  have h := descentCount_add_ascentCount hn σ
  omega

theorem descentCount_le {n : ℕ} (σ : Equiv.Perm (Fin n)) : σ.descentCount ≤ n - 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact Nat.le_pred_of_lt (descentCount_lt_of_pos hn σ)

theorem descentCount_eq_zero_iff {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    σ.descentCount = 0 ↔ σ = 1 := by
  refine ⟨fun h => ?_, fun h => h ▸ descentCount_one_perm n⟩
  rcases n with _ | m
  · exact Subsingleton.elim _ _
  · rw [descentCount_succ, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h
    have hmono : Monotone σ := by
      refine Fin.monotone_iff_le_succ.mpr fun i => ?_
      have hi := h (Finset.mem_univ i)
      exact not_lt.mp hi
    ext x
    have horder : ∀ a b : Fin (m + 1), a < b → σ a < σ b := fun a b hab =>
      (hmono hab.le).lt_of_ne (σ.injective.ne hab.ne)
    have hid : ∀ k : ℕ, (hk : k < m + 1) → σ ⟨k, hk⟩ = ⟨k, hk⟩ := by
      intro k
      induction k using Nat.strong_induction_on with
      | _ k ih =>
        intro hk
        have hlt_prev : ∀ j : Fin (m + 1), (j : ℕ) < k → (σ j : ℕ) = j := by
          intro j hj
          have hj' := ih j hj (hj.trans hk)
          exact congrArg Fin.val hj'
        have hge : k ≤ (σ ⟨k, hk⟩ : ℕ) := by
          by_contra hlt
          have hlt' : (σ ⟨k, hk⟩ : ℕ) < k := Nat.lt_of_not_ge hlt
          have hpre := hlt_prev (σ ⟨k, hk⟩) hlt'
          have hinj : σ ⟨(σ ⟨k, hk⟩ : ℕ), hlt'.trans hk⟩ = σ ⟨k, hk⟩ := Fin.ext hpre
          have hcontra := congrArg Fin.val (σ.injective hinj)
          simp only at hcontra
          omega
        have hle : (σ ⟨k, hk⟩ : ℕ) ≤ k := by
          by_contra hgt
          have hgt' : k < (σ ⟨k, hk⟩ : ℕ) := Nat.lt_of_not_ge hgt
          rcases lt_trichotomy (σ.symm ⟨k, hk⟩) ⟨k, hk⟩ with hs | hs | hs
          · have heq := hlt_prev (σ.symm ⟨k, hk⟩) hs
            simp only [Equiv.apply_symm_apply] at heq
            exact hs.ne (Fin.ext heq.symm)
          · have := congrArg σ hs
            simp only [Equiv.apply_symm_apply] at this
            exact hgt'.ne (congrArg Fin.val this)
          · have hord := horder ⟨k, hk⟩ (σ.symm ⟨k, hk⟩) hs
            simp only [Equiv.apply_symm_apply] at hord
            exact hgt'.asymm hord
        exact Fin.ext (le_antisymm hle hge)
    change (σ x).val = x.val
    have hx := congrArg Fin.val (hid x.val x.isLt)
    simpa using hx

@[simp]
theorem descentCount_mul_revPerm {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (σ * Fin.revPerm).descentCount = σ.ascentCount := by
  rcases n with _ | m
  · simp
  · rw [descentCount_succ, ascentCount_succ]
    refine Finset.card_bij (fun i _ => i.rev) ?_ (fun _ _ _ _ h => Fin.rev_injective h) ?_
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.Perm.mul_apply,
        Fin.revPerm_apply] at hi
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      simpa [Fin.rev_succ, Fin.rev_castSucc] using hi
    · intro j hj
      refine ⟨j.rev, ?_, Fin.rev_rev j⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.Perm.mul_apply,
        Fin.revPerm_apply, Fin.rev_succ, Fin.rev_castSucc, Fin.rev_rev]
      exact (Finset.mem_filter.mp hj).2

@[simp]
theorem descentCount_revPerm_mul {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (Fin.revPerm * σ).descentCount = σ.ascentCount := by
  rcases n with _ | m
  · simp
  · rw [descentCount_succ, ascentCount_succ]
    congr 1
    ext i
    simp [Fin.rev_lt_rev]

/-! ### Inserting `Fin.last n` into a permutation of `Fin n` -/

private noncomputable def insertLastFun {n : ℕ} (p : Fin (n + 1)) (σ : Equiv.Perm (Fin n)) :
    Fin (n + 1) → Fin (n + 1) :=
  fun x =>
    if hx : x = p then Fin.last n
    else if hlt : x < p then (σ ⟨x.val, lt_of_lt_of_le hlt (Nat.le_of_lt_succ p.isLt)⟩).castSucc
    else (σ ⟨x.val - 1, by
      have hgt : p.val < x.val := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm (Fin.val_ne_of_ne hx))
      omega⟩).castSucc

private lemma insertLastFun_self {n : ℕ} (p : Fin (n + 1)) (σ : Equiv.Perm (Fin n)) :
    insertLastFun p σ p = Fin.last n := by
  simp [insertLastFun]

private lemma insertLastFun_succAbove {n : ℕ} (p : Fin (n + 1)) (σ : Equiv.Perm (Fin n))
    (i : Fin n) : insertLastFun p σ (p.succAbove i) = (σ i).castSucc := by
  rcases lt_or_ge i.castSucc p with hlt | hle
  · rw [Fin.succAbove_of_castSucc_lt p i hlt]
    have hne : i.castSucc ≠ p := hlt.ne
    simp only [insertLastFun, hne, ↓reduceDIte, hlt]
    rfl
  · rw [Fin.succAbove_of_le_castSucc p i hle]
    have hgt : p < i.succ := Nat.lt_succ_of_le hle
    have hne : i.succ ≠ p := hgt.ne'
    have hnot : ¬ i.succ < p := not_lt_of_gt hgt
    simp only [insertLastFun, hne, ↓reduceDIte, hnot]
    rfl

private lemma insertLastFun_bijective {n : ℕ} (p : Fin (n + 1)) (σ : Equiv.Perm (Fin n)) :
    Function.Bijective (insertLastFun p σ) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun x y hxy => ?_, rfl⟩
  by_cases hx : x = p <;> by_cases hy : y = p
  · exact hx.trans hy.symm
  · subst hx
    obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hy
    rw [insertLastFun_self, insertLastFun_succAbove] at hxy
    exact absurd hxy (Fin.castSucc_lt_last _).ne'
  · subst hy
    obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hx
    rw [insertLastFun_succAbove, insertLastFun_self] at hxy
    exact absurd hxy (Fin.castSucc_lt_last _).ne
  · obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hx
    obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hy
    rw [insertLastFun_succAbove, insertLastFun_succAbove] at hxy
    have hij : σ i = σ j := Fin.castSucc_inj.mp hxy
    rw [σ.injective hij]

private noncomputable def insertLast {n : ℕ} (p : Fin (n + 1)) (σ : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin (n + 1)) :=
  Equiv.ofBijective (insertLastFun p σ) (insertLastFun_bijective p σ)

@[simp]
private lemma insertLast_apply_self {n : ℕ} (p : Fin (n + 1)) (σ : Equiv.Perm (Fin n)) :
    insertLast p σ p = Fin.last n :=
  insertLastFun_self p σ

@[simp]
private lemma insertLast_apply_succAbove {n : ℕ} (p : Fin (n + 1)) (σ : Equiv.Perm (Fin n))
    (i : Fin n) : insertLast p σ (p.succAbove i) = (σ i).castSucc :=
  insertLastFun_succAbove p σ i

private lemma insertLast_uncurry_bijective (n : ℕ) :
    Function.Bijective (fun q : Fin (n + 1) × Equiv.Perm (Fin n) => insertLast q.1 q.2) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun ⟨p₁, σ₁⟩ ⟨p₂, σ₂⟩ h => ?_, ?_⟩
  · have hp : p₁ = p₂ := by
      have h1 := congrArg (fun τ : Equiv.Perm (Fin (n + 1)) => τ p₁) h
      rw [insertLast_apply_self] at h1
      by_contra hne
      obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hne
      rw [← hj, insertLast_apply_succAbove] at h1
      exact (Fin.castSucc_lt_last _).ne h1.symm
    subst hp
    congr 1
    ext i
    have h2 := congrArg (fun τ : Equiv.Perm (Fin (n + 1)) => τ (p₁.succAbove i)) h
    rw [insertLast_apply_succAbove, insertLast_apply_succAbove] at h2
    exact congrArg Fin.val (Fin.castSucc_inj.mp h2)
  · rw [Fintype.card_prod, Fintype.card_perm, Fintype.card_perm, Fintype.card_fin,
      Fintype.card_fin, Nat.factorial_succ]

private noncomputable def insertLastEquiv (n : ℕ) :
    Fin (n + 1) × Equiv.Perm (Fin n) ≃ Equiv.Perm (Fin (n + 1)) :=
  Equiv.ofBijective _ (insertLast_uncurry_bijective n)

private lemma descentCount_insertLast_zero {m : ℕ} (σ : Equiv.Perm (Fin (m + 1))) :
    (insertLast 0 σ).descentCount = σ.descentCount + 1 := by
  rw [descentCount_succ, descentCount_succ]
  have hsplit : (Finset.univ.filter fun i : Fin (m + 1) =>
      insertLast 0 σ i.succ < insertLast 0 σ i.castSucc) =
      insert 0 ((Finset.univ.filter fun j : Fin m => σ j.succ < σ j.castSucc).map
        (Fin.succEmb m)) := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.castSucc_zero,
        insertLast_apply_self, Fin.succ_zero_eq_one, Finset.mem_insert, true_or, iff_true]
      have h1 : (1 : Fin (m + 2)) = (0 : Fin (m + 2)).succAbove 0 := by
        rw [Fin.succAbove_zero]; rfl
      rw [h1, insertLast_apply_succAbove]
      exact Fin.castSucc_lt_last _
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Fin.succ_ne_zero, false_or, Finset.mem_map]
      have h1 : j.succ.succ = (0 : Fin (m + 2)).succAbove j.succ := by
        rw [Fin.succAbove_zero]
      have h2 : j.succ.castSucc = (0 : Fin (m + 2)).succAbove j.castSucc := by
        rw [Fin.succAbove_zero]
        exact Fin.ext rfl
      rw [h1, h2, insertLast_apply_succAbove, insertLast_apply_succAbove,
        Fin.castSucc_lt_castSucc_iff]
      constructor
      · intro h
        exact ⟨j, h, rfl⟩
      · rintro ⟨a, ha, hae⟩
        have hja : a = j := Fin.succ_inj.mp hae
        subst hja
        exact ha
  rw [hsplit, Finset.card_insert_of_notMem (by simp), Finset.card_map, add_comm]

private lemma descentCount_insertLast_last {m : ℕ} (σ : Equiv.Perm (Fin (m + 1))) :
    (insertLast (Fin.last (m + 1)) σ).descentCount = σ.descentCount := by
  rw [descentCount_succ, descentCount_succ]
  have hsplit : (Finset.univ.filter fun i : Fin (m + 1) =>
      insertLast (Fin.last (m + 1)) σ i.succ < insertLast (Fin.last (m + 1)) σ i.castSucc) =
      (Finset.univ.filter fun j : Fin m => σ j.succ < σ j.castSucc).map Fin.castSuccEmb := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.succ_last,
        insertLast_apply_self, Finset.mem_map, Fin.castSuccEmb_apply]
      constructor
      · intro h
        exact absurd h (not_lt_of_ge (Fin.le_last _))
      · rintro ⟨j, _, hj⟩
        exact absurd hj (Fin.castSucc_lt_last _).ne
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
        Fin.castSuccEmb_apply, Fin.castSucc_inj, exists_eq_right]
      have h1 : j.castSucc.succ = (Fin.last (m + 1)).succAbove j.succ := by
        rw [Fin.succAbove_last]
        exact Fin.ext rfl
      have h2 : j.castSucc.castSucc = (Fin.last (m + 1)).succAbove j.castSucc := by
        rw [Fin.succAbove_last]
      rw [h1, h2, insertLast_apply_succAbove, insertLast_apply_succAbove,
        Fin.castSucc_lt_castSucc_iff]
  rw [hsplit, Finset.card_map]

private lemma descentCount_insertLast_succ_castSucc {m : ℕ} (k : Fin m)
    (σ : Equiv.Perm (Fin (m + 1))) :
    (insertLast k.succ.castSucc σ).descentCount =
      if σ k.succ < σ k.castSucc then σ.descentCount else σ.descentCount + 1 := by
  set p : Fin (m + 2) := k.succ.castSucc
  rw [descentCount_succ, descentCount_succ]
  let f : Fin m → Fin (m + 1) := fun j =>
    if j < k then j.castSucc else if j = k then k.succ else j.succ
  have hf_inj : Function.Injective f := by
    intro a b hab
    dsimp [f] at hab
    split_ifs at hab with ha1 ha2 hb1 hb2 <;>
      simp only [Fin.ext_iff, Fin.val_castSucc, Fin.val_succ] at hab <;> omega
  have hf_mem : ∀ j : Fin m,
      (insertLast p σ (f j).succ < insertLast p σ (f j).castSucc) ↔
        (if j = k then True else σ j.succ < σ j.castSucc) := by
    intro j
    dsimp [f]
    rcases lt_trichotomy j k with hjk | heq | hjk
    · have h1 : (j.castSucc : Fin (m + 1)).castSucc = p.succAbove j.castSucc := by
        rw [Fin.succAbove_of_castSucc_lt]
        exact Fin.lt_def.mpr (by change j.val < k.val + 1; have : j.val < k.val := hjk; omega)
      have h2 : (j.castSucc : Fin (m + 1)).succ = p.succAbove j.succ := by
        rw [Fin.succAbove_of_castSucc_lt]
        · exact Fin.ext rfl
        · exact Fin.lt_def.mpr (by change j.val + 1 < k.val + 1; have : j.val < k.val := hjk; omega)
      simp only [hjk, ↓reduceIte, hjk.ne]
      rw [h1, h2, insertLast_apply_succAbove, insertLast_apply_succAbove,
        Fin.castSucc_lt_castSucc_iff]
    · subst heq
      simp only [lt_irrefl, ↓reduceIte]
      have hk1 : (j.succ : Fin (m + 1)).castSucc = p := Fin.ext rfl
      have hk2 : (j.succ : Fin (m + 1)).succ = p.succAbove j.succ := by
        rw [Fin.succAbove_of_le_castSucc]
        exact le_rfl
      rw [hk1, hk2, insertLast_apply_self, insertLast_apply_succAbove]
      simp [Fin.castSucc_lt_last]
    · have hnot1 : ¬ j < k := not_lt_of_gt hjk
      have hnot2 : j ≠ k := hjk.ne'
      have h1 : (j.succ : Fin (m + 1)).castSucc = p.succAbove j.castSucc := by
        rw [Fin.succAbove_of_le_castSucc]
        · exact Fin.ext rfl
        · exact Fin.le_def.mpr (by change k.val + 1 ≤ j.val; have : k.val < j.val := hjk; omega)
      have h2 : (j.succ : Fin (m + 1)).succ = p.succAbove j.succ := by
        rw [Fin.succAbove_of_le_castSucc]
        exact Fin.le_def.mpr (by change k.val + 1 ≤ j.val + 1; have : k.val < j.val := hjk; omega)
      simp only [hnot1, ↓reduceIte, hnot2]
      rw [h1, h2, insertLast_apply_succAbove, insertLast_apply_succAbove,
        Fin.castSucc_lt_castSucc_iff]
  have hnot_kcast : ¬ (insertLast p σ (k.castSucc : Fin (m + 1)).succ <
      insertLast p σ (k.castSucc : Fin (m + 1)).castSucc) := by
    have hk1 : (k.castSucc : Fin (m + 1)).succ = p := Fin.ext rfl
    have hk2 : (k.castSucc : Fin (m + 1)).castSucc = p.succAbove k.castSucc := by
      rw [Fin.succAbove_of_castSucc_lt]
      exact Fin.lt_def.mpr (by simp [p])
    rw [hk1, hk2, insertLast_apply_self, insertLast_apply_succAbove]
    exact not_lt_of_ge (Fin.le_last _)
  have hmap : (Finset.univ.filter fun i : Fin (m + 1) =>
      insertLast p σ i.succ < insertLast p σ i.castSucc) =
      (Finset.univ.filter fun j : Fin m =>
        if j = k then True else σ j.succ < σ j.castSucc).map ⟨f, hf_inj⟩ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Function.Embedding.coeFn_mk]
    constructor
    · intro hi
      rcases lt_trichotomy i k.castSucc with hlt | heq | hgt
      · have hilt : i.val < k.val := hlt
        let j : Fin m := ⟨i.val, hilt.trans k.isLt⟩
        have hjk : j < k := hilt
        refine ⟨j, ?_, ?_⟩
        · rw [← hf_mem]
          have hf_eq : f j = i := by
            dsimp [f]
            simp only [hjk, ↓reduceIte]
            exact Fin.ext rfl
          rwa [hf_eq]
        · dsimp [f]
          simp only [hjk, ↓reduceIte]
          exact Fin.ext rfl
      · exact absurd (heq ▸ hi) hnot_kcast
      · have hgt_val : k.val < i.val := hgt
        rcases eq_or_lt_of_le (Nat.succ_le_of_lt hgt_val) with heq' | hgt'
        · refine ⟨k, by simp, ?_⟩
          dsimp [f]
          simp only [lt_irrefl, ↓reduceIte]
          exact Fin.ext heq'
        · let j : Fin m := ⟨i.val - 1, by omega⟩
          have hjk : k < j := by change k.val < i.val - 1; omega
          refine ⟨j, ?_, ?_⟩
          · rw [← hf_mem]
            have hf_eq : f j = i := by
              dsimp [f]
              simp only [not_lt_of_gt hjk, ↓reduceIte, hjk.ne']
              ext; simp [j]; omega
            rwa [hf_eq]
          · dsimp [f]
            simp only [not_lt_of_gt hjk, ↓reduceIte, hjk.ne']
            ext; simp [j]; omega
    · rintro ⟨j, hj, rfl⟩
      exact (hf_mem j).mpr hj
  rw [hmap, Finset.card_map]
  split_ifs with hkd
  · congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs with hjk
    · subst hjk; exact iff_of_true trivial hkd
    · rfl
  · have hsplit : (Finset.univ.filter fun j : Fin m =>
        if j = k then True else σ j.succ < σ j.castSucc) =
        insert k (Finset.univ.filter fun j : Fin m => σ j.succ < σ j.castSucc) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      split_ifs with hjk
      · subst hjk; simp
      · simp [hjk]
    rw [hsplit, Finset.card_insert_of_notMem (by simp [Finset.mem_filter, hkd])]

end Equiv.Perm

namespace TauCeti

/-- The descent-indexed Eulerian number `eulerianNumber n q`: the number of permutations of
`Fin n` having exactly `q` descents. By convention `eulerianNumber 0 0 = 1` and
`eulerianNumber 0 (q + 1) = 0`. -/
def eulerianNumber (n q : ℕ) : ℕ :=
  (Finset.univ.filter fun σ : Equiv.Perm (Fin n) => σ.descentCount = q).card

/-- `eulerianNumber n q` also counts permutations of `Fin n` with `q` ascents. -/
theorem eulerianNumber_eq_card_ascentCount (n q : ℕ) :
    eulerianNumber n q =
      (Finset.univ.filter fun σ : Equiv.Perm (Fin n) => σ.ascentCount = q).card := by
  rw [eulerianNumber]
  refine Finset.card_bij (fun σ _ => σ * Fin.revPerm) ?_ (fun _ _ _ _ h => mul_right_cancel h) ?_
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    rw [← Equiv.Perm.descentCount_mul_revPerm (σ * Fin.revPerm), mul_assoc,
      show (Fin.revPerm * Fin.revPerm : Equiv.Perm (Fin n)) = 1 by ext x; simp, mul_one, hσ]
  · intro τ hτ
    refine ⟨τ * Fin.revPerm, ?_, by
      rw [mul_assoc, show (Fin.revPerm * Fin.revPerm : Equiv.Perm (Fin n)) = 1 by ext x; simp,
        mul_one]⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
    simpa [Equiv.Perm.descentCount_mul_revPerm] using hτ

/-- The zeroth row of Eulerian numbers: `eulerianNumber 0 q = if q = 0 then 1 else 0`. -/
@[simp]
theorem eulerianNumber_zero_left (q : ℕ) :
    eulerianNumber 0 q = if q = 0 then 1 else 0 := by
  rw [eulerianNumber]
  split_ifs with hq
  · subst hq; simp
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro σ _
    simp [Ne.symm hq]

/-- Base value `eulerianNumber 0 0 = 1`. -/
theorem eulerianNumber_zero_zero : eulerianNumber 0 0 = 1 := by simp

/-- Vanishing in the zeroth row: `eulerianNumber 0 (q + 1) = 0`. -/
theorem eulerianNumber_zero_succ (q : ℕ) : eulerianNumber 0 (q + 1) = 0 := by simp

/-- For `1 ≤ n ≤ q`, `eulerianNumber n q = 0`. -/
theorem eulerianNumber_eq_zero_of_le {n q : ℕ} (hn : 1 ≤ n) (hq : n ≤ q) :
    eulerianNumber n q = 0 := by
  rw [eulerianNumber, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro σ _
  exact (lt_of_lt_of_le (Equiv.Perm.descentCount_lt_of_pos hn σ) hq).ne

/-- For `n < q`, `eulerianNumber n q = 0`. -/
theorem eulerianNumber_eq_zero_of_lt {n q : ℕ} (hq : n < q) : eulerianNumber n q = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq.ne'
    simp
  · exact eulerianNumber_eq_zero_of_le hn hq.le

/-- For `1 ≤ n`, `eulerianNumber n n = 0`. -/
@[simp]
theorem eulerianNumber_self {n : ℕ} (hn : 1 ≤ n) : eulerianNumber n n = 0 :=
  eulerianNumber_eq_zero_of_le hn le_rfl

/-- Every row starts with `eulerianNumber n 0 = 1`. -/
@[simp]
theorem eulerianNumber_zero_right (n : ℕ) : eulerianNumber n 0 = 1 := by
  rw [eulerianNumber]
  have h : (Finset.univ.filter fun σ : Equiv.Perm (Fin n) => σ.descentCount = 0) = {1} := by
    ext σ; simp [Equiv.Perm.descentCount_eq_zero_iff]
  rw [h, Finset.card_singleton]

/-- Row sum of Eulerian numbers: `∑ q ∈ Finset.range (n + 1), eulerianNumber n q = n.factorial`. -/
theorem sum_range_eulerianNumber (n : ℕ) :
    ∑ q ∈ Finset.range (n + 1), eulerianNumber n q = n.factorial := by
  have hcard : (Finset.univ : Finset (Equiv.Perm (Fin n))).card = n.factorial := by
    rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  have hmaps : ∀ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))),
      σ.descentCount ∈ Finset.range (n + 1) := by
    intro σ _; rw [Finset.mem_range]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · exact (Equiv.Perm.descentCount_lt_of_pos hn σ).trans (Nat.lt_succ_self n)
  have hsum := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset (Equiv.Perm (Fin n))) (Finset.range (n + 1)) (fun σ => σ.descentCount)
  rw [Finset.filter_true_of_mem hmaps, hcard] at hsum
  simpa [eulerianNumber] using hsum

/-- For `0 < n`, `∑ q ∈ Finset.range n, eulerianNumber n q = n.factorial`. -/
theorem sum_range_eulerianNumber_of_pos {n : ℕ} (hn : 0 < n) :
    ∑ q ∈ Finset.range n, eulerianNumber n q = n.factorial := by
  rw [← sum_range_eulerianNumber n, Finset.sum_range_succ, eulerianNumber_self hn, add_zero]

/-- Symmetry of the Eulerian triangle: `A(n, q) = A(n, n - 1 - q)` for `q < n`. -/
theorem eulerianNumber_symm {n q : ℕ} (hq : q < n) :
    eulerianNumber n q = eulerianNumber n (n - 1 - q) := by
  rw [eulerianNumber_eq_card_ascentCount, eulerianNumber]
  congr 1; ext σ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hsum := Equiv.Perm.descentCount_add_ascentCount (Nat.zero_lt_of_lt hq) σ
  omega

/-- The Pascal-style recurrence for Eulerian numbers:
`A(n + 1, q + 1) = (q + 2) * A(n, q + 1) + (n - q) * A(n, q)`. -/
theorem eulerianNumber_succ_succ (n q : ℕ) :
    eulerianNumber (n + 1) (q + 1) =
      (q + 2) * eulerianNumber n (q + 1) + (n - q) * eulerianNumber n q := by
  rcases n with _ | m
  · simp [eulerianNumber_eq_zero_of_le (by omega : 1 ≤ 1) (by omega : 1 ≤ q + 1)]
  · have hcount : eulerianNumber (m + 2) (q + 1) =
        ∑ σ : Equiv.Perm (Fin (m + 1)),
          (Finset.univ.filter fun p : Fin (m + 2) =>
            (Equiv.Perm.insertLastEquiv (m + 1) (p, σ)).descentCount = q + 1).card := by
      have hfilt :
          (Finset.univ.filter fun τ : Equiv.Perm (Fin (m + 2)) => τ.descentCount = q + 1) =
          (Finset.univ.filter fun τ : Equiv.Perm (Fin (m + 2)) =>
            τ.descentCount = q + 1).filter
            (fun τ => ((Equiv.Perm.insertLastEquiv (m + 1)).symm τ).2 ∈ Finset.univ) := by
        simp
      rw [eulerianNumber, hfilt, ← Finset.sum_card_fiberwise_eq_card_filter
        (Finset.univ.filter fun τ : Equiv.Perm (Fin (m + 2)) => τ.descentCount = q + 1)
        Finset.univ
        (fun τ => ((Equiv.Perm.insertLastEquiv (m + 1)).symm τ).2)]
      simp_rw [Finset.filter_filter]
      refine Finset.sum_congr rfl fun σ _ => ?_
      refine Finset.card_bij (fun τ _ => ((Equiv.Perm.insertLastEquiv (m + 1)).symm τ).1) ?_ ?_ ?_
      · intro τ hτ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
        have hpair : (Equiv.Perm.insertLastEquiv (m + 1)
            (((Equiv.Perm.insertLastEquiv (m + 1)).symm τ).1, σ)) = τ := by
          rw [← hτ.2, Equiv.apply_symm_apply]
        simpa [hpair] using hτ.1
      · intro τ₁ hτ₁ τ₂ hτ₂ hfst
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ₁ hτ₂
        apply (Equiv.Perm.insertLastEquiv (m + 1)).symm.injective
        ext <;> simp [hfst, hτ₁.2, hτ₂.2]
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
        exact ⟨Equiv.Perm.insertLastEquiv (m + 1) (p, σ), by simp [hp], by simp⟩
    have hfiber : ∀ σ : Equiv.Perm (Fin (m + 1)),
        (Finset.univ.filter fun p : Fin (m + 2) =>
          (Equiv.Perm.insertLastEquiv (m + 1) (p, σ)).descentCount = q + 1).card =
          (if σ.descentCount = q + 1 then q + 2 else 0) +
            (if σ.descentCount = q then m + 1 - q else 0) := by
      intro σ
      have hcard_p : (Finset.univ.filter fun p : Fin (m + 2) =>
          (Equiv.Perm.insertLastEquiv (m + 1) (p, σ)).descentCount = q + 1).card =
          (if σ.descentCount + 1 = q + 1 then 1 else 0) +
          (if σ.descentCount = q + 1 then 1 else 0) +
          ∑ k : Fin m, if (if σ k.succ < σ k.castSucc then σ.descentCount
              else σ.descentCount + 1) = q + 1 then 1 else 0 := by
        rw [Finset.card_filter, Fin.sum_univ_succ, Fin.sum_univ_castSucc]
        have h0' : (Equiv.Perm.insertLastEquiv (m + 1) (0, σ)).descentCount =
            σ.descentCount + 1 := Equiv.Perm.descentCount_insertLast_zero σ
        have hlast' : (Equiv.Perm.insertLastEquiv (m + 1)
            ((Fin.last m).succ, σ)).descentCount = σ.descentCount := by
          rw [Fin.succ_last]; exact Equiv.Perm.descentCount_insertLast_last σ
        have hmid' : ∀ k : Fin m,
            (Equiv.Perm.insertLastEquiv (m + 1) (k.castSucc.succ, σ)).descentCount =
              if σ k.succ < σ k.castSucc then σ.descentCount else σ.descentCount + 1 := fun k =>
          Equiv.Perm.descentCount_insertLast_succ_castSucc k σ
        simp_rw [h0', hlast', hmid']; ring
      rw [hcard_p]
      have hsum_k : ∑ k : Fin m, (if (if σ k.succ < σ k.castSucc then σ.descentCount
            else σ.descentCount + 1) = q + 1 then 1 else 0) =
          (if σ.descentCount = q + 1 then σ.descentCount else 0) +
            (if σ.descentCount = q then σ.ascentCount else 0) := by
        have hsplit_k : ∀ k : Fin m,
            (if (if σ k.succ < σ k.castSucc then σ.descentCount
              else σ.descentCount + 1) = q + 1 then (1 : ℕ) else 0) =
            (if σ k.succ < σ k.castSucc then (if σ.descentCount = q + 1 then 1 else 0) else 0) +
            (if σ k.castSucc < σ k.succ then (if σ.descentCount = q then 1 else 0) else 0) := by
          intro k
          rcases lt_or_gt_of_ne (σ.injective.ne k.castSucc_lt_succ.ne') with hlt | hgt
          · have hn : ¬ σ k.castSucc < σ k.succ := lt_asymm hlt
            simp only [hlt, ↓reduceIte, hn, add_zero]
          · have hn : ¬ σ k.succ < σ k.castSucc := lt_asymm hgt
            simp only [hn, ↓reduceIte, hgt, zero_add]
            split_ifs with h1 h2 <;> simp_all
        simp_rw [hsplit_k, Finset.sum_add_distrib]
        have hd_sum : ∑ k : Fin m,
            (if σ k.succ < σ k.castSucc then (if σ.descentCount = q + 1 then 1 else 0) else 0) =
            if σ.descentCount = q + 1 then σ.descentCount else 0 := by
          rw [Equiv.Perm.descentCount_succ, ← Finset.sum_filter]; split_ifs <;> simp
        have ha_sum : ∑ k : Fin m,
            (if σ k.castSucc < σ k.succ then (if σ.descentCount = q then 1 else 0) else 0) =
            if σ.descentCount = q then σ.ascentCount else 0 := by
          rw [Equiv.Perm.ascentCount_succ, ← Finset.sum_filter]; split_ifs <;> simp
        rw [hd_sum, ha_sum]
      rw [hsum_k]
      have htot := Equiv.Perm.descentCount_add_ascentCount (Nat.succ_pos m) σ
      rw [Nat.succ_sub_one] at htot
      split_ifs <;> omega
    rw [hcount]
    simp_rw [hfiber, Finset.sum_add_distrib]
    have h1 : ∑ σ : Equiv.Perm (Fin (m + 1)), (if σ.descentCount = q + 1 then q + 2 else 0) =
        (q + 2) * eulerianNumber (m + 1) (q + 1) := by
      rw [eulerianNumber, Finset.card_filter, Finset.mul_sum]
      exact Finset.sum_congr rfl fun σ _ => by split_ifs <;> simp
    have h2 : ∑ σ : Equiv.Perm (Fin (m + 1)), (if σ.descentCount = q then m + 1 - q else 0) =
        (m + 1 - q) * eulerianNumber (m + 1) q := by
      rw [eulerianNumber, Finset.card_filter, Finset.mul_sum]
      exact Finset.sum_congr rfl fun σ _ => by split_ifs <;> simp
    rw [h1, h2]

/-- Computable Pascal-style recurrence for `eulerianNumber n q`. -/
@[expose] def eulerianRec : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | n + 1, q + 1 => (q + 2) * eulerianRec n (q + 1) + (n - q) * eulerianRec n q

/-- `eulerianNumber` agrees with the computable recurrence `eulerianRec`. -/
theorem eulerianNumber_eq_eulerianRec (n q : ℕ) : eulerianNumber n q = eulerianRec n q := by
  induction n generalizing q with
  | zero =>
    cases q with
    | zero => simp [eulerianRec]
    | succ q => simp [eulerianRec]
  | succ n ih =>
    cases q with
    | zero => simp [eulerianRec]
    | succ q =>
      rw [eulerianNumber_succ_succ, eulerianRec, ih (q + 1), ih q]

/-- Small Eulerian value `eulerianNumber 2 1 = 1`. -/
@[simp] theorem eulerianNumber_two_one : eulerianNumber 2 1 = 1 := by
  rw [eulerianNumber_eq_eulerianRec]; decide

/-- Small Eulerian value `eulerianNumber 3 1 = 4`. -/
@[simp] theorem eulerianNumber_three_one : eulerianNumber 3 1 = 4 := by
  rw [eulerianNumber_eq_eulerianRec]; decide

/-- Small Eulerian value `eulerianNumber 3 2 = 1`. -/
@[simp] theorem eulerianNumber_three_two : eulerianNumber 3 2 = 1 := by
  rw [eulerianNumber_eq_eulerianRec]; decide

/-- Small Eulerian value `eulerianNumber 4 1 = 11`. -/
@[simp] theorem eulerianNumber_four_one : eulerianNumber 4 1 = 11 := by
  rw [eulerianNumber_eq_eulerianRec]; decide

/-- Small Eulerian value `eulerianNumber 4 2 = 11`. -/
@[simp] theorem eulerianNumber_four_two : eulerianNumber 4 2 = 11 := by
  rw [eulerianNumber_eq_eulerianRec]; decide

/-- Small Eulerian value `eulerianNumber 5 1 = 26`. -/
@[simp] theorem eulerianNumber_five_one : eulerianNumber 5 1 = 26 := by
  rw [eulerianNumber_eq_eulerianRec]; decide

/-- Small Eulerian value `eulerianNumber 5 2 = 66`. -/
@[simp] theorem eulerianNumber_five_two : eulerianNumber 5 2 = 66 := by
  rw [eulerianNumber_eq_eulerianRec]; decide

/-- **Worpitzky's identity**:
`(q + 1) ^ n = ∑ j ∈ Finset.range (q + 1), A(n, j) * C(n + q - j, n)`. -/
theorem pow_eq_sum_eulerianNumber_mul_choose (n q : ℕ) :
    (q + 1) ^ n =
      ∑ j ∈ Finset.range (q + 1), eulerianNumber n j * (n + q - j).choose n := by
  induction n generalizing q with
  | zero => simp
  | succ n ih =>
    apply Nat.eq_of_mul_eq_mul_left (Nat.succ_pos n)
    rw [pow_succ', ← mul_assoc, mul_comm (n + 1) (q + 1), mul_assoc, ih q, Finset.mul_sum]
    have hsplit : ∑ j ∈ Finset.range (q + 1),
        eulerianNumber (n + 1) j * (n + 1 + q - j).choose (n + 1) =
        (n + 1 + q).choose (n + 1) +
        ∑ k ∈ Finset.range q,
          ((k + 2) * eulerianNumber n (k + 1) + (n - k) * eulerianNumber n k) *
            (n + q - k).choose (n + 1) := by
      rw [Finset.sum_range_succ', eulerianNumber_zero_right, one_mul, Nat.sub_zero, add_comm]
      refine congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun k _ => ?_)
      rw [eulerianNumber_succ_succ, show n + 1 + q - (k + 1) = n + q - k by omega]
    rw [hsplit, Finset.mul_sum]
    have hreidx : ∑ k ∈ Finset.range q,
        ((k + 2) * eulerianNumber n (k + 1) + (n - k) * eulerianNumber n k) *
          (n + q - k).choose (n + 1) =
        ∑ k ∈ Finset.range q, (k + 2) * eulerianNumber n (k + 1) * (n + q - k).choose (n + 1) +
        ∑ k ∈ Finset.range q, (n - k) * eulerianNumber n k * (n + q - k).choose (n + 1) := by
      simp_rw [add_mul, Finset.sum_add_distrib]
    rw [hreidx]
    have htail : ∑ k ∈ Finset.range q,
        (n - k) * eulerianNumber n k * (n + q - k).choose (n + 1) =
        ∑ j ∈ Finset.range (q + 1),
          (n - j) * eulerianNumber n j * (n + q - j).choose (n + 1) := by
      rw [Finset.sum_range_succ, show n + q - q = n by omega,
        Nat.choose_eq_zero_of_lt (Nat.lt_succ_self n), mul_zero, add_zero]
    have hhead : (n + 1 + q).choose (n + 1) +
        ∑ k ∈ Finset.range q, (k + 2) * eulerianNumber n (k + 1) * (n + q - k).choose (n + 1) =
        ∑ j ∈ Finset.range (q + 1),
          (j + 1) * eulerianNumber n j * (n + 1 + q - j).choose (n + 1) := by
      rw [Finset.sum_range_succ', eulerianNumber_zero_right]
      simp only [zero_add, one_mul, Nat.sub_zero]
      rw [add_comm ((n + 1 + q).choose (n + 1))]
      refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun k _ => ?_) rfl
      rw [show n + 1 + q - (k + 1) = n + q - k by omega, show k + 1 + 1 = k + 2 by ring]
    rw [htail, ← add_assoc, hhead, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjq : j ≤ q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rcases le_or_gt j n with hjn | hnj
    · have h1 : (n + 1) * (n + 1 + q - j).choose (n + 1) =
          (n + 1 + q - j) * (n + q - j).choose n := by
        rw [show n + 1 + q - j = (n + q - j) + 1 by omega,
          Nat.add_one_mul_choose_eq, mul_comm (n + 1)]
      have h2 : (n + 1) * (n + q - j).choose (n + 1) = (q - j) * (n + q - j).choose n := by
        have hch := Nat.choose_succ_right_eq (n + q - j) n
        rw [show n + q - j - n = q - j by omega] at hch
        linarith
      calc
        (q + 1) * ((n + 1) * (eulerianNumber n j * (n + q - j).choose n))
            = eulerianNumber n j * ((n + 1) * (q + 1) * (n + q - j).choose n) := by ring
        _ = eulerianNumber n j *
              (((j + 1) * (n + 1 + q - j) + (n - j) * (q - j)) * (n + q - j).choose n) := by
            congr 2
            zify [hjq, hjn, show j ≤ n + 1 + q by omega]
            ring
        _ = (j + 1) * eulerianNumber n j * ((n + 1) * (n + 1 + q - j).choose (n + 1)) +
              (n - j) * eulerianNumber n j * ((n + 1) * (n + q - j).choose (n + 1)) := by
            rw [h1, h2]; ring
        _ = (n + 1) * ((j + 1) * eulerianNumber n j * (n + 1 + q - j).choose (n + 1) +
              (n - j) * eulerianNumber n j * (n + q - j).choose (n + 1)) := by ring
    · have hzero : eulerianNumber n j = 0 := eulerianNumber_eq_zero_of_lt hnj
      simp [hzero]

/-- Closed form for `eulerianNumber n 1`: `A(n, 1) = 2 ^ n - n - 1`. -/
theorem eulerianNumber_one_right (n : ℕ) : eulerianNumber n 1 = 2 ^ n - n - 1 := by
  have hw := pow_eq_sum_eulerianNumber_mul_choose n 1
  rw [Finset.sum_range_succ, Finset.sum_range_one, eulerianNumber_zero_right, one_mul,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.choose_self, mul_one,
    Nat.choose_succ_self_right, show 1 + 1 = 2 from rfl] at hw
  omega

/-- Every entry `eulerianNumber n q` with `q < n` is strictly positive. -/
theorem eulerianNumber_pos_of_lt {n q : ℕ} (hq : q < n) : 0 < eulerianNumber n q := by
  induction n generalizing q with
  | zero => exact absurd hq (Nat.not_lt_zero _)
  | succ n ih =>
    cases q with
    | zero => simp
    | succ q =>
      rw [eulerianNumber_succ_succ]
      have hq' : q < n := Nat.lt_of_succ_lt_succ hq
      have hpos := ih hq'
      have hsub : 0 < n - q := Nat.sub_pos_of_lt hq'
      exact Nat.add_pos_right _ (Nat.mul_pos hsub hpos)

/-- The coefficients of `TauCeti.eulerianPolynomial n` are the Eulerian numbers
`eulerianNumber n q`. -/
theorem eulerianPolynomial_coeff (n q : ℕ) :
    (eulerianPolynomial n).coeff q = (eulerianNumber n q : ℤ) := by
  induction n generalizing q with
  | zero =>
    simp only [eulerianPolynomial_zero, Polynomial.coeff_one, eulerianNumber_zero_left]
    split_ifs <;> rfl
  | succ n ih =>
    rw [eulerianPolynomial_succ]
    have hsplit : (1 + Polynomial.C (n : ℤ) * Polynomial.X) * eulerianPolynomial n +
        Polynomial.X * (1 - Polynomial.X) * (eulerianPolynomial n).derivative =
        eulerianPolynomial n + Polynomial.C (n : ℤ) * (Polynomial.X * eulerianPolynomial n) +
        (Polynomial.X * (eulerianPolynomial n).derivative -
          Polynomial.X * (Polynomial.X * (eulerianPolynomial n).derivative)) := by
      ring
    rw [hsplit]
    cases q with
    | zero =>
      simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
        Polynomial.coeff_X_mul_zero, mul_zero, add_zero, sub_zero, ih 0,
        eulerianNumber_zero_right]
    | succ k =>
      simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
        Polynomial.coeff_X_mul, Polynomial.coeff_derivative, ih (k + 1), ih k]
      rw [eulerianNumber_succ_succ]
      cases k with
      | zero =>
        simp only [Polynomial.coeff_X_mul_zero, sub_zero, Nat.cast_zero, zero_add, Nat.sub_zero]
        push_cast
        ring
      | succ k' =>
        simp only [Polynomial.coeff_X_mul, Polynomial.coeff_derivative, ih (k' + 1)]
        rcases le_or_gt (k' + 1) n with hkn | hnk
        · zify [hkn]
          ring
        · have hzero : eulerianNumber n (k' + 1) = 0 := eulerianNumber_eq_zero_of_lt hnk
          simp only [hzero, Nat.cast_zero, mul_zero, add_zero]
          push_cast
          ring

/-- Along the first half of each row, Eulerian numbers increase:
`A(n, q) ≤ A(n, q + 1)` whenever `2 * (q + 1) ≤ n`. -/
theorem eulerianNumber_le_succ_of_two_mul_le {n q : ℕ} (hq : 2 * (q + 1) ≤ n) :
    eulerianNumber n q ≤ eulerianNumber n (q + 1) := by
  induction n generalizing q with
  | zero => omega
  | succ n ih =>
    cases q with
    | zero =>
      rw [eulerianNumber_zero_right]
      exact eulerianNumber_pos_of_lt (by omega)
    | succ k =>
      rw [eulerianNumber_succ_succ, eulerianNumber_succ_succ]
      rcases lt_or_eq_of_le hq with hlt | heq
      · have ih1 : eulerianNumber n k ≤ eulerianNumber n (k + 1) := ih (by omega)
        have ih2 : eulerianNumber n (k + 1) ≤ eulerianNumber n (k + 2) := ih (by omega)
        calc
          (k + 2) * eulerianNumber n (k + 1) + (n - k) * eulerianNumber n k
              ≤ (k + 2) * eulerianNumber n (k + 1) + (n - k) * eulerianNumber n (k + 1) :=
            Nat.add_le_add_left (Nat.mul_le_mul_left _ ih1) _
          _ = (k + 3) * eulerianNumber n (k + 1) + (n - (k + 1)) * eulerianNumber n (k + 1) := by
            have hk : k ≤ n := by omega
            have hnk : k + 1 ≤ n := by omega
            zify [hk, hnk]
            ring
          _ ≤ (k + 3) * eulerianNumber n (k + 2) + (n - (k + 1)) * eulerianNumber n (k + 1) :=
            Nat.add_le_add_right (Nat.mul_le_mul_left _ ih2) _
      · have hsym : eulerianNumber n (k + 2) = eulerianNumber n k := by
          rw [eulerianNumber_symm (by omega), show n - 1 - (k + 2) = k by omega]
        rw [hsym, show n - (k + 1) = k + 2 by omega, show n - k = k + 3 by omega]
        ring_nf
        rfl

/-- On the first half `Set.Iic (n / 2)`, `eulerianNumber n` is monotone. -/
theorem eulerianNumber_monotoneOn (n : ℕ) : MonotoneOn (eulerianNumber n) (Set.Iic (n / 2)) := by
  intro a _ b hb hab
  have hb' : b ≤ n / 2 := Set.mem_Iic.mp hb
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  induction d with
  | zero => simp
  | succ d ih =>
    have hstep := ih (Set.mem_Iic.mpr (by omega)) (Nat.le_add_right a d) (by omega)
    have hsucc : eulerianNumber n (a + d) ≤ eulerianNumber n (a + d + 1) :=
      eulerianNumber_le_succ_of_two_mul_le (by omega)
    exact hstep.trans hsucc

/-- On the second half `Set.Ici ((n - 1) / 2)`, `eulerianNumber n` is antitone. -/
theorem eulerianNumber_antitoneOn (n : ℕ) :
    AntitoneOn (eulerianNumber n) (Set.Ici ((n - 1) / 2)) := by
  intro a ha b _ hab
  have ha' : (n - 1) / 2 ≤ a := Set.mem_Ici.mp ha
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · cases a <;> cases b <;> simp_all
  · rcases le_or_gt n b with hnb | hbn
    · rw [eulerianNumber_eq_zero_of_le hn hnb]
      exact Nat.zero_le _
    · have han : a < n := lt_of_le_of_lt hab hbn
      rw [eulerianNumber_symm han, eulerianNumber_symm hbn]
      refine eulerianNumber_monotoneOn n ?_ ?_ (by omega)
      · rw [Set.mem_Iic]
        omega
      · rw [Set.mem_Iic]
        omega

end TauCeti
