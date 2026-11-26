/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Data.Finset.Sort
public import Mathlib.GroupTheory.Perm.Fin
public import TauCeti.GroupTheory.Perm.Basic
public import Mathlib.GroupTheory.Perm.List
public import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic
import Mathlib.Data.Fintype.Fin
-- Non-public: a cycle and an adjacent transposition generate the permutation group.
import Mathlib.GroupTheory.Perm.Closure

/-!
# Permutations of `Fin n`

This file supplements Mathlib's `Mathlib.GroupTheory.Perm.Fin`.

## Main results

* `Fin.coe_cycleRange`: the value of the cycle `Fin.cycleRange i = (0 1 ⋯ i)` at `j`, as a
  natural number, read off the comparison of the values of `j` and `i`. Unlike
  `Fin.cycleRange_apply` it needs no `NeZero n` instance, and both its case split and its result
  are stated on natural numbers, ready for `omega`.
* `List.formPerm_finRange`, `Fin.formPerm_sort_univ`: the cycle through the points of `Fin n` in
  increasing order is the rotation `finRotate n`, that is `i ↦ i + 1` modulo `n`.
* `Fin.swap_apply_lt_swap_apply`: an adjacent transposition `(a a+1)` of `Fin n` keeps every
  strict pair in order except `a < a + 1` itself.
* `Fin.cons_comp_perm`: prepending a fixed first entry commutes with permuting the other entries,
  through the permutation `Equiv.Perm.decomposeFin.symm (0, σ)` of `Fin (n + 1)` fixing `0`.
* `TauCeti.isCycleOn_finRotate`: the rotation `finRotate n` is a single cycle on all of `Fin n`.
* `TauCeti.closure_finRotate_swap_eq_top`: the rotation `finRotate n` and the transposition `(0 1)`
  generate the permutations of `Fin n`.
* `MonoidHom.ext_perm_fin`: a monoid homomorphism out of the permutations of `Fin n` is
  determined by its values at `finRotate n` and `(0 1)`.
* `Equiv.Perm.eq_one_of_rows`: a permutation of `Fin (m * n)` that fixes every point of each
  row `finProdFinEquiv (i, ·)` is the identity. Checking one row at a time keeps each
  `decide +kernel` certificate small.
* `Equiv.Perm.sum_comp_symm_apply_zero`: summing a function of `σ⁻¹ 0` over all permutations of
  `Fin (n + 1)` counts each value `n!` times.
* `Equiv.Perm.consFin`, `Equiv.Perm.snocFin`: ordered insertion and its sign in every
  dimension, including the empty tail missing from the primed Mathlib decomposition.
* `TauCeti.sum_sign_smul_eq_sum_consFin`: reindex a signed permutation sum through ordered
  first-coordinate insertion, including dimension zero.
* `Equiv.Perm.card_filter_val_lt`: a permutation of `Fin n` maps `min n m` indices below `m`.
* `Equiv.Perm.IsSwap.two_le`: if `Fin n` admits a transposition, then `2 ≤ n`.
-/

public section

namespace Fin

/-- The value of the cycle `(0 1 ⋯ i)` at `j`: one more than `j` below `i`, `0` at `i`, and `j`
above `i`. -/
theorem coe_cycleRange {n : ℕ} (i j : Fin n) :
    (cycleRange i j : ℕ) = if (j : ℕ) < i then (j : ℕ) + 1 else if (j : ℕ) = i then 0 else j := by
  rcases le_or_gt j i with h | h
  · rw [coe_cycleRange_of_le h]
    simp only [Fin.ext_iff]
    split_ifs <;> omega
  · rw [cycleRange_of_gt h]
    split_ifs <;> omega

/-- The cycle through the points of `Fin n` in increasing order is the rotation `i ↦ i + 1`
modulo `n`. -/
@[simp]
theorem _root_.List.formPerm_finRange (n : ℕ) : (List.finRange n).formPerm = finRotate n := by
  ext x
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := x.pos; omega⟩
  have hx : (List.finRange (m + 1))[(x : ℕ)]'(by simp [x.isLt]) = x := by simp
  rw [← hx, List.formPerm_apply_getElem _ (List.nodup_finRange _)]
  simp only [List.getElem_finRange, Fin.val_cast, List.length_finRange, coe_finRotate, Fin.ext_iff,
    Fin.val_last]
  split_ifs with h
  · rw [h, Nat.mod_self]
  · exact Nat.mod_eq_of_lt (by omega)

/-- The cycle through the points of `Fin n`, enumerated in increasing order by `Finset.sort`, is
the rotation `i ↦ i + 1` modulo `n`. -/
@[simp]
theorem formPerm_sort_univ (n : ℕ) :
    (Finset.univ : Finset (Fin n)).sort.formPerm = finRotate n := by
  rw [sort_univ, List.formPerm_finRange]

/-- An adjacent transposition `(a b)`, with `b = a + 1`, preserves the strict order of every pair
of elements of `Fin n` other than the pair `a < b` itself. -/
theorem swap_apply_lt_swap_apply {n : ℕ} {a b i j : Fin n} (hab : (a : ℕ) + 1 = b) (hij : i < j)
    (hne : ¬(i = a ∧ j = b)) : Equiv.swap a b i < Equiv.swap a b j := by
  simp only [Equiv.swap_apply_def]
  simp only [Fin.lt_def, Fin.ext_iff] at hij hne ⊢
  split_ifs <;> simp_all <;> omega

/-- Prepending a fixed first entry commutes with permuting the other entries: the permutation `σ`
of the last `n` coordinates extends, by `Equiv.Perm.decomposeFin`, to the permutation of
`Fin (n + 1)` that fixes `0`. -/
theorem cons_comp_perm {α : Type*} {n : ℕ} (a : α) (y : Fin n → α) (σ : Equiv.Perm (Fin n)) :
    (cons a (y ∘ σ) : Fin (n + 1) → α) =
      (cons a y : Fin (n + 1) → α) ∘ Equiv.Perm.decomposeFin.symm (0, σ) := by
  funext i
  cases i using Fin.cases <;>
    simp [Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.decomposeFin_symm_apply_succ]

end Fin

namespace TauCeti

/-- The rotation `i ↦ i + 1` of `Fin n` is a single cycle on all of `Fin n`. -/
theorem isCycleOn_finRotate : ∀ {n : ℕ}, (finRotate n).IsCycleOn Set.univ
  | 0 => Equiv.Perm.isCycleOn_of_subsingleton _ _
  | 1 => Equiv.Perm.isCycleOn_of_subsingleton _ _
  | _ + 2 => by
    convert isCycle_finRotate.isCycleOn using 1
    ext x
    simp

/-- **The rotation `finRotate n` and the transposition `(0 1)` generate the permutations of
`Fin n`.** -/
theorem closure_finRotate_swap_eq_top : ∀ {n : ℕ} [NeZero n],
    Subgroup.closure {finRotate n, Equiv.swap (0 : Fin n) 1} = ⊤
  | 0, h => absurd rfl h.out
  | 1, _ => eq_top_iff.2 fun g _ => Subsingleton.elim g 1 ▸ one_mem _
  | n + 2, _ => by
    simpa using Equiv.Perm.closure_cycle_adjacent_swap (σ := finRotate (n + 2)) isCycle_finRotate
      support_finRotate 0

end TauCeti

namespace MonoidHom

/-- A monoid homomorphism out of the permutations of `Fin n` is determined by its values at the
generators `finRotate n` and `(0 1)`. -/
theorem ext_perm_fin {n : ℕ} [NeZero n] {M : Type*} [Monoid M]
    {f g : Equiv.Perm (Fin n) →* M} (h₁ : f (finRotate n) = g (finRotate n))
    (h₂ : f (Equiv.swap 0 1) = g (Equiv.swap 0 1)) : f = g :=
  eq_of_eqOn_dense TauCeti.closure_finRotate_swap_eq_top <| by
    rintro x (rfl | rfl)
    exacts [h₁, h₂]

end MonoidHom

namespace Equiv.Perm

/-- A permutation preserving consecutive adjacency and fixing the last point of a finite
chain is the identity. Only forward preservation of adjacency is needed. -/
theorem eq_one_of_adjacent_of_apply_last_eq_self {n : ℕ} {σ : Perm (Fin (n + 1))}
    (hadj : ∀ i j, i.val + 1 = j.val →
      (σ i).val + 1 = (σ j).val ∨ (σ j).val + 1 = (σ i).val)
    (hlast : σ (Fin.last n) = Fin.last n) : σ = 1 := by
  have hfix : ∀ k : ℕ, ∀ j : Fin (n + 1), n - j.val ≤ k → σ j = j := by
    intro k
    induction k with
    | zero =>
        intro j hj
        have hjlast : j = Fin.last n := by apply Fin.ext; simp only [Fin.val_last]; omega
        simpa [hjlast] using hlast
    | succ k ih =>
        intro j hj
        by_cases hj' : n - j.val ≤ k
        · exact ih j hj'
        let s : Fin (n + 1) := ⟨j.val + 1, by omega⟩
        have hs : σ s = s := ih s (by dsimp only [s, Fin.val_mk]; omega)
        have hstep := hadj j s rfl
        rw [hs] at hstep
        have hne : (σ j).val ≠ j.val + 2 := by
          intro he
          have hfixed := ih (σ j) (by omega)
          have hjfix : σ j = j := σ.injective hfixed
          have := congrArg Fin.val hjfix
          omega
        apply Fin.ext
        dsimp only [s, Fin.val_mk] at hstep
        omega
  exact Equiv.ext fun j ↦ hfix (n - j.val) j le_rfl

/-- A permutation of `Fin (m * n)` is the identity once it fixes every point of each row
`finProdFinEquiv (i, ·)`. Splitting a kernel decision over the rows keeps each certificate small. -/
theorem eq_one_of_rows {m n : ℕ} (p : Equiv.Perm (Fin (m * n)))
    (h : ∀ i j, p (finProdFinEquiv (i, j)) = finProdFinEquiv (i, j)) : p = 1 := by
  refine Equiv.ext fun k ↦ ?_
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k
  exact h i j

/-- A product over all permutations of `Fin (n + 1)` of a function of `σ⁻¹ 0` takes each value
`n!` times. -/
@[to_additive /-- A sum over all permutations of `Fin (n + 1)` of a function of `σ⁻¹ 0` takes each
value `n!` times. -/]
theorem prod_comp_symm_apply_zero {M : Type*} [CommMonoid M] {n : ℕ} (f : Fin (n + 1) → M) :
    ∏ σ : Perm (Fin (n + 1)), f (σ.symm 0) = (∏ p, f p) ^ n.factorial := by
  rw [← Fintype.prod_equiv (Equiv.inv (Perm (Fin (n + 1)))) (fun σ ↦ f (σ 0))
    (fun σ ↦ f (σ.symm 0)) fun σ ↦ rfl,
    ← Fintype.prod_equiv (decomposeFin.symm : Fin (n + 1) × Perm (Fin n) ≃ _)
      (fun pe ↦ f pe.1) (fun σ ↦ f (σ 0)) fun pe ↦ by rw [decomposeFin_symm_apply_zero]]
  simp [Fintype.prod_prod_type, Finset.prod_const, Fintype.card_perm, Finset.prod_pow]

section

open _root_.Finset

/-- A permutation of `Fin n` maps `min n m` indices below `m`. -/
theorem card_filter_val_lt {n m : ℕ} (σ : Perm (Fin n)) :
    #{i : Fin n | (σ i : ℕ) < m} = min n m :=
  (card_equiv σ fun _ => by simp).trans Fin.card_filter_val_lt

end

/-- If `Fin n` admits a transposition, then `2 ≤ n`. -/
theorem IsSwap.two_le {n : ℕ} {τ : Perm (Fin n)} (hτ : τ.IsSwap) : 2 ≤ n := by
  simpa only [Fintype.card_fin] using hτ.two_le_card

end Equiv.Perm

noncomputable section

namespace Equiv.Perm


/-- Ordered first-coordinate insertion, extending Mathlib's primed decomposition to the
empty tail. The positive-dimensional cases are exactly `decomposeFin'Symm`. -/
def consFin : {n : ℕ} → Fin (n + 1) → Perm (Fin n) → Perm (Fin (n + 1))
  | 0, _, _ => 1
  | _ + 1, j, π => decomposeFin'Symm j π

/-- Positive-dimensional ordered insertion is the native Mathlib construction. -/
lemma consFin_eq_decomposeFin'Symm {n : ℕ} (j : Fin (n + 2)) (π : Perm (Fin (n + 1))) :
    consFin j π = decomposeFin'Symm j π := by
  rfl

/-- The distinguished coordinate is first. -/
@[simp]
lemma consFin_zero {n : ℕ} (j : Fin (n + 1)) (π : Perm (Fin n)) :
    consFin j π 0 = j := by
  cases n with
  | zero => exact Subsingleton.elim (α := Fin 1) _ _
  | succ n => exact decomposeFin'Symm_zero j π

/-- The remaining coordinates preserve their increasing-coordinate identification. -/
@[simp]
lemma consFin_succ {n : ℕ} (j : Fin (n + 1)) (π : Perm (Fin n)) (k : Fin n) :
    consFin j π k.succ = j.succAbove (π k) := by
  cases n with
  | zero => exact k.elim0
  | succ n => exact decomposeFin'Symm_succ j π k

/-- The first coordinate has position zero. -/
@[simp]
lemma consFin_symm_self {n : ℕ} (j : Fin (n + 1)) (π : Perm (Fin n)) :
    (consFin j π).symm j = 0 := by
  cases n with
  | zero => exact Subsingleton.elim (α := Fin 1) _ _
  | succ n => exact decomposeFin'Symm_symm_eq_zero j π

/-- The position of another coordinate is its position in the smaller permutation, plus one. -/
@[simp]
lemma consFin_symm_succAbove {n : ℕ} (j : Fin (n + 1))
    (π : Perm (Fin n)) (k : Fin n) :
    (consFin j π).symm (j.succAbove (π k)) = k.succ := by
  cases n with
  | zero => exact k.elim0
  | succ n => exact decomposeFin'Symm_symm_succAbove j π k

/-- Ordered insertion has the native coordinate insertion sign, including the empty tail. -/
@[simp]
lemma sign_consFin {n : ℕ} (j : Fin (n + 1)) (π : Perm (Fin n)) :
    (consFin j π).sign = (-1) ^ (j : ℕ) * π.sign := by
  cases n with
  | zero =>
    have hj : j = 0 := Subsingleton.elim (α := Fin 1) _ _
    have hπ : π = 1 := Subsingleton.elim _ _
    subst j
    subst π
    simp [consFin]
  | succ n => exact sign_decomposeFin'Symm j π

/-- Every permutation is uniquely an ordered insertion. For a nonempty tail this is the
inverse of Mathlib's `decomposeFin'`; the empty-tail case is the unique map. -/
def consFinEquiv : (n : ℕ) → Fin (n + 1) × Perm (Fin n) ≃ Perm (Fin (n + 1))
  | 0 => Equiv.ofBijective (fun p : Fin 1 × Perm (Fin 0) ↦
      (consFin p.1 p.2 : Perm (Fin 1)))
      (Function.bijective_of_subsingleton' (α := Fin 1 × Perm (Fin 0))
        (β := Perm (Fin 1)) _)
  | _ + 1 => decomposeFin'.symm

/-- The first-coordinate equivalence evaluates to ordered insertion. -/
@[simp]
lemma consFinEquiv_apply {n : ℕ} (j : Fin (n + 1)) (π : Perm (Fin n)) :
    consFinEquiv n (j, π) = consFin j π := by
  cases n with
  | zero => exact Subsingleton.elim (α := Perm (Fin 1)) _ _
  | succ n => exact decomposeFin'_symm j π

/-- The ordering obtained by placing the distinguished coordinate last. -/
def snocFin {n : ℕ} (j : Fin (n + 1)) (π : Perm (Fin n)) :
    Perm (Fin (n + 1)) := consFin j π * finRotate (n + 1)

/-- The earlier steps of the last-coordinate ordering follow the smaller permutation. -/
@[simp]
lemma snocFin_castSucc {n : ℕ} (j : Fin (n + 1)) (π : Perm (Fin n))
    (i : Fin n) : snocFin j π i.castSucc = j.succAbove (π i) := by
  have hi : finRotate (n + 1) i.castSucc = i.succ := by
    apply Fin.ext
    rw [coe_finRotate_of_ne_last (Fin.castSucc_ne_last i)]
    rfl
  simp [snocFin, Perm.mul_apply, hi]

/-- The distinguished coordinate is the last step. -/
@[simp]
lemma snocFin_last {n : ℕ} (j : Fin (n + 1)) (π : Perm (Fin n)) :
    snocFin j π (Fin.last (n)) = j := by
  simp [snocFin, Perm.mul_apply]

/-- The distinguished coordinate has the last position in this ordering. -/
@[simp]
lemma snocFin_symm_self {n : ℕ} (j : Fin (n + 1)) (π : Perm (Fin n)) :
    (snocFin j π).symm j = Fin.last (n) := by
  apply (snocFin j π).injective
  simp

/-- The position of an earlier coordinate in the last-coordinate ordering. -/
@[simp]
lemma snocFin_symm_succAbove {n : ℕ} (j : Fin (n + 1))
    (π : Perm (Fin n)) (i : Fin n) :
    (snocFin j π).symm (j.succAbove (π i)) = i.castSucc := by
  apply (snocFin j π).injective
  simp

/-- The sign of the ordering with the distinguished coordinate last. -/
@[simp]
lemma sign_snocFin {n : ℕ} (j : Fin (n + 1)) (π : Perm (Fin n)) :
    (snocFin j π).sign = (-1) ^ ((j : ℕ) + n) * π.sign := by
  simp [snocFin, Perm.sign_mul, sign_consFin, sign_finRotate,
    pow_add, mul_assoc, mul_comm]

/-- Every permutation is uniquely a last-coordinate insertion, including the empty tail. -/
def snocFinEquiv (n : ℕ) : Fin (n + 1) × Perm (Fin n) ≃ Perm (Fin (n + 1)) :=
  (consFinEquiv n).trans (Equiv.mulRight (finRotate (n + 1)))

/-- The last-coordinate equivalence evaluates to ordered insertion. -/
@[simp]
lemma snocFinEquiv_apply {n : ℕ} (j : Fin (n + 1)) (π : Perm (Fin n)) :
    snocFinEquiv n (j, π) = snocFin j π := by
  simp [snocFinEquiv, snocFin]

end Equiv.Perm

end

namespace TauCeti

open Equiv

/-- Reindex a signed permutation sum by the first coordinate and the remaining ordering.
This is the common decomposition step in simplex and cube boundary formulas. -/
theorem sum_sign_smul_eq_sum_consFin {A : Type*} [AddCommGroup A] (n : ℕ)
    (F : Perm (Fin (n + 1)) → A) :
    ∑ π : Perm (Fin (n + 1)), π.sign • F π =
      ∑ j : Fin (n + 1), ((-1 : ℤ) ^ (j : ℕ)) •
        ∑ π : Perm (Fin n), π.sign • F (Perm.consFin j π) := by
  rw [← (Perm.consFinEquiv n).sum_comp, Fintype.sum_prod_type]
  simp only [Perm.consFinEquiv_apply, Perm.sign_consFin, mul_smul, Finset.smul_sum,
    Units.smul_def, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]

end TauCeti
