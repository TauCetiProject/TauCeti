/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Coxeter.Length
public import TauCeti.LinearAlgebra.Matrix.Cartan.Realization.Weyl.Basic
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Matrix
import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
import TauCeti.GroupTheory.Coxeter.Basic
import TauCeti.GroupTheory.Coxeter.Dihedral
import TauCeti.GroupTheory.Coxeter.Geometric.Basic

/-!
# The Weyl group of a Kac–Moody realization is a Coxeter group

Let `A : Matrix I I ℤ` be a generalized Cartan matrix (`A i i = 2`, `A i j ≤ 0` for `i ≠ j`, and
`A i j = 0 ↔ A j i = 0`) and let `R : CartanRealization (A.map Int.cast) H` be a realization of
`A` over a field `K`. No symmetrizability, nonsingularity, finiteness of `I`, or finite
dimensionality of `H` is assumed.

This file reads a Coxeter matrix `TauCeti.cartanCoxeterMatrix A` off `A` (assigning `2, 3, 4, 6`
when `A i j * A j i = 0, 1, 2, 3` for `i ≠ j`, `0` when `3 < A i j * A j i`, and `1` on the
diagonal), verifies the braid relations of the simple reflections over an arbitrary field `K` via
Mathlib's Chebyshev reflection formulas (`Module.reflection_mul_reflection_pow_apply`), and proves
Kac's **Lemma 3.11** and **Proposition 3.13** over any field of characteristic zero:

* `ℓ(w sᵢ) < ℓ(w)` if and only if `-w(αᵢ) ∈ Q₊`, and `ℓ(w sᵢ) = ℓ(w) + 1` if and only if
  `w(αᵢ) ∈ Q₊`;
* the canonical lift `(cartanCoxeterMatrix A).Group →* R.weylGroup _` is an isomorphism of groups,
  equipping `R.weylGroup _` with a `CoxeterSystem` whose Coxeter length agrees with
  `R.weylLength _`;
* the action of `R.weylGroup _` on the root lattice `Q` is faithful even when `A` is singular or
  `H` has central directions, and any two characteristic-zero realizations of `A` have canonically
  isomorphic Weyl groups matching simple reflections index-by-index.

## Main definitions

* `TauCeti.cartanCoxeterMatrix`: the `CoxeterMatrix I` read off an integer matrix `A`.
* `TauCeti.CartanRealization.weylCoxeterHom`: the canonical lift
  `(cartanCoxeterMatrix A).Group →* R.weylGroup _` over any field.
* `TauCeti.CartanRealization.weylCoxeterEquiv`,
  `TauCeti.CartanRealization.weylCoxeterSystem`: the Coxeter group isomorphism and `CoxeterSystem`
  on `R.weylGroup _` in characteristic zero.
* `TauCeti.CartanRealization.weylGroupEquiv`: the canonical isomorphism between the Weyl groups of
  any two characteristic-zero realizations of `A`.

## Main results

* `TauCeti.CartanRealization.isLiftable_weylSimple`: the simple reflections satisfy the Coxeter
  relations of `cartanCoxeterMatrix A` over any field.
* `TauCeti.CartanRealization.weylLength_mul_weylSimple_lt_iff`,
  `TauCeti.CartanRealization.weylLength_mul_weylSimple_eq_add_one_iff`: Kac's Lemma 3.11.
* `TauCeti.CartanRealization.weylCoxeterSystem_length`: Coxeter length equals `R.weylLength _`.
* `TauCeti.CartanRealization.orderOf_weylSimple_mul_weylSimple`: the exact order of `sᵢ * sⱼ` is
  `cartanCoxeterMatrix A i j` (`0` meaning infinite order when `3 < A i j * A j i` for `i ≠ j`).
* `TauCeti.CartanRealization.rootLatticeAction_injective`: `W` acts faithfully on `Q`.

## References

* V. G. Kac, *Infinite-dimensional Lie algebras*, third edition, Cambridge University Press, 1990,
  §§3.7–3.13 (Lemma 3.11 and Proposition 3.13).
-/

public section

open Module Polynomial.Chebyshev

namespace TauCeti

/-! ### The Coxeter matrix of an integer matrix -/

section CartanCoxeterMatrix

variable {I : Type*} [DecidableEq I]

/-- **The Coxeter matrix read off an integer matrix `A`.** On the diagonal its entries are `1`;
off the diagonal its `(i, j)` entry is `coxeterOrder (A i j * A j i)` (`2, 3, 4, 6` on
`0, 1, 2, 3`) when `A i j * A j i ≤ 3`, and `0` (Mathlib's encoding of `∞`) when
`3 < A i j * A j i`. -/
def cartanCoxeterMatrix (A : Matrix I I ℤ) : CoxeterMatrix I where
  M := .of fun i j ↦
    if i = j then 1
    else if A i j * A j i ≤ 3 then coxeterOrder (A i j * A j i) else 0
  isSymm := by
    ext i j
    simp only [Matrix.transpose_apply, Matrix.of_apply, eq_comm (a := j), mul_comm (A j i)]
  diagonal i := by simp
  off_diagonal i j hij := by
    simp only [Matrix.of_apply, hij, ↓reduceIte]
    split_ifs with hle
    · by_cases hmem : A i j * A j i ∈ ({0, 1, 2, 3} : Set ℤ)
      · have := two_le_coxeterOrder hmem
        omega
      · have hnot : A i j * A j i ∉ ({0, 1, 2, 3, 4} : Set ℤ) := by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem ⊢
          omega
        rw [coxeterOrder_eq_zero_iff.mpr hnot]
        exact Nat.zero_ne_one
    · exact Nat.zero_ne_one

theorem cartanCoxeterMatrix_apply (A : Matrix I I ℤ) (i j : I) :
    cartanCoxeterMatrix A i j =
      if i = j then 1
      else if A i j * A j i ≤ 3 then coxeterOrder (A i j * A j i) else 0 := (rfl)

theorem cartanCoxeterMatrix_of_ne_of_le {A : Matrix I I ℤ} {i j : I} (hij : i ≠ j)
    (h : A i j * A j i ≤ 3) :
    cartanCoxeterMatrix A i j = coxeterOrder (A i j * A j i) := by
  simp [cartanCoxeterMatrix_apply, hij, h]

theorem cartanCoxeterMatrix_of_ne_of_lt {A : Matrix I I ℤ} {i j : I} (hij : i ≠ j)
    (h : 3 < A i j * A j i) :
    cartanCoxeterMatrix A i j = 0 := by
  simp [cartanCoxeterMatrix_apply, hij, not_le.mpr h]

/-- When `0 ≤ A i j * A j i` and `i ≠ j`, the Coxeter entry vanishes (representing `∞`) exactly
when the Cartan product exceeds `3`. -/
theorem cartanCoxeterMatrix_eq_zero_iff {A : Matrix I I ℤ} {i j : I} (hij : i ≠ j)
    (hnonneg : 0 ≤ A i j * A j i) :
    cartanCoxeterMatrix A i j = 0 ↔ 3 < A i j * A j i := by
  refine ⟨fun h ↦ not_le.mp fun hle ↦ ?_, cartanCoxeterMatrix_of_ne_of_lt hij⟩
  have hmem : A i j * A j i ∈ ({0, 1, 2, 3} : Set ℤ) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; omega
  have := two_le_coxeterOrder hmem
  rw [cartanCoxeterMatrix_of_ne_of_le hij hle] at h
  omega

/-- When `A` has symmetric zero pattern and `A i i ≠ 0`, the Coxeter entry at `(i, j)` is `2`
exactly when `A i j = 0`. -/
theorem cartanCoxeterMatrix_eq_two_iff {A : Matrix I I ℤ}
    (hdiag : ∀ i, A i i ≠ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) (i j : I) :
    cartanCoxeterMatrix A i j = 2 ↔ A i j = 0 := by
  rcases eq_or_ne i j with rfl | hij
  · simp [hdiag i]
  · rcases le_or_gt (A i j * A j i) 3 with hle | hlt
    · rw [cartanCoxeterMatrix_of_ne_of_le hij hle, coxeterOrder_eq_two_iff, mul_eq_zero]
      exact or_iff_left_iff_imp.mpr (hzero i j).mpr
    · rw [cartanCoxeterMatrix_of_ne_of_lt hij hlt]
      refine ⟨by omega, fun h₀ ↦ absurd ?_ (not_le.mpr hlt)⟩
      simp [h₀]

/-- When all off-diagonal Cartan products lie in `{0, 1, 2, 3}`, `cartanCoxeterMatrix` agrees with
`coxeterMatrixOfCartanMatrix`. -/
theorem cartanCoxeterMatrix_eq_coxeterMatrixOfCartanMatrix (A : Matrix I I ℤ)
    (hdiag : ∀ i, A i i = 2)
    (hmem : ∀ i j, i ≠ j → A i j * A j i ∈ ({0, 1, 2, 3} : Set ℤ)) :
    cartanCoxeterMatrix A = coxeterMatrixOfCartanMatrix A hdiag hmem := by
  ext i j
  rcases eq_or_ne i j with rfl | hij
  · simp
  · have hle : A i j * A j i ≤ 3 := by
      have := hmem i j hij
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
      omega
    rw [cartanCoxeterMatrix_of_ne_of_le hij hle, coxeterMatrixOfCartanMatrix_apply]

end CartanCoxeterMatrix

namespace CartanRealization

/-! ### Braid relations and rank-two Chebyshev positivity over an arbitrary field -/

private theorem simpleReflection_comm_of_eq_zero {I K H : Type*} [Field K] [AddCommGroup H]
    [Module K H] {A : Matrix I I ℤ} (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)
    (hdiag : ∀ i, A i i = 2) {i j : I} (hij : A i j = 0) (hji : A j i = 0) :
    R.simpleReflection (diag_map_intCast hdiag) i *
        R.simpleReflection (diag_map_intCast hdiag) j =
      R.simpleReflection (diag_map_intCast hdiag) j *
        R.simpleReflection (diag_map_intCast hdiag) i := by
  ext φ h
  simp only [mul_apply_eq_comp, simpleReflection_apply, map_sub, map_smul, root_coroot,
    Matrix.map_apply, hij, hji, Int.cast_zero, zero_smul, sub_zero]
  exact sub_right_comm _ _ _

/-- For `t ≥ 2`, the Chebyshev `S`-sequence `(S ℤ n).eval t` is positive and nondecreasing on
`ℕ`. -/
private theorem one_le_chebyshev_S_eval_of_two_le {t : ℤ} (ht : 2 ≤ t) :
    ∀ n : ℕ, 1 ≤ (S ℤ n).eval t ∧ (S ℤ n).eval t ≤ (S ℤ (n + 1 : ℕ)).eval t
  | 0 => by simp; omega
  | n + 1 => by
    obtain ⟨h1, hmono⟩ := one_le_chebyshev_S_eval_of_two_le ht n
    push_cast at hmono ⊢
    have hrec : (S ℤ ((n : ℤ) + 1 + 1)).eval t =
        t * (S ℤ ((n : ℤ) + 1)).eval t - (S ℤ n).eval t := by
      simp [add_assoc, S_add_two]
    have hmul : 2 * (S ℤ ((n : ℤ) + 1)).eval t ≤ t * (S ℤ ((n : ℤ) + 1)).eval t :=
      mul_le_mul_of_nonneg_right ht (by omega)
    exact ⟨by omega, by omega⟩

/-- The two Chebyshev combinations occurring in `(sᵢ sⱼ)^n (αᵢ)` and `sⱼ (sᵢ sⱼ)^n (αᵢ)` are
nonnegative for every reduced alternating word of length `m` not ending in `i`. -/
private theorem nonneg_chebyshev_pair {c : ℤ} (hc : 0 ≤ c) {m : ℕ}
    (hm : c ≤ 3 → m < coxeterOrder c) :
    0 ≤ (S ℤ (m / 2 : ℕ)).eval (c - 2) + (S ℤ (((m / 2 : ℕ) : ℤ) - 1)).eval (c - 2) ∧
      0 ≤ (if Even m then (S ℤ (((m / 2 : ℕ) : ℤ) - 1)).eval (c - 2)
        else (S ℤ (m / 2 : ℕ)).eval (c - 2)) := by
  rcases le_or_gt c 3 with hle | hgt
  · have hlt := hm hle
    have hmem : c ∈ ({0, 1, 2, 3} : Set ℤ) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; omega
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with rfl | rfl | rfl | rfl
    · rw [coxeterOrder_zero] at hlt
      interval_cases m <;> simp [Nat.even_iff, S_neg_one, S_zero]
    · rw [coxeterOrder_one] at hlt
      interval_cases m <;> simp [Nat.even_iff, S_neg_one, S_zero, S_one]
    · rw [coxeterOrder_two] at hlt
      interval_cases m <;> simp [Nat.even_iff, S_neg_one, S_zero, S_one]
    · rw [coxeterOrder_three] at hlt
      interval_cases m <;> simp [Nat.even_iff, S_neg_one, S_zero, S_one, S_two]
  · have ht : 2 ≤ c - 2 := by omega
    have hn := (one_le_chebyshev_S_eval_of_two_le ht (m / 2)).1
    have hn1 : 0 ≤ (S ℤ (((m / 2 : ℕ) : ℤ) - 1)).eval (c - 2) := by
      rcases eq_zero_or_pos (m / 2) with h0 | hpos
      · simp [h0]
      · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
        have hk1 := (one_le_chebyshev_S_eval_of_two_le ht k).1
        simpa [hk] using le_trans zero_le_one hk1
    exact ⟨by omega, by split_ifs <;> omega⟩

/-- Closed-form Chebyshev evaluation of `((if Even m then 1 else sⱼ) * (sᵢ * sⱼ) ^ (m / 2)) αᵢ`. -/
private theorem alternating_simpleReflection_apply_root {I K H : Type*} [Field K] [AddCommGroup H]
    [Module K H] {A : Matrix I I ℤ} (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)
    (hdiag : ∀ i, A i i = 2) (i j : I) (m : ℕ) :
    let hd := diag_map_intCast (K := K) hdiag
    let c := A i j * A j i
    let aZ : ℤ := (S ℤ (m / 2 : ℕ)).eval (c - 2) + (S ℤ (((m / 2 : ℕ) : ℤ) - 1)).eval (c - 2)
    let bS : ℤ := if Even m then (S ℤ (((m / 2 : ℕ) : ℤ) - 1)).eval (c - 2)
      else (S ℤ (m / 2 : ℕ)).eval (c - 2)
    (((if Even m then 1 else R.simpleReflection hd j) *
        (R.simpleReflection hd i * R.simpleReflection hd j) ^ (m / 2)) (R.root i)) =
      (aZ : K) • R.root i + ((bS * -A j i : ℤ) : K) • R.root j := by
  intro hd c aZ bS
  have hfi : (Dual.eval K H (R.coroot i)) (R.root i) = 2 := by simp [hdiag i]
  have hfj : (Dual.eval K H (R.coroot j)) (R.root j) = 2 := by simp [hdiag j]
  have htK : ((c - 2 : ℤ) : K) =
      (Dual.eval K H (R.coroot i)) (R.root j) *
        (Dual.eval K H (R.coroot j)) (R.root i) - 2 := by
    simp [c, R.root_coroot]
  have hS1 : (S K (m / 2 : ℕ)).eval ((c - 2 : ℤ) : K) =
      (((S ℤ (m / 2 : ℕ)).eval (c - 2) : ℤ) : K) :=
    (Polynomial.Chebyshev.algebraMap_eval_S (c - 2) (m / 2 : ℕ)).symm
  have hS2 : (S K (((m / 2 : ℕ) : ℤ) - 1)).eval ((c - 2 : ℤ) : K) =
      (((S ℤ (((m / 2 : ℕ) : ℤ) - 1)).eval (c - 2) : ℤ) : K) :=
    (Polynomial.Chebyshev.algebraMap_eval_S (c - 2) (((m / 2 : ℕ) : ℤ) - 1)).symm
  have hg : -(Dual.eval K H (R.coroot j) (R.root i)) = ((-A j i : ℤ) : K) := by
    simp [R.root_coroot]
  rw [R.simpleReflection_eq_reflection hd i hfi, R.simpleReflection_eq_reflection hd j hfj]
  by_cases hm_even : Even m
  · simp only [hm_even, ↓reduceIte, one_mul, bS]
    rw [Module.reflection_mul_reflection_pow_apply_self hfi hfj (m / 2) ((c - 2 : ℤ) : K) htK,
      hS1, hS2, hg]
    simp only [aZ, Int.cast_add, Int.cast_mul, Int.cast_neg]
  · simp only [hm_even, ↓reduceIte, bS]
    rw [Module.reflection_mul_reflection_mul_reflection_pow_apply_self hfi hfj (m / 2)
      ((c - 2 : ℤ) : K) htK, hS1, hS2, hg]
    simp only [aZ, Int.cast_add, Int.cast_mul, Int.cast_neg]

section BraidRelations

variable {I K H : Type*} [DecidableEq I] [Field K] [AddCommGroup H] [Module K H]
  {A : Matrix I I ℤ} (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)

/-- **The braid relations of `cartanCoxeterMatrix A` hold on `Dual K H` over any field.** -/
theorem simpleReflection_mul_pow_cartanCoxeterMatrix (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) (i j : I) :
    (R.simpleReflection (diag_map_intCast hdiag) i *
        R.simpleReflection (diag_map_intCast hdiag) j) ^ cartanCoxeterMatrix A i j = 1 := by
  let hd := diag_map_intCast (K := K) hdiag
  rcases eq_or_ne i j with rfl | hij
  · simp
  rcases lt_or_ge 3 (A i j * A j i) with hlt | hle
  · rw [cartanCoxeterMatrix_of_ne_of_lt hij hlt, pow_zero]
  rw [cartanCoxeterMatrix_of_ne_of_le hij hle]
  have hnonneg : 0 ≤ A i j * A j i :=
    mul_nonneg_of_nonpos_of_nonpos (hoff i j hij) (hoff j i hij.symm)
  have hmem : A i j * A j i ∈ ({0, 1, 2, 3} : Set ℤ) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; omega
  have hpair : (Dual.eval K H (R.coroot i)) (R.root j) *
      (Dual.eval K H (R.coroot j)) (R.root i) = ((A i j * A j i : ℤ) : K) := by
    simp [R.root_coroot]
  have hfi : (Dual.eval K H (R.coroot i)) (R.root i) = 2 := by simp [hdiag i]
  have hfj : (Dual.eval K H (R.coroot j)) (R.root j) = 2 := by simp [hdiag j]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with hc | hc | hc | hc
  · rw [hc, coxeterOrder_zero, sq]
    have hij0 : A i j = 0 := (mul_eq_zero.mp hc).elim id (hzero i j).mpr
    rw [mul_assoc, ← mul_assoc (R.simpleReflection hd j),
      ← R.simpleReflection_comm_of_eq_zero hdiag hij0 ((hzero i j).mp hij0),
      mul_assoc, R.simpleReflection_mul_self, mul_one, R.simpleReflection_mul_self]
  · rw [hc, coxeterOrder_one, R.simpleReflection_eq_reflection hd i hfi,
      R.simpleReflection_eq_reflection hd j hfj]
    ext φ
    rw [Module.reflection_mul_reflection_pow_apply hfi hfj 3 φ (-1 : K)
      (by rw [hpair, hc]; norm_num), one_apply_eq_self]
    norm_num [S_zero, S_one]
  · rw [hc, coxeterOrder_two, R.simpleReflection_eq_reflection hd i hfi,
      R.simpleReflection_eq_reflection hd j hfj]
    ext φ
    rw [Module.reflection_mul_reflection_pow_apply hfi hfj 4 φ (0 : K)
      (by rw [hpair, hc]; norm_num), one_apply_eq_self]
    norm_num [S_zero, S_one]
  · rw [hc, coxeterOrder_three, R.simpleReflection_eq_reflection hd i hfi,
      R.simpleReflection_eq_reflection hd j hfj]
    ext φ
    rw [Module.reflection_mul_reflection_pow_apply hfi hfj 6 φ (1 : K)
      (by rw [hpair, hc]; norm_num), one_apply_eq_self]
    norm_num [S_two]

/-- **The simple reflections in `R.weylGroup` satisfy the Coxeter relations of
`cartanCoxeterMatrix A`.** -/
theorem isLiftable_weylSimple (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) :
    CoxeterMatrix.IsLiftable (cartanCoxeterMatrix A)
      (R.weylSimple (diag_map_intCast hdiag)) := fun i j ↦
  Subtype.ext <| by
    simpa using R.simpleReflection_mul_pow_cartanCoxeterMatrix hdiag hoff hzero i j

/-- The canonical group homomorphism from the presented Coxeter group
`(cartanCoxeterMatrix A).Group` to `R.weylGroup`, sending each generator `M.simple i` to
`R.weylSimple _ i`. -/
noncomputable def weylCoxeterHom (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) :
    (cartanCoxeterMatrix A).Group →* R.weylGroup (diag_map_intCast hdiag) :=
  (cartanCoxeterMatrix A).toCoxeterSystem.lift
    ⟨R.weylSimple (diag_map_intCast hdiag), R.isLiftable_weylSimple hdiag hoff hzero⟩

@[simp]
theorem weylCoxeterHom_simple (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) (i : I) :
    R.weylCoxeterHom hdiag hoff hzero ((cartanCoxeterMatrix A).simple i) =
      R.weylSimple (diag_map_intCast hdiag) i :=
  (cartanCoxeterMatrix A).toCoxeterSystem.lift_apply_simple
    (R.isLiftable_weylSimple hdiag hoff hzero) i

theorem weylCoxeterHom_wordProd (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) (l : List I) :
    R.weylCoxeterHom hdiag hoff hzero ((cartanCoxeterMatrix A).toCoxeterSystem.wordProd l) =
      (l.map (R.weylSimple (diag_map_intCast hdiag))).prod := by
  rw [CoxeterSystem.wordProd, map_list_prod, List.map_map]
  exact congrArg List.prod (congrArg (fun f ↦ l.map f)
    (funext (R.weylCoxeterHom_simple hdiag hoff hzero)))

/-- `weylCoxeterHom` is surjective onto `R.weylGroup`. -/
theorem weylCoxeterHom_surjective (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) :
    Function.Surjective (R.weylCoxeterHom hdiag hoff hzero) := fun w ↦ by
  obtain ⟨l, rfl⟩ := R.exists_word_prod_eq (diag_map_intCast hdiag) w
  exact ⟨(cartanCoxeterMatrix A).toCoxeterSystem.wordProd l,
    R.weylCoxeterHom_wordProd hdiag hoff hzero l⟩

private theorem not_wordProd_alternatingWord_succ_of_not_isRightDescent {i j : I}
    {v : (cartanCoxeterMatrix A).Group}
    (hdesc : ¬(cartanCoxeterMatrix A).toCoxeterSystem.IsRightDescent v i) (k : ℕ)
    (hkv : (cartanCoxeterMatrix A).toCoxeterSystem.length v = k + 1) :
    (cartanCoxeterMatrix A).toCoxeterSystem.wordProd
      (CoxeterSystem.alternatingWord j i (k + 1)) ≠ v := fun hk ↦
  hdesc <| by
    let cs₀ := (cartanCoxeterMatrix A).toCoxeterSystem
    have hmul : v * cs₀.simple i = cs₀.wordProd (CoxeterSystem.alternatingWord i j k) := by
      rw [← hk, CoxeterSystem.alternatingWord_succ, cs₀.wordProd_concat,
        cs₀.simple_mul_simple_cancel_right]
    rw [CoxeterSystem.IsRightDescent, hmul, hkv]
    exact (cs₀.length_wordProd_le _).trans_lt
      (by rw [CoxeterSystem.length_alternatingWord]; omega)

private theorem parabolic_pair_word_of_not_isRightDescent
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) {i j : I} (hij : i ≠ j)
    {v : (cartanCoxeterMatrix A).Group}
    (hv : v ∈ (cartanCoxeterMatrix A).toCoxeterSystem.parabolic {i, j})
    (hdesc : ¬(cartanCoxeterMatrix A).toCoxeterSystem.IsRightDescent v i) :
    (cartanCoxeterMatrix A).toCoxeterSystem.wordProd
        (CoxeterSystem.alternatingWord i j
          ((cartanCoxeterMatrix A).toCoxeterSystem.length v)) = v ∧
      (A i j * A j i ≤ 3 →
        (cartanCoxeterMatrix A).toCoxeterSystem.length v < coxeterOrder (A i j * A j i)) := by
  let cs₀ := (cartanCoxeterMatrix A).toCoxeterSystem
  have hv_eq : cs₀.wordProd (CoxeterSystem.alternatingWord i j (cs₀.length v)) = v := by
    rcases cs₀.wordProd_alternatingWord_eq_of_mem_parabolic_pair hv with h | h
    · exact h
    · rcases hm : (cartanCoxeterMatrix A).toCoxeterSystem.length v with _ | k
      · rw [List.eq_nil_of_length_eq_zero (CoxeterSystem.length_alternatingWord i j 0),
          cs₀.wordProd_nil, cs₀.length_eq_zero_iff.mp hm]
      · rw [show cs₀.length v = k + 1 from hm] at h
        exact absurd h (not_wordProd_alternatingWord_succ_of_not_isRightDescent hdesc k hm)
  refine ⟨hv_eq, fun hle ↦ ?_⟩
  have hM : cartanCoxeterMatrix A i j = coxeterOrder (A i j * A j i) :=
    cartanCoxeterMatrix_of_ne_of_le hij hle
  have hne0 : cartanCoxeterMatrix A i j ≠ 0 := by
    have h0 := mul_nonneg_of_nonpos_of_nonpos (hoff i j hij) (hoff j i hij.symm)
    have hmem : A i j * A j i ∈ ({0, 1, 2, 3} : Set ℤ) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; omega
    have h2 := two_le_coxeterOrder hmem
    rw [hM]; omega
  have hred : cs₀.IsReduced (CoxeterSystem.alternatingWord i j (cs₀.length v)) := by
    rw [CoxeterSystem.IsReduced, hv_eq, CoxeterSystem.length_alternatingWord]
  have hle' : cs₀.length v ≤ cartanCoxeterMatrix A i j :=
    not_lt.mp fun hgt ↦ cs₀.not_isReduced_alternatingWord i j hne0 hgt hred
  rcases lt_or_eq_of_le hle' with hlt | heq
  · rwa [← hM]
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hne0
    have hbr : cs₀.wordProd (CoxeterSystem.alternatingWord j i (k + 1)) = v := by
      calc cs₀.wordProd (CoxeterSystem.alternatingWord j i (k + 1))
        _ = cs₀.wordProd (CoxeterSystem.braidWord (cartanCoxeterMatrix A) j i) := by
            rw [CoxeterSystem.braidWord, (cartanCoxeterMatrix A).symmetric j i, hk,
              Nat.succ_eq_add_one]
        _ = cs₀.wordProd (CoxeterSystem.braidWord (cartanCoxeterMatrix A) i j) :=
            cs₀.wordProd_braidWord_eq j i
        _ = v := by rw [CoxeterSystem.braidWord, ← heq, hv_eq]
    exact absurd hbr
      (not_wordProd_alternatingWord_succ_of_not_isRightDescent hdesc k (heq.trans hk))

/-- In a rank-two standard parabolic subgroup `⟨sᵢ, sⱼ⟩`, an element `v` for which `i` is not a
right descent sends `αᵢ` to a natural combination `a • αᵢ + b • αⱼ`. -/
private theorem exists_apply_root_eq_nsmul_of_mem_parabolic_pair
    (hdiag : ∀ i, A i i = 2) (hoff : ∀ i j, i ≠ j → A i j ≤ 0)
    (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) {i j : I} (hij : i ≠ j)
    {v : (cartanCoxeterMatrix A).Group}
    (hv : v ∈ (cartanCoxeterMatrix A).toCoxeterSystem.parabolic {i, j})
    (hdesc : ¬(cartanCoxeterMatrix A).toCoxeterSystem.IsRightDescent v i) :
    ∃ a b : ℕ,
      ((R.weylCoxeterHom hdiag hoff hzero v :
          Dual K H ≃ₗ[K] Dual K H) (R.root i)) = a • R.root i + b • R.root j := by
  obtain ⟨hv_eq, hm_lt⟩ := parabolic_pair_word_of_not_isRightDescent hoff hij hv hdesc
  let m := (cartanCoxeterMatrix A).toCoxeterSystem.length v
  let hd := diag_map_intCast (K := K) hdiag
  let c := A i j * A j i
  have hnonneg : 0 ≤ c := mul_nonneg_of_nonpos_of_nonpos (hoff i j hij) (hoff j i hij.symm)
  obtain ⟨ha, hb⟩ := nonneg_chebyshev_pair (m := m) hnonneg hm_lt
  let aZ : ℤ := (S ℤ (m / 2 : ℕ)).eval (c - 2) + (S ℤ (((m / 2 : ℕ) : ℤ) - 1)).eval (c - 2)
  let bS : ℤ := if Even m then (S ℤ (((m / 2 : ℕ) : ℤ) - 1)).eval (c - 2)
    else (S ℤ (m / 2 : ℕ)).eval (c - 2)
  have hbZ : 0 ≤ bS * -A j i := mul_nonneg hb (neg_nonneg.mpr (hoff j i hij.symm))
  have ha_eq : (aZ.toNat : ℤ) = aZ := Int.toNat_of_nonneg ha
  have hb_eq : ((bS * -A j i).toNat : ℤ) = bS * -A j i := Int.toNat_of_nonneg hbZ
  have hval : (R.weylCoxeterHom hdiag hoff hzero v : Dual K H ≃ₗ[K] Dual K H) =
      (if Even m then 1 else R.simpleReflection hd j) *
        (R.simpleReflection hd i * R.simpleReflection hd j) ^ (m / 2) := by
    have hprod : ((CoxeterSystem.alternatingWord i j m).map (R.weylSimple hd)).prod =
        R.weylCoxeterHom hdiag hoff hzero v := by
      rw [← R.weylCoxeterHom_wordProd hdiag hoff hzero, hv_eq]
    rw [← (R.prod_map_weylSimple_eq_iff hd _ _).mp hprod,
      TauCeti.prod_map_alternatingWord (R.simpleReflection hd) i j m]
  refine ⟨aZ.toNat, (bS * -A j i).toNat, ?_⟩
  rw [hval, R.alternating_simpleReflection_apply_root hdiag i j m,
    Int.cast_smul_eq_zsmul K aZ (R.root i), Int.cast_smul_eq_zsmul K (bS * -A j i) (R.root j),
    ← natCast_zsmul, ← natCast_zsmul, ha_eq, hb_eq]

/-- Key induction of Kac's Lemma 3.11: if `i` is not a right descent of `w` in the presented
Coxeter group, then `w(αᵢ) ∈ Q₊` (over any field `K`!). -/
private theorem apply_root_mem_posRootCone_of_not_isRightDescent
    (hdiag : ∀ i, A i i = 2) (hoff : ∀ i j, i ≠ j → A i j ≤ 0)
    (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) {w : (cartanCoxeterMatrix A).Group} {i : I}
    (hwi : ¬(cartanCoxeterMatrix A).toCoxeterSystem.IsRightDescent w i) :
    ((R.weylCoxeterHom hdiag hoff hzero w : Dual K H ≃ₗ[K] Dual K H) (R.root i)) ∈
      R.posRootCone := by
  let cs₀ := (cartanCoxeterMatrix A).toCoxeterSystem
  induction hlen : cs₀.length w using Nat.strong_induction_on generalizing w i with
  | _ n ih =>
    rcases eq_or_ne w 1 with rfl | hw1
    · simpa using R.root_mem_posRootCone i
    obtain ⟨j, hwj⟩ := cs₀.exists_rightDescent_of_ne_one hw1
    have hij : i ≠ j := fun h ↦ hwi (h ▸ hwj)
    obtain ⟨p, ⟨hu, hv, hmul⟩, -⟩ := cs₀.existsUnique_isMinimalCosetRep_mul {i, j} w
    rcases p with ⟨u, v⟩
    dsimp only at hu hv hmul; subst hmul
    have hv1 : v ≠ 1 := fun hv0 ↦ by
      rw [hv0, mul_one] at hwj
      exact cs₀.isMinimalCosetRep_iff.mp hu j (by simp) hwj
    have hv_pos : 0 < cs₀.length v := Nat.pos_of_ne_zero (mt cs₀.length_eq_zero_iff.mp hv1)
    have hadd := cs₀.length_mul_of_isMinimalCosetRep hu hv
    have hvi : ¬cs₀.IsRightDescent v i := fun hd ↦ hwi <| by
      rw [CoxeterSystem.IsRightDescent, mul_assoc,
        cs₀.length_mul_of_isMinimalCosetRep hu
          (mul_mem hv (cs₀.simple_mem_parabolic (by simp))), hadd]
      exact Nat.add_lt_add_left hd _
    obtain ⟨a, b, hab⟩ :=
      R.exists_apply_root_eq_nsmul_of_mem_parabolic_pair hdiag hoff hzero hij hv hvi
    have hu_cone {k : I} (hk : k ∈ ({i, j} : Set I)) :
        ((R.weylCoxeterHom hdiag hoff hzero u : Dual K H ≃ₗ[K] Dual K H) (R.root k)) ∈
          R.posRootCone :=
      ih (cs₀.length u) (by omega) (cs₀.isMinimalCosetRep_iff.mp hu k hk) rfl
    rw [map_mul, Subgroup.coe_mul, mul_apply_eq_comp, hab, map_add, map_nsmul, map_nsmul]
    exact add_mem (Submodule.smul_mem _ a (hu_cone (by simp)))
      (Submodule.smul_mem _ b (hu_cone (by simp)))

end BraidRelations

/-! ### Kac's Lemma 3.11 and the Coxeter presentation in characteristic zero -/

section CoxeterPresentation

variable {I K H : Type*} [DecidableEq I] [Field K] [CharZero K] [AddCommGroup H] [Module K H]
  {A : Matrix I I ℤ} (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)

private theorem isRightDescent_toCoxeterSystem_iff
    (hdiag : ∀ i, A i i = 2) (hoff : ∀ i j, i ≠ j → A i j ≤ 0)
    (hzero : ∀ i j, A i j = 0 ↔ A j i = 0)
    (w : (cartanCoxeterMatrix A).Group) (i : I) :
    (cartanCoxeterMatrix A).toCoxeterSystem.IsRightDescent w i ↔
      -((R.weylCoxeterHom hdiag hoff hzero w : Dual K H ≃ₗ[K] Dual K H) (R.root i)) ∈
        R.posRootCone := by
  let cs₀ := (cartanCoxeterMatrix A).toCoxeterSystem
  have hne : ((R.weylCoxeterHom hdiag hoff hzero w :
      Dual K H ≃ₗ[K] Dual K H) (R.root i)) ≠ 0 :=
    (map_ne_zero_iff _ (LinearEquiv.injective _)).mpr (R.root_linearIndependent.ne_zero i)
  refine ⟨fun hd ↦ ?_, fun hneg ↦ ?_⟩
  · have hnd : ¬cs₀.IsRightDescent (w * cs₀.simple i) i :=
      cs₀.isRightDescent_iff_not_isRightDescent_mul.mp hd
    have hpos := R.apply_root_mem_posRootCone_of_not_isRightDescent hdiag hoff hzero hnd
    have hcs : cs₀.simple i = (cartanCoxeterMatrix A).simple i := rfl
    rw [hcs, map_mul, R.weylCoxeterHom_simple, Subgroup.coe_mul, mul_apply_eq_comp,
      coe_weylSimple, simpleReflection_root_self, map_neg] at hpos
    exact hpos
  · by_contra hnd
    have hpos := R.apply_root_mem_posRootCone_of_not_isRightDescent hdiag hoff hzero hnd
    exact hne (R.isPointed_posRootCone _ hpos hneg)

/-- `weylCoxeterHom` is injective over any field of characteristic zero. -/
theorem weylCoxeterHom_injective (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) :
    Function.Injective (R.weylCoxeterHom hdiag hoff hzero) := by
  refine (injective_iff_map_eq_one _).mpr fun w hw ↦ ?_
  by_contra hw1
  obtain ⟨i, hd⟩ := (cartanCoxeterMatrix A).toCoxeterSystem.exists_rightDescent_of_ne_one hw1
  have hneg := (R.isRightDescent_toCoxeterSystem_iff hdiag hoff hzero w i).mp hd
  rw [hw, Subgroup.coe_one, one_apply_eq_self] at hneg
  exact R.root_linearIndependent.ne_zero i
    (R.isPointed_posRootCone _ (R.root_mem_posRootCone i) hneg)

/-- **Kac's Proposition 3.13 (group isomorphism form).** The presented Coxeter group of
`cartanCoxeterMatrix A` maps isomorphically onto the Weyl group `R.weylGroup _`. -/
noncomputable def weylCoxeterEquiv (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) :
    (cartanCoxeterMatrix A).Group ≃* R.weylGroup (diag_map_intCast hdiag) :=
  MulEquiv.ofBijective (R.weylCoxeterHom hdiag hoff hzero)
    ⟨R.weylCoxeterHom_injective hdiag hoff hzero, R.weylCoxeterHom_surjective hdiag hoff hzero⟩

@[simp]
theorem weylCoxeterEquiv_simple (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) (i : I) :
    R.weylCoxeterEquiv hdiag hoff hzero ((cartanCoxeterMatrix A).simple i) =
      R.weylSimple (diag_map_intCast hdiag) i :=
  R.weylCoxeterHom_simple hdiag hoff hzero i

@[simp]
theorem weylCoxeterEquiv_symm_weylSimple (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) (i : I) :
    (R.weylCoxeterEquiv hdiag hoff hzero).symm (R.weylSimple (diag_map_intCast hdiag) i) =
      (cartanCoxeterMatrix A).simple i :=
  (R.weylCoxeterEquiv hdiag hoff hzero).symm_apply_eq.mpr
    (R.weylCoxeterEquiv_simple hdiag hoff hzero i).symm

/-- **Kac's Proposition 3.13 (`CoxeterSystem` form).** The Weyl group of a realization of a
generalized Cartan matrix over a characteristic-zero field forms a `CoxeterSystem` with Coxeter
matrix `cartanCoxeterMatrix A` and simple reflections `R.weylSimple _`. -/
noncomputable def weylCoxeterSystem (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) :
    CoxeterSystem (cartanCoxeterMatrix A) (R.weylGroup (diag_map_intCast hdiag)) :=
  (cartanCoxeterMatrix A).toCoxeterSystem.map (R.weylCoxeterEquiv hdiag hoff hzero)

@[simp]
theorem weylCoxeterSystem_simple (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) (i : I) :
    (R.weylCoxeterSystem hdiag hoff hzero).simple i =
      R.weylSimple (diag_map_intCast hdiag) i :=
  R.weylCoxeterEquiv_simple hdiag hoff hzero i

@[simp]
theorem weylCoxeterSystem_wordProd (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) (l : List I) :
    (R.weylCoxeterSystem hdiag hoff hzero).wordProd l =
      (l.map (R.weylSimple (diag_map_intCast hdiag))).prod := by
  rw [CoxeterSystem.wordProd]
  exact congrArg List.prod (congrArg (fun f ↦ l.map f)
    (funext (R.weylCoxeterSystem_simple hdiag hoff hzero)))

/-- The Coxeter length of `R.weylCoxeterSystem` agrees with the generator word length
`R.weylLength`. -/
@[simp]
theorem weylCoxeterSystem_length (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0)
    (w : R.weylGroup (diag_map_intCast hdiag)) :
    (R.weylCoxeterSystem hdiag hoff hzero).length w =
      R.weylLength (diag_map_intCast hdiag) w := by
  let cs := R.weylCoxeterSystem hdiag hoff hzero
  refine le_antisymm ?_ ?_
  · obtain ⟨l, hl, hprod⟩ := R.exists_length_eq_weylLength (diag_map_intCast hdiag) w
    rw [← hl, ← hprod, ← R.weylCoxeterSystem_wordProd hdiag hoff hzero l]
    exact cs.length_wordProd_le l
  · obtain ⟨ω, hred, rfl⟩ := cs.exists_isReduced w
    rw [hred.eq]
    exact R.weylLength_le_of_prod_eq (diag_map_intCast hdiag)
      (R.weylCoxeterSystem_wordProd hdiag hoff hzero ω).symm

private theorem length_weylCoxeterEquiv (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0)
    (x : (cartanCoxeterMatrix A).Group) :
    (R.weylCoxeterSystem hdiag hoff hzero).length (R.weylCoxeterEquiv hdiag hoff hzero x) =
      (cartanCoxeterMatrix A).toCoxeterSystem.length x := by
  let cs₀ := (cartanCoxeterMatrix A).toCoxeterSystem
  let cs := R.weylCoxeterSystem hdiag hoff hzero
  let e := R.weylCoxeterEquiv hdiag hoff hzero
  have hmap (ω : List I) : e (cs₀.wordProd ω) = cs.wordProd ω :=
    (R.weylCoxeterHom_wordProd hdiag hoff hzero ω).trans
      (R.weylCoxeterSystem_wordProd hdiag hoff hzero ω).symm
  refine le_antisymm ?_ ?_
  · obtain ⟨ω, hred, rfl⟩ := cs₀.exists_isReduced x
    rw [hred.eq, hmap]
    exact cs.length_wordProd_le ω
  · obtain ⟨ω, hred, hω⟩ := cs.exists_isReduced (e x)
    have hcs : cs.length (e x) = ω.length := hω ▸ hred.eq
    rw [hcs, ← e.injective ((hmap ω).trans hω.symm)]
    exact cs₀.length_wordProd_le ω

/-- **Kac's Lemma 3.11 (right-descent form).** Index `i` is a right descent of `w` if and only if
`-w(αᵢ) ∈ Q₊`. -/
theorem isRightDescent_weylCoxeterSystem_iff (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0)
    (w : R.weylGroup (diag_map_intCast hdiag)) (i : I) :
    (R.weylCoxeterSystem hdiag hoff hzero).IsRightDescent w i ↔
      -((w : Dual K H ≃ₗ[K] Dual K H) (R.root i)) ∈ R.posRootCone := by
  let e := R.weylCoxeterEquiv hdiag hoff hzero
  obtain ⟨u, rfl⟩ : ∃ u, e u = w := ⟨e.symm w, e.apply_symm_apply w⟩
  have hcs : (cartanCoxeterMatrix A).toCoxeterSystem.simple i =
      (cartanCoxeterMatrix A).simple i := rfl
  have hdesc : (R.weylCoxeterSystem hdiag hoff hzero).IsRightDescent (e u) i ↔
      (cartanCoxeterMatrix A).toCoxeterSystem.IsRightDescent u i := by
    rw [CoxeterSystem.IsRightDescent, CoxeterSystem.IsRightDescent, hcs,
      R.weylCoxeterSystem_simple, ← R.weylCoxeterEquiv_simple hdiag hoff hzero, ← map_mul,
      R.length_weylCoxeterEquiv, R.length_weylCoxeterEquiv]
  exact hdesc.trans (R.isRightDescent_toCoxeterSystem_iff hdiag hoff hzero u i)

/-- **Kac's Lemma 3.11 (right-ascent form).** Index `i` is not a right descent of `w` if and only
if `w(αᵢ) ∈ Q₊`. -/
theorem not_isRightDescent_weylCoxeterSystem_iff (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0)
    (w : R.weylGroup (diag_map_intCast hdiag)) (i : I) :
    ¬(R.weylCoxeterSystem hdiag hoff hzero).IsRightDescent w i ↔
      (w : Dual K H ≃ₗ[K] Dual K H) (R.root i) ∈ R.posRootCone := by
  rw [(R.weylCoxeterSystem hdiag hoff hzero).isRightDescent_iff_not_isRightDescent_mul,
    not_not, R.isRightDescent_weylCoxeterSystem_iff, R.weylCoxeterSystem_simple]
  simp [mul_apply_eq_comp]

/-- **The exact order of `sᵢ * sⱼ` in the Weyl group is `cartanCoxeterMatrix A i j`** (`0` meaning
infinite order when `3 < A i j * A j i` for `i ≠ j`). -/
@[simp]
theorem orderOf_weylSimple_mul_weylSimple (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) (i j : I) :
    orderOf (R.weylSimple (diag_map_intCast hdiag) i *
        R.weylSimple (diag_map_intCast hdiag) j) = cartanCoxeterMatrix A i j := by
  simpa using (R.weylCoxeterSystem hdiag hoff hzero).orderOf_simple_mul_simple i j

end CoxeterPresentation

/-! ### `[DecidableEq I]`-free consequences and realization independence -/

section Consequences

variable {I K H : Type*} [Field K] [CharZero K] [AddCommGroup H] [Module K H]
  {A : Matrix I I ℤ} (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)

/-- **Kac's Lemma 3.11 (`weylLength` descent form)**: `ℓ(w sᵢ) < ℓ(w) ↔ -w(αᵢ) ∈ Q₊`. -/
theorem weylLength_mul_weylSimple_lt_iff (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0)
    (w : R.weylGroup (diag_map_intCast hdiag)) (i : I) :
    R.weylLength (diag_map_intCast hdiag) (w * R.weylSimple (diag_map_intCast hdiag) i) <
        R.weylLength (diag_map_intCast hdiag) w ↔
      -((w : Dual K H ≃ₗ[K] Dual K H) (R.root i)) ∈ R.posRootCone := by
  classical
  rw [← R.weylCoxeterSystem_length hdiag hoff hzero, ← R.weylCoxeterSystem_length hdiag hoff hzero,
    ← R.weylCoxeterSystem_simple hdiag hoff hzero]
  exact R.isRightDescent_weylCoxeterSystem_iff hdiag hoff hzero w i

/-- **Kac's Lemma 3.11 (`weylLength` ascent form)**: `ℓ(w sᵢ) = ℓ(w) + 1 ↔ w(αᵢ) ∈ Q₊`. -/
theorem weylLength_mul_weylSimple_eq_add_one_iff (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0)
    (w : R.weylGroup (diag_map_intCast hdiag)) (i : I) :
    R.weylLength (diag_map_intCast hdiag) (w * R.weylSimple (diag_map_intCast hdiag) i) =
        R.weylLength (diag_map_intCast hdiag) w + 1 ↔
      (w : Dual K H ≃ₗ[K] Dual K H) (R.root i) ∈ R.posRootCone := by
  classical
  rw [← R.weylCoxeterSystem_length hdiag hoff hzero, ← R.weylCoxeterSystem_length hdiag hoff hzero,
    ← R.weylCoxeterSystem_simple hdiag hoff hzero,
    ← (R.weylCoxeterSystem hdiag hoff hzero).not_isRightDescent_iff]
  exact R.not_isRightDescent_weylCoxeterSystem_iff hdiag hoff hzero w i

/-- **Sign dichotomy of `W`-translates of simple roots**: for every `w ∈ W` and `i : I`, either
`w(αᵢ) ∈ Q₊` or `-w(αᵢ) ∈ Q₊`. -/
theorem apply_root_mem_posRootCone_or_neg_mem_posRootCone (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0)
    (w : R.weylGroup (diag_map_intCast hdiag)) (i : I) :
    (w : Dual K H ≃ₗ[K] Dual K H) (R.root i) ∈ R.posRootCone ∨
      -((w : Dual K H ≃ₗ[K] Dual K H) (R.root i)) ∈ R.posRootCone := by
  classical
  by_cases hd : (R.weylCoxeterSystem hdiag hoff hzero).IsRightDescent w i
  · exact Or.inr ((R.isRightDescent_weylCoxeterSystem_iff hdiag hoff hzero w i).mp hd)
  · exact Or.inl ((R.not_isRightDescent_weylCoxeterSystem_iff hdiag hoff hzero w i).mp hd)

/-- **Distinct indices determine distinct simple reflections in the Weyl group.** -/
theorem weylSimple_injective (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) :
    Function.Injective (R.weylSimple (diag_map_intCast hdiag)) := by
  classical
  have h := (R.weylCoxeterSystem hdiag hoff hzero).simple_injective
  rwa [funext (R.weylCoxeterSystem_simple hdiag hoff hzero)] at h

/-- **The action of the Weyl group on the root lattice `Q` is faithful**, even when `A` is
singular or `H` has central directions. -/
theorem rootLatticeAction_injective (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) :
    Function.Injective (R.rootLatticeAction (diag_map_intCast hdiag)) := by
  classical
  refine (injective_iff_map_eq_one _).mpr fun w hw ↦ ?_
  by_contra hw1
  obtain ⟨i, hd⟩ :=
    (R.weylCoxeterSystem hdiag hoff hzero).exists_rightDescent_of_ne_one hw1
  have hneg := (R.isRightDescent_weylCoxeterSystem_iff hdiag hoff hzero w i).mp hd
  have hfix : (w : Dual K H ≃ₗ[K] Dual K H) (R.root i) = R.root i := by
    have hi := congrArg Subtype.val congr($(hw) ⟨R.root i, R.root_mem_rootLattice i⟩)
    simpa using hi
  rw [hfix] at hneg
  exact R.root_linearIndependent.ne_zero i
    (R.isPointed_posRootCone _ (R.root_mem_posRootCone i) hneg)

/-- **Realization independence of the Weyl group.** Any two realizations of the same generalized
Cartan matrix `A` over fields of characteristic zero (even of different dimensions or over
different scalar fields) have canonically isomorphic Weyl groups matching simple reflections
index-by-index. -/
noncomputable def weylGroupEquiv {K' H' : Type*} [Field K'] [CharZero K'] [AddCommGroup H']
    [Module K' H'] (R' : CartanRealization (A.map (Int.cast : ℤ → K')) H')
    (hdiag : ∀ i, A i i = 2) (hoff : ∀ i j, i ≠ j → A i j ≤ 0)
    (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) :
    R.weylGroup (diag_map_intCast hdiag) ≃* R'.weylGroup (diag_map_intCast hdiag) := by
  classical
  exact (R.weylCoxeterEquiv hdiag hoff hzero).symm.trans (R'.weylCoxeterEquiv hdiag hoff hzero)

@[simp]
theorem weylGroupEquiv_weylSimple {K' H' : Type*} [Field K'] [CharZero K'] [AddCommGroup H']
    [Module K' H'] (R' : CartanRealization (A.map (Int.cast : ℤ → K')) H')
    (hdiag : ∀ i, A i i = 2) (hoff : ∀ i j, i ≠ j → A i j ≤ 0)
    (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) (i : I) :
    R.weylGroupEquiv R' hdiag hoff hzero (R.weylSimple (diag_map_intCast hdiag) i) =
      R'.weylSimple (diag_map_intCast hdiag) i := by
  simp [weylGroupEquiv]

@[simp]
theorem weylLength_weylGroupEquiv {K' H' : Type*} [Field K'] [CharZero K'] [AddCommGroup H']
    [Module K' H'] (R' : CartanRealization (A.map (Int.cast : ℤ → K')) H')
    (hdiag : ∀ i, A i i = 2) (hoff : ∀ i j, i ≠ j → A i j ≤ 0)
    (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) (w : R.weylGroup (diag_map_intCast hdiag)) :
    R'.weylLength (diag_map_intCast hdiag) (R.weylGroupEquiv R' hdiag hoff hzero w) =
      R.weylLength (diag_map_intCast hdiag) w :=
  R.weylLength_equiv (diag_map_intCast hdiag) (diag_map_intCast hdiag)
    (R.weylGroupEquiv R' hdiag hoff hzero) (R.weylGroupEquiv_weylSimple R' hdiag hoff hzero) w

end Consequences

/-- When the index type, scalar field, and ambient space lie in a common universe, the Weyl group
carries an `IsCoxeterGroup` proof. -/
theorem isCoxeterGroup_weylGroup.{u} {I K H : Type u} [Field K] [CharZero K]
    [AddCommGroup H] [Module K H] {A : Matrix I I ℤ}
    (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)
    (hdiag : ∀ i, A i i = 2) (hoff : ∀ i j, i ≠ j → A i j ≤ 0)
    (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) :
    IsCoxeterGroup (R.weylGroup (diag_map_intCast hdiag)) := by
  classical
  exact ⟨I, cartanCoxeterMatrix A, ⟨R.weylCoxeterSystem hdiag hoff hzero⟩⟩

/-! ### Concrete checks across types `A₁`, `A₁⁽¹⁾`, `B₂`, and empty rank -/

section Examples

/-- Type `A₁`: the Weyl group is generated by a single involution `s₀`, so every element is `1`
or `s₀`, and `s₀` has order `2`. -/
example {K H : Type*} [Field K] [CharZero K] [AddCommGroup H] [Module K H]
    (R : CartanRealization ((CartanMatrix.A 1).map (Int.cast : ℤ → K)) H) :
    let hd := diag_map_intCast (K := K) (fun i ↦ by rw [CartanMatrix.A_one]; fin_cases i; rfl)
    orderOf (R.weylSimple hd 0) = 2 ∧
      ∀ w : R.weylGroup hd, w = 1 ∨ w = R.weylSimple hd 0 := by
  intro hd
  refine ⟨orderOf_eq_prime (R.weylSimple_mul_self hd 0 ▸ sq (R.weylSimple hd 0))
      (R.weylSimple_ne_one hd 0), ?_⟩
  refine R.weylGroup_induction hd (P := fun w ↦ w = 1 ∨ w = R.weylSimple hd 0)
    (Or.inl rfl) (fun i ↦ Or.inr (congrArg (R.weylSimple hd) (Subsingleton.elim i 0))) ?_
  rintro u v (rfl | rfl) (rfl | rfl) <;> simp

/-- Affine type `A₁⁽¹⁾`: the matrix `!![2, -2; -2, 2]` has Coxeter entry `0` (`∞`) off the
diagonal, so `s₀ * s₁` has infinite order (`orderOf = 0`) in every characteristic-zero
realization. -/
example {K H : Type*} [Field K] [CharZero K] [AddCommGroup H] [Module K H]
    (R : CartanRealization
      ((!![2, -2; -2, 2] : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → K)) H) :
    let hdiag : ∀ i : Fin 2, (!![2, -2; -2, 2] : Matrix (Fin 2) (Fin 2) ℤ) i i = 2 := by decide
    orderOf (R.weylSimple (diag_map_intCast hdiag) 0 *
        R.weylSimple (diag_map_intCast hdiag) 1) = 0 := by
  intro hdiag
  have hoff : ∀ i j : Fin 2, i ≠ j →
      (!![2, -2; -2, 2] : Matrix (Fin 2) (Fin 2) ℤ) i j ≤ 0 := by
    intro i j; fin_cases i <;> fin_cases j <;> decide
  have hzero : ∀ i j : Fin 2,
      (!![2, -2; -2, 2] : Matrix (Fin 2) (Fin 2) ℤ) i j = 0 ↔
        (!![2, -2; -2, 2] : Matrix (Fin 2) (Fin 2) ℤ) j i = 0 := by
    intro i j; fin_cases i <;> fin_cases j <;> decide
  rw [R.orderOf_weylSimple_mul_weylSimple hdiag hoff hzero 0 1]
  exact cartanCoxeterMatrix_of_ne_of_lt (by decide) (by decide)

/-- Non-simply-laced finite type `B₂`: `s₀ * s₁` has order `4`. -/
example {K H : Type*} [Field K] [CharZero K] [AddCommGroup H] [Module K H]
    (R : CartanRealization ((CartanMatrix.B 2).map (Int.cast : ℤ → K)) H) :
    orderOf (R.weylSimple (diag_map_intCast (CartanMatrix.B_diag 2)) 0 *
        R.weylSimple (diag_map_intCast (CartanMatrix.B_diag 2)) 1) = 4 := by
  have hzero : ∀ i j : Fin 2, CartanMatrix.B 2 i j = 0 ↔ CartanMatrix.B 2 j i = 0 := by
    rw [CartanMatrix.B_two]
    intro i j; fin_cases i <;> fin_cases j <;> decide
  rw [R.orderOf_weylSimple_mul_weylSimple (CartanMatrix.B_diag 2)
    (CartanMatrix.B_off_diag_nonpos 2) hzero 0 1,
    cartanCoxeterMatrix_of_ne_of_le (by decide) (by rw [CartanMatrix.B_two]; decide),
    CartanMatrix.B_two]
  norm_num

/-- Empty index set: the Weyl group is trivial and every element has word length `0`. -/
example {K H : Type*} [Field K] [AddCommGroup H] [Module K H]
    (R : CartanRealization ((0 : Matrix (Fin 0) (Fin 0) ℤ).map (Int.cast : ℤ → K)) H) :
    let hdiag : ∀ i : Fin 0, (0 : Matrix (Fin 0) (Fin 0) ℤ) i i = 2 := isEmptyElim
    ∀ w : R.weylGroup (diag_map_intCast hdiag),
      R.weylLength (diag_map_intCast hdiag) w = 0 := by
  intro hdiag w
  simp [Subsingleton.elim w 1]

end Examples

end CartanRealization

end TauCeti
