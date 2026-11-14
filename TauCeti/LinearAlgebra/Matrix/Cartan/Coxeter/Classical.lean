/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import TauCeti.Data.List.OneDegenerateOrder
public import TauCeti.LinearAlgebra.Matrix.Cartan.Coxeter.Basic
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import TauCeti.LinearAlgebra.Matrix.Charpoly.Cyclotomic
import TauCeti.LinearAlgebra.Matrix.Triangular

/-!
# Coxeter elements of the classical Cartan matrices

This file computes the order and the characteristic polynomial of the standard Coxeter element
`c = s₁ ⋯ sₙ` (`Matrix.coxeterElement`) of each classical Cartan matrix `CartanMatrix.A n`,
`CartanMatrix.B n`, `CartanMatrix.C n`, and `CartanMatrix.D n`, and proves that the Bourbaki node
order `List.finRange n` is a one-degenerate order (`List.IsOneDegenerateOrder`) of the Dynkin
diagram in every rank:

| type | rank bound | Coxeter number `h` | characteristic polynomial |
|---|---|---|---|
| `Aₙ` | all `n` | `n + 1` | `∑_{k=0}^n X^k` |
| `Bₙ` | `1 ≤ n` | `2 n` | `X^n + 1` |
| `Cₙ` | `1 ≤ n` | `2 n` | `X^n + 1` |
| `Dₙ` | `2 ≤ n` | `2 (n - 1)` | `(X^{n-1} + 1)(X + 1)` |

Each classical family is reduced to a cyclic or signed-cyclic permutation model by an explicit
integral intertwining matrix:

* **Type `Aₙ`**: embedding the simple roots as the columns `eⱼ - eⱼ₊₁` of an `(n + 1) × n` integer
  matrix `P_A` with an explicit left inverse `L_A` intertwines `coxA n` with the `(n + 1)`-cycle
  `e₀ ↦ e₁ ↦ ⋯ ↦ eₙ ↦ e₀`. Both `1 + X + ⋯ + X^n` and the characteristic polynomial are monic of
  degree `n` and annihilate `coxA n`, and `e₀` is a cyclic vector, forcing them to agree.
* **Type `Bₙ`**: the lower-unitriangular matrix `P_B` with columns `e₀ - e₁, …, eₙ₋₂ - eₙ₋₁, eₙ₋₁`
  conjugates `coxB n` over `ℤ` to the signed `n`-cycle `e₀ ↦ e₁ ↦ ⋯ ↦ eₙ₋₁ ↦ -e₀`, whose `n`-th
  power is `-1` and for which `e₀` is again cyclic.
* **Type `Cₙ`**: the diagonal matrix `diag(1, …, 1, 2)` intertwines `coxC n` with `coxB n` over `ℤ`
  and is invertible over `ℚ`, so `coxC n` has the same characteristic polynomial and order as
  `coxB n`.
* **Type `Dₙ`**: the integer matrix `P_D` with columns `e₀ - e₁, …, eₙ₋₂ - eₙ₋₁, eₙ₋₂ + eₙ₋₁` has
  determinant `2` and intertwines `coxD n` with the block-diagonal matrix pairing a signed
  `(n - 1)`-cycle on `e₀, …, eₙ₋₂` with `-1` on `eₙ₋₁`.

## Main definitions

* `TauCeti.Coxeter.coxA`, `TauCeti.Coxeter.coxB`, `TauCeti.Coxeter.coxC`, `TauCeti.Coxeter.coxD`:
  the standard Coxeter elements of types `Aₙ`, `Bₙ`, `Cₙ`, `Dₙ`.

## Main results

* `TauCeti.Coxeter.isOneDegenerateOrder_A` (and `B`, `C`, `D`): `List.finRange n` is a
  one-degenerate order of the Dynkin diagram.
* `TauCeti.Coxeter.orderOf_coxA` (and `coxB`, `coxC`, `coxD`): the order of the Coxeter element.
* `TauCeti.Coxeter.charpoly_coxA` (and `coxB`, `coxC`, `coxD`): its characteristic polynomial.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. V, §6, and Plates I--IV.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge University Press (1990),
  §§ 3.16--3.20.
-/

public section

open Matrix Polynomial

namespace TauCeti.Coxeter

/-! ### Definitions of the classical Coxeter matrices -/

/-- The Coxeter element of type `Aₙ` in the Bourbaki numbering. -/
@[expose] def coxA (n : ℕ) : Matrix (Fin n) (Fin n) ℤ := coxeterElement (CartanMatrix.A n)

/-- The Coxeter element of type `Bₙ` in the Bourbaki numbering. -/
@[expose] def coxB (n : ℕ) : Matrix (Fin n) (Fin n) ℤ := coxeterElement (CartanMatrix.B n)

/-- The Coxeter element of type `Cₙ` in the Bourbaki numbering. -/
@[expose] def coxC (n : ℕ) : Matrix (Fin n) (Fin n) ℤ := coxeterElement (CartanMatrix.C n)

/-- The Coxeter element of type `Dₙ` in the Bourbaki numbering. -/
@[expose] def coxD (n : ℕ) : Matrix (Fin n) (Fin n) ℤ := coxeterElement (CartanMatrix.D n)

/-! ### One-degenerate orders of the classical diagrams -/

private lemma lt_of_mem_prefix_finRange {n : ℕ} {S₁ S₂ : List (Fin n)} {z x : Fin n}
    (hS : List.finRange n = S₁ ++ z :: S₂) (hx : x ∈ S₁) : x.val < z.val := by
  have hpw : (List.finRange n).Pairwise (fun a b => a.val < b.val) :=
    List.pairwise_iff_getElem.2 fun i j hi hj hij => by simpa using hij
  rw [hS, List.pairwise_append] at hpw
  exact hpw.2.2 x hx z (List.mem_cons_self ..)

/-- The Bourbaki numbering `List.finRange n` is a one-degenerate order of the Dynkin diagram of
type `Aₙ`. -/
theorem isOneDegenerateOrder_A (n : ℕ) :
    List.IsOneDegenerateOrder (fun i j : Fin n => CartanMatrix.A n i j ≠ 0) (List.finRange n) := by
  rw [List.isOneDegenerateOrder_iff]
  intro S₁ z S₂ hS x hx y hy hzx hzy
  have hxz := lt_of_mem_prefix_finRange hS hx
  have hyz := lt_of_mem_prefix_finRange hS hy
  simp only [CartanMatrix.A, Matrix.of_apply] at hzx hzy
  ext
  split_ifs at hzx hzy <;> omega

/-- The Bourbaki numbering `List.finRange n` is a one-degenerate order of the Dynkin diagram of
type `Bₙ`. -/
theorem isOneDegenerateOrder_B (n : ℕ) :
    List.IsOneDegenerateOrder (fun i j : Fin n => CartanMatrix.B n i j ≠ 0) (List.finRange n) := by
  rw [List.isOneDegenerateOrder_iff]
  intro S₁ z S₂ hS x hx y hy hzx hzy
  have hxz := lt_of_mem_prefix_finRange hS hx
  have hyz := lt_of_mem_prefix_finRange hS hy
  simp only [CartanMatrix.B, Matrix.of_apply] at hzx hzy
  ext
  split_ifs at hzx hzy <;> omega

/-- The Bourbaki numbering `List.finRange n` is a one-degenerate order of the Dynkin diagram of
type `Cₙ`. -/
theorem isOneDegenerateOrder_C (n : ℕ) :
    List.IsOneDegenerateOrder (fun i j : Fin n => CartanMatrix.C n i j ≠ 0) (List.finRange n) := by
  rw [List.isOneDegenerateOrder_iff]
  intro S₁ z S₂ hS x hx y hy hzx hzy
  have hxz := lt_of_mem_prefix_finRange hS hx
  have hyz := lt_of_mem_prefix_finRange hS hy
  simp only [CartanMatrix.C, Matrix.of_apply] at hzx hzy
  ext
  split_ifs at hzx hzy <;> omega

/-- The Bourbaki numbering `List.finRange n` is a one-degenerate order of the Dynkin diagram of
type `Dₙ`: every node `z` is adjacent to at most one node of smaller index (`z - 1` on the stem
and on the first prong, and the branch node `n - 3` on the second prong `n - 1`). -/
theorem isOneDegenerateOrder_D (n : ℕ) :
    List.IsOneDegenerateOrder (fun i j : Fin n => CartanMatrix.D n i j ≠ 0) (List.finRange n) := by
  rw [List.isOneDegenerateOrder_iff]
  intro S₁ z S₂ hS x hx y hy hzx hzy
  have hxz := lt_of_mem_prefix_finRange hS hx
  have hyz := lt_of_mem_prefix_finRange hS hy
  simp only [CartanMatrix.D, Matrix.of_apply] at hzx hzy
  ext
  split_ifs at hzx hzy <;> omega

/-! ### Shared intertwining, cyclic-vector, and permutation machinery -/

/-- If `P` intertwines each simple reflection of `A` with `S i`, then `P` intertwines the product
along any list of indices. -/
private lemma mul_prod_map_reflMatrix {κ : Type*} [Fintype κ] [DecidableEq κ] {n : ℕ}
    (P : Matrix κ (Fin n) ℤ) (A : Matrix (Fin n) (Fin n) ℤ) (S : Fin n → Matrix κ κ ℤ)
    (hS : ∀ i, P * reflMatrix A i = S i * P) (l : List (Fin n)) :
    P * (l.map (reflMatrix A)).prod = (l.map S).prod * P := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [← Matrix.mul_assoc, hS i, Matrix.mul_assoc, ih, Matrix.mul_assoc]

/-- Specialisation of `mul_prod_map_reflMatrix` to `coxeterElement A`. -/
private lemma mul_coxeterElement {κ : Type*} [Fintype κ] [DecidableEq κ] {n : ℕ}
    (P : Matrix κ (Fin n) ℤ) (A : Matrix (Fin n) (Fin n) ℤ) (S : Fin n → Matrix κ κ ℤ)
    (hS : ∀ i, P * reflMatrix A i = S i * P) :
    P * coxeterElement A = ((List.finRange n).map S).prod * P :=
  mul_prod_map_reflMatrix P A S hS (List.finRange n)

/-- If `P` intertwines `X` with `Y`, it intertwines every natural power `X ^ m` with `Y ^ m`. -/
private lemma mul_pow_of_intertwine {κ₁ κ₂ : Type*} [Fintype κ₁] [DecidableEq κ₁]
    [Fintype κ₂] [DecidableEq κ₂] {P : Matrix κ₁ κ₂ ℤ} {X : Matrix κ₂ κ₂ ℤ}
    {Y : Matrix κ₁ κ₁ ℤ} (h : P * X = Y * P) (m : ℕ) :
    P * X ^ m = Y ^ m * P := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ← pow_succ]

/-- Right-multiplying `P` by `reflMatrix A i` subtracts `A j i` times column `i` from column `j`. -/
private lemma mul_reflMatrix_apply {κ : Type*} {n : ℕ}
    (P : Matrix κ (Fin n) ℤ) (A : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) (r : κ) (j : Fin n) :
    (P * reflMatrix A i) r j = P r j - P r i * A j i := by
  rw [Matrix.mul_apply]
  simp only [reflMatrix_apply, mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

/-- If an integer matrix `P` with nonzero determinant intertwines `X` with `Y`, then `X` and `Y`
have the same characteristic polynomial and the same multiplicative order: after casting to `ℚ`,
`P` becomes a unit conjugating `X` to `Y`. -/
private theorem charpoly_and_orderOf_of_intertwine {κ : Type*} [Fintype κ] [DecidableEq κ]
    {P X Y : Matrix κ κ ℤ} (hdet : P.det ≠ 0) (hXY : P * X = Y * P) :
    X.charpoly = Y.charpoly ∧ orderOf X = orderOf Y := by
  let φ : Matrix κ κ ℤ →+* Matrix κ κ ℚ := (Int.castRingHom ℚ).mapMatrix
  have hφ_inj : Function.Injective φ := by
    intro M₁ M₂ h
    exact Matrix.map_injective (Int.castRingHom ℚ).injective_int (by simpa [φ] using h)
  have hu : IsUnit (φ P) := by
    rw [Matrix.isUnit_iff_isUnit_det, ← RingHom.map_det, isUnit_iff_ne_zero]
    exact Int.cast_ne_zero.mpr hdet
  let Pq : Matrix κ κ ℚ := φ P
  let Qq : Matrix κ κ ℚ := ↑hu.unit⁻¹
  have hPQ : Pq * Qq = 1 := hu.mul_val_inv
  have hQP : Qq * Pq = 1 := hu.val_inv_mul
  have hconj : Pq * φ X = φ Y * Pq := by simpa only [Pq, map_mul] using congrArg φ hXY
  have hY : φ Y = Pq * φ X * Qq := by
    rw [hconj, Matrix.mul_assoc, hPQ, Matrix.mul_one]
  refine ⟨?_, ?_⟩
  · apply Matrix.charpoly_eq_of_map_rat
    rw [← Y.charpoly_map (Int.castRingHom ℚ), ← (Int.castRingHom ℚ).mapMatrix_apply,
      ← (Int.castRingHom ℚ).mapMatrix_apply, hY, Matrix.charpoly_mul_comm (Pq * φ X) Qq,
      ← Matrix.mul_assoc, hQP, Matrix.one_mul]
  · rw [← orderOf_injective φ.toMonoidHom hφ_inj X,
      ← orderOf_injective φ.toMonoidHom hφ_inj Y, orderOf_eq_orderOf_iff]
    intro k
    have hk : Pq * φ X ^ k = φ Y ^ k * Pq := SemiconjBy.pow_right hconj k
    constructor <;> intro h1
    · have h1' : φ X ^ k = 1 := h1
      calc
        φ Y ^ k = φ Y ^ k * (Pq * Qq) := by rw [hPQ, Matrix.mul_one]
        _ = (Pq * φ X ^ k) * Qq := by rw [← Matrix.mul_assoc, ← hk]
        _ = 1 := by rw [h1', Matrix.mul_one, hPQ]
    · have h1' : φ Y ^ k = 1 := h1
      calc
        φ X ^ k = (Qq * Pq) * φ X ^ k := by rw [hQP, Matrix.one_mul]
        _ = Qq * (φ Y ^ k * Pq) := by rw [Matrix.mul_assoc, hk]
        _ = 1 := by rw [h1', Matrix.one_mul, hQP]

/-- **Cyclic-vector criterion for the characteristic polynomial.** If `p` is monic of degree `n`,
annihilates `M`, and the first `n` powers of `M` carry `e₀` to the standard basis vectors `eₘ`,
then `M.charpoly = p`: the difference `M.charpoly - p` has degree `< n` and annihilates `M`, so its
evaluation at `e₀` forces every coefficient below `n` to vanish. -/
private theorem charpoly_eq_of_isMonicOfDegree_of_cyclic {n : ℕ} (hn : 0 < n)
    {M : Matrix (Fin n) (Fin n) ℤ} {p : ℤ[X]} (hp : p.IsMonicOfDegree n)
    (hann : aeval M p = 0)
    (hcyc : ∀ m (hm : m < n), M ^ m *ᵥ Pi.single ⟨0, hn⟩ 1 = Pi.single ⟨m, hm⟩ 1) :
    M.charpoly = p := by
  have hdeg_lt : (M.charpoly - p).natDegree < n := by
    refine IsMonicOfDegree.natDegree_sub_lt hn.ne' ⟨?_, M.charpoly_monic⟩ hp
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hann_sub : aeval M (M.charpoly - p) = 0 := by
    rw [map_sub, Matrix.aeval_self_charpoly, hann, sub_zero]
  rw [← sub_eq_zero]
  set q := M.charpoly - p
  ext j
  rw [coeff_zero]
  rcases lt_or_ge j n with hj | hj
  · have hvec : (aeval M q *ᵥ Pi.single ⟨0, hn⟩ 1) ⟨j, hj⟩ = 0 := by
      rw [hann_sub, Matrix.zero_mulVec, Pi.zero_apply]
    rw [aeval_eq_sum_range' hdeg_lt, Matrix.sum_mulVec, Finset.sum_apply] at hvec
    have hsum : (∑ i ∈ Finset.range n,
        ((q.coeff i • M ^ i) *ᵥ Pi.single ⟨0, hn⟩ 1) ⟨j, hj⟩) = q.coeff j := by
      rw [Finset.sum_eq_single_of_mem j (Finset.mem_range.mpr hj)]
      · rw [Matrix.smul_mulVec, Pi.smul_apply, hcyc j hj, Pi.single_eq_same, smul_eq_mul, mul_one]
      · intro i hi hij
        have hi' : i < n := Finset.mem_range.mp hi
        rw [Matrix.smul_mulVec, Pi.smul_apply, hcyc i hi',
          Pi.single_eq_of_ne (Fin.ne_of_val_ne hij.symm), smul_zero]
    exact hsum.symm.trans hvec
  · exact coeff_eq_zero_of_natDegree_lt (hdeg_lt.trans_le hj)

/-- Matrix whose `j`-th column is the `f j`-th standard basis vector, so right-multiplying by it
reindexes columns by `f`. -/
private def colPermMat {κ : Type*} [DecidableEq κ] (f : κ → κ) : Matrix κ κ ℤ :=
  Matrix.of fun r j => if r = f j then 1 else 0

private lemma colPermMat_id {κ : Type*} [DecidableEq κ] :
    colPermMat (id : κ → κ) = 1 := by
  ext i j
  simp [colPermMat, Matrix.one_apply]

private lemma colPermMat_mul {κ : Type*} [Fintype κ] [DecidableEq κ] (f g : κ → κ) :
    colPermMat f * colPermMat g = colPermMat (f ∘ g) := by
  ext i j
  simp [Matrix.mul_apply, colPermMat]

private lemma colPermMat_mulVec_single {κ : Type*} [Fintype κ] [DecidableEq κ]
    (f : κ → κ) (j : κ) :
    colPermMat f *ᵥ Pi.single j 1 = Pi.single (f j) 1 := by
  ext r
  simp [Matrix.mulVec, dotProduct, colPermMat, Pi.single_apply, eq_comm]

private lemma colPermMat_mul_apply_of_involutive {κ₁ κ₂ : Type*} [Fintype κ₁] [DecidableEq κ₁]
    {f : κ₁ → κ₁} (hf : Function.Involutive f) (M : Matrix κ₁ κ₂ ℤ) (r : κ₁) (j : κ₂) :
    (colPermMat f * M) r j = M (f r) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (f r)]
  · simp [colPermMat, hf r]
  · intro k _ hkf
    have hrf : r ≠ f k := fun h => hkf (by rw [h, hf k])
    simp [colPermMat, hrf]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Swap of `k` and `k + 1` in `Fin N`. -/
private def adjSwapFun (N k : ℕ) (hk : k + 1 < N) (j : Fin N) : Fin N :=
  if j.val = k then ⟨k + 1, hk⟩
  else if j.val = k + 1 then ⟨k, by omega⟩
  else j

private lemma val_adjSwapFun (N k : ℕ) (hk : k + 1 < N) (j : Fin N) :
    (adjSwapFun N k hk j).val =
      if j.val = k then k + 1 else if j.val = k + 1 then k else j.val := by
  unfold adjSwapFun
  split_ifs <;> rfl

private lemma involutive_adjSwapFun (N k : ℕ) (hk : k + 1 < N) :
    Function.Involutive (adjSwapFun N k hk) := by
  intro j
  apply Fin.ext
  simp only [val_adjSwapFun]
  split_ifs <;> omega

/-- Cyclic shift `0 ↦ 1 ↦ ⋯ ↦ k ↦ 0` on the first `k + 1` elements of `Fin N`, fixing `> k`. -/
private def cyclePrefixFun (N k : ℕ) (hk : k < N) (j : Fin N) : Fin N :=
  if h : j.val < k then ⟨j.val + 1, by omega⟩
  else if j.val = k then ⟨0, by omega⟩
  else j

private lemma val_cyclePrefixFun (N k : ℕ) (hk : k < N) (j : Fin N) :
    (cyclePrefixFun N k hk j).val =
      if j.val < k then j.val + 1 else if j.val = k then 0 else j.val := by
  unfold cyclePrefixFun
  split_ifs <;> rfl

private lemma cyclePrefixFun_zero {N : ℕ} (h0 : 0 < N) :
    cyclePrefixFun N 0 h0 = id := by
  funext j
  apply Fin.ext
  simp only [val_cyclePrefixFun, Nat.not_lt_zero, ↓reduceIte, id_eq]
  split_ifs <;> omega

private lemma cyclePrefixFun_comp_adjSwapFun {N k : ℕ} (hk : k + 1 < N) :
    cyclePrefixFun N k (by omega) ∘ adjSwapFun N k hk = cyclePrefixFun N (k + 1) hk := by
  funext j
  apply Fin.ext
  simp only [Function.comp_apply, val_cyclePrefixFun, val_adjSwapFun]
  split_ifs <;> omega

/-- The product of the first `k` adjacent-swap matrices `(0,1), (1,2), …, (k-1,k)` on `Fin N`
is the `(k + 1)`-cycle `0 ↦ 1 ↦ ⋯ ↦ k ↦ 0`. -/
private lemma prod_take_adjSwap {N : ℕ} (S : Fin N → Matrix (Fin N) (Fin N) ℤ) (k : ℕ)
    (hk : k < N)
    (hS : ∀ (i : Fin k), S ⟨i.val, by omega⟩ = colPermMat (adjSwapFun N i.val (by omega))) :
    (((List.finRange k).map fun i : Fin k => S ⟨i.val, by omega⟩).prod) =
      colPermMat (cyclePrefixFun N k hk) := by
  induction k with
  | zero =>
    simp [cyclePrefixFun_zero hk, colPermMat_id]
  | succ k ih =>
    rw [List.finRange_succ_last, List.map_append, List.prod_append, List.map_map,
      List.map_singleton, List.prod_singleton]
    have hpre : (((List.finRange k).map
        ((fun i : Fin (k + 1) => S ⟨i.val, by omega⟩) ∘ Fin.castSucc)).prod) =
        colPermMat (cyclePrefixFun N k (by omega)) :=
      ih (by omega) fun i => hS i.castSucc
    rw [hpre, hS (Fin.last k), colPermMat_mul]
    simp only [Fin.val_last, cyclePrefixFun_comp_adjSwapFun hk]

/-! ### Type `Aₙ`: root-difference embedding into the `(n + 1)`-cycle -/

/-- The `(n + 1) × n` integer matrix whose `j`-th column is `eⱼ - eⱼ₊₁`. -/
private def matPA (n : ℕ) : Matrix (Fin (n + 1)) (Fin n) ℤ :=
  Matrix.of fun r j =>
    (if r.val = j.val then 1 else 0) - (if r.val = j.val + 1 then 1 else 0)

private lemma matPA_mulVec_single (n : ℕ) (j : Fin n) :
    matPA n *ᵥ Pi.single j 1 =
      Pi.single ⟨j.val, by omega⟩ 1 - Pi.single ⟨j.val + 1, by omega⟩ 1 := by
  ext r
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single j]
  · simp [matPA, Pi.single_apply, Fin.ext_iff, eq_comm]
  · intro k _ hkj
    simp [hkj]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Explicit left inverse of `matPA n`: summing rows `0, …, i` recovers the `i`-th coordinate. -/
private def leftInvPA (n : ℕ) : Matrix (Fin n) (Fin (n + 1)) ℤ :=
  Matrix.of fun i r => if r.val ≤ i.val then 1 else 0

private lemma leftInvPA_mul_matPA (n : ℕ) : leftInvPA n * matPA n = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [leftInvPA, matPA, Matrix.of_apply, mul_sub, Finset.sum_sub_distrib]
  have h1 : (∑ r : Fin (n + 1), (if r.val ≤ i.val then (1 : ℤ) else 0) *
      (if r.val = j.val then 1 else 0)) = if j.val ≤ i.val then 1 else 0 := by
    rw [Finset.sum_eq_single ⟨j.val, by omega⟩]
    · simp
    · intro r _ hr
      have : r.val ≠ j.val := fun h => hr (Fin.ext h)
      simp [this]
    · intro h; exact absurd (Finset.mem_univ _) h
  have h2 : (∑ r : Fin (n + 1), (if r.val ≤ i.val then (1 : ℤ) else 0) *
      (if r.val = j.val + 1 then 1 else 0)) = if j.val + 1 ≤ i.val then 1 else 0 := by
    rw [Finset.sum_eq_single ⟨j.val + 1, by omega⟩]
    · simp
    · intro r _ hr
      have : r.val ≠ j.val + 1 := fun h => hr (Fin.ext h)
      simp [this]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [h1, h2]
  simp only [Matrix.one_apply, Fin.ext_iff]
  split_ifs <;> omega

private lemma matPA_left_injective {n : ℕ} {κ : Type*} {X Y : Matrix (Fin n) κ ℤ}
    (h : matPA n * X = matPA n * Y) : X = Y := by
  calc
    X = (1 : Matrix (Fin n) (Fin n) ℤ) * X := (Matrix.one_mul X).symm
    _ = leftInvPA n * matPA n * X := by rw [leftInvPA_mul_matPA]
    _ = leftInvPA n * (matPA n * Y) := by rw [Matrix.mul_assoc, h]
    _ = (1 : Matrix (Fin n) (Fin n) ℤ) * Y := by rw [← Matrix.mul_assoc, leftInvPA_mul_matPA]
    _ = Y := Matrix.one_mul Y

/-- Coordinate simple reflections of type `Aₙ` on `Fin (n + 1)`. -/
private def reflCoordA (n : ℕ) (i : Fin (n + 1)) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  if hi : i.val + 1 < n + 1 then colPermMat (adjSwapFun (n + 1) i.val hi) else 1

private lemma matPA_mul_reflMatrix (n : ℕ) (i : Fin n) :
    matPA n * reflMatrix (CartanMatrix.A n) i = reflCoordA n ⟨i.val, by omega⟩ * matPA n := by
  ext r j
  have hi : i.val + 1 < n + 1 := by omega
  rw [mul_reflMatrix_apply, reflCoordA, dite_eq_left_of_eq_true (eq_true hi),
      colPermMat_mul_apply_of_involutive (involutive_adjSwapFun (n + 1) i.val hi)]
  have := r.isLt; have := j.isLt; have := i.isLt
  simp only [matPA, CartanMatrix.A, Matrix.of_apply, val_adjSwapFun, Fin.ext_iff]
  split_ifs <;> omega

/-- Cyclic shift `0 ↦ 1 ↦ ⋯ ↦ n ↦ 0` on `Fin (n + 1)`. -/
private def cycleFun (n : ℕ) : Fin (n + 1) → Fin (n + 1) :=
  cyclePrefixFun (n + 1) n (Nat.lt_succ_self n)

private lemma matPA_mul_coxA (n : ℕ) :
    matPA n * coxA n = colPermMat (cycleFun n) * matPA n := by
  rw [coxA, mul_coxeterElement (matPA n) (CartanMatrix.A n)
    (fun i => reflCoordA n ⟨i.val, by omega⟩) (matPA_mul_reflMatrix n)]
  congr 1
  exact prod_take_adjSwap (N := n + 1) (reflCoordA n) n (Nat.lt_succ_self n) fun i => by
    simp [reflCoordA, Nat.add_lt_add_right i.isLt 1]

private lemma cycleFun_apply (n : ℕ) (j : Fin (n + 1)) :
    cycleFun n j = ⟨(j.val + 1) % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩ := by
  apply Fin.ext
  have := j.isLt
  simp only [cycleFun, val_cyclePrefixFun]
  split_ifs with hj hjn
  · exact (Nat.mod_eq_of_lt (by omega : j.val + 1 < n + 1)).symm
  · simp [hjn]
  · omega

private lemma colPermMat_cycleFun_pow_mulVec_single (n m : ℕ) (j : Fin (n + 1)) :
    (colPermMat (cycleFun n) ^ m) *ᵥ Pi.single j 1 =
      Pi.single ⟨(j.val + m) % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩ 1 := by
  induction m generalizing j with
  | zero =>
    rw [pow_zero, Matrix.one_mulVec]
    congr 1; ext; simp [Nat.mod_eq_of_lt j.isLt]
  | succ m ih =>
    rw [pow_succ, ← Matrix.mulVec_mulVec, colPermMat_mulVec_single, cycleFun_apply, ih]
    congr 1; ext
    simp [Nat.mod_add_mod, Nat.add_assoc, Nat.add_comm 1 m]

private lemma coxA_pow_mulVec_single_zero {n : ℕ} (hn : 0 < n) (m : ℕ) (hm : m < n) :
    coxA n ^ m *ᵥ Pi.single ⟨0, hn⟩ 1 = Pi.single ⟨m, hm⟩ 1 := by
  have hpow : matPA n * coxA n ^ m = colPermMat (cycleFun n) ^ m * matPA n :=
    mul_pow_of_intertwine (matPA_mul_coxA n) m
  have hcol : (matPA n * coxA n ^ m) *ᵥ Pi.single ⟨0, hn⟩ 1 =
      matPA n *ᵥ Pi.single ⟨m, hm⟩ 1 := by
    rw [hpow, ← Matrix.mulVec_mulVec, matPA_mulVec_single, matPA_mulVec_single,
      Matrix.mulVec_sub, colPermMat_cycleFun_pow_mulVec_single,
      colPermMat_cycleFun_pow_mulVec_single]
    have h0 : (⟨(0 + m) % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩ : Fin (n + 1)) =
        ⟨m, by omega⟩ := by
      ext; simp [Nat.mod_eq_of_lt (by omega : m < n + 1)]
    have h1 : (⟨(0 + 1 + m) % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩ : Fin (n + 1)) =
        ⟨m + 1, by omega⟩ := by
      ext; simp [Nat.add_comm 1 m, Nat.mod_eq_of_lt (by omega : m + 1 < n + 1)]
    rw [h0, h1]
  have h1 := congrArg (leftInvPA n *ᵥ ·) hcol
  rwa [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, leftInvPA_mul_matPA, Matrix.one_mul,
    Matrix.mulVec_mulVec, leftInvPA_mul_matPA, Matrix.one_mulVec] at h1

private lemma sum_cycle_single_apply (n : ℕ) (a r : Fin (n + 1)) :
    (∑ m ∈ Finset.range (n + 1),
      (Pi.single (M := fun _ : Fin (n + 1) => ℤ)
        ⟨(a.val + m) % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩ 1) r) = 1 := by
  have ha := a.isLt; have hr := r.isLt
  let m₀ : ℕ := if a.val ≤ r.val then r.val - a.val else r.val + (n + 1) - a.val
  have hm₀_lt : m₀ < n + 1 := by dsimp [m₀]; split_ifs <;> omega
  rw [Finset.sum_eq_single_of_mem m₀ (Finset.mem_range.mpr hm₀_lt)]
  · have hm₀ : (a.val + m₀) % (n + 1) = r.val := by
      dsimp [m₀]
      split_ifs with har
      · rw [Nat.add_sub_of_le har, Nat.mod_eq_of_lt hr]
      · have hsum : a.val + (r.val + (n + 1) - a.val) = r.val + (n + 1) := by omega
        rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt hr]
    simp [hm₀]
  · intro m hm hne
    have hm_lt : m < n + 1 := Finset.mem_range.mp hm
    have hne_mod : (a.val + m) % (n + 1) ≠ r.val := by
      intro heq
      apply hne
      dsimp [m₀]
      rcases lt_or_ge (a.val + m) (n + 1) with hlt | hge
      · rw [Nat.mod_eq_of_lt hlt] at heq
        split_ifs <;> omega
      · have hsub : a.val + m = (a.val + m - (n + 1)) + (n + 1) := by omega
        rw [hsub, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at heq
        split_ifs <;> omega
    simp [Fin.ext_iff, hne_mod.symm]

private lemma sum_coxA_pow_eq_zero (n : ℕ) :
    (∑ m ∈ Finset.range (n + 1), coxA n ^ m) = 0 := by
  apply matPA_left_injective
  rw [Matrix.mul_zero, Matrix.mul_sum]
  have hterm : ∀ m, matPA n * coxA n ^ m = colPermMat (cycleFun n) ^ m * matPA n :=
    fun m => mul_pow_of_intertwine (matPA_mul_coxA n) m
  simp_rw [hterm, ← Matrix.sum_mul]
  ext r j
  have hval : ((∑ m ∈ Finset.range (n + 1), colPermMat (cycleFun n) ^ m) * matPA n) r j =
      (((∑ m ∈ Finset.range (n + 1), colPermMat (cycleFun n) ^ m) *ᵥ
        (matPA n *ᵥ Pi.single j 1)) r) := by
    rw [Matrix.mulVec_mulVec]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [hval, matPA_mulVec_single, Matrix.mulVec_sub, Matrix.sum_mulVec, Matrix.sum_mulVec,
    Pi.sub_apply, Finset.sum_apply, Finset.sum_apply, Matrix.zero_apply, sub_eq_zero]
  simp_rw [colPermMat_cycleFun_pow_mulVec_single]
  rw [sum_cycle_single_apply n ⟨j.val, by omega⟩ r,
    sum_cycle_single_apply n ⟨j.val + 1, by omega⟩ r]

/-- **The characteristic polynomial of the `Aₙ` Coxeter element is `1 + X + ⋯ + X^n`.** -/
theorem charpoly_coxA (n : ℕ) :
    (coxA n).charpoly = ∑ k ∈ Finset.range (n + 1), X ^ k := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  · have hmon : (∑ k ∈ Finset.range (n + 1), (X : ℤ[X]) ^ k).IsMonicOfDegree n := by
      rw [Finset.sum_range_succ, add_comm]
      refine (isMonicOfDegree_X_pow ℤ n).add_right ?_
      by_cases hp0 : (∑ k ∈ Finset.range n, (X : ℤ[X]) ^ k) = 0
      · rw [hp0, natDegree_zero]; exact hn
      · rw [natDegree_lt_iff_degree_lt hp0]
        refine (Polynomial.degree_sum_le (Finset.range n) fun k => (X : ℤ[X]) ^ k).trans_lt ?_
        refine (Finset.sup_lt_iff (WithBot.bot_lt_coe n)).mpr fun k hk => ?_
        rw [degree_X_pow]
        exact WithBot.coe_lt_coe.2 (Finset.mem_range.mp hk)
    have hann : aeval (coxA n) (∑ k ∈ Finset.range (n + 1), (X : ℤ[X]) ^ k) = 0 := by
      simpa using sum_coxA_pow_eq_zero n
    exact charpoly_eq_of_isMonicOfDegree_of_cyclic hn hmon hann (coxA_pow_mulVec_single_zero hn)

/-- **The Coxeter number of `Aₙ` is `n + 1`**: the Coxeter element of type `Aₙ` has order
`n + 1`. -/
theorem orderOf_coxA (n : ℕ) : orderOf (coxA n) = n + 1 := by
  rcases n.eq_zero_or_pos with rfl | hn
  · exact orderOf_eq_one_iff.mpr (Subsingleton.elim _ _)
  · refine (orderOf_eq_iff (Nat.succ_pos n)).mpr ⟨?_, fun m hm hpos h1 => ?_⟩
    · have hgeom := geom_sum_mul (coxA n) (n + 1)
      rw [sum_coxA_pow_eq_zero, zero_mul] at hgeom
      exact sub_eq_zero.mp hgeom.symm
    · rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hm) with hmn | hmn
      · have hv := coxA_pow_mulVec_single_zero hn m hmn
        rw [h1, Matrix.one_mulVec] at hv
        have := congrFun hv ⟨0, hn⟩
        simp [Fin.ext_iff, hpos.ne'] at this
      · rw [hmn] at h1
        have hsum : ((∑ k ∈ Finset.range (n + 1), coxA n ^ k) *ᵥ
            Pi.single ⟨0, hn⟩ (1 : ℤ)) ⟨0, hn⟩ = 0 := by
          rw [sum_coxA_pow_eq_zero, Matrix.zero_mulVec, Pi.zero_apply]
        rw [Finset.sum_range_succ, Matrix.add_mulVec, Matrix.sum_mulVec, Pi.add_apply,
          Finset.sum_apply, h1, Matrix.one_mulVec, Pi.single_eq_same] at hsum
        have hfirst : (∑ k ∈ Finset.range n,
            (coxA n ^ k *ᵥ Pi.single ⟨0, hn⟩ (1 : ℤ)) ⟨0, hn⟩) = 1 := by
          rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr hn)]
          · rw [pow_zero, Matrix.one_mulVec, Pi.single_eq_same]
          · intro k hk hk0
            rw [coxA_pow_mulVec_single_zero hn k (Finset.mem_range.mp hk)]
            simp [Fin.ext_iff, hk0.symm]
        omega

/-! ### The signed `n`-cycle model -/

/-- The signed `n`-cycle matrix sending `eⱼ ↦ eⱼ₊₁` for `j + 1 < n` and `eₙ₋₁ ↦ -e₀`. -/
private def negCycleMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun r j =>
    if j.val + 1 < n then (if r.val = j.val + 1 then 1 else 0)
    else (if r.val = 0 then -1 else 0)

private lemma negCycleMatrix_mulVec_single {n : ℕ} (j : Fin n) :
    negCycleMatrix n *ᵥ Pi.single j 1 =
      if hj : j.val + 1 < n then Pi.single ⟨j.val + 1, hj⟩ 1
      else -Pi.single ⟨0, by have := j.isLt; omega⟩ 1 := by
  ext r
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single j]
  · simp only [negCycleMatrix, Matrix.of_apply, Pi.single_eq_same, mul_one]
    by_cases hj : j.val + 1 < n
    · rw [ite_eq_left hj, dite_eq_left_of_eq_true (eq_true hj)]
      simp only [Pi.single_apply, Fin.ext_iff]
    · rw [ite_eq_right hj, dite_eq_right_of_eq_false (eq_false hj)]
      simp only [Pi.neg_apply, Pi.single_apply, Fin.ext_iff]
      split_ifs <;> omega
  · intro k _ hkj
    simp [hkj]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma negCycleMatrix_pow_mulVec_single {n : ℕ} (j : Fin n) (m : ℕ)
    (hm : j.val + m < n) :
    negCycleMatrix n ^ m *ᵥ Pi.single j 1 = Pi.single ⟨j.val + m, hm⟩ 1 := by
  induction m generalizing j with
  | zero => rw [pow_zero, Matrix.one_mulVec]; congr 1
  | succ m ih =>
    have hj1 : j.val + 1 < n := by omega
    rw [pow_succ, ← Matrix.mulVec_mulVec, negCycleMatrix_mulVec_single,
      dite_eq_left_of_eq_true (eq_true hj1), ih ⟨j.val + 1, hj1⟩ (by simp; omega)]
    congr 1; ext; simp; omega

private lemma negCycleMatrix_pow_self {n : ℕ} (hn : 1 ≤ n) :
    negCycleMatrix n ^ n = -1 := by
  ext r j
  have hpow : (negCycleMatrix n ^ (j.val + (1 + (n - 1 - j.val))) *ᵥ Pi.single j 1) r =
      -(1 : Matrix (Fin n) (Fin n) ℤ) r j := by
    rw [pow_add, pow_add, pow_one, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have h1 := negCycleMatrix_pow_mulVec_single j (n - 1 - j.val) (by have := j.isLt; omega)
    have hnot : ¬ (⟨j.val + (n - 1 - j.val), by have := j.isLt; omega⟩ : Fin n).val + 1 < n := by
      have := j.isLt; simp; omega
    rw [h1, negCycleMatrix_mulVec_single, dite_eq_right_of_eq_false (eq_false hnot),
      Matrix.mulVec_neg, negCycleMatrix_pow_mulVec_single ⟨0, by omega⟩ j.val (by simp)]
    simp [Matrix.one_apply, Pi.single_apply, Fin.ext_iff]
  have hsplit : j.val + (1 + (n - 1 - j.val)) = n := by have := j.isLt; omega
  rw [hsplit] at hpow
  rw [Matrix.neg_apply, ← hpow, Matrix.mulVec, dotProduct, Finset.sum_eq_single j]
  · simp
  · intro k _ hkj; simp [hkj]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma charpoly_negCycleMatrix {n : ℕ} (hn : 1 ≤ n) :
    (negCycleMatrix n).charpoly = X ^ n + 1 := by
  have hmon : ((X : ℤ[X]) ^ n + 1).IsMonicOfDegree n :=
    (isMonicOfDegree_X_pow ℤ n).add_right (by simpa using Nat.pos_of_ne_zero (by omega))
  have hann : aeval (negCycleMatrix n) ((X : ℤ[X]) ^ n + 1) = 0 := by
    simp [negCycleMatrix_pow_self hn]
  refine charpoly_eq_of_isMonicOfDegree_of_cyclic (by omega) hmon hann fun m hm => ?_
  simpa using negCycleMatrix_pow_mulVec_single (⟨0, by omega⟩ : Fin n) m (by simpa using hm)

private lemma orderOf_negCycleMatrix {n : ℕ} (hn : 1 ≤ n) :
    orderOf (negCycleMatrix n) = 2 * n := by
  refine (orderOf_eq_iff (by omega)).2 ⟨?_, fun m hm hpos h1 => ?_⟩
  · rw [mul_comm, pow_mul, negCycleMatrix_pow_self hn, neg_one_sq]
  · rcases lt_trichotomy m n with hlt | rfl | hgt
    · have hv := negCycleMatrix_pow_mulVec_single (⟨0, by omega⟩ : Fin n) m (by simpa using hlt)
      rw [h1, Matrix.one_mulVec] at hv
      have := congrFun hv ⟨0, by omega⟩
      simp [Fin.ext_iff, hpos.ne'] at this
    · rw [negCycleMatrix_pow_self hn] at h1
      have := congrFun₂ h1 ⟨0, by omega⟩ ⟨0, by omega⟩
      simp at this
    · have hsplit : m = n + (m - n) := by omega
      rw [hsplit, pow_add, negCycleMatrix_pow_self hn, neg_one_mul] at h1
      have hmn : m - n < n := by omega
      have hv := negCycleMatrix_pow_mulVec_single (⟨0, by omega⟩ : Fin n) (m - n)
        (by simpa using hmn)
      have hneg1 : negCycleMatrix n ^ (m - n) = -1 := neg_eq_iff_eq_neg.mp h1
      rw [hneg1] at hv
      have := congrFun hv ⟨0, by omega⟩
      have hmne : m - n ≠ 0 := by omega
      simp [Fin.ext_iff, hmne.symm] at this

/-! ### Type `Bₙ`: lower-unitriangular conjugation to the signed `n`-cycle -/

/-- The `n × n` lower-unitriangular matrix with columns `e₀ - e₁, …, eₙ₋₂ - eₙ₋₁, eₙ₋₁`. -/
private def matPB (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun r j =>
    if j.val + 1 < n then
      (if r.val = j.val then 1 else 0) - (if r.val = j.val + 1 then 1 else 0)
    else
      if r = j then 1 else 0

private lemma det_matPB (n : ℕ) : (matPB n).det = 1 := by
  have htri : (matPB n).IsLowerTriangular := by
    intro i j hij
    have hlt : i.val < j.val := Fin.lt_def.mp hij
    simp only [matPB, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> omega
  rw [Matrix.det_of_isLowerTriangular _ htri]
  refine Finset.prod_eq_one fun i _ => ?_
  simp only [matPB, Matrix.of_apply]
  split_ifs <;> omega

/-- Coordinate simple reflections of type `Bₙ`: adjacent swaps for `i < n - 1`, and negation of the
last coordinate for `i = n - 1`. -/
private def reflCoordB (n : ℕ) (i : Fin n) : Matrix (Fin n) (Fin n) ℤ :=
  if hi : i.val + 1 < n then
    colPermMat (adjSwapFun n i.val hi)
  else
    Matrix.diagonal fun r : Fin n => if r.val + 1 = n then -1 else 1

private lemma matPB_mul_reflMatrix (n : ℕ) (i : Fin n) :
    matPB n * reflMatrix (CartanMatrix.B n) i = reflCoordB n i * matPB n := by
  ext r j
  rw [mul_reflMatrix_apply]
  by_cases hi : i.val + 1 < n
  · rw [reflCoordB, dite_eq_left_of_eq_true (eq_true hi),
      colPermMat_mul_apply_of_involutive (involutive_adjSwapFun n i.val hi)]
    have := r.isLt; have := j.isLt
    simp only [matPB, CartanMatrix.B, Matrix.of_apply, val_adjSwapFun, Fin.ext_iff]
    split_ifs <;> omega
  · rw [reflCoordB, dite_eq_right_of_eq_false (eq_false hi), Matrix.diagonal_mul]
    have := r.isLt; have := j.isLt; have := i.isLt
    simp only [matPB, CartanMatrix.B, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> omega

private lemma matPB_mul_coxB {n : ℕ} (hn : 1 ≤ n) :
    matPB n * coxB n = negCycleMatrix n * matPB n := by
  rw [coxB, mul_coxeterElement (matPB n) (CartanMatrix.B n) (reflCoordB n) (matPB_mul_reflMatrix n)]
  congr 1
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [List.finRange_succ_last, List.map_append, List.prod_append, List.map_map,
    List.map_singleton, List.prod_singleton]
  have hpre : (((List.finRange m).map (reflCoordB (m + 1) ∘ Fin.castSucc)).prod) =
      colPermMat (cyclePrefixFun (m + 1) m (Nat.lt_succ_self m)) := by
    refine prod_take_adjSwap (N := m + 1) (reflCoordB (m + 1)) m (Nat.lt_succ_self m) fun i => ?_
    simp [reflCoordB, Nat.add_lt_add_right i.isLt 1]
  have hlast : reflCoordB (m + 1) (Fin.last m) =
      Matrix.diagonal fun r : Fin (m + 1) => if r.val + 1 = m + 1 then -1 else 1 := by
    simp [reflCoordB]
  rw [hpre, hlast]
  ext r j
  rw [Matrix.mul_diagonal]
  have := r.isLt; have := j.isLt
  simp only [colPermMat, negCycleMatrix, Matrix.of_apply, Fin.ext_iff, val_cyclePrefixFun]
  split_ifs <;> omega

/-- **The characteristic polynomial of the `Bₙ` Coxeter element is `X^n + 1`** (`1 ≤ n`). -/
theorem charpoly_coxB {n : ℕ} (hn : 1 ≤ n) :
    (coxB n).charpoly = X ^ n + 1 := by
  have h := charpoly_and_orderOf_of_intertwine (by rw [det_matPB]; norm_num) (matPB_mul_coxB hn)
  exact h.1.trans (charpoly_negCycleMatrix hn)

/-- **The Coxeter number of `Bₙ` is `2 n`** (`1 ≤ n`): the Coxeter element of type `Bₙ` has order
`2 n`. -/
theorem orderOf_coxB {n : ℕ} (hn : 1 ≤ n) :
    orderOf (coxB n) = 2 * n := by
  have h := charpoly_and_orderOf_of_intertwine (by rw [det_matPB]; norm_num) (matPB_mul_coxB hn)
  exact h.2.trans (orderOf_negCycleMatrix hn)

/-! ### Type `Cₙ`: diagonal conjugation to type `Bₙ` -/

/-- The diagonal matrix `diag(1, …, 1, 2)` intertwining `coxC n` with `coxB n`. -/
private def diagBC (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.diagonal fun k : Fin n => if k.val + 1 = n then 2 else 1

private lemma det_diagBC_ne_zero (n : ℕ) : (diagBC n).det ≠ 0 := by
  rw [diagBC, Matrix.det_diagonal]
  refine Finset.prod_ne_zero_iff.mpr fun k _ => ?_
  split_ifs <;> norm_num

private lemma diagBC_mul_reflMatrix (n : ℕ) (i : Fin n) :
    diagBC n * reflMatrix (CartanMatrix.C n) i =
      reflMatrix (CartanMatrix.B n) i * diagBC n := by
  ext r j
  rw [diagBC, Matrix.diagonal_mul, Matrix.mul_diagonal]
  have := r.isLt; have := j.isLt; have := i.isLt
  simp only [reflMatrix_apply, CartanMatrix.B, CartanMatrix.C, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> omega

private lemma diagBC_mul_coxC (n : ℕ) :
    diagBC n * coxC n = coxB n * diagBC n :=
  mul_coxeterElement (diagBC n) (CartanMatrix.C n) (reflMatrix (CartanMatrix.B n))
    (diagBC_mul_reflMatrix n)

/-- **The characteristic polynomial of the `Cₙ` Coxeter element is `X^n + 1`** (`1 ≤ n`). -/
theorem charpoly_coxC {n : ℕ} (hn : 1 ≤ n) :
    (coxC n).charpoly = X ^ n + 1 :=
  (charpoly_and_orderOf_of_intertwine (det_diagBC_ne_zero n) (diagBC_mul_coxC n)).1.trans
    (charpoly_coxB hn)

/-- **The Coxeter number of `Cₙ` is `2 n`** (`1 ≤ n`): the Coxeter element of type `Cₙ` has order
`2 n`. -/
theorem orderOf_coxC {n : ℕ} (hn : 1 ≤ n) :
    orderOf (coxC n) = 2 * n :=
  (charpoly_and_orderOf_of_intertwine (det_diagBC_ne_zero n) (diagBC_mul_coxC n)).2.trans
    (orderOf_coxB hn)

/-! ### Type `Dₙ`: block-diagonal conjugation to a signed `(n - 1)`-cycle and `-1` -/

/-- The `n × n` integer matrix with columns `e₀ - e₁, …, eₙ₋₂ - eₙ₋₁, eₙ₋₂ + eₙ₋₁`. -/
private def matPD (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun r j =>
    if j.val + 1 < n then
      (if r.val = j.val then 1 else 0) - (if r.val = j.val + 1 then 1 else 0)
    else
      (if r.val + 2 = n then 1 else 0) + (if r.val + 1 = n then 1 else 0)

/-- Upper-triangular column operation `col_{n-1} ↦ col_{n-2} + 2 col_{n-1}` relating `matPB n` to
`matPD n`. -/
private def upperUD (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun k j =>
    if j.val + 1 < n then
      if k = j then 1 else 0
    else
      (if k.val + 2 = n then 1 else 0) + (if k.val + 1 = n then 2 else 0)

private lemma matPB_mul_upperUD {n : ℕ} (hn : 2 ≤ n) :
    matPB n * upperUD n = matPD n := by
  ext r j
  rw [Matrix.mul_apply]
  by_cases hj : j.val + 1 < n
  · rw [Finset.sum_eq_single j]
    · simp [matPB, upperUD, matPD, hj]
    · intro k _ hkj
      simp [upperUD, hj, hkj]
    · intro h; exact absurd (Finset.mem_univ _) h
  · have hsum : (∑ k : Fin n, matPB n r k * upperUD n k j) =
        matPB n r ⟨n - 2, by omega⟩ * 1 + matPB n r ⟨n - 1, by omega⟩ * 2 := by
      have hne : (⟨n - 2, by omega⟩ : Fin n) ≠ ⟨n - 1, by omega⟩ := by
        simp [Fin.ext_iff]; omega
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨n - 2, by omega⟩ : Fin n)),
        ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ _⟩)]
      have hrest : ∑ k ∈ (Finset.univ.erase (⟨n - 2, by omega⟩ : Fin n)).erase
          ⟨n - 1, by omega⟩, matPB n r k * upperUD n k j = 0 := by
        refine Finset.sum_eq_zero fun k hk => ?_
        have hk1 : k.val ≠ n - 1 := fun h => (Finset.mem_erase.mp hk).1 (Fin.ext h)
        have hk2 : k.val ≠ n - 2 :=
          fun h => (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1 (Fin.ext h)
        have hzero : upperUD n k j = 0 := by
          simp only [upperUD, Matrix.of_apply, hj, ↓reduceIte]
          split_ifs <;> omega
        rw [hzero, mul_zero]
      rw [hrest, add_zero]
      congr 2
      · simp only [upperUD, Matrix.of_apply, hj, ↓reduceIte]
        split_ifs <;> omega
      · simp only [upperUD, Matrix.of_apply, hj, ↓reduceIte]
        split_ifs <;> omega
    rw [hsum]
    have := r.isLt; have := j.isLt
    have hpb2 : matPB n r ⟨n - 2, by omega⟩ =
        (if r.val = n - 2 then 1 else 0) - (if r.val = n - 2 + 1 then 1 else 0) := by
      simp only [matPB, Matrix.of_apply, Fin.ext_iff]
      split_ifs <;> omega
    have hpb1 : matPB n r ⟨n - 1, by omega⟩ = if r.val = n - 1 then 1 else 0 := by
      simp only [matPB, Matrix.of_apply, Fin.ext_iff]
      split_ifs <;> omega
    rw [hpb2, hpb1]
    simp only [matPD, Matrix.of_apply, hj, ↓reduceIte]
    split_ifs <;> omega

private lemma det_matPD {n : ℕ} (hn : 2 ≤ n) : (matPD n).det = 2 := by
  rw [← matPB_mul_upperUD hn, Matrix.det_mul, det_matPB, one_mul]
  have htri : (upperUD n).IsUpperTriangular := by
    intro i j hij
    have hlt : j.val < i.val := Fin.lt_def.mp hij
    have := i.isLt
    simp only [upperUD, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> omega
  rw [Matrix.det_of_isUpperTriangular htri]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Fin.prod_univ_castSucc]
  have h1 : (∏ i : Fin m, upperUD (m + 1) i.castSucc i.castSucc) = 1 := by
    refine Finset.prod_eq_one fun i _ => ?_
    simp [upperUD]
  have h2 : upperUD (m + 1) (Fin.last m) (Fin.last m) = 2 := by
    simp only [upperUD, Matrix.of_apply, Fin.val_last]
    split_ifs <;> omega
  rw [h1, h2, one_mul]

private lemma cartanMatrixD_apply_of_lt {n : ℕ} {i : Fin n} (hi : i.val + 1 < n) (j : Fin n) :
    CartanMatrix.D n j i =
      if j = i then 2
      else if n ≤ 2 then 0
      else if j.val + 1 < n then
        if j.val + 1 = i.val ∨ (i.val + 1 = j.val ∧ i.val + 2 < n) then -1 else 0
      else
        if i.val + 3 = n then -1 else 0 := by
  have := j.isLt
  simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> omega

private lemma cartanMatrixD_apply_of_not_lt {n : ℕ} {i : Fin n} (hi : ¬ i.val + 1 < n)
    (j : Fin n) :
    CartanMatrix.D n j i =
      if j = i then 2
      else if n ≤ 2 then 0
      else if j.val + 3 = n then -1
      else 0 := by
  have := i.isLt; have := j.isLt
  simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> omega

/-- The last reflection of `Dₙ` in standard coordinates sends `eₙ₋₂ ↦ -eₙ₋₁`, `eₙ₋₁ ↦ -eₙ₋₂`, and
fixes `eᵣ` for `r < n - 2`. -/
private def lastReflD (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun r j =>
    if j.val + 2 = n then (if r.val + 1 = n then -1 else 0)
    else if j.val + 1 = n then (if r.val + 2 = n then -1 else 0)
    else (if r = j then 1 else 0)

private lemma lastReflD_mul_apply {n : ℕ} (hn : 2 ≤ n) {κ : Type*} (M : Matrix (Fin n) κ ℤ)
    (r : Fin n) (j : κ) :
    (lastReflD n * M) r j =
      if r.val + 1 = n then -M ⟨n - 2, by omega⟩ j
      else if r.val + 2 = n then -M ⟨n - 1, by omega⟩ j
      else M r j := by
  rw [Matrix.mul_apply]
  by_cases hr1 : r.val + 1 = n
  · rw [ite_eq_left hr1, Finset.sum_eq_single ⟨n - 2, by omega⟩]
    · simp only [lastReflD, Matrix.of_apply, hr1]
      split_ifs <;> omega
    · intro k _ hk
      refine mul_eq_zero_of_left ?_ _
      have hne : k.val + 2 ≠ n := fun h => hk (Fin.ext (by simp; omega))
      have := k.isLt
      simp only [lastReflD, Matrix.of_apply, hr1, Fin.ext_iff]
      split_ifs <;> omega
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [ite_eq_right hr1]
    by_cases hr2 : r.val + 2 = n
    · rw [ite_eq_left hr2, Finset.sum_eq_single ⟨n - 1, by omega⟩]
      · simp only [lastReflD, Matrix.of_apply, hr2]
        split_ifs <;> omega
      · intro k _ hk
        refine mul_eq_zero_of_left ?_ _
        have hne : k.val + 1 ≠ n := fun h => hk (Fin.ext (by simp; omega))
        have := k.isLt
        simp only [lastReflD, Matrix.of_apply, hr1, hr2, Fin.ext_iff]
        split_ifs <;> omega
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [ite_eq_right hr2, Finset.sum_eq_single r]
      · simp only [lastReflD, Matrix.of_apply, hr1, hr2, ↓reduceIte, one_mul]
      · intro k _ hk
        refine mul_eq_zero_of_left ?_ _
        have hkr : r ≠ k := hk.symm
        simp only [lastReflD, Matrix.of_apply, hr1, hr2, hkr, ↓reduceIte]
        split_ifs <;> omega
      · intro h; exact absurd (Finset.mem_univ _) h

/-- Coordinate simple reflections of type `Dₙ`. -/
private def reflCoordD (n : ℕ) (i : Fin n) : Matrix (Fin n) (Fin n) ℤ :=
  if hi : i.val + 1 < n then colPermMat (adjSwapFun n i.val hi) else lastReflD n

private lemma matPD_mul_reflMatrix {n : ℕ} (hn : 2 ≤ n) (i : Fin n) :
    matPD n * reflMatrix (CartanMatrix.D n) i = reflCoordD n i * matPD n := by
  ext r j
  rw [mul_reflMatrix_apply]
  have := r.isLt; have := j.isLt; have := i.isLt
  by_cases hi : i.val + 1 < n
  · rw [reflCoordD, dite_eq_left_of_eq_true (eq_true hi),
      colPermMat_mul_apply_of_involutive (involutive_adjSwapFun n i.val hi),
      cartanMatrixD_apply_of_lt hi j]
    by_cases hj : j.val + 1 < n
    · rcases eq_or_ne j i with rfl | hji
      · simp only [ ↓reduceIte, matPD, Matrix.of_apply, hi, val_adjSwapFun]
        split_ifs <;> omega
      · simp only [hji, hj, hi, ↓reduceIte, matPD, Matrix.of_apply, val_adjSwapFun]
        split_ifs <;> omega
    · have hji : j ≠ i := fun h => hj (h ▸ hi)
      simp only [hji, hj, hi, ↓reduceIte, matPD, Matrix.of_apply, val_adjSwapFun]
      split_ifs <;> omega
  · rw [reflCoordD, dite_eq_right_of_eq_false (eq_false hi), lastReflD_mul_apply hn,
      cartanMatrixD_apply_of_not_lt hi j]
    by_cases hj : j.val + 1 < n
    · have hji : j ≠ i := fun h => hi (h ▸ hj)
      simp only [hji, hj, hi, ↓reduceIte, matPD, Matrix.of_apply]
      split_ifs <;> omega
    · have hji : j = i := Fin.ext (by omega)
      simp only [hji, hi, ↓reduceIte, matPD, Matrix.of_apply]
      split_ifs <;> omega

/-- Block-diagonal model of `coxD (m + 1)`: `negCycleMatrix m` on `Fin m` and `-1` on `Fin 1`. -/
private def blockModelD (m : ℕ) : Matrix (Fin m ⊕ Fin 1) (Fin m ⊕ Fin 1) ℤ :=
  Matrix.fromBlocks (negCycleMatrix m) 0 0 (-1)

/-- `blockModelD m` transported to `Fin (m + 1)` along `finSumFinEquiv`. -/
private def modelDSucc (m : ℕ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ :=
  (blockModelD m).reindex (finSumFinEquiv : Fin m ⊕ Fin 1 ≃ Fin (m + 1))
    (finSumFinEquiv : Fin m ⊕ Fin 1 ≃ Fin (m + 1))

private lemma colPermMat_cyclePrefix_mul_apply {m : ℕ} {κ : Type*}
    (M : Matrix (Fin (m + 1)) κ ℤ) (r : Fin (m + 1)) (j : κ) :
    (colPermMat (cyclePrefixFun (m + 1) m (Nat.lt_succ_self m)) * M) r j =
      if hr : 0 < r.val then M ⟨r.val - 1, by omega⟩ j else M ⟨m, by omega⟩ j := by
  rw [Matrix.mul_apply]
  by_cases hr : 0 < r.val
  · rw [dite_eq_left_of_eq_true (eq_true hr), Finset.sum_eq_single ⟨r.val - 1, by omega⟩]
    · have := r.isLt
      simp only [colPermMat, Matrix.of_apply, Fin.ext_iff, val_cyclePrefixFun]
      split_ifs <;> omega
    · intro k _ hk
      have hne : k.val ≠ r.val - 1 := fun h => hk (Fin.ext h)
      have := r.isLt; have := k.isLt
      simp only [colPermMat, Matrix.of_apply, Fin.ext_iff, val_cyclePrefixFun]
      split_ifs <;> omega
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [dite_eq_right_of_eq_false (eq_false hr), Finset.sum_eq_single ⟨m, by omega⟩]
    · simp only [colPermMat, Matrix.of_apply, Fin.ext_iff, val_cyclePrefixFun]
      split_ifs <;> omega
    · intro k _ hk
      have hne : k.val ≠ m := fun h => hk (Fin.ext h)
      have := k.isLt
      simp only [colPermMat, Matrix.of_apply, Fin.ext_iff, val_cyclePrefixFun]
      split_ifs <;> omega
    · intro h; exact absurd (Finset.mem_univ _) h

private lemma colPermMat_cyclePrefix_mul_lastReflD {m : ℕ} (hm : 1 ≤ m) :
    colPermMat (cyclePrefixFun (m + 1) m (Nat.lt_succ_self m)) * lastReflD (m + 1) =
      modelDSucc m := by
  ext r j
  rw [colPermMat_cyclePrefix_mul_apply]
  refine Fin.lastCases ?_ (fun r₀ => ?_) r <;> refine Fin.lastCases ?_ (fun j₀ => ?_) j
  · simp only [Fin.val_last, modelDSucc, Matrix.reindex_apply, Matrix.submatrix_apply,
      finSumFinEquiv_symm_last, blockModelD, Matrix.fromBlocks_apply₂₂, Matrix.neg_apply,
      Matrix.one_apply_eq]
    rw [dite_eq_left_of_eq_true (eq_true (by omega : 0 < m))]
    simp only [lastReflD, Matrix.of_apply, Fin.val_last, Fin.ext_iff]
    split_ifs <;> omega
  · have hj₀ := j₀.isLt
    simp only [Fin.val_last, modelDSucc, Matrix.reindex_apply,
      Matrix.submatrix_apply, finSumFinEquiv_symm_last, finSumFinEquiv_symm_apply_castSucc,
      blockModelD, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
    rw [dite_eq_left_of_eq_true (eq_true (by omega : 0 < m))]
    simp only [lastReflD, Matrix.of_apply, Fin.val_castSucc, Fin.ext_iff]
    split_ifs <;> omega
  · have hr₀ := r₀.isLt
    simp only [Fin.val_castSucc, modelDSucc, Matrix.reindex_apply,
      Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castSucc, finSumFinEquiv_symm_last,
      blockModelD, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]
    by_cases hr : 0 < r₀.val
    · rw [dite_eq_left_of_eq_true (eq_true hr)]
      simp only [lastReflD, Matrix.of_apply, Fin.val_last, Fin.ext_iff]
      split_ifs <;> omega
    · rw [dite_eq_right_of_eq_false (eq_false hr)]
      simp only [lastReflD, Matrix.of_apply, Fin.val_last, Fin.ext_iff]
      split_ifs <;> omega
  · have hr₀ := r₀.isLt; have hj₀ := j₀.isLt
    simp only [Fin.val_castSucc, modelDSucc, Matrix.reindex_apply, Matrix.submatrix_apply,
      finSumFinEquiv_symm_apply_castSucc, blockModelD, Matrix.fromBlocks_apply₁₁, negCycleMatrix,
      Matrix.of_apply]
    by_cases hr : 0 < r₀.val
    · rw [dite_eq_left_of_eq_true (eq_true hr)]
      simp only [lastReflD, Matrix.of_apply, Fin.val_castSucc, Fin.ext_iff]
      split_ifs <;> omega
    · rw [dite_eq_right_of_eq_false (eq_false hr)]
      simp only [lastReflD, Matrix.of_apply, Fin.val_castSucc, Fin.ext_iff]
      split_ifs <;> omega

private lemma matPD_mul_coxD_succ {m : ℕ} (hm : 1 ≤ m) :
    matPD (m + 1) * coxD (m + 1) = modelDSucc m * matPD (m + 1) := by
  rw [coxD, mul_coxeterElement (matPD (m + 1)) (CartanMatrix.D (m + 1))
    (reflCoordD (m + 1)) (matPD_mul_reflMatrix (by omega))]
  congr 1
  rw [List.finRange_succ_last, List.map_append, List.prod_append, List.map_map,
    List.map_singleton, List.prod_singleton]
  have hpre : (((List.finRange m).map (reflCoordD (m + 1) ∘ Fin.castSucc)).prod) =
      colPermMat (cyclePrefixFun (m + 1) m (Nat.lt_succ_self m)) := by
    refine prod_take_adjSwap (N := m + 1) (reflCoordD (m + 1)) m (Nat.lt_succ_self m) fun i => ?_
    simp [reflCoordD, Nat.add_lt_add_right i.isLt 1]
  have hlast : reflCoordD (m + 1) (Fin.last m) = lastReflD (m + 1) := by
    simp [reflCoordD]
  rw [hpre, hlast, colPermMat_cyclePrefix_mul_lastReflD hm]

private lemma charpoly_modelDSucc {m : ℕ} (hm : 1 ≤ m) :
    (modelDSucc m).charpoly = (X ^ m + 1) * (X + 1) := by
  rw [modelDSucc, Matrix.charpoly_reindex, blockModelD, Matrix.charpoly_fromBlocks_zero₁₂,
    charpoly_negCycleMatrix hm]
  congr 1
  rw [Matrix.charpoly, Matrix.charmatrix, Matrix.det_fin_one]
  simp [sub_neg_eq_add]

private lemma orderOf_modelDSucc {m : ℕ} (hm : 1 ≤ m) :
    orderOf (modelDSucc m) = 2 * m := by
  let e : Fin m ⊕ Fin 1 ≃ Fin (m + 1) := finSumFinEquiv
  let φ := (Matrix.reindexAlgEquiv ℤ ℤ e).toMulEquiv
  have he : orderOf (modelDSucc m) = orderOf (blockModelD m) :=
    φ.orderOf_eq (blockModelD m)
  rw [he]
  refine (orderOf_eq_iff (by omega)).2 ⟨?_, fun k hk hpos h1 => ?_⟩
  · rw [blockModelD, Matrix.fromBlocks_diagonal_pow, pow_mul' (negCycleMatrix m),
      negCycleMatrix_pow_self hm, neg_one_sq, pow_mul (-1 : Matrix (Fin 1) (Fin 1) ℤ),
      neg_one_sq, one_pow, Matrix.fromBlocks_one]
  · rw [blockModelD, Matrix.fromBlocks_diagonal_pow, ← Matrix.fromBlocks_one,
      Matrix.fromBlocks_inj] at h1
    exact pow_ne_one_of_lt_orderOf hpos.ne' (by rwa [orderOf_negCycleMatrix hm]) h1.1

/-- **The characteristic polynomial of the `Dₙ` Coxeter element is `(X^{n-1} + 1)(X + 1)`**
(`2 ≤ n`). -/
theorem charpoly_coxD {n : ℕ} (hn : 2 ≤ n) :
    (coxD n).charpoly = (X ^ (n - 1) + 1) * (X + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : 1 ≤ m := by omega
  have h := charpoly_and_orderOf_of_intertwine (by rw [det_matPD hn]; norm_num)
    (matPD_mul_coxD_succ hm)
  simpa using h.1.trans (charpoly_modelDSucc hm)

/-- **The Coxeter number of `Dₙ` is `2 (n - 1)`** (`2 ≤ n`): the Coxeter element of type `Dₙ` has
order `2 (n - 1)`. -/
theorem orderOf_coxD {n : ℕ} (hn : 2 ≤ n) :
    orderOf (coxD n) = 2 * (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : 1 ≤ m := by omega
  have h := charpoly_and_orderOf_of_intertwine (by rw [det_matPD hn]; norm_num)
    (matPD_mul_coxD_succ hm)
  simpa using h.2.trans (orderOf_modelDSucc hm)

end TauCeti.Coxeter

end
