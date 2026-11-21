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

private lemma isOneDegenerateOrder_finRange {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ}
    (h : ∀ x y z : Fin n, x.val < z.val → y.val < z.val → A z x ≠ 0 → A z y ≠ 0 → x.val = y.val) :
    List.IsOneDegenerateOrder (fun i j : Fin n => A i j ≠ 0) (List.finRange n) := by
  have hpw : (List.finRange n).Pairwise (fun a b => a.val < b.val) :=
    List.pairwise_iff_getElem.2 fun _ _ _ _ hij => by simpa using hij
  rw [List.isOneDegenerateOrder_iff]
  intro S₁ z S₂ hS x hx y hy hzx hzy
  rw [hS, List.pairwise_append] at hpw
  exact Fin.ext (h x y z (hpw.2.2 x hx z (List.mem_cons_self ..))
    (hpw.2.2 y hy z (List.mem_cons_self ..)) hzx hzy)

/-- The Bourbaki numbering `List.finRange n` is a one-degenerate order of the Dynkin diagram of
type `Aₙ`. -/
theorem isOneDegenerateOrder_A (n : ℕ) :
    List.IsOneDegenerateOrder (fun i j : Fin n => CartanMatrix.A n i j ≠ 0) (List.finRange n) :=
  isOneDegenerateOrder_finRange fun _ _ _ hxz hyz hzx hzy => by
    simp only [CartanMatrix.A, Matrix.of_apply] at hzx hzy; split_ifs at hzx hzy <;> omega

/-- The Bourbaki numbering `List.finRange n` is a one-degenerate order of the Dynkin diagram of
type `Bₙ`. -/
theorem isOneDegenerateOrder_B (n : ℕ) :
    List.IsOneDegenerateOrder (fun i j : Fin n => CartanMatrix.B n i j ≠ 0) (List.finRange n) :=
  isOneDegenerateOrder_finRange fun _ _ _ hxz hyz hzx hzy => by
    simp only [CartanMatrix.B, Matrix.of_apply] at hzx hzy; split_ifs at hzx hzy <;> omega

/-- The Bourbaki numbering `List.finRange n` is a one-degenerate order of the Dynkin diagram of
type `Cₙ`. -/
theorem isOneDegenerateOrder_C (n : ℕ) :
    List.IsOneDegenerateOrder (fun i j : Fin n => CartanMatrix.C n i j ≠ 0) (List.finRange n) :=
  isOneDegenerateOrder_finRange fun _ _ _ hxz hyz hzx hzy => by
    simp only [CartanMatrix.C, Matrix.of_apply] at hzx hzy; split_ifs at hzx hzy <;> omega

/-- The Bourbaki numbering `List.finRange n` is a one-degenerate order of the Dynkin diagram of
type `Dₙ`: every node `z` is adjacent to at most one node of smaller index (`z - 1` on the stem
and on the first prong, and the branch node `n - 3` on the second prong `n - 1`). -/
theorem isOneDegenerateOrder_D (n : ℕ) :
    List.IsOneDegenerateOrder (fun i j : Fin n => CartanMatrix.D n i j ≠ 0) (List.finRange n) :=
  isOneDegenerateOrder_finRange fun _ _ _ hxz hyz hzx hzy => by
    simp only [CartanMatrix.D, Matrix.of_apply] at hzx hzy; split_ifs at hzx hzy <;> omega

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
    simp only [List.map_cons, List.prod_cons, ← Matrix.mul_assoc, hS i]
    rw [Matrix.mul_assoc, ih, Matrix.mul_assoc]

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
  have hφ_inj : Function.Injective φ := fun _ _ h =>
    Matrix.map_injective (Int.castRingHom ℚ).injective_int (by simpa [φ] using h)
  have hu : IsUnit (φ P) := by
    rw [Matrix.isUnit_iff_isUnit_det, ← RingHom.map_det, isUnit_iff_ne_zero]
    exact Int.cast_ne_zero.mpr hdet
  let u := hu.unit
  have hY : φ Y = u.val * φ X * (u⁻¹).val := by
    have hconj : u.val * φ X = φ Y * u.val := by
      simpa only [u, IsUnit.unit_spec, map_mul] using congrArg φ hXY
    rw [hconj, Matrix.mul_assoc, u.mul_inv, Matrix.mul_one]
  refine ⟨?_, ?_⟩
  · apply Matrix.charpoly_eq_of_map_rat
    rw [← Y.charpoly_map (Int.castRingHom ℚ), ← (Int.castRingHom ℚ).mapMatrix_apply,
      ← (Int.castRingHom ℚ).mapMatrix_apply, hY, Matrix.charpoly_mul_comm (u.val * φ X),
      ← Matrix.mul_assoc, u.inv_mul, Matrix.one_mul]
  · rw [← orderOf_injective φ.toMonoidHom hφ_inj X,
      ← orderOf_injective φ.toMonoidHom hφ_inj Y]
    let ψ : Matrix κ κ ℚ ≃* Matrix κ κ ℚ :=
      { toFun := fun M => u.val * M * (u⁻¹).val
        invFun := fun M => (u⁻¹).val * M * u.val
        left_inv := fun M => by simp [Matrix.mul_assoc]
        right_inv := fun M => by simp [Matrix.mul_assoc]
        map_mul' := fun M₁ M₂ => by simp [Matrix.mul_assoc] }
    change orderOf (φ X) = orderOf (φ Y)
    rw [hY]
    exact (ψ.orderOf_eq (φ X)).symm

/-- **Cyclic-vector criterion for the characteristic polynomial.** If `p` is monic of degree `n`,
annihilates `M`, and the first `n` powers of `M` carry `e₀` to the standard basis vectors `eₘ`,
then `M.charpoly = p`: the difference `M.charpoly - p` has degree `< n` and annihilates `M`, so its
evaluation at `e₀` forces every coefficient below `n` to vanish. -/
private theorem charpoly_eq_of_isMonicOfDegree_of_cyclic {n : ℕ} (hn : 0 < n)
    {M : Matrix (Fin n) (Fin n) ℤ} {p : ℤ[X]} (hp : p.IsMonicOfDegree n)
    (hann : aeval M p = 0)
    (hcyc : ∀ m (hm : m < n), M ^ m *ᵥ Pi.single ⟨0, hn⟩ 1 = Pi.single ⟨m, hm⟩ 1) :
    M.charpoly = p := by
  have hdeg_lt : (M.charpoly - p).natDegree < n :=
    IsMonicOfDegree.natDegree_sub_lt hn.ne'
      ⟨by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin], M.charpoly_monic⟩ hp
  have hann_sub : aeval M (M.charpoly - p) = 0 := by
    rw [map_sub, Matrix.aeval_self_charpoly, hann, sub_zero]
  rw [← sub_eq_zero]
  set q := M.charpoly - p
  ext j
  rw [coeff_zero]
  rcases lt_or_ge j n with hj | hj
  · have hvec : (aeval M q *ᵥ Pi.single ⟨0, hn⟩ 1) ⟨j, hj⟩ = 0 := by
      rw [hann_sub, Matrix.zero_mulVec, Pi.zero_apply]
    rw [aeval_eq_sum_range' hdeg_lt, Matrix.sum_mulVec, Finset.sum_apply,
      Finset.sum_eq_single_of_mem j (Finset.mem_range.mpr hj)] at hvec
    · rw [Matrix.smul_mulVec, Pi.smul_apply, hcyc j hj, Pi.single_eq_same, smul_eq_mul,
        mul_one] at hvec
      exact hvec
    · intro i hi hij
      rw [Matrix.smul_mulVec, Pi.smul_apply, hcyc i (Finset.mem_range.mp hi),
        Pi.single_eq_of_ne (Fin.ne_of_val_ne hij.symm), smul_zero]
  · exact coeff_eq_zero_of_natDegree_lt (hdeg_lt.trans_le hj)

/-- Matrix whose `j`-th column is the `f j`-th standard basis vector, so right-multiplying by it
reindexes columns by `f`. -/
private def colPermMat {κ : Type*} [DecidableEq κ] (f : κ → κ) : Matrix κ κ ℤ :=
  Matrix.of fun r j => if r = f j then 1 else 0

private lemma colPermMat_id {κ : Type*} [DecidableEq κ] : colPermMat (id : κ → κ) = 1 := by
  ext i j; simp [colPermMat, Matrix.one_apply]

private lemma colPermMat_mul {κ : Type*} [Fintype κ] [DecidableEq κ] (f g : κ → κ) :
    colPermMat f * colPermMat g = colPermMat (f ∘ g) := by
  ext i j; simp [Matrix.mul_apply, colPermMat]

private lemma colPermMat_mulVec_single {κ : Type*} [Fintype κ] [DecidableEq κ]
    (f : κ → κ) (j : κ) : colPermMat f *ᵥ Pi.single j 1 = Pi.single (f j) 1 := by
  ext r; simp [Matrix.mulVec_single, colPermMat, Pi.single_apply]

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
  if j.val = k then ⟨k + 1, hk⟩ else if j.val = k + 1 then ⟨k, by omega⟩ else j

private lemma val_adjSwapFun (N k : ℕ) (hk : k + 1 < N) (j : Fin N) :
    (adjSwapFun N k hk j).val =
      if j.val = k then k + 1 else if j.val = k + 1 then k else j.val := by
  unfold adjSwapFun; split_ifs <;> rfl

private lemma involutive_adjSwapFun (N k : ℕ) (hk : k + 1 < N) :
    Function.Involutive (adjSwapFun N k hk) := fun j => Fin.ext <| by
  simp only [val_adjSwapFun]; split_ifs <;> omega

/-- Cyclic shift `0 ↦ 1 ↦ ⋯ ↦ k ↦ 0` on the first `k + 1` elements of `Fin N`, fixing `> k`. -/
private def cyclePrefixFun (N k : ℕ) (hk : k < N) (j : Fin N) : Fin N :=
  if h : j.val < k then ⟨j.val + 1, by omega⟩ else if j.val = k then ⟨0, by omega⟩ else j

private lemma val_cyclePrefixFun (N k : ℕ) (hk : k < N) (j : Fin N) :
    (cyclePrefixFun N k hk j).val =
      if j.val < k then j.val + 1 else if j.val = k then 0 else j.val := by
  unfold cyclePrefixFun; split_ifs <;> rfl

private lemma cyclePrefixFun_zero {N : ℕ} (h0 : 0 < N) : cyclePrefixFun N 0 h0 = id :=
  funext fun j => Fin.ext <| by
    simp only [val_cyclePrefixFun, Nat.not_lt_zero, ↓reduceIte, id_eq]; split_ifs <;> omega

private lemma cyclePrefixFun_comp_adjSwapFun {N k : ℕ} (hk : k + 1 < N) :
    cyclePrefixFun N k (by omega) ∘ adjSwapFun N k hk = cyclePrefixFun N (k + 1) hk :=
  funext fun j => Fin.ext <| by
    simp only [Function.comp_apply, val_cyclePrefixFun, val_adjSwapFun]; split_ifs <;> omega

/-- The product of the first `k` adjacent-swap matrices `(0,1), (1,2), …, (k-1,k)` on `Fin N`
is the `(k + 1)`-cycle `0 ↦ 1 ↦ ⋯ ↦ k ↦ 0`. -/
private lemma prod_take_adjSwap {N : ℕ} (S : Fin N → Matrix (Fin N) (Fin N) ℤ) (k : ℕ)
    (hk : k < N)
    (hS : ∀ (i : Fin k), S ⟨i.val, by omega⟩ = colPermMat (adjSwapFun N i.val (by omega))) :
    (((List.finRange k).map fun i : Fin k => S ⟨i.val, by omega⟩).prod) =
      colPermMat (cyclePrefixFun N k hk) := by
  induction k with
  | zero => simp [cyclePrefixFun_zero hk, colPermMat_id]
  | succ k ih =>
    rw [List.finRange_succ_last, List.map_append, List.prod_append, List.map_map,
      List.map_singleton, List.prod_singleton]
    have hpre : (((List.finRange k).map
        ((fun i : Fin (k + 1) => S ⟨i.val, by omega⟩) ∘ Fin.castSucc)).prod) =
        colPermMat (cyclePrefixFun N k (by omega)) :=
      ih (by omega) fun i => hS i.castSucc
    rw [hpre, hS (Fin.last k), colPermMat_mul]
    simp only [Fin.val_last, cyclePrefixFun_comp_adjSwapFun hk]

/-- Factoring the product of `m + 1` reflections on `Fin (m + 1)` whose first `m` factors are
adjacent swaps as the `(m + 1)`-cycle followed by the last reflection. -/
private lemma prod_finRange_succ_adjSwap {m : ℕ}
    (S : Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ)
    (hS : ∀ i : Fin m, S i.castSucc = colPermMat (adjSwapFun (m + 1) i.val (by omega))) :
    ((List.finRange (m + 1)).map S).prod =
      colPermMat (cyclePrefixFun (m + 1) m (Nat.lt_succ_self m)) * S (Fin.last m) := by
  rw [List.finRange_succ_last, List.map_append, List.prod_append, List.map_map,
    List.map_singleton, List.prod_singleton]
  congr 1
  exact prod_take_adjSwap S m (Nat.lt_succ_self m) hS

/-! ### Type `Aₙ`: root-difference embedding into the `(n + 1)`-cycle -/

/-- The `(n + 1) × n` integer matrix whose `j`-th column is `eⱼ - eⱼ₊₁`. -/
private def matPA (n : ℕ) : Matrix (Fin (n + 1)) (Fin n) ℤ :=
  Matrix.of fun r j =>
    (if r.val = j.val then 1 else 0) - (if r.val = j.val + 1 then 1 else 0)

private lemma matPA_mulVec_single (n : ℕ) (j : Fin n) :
    matPA n *ᵥ Pi.single j 1 =
      Pi.single ⟨j.val, by omega⟩ 1 - Pi.single ⟨j.val + 1, by omega⟩ 1 := by
  ext r; simp [Matrix.mulVec_single, matPA, Pi.single_apply, Fin.ext_iff, eq_comm]

/-- Explicit left inverse of `matPA n`: summing rows `0, …, i` recovers the `i`-th coordinate. -/
private def leftInvPA (n : ℕ) : Matrix (Fin n) (Fin (n + 1)) ℤ :=
  Matrix.of fun i r => if r.val ≤ i.val then 1 else 0

private lemma leftInvPA_mul_matPA (n : ℕ) : leftInvPA n * matPA n = 1 := by
  ext i j
  have hsum : ∀ k : Fin (n + 1),
      (∑ r : Fin (n + 1), (if r.val ≤ i.val then (1 : ℤ) else 0) *
        (if r.val = k.val then 1 else 0)) = if k.val ≤ i.val then 1 else 0 := fun k => by
    rw [Finset.sum_eq_single k]
    · simp
    · intro r _ hr; simp [Fin.val_ne_of_ne hr]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [Matrix.mul_apply]
  simp only [leftInvPA, matPA, Matrix.of_apply, mul_sub, Finset.sum_sub_distrib,
    hsum ⟨j.val, by omega⟩, hsum ⟨j.val + 1, by omega⟩, Matrix.one_apply, Fin.ext_iff]
  split_ifs <;> omega

private lemma matPA_left_injective {n : ℕ} {κ : Type*} {X Y : Matrix (Fin n) κ ℤ}
    (h : matPA n * X = matPA n * Y) : X = Y := by
  simpa [← Matrix.mul_assoc, leftInvPA_mul_matPA] using congrArg (leftInvPA n * ·) h

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

private lemma colPermMat_cycleFun_pow_self (n : ℕ) :
    colPermMat (cycleFun n) ^ (n + 1) = 1 := by
  ext r j
  have h := congrFun (colPermMat_cycleFun_pow_mulVec_single n (n + 1) j) r
  simpa [Matrix.mulVec_single, Nat.mod_eq_of_lt j.isLt, Matrix.one_apply, Pi.single_apply,
    eq_comm] using h

private lemma coxA_pow_mulVec_single_zero {n : ℕ} (hn : 0 < n) (m : ℕ) (hm : m < n) :
    coxA n ^ m *ᵥ Pi.single ⟨0, hn⟩ 1 = Pi.single ⟨m, hm⟩ 1 := by
  have hcol : (matPA n * coxA n ^ m) *ᵥ Pi.single ⟨0, hn⟩ 1 =
      matPA n *ᵥ Pi.single ⟨m, hm⟩ 1 := by
    rw [mul_pow_of_intertwine (matPA_mul_coxA n) m, ← Matrix.mulVec_mulVec, matPA_mulVec_single,
      matPA_mulVec_single, Matrix.mulVec_sub, colPermMat_cycleFun_pow_mulVec_single,
      colPermMat_cycleFun_pow_mulVec_single]
    congr 1
    · congr 1; ext; simp [Nat.mod_eq_of_lt (by omega : m < n + 1)]
    · congr 1; ext; simp [Nat.add_comm 1 m, Nat.mod_eq_of_lt (by omega : m + 1 < n + 1)]
  have h1 := congrArg (leftInvPA n *ᵥ ·) hcol
  rwa [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, leftInvPA_mul_matPA, Matrix.one_mul,
    Matrix.mulVec_mulVec, leftInvPA_mul_matPA, Matrix.one_mulVec] at h1

private lemma sum_coxA_pow_eq_zero (n : ℕ) :
    (∑ m ∈ Finset.range (n + 1), coxA n ^ m) = 0 := by
  apply matPA_left_injective
  rw [Matrix.mul_zero, Matrix.mul_sum]
  simp_rw [mul_pow_of_intertwine (matPA_mul_coxA n), ← Matrix.sum_mul]
  set C := colPermMat (cycleFun n)
  have hgeom : (∑ m ∈ Finset.range (n + 1), C ^ m) * (1 - C) = 0 := by
    rw [geom_sum_mul_neg, colPermMat_cycleFun_pow_self, sub_self]
  ext r j
  have hcol : matPA n *ᵥ Pi.single j 1 = (1 - C) *ᵥ Pi.single ⟨j.val, by omega⟩ 1 := by
    rw [matPA_mulVec_single, Matrix.sub_mulVec, Matrix.one_mulVec, colPermMat_mulVec_single]
    congr 2; ext; simp [cycleFun_apply, Nat.mod_eq_of_lt (by omega : j.val + 1 < n + 1)]
  have h0 : (((∑ m ∈ Finset.range (n + 1), C ^ m) * matPA n) *ᵥ Pi.single j 1) r = 0 := by
    rw [← Matrix.mulVec_mulVec, hcol, Matrix.mulVec_mulVec, hgeom, Matrix.zero_mulVec,
      Pi.zero_apply]
  simpa [Matrix.mulVec_single] using h0

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
        refine (Polynomial.degree_sum_le (Finset.range n) _).trans_lt ?_
        refine (Finset.sup_lt_iff (WithBot.bot_lt_coe n)).mpr fun k hk => ?_
        rw [degree_X_pow]
        exact WithBot.coe_lt_coe.2 (Finset.mem_range.mp hk)
    exact charpoly_eq_of_isMonicOfDegree_of_cyclic hn hmon (by simpa using sum_coxA_pow_eq_zero n)
      (coxA_pow_mulVec_single_zero hn)

/-- **The Coxeter number of `Aₙ` is `n + 1`**: the Coxeter element of type `Aₙ` has order
`n + 1`. -/
theorem orderOf_coxA (n : ℕ) : orderOf (coxA n) = n + 1 := by
  rcases n.eq_zero_or_pos with rfl | hn
  · exact orderOf_eq_one_iff.mpr (Subsingleton.elim _ _)
  · have hpow : coxA n ^ (n + 1) = 1 := by
      have hgeom := geom_sum_mul (coxA n) (n + 1)
      rw [sum_coxA_pow_eq_zero, zero_mul] at hgeom
      exact sub_eq_zero.mp hgeom.symm
    refine (orderOf_eq_iff (Nat.succ_pos n)).mpr ⟨hpow, fun m hm hpos h1 => ?_⟩
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hm) with hmn | hmn
    · have hv := congrFun (coxA_pow_mulVec_single_zero hn m hmn) ⟨0, hn⟩
      simp [h1, Fin.ext_iff, hpos.ne'] at hv
    · rw [hmn] at h1
      have hc1 : coxA n = 1 := by simpa [pow_succ, h1] using hpow
      have hsum := congrFun₂ (sum_coxA_pow_eq_zero n) ⟨0, hn⟩ ⟨0, hn⟩
      simp [hc1] at hsum
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
  by_cases hj : j.val + 1 < n
  · simp [Matrix.mulVec_single, negCycleMatrix, hj, Pi.single_apply, Fin.ext_iff]
  · by_cases hr : r.val = 0 <;>
      simp [Matrix.mulVec_single, negCycleMatrix, hj, hr, Pi.single_apply, Fin.ext_iff]

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
    rw [pow_add, pow_add, pow_one, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      negCycleMatrix_pow_mulVec_single j (n - 1 - j.val) (by have := j.isLt; omega),
      negCycleMatrix_mulVec_single,
      dite_eq_right_of_eq_false (eq_false (by have := j.isLt; simp; omega)),
      Matrix.mulVec_neg, negCycleMatrix_pow_mulVec_single ⟨0, by omega⟩ j.val (by simp)]
    simp [Matrix.one_apply, Pi.single_apply, Fin.ext_iff]
  have hsplit : j.val + (1 + (n - 1 - j.val)) = n := by have := j.isLt; omega
  rw [hsplit] at hpow
  simpa [Matrix.mulVec_single] using hpow

private lemma charpoly_negCycleMatrix {n : ℕ} (hn : 1 ≤ n) :
    (negCycleMatrix n).charpoly = X ^ n + 1 := by
  have hmon : ((X : ℤ[X]) ^ n + 1).IsMonicOfDegree n :=
    (isMonicOfDegree_X_pow ℤ n).add_right (by simpa using Nat.pos_of_ne_zero (by omega))
  refine charpoly_eq_of_isMonicOfDegree_of_cyclic (by omega) hmon
    (by simp [negCycleMatrix_pow_self hn]) fun m hm => ?_
  simpa using negCycleMatrix_pow_mulVec_single (⟨0, by omega⟩ : Fin n) m (by simpa using hm)

private lemma orderOf_negCycleMatrix {n : ℕ} (hn : 1 ≤ n) :
    orderOf (negCycleMatrix n) = 2 * n := by
  refine (orderOf_eq_iff (by omega)).2 ⟨?_, fun m hm hpos h1 => ?_⟩
  · rw [mul_comm, pow_mul, negCycleMatrix_pow_self hn, neg_one_sq]
  · rcases lt_trichotomy m n with hlt | rfl | hgt
    · have hv := congrFun (negCycleMatrix_pow_mulVec_single (⟨0, by omega⟩ : Fin n) m
        (by simpa using hlt)) ⟨0, by omega⟩
      simp [h1, Fin.ext_iff, hpos.ne'] at hv
    · have h0 := congrFun₂ (negCycleMatrix_pow_self hn ▸ h1) ⟨0, by omega⟩ ⟨0, by omega⟩
      simp at h0
    · have hneg1 : negCycleMatrix n ^ (m - n) = -1 := by
        rw [show m = n + (m - n) by omega, pow_add, negCycleMatrix_pow_self hn, neg_one_mul] at h1
        exact neg_eq_iff_eq_neg.mp h1
      have hv := congrFun (negCycleMatrix_pow_mulVec_single (⟨0, by omega⟩ : Fin n) (m - n)
        (by simp; omega)) ⟨0, by omega⟩
      simp [hneg1, Fin.ext_iff, show m - n ≠ 0 by omega] at hv

/-! ### Type `Bₙ`: lower-unitriangular conjugation to the signed `n`-cycle -/

/-- The `n × n` lower-unitriangular matrix with columns `e₀ - e₁, …, eₙ₋₂ - eₙ₋₁, eₙ₋₁`. -/
private def matPB (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun r j =>
    if j.val + 1 < n then
      (if r.val = j.val then 1 else 0) - (if r.val = j.val + 1 then 1 else 0)
    else
      if r = j then 1 else 0

private lemma det_matPB (n : ℕ) : (matPB n).det = 1 := by
  have htri : (matPB n).IsLowerTriangular := fun i j hij => by
    have hlt : i.val < j.val := Fin.lt_def.mp hij
    simp only [matPB, Matrix.of_apply, Fin.ext_iff]; split_ifs <;> omega
  rw [Matrix.det_of_isLowerTriangular _ htri]
  refine Finset.prod_eq_one fun i _ => ?_
  simp only [matPB, Matrix.of_apply]; split_ifs <;> omega

/-- Coordinate simple reflections of type `Bₙ`: adjacent swaps for `i < n - 1`, and negation of the
last coordinate for `i = n - 1`. -/
private def reflCoordB (n : ℕ) (i : Fin n) : Matrix (Fin n) (Fin n) ℤ :=
  if hi : i.val + 1 < n then colPermMat (adjSwapFun n i.val hi)
  else Matrix.diagonal fun r : Fin n => if r.val + 1 = n then -1 else 1

private lemma matPB_mul_reflMatrix (n : ℕ) (i : Fin n) :
    matPB n * reflMatrix (CartanMatrix.B n) i = reflCoordB n i * matPB n := by
  ext r j
  rw [mul_reflMatrix_apply]
  have := r.isLt; have := j.isLt; have := i.isLt
  by_cases hi : i.val + 1 < n
  · rw [reflCoordB, dite_eq_left_of_eq_true (eq_true hi),
      colPermMat_mul_apply_of_involutive (involutive_adjSwapFun n i.val hi)]
    simp only [matPB, CartanMatrix.B, Matrix.of_apply, val_adjSwapFun, Fin.ext_iff]
    split_ifs <;> omega
  · rw [reflCoordB, dite_eq_right_of_eq_false (eq_false hi), Matrix.diagonal_mul]
    simp only [matPB, CartanMatrix.B, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> omega

private lemma matPB_mul_coxB {n : ℕ} (hn : 1 ≤ n) :
    matPB n * coxB n = negCycleMatrix n * matPB n := by
  rw [coxB, mul_coxeterElement (matPB n) (CartanMatrix.B n) (reflCoordB n) (matPB_mul_reflMatrix n)]
  congr 1
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [prod_finRange_succ_adjSwap (reflCoordB (m + 1)) fun i => by
    simp [reflCoordB, Nat.add_lt_add_right i.isLt 1]]
  ext r j
  have := r.isLt; have := j.isLt
  simp only [reflCoordB, Fin.val_last, lt_self_iff_false, ↓reduceDIte, Matrix.mul_diagonal,
    colPermMat, negCycleMatrix, Matrix.of_apply, Fin.ext_iff, val_cyclePrefixFun]
  split_ifs <;> omega

/-- **The characteristic polynomial of the `Bₙ` Coxeter element is `X^n + 1`** (`1 ≤ n`). -/
theorem charpoly_coxB {n : ℕ} (hn : 1 ≤ n) : (coxB n).charpoly = X ^ n + 1 :=
  (charpoly_and_orderOf_of_intertwine (by rw [det_matPB]; norm_num) (matPB_mul_coxB hn)).1.trans
    (charpoly_negCycleMatrix hn)

/-- **The Coxeter number of `Bₙ` is `2 n`** (`1 ≤ n`): the Coxeter element of type `Bₙ` has order
`2 n`. -/
theorem orderOf_coxB {n : ℕ} (hn : 1 ≤ n) : orderOf (coxB n) = 2 * n :=
  (charpoly_and_orderOf_of_intertwine (by rw [det_matPB]; norm_num) (matPB_mul_coxB hn)).2.trans
    (orderOf_negCycleMatrix hn)

/-! ### Type `Cₙ`: diagonal conjugation to type `Bₙ` -/

/-- The diagonal matrix `diag(1, …, 1, 2)` intertwining `coxC n` with `coxB n`. -/
private def diagBC (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.diagonal fun k : Fin n => if k.val + 1 = n then 2 else 1

private lemma det_diagBC_ne_zero (n : ℕ) : (diagBC n).det ≠ 0 := by
  rw [diagBC, Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr fun k _ => by split_ifs <;> norm_num

private lemma diagBC_mul_reflMatrix (n : ℕ) (i : Fin n) :
    diagBC n * reflMatrix (CartanMatrix.C n) i = reflMatrix (CartanMatrix.B n) i * diagBC n := by
  ext r j
  rw [diagBC, Matrix.diagonal_mul, Matrix.mul_diagonal]
  have := r.isLt; have := j.isLt; have := i.isLt
  simp only [reflMatrix_apply, CartanMatrix.B, CartanMatrix.C, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> omega

private lemma diagBC_mul_coxC (n : ℕ) : diagBC n * coxC n = coxB n * diagBC n :=
  mul_coxeterElement (diagBC n) (CartanMatrix.C n) (reflMatrix (CartanMatrix.B n))
    (diagBC_mul_reflMatrix n)

/-- **The characteristic polynomial of the `Cₙ` Coxeter element is `X^n + 1`** (`1 ≤ n`). -/
theorem charpoly_coxC {n : ℕ} (hn : 1 ≤ n) : (coxC n).charpoly = X ^ n + 1 :=
  (charpoly_and_orderOf_of_intertwine (det_diagBC_ne_zero n) (diagBC_mul_coxC n)).1.trans
    (charpoly_coxB hn)

/-- **The Coxeter number of `Cₙ` is `2 n`** (`1 ≤ n`): the Coxeter element of type `Cₙ` has order
`2 n`. -/
theorem orderOf_coxC {n : ℕ} (hn : 1 ≤ n) : orderOf (coxC n) = 2 * n :=
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
    if j.val + 1 < n then if k = j then 1 else 0
    else (if k.val + 2 = n then 1 else 0) + (if k.val + 1 = n then 2 else 0)

private lemma matPB_mul_upperUD {n : ℕ} (hn : 2 ≤ n) : matPB n * upperUD n = matPD n := by
  ext r j
  rw [Matrix.mul_apply]
  by_cases hj : j.val + 1 < n
  · rw [Finset.sum_eq_single j]
    · simp [matPB, upperUD, matPD, hj]
    · intro k _ hkj; simp [upperUD, hj, hkj]
    · intro h; exact absurd (Finset.mem_univ _) h
  · have h1 : ∀ k : Fin n, (k.val + 2 = n) ↔ k = ⟨n - 2, by omega⟩ := fun k => by
      simp only [Fin.ext_iff]; omega
    have h2 : ∀ k : Fin n, (k.val + 1 = n) ↔ k = ⟨n - 1, by omega⟩ := fun k => by
      simp only [Fin.ext_iff]; omega
    simp only [upperUD, Matrix.of_apply, hj, ↓reduceIte, mul_add, Finset.sum_add_distrib,
      h1, h2, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ]
    have := r.isLt; have := j.isLt
    simp only [matPB, matPD, Matrix.of_apply, hj, ↓reduceIte, Fin.ext_iff]
    split_ifs <;> omega

private lemma det_matPD {n : ℕ} (hn : 2 ≤ n) : (matPD n).det = 2 := by
  rw [← matPB_mul_upperUD hn, Matrix.det_mul, det_matPB, one_mul]
  have htri : (upperUD n).IsUpperTriangular := fun i j hij => by
    have hlt : j.val < i.val := Fin.lt_def.mp hij
    have := i.isLt
    simp only [upperUD, Matrix.of_apply, Fin.ext_iff]; split_ifs <;> omega
  rw [Matrix.det_of_isUpperTriangular htri]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Fin.prod_univ_castSucc, Finset.prod_eq_one fun i _ => by simp [upperUD], one_mul]
  simp only [upperUD, Matrix.of_apply, Fin.val_last]; split_ifs <;> omega

private lemma cartanMatrixD_apply_of_lt {n : ℕ} {i : Fin n} (hi : i.val + 1 < n) (j : Fin n) :
    CartanMatrix.D n j i =
      if j = i then 2
      else if n ≤ 2 then 0
      else if j.val + 1 < n then
        if j.val + 1 = i.val ∨ (i.val + 1 = j.val ∧ i.val + 2 < n) then -1 else 0
      else
        if i.val + 3 = n then -1 else 0 := by
  have := j.isLt
  simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]; split_ifs <;> omega

private lemma cartanMatrixD_apply_of_not_lt {n : ℕ} {i : Fin n} (hi : ¬ i.val + 1 < n)
    (j : Fin n) :
    CartanMatrix.D n j i =
      if j = i then 2 else if n ≤ 2 then 0 else if j.val + 3 = n then -1 else 0 := by
  have := i.isLt; have := j.isLt
  simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]; split_ifs <;> omega

/-- Diagonal sign matrix negating the last two coordinates `n - 2` and `n - 1`. -/
private def negLastTwo (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.diagonal fun r : Fin n => if n ≤ r.val + 2 then -1 else 1

/-- The last reflection of `Dₙ` in standard coordinates sends `eₙ₋₂ ↦ -eₙ₋₁`, `eₙ₋₁ ↦ -eₙ₋₂`, and
fixes `eᵣ` for `r < n - 2`. -/
private def lastReflD {n : ℕ} (hn : 2 ≤ n) : Matrix (Fin n) (Fin n) ℤ :=
  negLastTwo n * colPermMat (adjSwapFun n (n - 2) (by omega))

private lemma lastReflD_mul_apply {n : ℕ} (hn : 2 ≤ n) {κ : Type*} (M : Matrix (Fin n) κ ℤ)
    (r : Fin n) (j : κ) :
    (lastReflD hn * M) r j =
      if r.val + 1 = n then -M ⟨n - 2, by omega⟩ j
      else if r.val + 2 = n then -M ⟨n - 1, by omega⟩ j
      else M r j := by
  rw [lastReflD, Matrix.mul_assoc, negLastTwo, Matrix.diagonal_mul,
    colPermMat_mul_apply_of_involutive (involutive_adjSwapFun n (n - 2) (by omega))]
  have := r.isLt
  have hswap : adjSwapFun n (n - 2) (by omega) r =
      if r.val + 1 = n then ⟨n - 2, by omega⟩
      else if r.val + 2 = n then ⟨n - 1, by omega⟩
      else r := Fin.ext <| by simp only [val_adjSwapFun, apply_ite Fin.val]; split_ifs <;> omega
  rw [hswap]
  split_ifs <;> simp <;> omega

private lemma lastReflD_eq_swap_mul_diag {n : ℕ} (hn : 2 ≤ n) :
    lastReflD hn = colPermMat (adjSwapFun n (n - 2) (by omega)) * negLastTwo n := by
  ext r j
  have := r.isLt; have := j.isLt
  simp only [lastReflD, negLastTwo, Matrix.diagonal_mul, Matrix.mul_diagonal, colPermMat,
    Matrix.of_apply, Fin.ext_iff, val_adjSwapFun]
  split_ifs <;> omega

/-- Coordinate simple reflections of type `Dₙ`. -/
private def reflCoordD {n : ℕ} (hn : 2 ≤ n) (i : Fin n) : Matrix (Fin n) (Fin n) ℤ :=
  if hi : i.val + 1 < n then colPermMat (adjSwapFun n i.val hi) else lastReflD hn

private lemma matPD_mul_reflMatrix {n : ℕ} (hn : 2 ≤ n) (i : Fin n) :
    matPD n * reflMatrix (CartanMatrix.D n) i = reflCoordD hn i * matPD n := by
  ext r j
  rw [mul_reflMatrix_apply]
  have := r.isLt; have := j.isLt; have := i.isLt
  by_cases hi : i.val + 1 < n
  · rw [reflCoordD, dite_eq_left_of_eq_true (eq_true hi),
      colPermMat_mul_apply_of_involutive (involutive_adjSwapFun n i.val hi),
      cartanMatrixD_apply_of_lt hi j]
    by_cases hj : j.val + 1 < n
    · rcases eq_or_ne j i with rfl | hji
      · simp only [↓reduceIte, matPD, Matrix.of_apply, hi, val_adjSwapFun]
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

private lemma colPermMat_cyclePrefix_mul_lastReflD {m : ℕ} (hm : 1 ≤ m) :
    colPermMat (cyclePrefixFun (m + 1) m (Nat.lt_succ_self m)) *
      lastReflD (n := m + 1) (by omega) = modelDSucc m := by
  rw [lastReflD_eq_swap_mul_diag, ← Matrix.mul_assoc, colPermMat_mul]
  ext r j
  rw [negLastTwo, Matrix.mul_diagonal]
  refine Fin.lastCases ?_ (fun r₀ => ?_) r <;> refine Fin.lastCases ?_ (fun j₀ => ?_) j <;>
    simp only [modelDSucc, Matrix.reindex_apply, Matrix.submatrix_apply, blockModelD,
      finSumFinEquiv_symm_last, finSumFinEquiv_symm_apply_castSucc,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.neg_apply, Matrix.one_apply_eq, Matrix.zero_apply,
      negCycleMatrix, colPermMat, Matrix.of_apply, Function.comp_apply, Fin.ext_iff,
      Fin.val_last, Fin.val_castSucc, val_cyclePrefixFun, val_adjSwapFun] <;>
    (try have := r₀.isLt) <;> (try have := j₀.isLt) <;> split_ifs <;> omega

private lemma matPD_mul_coxD_succ {m : ℕ} (hm : 1 ≤ m) :
    matPD (m + 1) * coxD (m + 1) = modelDSucc m * matPD (m + 1) := by
  rw [coxD, mul_coxeterElement (matPD (m + 1)) (CartanMatrix.D (m + 1))
    (reflCoordD (by omega)) (matPD_mul_reflMatrix (by omega))]
  congr 1
  rw [prod_finRange_succ_adjSwap (reflCoordD (by omega)) fun i => by
    simp [reflCoordD, Nat.add_lt_add_right i.isLt 1]]
  simpa [reflCoordD] using colPermMat_cyclePrefix_mul_lastReflD hm

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
  have he : orderOf (modelDSucc m) = orderOf (blockModelD m) :=
    (Matrix.reindexAlgEquiv ℤ ℤ e).toMulEquiv.orderOf_eq (blockModelD m)
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
theorem orderOf_coxD {n : ℕ} (hn : 2 ≤ n) : orderOf (coxD n) = 2 * (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : 1 ≤ m := by omega
  have h := charpoly_and_orderOf_of_intertwine (by rw [det_matPD hn]; norm_num)
    (matPD_mul_coxD_succ hm)
  simpa using h.2.trans (orderOf_modelDSucc hm)

end TauCeti.Coxeter

end
