/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.List.OneDegenerateOrder
public import TauCeti.LinearAlgebra.Matrix.Cartan.Coxeter.Basic
public import TauCeti.LinearAlgebra.Matrix.Charpoly.Companion
import Mathlib.Data.List.FinRange
import TauCeti.Algebra.BigOperators.Group.List
import TauCeti.LinearAlgebra.Matrix.Block
import TauCeti.LinearAlgebra.Matrix.Charpoly.Semiconj

/-!
# Coxeter elements of the classical Cartan matrices

This file computes the characteristic polynomial and multiplicative order of `Matrix.coxeterElement`
for the four classical Cartan families `Aₙ`, `Bₙ`, `Cₙ`, and `Dₙ`, and shows that `List.finRange n`
is a one-degenerate order of each classical Dynkin diagram:

* `Aₙ`: `coxeterElement = companion (fun _ => 1)`, `charpoly = ∑_{k=0}^n X^k`, `h = n + 1`.
* `Bₙ`, `Cₙ` (`0 < n`): intertwined with `companion (Pi.single 0 1)`, `charpoly = X^n + 1`,
  `h = 2n`.
* `Dₙ` (`2 ≤ n`): intertwined with `blockDiag(companion (Pi.single 0 1), -1)`,
  `charpoly = (X^{n-1} + 1)(X + 1)`, `h = 2n - 2`.

## Main results

* `TauCeti.Coxeter.isOneDegenerateOrder_A`, `isOneDegenerateOrder_B`, `isOneDegenerateOrder_C`,
  `isOneDegenerateOrder_D`.
* `TauCeti.Coxeter.coxeterElement_A`, `charpoly_coxeterElement_A`, `orderOf_coxeterElement_A`.
* `TauCeti.Coxeter.charpoly_coxeterElement_B`, `orderOf_coxeterElement_B`.
* `TauCeti.Coxeter.charpoly_coxeterElement_C`, `orderOf_coxeterElement_C`.
* `TauCeti.Coxeter.charpoly_coxeterElement_D`, `orderOf_coxeterElement_D`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. V, §6, and Plates I--IV.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge University Press (1990),
  §§ 3.16–3.20.
-/

public section

open Matrix Polynomial

namespace TauCeti.Coxeter

/-! ### One-degenerate orders of the classical diagrams -/

private theorem isOneDegenerateOrder_finRange_of_lt {n : ℕ} {adj : Fin n → Fin n → Prop}
    (h : ∀ z x y : Fin n, (x : ℕ) < (z : ℕ) → (y : ℕ) < (z : ℕ) → adj z x → adj z y → x = y) :
    List.IsOneDegenerateOrder adj (List.finRange n) := by
  rw [List.isOneDegenerateOrder_iff]
  intro S₁ z S₂ hS x hx y hy hzx hzy
  have hnd : (S₁ ++ z :: S₂).Nodup := hS ▸ List.nodup_finRange n
  have hzS₁ : z ∉ S₁ := fun hz => (List.nodup_append.1 hnd).2.2 z hz z List.mem_cons_self rfl
  have hlt : ∀ u ∈ S₁, (u : ℕ) < (z : ℕ) := fun u hu => by
    have hu_idx :=
      (List.idxOf_finRange u).symm.trans (by rw [hS, List.idxOf_append, ite_eq_left hu])
    have hz_idx :=
      (List.idxOf_finRange z).symm.trans (by rw [hS, List.idxOf_append, ite_eq_right hzS₁])
    have := List.idxOf_lt_length_of_mem hu; omega
  exact h z x y (hlt x hx) (hlt y hy) hzx hzy

/-- `List.finRange n` is a one-degenerate order of the Dynkin diagram of type `Aₙ`. -/
theorem isOneDegenerateOrder_A (n : ℕ) :
    List.IsOneDegenerateOrder (fun i j : Fin n => CartanMatrix.A n i j ≠ 0) (List.finRange n) := by
  refine isOneDegenerateOrder_finRange_of_lt fun z x y hxz hyz hzx hzy => ?_
  simp only [CartanMatrix.A, of_apply, ne_eq, Fin.ext_iff] at hzx hzy
  apply Fin.ext; split_ifs at hzx hzy <;> omega

/-- `List.finRange n` is a one-degenerate order of the Dynkin diagram of type `Bₙ`. -/
theorem isOneDegenerateOrder_B (n : ℕ) :
    List.IsOneDegenerateOrder (fun i j : Fin n => CartanMatrix.B n i j ≠ 0) (List.finRange n) := by
  refine isOneDegenerateOrder_finRange_of_lt fun z x y hxz hyz hzx hzy => ?_
  simp only [CartanMatrix.B, of_apply, ne_eq, Fin.ext_iff] at hzx hzy
  apply Fin.ext; split_ifs at hzx hzy <;> omega

/-- `List.finRange n` is a one-degenerate order of the Dynkin diagram of type `Cₙ`. -/
theorem isOneDegenerateOrder_C (n : ℕ) :
    List.IsOneDegenerateOrder (fun i j : Fin n => CartanMatrix.C n i j ≠ 0) (List.finRange n) := by
  refine isOneDegenerateOrder_finRange_of_lt fun z x y hxz hyz hzx hzy => ?_
  simp only [CartanMatrix.C, of_apply, ne_eq, Fin.ext_iff] at hzx hzy
  apply Fin.ext; split_ifs at hzx hzy <;> omega

/-- `List.finRange n` is a one-degenerate order of the Dynkin diagram of type `Dₙ`. -/
theorem isOneDegenerateOrder_D (n : ℕ) :
    List.IsOneDegenerateOrder (fun i j : Fin n => CartanMatrix.D n i j ≠ 0) (List.finRange n) := by
  refine isOneDegenerateOrder_finRange_of_lt fun z x y hxz hyz hzx hzy => ?_
  have _ : (z : ℕ) < n := z.isLt
  simp only [CartanMatrix.D, of_apply, ne_eq, Fin.ext_iff] at hzx hzy
  apply Fin.ext; split_ifs at hzx hzy <;> omega

/-! ### Prefix-product and intertwining helpers -/

private theorem ext_of_mulVec_single_one {m n R : Type*} [Fintype n] [DecidableEq n]
    [NonAssocSemiring R] {A B : Matrix m n R}
    (h : ∀ j, A *ᵥ Pi.single j 1 = B *ᵥ Pi.single j 1) : A = B :=
  ext_col fun j => by rw [← mulVec_single_one, ← mulVec_single_one, h j]

private theorem take_finRange_succ {n m : ℕ} (hm : m < n) :
    (List.finRange n).take (m + 1) = (List.finRange n).take m ++ [⟨m, hm⟩] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by simp [hm])]; simp

private theorem take_finRange_self (n : ℕ) :
    (List.finRange n).take n = List.finRange n :=
  List.take_of_length_le (by simp)

private theorem reflMatrix_mulVec_single {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) :
    reflMatrix A i *ᵥ Pi.single j 1 = Pi.single j 1 - A j i • Pi.single i 1 := by
  ext k; rw [mulVec_single_one, col_apply, reflMatrix_apply]; simp [Pi.single_apply, eq_comm]

private theorem mul_reflMatrix_apply {n : ℕ} (V A : Matrix (Fin n) (Fin n) ℤ) (i r j : Fin n) :
    (V * reflMatrix A i) r j = V r j - V r i * A j i := by
  rw [Matrix.mul_apply]
  simp only [reflMatrix_apply, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq', Finset.sum_ite_eq']; simp

private theorem charpoly_and_orderOf_eq_of_semiconjBy {n : ℕ}
    {V M G : Matrix (Fin n) (Fin n) ℤ} (h : SemiconjBy V M G)
    {U : Matrix (Fin n) (Fin n) ℚ} (hUV : U * V.map (Int.castRingHom ℚ) = 1) :
    M.charpoly = G.charpoly ∧ orderOf M = orderOf G :=
  ⟨charpoly_eq_of_semiconjBy h (Int.castRingHom ℚ).injective_int hUV,
   orderOf_eq_of_semiconjBy h (Int.castRingHom ℚ).injective_int hUV⟩

/-! ### Type `Aₙ` -/

private def aPrefixVec (n m : ℕ) (j k : Fin n) : ℤ :=
  if (j : ℕ) + 1 < m then (if (k : ℕ) = (j : ℕ) + 1 then 1 else 0)
  else if (j : ℕ) + 1 = m then (if (k : ℕ) < m then -1 else 0)
  else if (j : ℕ) = m then (if (k : ℕ) ≤ m then 1 else 0)
  else if k = j then 1 else 0

private theorem prod_take_reflMatrix_A_mulVec_single (n : ℕ) {m : ℕ} (hm : m ≤ n) (j : Fin n) :
    (((List.finRange n).take m).map (reflMatrix (CartanMatrix.A n))).prod *ᵥ Pi.single j 1 =
      aPrefixVec n m j := by
  induction m generalizing j with
  | zero =>
    rw [List.take_zero, List.map_nil, List.prod_nil, one_mulVec]; ext k
    rw [Pi.single_apply]; simp only [aPrefixVec, Fin.ext_iff]; grind
  | succ m ih =>
    have hmlt : m < n := by omega
    rw [take_finRange_succ hmlt, List.map_append, List.map_singleton, List.prod_append,
      List.prod_singleton, ← mulVec_mulVec, reflMatrix_mulVec_single, mulVec_sub, mulVec_smul,
      ih (by omega), ih (by omega)]
    ext k; rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      show aPrefixVec n m ⟨m, hmlt⟩ k = if (k : ℕ) ≤ m then 1 else 0 by simp [aPrefixVec]]
    have _ := k.isLt; have _ := j.isLt
    simp only [CartanMatrix.A, of_apply, aPrefixVec, Fin.ext_iff]; grind

/-- **In the simple-root basis, the Coxeter element of `CartanMatrix.A n` is the all-ones companion
matrix.** -/
theorem coxeterElement_A (n : ℕ) :
    coxeterElement (CartanMatrix.A n) = companion (fun _ : Fin n => (1 : ℤ)) := by
  ext k j
  have h := congrFun (prod_take_reflMatrix_A_mulVec_single n le_rfl j) k
  rw [take_finRange_self, ← coxeterElement, mulVec_single_one, col_apply] at h
  rw [h, companion_apply]; simp only [aPrefixVec]
  have _ := j.isLt; have _ := k.isLt; split_ifs <;> omega

/-- **The characteristic polynomial of the `Aₙ` Coxeter element is `∑_{k=0}^n X^k`.** -/
theorem charpoly_coxeterElement_A (n : ℕ) :
    (coxeterElement (CartanMatrix.A n)).charpoly = ∑ k ∈ Finset.range (n + 1), X ^ k := by
  rw [coxeterElement_A, charpoly_companion_const_one]

/-- **The Coxeter number of `Aₙ` (`0 < n`) is `n + 1`**: the Coxeter element has order `n + 1`. -/
theorem orderOf_coxeterElement_A {n : ℕ} (hn : 0 < n) :
    orderOf (coxeterElement (CartanMatrix.A n)) = n + 1 := by
  rw [coxeterElement_A]; exact orderOf_companion_const_one hn (by decide)

/-! ### Signed-permutation and adjacent-transposition helpers for `Bₙ` and `Dₙ` -/

private def signedPerm {n : ℕ} (σ : Equiv.Perm (Fin n)) (s : Fin n → ℤ) :
    Matrix (Fin n) (Fin n) ℤ :=
  of fun r c => if r = σ c then s c else 0

private theorem signedPerm_mulVec_single {n : ℕ} (σ : Equiv.Perm (Fin n)) (s : Fin n → ℤ)
    (j : Fin n) : signedPerm σ s *ᵥ Pi.single j 1 = s j • Pi.single (σ j) 1 := by
  ext r; rw [mulVec_single_one, col_apply, signedPerm, of_apply]
  rcases eq_or_ne r (σ j) with rfl | h <;> simp [*]

private theorem signedPerm_mul_apply {n : ℕ} (σ : Equiv.Perm (Fin n)) (s : Fin n → ℤ)
    (V : Matrix (Fin n) (Fin n) ℤ) (r j : Fin n) :
    (signedPerm σ s * V) r j = s (σ.symm r) * V (σ.symm r) j := by
  rw [Matrix.mul_apply, Fintype.sum_eq_single (σ.symm r)]
  · simp [signedPerm]
  · intro x hx; simp [signedPerm, show r ≠ σ x from fun h => hx (by rw [h, σ.symm_apply_apply])]

private abbrev swapMatrix {n : ℕ} (i₁ i₂ : Fin n) : Matrix (Fin n) (Fin n) ℤ :=
  signedPerm (Equiv.swap i₁ i₂) 1

private def swapPrefixVec {n : ℕ} (m : ℕ) (j k : Fin n) : ℤ :=
  if (j : ℕ) < m then (if (k : ℕ) = (j : ℕ) + 1 then 1 else 0)
  else if (j : ℕ) = m then (if (k : ℕ) = 0 then 1 else 0)
  else if k = j then 1 else 0

private theorem prod_take_swap_mulVec_single {n : ℕ} (g : Fin n → Matrix (Fin n) (Fin n) ℤ)
    {m : ℕ} (hm : m < n)
    (hg : ∀ (u : ℕ) (_hu : u < m) (hu1 : u + 1 < n),
      g ⟨u, by omega⟩ = swapMatrix ⟨u, by omega⟩ ⟨u + 1, hu1⟩)
    (j : Fin n) :
    (((List.finRange n).take m).map g).prod *ᵥ Pi.single j 1 = swapPrefixVec m j := by
  induction m generalizing j with
  | zero =>
    rw [List.take_zero, List.map_nil, List.prod_nil, one_mulVec]; ext k
    rw [Pi.single_apply]; simp only [swapPrefixVec, Fin.ext_iff]
    have _ := k.isLt; have _ := j.isLt; split_ifs <;> omega
  | succ m ih =>
    have hm0 : m < n := by omega
    rw [take_finRange_succ hm0, List.map_append, List.map_singleton, List.prod_append,
      List.prod_singleton, ← mulVec_mulVec, hg m (by omega) hm, signedPerm_mulVec_single,
      Pi.one_apply, one_smul, ih hm0 (fun u hu hu1 => hg u (by omega) hu1)]
    ext k; simp only [swapPrefixVec, Equiv.swap_apply_def, Fin.ext_iff]; grind

/-! ### Type `Bₙ` -/

private def basisB (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  of fun r j => (if r = j then 1 else 0) - (if (r : ℕ) = (j : ℕ) + 1 then 1 else 0)

private def invBasisB (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  of fun k i => if (i : ℕ) ≤ (k : ℕ) then 1 else 0

private theorem invBasisB_mul_basisB (n : ℕ) : invBasisB n * basisB n = 1 := by
  refine ext_of_mulVec_single_one fun j => ?_
  rw [← mulVec_mulVec, one_mulVec]
  rcases lt_or_ge ((j : ℕ) + 1) n with hj | hj
  · have hv : basisB n *ᵥ Pi.single j 1 = Pi.single j 1 - Pi.single ⟨(j : ℕ) + 1, hj⟩ 1 := by
      ext r; rw [mulVec_single_one, col_apply, basisB, of_apply]
      simp [Pi.single_apply, Fin.ext_iff]
    rw [hv, mulVec_sub, mulVec_single_one, mulVec_single_one]
    ext r; have _ := j.isLt; have _ := r.isLt
    simp only [Pi.sub_apply, col_apply, invBasisB, of_apply, Pi.single_apply, Fin.ext_iff]
    split_ifs <;> omega
  · have hv : basisB n *ᵥ Pi.single j 1 = Pi.single j 1 := by
      ext r; have _ := r.isLt; rw [mulVec_single_one, col_apply, basisB, of_apply]
      simp only [Pi.single_apply, Fin.ext_iff]; split_ifs <;> omega
    rw [hv, mulVec_single_one]
    ext r; have _ := j.isLt; have _ := r.isLt
    simp only [col_apply, invBasisB, of_apply, Pi.single_apply, Fin.ext_iff]
    split_ifs <;> omega

private abbrev signFlipLast (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  signedPerm 1 (fun c => if (c : ℕ) + 1 = n then -1 else 1)

private def reflStdB (n : ℕ) (i : Fin n) : Matrix (Fin n) (Fin n) ℤ :=
  if hi : (i : ℕ) + 1 < n then swapMatrix i ⟨(i : ℕ) + 1, hi⟩ else signFlipLast n

private theorem basisB_mul_reflMatrix_B (n : ℕ) (i : Fin n) :
    basisB n * reflMatrix (CartanMatrix.B n) i = reflStdB n i * basisB n := by
  ext r j; rw [mul_reflMatrix_apply, reflStdB]
  have _ := i.isLt; have _ := r.isLt; have _ := j.isLt
  rcases lt_or_ge ((i : ℕ) + 1) n with hi | hi
  · rw [dite_eq_left hi, signedPerm_mul_apply, Equiv.symm_swap, Pi.one_apply, one_mul]
    simp only [Equiv.swap_apply_def, basisB, CartanMatrix.B, of_apply, Fin.ext_iff]; grind
  · rw [dite_eq_right (by omega), signedPerm_mul_apply,
      show (1 : Equiv.Perm (Fin n)).symm = 1 from rfl, Equiv.Perm.one_apply]
    simp only [basisB, CartanMatrix.B, of_apply, Fin.ext_iff]; grind

private theorem prod_reflStdB_eq_companion {n : ℕ} (hn : 0 < n) :
    ((List.finRange n).map (reflStdB n)).prod = companion (Pi.single ⟨0, hn⟩ (1 : ℤ)) := by
  have hm : n - 1 < n := by omega
  have hlist : List.finRange n = (List.finRange n).take (n - 1) ++ [⟨n - 1, hm⟩] := by
    simpa [show n - 1 + 1 = n by omega, take_finRange_self] using take_finRange_succ hm
  refine ext_of_mulVec_single_one fun j => ?_
  conv_lhs => rw [hlist]
  rw [List.map_append, List.map_singleton, List.prod_append, List.prod_singleton,
    ← mulVec_mulVec, show reflStdB n ⟨n - 1, hm⟩ = signFlipLast n from
      dite_eq_right (by simp; omega),
    signedPerm_mulVec_single, Equiv.Perm.one_apply, mulVec_smul,
    prod_take_swap_mulVec_single (reflStdB n) hm (fun u _ hu1 => by simp [reflStdB, hu1]) j]
  rcases lt_or_ge ((j : ℕ) + 1) n with hj | hj
  · rw [ite_eq_right (by omega), one_smul, companion_mulVec_single_of_lt _ hj]
    ext r; simp only [swapPrefixVec, Pi.single_apply, Fin.ext_iff]; split_ifs <;> omega
  · have hjeq : (j : ℕ) + 1 = n := by have := j.isLt; omega
    rw [ite_eq_left hjeq, neg_one_smul, companion_mulVec_single_of_eq _ hjeq]
    ext r; simp only [Pi.neg_apply, swapPrefixVec, Pi.single_apply, Fin.ext_iff]
    split_ifs <;> omega

private theorem charpoly_and_orderOf_B {n : ℕ} (hn : 0 < n) :
    (coxeterElement (CartanMatrix.B n)).charpoly =
        (companion (Pi.single ⟨0, hn⟩ (1 : ℤ))).charpoly ∧
      orderOf (coxeterElement (CartanMatrix.B n)) =
        orderOf (companion (Pi.single ⟨0, hn⟩ (1 : ℤ))) :=
  charpoly_and_orderOf_eq_of_semiconjBy
    (by rw [coxeterElement, ← prod_reflStdB_eq_companion hn]
        exact SemiconjBy.list_map_prod_right _ fun i _ => basisB_mul_reflMatrix_B n i)
    (U := (invBasisB n).map (Int.castRingHom ℚ))
    (by rw [← Matrix.map_mul, invBasisB_mul_basisB, Matrix.map_one _ (map_zero _) (map_one _)])

/-- **The characteristic polynomial of the `Bₙ` (`0 < n`) Coxeter element is `X^n + 1`.** -/
theorem charpoly_coxeterElement_B {n : ℕ} (hn : 0 < n) :
    (coxeterElement (CartanMatrix.B n)).charpoly = X ^ n + 1 := by
  rw [(charpoly_and_orderOf_B hn).1, charpoly_companion_single_zero hn 1, map_one]

/-- **The Coxeter number of `Bₙ` (`0 < n`) is `2 n`**: the Coxeter element has order `2 n`. -/
theorem orderOf_coxeterElement_B {n : ℕ} (hn : 0 < n) :
    orderOf (coxeterElement (CartanMatrix.B n)) = 2 * n := by
  rw [(charpoly_and_orderOf_B hn).2]; exact orderOf_companion_single_zero_one hn (by decide)

/-! ### Type `Cₙ` -/

private def diagBC (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  diagonal fun k : Fin n => if (k : ℕ) + 1 = n then 1 else 2

private theorem diagBC_mul_reflMatrix_B (n : ℕ) (i : Fin n) :
    diagBC n * reflMatrix (CartanMatrix.B n) i = reflMatrix (CartanMatrix.C n) i * diagBC n := by
  ext r j
  simp only [diagBC, diagonal_mul, mul_diagonal, reflMatrix_apply, CartanMatrix.B, CartanMatrix.C,
    of_apply, Fin.ext_iff]
  have _ := i.isLt; have _ := r.isLt; have _ := j.isLt; split_ifs <;> omega

private theorem charpoly_and_orderOf_C (n : ℕ) :
    (coxeterElement (CartanMatrix.B n)).charpoly =
        (coxeterElement (CartanMatrix.C n)).charpoly ∧
      orderOf (coxeterElement (CartanMatrix.B n)) =
        orderOf (coxeterElement (CartanMatrix.C n)) := by
  refine charpoly_and_orderOf_eq_of_semiconjBy
    (by rw [coxeterElement, coxeterElement]
        exact SemiconjBy.list_map_prod_right _ fun i _ => diagBC_mul_reflMatrix_B n i)
    (U := diagonal fun k : Fin n => if (k : ℕ) + 1 = n then (1 : ℚ) else 1 / 2) ?_
  rw [diagBC, diagonal_map (map_zero _), diagonal_mul_diagonal, ← diagonal_one]
  congr 1; ext k; split_ifs <;> norm_num

/-- **The characteristic polynomial of the `Cₙ` (`0 < n`) Coxeter element is `X^n + 1`.** -/
theorem charpoly_coxeterElement_C {n : ℕ} (hn : 0 < n) :
    (coxeterElement (CartanMatrix.C n)).charpoly = X ^ n + 1 := by
  rw [← (charpoly_and_orderOf_C n).1, charpoly_coxeterElement_B hn]

/-- **The Coxeter number of `Cₙ` (`0 < n`) is `2 n`**: the Coxeter element has order `2 n`. -/
theorem orderOf_coxeterElement_C {n : ℕ} (hn : 0 < n) :
    orderOf (coxeterElement (CartanMatrix.C n)) = 2 * n := by
  rw [← (charpoly_and_orderOf_C n).2, orderOf_coxeterElement_B hn]

/-! ### Type `Dₙ` (`2 ≤ n`) -/

private def basisD (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  of fun r j =>
    if (j : ℕ) + 1 < n then
      (if r = j then 1 else 0) - (if (r : ℕ) = (j : ℕ) + 1 then 1 else 0)
    else
      (if (r : ℕ) + 2 = n then 1 else 0) + (if (r : ℕ) + 1 = n then 1 else 0)

private def twiceInvBasisD (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  of fun k i =>
    if (i : ℕ) + 1 < n then
      if (k : ℕ) + 2 < n then (if (i : ℕ) ≤ (k : ℕ) then 2 else 0) else 1
    else
      if (k : ℕ) + 2 = n then -1 else if (k : ℕ) + 1 = n then 1 else 0

private theorem twiceInvBasisD_mul_basisD {n : ℕ} (hn : 2 ≤ n) :
    twiceInvBasisD n * basisD n = (2 : ℤ) • 1 := by
  refine ext_of_mulVec_single_one fun j => ?_
  rw [← mulVec_mulVec, smul_mulVec, one_mulVec]
  rcases lt_or_ge ((j : ℕ) + 1) n with hj | hj
  · have hv : basisD n *ᵥ Pi.single j 1 = Pi.single j 1 - Pi.single ⟨(j : ℕ) + 1, hj⟩ 1 := by
      ext r; rw [mulVec_single_one, col_apply, basisD, of_apply, ite_eq_left hj]
      simp [Pi.single_apply, Fin.ext_iff]
    rw [hv, mulVec_sub, mulVec_single_one, mulVec_single_one]
    ext r; have _ := j.isLt; have _ := r.isLt
    simp only [Pi.sub_apply, col_apply, twiceInvBasisD, of_apply, Pi.smul_apply, smul_eq_mul,
      Pi.single_apply, Fin.ext_iff]; split_ifs <;> omega
  · have hv : basisD n *ᵥ Pi.single j 1 =
        Pi.single ⟨n - 2, by omega⟩ 1 + Pi.single ⟨n - 1, by omega⟩ 1 := by
      ext r; have _ := r.isLt
      rw [mulVec_single_one, col_apply, basisD, of_apply, ite_eq_right (by omega)]
      simp only [Pi.add_apply, Pi.single_apply, Fin.ext_iff]; split_ifs <;> omega
    rw [hv, mulVec_add, mulVec_single_one, mulVec_single_one]
    ext r; have _ := j.isLt; have _ := r.isLt
    simp only [Pi.add_apply, col_apply, twiceInvBasisD, of_apply, Pi.smul_apply, smul_eq_mul,
      Pi.single_apply, Fin.ext_iff]; split_ifs <;> omega

private def negSwapLast {n : ℕ} (hn : 2 ≤ n) : Matrix (Fin n) (Fin n) ℤ :=
  signedPerm (Equiv.swap ⟨n - 2, by omega⟩ ⟨n - 1, by omega⟩)
    (fun c => if (c : ℕ) + 2 < n then 1 else -1)

private def reflStdD {n : ℕ} (hn : 2 ≤ n) (i : Fin n) : Matrix (Fin n) (Fin n) ℤ :=
  if hi : (i : ℕ) + 1 < n then swapMatrix i ⟨(i : ℕ) + 1, hi⟩ else negSwapLast hn

private theorem basisD_mul_reflMatrix_D {n : ℕ} (hn : 2 ≤ n) (i : Fin n) :
    basisD n * reflMatrix (CartanMatrix.D n) i = reflStdD hn i * basisD n := by
  have hm2 : n - 2 < n := by omega
  have hm1 : n - 1 < n := by omega
  ext r j; rw [mul_reflMatrix_apply, reflStdD]
  have _ := i.isLt; have _ := r.isLt; have _ := j.isLt
  rcases lt_or_ge ((i : ℕ) + 1) n with hi | hi
  · rw [dite_eq_left hi, signedPerm_mul_apply, Equiv.symm_swap, Pi.one_apply, one_mul]
    by_cases hj : (j : ℕ) + 1 < n <;> (
      rcases eq_or_ne r i with rfl | hr1
      · simp only [Equiv.swap_apply_left, basisD, CartanMatrix.D, of_apply, hj, ↓reduceIte,
          Fin.ext_iff]; grind
      · rcases eq_or_ne r ⟨(i : ℕ) + 1, hi⟩ with rfl | hr2
        · simp only [Equiv.swap_apply_right, basisD, CartanMatrix.D, of_apply, hj, ↓reduceIte,
            Fin.ext_iff]; grind
        · rw [Equiv.swap_apply_of_ne_of_ne hr1 hr2]
          simp only [basisD, CartanMatrix.D, of_apply, hj, ↓reduceIte, Fin.ext_iff] at hr1 hr2 ⊢
          grind)
  · have hni : ¬ ((i : ℕ) + 1 < n) := by omega
    rw [dite_eq_right hni, negSwapLast, signedPerm_mul_apply, Equiv.symm_swap]
    by_cases hj : (j : ℕ) + 1 < n <;> (
      rcases eq_or_ne r ⟨n - 2, hm2⟩ with rfl | hr1
      · simp only [Equiv.swap_apply_left, basisD, CartanMatrix.D, of_apply, hj, ↓reduceIte,
          Fin.ext_iff]; grind
      · rcases eq_or_ne r ⟨n - 1, hm1⟩ with rfl | hr2
        · simp only [Equiv.swap_apply_right, basisD, CartanMatrix.D, of_apply, hj, ↓reduceIte,
            Fin.ext_iff]; grind
        · rw [Equiv.swap_apply_of_ne_of_ne hr1 hr2]
          simp only [basisD, CartanMatrix.D, of_apply, hj, ↓reduceIte, Fin.ext_iff] at hr1 hr2 ⊢
          grind)

private abbrev splitEquivD {n : ℕ} (hn : 2 ≤ n) : Fin (n - 1) ⊕ Fin 1 ≃ Fin n :=
  finSumFinEquiv.trans (finCongr (by omega))

private theorem splitEquivD_symm_of_lt {n : ℕ} (hn : 2 ≤ n) (x : Fin n) (hx : (x : ℕ) < n - 1) :
    (splitEquivD hn).symm x = Sum.inl ⟨(x : ℕ), hx⟩ :=
  (splitEquivD hn).injective (by simp [splitEquivD, finSumFinEquiv_apply_left])

private theorem splitEquivD_symm_of_ge {n : ℕ} (hn : 2 ≤ n) (x : Fin n) (hx : n - 1 ≤ (x : ℕ)) :
    (splitEquivD hn).symm x = Sum.inr ⟨0, by omega⟩ :=
  (splitEquivD hn).injective
    (by have _ := x.isLt; ext; simp [splitEquivD, finSumFinEquiv_apply_right]; omega)

private def modelD {n : ℕ} (hn : 2 ≤ n) : Matrix (Fin n) (Fin n) ℤ :=
  reindex (splitEquivD hn) (splitEquivD hn)
    (fromBlocks (companion (Pi.single ⟨0, by omega⟩ (1 : ℤ))) 0 0 (-1 : Matrix (Fin 1) (Fin 1) ℤ))

private theorem modelD_apply {n : ℕ} (hn : 2 ≤ n) (r j : Fin n) :
    modelD hn r j =
      if (j : ℕ) + 2 < n then (if (r : ℕ) = (j : ℕ) + 1 then 1 else 0)
      else if (j : ℕ) + 2 = n then (if (r : ℕ) = 0 then -1 else 0)
      else if (r : ℕ) + 1 = n then -1 else 0 := by
  have _ := r.isLt; have _ := j.isLt
  simp only [modelD, reindex_apply, submatrix_apply]
  rcases lt_or_ge (r : ℕ) (n - 1) with hr | hr <;>
    rcases lt_or_ge (j : ℕ) (n - 1) with hj | hj
  · rw [splitEquivD_symm_of_lt hn r hr, splitEquivD_symm_of_lt hn j hj]
    simp only [fromBlocks_apply₁₁, companion_apply, Pi.single_apply, Fin.ext_iff]; grind
  · rw [splitEquivD_symm_of_lt hn r hr, splitEquivD_symm_of_ge hn j hj]
    simp only [fromBlocks_apply₁₂, Matrix.zero_apply]; grind
  · rw [splitEquivD_symm_of_ge hn r hr, splitEquivD_symm_of_lt hn j hj]
    simp only [fromBlocks_apply₂₁, Matrix.zero_apply]; grind
  · rw [splitEquivD_symm_of_ge hn r hr, splitEquivD_symm_of_ge hn j hj]
    simp only [fromBlocks_apply₂₂, Matrix.neg_apply, Matrix.one_apply_eq]; grind

private theorem prod_reflStdD_eq_modelD {n : ℕ} (hn : 2 ≤ n) :
    ((List.finRange n).map (reflStdD hn)).prod = modelD hn := by
  have hm2 : n - 2 < n := by omega
  have hm1 : n - 1 < n := by omega
  have hlist : List.finRange n =
      (List.finRange n).take (n - 2) ++ [⟨n - 2, hm2⟩, ⟨n - 1, hm1⟩] := by
    have h1 : List.finRange n = (List.finRange n).take (n - 1) ++ [⟨n - 1, hm1⟩] := by
      simpa [show (n - 1) + 1 = n by omega, take_finRange_self] using take_finRange_succ hm1
    have h2 : (List.finRange n).take (n - 1) =
        (List.finRange n).take (n - 2) ++ [⟨n - 2, hm2⟩] := by
      simpa [show (n - 2) + 1 = n - 1 by omega] using take_finRange_succ hm2
    (conv_lhs => rw [h1, h2, List.append_assoc]); rfl
  refine ext_of_mulVec_single_one fun j => ?_
  conv_lhs => rw [hlist]
  rw [List.map_append, List.prod_append]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Matrix.mul_one]
  have hpen : reflStdD hn ⟨n - 2, hm2⟩ = swapMatrix ⟨n - 2, hm2⟩ ⟨n - 1, hm1⟩ := by
    rw [reflStdD, dite_eq_left (by dsimp; omega)]; exact congrArg _ (Fin.ext (by dsimp; omega))
  rw [← mulVec_mulVec, ← mulVec_mulVec, hpen,
    show reflStdD hn ⟨n - 1, hm1⟩ = negSwapLast hn from dite_eq_right (by simp; omega),
    negSwapLast, signedPerm_mulVec_single, mulVec_smul, signedPerm_mulVec_single,
    Pi.one_apply, one_smul, Equiv.swap_apply_self, mulVec_smul,
    prod_take_swap_mulVec_single (reflStdD hn) hm2 (fun u _ hu1 => by simp [reflStdD, hu1]) j]
  ext r; rw [Pi.smul_apply, smul_eq_mul, mulVec_single_one, col_apply, modelD_apply hn]
  have _ := j.isLt; have _ := r.isLt; simp only [swapPrefixVec, Fin.ext_iff]; grind

private theorem charpoly_and_orderOf_D {n : ℕ} (hn : 2 ≤ n) :
    (coxeterElement (CartanMatrix.D n)).charpoly = (modelD hn).charpoly ∧
      orderOf (coxeterElement (CartanMatrix.D n)) = orderOf (modelD hn) := by
  refine charpoly_and_orderOf_eq_of_semiconjBy
    (by rw [coxeterElement, ← prod_reflStdD_eq_modelD hn]
        exact SemiconjBy.list_map_prod_right _ fun i _ => basisD_mul_reflMatrix_D hn i)
    (U := (1 / 2 : ℚ) • (twiceInvBasisD n).map (Int.castRingHom ℚ)) ?_
  rw [smul_mul_assoc, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← map_mul,
    twiceInvBasisD_mul_basisD hn, map_zsmul, map_one, two_zsmul, ← two_smul ℚ, smul_smul]
  norm_num

/-- **The characteristic polynomial of the `Dₙ` (`2 ≤ n`) Coxeter element is
`(X^{n-1} + 1)(X + 1)`.** -/
theorem charpoly_coxeterElement_D {n : ℕ} (hn : 2 ≤ n) :
    (coxeterElement (CartanMatrix.D n)).charpoly = (X ^ (n - 1) + 1) * (X + 1) := by
  rw [(charpoly_and_orderOf_D hn).1, modelD, charpoly_reindex, charpoly_fromBlocks_zero₁₂,
    charpoly_companion_single_zero (by omega) 1, map_one]
  congr 1; rw [Matrix.charpoly, det_fin_one]; simp [charmatrix]

/-- **The Coxeter number of `Dₙ` (`2 ≤ n`) is `2 n - 2`**: the Coxeter element has order
`2 n - 2`. -/
theorem orderOf_coxeterElement_D {n : ℕ} (hn : 2 ≤ n) :
    orderOf (coxeterElement (CartanMatrix.D n)) = 2 * n - 2 := by
  rw [(charpoly_and_orderOf_D hn).2, modelD, ← coe_reindexRingEquiv ℤ (splitEquivD hn),
    ← RingEquiv.coe_toMulEquiv, MulEquiv.orderOf_eq, orderOf_fromBlocks_zero_zero,
    orderOf_companion_single_zero_one (by omega) (by decide)]
  have h2 : orderOf (-1 : Matrix (Fin 1) (Fin 1) ℤ) = 2 := orderOf_eq_prime (by decide) (by decide)
  rw [h2, Nat.lcm_eq_left ⟨n - 1, rfl⟩]; omega

end TauCeti.Coxeter

end
