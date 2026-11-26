/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RootsOfUnity.Complex
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.Every
import TauCeti.LinearAlgebra.Matrix.Cartan.Coxeter.Classical
import TauCeti.LinearAlgebra.Matrix.Cartan.Coxeter.Exceptional
import TauCeti.RingTheory.Polynomial.Cyclotomic.Roots
import TauCeti.RingTheory.RootsOfUnity.Complex.Exp

/-!
# Coxeter elements, characteristic polynomials, and eigenvalues of classical bases

This file transports the matrix calculations of
`TauCeti.LinearAlgebra.Matrix.Cartan.Coxeter.Classical` to arbitrary Coxeter elements
`wordProd P b l` of bases of classical Cartan type (`Aₙ`, `Bₙ`, `Cₙ`, `Dₙ`) and computes their
complex eigenvalue multisets — retaining multiplicity:

| type | rank condition | `h` | exponents `e` |
|---|---|---|---|
| `Aₙ` | `0 < n` (`charpoly`/eigenvalues all `n`) | `n + 1` | `1, 2, …, n` |
| `Bₙ` | `0 < n` | `2 * n` | `1, 3, …, 2n - 1` |
| `Cₙ` | `0 < n` | `2 * n` | `1, 3, …, 2n - 1` |
| `Dₙ` | `2 ≤ n` | `2 * (n - 1)` | `1, 3, …, 2n - 3, n - 1` |

Stating the eigenvalue theorems as equalities of `Multiset ℂ` rather than set membership is
essential in even type `D₂ₘ`, where the middle exponent `n - 1 = 2m - 1` occurs twice and `-1` is
an eigenvalue of multiplicity `2`. The corresponding eigenvalue multisets for the exceptional types
live in `TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.Eigen`.

## Main definitions

* `TauCeti.Coxeter.aExponents`, `bExponents`, `cExponents`, `dExponents`: the exponent lists of the
  four classical families.

## Main results

* `TauCeti.Coxeter.mem_aExponents`, `mem_bExponents`, `mem_cExponents`, `mem_dExponents`:
  `@[simp]` membership characterizations of the classical exponent lists across all ranks.
* `TauCeti.Coxeter.orderOf_wordProd_of_hasCartanType_A` (and `_B`, `_C`, `_D`) and
  `TauCeti.Coxeter.charpoly_of_hasCartanType_A_of_actsBy` (and `_B`, `_C`, `_D`): order and
  characteristic polynomial of every Coxeter element of a classical base.
* `TauCeti.Coxeter.charpoly_of_hasCartanType_of_actsBy`: uniform characteristic polynomial on simple
  roots for any base of Cartan type `t`.
* `TauCeti.Coxeter.roots_charpoly_of_hasCartanType_A_of_actsBy` (and `_B`, `_C`, `_D`) together
  with the weight-space versions for `P.weylGroupRootRep`: complex eigenvalue multisets
  `exp (2πi e / h)` with multiplicity.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. V, §6, and Plates I--IX.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge University Press (1990),
  §§ 3.16–3.20.
-/

public section

open Matrix Polynomial RootPairing TauCeti

namespace TauCeti.Coxeter

/-! ### Exponent lists of the classical families -/

/-- The exponents `1, 2, …, n` of type `Aₙ`. -/
def aExponents (n : ℕ) : List ℕ := (List.range n).map (· + 1)

/-- `aExponents n` unfolds to `(List.range n).map (· + 1)`. -/
theorem aExponents_def (n : ℕ) : aExponents n = (List.range n).map (· + 1) := (rfl)

/-- The exponents `1, 3, …, 2n - 1` of type `Bₙ`. -/
def bExponents (n : ℕ) : List ℕ := (List.range n).map fun k => 2 * k + 1

/-- `bExponents n` unfolds to `(List.range n).map fun k => 2 * k + 1`. -/
theorem bExponents_def (n : ℕ) : bExponents n = (List.range n).map fun k => 2 * k + 1 := (rfl)

/-- The exponents `1, 3, …, 2n - 1` of type `Cₙ`. -/
def cExponents (n : ℕ) : List ℕ := bExponents n

/-- `cExponents n` unfolds to `bExponents n`. -/
theorem cExponents_def (n : ℕ) : cExponents n = bExponents n := (rfl)

/-- The exponents `1, 3, …, 2n - 3, n - 1` of type `Dₙ` (empty for `n = 0`). -/
def dExponents (n : ℕ) : List ℕ :=
  if n = 0 then [] else (List.range (n - 1)).map (fun k => 2 * k + 1) ++ [n - 1]

/-- `dExponents n` unfolds to its list definition. -/
theorem dExponents_def (n : ℕ) :
    dExponents n =
      if n = 0 then [] else (List.range (n - 1)).map (fun k => 2 * k + 1) ++ [n - 1] := (rfl)

/-- Type `A₀` has no exponents. -/
@[simp] theorem aExponents_zero : aExponents 0 = [] := (rfl)

/-- Type `B₀` has no exponents. -/
@[simp] theorem bExponents_zero : bExponents 0 = [] := (rfl)

/-- Type `C₀` has no exponents. -/
@[simp] theorem cExponents_zero : cExponents 0 = [] := (rfl)

/-- Type `D₀` has no exponents. -/
@[simp] theorem dExponents_zero : dExponents 0 = [] := (rfl)

/-- For positive rank `m + 1`, `dExponents (m + 1)` consists of `bExponents m` followed by `m`. -/
theorem dExponents_succ (m : ℕ) : dExponents (m + 1) = bExponents m ++ [m] := by
  simp [dExponents, bExponents]

/-- Type `Aₙ` has `n` exponents. -/
@[simp] theorem length_aExponents (n : ℕ) : (aExponents n).length = n := by simp [aExponents]

/-- Type `Bₙ` has `n` exponents. -/
@[simp] theorem length_bExponents (n : ℕ) : (bExponents n).length = n := by simp [bExponents]

/-- Type `Cₙ` has `n` exponents. -/
@[simp] theorem length_cExponents (n : ℕ) : (cExponents n).length = n := by simp [cExponents]

/-- Type `Dₙ` has `n` exponents (counted with multiplicity). -/
@[simp] theorem length_dExponents (n : ℕ) : (dExponents n).length = n := by
  rcases n with _ | m <;> simp [dExponents]

/-- A natural number belongs to `aExponents n` if and only if `1 ≤ e` and `e ≤ n`. -/
@[simp]
theorem mem_aExponents {e n : ℕ} : e ∈ aExponents n ↔ 1 ≤ e ∧ e ≤ n := by
  simp only [aExponents, List.mem_map, List.mem_range]
  exact ⟨fun ⟨k, _, hke⟩ => by omega, fun ⟨_, _⟩ => ⟨e - 1, by omega, by omega⟩⟩

/-- A natural number belongs to `bExponents n` if and only if it is odd and strictly less than
`2 * n`. -/
@[simp]
theorem mem_bExponents {e n : ℕ} : e ∈ bExponents n ↔ Odd e ∧ e < 2 * n := by
  simp only [bExponents, List.mem_map, List.mem_range]
  refine ⟨fun ⟨k, _, hke⟩ => ⟨⟨k, hke.symm⟩, by omega⟩, ?_⟩
  rintro ⟨⟨k, rfl⟩, hlt⟩
  exact ⟨k, by omega, rfl⟩

/-- A natural number belongs to `cExponents n` if and only if it is odd and strictly less than
`2 * n`. -/
@[simp]
theorem mem_cExponents {e n : ℕ} : e ∈ cExponents n ↔ Odd e ∧ e < 2 * n := by
  rw [cExponents, mem_bExponents]

/-- A natural number belongs to `dExponents n` if and only if it is an odd number strictly less
than `2 * (n - 1)` or `n ≠ 0` and `e = n - 1`. -/
@[simp]
theorem mem_dExponents {e n : ℕ} :
    e ∈ dExponents n ↔ (Odd e ∧ e < 2 * (n - 1)) ∨ (n ≠ 0 ∧ e = n - 1) := by
  rcases n with _ | m
  · simp [dExponents]
  · simp [dExponents_succ, mem_bExponents]

/-! ### Orders and characteristic polynomials of classical Coxeter elements -/

section ClassicalOrdersAndCharpoly

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] {P : RootPairing ι R M N} [P.IsCrystallographic] [IsDomain R] [CharZero R]
  {b : P.Base} {l : List b.support}

/-- **Every Coxeter element of a base of type `Aₙ` (`0 < n`) has order `n + 1`.** -/
theorem orderOf_wordProd_of_hasCartanType_A [Finite ι] {n : ℕ} (hn : 0 < n)
    (h : HasCartanType P b (.A n)) (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    orderOf (wordProd P b l) = n + 1 :=
  (orderOf_wordProd_of_isOneDegenerateOrder_of_hasCartanType (t := .A n)
    (DynkinType.cartanMatrix_A n) (isOneDegenerateOrder_A n) (List.Perm.refl _) h hnd hall).trans
    ((congrArg orderOf (coxA_def n).symm).trans (orderOf_coxA hn))

/-- **Every Coxeter element of a base of type `Bₙ` (`0 < n`) has order `2 * n`.** -/
theorem orderOf_wordProd_of_hasCartanType_B [Finite ι] {n : ℕ} (hn : 0 < n)
    (h : HasCartanType P b (.B n)) (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    orderOf (wordProd P b l) = 2 * n :=
  (orderOf_wordProd_of_isOneDegenerateOrder_of_hasCartanType (t := .B n)
    (DynkinType.cartanMatrix_B n) (isOneDegenerateOrder_B n) (List.Perm.refl _) h hnd hall).trans
    ((congrArg orderOf (coxB_def n).symm).trans (orderOf_coxB hn))

/-- **Every Coxeter element of a base of type `Cₙ` (`0 < n`) has order `2 * n`.** -/
theorem orderOf_wordProd_of_hasCartanType_C [Finite ι] {n : ℕ} (hn : 0 < n)
    (h : HasCartanType P b (.C n)) (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    orderOf (wordProd P b l) = 2 * n :=
  (orderOf_wordProd_of_isOneDegenerateOrder_of_hasCartanType (t := .C n)
    (DynkinType.cartanMatrix_C n) (isOneDegenerateOrder_C n) (List.Perm.refl _) h hnd hall).trans
    ((congrArg orderOf (coxC_def n).symm).trans (orderOf_coxC hn))

/-- **Every Coxeter element of a base of type `Dₙ` (`2 ≤ n`) has order `2 * (n - 1)`.** -/
theorem orderOf_wordProd_of_hasCartanType_D [Finite ι] {n : ℕ} (hn : 2 ≤ n)
    (h : HasCartanType P b (.D n)) (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    orderOf (wordProd P b l) = 2 * (n - 1) :=
  (orderOf_wordProd_of_isOneDegenerateOrder_of_hasCartanType (t := .D n)
    (DynkinType.cartanMatrix_D n) (isOneDegenerateOrder_D n) (List.Perm.refl _) h hnd hall).trans
    ((congrArg orderOf (coxD_def n).symm).trans (orderOf_coxD hn))

/-- **Every Coxeter element of a base of type `Aₙ`** has characteristic polynomial
`∑ k ∈ Finset.range (n + 1), X ^ k` on the simple roots. -/
theorem charpoly_of_hasCartanType_A_of_actsBy [DecidableEq ι] {n : ℕ}
    (h : HasCartanType P b (.A n)) (hnd : l.Nodup) (hall : ∀ i, i ∈ l)
    {W : Matrix b.support b.support ℤ} (hW : b.ActsBy (wordProd P b l) W) :
    W.charpoly = ∑ k ∈ Finset.range (n + 1), X ^ k :=
  (charpoly_of_isOneDegenerateOrder_of_hasCartanType_of_actsBy (t := .A n)
    (DynkinType.cartanMatrix_A n) (isOneDegenerateOrder_A n) (List.Perm.refl _) h hnd hall
    hW).trans ((congrArg Matrix.charpoly (coxA_def n).symm).trans (charpoly_coxA n))

/-- **Every Coxeter element of a base of type `Bₙ` (`0 < n`)** has characteristic polynomial
`X ^ n + 1` on the simple roots. -/
theorem charpoly_of_hasCartanType_B_of_actsBy [DecidableEq ι] {n : ℕ} (hn : 0 < n)
    (h : HasCartanType P b (.B n)) (hnd : l.Nodup) (hall : ∀ i, i ∈ l)
    {W : Matrix b.support b.support ℤ} (hW : b.ActsBy (wordProd P b l) W) :
    W.charpoly = X ^ n + 1 :=
  (charpoly_of_isOneDegenerateOrder_of_hasCartanType_of_actsBy (t := .B n)
    (DynkinType.cartanMatrix_B n) (isOneDegenerateOrder_B n) (List.Perm.refl _) h hnd hall
    hW).trans ((congrArg Matrix.charpoly (coxB_def n).symm).trans (charpoly_coxB hn))

/-- **Every Coxeter element of a base of type `Cₙ` (`0 < n`)** has characteristic polynomial
`X ^ n + 1` on the simple roots. -/
theorem charpoly_of_hasCartanType_C_of_actsBy [DecidableEq ι] {n : ℕ} (hn : 0 < n)
    (h : HasCartanType P b (.C n)) (hnd : l.Nodup) (hall : ∀ i, i ∈ l)
    {W : Matrix b.support b.support ℤ} (hW : b.ActsBy (wordProd P b l) W) :
    W.charpoly = X ^ n + 1 :=
  (charpoly_of_isOneDegenerateOrder_of_hasCartanType_of_actsBy (t := .C n)
    (DynkinType.cartanMatrix_C n) (isOneDegenerateOrder_C n) (List.Perm.refl _) h hnd hall
    hW).trans ((congrArg Matrix.charpoly (coxC_def n).symm).trans (charpoly_coxC hn))

/-- **Every Coxeter element of a base of type `Dₙ` (`2 ≤ n`)** has characteristic polynomial
`(X ^ (n - 1) + 1) * (X + 1)` on the simple roots. -/
theorem charpoly_of_hasCartanType_D_of_actsBy [DecidableEq ι] {n : ℕ} (hn : 2 ≤ n)
    (h : HasCartanType P b (.D n)) (hnd : l.Nodup) (hall : ∀ i, i ∈ l)
    {W : Matrix b.support b.support ℤ} (hW : b.ActsBy (wordProd P b l) W) :
    W.charpoly = (X ^ (n - 1) + 1) * (X + 1) :=
  (charpoly_of_isOneDegenerateOrder_of_hasCartanType_of_actsBy (t := .D n)
    (DynkinType.cartanMatrix_D n) (isOneDegenerateOrder_D n) (List.Perm.refl _) h hnd hall
    hW).trans ((congrArg Matrix.charpoly (coxD_def n).symm).trans (charpoly_coxD hn))

end ClassicalOrdersAndCharpoly

section UniformCharpoly

variable {ι R M N : Type*} [CommRing R] [CharZero R] [IsDomain R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic]

/-- **Every Coxeter element of a base of Cartan type `t`** has the same characteristic polynomial
on the simple roots as `Matrix.coxeterElement t.cartanMatrix`. -/
theorem charpoly_of_hasCartanType_of_actsBy [DecidableEq ι] {b : P.Base} {t : DynkinType}
    (h : HasCartanType P b t) {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l)
    {W : Matrix b.support b.support ℤ} (hW : b.ActsBy (wordProd P b l) W) :
    W.charpoly = (coxeterElement t.cartanMatrix).charpoly := by
  cases t with
  | A n =>
    rw [charpoly_of_hasCartanType_A_of_actsBy h hnd hall hW, ← charpoly_coxA n, coxA_def]
    exact congrArg (fun M : Matrix (Fin n) (Fin n) ℤ => (coxeterElement M).charpoly)
      (DynkinType.cartanMatrix_A n).symm
  | B n =>
    rcases n with _ | m
    · have : IsEmpty b.support := by
        rw [← Fintype.card_eq_zero_iff, Fintype.card_coe, h.card_support, DynkinType.rank_B]
      rw [Matrix.charpoly, Matrix.det_isEmpty, ← charpoly_coxB_zero, coxB_def]
      exact congrArg (fun M : Matrix (Fin 0) (Fin 0) ℤ => (coxeterElement M).charpoly)
        (DynkinType.cartanMatrix_B 0).symm
    · rw [charpoly_of_hasCartanType_B_of_actsBy (Nat.succ_pos m) h hnd hall hW,
        ← charpoly_coxB (Nat.succ_pos m), coxB_def]
      exact congrArg (fun M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ => (coxeterElement M).charpoly)
        (DynkinType.cartanMatrix_B (m + 1)).symm
  | C n =>
    rcases n with _ | m
    · have : IsEmpty b.support := by
        rw [← Fintype.card_eq_zero_iff, Fintype.card_coe, h.card_support, DynkinType.rank_C]
      rw [Matrix.charpoly, Matrix.det_isEmpty, ← charpoly_coxC_zero, coxC_def]
      exact congrArg (fun M : Matrix (Fin 0) (Fin 0) ℤ => (coxeterElement M).charpoly)
        (DynkinType.cartanMatrix_C 0).symm
    · rw [charpoly_of_hasCartanType_C_of_actsBy (Nat.succ_pos m) h hnd hall hW,
        ← charpoly_coxC (Nat.succ_pos m), coxC_def]
      exact congrArg (fun M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ => (coxeterElement M).charpoly)
        (DynkinType.cartanMatrix_C (m + 1)).symm
  | D n =>
    rcases n with _ | _ | m
    · have : IsEmpty b.support := by
        rw [← Fintype.card_eq_zero_iff, Fintype.card_coe, h.card_support, DynkinType.rank_D]
      rw [Matrix.charpoly, Matrix.det_isEmpty, ← charpoly_coxD_zero, coxD_def]
      exact congrArg (fun M : Matrix (Fin 0) (Fin 0) ℤ => (coxeterElement M).charpoly)
        (DynkinType.cartanMatrix_D 0).symm
    · have hc := charpoly_of_isOneDegenerateOrder_of_hasCartanType_of_actsBy (t := .D 1)
        (DynkinType.cartanMatrix_D 1) (isOneDegenerateOrder_D 1) (List.Perm.refl _) h hnd hall hW
      exact hc.trans (congrArg (fun M : Matrix (Fin 1) (Fin 1) ℤ => (coxeterElement M).charpoly)
        (DynkinType.cartanMatrix_D 1).symm)
    · rw [charpoly_of_hasCartanType_D_of_actsBy (by omega) h hnd hall hW,
        ← charpoly_coxD (by omega), coxD_def]
      exact congrArg
        (fun M : Matrix (Fin (m + 2)) (Fin (m + 2)) ℤ => (coxeterElement M).charpoly)
        (DynkinType.cartanMatrix_D (m + 2)).symm
  | E6 =>
    rw [charpoly_of_hasCartanType_E6_of_actsBy h hnd hall hW, ← charpoly_coxE6]
    exact congrArg (fun M : Matrix (Fin 6) (Fin 6) ℤ => (coxeterElement M).charpoly)
      DynkinType.cartanMatrix_E6.symm
  | E7 =>
    rw [charpoly_of_hasCartanType_E7_of_actsBy h hnd hall hW, ← charpoly_coxE7]
    exact congrArg (fun M : Matrix (Fin 7) (Fin 7) ℤ => (coxeterElement M).charpoly)
      DynkinType.cartanMatrix_E7.symm
  | E8 =>
    rw [charpoly_of_hasCartanType_E8_of_actsBy h hnd hall hW, ← charpoly_coxE8]
    exact congrArg (fun M : Matrix (Fin 8) (Fin 8) ℤ => (coxeterElement M).charpoly)
      DynkinType.cartanMatrix_E8.symm
  | F4 =>
    rw [charpoly_of_hasCartanType_F4_of_actsBy h hnd hall hW, ← charpoly_coxF4]
    exact congrArg (fun M : Matrix (Fin 4) (Fin 4) ℤ => (coxeterElement M).charpoly)
      DynkinType.cartanMatrix_F4.symm
  | G2 =>
    rw [charpoly_of_hasCartanType_G2_of_actsBy h hnd hall hW, ← charpoly_coxG2]
    exact congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => (coxeterElement M).charpoly)
      DynkinType.cartanMatrix_G2.symm

end UniformCharpoly

/-! ### Complex eigenvalue multisets on simple roots and on the weight space -/

section EigenvalueMultisets

variable {ι R M N : Type*} [DecidableEq ι] [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {P : RootPairing ι R M N} [P.IsCrystallographic] [IsDomain R]
  [CharZero R] {b : P.Base} {l : List b.support}

/-- **Complex eigenvalue multiset of a Coxeter element of type `Aₙ` on the simple roots**:
`exp (2πi e / (n + 1))` for `e ∈ aExponents n = [1, 2, …, n]`. -/
theorem roots_charpoly_of_hasCartanType_A_of_actsBy {n : ℕ} (h : HasCartanType P b (.A n))
    (hnd : l.Nodup) (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ}
    (hW : b.ActsBy (wordProd P b l) W) :
    (W.map (Int.castRingHom ℂ)).charpoly.roots =
      Multiset.ofList (aExponents n |>.map fun e : ℕ =>
        Complex.exp (2 * Real.pi * Complex.I * (e / (n + 1 : ℂ)))) := by
  have hmap :
      (W.map (Int.castRingHom ℂ)).charpoly = ∑ k ∈ Finset.range (n + 1), (X : ℂ[X]) ^ k := by
    rw [Matrix.charpoly_map, charpoly_of_hasCartanType_A_of_actsBy h hnd hall hW,
      Polynomial.map_sum]; simp
  rw [hmap, roots_sum_range_X_pow (Complex.isPrimitiveRoot_exp (n + 1) (Nat.succ_ne_zero n))]
  simp [aExponents, List.map_map, Function.comp_def, exp_two_pi_I_div_pow]

/-- **Complex eigenvalue multiset of a Coxeter element of type `Bₙ` (`0 < n`) on the simple
roots**: `exp (2πi e / (2n))` for `e ∈ bExponents n = [1, 3, …, 2n - 1]`. -/
theorem roots_charpoly_of_hasCartanType_B_of_actsBy {n : ℕ} (hn : 0 < n)
    (h : HasCartanType P b (.B n)) (hnd : l.Nodup) (hall : ∀ i, i ∈ l)
    {W : Matrix b.support b.support ℤ} (hW : b.ActsBy (wordProd P b l) W) :
    (W.map (Int.castRingHom ℂ)).charpoly.roots =
      Multiset.ofList (bExponents n |>.map fun e : ℕ =>
        Complex.exp (2 * Real.pi * Complex.I * (e / (2 * n : ℂ)))) := by
  have hmap : (W.map (Int.castRingHom ℂ)).charpoly = (X : ℂ[X]) ^ n + 1 := by
    rw [Matrix.charpoly_map, charpoly_of_hasCartanType_B_of_actsBy hn h hnd hall hW]; simp
  rw [hmap, roots_X_pow_add_one hn (Complex.isPrimitiveRoot_exp (2 * n) (by omega))]
  simp [bExponents, List.map_map, Function.comp_def, exp_two_pi_I_div_pow]

/-- **Complex eigenvalue multiset of a Coxeter element of type `Cₙ` (`0 < n`) on the simple
roots**: `exp (2πi e / (2n))` for `e ∈ cExponents n = [1, 3, …, 2n - 1]`. -/
theorem roots_charpoly_of_hasCartanType_C_of_actsBy {n : ℕ} (hn : 0 < n)
    (h : HasCartanType P b (.C n)) (hnd : l.Nodup) (hall : ∀ i, i ∈ l)
    {W : Matrix b.support b.support ℤ} (hW : b.ActsBy (wordProd P b l) W) :
    (W.map (Int.castRingHom ℂ)).charpoly.roots =
      Multiset.ofList (cExponents n |>.map fun e : ℕ =>
        Complex.exp (2 * Real.pi * Complex.I * (e / (2 * n : ℂ)))) := by
  have hmap : (W.map (Int.castRingHom ℂ)).charpoly = (X : ℂ[X]) ^ n + 1 := by
    rw [Matrix.charpoly_map, charpoly_of_hasCartanType_C_of_actsBy hn h hnd hall hW]; simp
  rw [hmap, roots_X_pow_add_one hn (Complex.isPrimitiveRoot_exp (2 * n) (by omega))]
  simp [cExponents, bExponents, List.map_map, Function.comp_def, exp_two_pi_I_div_pow]

/-- **Complex eigenvalue multiset of a Coxeter element of type `Dₙ` (`2 ≤ n`) on the simple
roots**: `exp (2πi e / (2(n - 1)))` for `e ∈ dExponents n = [1, 3, …, 2n - 3, n - 1]`, retaining
the double eigenvalue `-1` when `n` is even. -/
theorem roots_charpoly_of_hasCartanType_D_of_actsBy {n : ℕ} (hn : 2 ≤ n)
    (h : HasCartanType P b (.D n)) (hnd : l.Nodup) (hall : ∀ i, i ∈ l)
    {W : Matrix b.support b.support ℤ} (hW : b.ActsBy (wordProd P b l) W) :
    (W.map (Int.castRingHom ℂ)).charpoly.roots =
      Multiset.ofList (dExponents n |>.map fun e : ℕ =>
        Complex.exp (2 * Real.pi * Complex.I * (e / (2 * (n - 1 : ℂ))))) := by
  have hn0 : n ≠ 0 := by omega
  have hmap : (W.map (Int.castRingHom ℂ)).charpoly = ((X : ℂ[X]) ^ (n - 1) + 1) * (X + 1) := by
    rw [Matrix.charpoly_map, charpoly_of_hasCartanType_D_of_actsBy hn h hnd hall hW]; simp
  rw [hmap, roots_X_pow_add_one_mul_X_add_one hn
    (Complex.isPrimitiveRoot_exp (2 * (n - 1)) (by omega))]
  simp [dExponents, hn0, List.map_map, Function.comp_def, exp_two_pi_I_div_pow,
    Nat.cast_sub (by omega : 1 ≤ n)]

end EigenvalueMultisets

section WeightSpaceEigenvalues

variable {ι M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
  {P : RootPairing ι ℂ M N} [P.IsRootSystem] [P.IsCrystallographic] [Module.Finite ℂ M]
  {b : P.Base} {l : List b.support}

/-- **Weight-space eigenvalue multiset of a Coxeter element of type `Aₙ`
(`P.weylGroupRootRep`).** -/
theorem roots_charpoly_weylGroupRootRep_wordProd_of_hasCartanType_A {n : ℕ}
    (h : HasCartanType P b (.A n)) (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    (P.weylGroupRootRep (wordProd P b l)).charpoly.roots =
      Multiset.ofList (aExponents n |>.map fun e : ℕ =>
        Complex.exp (2 * Real.pi * Complex.I * (e / (n + 1 : ℂ)))) := by
  classical
  rw [(b.actsBy_wordProd l).charpoly_weylGroupRootRep, ← Matrix.charpoly_map]
  exact roots_charpoly_of_hasCartanType_A_of_actsBy h hnd hall (b.actsBy_wordProd l)

/-- **Weight-space eigenvalue multiset of a Coxeter element of type `Bₙ` (`0 < n`).** -/
theorem roots_charpoly_weylGroupRootRep_wordProd_of_hasCartanType_B {n : ℕ} (hn : 0 < n)
    (h : HasCartanType P b (.B n)) (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    (P.weylGroupRootRep (wordProd P b l)).charpoly.roots =
      Multiset.ofList (bExponents n |>.map fun e : ℕ =>
        Complex.exp (2 * Real.pi * Complex.I * (e / (2 * n : ℂ)))) := by
  classical
  rw [(b.actsBy_wordProd l).charpoly_weylGroupRootRep, ← Matrix.charpoly_map]
  exact roots_charpoly_of_hasCartanType_B_of_actsBy hn h hnd hall (b.actsBy_wordProd l)

/-- **Weight-space eigenvalue multiset of a Coxeter element of type `Cₙ` (`0 < n`).** -/
theorem roots_charpoly_weylGroupRootRep_wordProd_of_hasCartanType_C {n : ℕ} (hn : 0 < n)
    (h : HasCartanType P b (.C n)) (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    (P.weylGroupRootRep (wordProd P b l)).charpoly.roots =
      Multiset.ofList (cExponents n |>.map fun e : ℕ =>
        Complex.exp (2 * Real.pi * Complex.I * (e / (2 * n : ℂ)))) := by
  classical
  rw [(b.actsBy_wordProd l).charpoly_weylGroupRootRep, ← Matrix.charpoly_map]
  exact roots_charpoly_of_hasCartanType_C_of_actsBy hn h hnd hall (b.actsBy_wordProd l)

/-- **Weight-space eigenvalue multiset of a Coxeter element of type `Dₙ` (`2 ≤ n`), including
reducible `D₂ = A₁ × A₁`.** -/
theorem roots_charpoly_weylGroupRootRep_wordProd_of_hasCartanType_D {n : ℕ} (hn : 2 ≤ n)
    (h : HasCartanType P b (.D n)) (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    (P.weylGroupRootRep (wordProd P b l)).charpoly.roots =
      Multiset.ofList (dExponents n |>.map fun e : ℕ =>
        Complex.exp (2 * Real.pi * Complex.I * (e / (2 * (n - 1 : ℂ))))) := by
  classical
  rw [(b.actsBy_wordProd l).charpoly_weylGroupRootRep, ← Matrix.charpoly_map]
  exact roots_charpoly_of_hasCartanType_D_of_actsBy hn h hnd hall (b.actsBy_wordProd l)

end WeightSpaceEigenvalues

end TauCeti.Coxeter

end
