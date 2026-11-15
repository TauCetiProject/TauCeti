/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Multiset.Range
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.Every
import TauCeti.LinearAlgebra.Matrix.Cartan.Coxeter.Classical
import TauCeti.RingTheory.Polynomial.Cyclotomic.ComplexRoots

/-!
# Coxeter elements of classical Cartan types

For a base `b` of Cartan type `Aₙ`, `Bₙ`, `Cₙ`, or `Dₙ`, every Coxeter element `wordProd P b l` has
the same multiplicative order and characteristic polynomial on the simple roots as the
Bourbaki-ordered `Matrix.coxeterElement` of the standard Cartan matrix, and its complex eigenvalue
multiset has the form `exp (2πi e / h)` over the classical exponent multiset (recording the
multiplicity-`2` eigenvalue `-1` in `D₂ₘ`).

## Main results

* `TauCeti.Coxeter.orderOf_wordProd_of_hasCartanType_A`, `B`, `C`, `D`.
* `TauCeti.Coxeter.charpoly_of_hasCartanType_A_of_actsBy`, `B`, `C`, `D`.
* `TauCeti.Coxeter.roots_charpoly_of_hasCartanType_A_of_actsBy`, `B`, `C`, `D`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. V, §6, and Plates I--IV.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge University Press (1990),
  §§ 3.16–3.20.
-/

public section

open Matrix Polynomial RootPairing TauCeti

namespace TauCeti.Coxeter

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {P : RootPairing ι R M N} [P.IsCrystallographic]
  [IsDomain R] [CharZero R] {b : P.Base} {l : List b.support}

/-! ### Multiplicative orders of classical Coxeter elements -/

/-- **Every Coxeter element of a base of type `Aₙ` (`0 < n`) has order `n + 1`.** -/
theorem orderOf_wordProd_of_hasCartanType_A [Finite ι] {n : ℕ} (hn : 0 < n)
    (h : HasCartanType P b (.A n)) (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    orderOf (wordProd P b l) = n + 1 :=
  (orderOf_wordProd_of_isOneDegenerateOrder_of_hasCartanType (DynkinType.cartanMatrix_A n)
    (isOneDegenerateOrder_A n) (.refl _) h hnd hall).trans (orderOf_coxeterElement_A hn)

/-- **Every Coxeter element of a base of type `Bₙ` (`0 < n`) has order `2 n`.** -/
theorem orderOf_wordProd_of_hasCartanType_B [Finite ι] {n : ℕ} (hn : 0 < n)
    (h : HasCartanType P b (.B n)) (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    orderOf (wordProd P b l) = 2 * n :=
  (orderOf_wordProd_of_isOneDegenerateOrder_of_hasCartanType (DynkinType.cartanMatrix_B n)
    (isOneDegenerateOrder_B n) (.refl _) h hnd hall).trans (orderOf_coxeterElement_B hn)

/-- **Every Coxeter element of a base of type `Cₙ` (`0 < n`) has order `2 n`.** -/
theorem orderOf_wordProd_of_hasCartanType_C [Finite ι] {n : ℕ} (hn : 0 < n)
    (h : HasCartanType P b (.C n)) (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    orderOf (wordProd P b l) = 2 * n :=
  (orderOf_wordProd_of_isOneDegenerateOrder_of_hasCartanType (DynkinType.cartanMatrix_C n)
    (isOneDegenerateOrder_C n) (.refl _) h hnd hall).trans (orderOf_coxeterElement_C hn)

/-- **Every Coxeter element of a base of type `Dₙ` (`2 ≤ n`) has order `2 n - 2`.** -/
theorem orderOf_wordProd_of_hasCartanType_D [Finite ι] {n : ℕ} (hn : 2 ≤ n)
    (h : HasCartanType P b (.D n)) (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    orderOf (wordProd P b l) = 2 * n - 2 :=
  (orderOf_wordProd_of_isOneDegenerateOrder_of_hasCartanType (DynkinType.cartanMatrix_D n)
    (isOneDegenerateOrder_D n) (.refl _) h hnd hall).trans (orderOf_coxeterElement_D hn)

/-! ### Characteristic polynomials on the simple roots -/

/-- **Characteristic polynomial of every Coxeter element of type `Aₙ` on the simple roots.** -/
theorem charpoly_of_hasCartanType_A_of_actsBy [DecidableEq ι] {n : ℕ}
    (h : HasCartanType P b (.A n)) (hnd : l.Nodup) (hall : ∀ i, i ∈ l)
    {W : Matrix b.support b.support ℤ} (hW : b.ActsBy (wordProd P b l) W) :
    W.charpoly = ∑ k ∈ Finset.range (n + 1), X ^ k :=
  (charpoly_of_isOneDegenerateOrder_of_hasCartanType_of_actsBy (DynkinType.cartanMatrix_A n)
    (isOneDegenerateOrder_A n) (.refl _) h hnd hall hW).trans (charpoly_coxeterElement_A n)

/-- **Characteristic polynomial of every Coxeter element of type `Bₙ` (`0 < n`) on the simple
roots.** -/
theorem charpoly_of_hasCartanType_B_of_actsBy [DecidableEq ι] {n : ℕ} (hn : 0 < n)
    (h : HasCartanType P b (.B n)) (hnd : l.Nodup) (hall : ∀ i, i ∈ l)
    {W : Matrix b.support b.support ℤ} (hW : b.ActsBy (wordProd P b l) W) :
    W.charpoly = X ^ n + 1 :=
  (charpoly_of_isOneDegenerateOrder_of_hasCartanType_of_actsBy (DynkinType.cartanMatrix_B n)
    (isOneDegenerateOrder_B n) (.refl _) h hnd hall hW).trans (charpoly_coxeterElement_B hn)

/-- **Characteristic polynomial of every Coxeter element of type `Cₙ` (`0 < n`) on the simple
roots.** -/
theorem charpoly_of_hasCartanType_C_of_actsBy [DecidableEq ι] {n : ℕ} (hn : 0 < n)
    (h : HasCartanType P b (.C n)) (hnd : l.Nodup) (hall : ∀ i, i ∈ l)
    {W : Matrix b.support b.support ℤ} (hW : b.ActsBy (wordProd P b l) W) :
    W.charpoly = X ^ n + 1 :=
  (charpoly_of_isOneDegenerateOrder_of_hasCartanType_of_actsBy (DynkinType.cartanMatrix_C n)
    (isOneDegenerateOrder_C n) (.refl _) h hnd hall hW).trans (charpoly_coxeterElement_C hn)

/-- **Characteristic polynomial of every Coxeter element of type `Dₙ` (`2 ≤ n`) on the simple
roots.** -/
theorem charpoly_of_hasCartanType_D_of_actsBy [DecidableEq ι] {n : ℕ} (hn : 2 ≤ n)
    (h : HasCartanType P b (.D n)) (hnd : l.Nodup) (hall : ∀ i, i ∈ l)
    {W : Matrix b.support b.support ℤ} (hW : b.ActsBy (wordProd P b l) W) :
    W.charpoly = (X ^ (n - 1) + 1) * (X + 1) :=
  (charpoly_of_isOneDegenerateOrder_of_hasCartanType_of_actsBy (DynkinType.cartanMatrix_D n)
    (isOneDegenerateOrder_D n) (.refl _) h hnd hall hW).trans (charpoly_coxeterElement_D hn)

/-! ### Complex eigenvalue multisets -/

/-- **Complex eigenvalue multiset of every Coxeter element of type `Aₙ` on the simple roots**:
`exp (2πi e / (n + 1))` for `e = 1, …, n`. -/
theorem roots_charpoly_of_hasCartanType_A_of_actsBy [DecidableEq ι] {n : ℕ}
    (h : HasCartanType P b (.A n)) (hnd : l.Nodup) (hall : ∀ i, i ∈ l)
    {W : Matrix b.support b.support ℤ} (hW : b.ActsBy (wordProd P b l) W) :
    (W.map (Int.castRingHom ℂ)).charpoly.roots =
      ((Multiset.range n).map (· + 1)).map
        fun e : ℕ => Complex.exp (2 * Real.pi * Complex.I * (e / (n + 1 : ℕ))) := by
  rw [charpoly_map, charpoly_of_hasCartanType_A_of_actsBy h hnd hall hW]
  simp only [Polynomial.map_sum, Polynomial.map_pow, map_X]
  simpa [Multiset.map_map] using roots_geom_sum_complex (n + 1)

/-- **Complex eigenvalue multiset of every Coxeter element of type `Bₙ` (`0 < n`) on the simple
roots**: `exp (2πi e / (2n))` for `e = 1, 3, …, 2n - 1`. -/
theorem roots_charpoly_of_hasCartanType_B_of_actsBy [DecidableEq ι] {n : ℕ} (hn : 0 < n)
    (h : HasCartanType P b (.B n)) (hnd : l.Nodup) (hall : ∀ i, i ∈ l)
    {W : Matrix b.support b.support ℤ} (hW : b.ActsBy (wordProd P b l) W) :
    (W.map (Int.castRingHom ℂ)).charpoly.roots =
      ((Multiset.range n).map (2 * · + 1)).map
        fun e : ℕ => Complex.exp (2 * Real.pi * Complex.I * (e / (2 * n : ℕ))) := by
  rw [charpoly_map, charpoly_of_hasCartanType_B_of_actsBy hn h hnd hall hW]
  simp only [Polynomial.map_add, Polynomial.map_pow, map_X, Polynomial.map_one]
  simpa [Multiset.map_map] using roots_X_pow_add_one_complex n

/-- **Complex eigenvalue multiset of every Coxeter element of type `Cₙ` (`0 < n`) on the simple
roots**: `exp (2πi e / (2n))` for `e = 1, 3, …, 2n - 1`. -/
theorem roots_charpoly_of_hasCartanType_C_of_actsBy [DecidableEq ι] {n : ℕ} (hn : 0 < n)
    (h : HasCartanType P b (.C n)) (hnd : l.Nodup) (hall : ∀ i, i ∈ l)
    {W : Matrix b.support b.support ℤ} (hW : b.ActsBy (wordProd P b l) W) :
    (W.map (Int.castRingHom ℂ)).charpoly.roots =
      ((Multiset.range n).map (2 * · + 1)).map
        fun e : ℕ => Complex.exp (2 * Real.pi * Complex.I * (e / (2 * n : ℕ))) := by
  rw [charpoly_map, charpoly_of_hasCartanType_C_of_actsBy hn h hnd hall hW]
  simp only [Polynomial.map_add, Polynomial.map_pow, map_X, Polynomial.map_one]
  simpa [Multiset.map_map] using roots_X_pow_add_one_complex n

/-- **Complex eigenvalue multiset of every Coxeter element of type `Dₙ` (`2 ≤ n`) on the simple
roots**: `exp (2πi e / (2n - 2))` for `e = n - 1` together with `e = 1, 3, …, 2n - 3`. -/
theorem roots_charpoly_of_hasCartanType_D_of_actsBy [DecidableEq ι] {n : ℕ} (hn : 2 ≤ n)
    (h : HasCartanType P b (.D n)) (hnd : l.Nodup) (hall : ∀ i, i ∈ l)
    {W : Matrix b.support b.support ℤ} (hW : b.ActsBy (wordProd P b l) W) :
    (W.map (Int.castRingHom ℂ)).charpoly.roots =
      ((n - 1) ::ₘ (Multiset.range (n - 1)).map (2 * · + 1)).map
        fun e : ℕ => Complex.exp (2 * Real.pi * Complex.I * (e / (2 * n - 2 : ℕ))) := by
  rw [charpoly_map, charpoly_of_hasCartanType_D_of_actsBy hn h hnd hall hW]
  simp only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_pow, map_X, Polynomial.map_one]
  have hp1 : ((X : ℂ[X]) ^ (n - 1) + 1) ≠ 0 := by
    simpa [sub_neg_eq_add] using X_pow_sub_C_ne_zero (by omega : 0 < n - 1) (-1 : ℂ)
  have hp2 : ((X : ℂ[X]) + 1) ≠ 0 := by
    simpa [sub_neg_eq_add] using X_pow_sub_C_ne_zero Nat.one_pos (-1 : ℂ)
  have hh : 2 * n - 2 = 2 * (n - 1) := by omega
  have hexp_mid : Complex.exp (2 * Real.pi * Complex.I * ((n - 1 : ℕ) / (2 * n - 2 : ℕ))) = -1 := by
    have hne : ((n - 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    rw [show (2 : ℂ) * Real.pi * Complex.I * (((n - 1 : ℕ) : ℂ) / ((2 * n - 2 : ℕ) : ℂ)) =
      Real.pi * Complex.I by rw [hh]; push_cast; field_simp [hne], Complex.exp_pi_mul_I]
  rw [roots_mul (mul_ne_zero hp1 hp2), roots_X_pow_add_one_complex (n - 1),
    show ((X : ℂ[X]) + 1).roots = {-1} by
      rw [show ((X : ℂ[X]) + 1) = X - C (-1) by simp, roots_X_sub_C],
    add_comm, Multiset.singleton_add, Multiset.map_cons, hexp_mid, hh, Multiset.map_map]
  rfl

end TauCeti.Coxeter

end
