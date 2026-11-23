/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.Every
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Exponents
import TauCeti.LinearAlgebra.Matrix.Cartan.Coxeter.Classical
import TauCeti.LinearAlgebra.Matrix.Cartan.Coxeter.Exceptional
import TauCeti.RingTheory.Polynomial.RootsOfUnity.Complex
import TauCeti.RingTheory.RootsOfUnity.Complex.Exp

/-!
# Eigenvalues of Coxeter elements and exponents of Dynkin types

For every irreducible crystallographic Dynkin type `t` (`TauCeti.DynkinType.Valid`), the complex
eigenvalues of the canonical Coxeter matrix `Matrix.coxeterElement t.cartanMatrix` — and hence of
the matrix of any Coxeter element on the simple roots — counted with multiplicity, are

`exp (2πi e / h)`

as `e` runs over the **exponents** `t.exponents` (`TauCeti.DynkinType.exponents`) of `t`, where
`h = t.coxeterNumber`:

| type | `h` | exponents `m₁, …, mᵣ` |
|---|---|---|
| `Aₙ` | `n + 1` | `1, 2, …, n` |
| `Bₙ`, `Cₙ` | `2 n` | `1, 3, 5, …, 2 n - 1` |
| `Dₙ` | `2 (n - 1)` | `1, 3, …, 2 n - 3, n - 1` |
| `E₆` | `12` | `1, 4, 5, 7, 8, 11` |
| `E₇` | `18` | `1, 5, 7, 9, 11, 13, 17` |
| `E₈` | `30` | `1, 7, 11, 13, 17, 19, 23, 29` |
| `F₄` | `12` | `1, 5, 7, 11` |
| `G₂` | `6` | `1, 5` |

In even-rank type `D_{2k}`, the exponent `2 k - 1 = n - 1` appears twice, corresponding to the
double eigenvalue `-1` of `(X^{2k - 1} + 1)(X + 1)`. Stating
`TauCeti.Coxeter.roots_charpoly_coxeterElement` and
`TauCeti.Coxeter.roots_charpoly_of_hasCartanType_of_actsBy` as equalities of multisets records every
multiplicity faithfully across all types.

## Main results

* `TauCeti.Coxeter.roots_charpoly_coxeterElement` and
  `TauCeti.Coxeter.mem_roots_charpoly_coxeterElement_of_coprime`: complex eigenvalue multiset and
  primitive `h`-th root containment for `Matrix.coxeterElement t.cartanMatrix`.
* `TauCeti.Coxeter.eigenvalues_of_hasCartanType_E8` (and `E7`, `E6`, `F4`, `G2`): the eigenvalues
  of the matrix of every Coxeter element of an exceptional type on the simple roots, each simple.
* `TauCeti.Coxeter.roots_charpoly_of_hasCartanType_A_of_actsBy` (and `B`, `C`, `D`) and
  `TauCeti.Coxeter.roots_charpoly_of_hasCartanType_of_actsBy`: transported complex eigenvalue
  multisets for any base of Cartan type `t`.
* `TauCeti.Coxeter.roots_charpoly_of_actsBy`, `mem_roots_charpoly_of_actsBy_of_coprime`, and
  `exp_two_pi_I_div_orderOf_mem_roots_charpoly_of_actsBy`: classification-free spectral theorems
  for finite irreducible reduced crystallographic root systems.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. V, §6, and Plates I--IX.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge University Press (1990),
  §§ 3.7, 3.16–3.20.
-/

public section

open Matrix Polynomial RootPairing TauCeti

namespace TauCeti.Coxeter

/-! ### Eigenvalue multisets for the canonical Coxeter matrices -/

private lemma eigenvalues_coxE6 :
    (∀ ζ : ℂ, ζ ∈ (coxE6.map (Int.castRingHom ℂ)).charpoly.roots ↔
      ∃ e ∈ DynkinType.E6.exponents, Complex.exp (2 * Real.pi * Complex.I * (e / 12)) = ζ) ∧
      (coxE6.map (Int.castRingHom ℂ)).charpoly.roots.Nodup := by
  have hc := charpoly_coxE6
  refine ⟨fun ζ => ?_, nodup_roots_charpoly_of_charpoly_eq_cyclotomic_mul (by norm_num) hc⟩
  have h4 : (4 : ℂ) / 12 = 1 / 3 := by norm_num
  have h8 : (8 : ℂ) / 12 = 2 / 3 := by norm_num
  rw [mem_roots_charpoly_of_charpoly_eq_cyclotomic_mul hc,
    show (List.range 12).filter (Nat.Coprime · 12) = [1, 5, 7, 11] by decide,
    show (List.range 3).filter (Nat.Coprime · 3) = [1, 2] by decide]
  simp only [DynkinType.exponents_E6, List.mem_cons, List.not_mem_nil, or_false,
    exists_eq_or_imp, exists_eq_left, Nat.cast_one, Nat.cast_ofNat, h4, h8]
  tauto

private lemma eigenvalues_coxE7 :
    (∀ ζ : ℂ, ζ ∈ (coxE7.map (Int.castRingHom ℂ)).charpoly.roots ↔
      ∃ e ∈ DynkinType.E7.exponents, Complex.exp (2 * Real.pi * Complex.I * (e / 18)) = ζ) ∧
      (coxE7.map (Int.castRingHom ℂ)).charpoly.roots.Nodup := by
  have hc := charpoly_coxE7
  refine ⟨fun ζ => ?_, nodup_roots_charpoly_of_charpoly_eq_cyclotomic_mul (by norm_num) hc⟩
  have h9 : (9 : ℂ) / 18 = 1 / 2 := by norm_num
  rw [mem_roots_charpoly_of_charpoly_eq_cyclotomic_mul hc,
    show (List.range 18).filter (Nat.Coprime · 18) = [1, 5, 7, 11, 13, 17] by decide,
    show (List.range 2).filter (Nat.Coprime · 2) = [1] by decide]
  simp only [DynkinType.exponents_E7, List.mem_cons, List.not_mem_nil, or_false,
    exists_eq_or_imp, exists_eq_left, Nat.cast_one, Nat.cast_ofNat, h9]
  tauto

private lemma eigenvalues_coxE8 :
    (∀ ζ : ℂ, ζ ∈ (coxE8.map (Int.castRingHom ℂ)).charpoly.roots ↔
      ∃ e ∈ DynkinType.E8.exponents, Complex.exp (2 * Real.pi * Complex.I * (e / 30)) = ζ) ∧
      (coxE8.map (Int.castRingHom ℂ)).charpoly.roots.Nodup := by
  have hc := charpoly_coxE8
  refine ⟨fun ζ => ?_, nodup_roots_charpoly_of_charpoly_eq_cyclotomic hc⟩
  rw [mem_roots_charpoly_of_charpoly_eq_cyclotomic hc, ← DynkinType.exponents_E8_eq_filter]
  norm_num

private lemma eigenvalues_coxF4 :
    (∀ ζ : ℂ, ζ ∈ (coxF4.map (Int.castRingHom ℂ)).charpoly.roots ↔
      ∃ e ∈ DynkinType.F4.exponents, Complex.exp (2 * Real.pi * Complex.I * (e / 12)) = ζ) ∧
      (coxF4.map (Int.castRingHom ℂ)).charpoly.roots.Nodup := by
  have hc := charpoly_coxF4
  refine ⟨fun ζ => ?_, nodup_roots_charpoly_of_charpoly_eq_cyclotomic hc⟩
  rw [mem_roots_charpoly_of_charpoly_eq_cyclotomic hc, ← DynkinType.exponents_F4_eq_filter]
  norm_num

private lemma eigenvalues_coxG2 :
    (∀ ζ : ℂ, ζ ∈ (coxG2.map (Int.castRingHom ℂ)).charpoly.roots ↔
      ∃ e ∈ DynkinType.G2.exponents, Complex.exp (2 * Real.pi * Complex.I * (e / 6)) = ζ) ∧
      (coxG2.map (Int.castRingHom ℂ)).charpoly.roots.Nodup := by
  have hc := charpoly_coxG2
  refine ⟨fun ζ => ?_, nodup_roots_charpoly_of_charpoly_eq_cyclotomic hc⟩
  rw [mem_roots_charpoly_of_charpoly_eq_cyclotomic hc, ← DynkinType.exponents_G2_eq_filter]
  norm_num

private lemma roots_charpoly_coxeterElement_A (n : ℕ) :
    ((coxeterElement (CartanMatrix.A n)).map (Int.castRingHom ℂ)).charpoly.roots =
      ((DynkinType.A n).exponents : Multiset ℕ).map fun e : ℕ =>
        Complex.exp (2 * Real.pi * Complex.I * (e / (DynkinType.A n).coxeterNumber)) := by
  rw [charpoly_map, charpoly_coxeterElement_A]
  simp [Polynomial.map_sum, roots_geom_sum_complex]

private lemma roots_charpoly_coxeterElement_B {n : ℕ} (hn : 1 ≤ n) :
    ((coxeterElement (CartanMatrix.B n)).map (Int.castRingHom ℂ)).charpoly.roots =
      ((DynkinType.B n).exponents : Multiset ℕ).map fun e : ℕ =>
        Complex.exp (2 * Real.pi * Complex.I * (e / (DynkinType.B n).coxeterNumber)) := by
  rw [charpoly_map, charpoly_coxeterElement_B hn]
  simpa using roots_X_pow_add_one_complex hn

private lemma roots_charpoly_coxeterElement_C {n : ℕ} (hn : 1 ≤ n) :
    ((coxeterElement (CartanMatrix.C n)).map (Int.castRingHom ℂ)).charpoly.roots =
      ((DynkinType.C n).exponents : Multiset ℕ).map fun e : ℕ =>
        Complex.exp (2 * Real.pi * Complex.I * (e / (DynkinType.C n).coxeterNumber)) := by
  rw [charpoly_map, charpoly_coxeterElement_C hn]
  simpa using roots_X_pow_add_one_complex hn

private lemma roots_charpoly_coxeterElement_D {n : ℕ} (hn : 2 ≤ n) :
    ((coxeterElement (CartanMatrix.D n)).map (Int.castRingHom ℂ)).charpoly.roots =
      ((DynkinType.D n).exponents : Multiset ℕ).map fun e : ℕ =>
        Complex.exp (2 * Real.pi * Complex.I * (e / (DynkinType.D n).coxeterNumber)) := by
  have hm : 1 ≤ n - 1 := by omega
  have hmC : ((n - 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hp1 : ((X : ℂ[X]) ^ (n - 1) + 1) ≠ 0 := by
    simpa [sub_neg_eq_add] using X_pow_sub_C_ne_zero (by omega : 0 < n - 1) (-1 : ℂ)
  have hp2 : ((X : ℂ[X]) + 1) ≠ 0 := by
    simpa using X_sub_C_ne_zero (-1 : ℂ)
  rw [charpoly_map, charpoly_coxeterElement_D hn]
  simp only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_pow, map_X, Polynomial.map_one,
    DynkinType.exponents_D_of_ne_zero (by omega : n ≠ 0), DynkinType.coxeterNumber_D,
    ← Multiset.coe_add, Multiset.map_add, Multiset.coe_singleton, Multiset.map_singleton]
  rw [roots_mul (mul_ne_zero hp1 hp2), roots_X_pow_add_one_complex hm]
  congr 1
  have hlin : ((X : ℂ[X]) + 1).roots = {-1} := by simpa using roots_X_add_C (1 : ℂ)
  rw [hlin]
  congr 1
  have hexp : 2 * (Real.pi : ℂ) * Complex.I * (((n - 1 : ℕ) : ℂ) / (2 * ((n - 1 : ℕ) : ℂ))) =
      Real.pi * Complex.I := by
    field_simp
  push_cast
  rw [hexp, Complex.exp_pi_mul_I]

/-- **Complex eigenvalue multiset of the canonical Coxeter matrix `Matrix.coxeterElement
t.cartanMatrix`** for any valid Dynkin type `t`: counted with multiplicity, the eigenvalues are
`exp (2πi e / h)` as `e` runs over `t.exponents`, where `h = t.coxeterNumber`. -/
theorem roots_charpoly_coxeterElement {t : DynkinType} (ht : t.Valid) :
    ((coxeterElement t.cartanMatrix).map (Int.castRingHom ℂ)).charpoly.roots =
      (t.exponents : Multiset ℕ).map fun e : ℕ =>
        Complex.exp (2 * Real.pi * Complex.I * (e / t.coxeterNumber)) := by
  cases t with
  | A n =>
    rw [DynkinType.cartanMatrix_A]
    exact roots_charpoly_coxeterElement_A n
  | B n =>
    rw [DynkinType.cartanMatrix_B]
    exact roots_charpoly_coxeterElement_B (n := n) (by have := DynkinType.valid_B.mp ht; omega)
  | C n =>
    rw [DynkinType.cartanMatrix_C]
    exact roots_charpoly_coxeterElement_C (n := n) (by have := DynkinType.valid_C.mp ht; omega)
  | D n =>
    rw [DynkinType.cartanMatrix_D]
    exact roots_charpoly_coxeterElement_D (n := n) (by have := DynkinType.valid_D.mp ht; omega)
  | E6 =>
    obtain ⟨hmem, hnd_r⟩ := eigenvalues_coxE6
    rw [DynkinType.cartanMatrix_E6, DynkinType.coxeterNumber_E6]
    rw [DynkinType.exponents_E6] at hmem ⊢
    exact multiset_eq_map_exp_of_mem_iff_of_nodup (h := 12) (by norm_num) (by decide) (by decide)
      hnd_r hmem
  | E7 =>
    obtain ⟨hmem, hnd_r⟩ := eigenvalues_coxE7
    rw [DynkinType.cartanMatrix_E7, DynkinType.coxeterNumber_E7]
    rw [DynkinType.exponents_E7] at hmem ⊢
    exact multiset_eq_map_exp_of_mem_iff_of_nodup (h := 18) (by norm_num) (by decide) (by decide)
      hnd_r hmem
  | E8 =>
    obtain ⟨hmem, hnd_r⟩ := eigenvalues_coxE8
    rw [DynkinType.cartanMatrix_E8, DynkinType.coxeterNumber_E8]
    rw [DynkinType.exponents_E8] at hmem ⊢
    exact multiset_eq_map_exp_of_mem_iff_of_nodup (h := 30) (by norm_num) (by decide) (by decide)
      hnd_r hmem
  | F4 =>
    obtain ⟨hmem, hnd_r⟩ := eigenvalues_coxF4
    rw [DynkinType.cartanMatrix_F4, DynkinType.coxeterNumber_F4]
    rw [DynkinType.exponents_F4] at hmem ⊢
    exact multiset_eq_map_exp_of_mem_iff_of_nodup (h := 12) (by norm_num) (by decide) (by decide)
      hnd_r hmem
  | G2 =>
    obtain ⟨hmem, hnd_r⟩ := eigenvalues_coxG2
    rw [DynkinType.cartanMatrix_G2, DynkinType.coxeterNumber_G2]
    rw [DynkinType.exponents_G2] at hmem ⊢
    exact multiset_eq_map_exp_of_mem_iff_of_nodup (h := 6) (by norm_num) (by decide) (by decide)
      hnd_r hmem

/-- **Every primitive `h`-th root of unity `exp (2πi e / h)` (`e < h`, `gcd(e, h) = 1`) is an
eigenvalue of `Matrix.coxeterElement t.cartanMatrix`** for any valid Dynkin type `t`. -/
theorem mem_roots_charpoly_coxeterElement_of_coprime {t : DynkinType} (ht : t.Valid) {e : ℕ}
    (he : e < t.coxeterNumber) (hcop : e.Coprime t.coxeterNumber) :
    Complex.exp (2 * Real.pi * Complex.I * (e / t.coxeterNumber)) ∈
      ((coxeterElement t.cartanMatrix).map (Int.castRingHom ℂ)).charpoly.roots := by
  rw [roots_charpoly_coxeterElement ht, Multiset.mem_map]
  exact ⟨e, Multiset.mem_coe.mpr (t.mem_exponents_of_coprime ht he hcop), rfl⟩

/-! ### Transported eigenvalues on bases of valid Cartan type -/

section HasCartanType

variable {ι R M N : Type*} [DecidableEq ι] [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {P : RootPairing ι R M N} [P.IsCrystallographic] [IsDomain R]
  [CharZero R]

/-- **Eigenvalues of the matrix of every Coxeter element of type `E₆` on the simple roots**:
`exp (2πi e / 12)` for the exponents `e = 1, 4, 5, 7, 8, 11`, each once. -/
theorem eigenvalues_of_hasCartanType_E6 {b : P.Base} (h : HasCartanType P b .E6)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ}
    (hW : b.ActsBy (wordProd P b l) W) :
    (∀ ζ : ℂ, ζ ∈ (W.map (Int.castRingHom ℂ)).charpoly.roots ↔
      ∃ e ∈ DynkinType.E6.exponents, Complex.exp (2 * Real.pi * Complex.I * (e / 12)) = ζ) ∧
      (W.map (Int.castRingHom ℂ)).charpoly.roots.Nodup := by
  have hcp := charpoly_of_hasCartanType_of_actsBy h hnd hall hW
  rw [DynkinType.cartanMatrix_E6] at hcp
  rw [charpoly_map, hcp, ← charpoly_map]
  exact eigenvalues_coxE6

/-- **Eigenvalues of the matrix of every Coxeter element of type `E₇` on the simple roots**:
`exp (2πi e / 18)` for the exponents `e = 1, 5, 7, 9, 11, 13, 17`, each once. -/
theorem eigenvalues_of_hasCartanType_E7 {b : P.Base} (h : HasCartanType P b .E7)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ}
    (hW : b.ActsBy (wordProd P b l) W) :
    (∀ ζ : ℂ, ζ ∈ (W.map (Int.castRingHom ℂ)).charpoly.roots ↔
      ∃ e ∈ DynkinType.E7.exponents, Complex.exp (2 * Real.pi * Complex.I * (e / 18)) = ζ) ∧
      (W.map (Int.castRingHom ℂ)).charpoly.roots.Nodup := by
  have hcp := charpoly_of_hasCartanType_of_actsBy h hnd hall hW
  rw [DynkinType.cartanMatrix_E7] at hcp
  rw [charpoly_map, hcp, ← charpoly_map]
  exact eigenvalues_coxE7

/-- **Eigenvalues of the matrix of every Coxeter element of type `E₈` on the simple roots**:
`exp (2πi e / 30)` for the exponents `e = 1, 7, 11, 13, 17, 19, 23, 29`, each once. -/
theorem eigenvalues_of_hasCartanType_E8 {b : P.Base} (h : HasCartanType P b .E8)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ}
    (hW : b.ActsBy (wordProd P b l) W) :
    (∀ ζ : ℂ, ζ ∈ (W.map (Int.castRingHom ℂ)).charpoly.roots ↔
      ∃ e ∈ DynkinType.E8.exponents, Complex.exp (2 * Real.pi * Complex.I * (e / 30)) = ζ) ∧
      (W.map (Int.castRingHom ℂ)).charpoly.roots.Nodup := by
  have hcp := charpoly_of_hasCartanType_of_actsBy h hnd hall hW
  rw [DynkinType.cartanMatrix_E8] at hcp
  rw [charpoly_map, hcp, ← charpoly_map]
  exact eigenvalues_coxE8

/-- **Eigenvalues of the matrix of every Coxeter element of type `F₄` on the simple roots**:
`exp (2πi e / 12)` for the exponents `e = 1, 5, 7, 11`, each once. -/
theorem eigenvalues_of_hasCartanType_F4 {b : P.Base} (h : HasCartanType P b .F4)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ}
    (hW : b.ActsBy (wordProd P b l) W) :
    (∀ ζ : ℂ, ζ ∈ (W.map (Int.castRingHom ℂ)).charpoly.roots ↔
      ∃ e ∈ DynkinType.F4.exponents, Complex.exp (2 * Real.pi * Complex.I * (e / 12)) = ζ) ∧
      (W.map (Int.castRingHom ℂ)).charpoly.roots.Nodup := by
  have hcp := charpoly_of_hasCartanType_of_actsBy h hnd hall hW
  rw [DynkinType.cartanMatrix_F4] at hcp
  rw [charpoly_map, hcp, ← charpoly_map]
  exact eigenvalues_coxF4

/-- **Eigenvalues of the matrix of every Coxeter element of type `G₂` on the simple roots**:
`exp (2πi e / 6)` for the exponents `e = 1, 5`, each once. -/
theorem eigenvalues_of_hasCartanType_G2 {b : P.Base} (h : HasCartanType P b .G2)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ}
    (hW : b.ActsBy (wordProd P b l) W) :
    (∀ ζ : ℂ, ζ ∈ (W.map (Int.castRingHom ℂ)).charpoly.roots ↔
      ∃ e ∈ DynkinType.G2.exponents, Complex.exp (2 * Real.pi * Complex.I * (e / 6)) = ζ) ∧
      (W.map (Int.castRingHom ℂ)).charpoly.roots.Nodup := by
  have hcp := charpoly_of_hasCartanType_of_actsBy h hnd hall hW
  rw [DynkinType.cartanMatrix_G2] at hcp
  rw [charpoly_map, hcp, ← charpoly_map]
  exact eigenvalues_coxG2

/-- **Complex eigenvalue multiset of every Coxeter element of type `Aₙ` on the simple roots**:
`exp (2πi e / (n + 1))` for `e = 1, …, n`, each with multiplicity one. -/
theorem roots_charpoly_of_hasCartanType_A_of_actsBy {n : ℕ} {b : P.Base}
    (h : HasCartanType P b (.A n)) {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l)
    {W : Matrix b.support b.support ℤ} (hW : b.ActsBy (wordProd P b l) W) :
    (W.map (Int.castRingHom ℂ)).charpoly.roots =
      ((DynkinType.A n).exponents : Multiset ℕ).map fun e : ℕ =>
        Complex.exp (2 * Real.pi * Complex.I * (e / (DynkinType.A n).coxeterNumber)) := by
  have hcp := charpoly_of_hasCartanType_of_actsBy h hnd hall hW
  rw [DynkinType.cartanMatrix_A] at hcp
  rw [charpoly_map, hcp, ← charpoly_map]
  exact roots_charpoly_coxeterElement_A n

/-- **Complex eigenvalue multiset of every Coxeter element of type `Bₙ` (`1 ≤ n`) on the simple
roots**: `exp (2πi e / (2 n))` for `e = 1, 3, …, 2 n - 1`, each with multiplicity one. -/
theorem roots_charpoly_of_hasCartanType_B_of_actsBy {n : ℕ} (hn : 1 ≤ n) {b : P.Base}
    (h : HasCartanType P b (.B n)) {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l)
    {W : Matrix b.support b.support ℤ} (hW : b.ActsBy (wordProd P b l) W) :
    (W.map (Int.castRingHom ℂ)).charpoly.roots =
      ((DynkinType.B n).exponents : Multiset ℕ).map fun e : ℕ =>
        Complex.exp (2 * Real.pi * Complex.I * (e / (DynkinType.B n).coxeterNumber)) := by
  have hcp := charpoly_of_hasCartanType_of_actsBy h hnd hall hW
  rw [DynkinType.cartanMatrix_B] at hcp
  rw [charpoly_map, hcp, ← charpoly_map]
  exact roots_charpoly_coxeterElement_B hn

/-- **Complex eigenvalue multiset of every Coxeter element of type `Cₙ` (`1 ≤ n`) on the simple
roots**: `exp (2πi e / (2 n))` for `e = 1, 3, …, 2 n - 1`, each with multiplicity one. -/
theorem roots_charpoly_of_hasCartanType_C_of_actsBy {n : ℕ} (hn : 1 ≤ n) {b : P.Base}
    (h : HasCartanType P b (.C n)) {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l)
    {W : Matrix b.support b.support ℤ} (hW : b.ActsBy (wordProd P b l) W) :
    (W.map (Int.castRingHom ℂ)).charpoly.roots =
      ((DynkinType.C n).exponents : Multiset ℕ).map fun e : ℕ =>
        Complex.exp (2 * Real.pi * Complex.I * (e / (DynkinType.C n).coxeterNumber)) := by
  have hcp := charpoly_of_hasCartanType_of_actsBy h hnd hall hW
  rw [DynkinType.cartanMatrix_C] at hcp
  rw [charpoly_map, hcp, ← charpoly_map]
  exact roots_charpoly_coxeterElement_C hn

/-- **Complex eigenvalue multiset of every Coxeter element of type `Dₙ` (`2 ≤ n`) on the simple
roots**: `exp (2πi e / (2 (n - 1)))` for `e = 1, 3, …, 2 n - 3, n - 1` (with `-1` of multiplicity
two when `n` is even). -/
theorem roots_charpoly_of_hasCartanType_D_of_actsBy {n : ℕ} (hn : 2 ≤ n) {b : P.Base}
    (h : HasCartanType P b (.D n)) {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l)
    {W : Matrix b.support b.support ℤ} (hW : b.ActsBy (wordProd P b l) W) :
    (W.map (Int.castRingHom ℂ)).charpoly.roots =
      ((DynkinType.D n).exponents : Multiset ℕ).map fun e : ℕ =>
        Complex.exp (2 * Real.pi * Complex.I * (e / (DynkinType.D n).coxeterNumber)) := by
  have hcp := charpoly_of_hasCartanType_of_actsBy h hnd hall hW
  rw [DynkinType.cartanMatrix_D] at hcp
  rw [charpoly_map, hcp, ← charpoly_map]
  exact roots_charpoly_coxeterElement_D hn

/-- **Complex eigenvalue multiset of every Coxeter element of a base of valid Cartan type `t`** on
the simple roots: counted with multiplicity, the eigenvalues are `exp (2πi e / h)` as `e` runs over
`t.exponents`, where `h = t.coxeterNumber`. -/
theorem roots_charpoly_of_hasCartanType_of_actsBy {t : DynkinType} (ht : t.Valid)
    {b : P.Base} (h : HasCartanType P b t) {l : List b.support} (hnd : l.Nodup)
    (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ}
    (hW : b.ActsBy (wordProd P b l) W) :
    (W.map (Int.castRingHom ℂ)).charpoly.roots =
      (t.exponents : Multiset ℕ).map fun e : ℕ =>
        Complex.exp (2 * Real.pi * Complex.I * (e / t.coxeterNumber)) := by
  rw [charpoly_map, charpoly_of_hasCartanType_of_actsBy h hnd hall hW, ← charpoly_map]
  exact roots_charpoly_coxeterElement ht

/-- **Every primitive `h`-th root of unity `exp (2πi e / h)` (`e < h`, `gcd(e, h) = 1`) is an
eigenvalue of every Coxeter element of a base of valid Cartan type `t`.** -/
theorem mem_roots_charpoly_of_hasCartanType_of_actsBy_of_coprime {t : DynkinType}
    (ht : t.Valid) {b : P.Base} (h : HasCartanType P b t) {l : List b.support}
    (hnd : l.Nodup) (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ}
    (hW : b.ActsBy (wordProd P b l) W) {e : ℕ} (he : e < t.coxeterNumber)
    (hcop : e.Coprime t.coxeterNumber) :
    Complex.exp (2 * Real.pi * Complex.I * (e / t.coxeterNumber)) ∈
      (W.map (Int.castRingHom ℂ)).charpoly.roots := by
  rw [charpoly_map, charpoly_of_hasCartanType_of_actsBy h hnd hall hW, ← charpoly_map]
  exact mem_roots_charpoly_coxeterElement_of_coprime ht he hcop

end HasCartanType

/-! ### Classification-free spectral theorems for irreducible root systems -/

section Irreducible

variable {ι R M N : Type*} [DecidableEq ι] [CommRing R] [IsDomain R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] {P : RootPairing ι R M N}
  [Finite ι] [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible]

/-- **Complex eigenvalue multiset of any Coxeter element on the simple roots** of a finite
irreducible reduced crystallographic root system: `exp (2πi e / h)` as `e` runs over the exponents
of `classifiedDynkinType b`, where `h = orderOf (wordProd P b l)`. -/
theorem roots_charpoly_of_actsBy {b : P.Base} {l : List b.support}
    (hnd : l.Nodup) (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ}
    (hW : b.ActsBy (wordProd P b l) W) :
    (W.map (Int.castRingHom ℂ)).charpoly.roots =
      ((classifiedDynkinType b).exponents : Multiset ℕ).map fun e : ℕ =>
        Complex.exp (2 * Real.pi * Complex.I * (e / orderOf (wordProd P b l))) := by
  rw [orderOf_wordProd_eq_coxeterNumber_classifiedDynkinType hnd hall]
  exact roots_charpoly_of_hasCartanType_of_actsBy (valid_classifiedDynkinType b)
    (hasCartanType_classifiedDynkinType b) hnd hall hW

/-- **Every primitive `h`-th root of unity is an eigenvalue of every Coxeter element** of a finite
irreducible reduced crystallographic root system on the simple roots, where
`h = orderOf (wordProd P b l)`. -/
theorem mem_roots_charpoly_of_actsBy_of_coprime {b : P.Base} {l : List b.support}
    (hnd : l.Nodup) (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ}
    (hW : b.ActsBy (wordProd P b l) W) {e : ℕ} (he : e < orderOf (wordProd P b l))
    (hcop : e.Coprime (orderOf (wordProd P b l))) :
    Complex.exp (2 * Real.pi * Complex.I * (e / orderOf (wordProd P b l))) ∈
      (W.map (Int.castRingHom ℂ)).charpoly.roots := by
  have hord := orderOf_wordProd_eq_coxeterNumber_classifiedDynkinType hnd hall
  rw [hord] at he hcop ⊢
  exact mem_roots_charpoly_of_hasCartanType_of_actsBy_of_coprime (valid_classifiedDynkinType b)
    (hasCartanType_classifiedDynkinType b) hnd hall hW he hcop

/-- **The primitive root `exp (2πi / h)` (`e = 1`) is an eigenvalue of every Coxeter element** of a
finite irreducible reduced crystallographic root system on the simple roots. -/
theorem exp_two_pi_I_div_orderOf_mem_roots_charpoly_of_actsBy {b : P.Base}
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ}
    (hW : b.ActsBy (wordProd P b l) W) :
    Complex.exp (2 * Real.pi * Complex.I / orderOf (wordProd P b l)) ∈
      (W.map (Int.castRingHom ℂ)).charpoly.roots := by
  have hmem := mem_roots_charpoly_of_actsBy_of_coprime hnd hall hW (e := 1)
    (two_le_orderOf_wordProd hnd hall) (Nat.coprime_one_left _)
  rw [Nat.cast_one, mul_one_div] at hmem
  exact hmem

end Irreducible

end TauCeti.Coxeter

end
