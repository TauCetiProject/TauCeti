/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.Every
public import TauCeti.LinearAlgebra.RootSystem.Exponents
public import Mathlib.RingTheory.RootsOfUnity.Complex
import TauCeti.RingTheory.Polynomial.RootsOfUnity.Complex

/-!
# Eigenvalues of Coxeter elements and exponents of Dynkin types

For every irreducible crystallographic Dynkin type `t` (`TauCeti.DynkinType.Valid`), the complex
eigenvalues of the matrix of any Coxeter element on the simple roots, counted with multiplicity, are

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
double eigenvalue `-1` of `(X^{2k - 1} + 1)(X + 1)`. Stating the uniform theorem
`TauCeti.Coxeter.roots_charpoly_of_hasCartanType_of_actsBy` as an equality of multisets records
every multiplicity faithfully across all types.

## Main definitions

* `TauCeti.Coxeter.e6Exponents` (and `e7`, `e8`, `f4`, `g2`): the exponents of the exceptional
  types.

## Main results

* `TauCeti.Coxeter.eigenvalues_of_hasCartanType_E8` (and `E7`, `E6`, `F4`, `G2`): the eigenvalues
  of the matrix of every Coxeter element of an exceptional type on the simple roots, each simple.
* `TauCeti.Coxeter.roots_charpoly_of_hasCartanType_A_of_actsBy` (and `B`, `C`, `D`) and
  `TauCeti.Coxeter.roots_charpoly_of_hasCartanType_of_actsBy`: the complex eigenvalue multiset of
  every Coxeter element of a base of valid Cartan type `t` is `(Multiset.ofList t.exponents).map
  (fun e => exp (2πi e / h))`.
* `TauCeti.Coxeter.mem_roots_charpoly_of_hasCartanType_of_coprime` (via
  `TauCeti.Coxeter.mem_roots_charpoly_of_hasCartanType_of_actsBy_of_coprime`): every primitive
  `h`-th root of unity is an eigenvalue.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. V, §6, and Plates I--IX.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge University Press (1990),
  §§ 3.7, 3.16–3.20.
-/

public section

open Matrix Polynomial RootPairing TauCeti

namespace TauCeti.Coxeter

/-- The exponents of `E₆`. -/
@[expose] def e6Exponents : List ℕ := [1, 4, 5, 7, 8, 11]

/-- The exponents of `E₇`. -/
@[expose] def e7Exponents : List ℕ := [1, 5, 7, 9, 11, 13, 17]

/-- The exponents of `E₈`. -/
@[expose] def e8Exponents : List ℕ := [1, 7, 11, 13, 17, 19, 23, 29]

/-- The exponents of `F₄`. -/
@[expose] def f4Exponents : List ℕ := [1, 5, 7, 11]

/-- The exponents of `G₂`. -/
@[expose] def g2Exponents : List ℕ := [1, 5]

/-- The exponents of `E₈` are the residues modulo `30` coprime to `30`. -/
theorem e8Exponents_eq_filter : e8Exponents = (List.range 30).filter (Nat.Coprime · 30) := by
  decide

/-- The exponents of `F₄` are the residues modulo `12` coprime to `12`. -/
theorem f4Exponents_eq_filter : f4Exponents = (List.range 12).filter (Nat.Coprime · 12) := by
  decide

/-- The exponents of `G₂` are the residues modulo `6` coprime to `6`. -/
theorem g2Exponents_eq_filter : g2Exponents = (List.range 6).filter (Nat.Coprime · 6) := by
  decide

end TauCeti.Coxeter

namespace TauCeti.Coxeter

variable {ι R M N : Type*} [DecidableEq ι] [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {P : RootPairing ι R M N} [P.IsCrystallographic] [IsDomain R]
  [CharZero R]

/-- **Eigenvalues of the matrix of every Coxeter element of type `E₆` on the simple roots**:
`exp (2πi e / 12)` for the exponents `e = 1, 4, 5, 7, 8, 11`, each once. -/
theorem eigenvalues_of_hasCartanType_E6 {b : P.Base} (h : HasCartanType P b .E6)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ}
    (hW : b.ActsBy (wordProd P b l) W) :
    (∀ ζ : ℂ, ζ ∈ (W.map (Int.castRingHom ℂ)).charpoly.roots ↔
      ∃ e ∈ e6Exponents, Complex.exp (2 * Real.pi * Complex.I * (e / 12)) = ζ) ∧
      (W.map (Int.castRingHom ℂ)).charpoly.roots.Nodup := by
  have hc := charpoly_of_hasCartanType_E6_of_actsBy h hnd hall hW
  refine ⟨fun ζ => ?_, nodup_roots_charpoly_of_charpoly_eq_cyclotomic_mul (by norm_num) hc⟩
  have h4 : (4 : ℂ) / 12 = 1 / 3 := by norm_num
  have h8 : (8 : ℂ) / 12 = 2 / 3 := by norm_num
  rw [mem_roots_charpoly_of_charpoly_eq_cyclotomic_mul hc,
    show (List.range 12).filter (Nat.Coprime · 12) = [1, 5, 7, 11] by decide,
    show (List.range 3).filter (Nat.Coprime · 3) = [1, 2] by decide]
  simp only [e6Exponents, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
    exists_eq_left, Nat.cast_one, Nat.cast_ofNat, h4, h8]
  tauto

/-- **Eigenvalues of the matrix of every Coxeter element of type `E₇` on the simple roots**:
`exp (2πi e / 18)` for the exponents `e = 1, 5, 7, 9, 11, 13, 17`, each once. -/
theorem eigenvalues_of_hasCartanType_E7 {b : P.Base} (h : HasCartanType P b .E7)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ}
    (hW : b.ActsBy (wordProd P b l) W) :
    (∀ ζ : ℂ, ζ ∈ (W.map (Int.castRingHom ℂ)).charpoly.roots ↔
      ∃ e ∈ e7Exponents, Complex.exp (2 * Real.pi * Complex.I * (e / 18)) = ζ) ∧
      (W.map (Int.castRingHom ℂ)).charpoly.roots.Nodup := by
  have hc := charpoly_of_hasCartanType_E7_of_actsBy h hnd hall hW
  refine ⟨fun ζ => ?_, nodup_roots_charpoly_of_charpoly_eq_cyclotomic_mul (by norm_num) hc⟩
  have h9 : (9 : ℂ) / 18 = 1 / 2 := by norm_num
  rw [mem_roots_charpoly_of_charpoly_eq_cyclotomic_mul hc,
    show (List.range 18).filter (Nat.Coprime · 18) = [1, 5, 7, 11, 13, 17] by decide,
    show (List.range 2).filter (Nat.Coprime · 2) = [1] by decide]
  simp only [e7Exponents, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
    exists_eq_left, Nat.cast_one, Nat.cast_ofNat, h9]
  tauto

/-- **Eigenvalues of the matrix of every Coxeter element of type `E₈` on the simple roots**:
`exp (2πi e / 30)` for the exponents `e = 1, 7, 11, 13, 17, 19, 23, 29`, each once. -/
theorem eigenvalues_of_hasCartanType_E8 {b : P.Base} (h : HasCartanType P b .E8)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ}
    (hW : b.ActsBy (wordProd P b l) W) :
    (∀ ζ : ℂ, ζ ∈ (W.map (Int.castRingHom ℂ)).charpoly.roots ↔
      ∃ e ∈ e8Exponents, Complex.exp (2 * Real.pi * Complex.I * (e / 30)) = ζ) ∧
      (W.map (Int.castRingHom ℂ)).charpoly.roots.Nodup := by
  have hc := charpoly_of_hasCartanType_E8_of_actsBy h hnd hall hW
  refine ⟨fun ζ => ?_, nodup_roots_charpoly_of_charpoly_eq_cyclotomic hc⟩
  rw [mem_roots_charpoly_of_charpoly_eq_cyclotomic hc, ← e8Exponents_eq_filter]
  norm_num

/-- **Eigenvalues of the matrix of every Coxeter element of type `F₄` on the simple roots**:
`exp (2πi e / 12)` for the exponents `e = 1, 5, 7, 11`, each once. -/
theorem eigenvalues_of_hasCartanType_F4 {b : P.Base} (h : HasCartanType P b .F4)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ}
    (hW : b.ActsBy (wordProd P b l) W) :
    (∀ ζ : ℂ, ζ ∈ (W.map (Int.castRingHom ℂ)).charpoly.roots ↔
      ∃ e ∈ f4Exponents, Complex.exp (2 * Real.pi * Complex.I * (e / 12)) = ζ) ∧
      (W.map (Int.castRingHom ℂ)).charpoly.roots.Nodup := by
  have hc := charpoly_of_hasCartanType_F4_of_actsBy h hnd hall hW
  refine ⟨fun ζ => ?_, nodup_roots_charpoly_of_charpoly_eq_cyclotomic hc⟩
  rw [mem_roots_charpoly_of_charpoly_eq_cyclotomic hc, ← f4Exponents_eq_filter]
  norm_num

/-- **Eigenvalues of the matrix of every Coxeter element of type `G₂` on the simple roots**:
`exp (2πi e / 6)` for the exponents `e = 1, 5`, each once. -/
theorem eigenvalues_of_hasCartanType_G2 {b : P.Base} (h : HasCartanType P b .G2)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ}
    (hW : b.ActsBy (wordProd P b l) W) :
    (∀ ζ : ℂ, ζ ∈ (W.map (Int.castRingHom ℂ)).charpoly.roots ↔
      ∃ e ∈ g2Exponents, Complex.exp (2 * Real.pi * Complex.I * (e / 6)) = ζ) ∧
      (W.map (Int.castRingHom ℂ)).charpoly.roots.Nodup := by
  have hc := charpoly_of_hasCartanType_G2_of_actsBy h hnd hall hW
  refine ⟨fun ζ => ?_, nodup_roots_charpoly_of_charpoly_eq_cyclotomic hc⟩
  rw [mem_roots_charpoly_of_charpoly_eq_cyclotomic hc, ← g2Exponents_eq_filter]
  norm_num

/-! ### Eigenvalue multisets for the classical types and for arbitrary valid Dynkin types -/

/-- **Complex eigenvalue multiset of every Coxeter element of type `Aₙ` on the simple roots**:
`exp (2πi e / (n + 1))` for `e = 1, …, n`, each with multiplicity one. -/
theorem roots_charpoly_of_hasCartanType_A_of_actsBy {n : ℕ} {b : P.Base}
    (h : HasCartanType P b (.A n)) {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l)
    {W : Matrix b.support b.support ℤ} (hW : b.ActsBy (wordProd P b l) W) :
    (W.map (Int.castRingHom ℂ)).charpoly.roots =
      (Multiset.ofList (DynkinType.A n).exponents).map fun e : ℕ =>
        Complex.exp (2 * Real.pi * Complex.I * (e / (DynkinType.A n).coxeterNumber)) := by
  rw [charpoly_map, charpoly_of_hasCartanType_A_of_actsBy h hnd hall hW]
  simp [Polynomial.map_sum, roots_geom_sum_complex]

/-- **Complex eigenvalue multiset of every Coxeter element of type `Bₙ` (`1 ≤ n`) on the simple
roots**: `exp (2πi e / (2 n))` for `e = 1, 3, …, 2 n - 1`, each with multiplicity one. -/
theorem roots_charpoly_of_hasCartanType_B_of_actsBy {n : ℕ} (hn : 1 ≤ n) {b : P.Base}
    (h : HasCartanType P b (.B n)) {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l)
    {W : Matrix b.support b.support ℤ} (hW : b.ActsBy (wordProd P b l) W) :
    (W.map (Int.castRingHom ℂ)).charpoly.roots =
      (Multiset.ofList (DynkinType.B n).exponents).map fun e : ℕ =>
        Complex.exp (2 * Real.pi * Complex.I * (e / (DynkinType.B n).coxeterNumber)) := by
  rw [charpoly_map, charpoly_of_hasCartanType_B_of_actsBy hn h hnd hall hW]
  simpa using roots_X_pow_add_one_complex hn

/-- **Complex eigenvalue multiset of every Coxeter element of type `Cₙ` (`1 ≤ n`) on the simple
roots**: `exp (2πi e / (2 n))` for `e = 1, 3, …, 2 n - 1`, each with multiplicity one. -/
theorem roots_charpoly_of_hasCartanType_C_of_actsBy {n : ℕ} (hn : 1 ≤ n) {b : P.Base}
    (h : HasCartanType P b (.C n)) {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l)
    {W : Matrix b.support b.support ℤ} (hW : b.ActsBy (wordProd P b l) W) :
    (W.map (Int.castRingHom ℂ)).charpoly.roots =
      (Multiset.ofList (DynkinType.C n).exponents).map fun e : ℕ =>
        Complex.exp (2 * Real.pi * Complex.I * (e / (DynkinType.C n).coxeterNumber)) := by
  rw [charpoly_map, charpoly_of_hasCartanType_C_of_actsBy hn h hnd hall hW]
  simpa using roots_X_pow_add_one_complex hn

/-- **Complex eigenvalue multiset of every Coxeter element of type `Dₙ` (`2 ≤ n`) on the simple
roots**: `exp (2πi e / (2 (n - 1)))` for `e = 1, 3, …, 2 n - 3, n - 1` (with `-1` of multiplicity
two when `n` is even). -/
theorem roots_charpoly_of_hasCartanType_D_of_actsBy {n : ℕ} (hn : 2 ≤ n) {b : P.Base}
    (h : HasCartanType P b (.D n)) {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l)
    {W : Matrix b.support b.support ℤ} (hW : b.ActsBy (wordProd P b l) W) :
    (W.map (Int.castRingHom ℂ)).charpoly.roots =
      (Multiset.ofList (DynkinType.D n).exponents).map fun e : ℕ =>
        Complex.exp (2 * Real.pi * Complex.I * (e / (DynkinType.D n).coxeterNumber)) := by
  have hm : 1 ≤ n - 1 := by omega
  have hmC : ((n - 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hp1 : ((X : ℂ[X]) ^ (n - 1) + 1) ≠ 0 := by
    simpa [sub_neg_eq_add] using X_pow_sub_C_ne_zero (by omega : 0 < n - 1) (-1 : ℂ)
  have hp2 : ((X : ℂ[X]) + 1) ≠ 0 := by
    simpa using X_sub_C_ne_zero (-1 : ℂ)
  rw [charpoly_map, charpoly_of_hasCartanType_D_of_actsBy hn h hnd hall hW]
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

/-- **Complex eigenvalue multiset of every Coxeter element of a base of valid Cartan type `t`** on
the simple roots: counted with multiplicity, the eigenvalues are `exp (2πi e / h)` as `e` runs over
`t.exponents`, where `h = t.coxeterNumber`. -/
theorem roots_charpoly_of_hasCartanType_of_actsBy {t : DynkinType} (ht : t.Valid)
    {b : P.Base} (h : HasCartanType P b t) {l : List b.support} (hnd : l.Nodup)
    (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ}
    (hW : b.ActsBy (wordProd P b l) W) :
    (W.map (Int.castRingHom ℂ)).charpoly.roots =
      (Multiset.ofList t.exponents).map fun e : ℕ =>
        Complex.exp (2 * Real.pi * Complex.I * (e / t.coxeterNumber)) := by
  cases t with
  | A n => exact roots_charpoly_of_hasCartanType_A_of_actsBy h hnd hall hW
  | B n =>
    exact roots_charpoly_of_hasCartanType_B_of_actsBy
      (by have := DynkinType.valid_B.mp ht; omega) h hnd hall hW
  | C n =>
    exact roots_charpoly_of_hasCartanType_C_of_actsBy
      (by have := DynkinType.valid_C.mp ht; omega) h hnd hall hW
  | D n =>
    exact roots_charpoly_of_hasCartanType_D_of_actsBy
      (by have := DynkinType.valid_D.mp ht; omega) h hnd hall hW
  | E6 =>
    obtain ⟨hmem, hnd_r⟩ := eigenvalues_of_hasCartanType_E6 h hnd hall hW
    rw [DynkinType.coxeterNumber_E6, DynkinType.exponents_E6]
    exact multiset_eq_map_exp_of_mem_iff_of_nodup (h := 12) (by norm_num) (by decide) (by decide)
      hnd_r (by simpa [e6Exponents] using hmem)
  | E7 =>
    obtain ⟨hmem, hnd_r⟩ := eigenvalues_of_hasCartanType_E7 h hnd hall hW
    rw [DynkinType.coxeterNumber_E7, DynkinType.exponents_E7]
    exact multiset_eq_map_exp_of_mem_iff_of_nodup (h := 18) (by norm_num) (by decide) (by decide)
      hnd_r (by simpa [e7Exponents] using hmem)
  | E8 =>
    obtain ⟨hmem, hnd_r⟩ := eigenvalues_of_hasCartanType_E8 h hnd hall hW
    rw [DynkinType.coxeterNumber_E8, DynkinType.exponents_E8]
    exact multiset_eq_map_exp_of_mem_iff_of_nodup (h := 30) (by norm_num) (by decide) (by decide)
      hnd_r (by simpa [e8Exponents] using hmem)
  | F4 =>
    obtain ⟨hmem, hnd_r⟩ := eigenvalues_of_hasCartanType_F4 h hnd hall hW
    rw [DynkinType.coxeterNumber_F4, DynkinType.exponents_F4]
    exact multiset_eq_map_exp_of_mem_iff_of_nodup (h := 12) (by norm_num) (by decide) (by decide)
      hnd_r (by simpa [f4Exponents] using hmem)
  | G2 =>
    obtain ⟨hmem, hnd_r⟩ := eigenvalues_of_hasCartanType_G2 h hnd hall hW
    rw [DynkinType.coxeterNumber_G2, DynkinType.exponents_G2]
    exact multiset_eq_map_exp_of_mem_iff_of_nodup (h := 6) (by norm_num) (by decide) (by decide)
      hnd_r (by simpa [g2Exponents] using hmem)

/-- **Every primitive `h`-th root of unity `exp (2πi e / h)` (`e < h`, `gcd(e, h) = 1`) is an
eigenvalue of every Coxeter element of a base of valid Cartan type `t`.** -/
theorem mem_roots_charpoly_of_hasCartanType_of_actsBy_of_coprime {t : DynkinType}
    (ht : t.Valid) {b : P.Base} (h : HasCartanType P b t) {l : List b.support}
    (hnd : l.Nodup) (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ}
    (hW : b.ActsBy (wordProd P b l) W) {e : ℕ} (he : e < t.coxeterNumber)
    (hcop : e.Coprime t.coxeterNumber) :
    Complex.exp (2 * Real.pi * Complex.I * (e / t.coxeterNumber)) ∈
      (W.map (Int.castRingHom ℂ)).charpoly.roots := by
  rw [roots_charpoly_of_hasCartanType_of_actsBy ht h hnd hall hW, Multiset.mem_map]
  exact ⟨e, Multiset.mem_coe.mpr (t.mem_exponents_of_coprime ht he hcop), rfl⟩

end TauCeti.Coxeter

end
