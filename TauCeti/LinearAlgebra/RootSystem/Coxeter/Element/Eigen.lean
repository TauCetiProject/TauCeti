/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.Every
public import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Eigenvalues of Coxeter elements: `exp (2πi e / h)` over the exponents

If an integer matrix has characteristic polynomial `Φ_h`, its complex eigenvalues are the
`exp (2πi e / h)` with `e < h` coprime to `h`, each once
(`TauCeti.Coxeter.mem_roots_charpoly_of_charpoly_eq_cyclotomic`). For `E₈`, `F₄` and `G₂` the
exponents are exactly the residues coprime to `h`, so every Coxeter element of these types has
eigenvalues `exp (2πi e / h)` over the exponents, each with multiplicity one.
-/

@[expose] public section

open Matrix Polynomial RootPairing TauCeti

namespace TauCeti.Coxeter

theorem mem_roots_charpoly_of_charpoly_eq_cyclotomic {κ : Type*} [Fintype κ] [DecidableEq κ]
    {M : Matrix κ κ ℤ} {h : ℕ} (hh : h ≠ 0) (hM : M.charpoly = cyclotomic h ℤ) (ζ : ℂ) :
    ζ ∈ (M.map (Int.castRingHom ℂ)).charpoly.roots ↔
      ∃ e ∈ (List.range h).filter (Nat.Coprime · h),
        Complex.exp (2 * Real.pi * Complex.I * (e / h)) = ζ := by
  have : NeZero (h : ℂ) := ⟨Nat.cast_ne_zero.2 hh⟩
  rw [charpoly_map, hM, map_cyclotomic, cyclotomic.roots_eq_primitiveRoots_val, Finset.mem_val,
    mem_primitiveRoots (Nat.pos_of_ne_zero hh), Complex.isPrimitiveRoot_iff ζ h hh]
  simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi, hc, h⟩; exact ⟨i, ⟨hi, hc⟩, h⟩
  · rintro ⟨i, ⟨hi, hc⟩, h⟩; exact ⟨i, hi, hc, h⟩

theorem nodup_roots_charpoly_of_charpoly_eq_cyclotomic {κ : Type*} [Fintype κ] [DecidableEq κ]
    {M : Matrix κ κ ℤ} {h : ℕ} (hh : h ≠ 0) (hM : M.charpoly = cyclotomic h ℤ) :
    (M.map (Int.castRingHom ℂ)).charpoly.roots.Nodup := by
  have : NeZero (h : ℂ) := ⟨Nat.cast_ne_zero.2 hh⟩
  rw [charpoly_map, hM, map_cyclotomic]
  exact roots_cyclotomic_nodup

/-- The exponents of `F₄`. -/
def f4Exponents : List ℕ := [1, 5, 7, 11]

/-- The exponents of `G₂`. -/
def g2Exponents : List ℕ := [1, 5]

theorem e8Exponents_eq : (List.range 30).filter (Nat.Coprime · 30) = e8Exponents := by decide
theorem f4Exponents_eq : (List.range 12).filter (Nat.Coprime · 12) = f4Exponents := by decide
theorem g2Exponents_eq : (List.range 6).filter (Nat.Coprime · 6) = g2Exponents := by decide

variable {ι R M N : Type*} [DecidableEq ι] [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {P : RootPairing ι R M N} [P.IsCrystallographic] [IsDomain R]
  [CharZero R]

/-- **Eigenvalues of every Coxeter element of type `E₈`**: `exp (2πi e / 30)` for the exponents
`e = 1, 7, 11, 13, 17, 19, 23, 29`, each once. -/
theorem eigenvalues_of_hasCartanType_E8 {b : P.Base} (h : HasCartanType P b .E8)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ}
    (hW : ActsBy b (wordProd P b l) W) :
    (∀ ζ : ℂ, ζ ∈ (W.map (Int.castRingHom ℂ)).charpoly.roots ↔
      ∃ e ∈ e8Exponents, Complex.exp (2 * Real.pi * Complex.I * (e / 30)) = ζ) ∧
      (W.map (Int.castRingHom ℂ)).charpoly.roots.Nodup := by
  have hc := charpoly_of_actsBy_of_hasCartanType_E8 h hnd hall hW
  refine ⟨fun ζ => ?_, nodup_roots_charpoly_of_charpoly_eq_cyclotomic (by norm_num) hc⟩
  rw [mem_roots_charpoly_of_charpoly_eq_cyclotomic (by norm_num) hc, e8Exponents_eq]
  norm_num

/-- **Eigenvalues of every Coxeter element of type `F₄`**: `exp (2πi e / 12)` for the exponents
`e = 1, 5, 7, 11`, each once. -/
theorem eigenvalues_of_hasCartanType_F4 {b : P.Base} (h : HasCartanType P b .F4)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ}
    (hW : ActsBy b (wordProd P b l) W) :
    (∀ ζ : ℂ, ζ ∈ (W.map (Int.castRingHom ℂ)).charpoly.roots ↔
      ∃ e ∈ f4Exponents, Complex.exp (2 * Real.pi * Complex.I * (e / 12)) = ζ) ∧
      (W.map (Int.castRingHom ℂ)).charpoly.roots.Nodup := by
  have hc := charpoly_of_actsBy_of_hasCartanType_F4 h hnd hall hW
  refine ⟨fun ζ => ?_, nodup_roots_charpoly_of_charpoly_eq_cyclotomic (by norm_num) hc⟩
  rw [mem_roots_charpoly_of_charpoly_eq_cyclotomic (by norm_num) hc, f4Exponents_eq]
  norm_num

/-- **Eigenvalues of every Coxeter element of type `G₂`**: `exp (2πi e / 6)` for the exponents
`e = 1, 5`, each once. -/
theorem eigenvalues_of_hasCartanType_G2 {b : P.Base} (h : HasCartanType P b .G2)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ}
    (hW : ActsBy b (wordProd P b l) W) :
    (∀ ζ : ℂ, ζ ∈ (W.map (Int.castRingHom ℂ)).charpoly.roots ↔
      ∃ e ∈ g2Exponents, Complex.exp (2 * Real.pi * Complex.I * (e / 6)) = ζ) ∧
      (W.map (Int.castRingHom ℂ)).charpoly.roots.Nodup := by
  have hc := charpoly_of_actsBy_of_hasCartanType_G2 h hnd hall hW
  refine ⟨fun ζ => ?_, nodup_roots_charpoly_of_charpoly_eq_cyclotomic (by norm_num) hc⟩
  rw [mem_roots_charpoly_of_charpoly_eq_cyclotomic (by norm_num) hc, g2Exponents_eq]
  norm_num

omit [DecidableEq ι] [P.IsCrystallographic] [IsDomain R] [CharZero R] in
theorem mem_roots_charpoly_of_charpoly_eq_cyclotomic_mul {κ : Type*} [Fintype κ] [DecidableEq κ]
    {M : Matrix κ κ ℤ} {a c : ℕ} (ha : a ≠ 0) (hc : c ≠ 0)
    (hM : M.charpoly = cyclotomic a ℤ * cyclotomic c ℤ) (ζ : ℂ) :
    ζ ∈ (M.map (Int.castRingHom ℂ)).charpoly.roots ↔
      (∃ e ∈ (List.range a).filter (Nat.Coprime · a),
        Complex.exp (2 * Real.pi * Complex.I * (e / a)) = ζ) ∨
      ∃ e ∈ (List.range c).filter (Nat.Coprime · c),
        Complex.exp (2 * Real.pi * Complex.I * (e / c)) = ζ := by
  have hMa : (M.map (Int.castRingHom ℂ)).charpoly = cyclotomic a ℂ * cyclotomic c ℂ := by
    rw [charpoly_map, hM, Polynomial.map_mul, map_cyclotomic, map_cyclotomic]
  have : NeZero (a : ℂ) := ⟨Nat.cast_ne_zero.2 ha⟩
  have : NeZero (c : ℂ) := ⟨Nat.cast_ne_zero.2 hc⟩
  rw [hMa, roots_mul (mul_ne_zero (cyclotomic_ne_zero a ℂ) (cyclotomic_ne_zero c ℂ)),
    Multiset.mem_add, cyclotomic.roots_eq_primitiveRoots_val,
    cyclotomic.roots_eq_primitiveRoots_val, Finset.mem_val, Finset.mem_val,
    mem_primitiveRoots (Nat.pos_of_ne_zero ha), mem_primitiveRoots (Nat.pos_of_ne_zero hc),
    Complex.isPrimitiveRoot_iff ζ a ha, Complex.isPrimitiveRoot_iff ζ c hc]
  simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro (⟨i, hi, hco, h⟩ | ⟨i, hi, hco, h⟩)
    exacts [Or.inl ⟨i, ⟨hi, hco⟩, h⟩, Or.inr ⟨i, ⟨hi, hco⟩, h⟩]
  · rintro (⟨i, ⟨hi, hco⟩, h⟩ | ⟨i, ⟨hi, hco⟩, h⟩)
    exacts [Or.inl ⟨i, hi, hco, h⟩, Or.inr ⟨i, hi, hco, h⟩]

/-- The exponents of `E₆`. -/
def e6Exponents : List ℕ := [1, 4, 5, 7, 8, 11]

/-- The exponents of `E₇`. -/
def e7Exponents : List ℕ := [1, 5, 7, 9, 11, 13, 17]

/-- **Eigenvalues of every Coxeter element of type `E₆`**: `exp (2πi e / 12)` for the exponents
`e = 1, 4, 5, 7, 8, 11`. -/
theorem eigenvalues_of_hasCartanType_E6 {b : P.Base} (h : HasCartanType P b .E6)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ}
    (hW : ActsBy b (wordProd P b l) W) (ζ : ℂ) :
    ζ ∈ (W.map (Int.castRingHom ℂ)).charpoly.roots ↔
      ∃ e ∈ e6Exponents, Complex.exp (2 * Real.pi * Complex.I * (e / 12)) = ζ := by
  rw [mem_roots_charpoly_of_charpoly_eq_cyclotomic_mul (by norm_num) (by norm_num)
    (charpoly_of_actsBy_of_hasCartanType_E6 h hnd hall hW),
    show (List.range 12).filter (Nat.Coprime · 12) = [1, 5, 7, 11] by decide,
    show (List.range 3).filter (Nat.Coprime · 3) = [1, 2] by decide]
  simp only [e6Exponents, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
    exists_eq_left]
  norm_num
  tauto

/-- **Eigenvalues of every Coxeter element of type `E₇`**: `exp (2πi e / 18)` for the exponents
`e = 1, 5, 7, 9, 11, 13, 17`. -/
theorem eigenvalues_of_hasCartanType_E7 {b : P.Base} (h : HasCartanType P b .E7)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ}
    (hW : ActsBy b (wordProd P b l) W) (ζ : ℂ) :
    ζ ∈ (W.map (Int.castRingHom ℂ)).charpoly.roots ↔
      ∃ e ∈ e7Exponents, Complex.exp (2 * Real.pi * Complex.I * (e / 18)) = ζ := by
  rw [mem_roots_charpoly_of_charpoly_eq_cyclotomic_mul (by norm_num) (by norm_num)
    (charpoly_of_actsBy_of_hasCartanType_E7 h hnd hall hW),
    show (List.range 18).filter (Nat.Coprime · 18) = [1, 5, 7, 11, 13, 17] by decide,
    show (List.range 2).filter (Nat.Coprime · 2) = [1] by decide]
  simp only [e7Exponents, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
    exists_eq_left]
  norm_num
  tauto

omit [DecidableEq ι] [P.IsCrystallographic] [IsDomain R] [CharZero R] in
/-- Two distinct cyclotomic factors have disjoint roots, so the eigenvalues are simple. -/
theorem nodup_roots_charpoly_of_charpoly_eq_cyclotomic_mul {κ : Type*} [Fintype κ]
    [DecidableEq κ] {M : Matrix κ κ ℤ} {a c : ℕ} (ha : a ≠ 0) (hc : c ≠ 0) (hac : a ≠ c)
    (hM : M.charpoly = cyclotomic a ℤ * cyclotomic c ℤ) :
    (M.map (Int.castRingHom ℂ)).charpoly.roots.Nodup := by
  have : NeZero (a : ℂ) := ⟨Nat.cast_ne_zero.2 ha⟩
  have : NeZero (c : ℂ) := ⟨Nat.cast_ne_zero.2 hc⟩
  rw [charpoly_map, hM, Polynomial.map_mul, map_cyclotomic, map_cyclotomic,
    roots_mul (mul_ne_zero (cyclotomic_ne_zero a ℂ) (cyclotomic_ne_zero c ℂ)),
    Multiset.nodup_add]
  refine ⟨roots_cyclotomic_nodup, roots_cyclotomic_nodup, Multiset.disjoint_left.2 ?_⟩
  intro ζ h1 h2
  rw [cyclotomic.roots_eq_primitiveRoots_val, Finset.mem_val,
    mem_primitiveRoots (Nat.pos_of_ne_zero ha)] at h1
  rw [cyclotomic.roots_eq_primitiveRoots_val, Finset.mem_val,
    mem_primitiveRoots (Nat.pos_of_ne_zero hc)] at h2
  exact hac (h1.unique h2)

/-- The eigenvalues of every Coxeter element of type `E₆` are simple. -/
theorem nodup_eigenvalues_of_hasCartanType_E6 {b : P.Base} (h : HasCartanType P b .E6)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ}
    (hW : ActsBy b (wordProd P b l) W) : (W.map (Int.castRingHom ℂ)).charpoly.roots.Nodup :=
  nodup_roots_charpoly_of_charpoly_eq_cyclotomic_mul (by norm_num) (by norm_num) (by norm_num)
    (charpoly_of_actsBy_of_hasCartanType_E6 h hnd hall hW)

/-- The eigenvalues of every Coxeter element of type `E₇` are simple. -/
theorem nodup_eigenvalues_of_hasCartanType_E7 {b : P.Base} (h : HasCartanType P b .E7)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ}
    (hW : ActsBy b (wordProd P b l) W) : (W.map (Int.castRingHom ℂ)).charpoly.roots.Nodup :=
  nodup_roots_charpoly_of_charpoly_eq_cyclotomic_mul (by norm_num) (by norm_num) (by norm_num)
    (charpoly_of_actsBy_of_hasCartanType_E7 h hnd hall hW)

/-! ### Acceptance checks on the exponent lists (roadmap §4 table) -/

/-- **Coprime-exponent theorem** for `E₈`: every `1 ≤ e < h` coprime to `h` is an exponent; the
same check for the other types follows. -/
theorem coprime_mem_e8Exponents : ∀ e ∈ List.range 30, Nat.Coprime e 30 → e ∈ e8Exponents := by
  decide

theorem coprime_mem_e7Exponents : ∀ e ∈ List.range 18, Nat.Coprime e 18 → e ∈ e7Exponents := by
  decide

theorem coprime_mem_e6Exponents : ∀ e ∈ List.range 12, Nat.Coprime e 12 → e ∈ e6Exponents := by
  decide

theorem coprime_mem_f4Exponents : ∀ e ∈ List.range 12, Nat.Coprime e 12 → e ∈ f4Exponents := by
  decide

theorem coprime_mem_g2Exponents : ∀ e ∈ List.range 6, Nat.Coprime e 6 → e ∈ g2Exponents := by
  decide

/-- `h = 1 + (largest exponent)`, there are `rank` exponents, and they sum to `rank * h / 2`,
the number of positive roots (`120`, `63`, `36`, `24`, `6`). -/
theorem exponents_data :
    (e8Exponents.length = 8 ∧ e8Exponents.max? = some 29 ∧ e8Exponents.sum = 8 * 30 / 2) ∧
    (e7Exponents.length = 7 ∧ e7Exponents.max? = some 17 ∧ e7Exponents.sum = 7 * 18 / 2) ∧
    (e6Exponents.length = 6 ∧ e6Exponents.max? = some 11 ∧ e6Exponents.sum = 6 * 12 / 2) ∧
    (f4Exponents.length = 4 ∧ f4Exponents.max? = some 11 ∧ f4Exponents.sum = 4 * 12 / 2) ∧
    (g2Exponents.length = 2 ∧ g2Exponents.max? = some 5 ∧ g2Exponents.sum = 2 * 6 / 2) := by
  decide

end TauCeti.Coxeter

end
