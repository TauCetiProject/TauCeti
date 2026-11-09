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

For each exceptional type, the characteristic polynomial of the matrix of a Coxeter element on the
simple roots is a product of cyclotomic polynomials, so the complex eigenvalues of that matrix are
roots of unity (`Matrix.mem_roots_charpoly_of_charpoly_eq_cyclotomic`). They are exactly the
`exp (2πi e / h)`, `e` running over the exponents of the type, each with multiplicity one. This
matrix describes the action on the span of the roots; the roots need not span the weight space, and
on a larger space the element can have further eigenvalues.

## Main definitions

* `TauCeti.Coxeter.e6Exponents` (and `e7`, `e8`, `f4`, `g2`): the exponents of the type.

## Main results

* `TauCeti.Coxeter.eigenvalues_of_hasCartanType_E8` (and `E7`, `E6`, `F4`, `G2`): the eigenvalues of
  the matrix of every Coxeter element on the simple roots, each simple.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. V, §6, and the plates of Ch. VI.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge University Press (1990),
  § 3.16.
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
  refine ⟨fun ζ => ?_, nodup_roots_charpoly_of_charpoly_eq_cyclotomic_mul (by norm_num)
    (by norm_num) (by norm_num) hc⟩
  have h4 : (4 : ℂ) / 12 = 1 / 3 := by norm_num
  have h8 : (8 : ℂ) / 12 = 2 / 3 := by norm_num
  rw [mem_roots_charpoly_of_charpoly_eq_cyclotomic_mul (by norm_num) (by norm_num) hc,
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
  refine ⟨fun ζ => ?_, nodup_roots_charpoly_of_charpoly_eq_cyclotomic_mul (by norm_num)
    (by norm_num) (by norm_num) hc⟩
  have h9 : (9 : ℂ) / 18 = 1 / 2 := by norm_num
  rw [mem_roots_charpoly_of_charpoly_eq_cyclotomic_mul (by norm_num) (by norm_num) hc,
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
  refine ⟨fun ζ => ?_, nodup_roots_charpoly_of_charpoly_eq_cyclotomic (by norm_num) hc⟩
  rw [mem_roots_charpoly_of_charpoly_eq_cyclotomic (by norm_num) hc, ← e8Exponents_eq_filter]
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
  refine ⟨fun ζ => ?_, nodup_roots_charpoly_of_charpoly_eq_cyclotomic (by norm_num) hc⟩
  rw [mem_roots_charpoly_of_charpoly_eq_cyclotomic (by norm_num) hc, ← f4Exponents_eq_filter]
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
  refine ⟨fun ζ => ?_, nodup_roots_charpoly_of_charpoly_eq_cyclotomic (by norm_num) hc⟩
  rw [mem_roots_charpoly_of_charpoly_eq_cyclotomic (by norm_num) hc, ← g2Exponents_eq_filter]
  norm_num

end TauCeti.Coxeter

end
