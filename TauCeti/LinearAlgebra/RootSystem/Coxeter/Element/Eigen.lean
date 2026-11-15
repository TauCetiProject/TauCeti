/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.Every
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Exponents
public import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Eigenvalues of Coxeter elements: `exp (2πi e / h)` over the exponents

For each exceptional type, the characteristic polynomial of the matrix of a Coxeter element on the
simple roots is a product of cyclotomic polynomials, so the complex eigenvalues of that matrix are
roots of unity (`Matrix.mem_roots_charpoly_of_charpoly_eq_cyclotomic`). They are exactly the
`exp (2πi e / h)`, `e` running over `DynkinType.exponents`, each with multiplicity one. This matrix
describes the action on the span of the roots; the roots need not span the weight space, and on a
larger space the element can have further eigenvalues.

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

variable {ι R M N : Type*} [DecidableEq ι] [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {P : RootPairing ι R M N} [P.IsCrystallographic] [IsDomain R]
  [CharZero R]

/-- **Eigenvalues of the matrix of every Coxeter element of type `E₆` on the simple roots**:
`exp (2πi e / 12)` for the exponents `e = 1, 4, 5, 7, 8, 11`, each once. -/
theorem eigenvalues_of_hasCartanType_E6 {b : P.Base} (h : HasCartanType P b .E6)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ}
    (hW : b.ActsBy (wordProd P b l) W) :
    (∀ ζ : ℂ, ζ ∈ (W.map (Int.castRingHom ℂ)).charpoly.roots ↔
      ∃ e ∈ DynkinType.E6.exponents,
        Complex.exp (2 * Real.pi * Complex.I * (e / DynkinType.E6.coxeterNumber)) = ζ) ∧
      (W.map (Int.castRingHom ℂ)).charpoly.roots.Nodup := by
  have hc := charpoly_of_hasCartanType_E6_of_actsBy h hnd hall hW
  refine ⟨fun ζ => ?_, nodup_roots_charpoly_of_charpoly_eq_cyclotomic_mul (by norm_num) hc⟩
  have h4 : (4 : ℂ) / 12 = 1 / 3 := by norm_num
  have h8 : (8 : ℂ) / 12 = 2 / 3 := by norm_num
  rw [mem_roots_charpoly_of_charpoly_eq_cyclotomic_mul hc,
    show (List.range 12).filter (Nat.Coprime · 12) = [1, 5, 7, 11] by decide,
    show (List.range 3).filter (Nat.Coprime · 3) = [1, 2] by decide,
    DynkinType.exponents_E6, DynkinType.coxeterNumber_E6]
  simp only [List.mem_cons, List.not_mem_nil, Multiset.insert_eq_cons, Multiset.mem_cons,
    Multiset.mem_singleton, or_false, exists_eq_or_imp, exists_eq_left, Nat.cast_one,
    Nat.cast_ofNat, h4, h8]
  tauto

/-- **Eigenvalues of the matrix of every Coxeter element of type `E₇` on the simple roots**:
`exp (2πi e / 18)` for the exponents `e = 1, 5, 7, 9, 11, 13, 17`, each once. -/
theorem eigenvalues_of_hasCartanType_E7 {b : P.Base} (h : HasCartanType P b .E7)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ}
    (hW : b.ActsBy (wordProd P b l) W) :
    (∀ ζ : ℂ, ζ ∈ (W.map (Int.castRingHom ℂ)).charpoly.roots ↔
      ∃ e ∈ DynkinType.E7.exponents,
        Complex.exp (2 * Real.pi * Complex.I * (e / DynkinType.E7.coxeterNumber)) = ζ) ∧
      (W.map (Int.castRingHom ℂ)).charpoly.roots.Nodup := by
  have hc := charpoly_of_hasCartanType_E7_of_actsBy h hnd hall hW
  refine ⟨fun ζ => ?_, nodup_roots_charpoly_of_charpoly_eq_cyclotomic_mul (by norm_num) hc⟩
  have h9 : (9 : ℂ) / 18 = 1 / 2 := by norm_num
  rw [mem_roots_charpoly_of_charpoly_eq_cyclotomic_mul hc,
    show (List.range 18).filter (Nat.Coprime · 18) = [1, 5, 7, 11, 13, 17] by decide,
    show (List.range 2).filter (Nat.Coprime · 2) = [1] by decide,
    DynkinType.exponents_E7, DynkinType.coxeterNumber_E7]
  simp only [List.mem_cons, List.not_mem_nil, Multiset.insert_eq_cons, Multiset.mem_cons,
    Multiset.mem_singleton, or_false, exists_eq_or_imp, exists_eq_left, Nat.cast_one,
    Nat.cast_ofNat, h9]
  tauto

/-- **Eigenvalues of the matrix of every Coxeter element of type `E₈` on the simple roots**:
`exp (2πi e / 30)` for the exponents `e = 1, 7, 11, 13, 17, 19, 23, 29`, each once. -/
theorem eigenvalues_of_hasCartanType_E8 {b : P.Base} (h : HasCartanType P b .E8)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ}
    (hW : b.ActsBy (wordProd P b l) W) :
    (∀ ζ : ℂ, ζ ∈ (W.map (Int.castRingHom ℂ)).charpoly.roots ↔
      ∃ e ∈ DynkinType.E8.exponents,
        Complex.exp (2 * Real.pi * Complex.I * (e / DynkinType.E8.coxeterNumber)) = ζ) ∧
      (W.map (Int.castRingHom ℂ)).charpoly.roots.Nodup := by
  have hc := charpoly_of_hasCartanType_E8_of_actsBy h hnd hall hW
  refine ⟨fun ζ => ?_, nodup_roots_charpoly_of_charpoly_eq_cyclotomic hc⟩
  rw [mem_roots_charpoly_of_charpoly_eq_cyclotomic hc,
    show (List.range 30).filter (Nat.Coprime · 30) = [1, 7, 11, 13, 17, 19, 23, 29] by decide,
    DynkinType.exponents_E8, DynkinType.coxeterNumber_E8]
  simp

/-- **Eigenvalues of the matrix of every Coxeter element of type `F₄` on the simple roots**:
`exp (2πi e / 12)` for the exponents `e = 1, 5, 7, 11`, each once. -/
theorem eigenvalues_of_hasCartanType_F4 {b : P.Base} (h : HasCartanType P b .F4)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ}
    (hW : b.ActsBy (wordProd P b l) W) :
    (∀ ζ : ℂ, ζ ∈ (W.map (Int.castRingHom ℂ)).charpoly.roots ↔
      ∃ e ∈ DynkinType.F4.exponents,
        Complex.exp (2 * Real.pi * Complex.I * (e / DynkinType.F4.coxeterNumber)) = ζ) ∧
      (W.map (Int.castRingHom ℂ)).charpoly.roots.Nodup := by
  have hc := charpoly_of_hasCartanType_F4_of_actsBy h hnd hall hW
  refine ⟨fun ζ => ?_, nodup_roots_charpoly_of_charpoly_eq_cyclotomic hc⟩
  rw [mem_roots_charpoly_of_charpoly_eq_cyclotomic hc,
    show (List.range 12).filter (Nat.Coprime · 12) = [1, 5, 7, 11] by decide,
    DynkinType.exponents_F4, DynkinType.coxeterNumber_F4]
  simp

/-- **Eigenvalues of the matrix of every Coxeter element of type `G₂` on the simple roots**:
`exp (2πi e / 6)` for the exponents `e = 1, 5`, each once. -/
theorem eigenvalues_of_hasCartanType_G2 {b : P.Base} (h : HasCartanType P b .G2)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ}
    (hW : b.ActsBy (wordProd P b l) W) :
    (∀ ζ : ℂ, ζ ∈ (W.map (Int.castRingHom ℂ)).charpoly.roots ↔
      ∃ e ∈ DynkinType.G2.exponents,
        Complex.exp (2 * Real.pi * Complex.I * (e / DynkinType.G2.coxeterNumber)) = ζ) ∧
      (W.map (Int.castRingHom ℂ)).charpoly.roots.Nodup := by
  have hc := charpoly_of_hasCartanType_G2_of_actsBy h hnd hall hW
  refine ⟨fun ζ => ?_, nodup_roots_charpoly_of_charpoly_eq_cyclotomic hc⟩
  rw [mem_roots_charpoly_of_charpoly_eq_cyclotomic hc,
    show (List.range 6).filter (Nat.Coprime · 6) = [1, 5] by decide,
    DynkinType.exponents_G2, DynkinType.coxeterNumber_G2]
  simp
end TauCeti.Coxeter

end
