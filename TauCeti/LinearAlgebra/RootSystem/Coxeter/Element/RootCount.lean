/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.RootCount
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Assembly

/-!
# Additional Coxeter element spectral, order, and root-count corollaries

Supplements `TauCeti.LinearAlgebra.RootSystem.Coxeter.Number` with the remaining `TauCeti.Coxeter`
theorems for Coxeter elements and canonical Cartan Coxeter matrices:
* `TauCeti.Coxeter.two_le_orderOf_wordProd`: every Coxeter element of a finite irreducible reduced
  crystallographic root system has order at least `2`.
* `TauCeti.Coxeter.orderOf_wordProd_eq_natCard_div_card_support_of_hasCartanType`,
  `orderOf_wordProd_eq_natCard_div_card_support`, and
  `two_mul_card_posRootsFinset_eq_card_support_mul_orderOf_wordProd`: `h = |Φ| / r` and finset
  positive-root count.
* `TauCeti.Coxeter.roots_charpoly_coxeterElement`,
  `mem_roots_charpoly_coxeterElement_of_coprime`,
  `mem_roots_charpoly_of_hasCartanType_of_actsBy_of_coprime`, `roots_charpoly_of_actsBy`,
  `mem_roots_charpoly_of_actsBy_of_coprime`, and
  `exp_two_pi_I_div_orderOf_mem_roots_charpoly_of_actsBy`: complex eigenvalue multisets and
  primitive-root containment for `coxeterElement t.cartanMatrix` and `ActsBy` matrices.
-/

public section

open Matrix RootPairing TauCeti

namespace TauCeti.Coxeter

section HasCartanType

variable {ι R M N : Type*} [CommRing R] [CharZero R] [IsDomain R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic]

/-- **For any base `b` of valid Cartan type `t` and any Coxeter element `c`,
`orderOf c = |Φ| / r`.** -/
theorem orderOf_wordProd_eq_natCard_div_card_support_of_hasCartanType [Finite ι] [P.IsReduced]
    {b : P.Base} {t : DynkinType} (ht : t.Valid) (h : HasCartanType P b t) {l : List b.support}
    (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    orderOf (wordProd P b l) = Nat.card ι / b.support.card := by
  rw [h.orderOf_wordProd ht hnd hall]
  exact h.coxeterNumber_eq_natCard_div_card_support ht

/-- **Complex eigenvalue multiset of the canonical Coxeter matrix `Matrix.coxeterElement
t.cartanMatrix`** for any valid Dynkin type `t`: counted with multiplicity, the eigenvalues are
`exp (2πi e / h)` as `e` runs over `t.exponents`, where `h = t.coxeterNumber`. -/
theorem roots_charpoly_coxeterElement {t : DynkinType} (ht : t.Valid) :
    ((coxeterElement t.cartanMatrix).map (Int.castRingHom ℂ)).charpoly.roots =
      (t.exponents : Multiset ℕ).map fun e : ℕ =>
        Complex.exp (2 * Real.pi * Complex.I * (e / t.coxeterNumber)) := by
  let b₀ := t.simplyConnectedBase ht
  let l₀ : List b₀.support := Finset.univ.toList
  have hct := t.hasCartanType_simplyConnectedRootDatum ht
  have hcp := charpoly_of_hasCartanType_of_actsBy hct (Finset.nodup_toList _)
    (fun i => Finset.mem_toList.mpr (Finset.mem_univ i)) (b₀.actsBy_wordProd l₀)
  have hroots := hct.roots_charpoly_of_actsBy ht (Finset.nodup_toList _)
    (fun i => Finset.mem_toList.mpr (Finset.mem_univ i)) (b₀.actsBy_wordProd l₀)
  rw [Matrix.charpoly_map, ← hcp, ← Matrix.charpoly_map]
  simpa using hroots

/-- **Every primitive `h`-th root of unity `exp (2πi e / h)` (`e < h`, `gcd(e, h) = 1`) is an
eigenvalue of `Matrix.coxeterElement t.cartanMatrix`** for any valid Dynkin type `t`. -/
theorem mem_roots_charpoly_coxeterElement_of_coprime {t : DynkinType} (ht : t.Valid) {e : ℕ}
    (he : e < t.coxeterNumber) (hcop : e.Coprime t.coxeterNumber) :
    Complex.exp (2 * Real.pi * Complex.I * (e / t.coxeterNumber)) ∈
      ((coxeterElement t.cartanMatrix).map (Int.castRingHom ℂ)).charpoly.roots := by
  rw [roots_charpoly_coxeterElement ht, Multiset.mem_map]
  exact ⟨e, Multiset.mem_coe.mpr (t.mem_exponents_of_coprime ht he hcop), rfl⟩

/-- **Every primitive `h`-th root of unity `exp (2πi e / h)` (`e < h`, `gcd(e, h) = 1`) is an
eigenvalue of every Coxeter element of a base of valid Cartan type `t`.** -/
theorem mem_roots_charpoly_of_hasCartanType_of_actsBy_of_coprime [DecidableEq ι] {t : DynkinType}
    (ht : t.Valid) {b : P.Base} (h : HasCartanType P b t) {l : List b.support}
    (hnd : l.Nodup) (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ}
    (hW : b.ActsBy (wordProd P b l) W) {e : ℕ} (he : e < t.coxeterNumber)
    (hcop : e.Coprime t.coxeterNumber) :
    Complex.exp (2 * Real.pi * Complex.I * (e / t.coxeterNumber)) ∈
      (W.map (Int.castRingHom ℂ)).charpoly.roots := by
  rw [charpoly_map, charpoly_of_hasCartanType_of_actsBy h hnd hall hW, ← charpoly_map]
  exact mem_roots_charpoly_coxeterElement_of_coprime ht he hcop

end HasCartanType

section Irreducible

variable {ι R M N : Type*} [CommRing R] [CharZero R] [IsDomain R] [Finite ι]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible]

/-- **Every Coxeter element of a finite irreducible reduced crystallographic root system has order
at least `2`.** -/
theorem two_le_orderOf_wordProd {b : P.Base} {l : List b.support} (hnd : l.Nodup)
    (hall : ∀ i, i ∈ l) : 2 ≤ orderOf (wordProd P b l) := by
  rw [b.orderOf_wordProd_eq_coxeterNumber_classifiedDynkinType hnd hall]
  exact (classifiedDynkinType b).two_le_coxeterNumber (valid_classifiedDynkinType b)

/-- **`h = |Φ| / r`**: in any finite irreducible reduced crystallographic root system, every Coxeter
element has order equal to the number of roots divided by the rank. -/
theorem orderOf_wordProd_eq_natCard_div_card_support {b : P.Base} {l : List b.support}
    (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    orderOf (wordProd P b l) = Nat.card ι / b.support.card :=
  orderOf_wordProd_eq_natCard_div_card_support_of_hasCartanType (valid_classifiedDynkinType b)
    (hasCartanType_classifiedDynkinType b) hnd hall

/-- Finset version of
`RootPairing.Base.two_mul_ncard_posRoots_eq_card_support_mul_orderOf_wordProd`. -/
theorem two_mul_card_posRootsFinset_eq_card_support_mul_orderOf_wordProd {b : P.Base}
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    2 * (posRootsFinset P b).card = b.support.card * orderOf (wordProd P b l) := by
  rw [card_posRootsFinset,
    b.two_mul_ncard_posRoots_eq_card_support_mul_orderOf_wordProd hnd hall]

/-- **Complex eigenvalue multiset of any Coxeter element on the simple roots** of a finite
irreducible reduced crystallographic root system: `exp (2πi e / h)` as `e` runs over the exponents
of `classifiedDynkinType b`, where `h = orderOf (wordProd P b l)`. -/
theorem roots_charpoly_of_actsBy [DecidableEq ι] {b : P.Base} {l : List b.support}
    (hnd : l.Nodup) (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ}
    (hW : b.ActsBy (wordProd P b l) W) :
    (W.map (Int.castRingHom ℂ)).charpoly.roots =
      ((classifiedDynkinType b).exponents : Multiset ℕ).map fun e : ℕ =>
        Complex.exp (2 * Real.pi * Complex.I * (e / orderOf (wordProd P b l))) := by
  rw [b.orderOf_wordProd_eq_coxeterNumber_classifiedDynkinType hnd hall]
  simpa using (hasCartanType_classifiedDynkinType b).roots_charpoly_of_actsBy
    (valid_classifiedDynkinType b) hnd hall hW

/-- **Every primitive `h`-th root of unity is an eigenvalue of every Coxeter element** of a finite
irreducible reduced crystallographic root system on the simple roots, where
`h = orderOf (wordProd P b l)`. -/
theorem mem_roots_charpoly_of_actsBy_of_coprime [DecidableEq ι] {b : P.Base} {l : List b.support}
    (hnd : l.Nodup) (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ}
    (hW : b.ActsBy (wordProd P b l) W) {e : ℕ} (he : e < orderOf (wordProd P b l))
    (hcop : e.Coprime (orderOf (wordProd P b l))) :
    Complex.exp (2 * Real.pi * Complex.I * (e / orderOf (wordProd P b l))) ∈
      (W.map (Int.castRingHom ℂ)).charpoly.roots := by
  have hord := b.orderOf_wordProd_eq_coxeterNumber_classifiedDynkinType hnd hall
  rw [hord] at he hcop ⊢
  exact mem_roots_charpoly_of_hasCartanType_of_actsBy_of_coprime (valid_classifiedDynkinType b)
    (hasCartanType_classifiedDynkinType b) hnd hall hW he hcop

/-- **The primitive root `exp (2πi / h)` (`e = 1`) is an eigenvalue of every Coxeter element** of a
finite irreducible reduced crystallographic root system on the simple roots. -/
theorem exp_two_pi_I_div_orderOf_mem_roots_charpoly_of_actsBy [DecidableEq ι] {b : P.Base}
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
