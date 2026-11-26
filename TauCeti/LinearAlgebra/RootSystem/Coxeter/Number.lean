/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.Classical
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.Eigen
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Classification
public import TauCeti.LinearAlgebra.RootSystem.NumberOfRoots.Basic
public import TauCeti.LinearAlgebra.RootSystem.Positive
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Coefficient
import TauCeti.RingTheory.Polynomial.Cyclotomic.Exponents
import TauCeti.RingTheory.RootsOfUnity.Complex.Exp

/-!
# The Coxeter number, exponents, root counts, and coprime-exponent Galois conjugacy

This file packages the Coxeter number `TauCeti.DynkinType.coxeterNumber` and the exponent list
`TauCeti.DynkinType.exponents` across all crystallographic `DynkinType`s, proves the combinatorial
identities relating `numRoots`, `rank`, `coxeterNumber`, and `exponents`, transfers the root count
to any reduced crystallographic root pairing with a base of valid Cartan type (with no spanning
hypothesis), and combines the Cartan–Killing classification with the classical and exceptional
Coxeter calculations into uniform theorems for irreducible reduced crystallographic finite root
systems:

* **Order of any Coxeter element**:
  `orderOf (wordProd P b l) = (classifiedDynkinType b).coxeterNumber`, independent of both the base
  `b` and the ordering `l` of its simple reflections.
* **Root-count formula `|Φ| = r * h`**: `Nat.card ι = b.support.card * orderOf (wordProd P b l)`,
  and `2 * (posRoots P b).ncard = b.support.card * orderOf (wordProd P b l)`.
* **Eigenvalues with multiplicity**: over `ℂ`, the root multiset of
  `(P.weylGroupRootRep (wordProd P b l)).charpoly` consists of `exp (2πi e / h)` as `e` runs over
  `(classifiedDynkinType b).exponents`.
* **Galois conjugacy of coprime exponents**: for every valid Dynkin type, every natural number
  `a < h` coprime to `h` is an exponent (`TauCeti.DynkinType.mem_exponents_of_coprime`), so
  `exp (2πi a / h)` is always a Coxeter eigenvalue
  (`RootPairing.Base.mem_roots_charpoly_weylGroupRootRep_wordProd_of_coprime`).

## Main definitions

* `TauCeti.DynkinType.coxeterNumber`: the Coxeter number `h` of a `DynkinType`.
* `TauCeti.DynkinType.exponents`: the list of exponents `m₁, …, mᵣ` of a `DynkinType`.

## Main results

* `TauCeti.DynkinType.numRoots_eq_rank_mul_coxeterNumber`,
  `TauCeti.DynkinType.two_mul_sum_exponents_eq_numRoots`, and
  `TauCeti.DynkinType.perm_map_sub_exponents`: `|Φ| = r * h`, `2 * ∑ mᵢ = |Φ|`, and the duality
  permutation `mᵢ ↦ h - mᵢ`.
* `TauCeti.HasCartanType.natCard_eq_numRoots` and
  `TauCeti.HasCartanType.natCard_eq_card_support_mul_orderOf_wordProd`: `|Φ| = t.numRoots = r * h`
  for any reduced crystallographic root pairing with a base of valid Cartan type `t`.
* `TauCeti.DynkinType.mem_exponents_of_coprime`: every natural number `a < h` coprime to `h` is an
  exponent of a valid `DynkinType`.
* `RootPairing.Base.orderOf_wordProd_eq_orderOf_wordProd`,
  `RootPairing.Base.natCard_eq_card_support_mul_orderOf_wordProd`, and
  `RootPairing.Base.roots_charpoly_weylGroupRootRep_wordProd`: unconditional theorems for any
  irreducible reduced crystallographic finite root system.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. V, §6.2, and Ch. VI, §1.11.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge University Press (1990),
  §§ 3.16–3.20.
-/

public section

open Function Matrix Polynomial RootPairing Set TauCeti

namespace TauCeti

namespace DynkinType

/-! ### The Coxeter number and exponents of a Dynkin type -/

/-- The **Coxeter number** `h` of a `DynkinType`: `n + 1` for `Aₙ`, `2n` for `Bₙ` and `Cₙ`,
`2(n - 1)` for `Dₙ`, and `12, 18, 30, 12, 6` for `E₆, E₇, E₈, F₄, G₂`. -/
def coxeterNumber : DynkinType → ℕ
  | .A n => n + 1
  | .B n | .C n => 2 * n
  | .D n => 2 * (n - 1)
  | .E6 => 12
  | .E7 => 18
  | .E8 => 30
  | .F4 => 12
  | .G2 => 6

/-- The Coxeter number of `Aₙ` is `n + 1`. -/
@[simp] theorem coxeterNumber_A (n : ℕ) : (A n).coxeterNumber = n + 1 := (rfl)
/-- The Coxeter number of `Bₙ` is `2 * n`. -/
@[simp] theorem coxeterNumber_B (n : ℕ) : (B n).coxeterNumber = 2 * n := (rfl)
/-- The Coxeter number of `Cₙ` is `2 * n`. -/
@[simp] theorem coxeterNumber_C (n : ℕ) : (C n).coxeterNumber = 2 * n := (rfl)
/-- The Coxeter number of `Dₙ` is `2 * (n - 1)`. -/
@[simp] theorem coxeterNumber_D (n : ℕ) : (D n).coxeterNumber = 2 * (n - 1) := (rfl)
/-- The Coxeter number of `E₆` is `12`. -/
@[simp] theorem coxeterNumber_E6 : E6.coxeterNumber = 12 := (rfl)
/-- The Coxeter number of `E₇` is `18`. -/
@[simp] theorem coxeterNumber_E7 : E7.coxeterNumber = 18 := (rfl)
/-- The Coxeter number of `E₈` is `30`. -/
@[simp] theorem coxeterNumber_E8 : E8.coxeterNumber = 30 := (rfl)
/-- The Coxeter number of `F₄` is `12`. -/
@[simp] theorem coxeterNumber_F4 : F4.coxeterNumber = 12 := (rfl)
/-- The Coxeter number of `G₂` is `6`. -/
@[simp] theorem coxeterNumber_G2 : G2.coxeterNumber = 6 := (rfl)

/-- Every valid Dynkin type has Coxeter number at least `2`. -/
theorem two_le_coxeterNumber {t : DynkinType} (ht : t.Valid) : 2 ≤ t.coxeterNumber := by
  cases t <;> simp_all <;> omega

/-- Every valid Dynkin type has positive Coxeter number. -/
theorem coxeterNumber_pos {t : DynkinType} (ht : t.Valid) : 0 < t.coxeterNumber :=
  lt_of_lt_of_le zero_lt_two (two_le_coxeterNumber ht)

/-- **Combinatorial root-count identity**: `numRoots = rank * coxeterNumber` for every
`DynkinType`. -/
theorem numRoots_eq_rank_mul_coxeterNumber (t : DynkinType) :
    t.numRoots = t.rank * t.coxeterNumber := by
  cases t with
  | A n => simp
  | B n | C n | D n => simp; ring
  | E6 | E7 | E8 | F4 | G2 => decide

/-- The **exponents** `m₁, …, mᵣ` of a `DynkinType`, with multiplicity (so `n - 1` appears twice in
even type `Dₙ`). -/
def exponents : DynkinType → List ℕ
  | .A n => Coxeter.aExponents n
  | .B n => Coxeter.bExponents n
  | .C n => Coxeter.cExponents n
  | .D n => Coxeter.dExponents n
  | .E6 => Coxeter.e6Exponents
  | .E7 => Coxeter.e7Exponents
  | .E8 => Coxeter.e8Exponents
  | .F4 => Coxeter.f4Exponents
  | .G2 => Coxeter.g2Exponents

/-- The exponents of `Aₙ` are `aExponents n = [1, 2, …, n]`. -/
@[simp] theorem exponents_A (n : ℕ) : (A n).exponents = Coxeter.aExponents n := (rfl)
/-- The exponents of `Bₙ` are `bExponents n = [1, 3, …, 2n - 1]`. -/
@[simp] theorem exponents_B (n : ℕ) : (B n).exponents = Coxeter.bExponents n := (rfl)
/-- The exponents of `Cₙ` are `cExponents n = [1, 3, …, 2n - 1]`. -/
@[simp] theorem exponents_C (n : ℕ) : (C n).exponents = Coxeter.cExponents n := (rfl)
/-- The exponents of `Dₙ` are `dExponents n = [1, 3, …, 2n - 3, n - 1]`. -/
@[simp] theorem exponents_D (n : ℕ) : (D n).exponents = Coxeter.dExponents n := (rfl)
/-- The exponents of `E₆` are `[1, 4, 5, 7, 8, 11]`. -/
@[simp] theorem exponents_E6 : E6.exponents = Coxeter.e6Exponents := (rfl)
/-- The exponents of `E₇` are `[1, 5, 7, 9, 11, 13, 17]`. -/
@[simp] theorem exponents_E7 : E7.exponents = Coxeter.e7Exponents := (rfl)
/-- The exponents of `E₈` are `[1, 7, 11, 13, 17, 19, 23, 29]`. -/
@[simp] theorem exponents_E8 : E8.exponents = Coxeter.e8Exponents := (rfl)
/-- The exponents of `F₄` are `[1, 5, 7, 11]`. -/
@[simp] theorem exponents_F4 : F4.exponents = Coxeter.f4Exponents := (rfl)
/-- The exponents of `G₂` are `[1, 5]`. -/
@[simp] theorem exponents_G2 : G2.exponents = Coxeter.g2Exponents := (rfl)

/-- The number of exponents (counted with multiplicity) equals the rank. -/
@[simp]
theorem length_exponents (t : DynkinType) : t.exponents.length = t.rank := by
  cases t with
  | A n | B n | C n | D n => simp
  | E6 | E7 | E8 | F4 | G2 => decide

/-- `1` is an exponent of every valid Dynkin type. -/
theorem one_mem_exponents {t : DynkinType} (ht : t.Valid) : 1 ∈ t.exponents := by
  cases t with
  | A n | B n | C n | D n => simp at ht ⊢; omega
  | E6 | E7 | E8 | F4 | G2 => decide

/-- Every exponent of a valid Dynkin type is positive. -/
theorem pos_of_mem_exponents {t : DynkinType} (ht : t.Valid) {e : ℕ} (he : e ∈ t.exponents) :
    0 < e := by
  cases t with
  | A n => simp at he; omega
  | B n | C n =>
    simp only [exponents_B, exponents_C, Coxeter.mem_bExponents, Coxeter.mem_cExponents] at he
    obtain ⟨k, rfl⟩ := he.1; omega
  | D n =>
    have hn := valid_D.mp ht
    simp only [exponents_D, Coxeter.mem_dExponents] at he
    rcases he with ⟨⟨k, rfl⟩, -⟩ | ⟨-, rfl⟩ <;> omega
  | E6 | E7 | E8 | F4 | G2 => revert e; decide

/-- Every exponent of a valid Dynkin type is strictly less than the Coxeter number. -/
theorem lt_coxeterNumber_of_mem_exponents {t : DynkinType} (ht : t.Valid) {e : ℕ}
    (he : e ∈ t.exponents) : e < t.coxeterNumber := by
  cases t with
  | A n | B n | C n | D n => simp at ht he ⊢; omega
  | E6 | E7 | E8 | F4 | G2 => revert e; decide

private theorem two_mul_sum_aExponents (n : ℕ) : 2 * (Coxeter.aExponents n).sum = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ m ih =>
    simp only [Coxeter.aExponents_def, List.range_succ, List.map_append, List.map_singleton,
      List.sum_append, List.sum_singleton] at ih ⊢
    linarith

private theorem sum_bExponents (n : ℕ) : (Coxeter.bExponents n).sum = n ^ 2 := by
  induction n with
  | zero => simp
  | succ m ih =>
    simp only [Coxeter.bExponents_def, List.range_succ, List.map_append, List.map_singleton,
      List.sum_append, List.sum_singleton] at ih ⊢
    nlinarith

/-- **Twice the sum of the exponents equals the number of roots** (so the sum of the exponents
equals the number of positive roots). -/
theorem two_mul_sum_exponents_eq_numRoots (t : DynkinType) :
    2 * t.exponents.sum = t.numRoots := by
  cases t with
  | A n => exact two_mul_sum_aExponents n
  | B n => simp [sum_bExponents]
  | C n => simp [Coxeter.cExponents_def, sum_bExponents]
  | D n =>
    rcases n with _ | m
    · simp
    · simp only [exponents_D, Coxeter.dExponents_succ, List.sum_append, List.sum_singleton,
        sum_bExponents, numRoots_D, Nat.add_sub_cancel]
      ring
  | E6 | E7 | E8 | F4 | G2 => decide

private theorem perm_map_two_mul_sub (m : ℕ) :
    ((Coxeter.bExponents m).map (2 * m - ·)).Perm (Coxeter.bExponents m) := by
  rw [Coxeter.bExponents_def]
  have hrev : ((List.range m).map fun k => 2 * k + 1).map (2 * m - ·) =
      ((List.range m).map fun k => 2 * k + 1).reverse := by
    rw [← List.map_reverse, List.map_map, List.range_eq_range' (n := m), List.reverse_range',
      List.map_map, ← List.range_eq_range']
    exact List.map_congr_left fun k hk => by rw [List.mem_range] at hk; simp; omega
  rw [hrev]
  exact List.reverse_perm _

/-- **Duality of exponents**: `e ↦ h - e` permutes `t.exponents` (preserving multiplicities). -/
theorem perm_map_sub_exponents (t : DynkinType) :
    (t.exponents.map (t.coxeterNumber - ·)).Perm t.exponents := by
  cases t with
  | A n =>
    simp only [exponents_A, coxeterNumber_A, Coxeter.aExponents_def]
    have hrev : ((List.range n).map (· + 1)).map (n + 1 - ·) =
        ((List.range n).map (· + 1)).reverse := by
      rw [← List.map_reverse, List.map_map, List.range_eq_range' (n := n), List.reverse_range',
        List.map_map, ← List.range_eq_range']
      exact List.map_congr_left fun k hk => by rw [List.mem_range] at hk; simp; omega
    rw [hrev]
    exact List.reverse_perm _
  | B n => exact perm_map_two_mul_sub n
  | C n => simpa [Coxeter.cExponents_def] using perm_map_two_mul_sub n
  | D n =>
    rcases n with _ | m
    · simp
    · have hsub : 2 * m - m = m := by omega
      simp only [exponents_D, coxeterNumber_D, Coxeter.dExponents_succ, Nat.add_sub_cancel,
        List.map_append, List.map_singleton, hsub]
      exact (perm_map_two_mul_sub m).append_right [m]
  | E6 | E7 | E8 | F4 | G2 => decide

end DynkinType

/-! ### Uniform theorems for a base of valid Cartan type -/

section HasCartanType

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] {P : RootPairing ι R M N}

/-- **A reduced crystallographic finite root pairing over a characteristic-zero domain whose base
has valid Cartan type `t` has `t.numRoots` roots** (with no `[P.IsRootSystem]` spanning
hypothesis). -/
theorem HasCartanType.natCard_eq_numRoots [Finite ι] [CharZero R] [IsDomain R]
    [P.IsCrystallographic] [P.IsReduced] {b : P.Base} {t : DynkinType} (h : HasCartanType P b t)
    (ht : t.Valid) : Nat.card ι = t.numRoots := by
  classical
  obtain ⟨e, he⟩ := (hasCartanType_iff b t).mp h
  have himg : (fun c : b.support → ℤ => c ∘ e.symm) '' range b.rootCoefficients =
      range (t.simpleRootCoefficients ht) := by
    rw [← b.iUnion_orbit_single_eq_range_rootCoefficients,
      ← t.iUnion_orbit_single_eq_range_simpleRootCoefficients ht]
    refine subset_antisymm ?_ ?_
    · rintro _ ⟨c, hc, rfl⟩
      obtain ⟨k, hk⟩ := mem_iUnion.mp hc
      refine mem_iUnion.mpr ⟨e k, ?_⟩
      have horb := Matrix.comp_equiv_mem_orbit b.cartanMatrix b.cartanMatrix_apply_same
        t.cartanMatrix_apply_same e.symm
        (fun i j => by rw [he, Equiv.apply_symm_apply, Equiv.apply_symm_apply]) hk
      have hs : (Pi.single k 1 : b.support → ℤ) ∘ e.symm = Pi.single (e k) 1 := by
        ext i; simp [Pi.single_apply, Equiv.symm_apply_eq]
      rwa [hs] at horb
    · rintro d hd
      obtain ⟨i, hi⟩ := mem_iUnion.mp hd
      refine ⟨d ∘ e, mem_iUnion.mpr ⟨e.symm i, ?_⟩, by ext j; simp⟩
      have horb := Matrix.comp_equiv_mem_orbit t.cartanMatrix t.cartanMatrix_apply_same
        b.cartanMatrix_apply_same e he hi
      have hs : (Pi.single i 1 : Fin t.rank → ℤ) ∘ e = Pi.single (e.symm i) 1 := by
        ext k; simp [Pi.single_apply, Equiv.eq_symm_apply]
      rwa [hs] at horb
  have hinj : Injective (fun c : b.support → ℤ => c ∘ e.symm) := fun c₁ c₂ hc =>
    funext fun k => by simpa using congrFun hc (e k)
  rw [← Set.ncard_univ ι, ← Set.ncard_image_of_injective univ b.rootCoefficients_injective,
    image_univ, ← Set.ncard_image_of_injective _ hinj, himg, ← image_univ,
    Set.ncard_image_of_injective _ (t.simpleRootCoefficients_injective ht), Set.ncard_univ,
    Nat.card_fin]

/-- Twice the number of positive roots of a base of valid Cartan type `t` equals `t.numRoots`. -/
theorem HasCartanType.two_mul_ncard_posRoots_eq_numRoots [Finite ι] [CharZero R] [IsDomain R]
    [P.IsCrystallographic] [P.IsReduced] {b : P.Base} {t : DynkinType} (h : HasCartanType P b t)
    (ht : t.Valid) : 2 * (posRoots P b).ncard = t.numRoots :=
  (two_mul_ncard_posRoots P b).trans (h.natCard_eq_numRoots ht)

/-- **Every Coxeter element of a base of valid Cartan type `t` has order `t.coxeterNumber`.** -/
theorem HasCartanType.orderOf_wordProd [Finite ι] [CharZero R] [IsDomain R] [P.IsCrystallographic]
    {b : P.Base} {t : DynkinType} (h : HasCartanType P b t) (ht : t.Valid) {l : List b.support}
    (hnd : l.Nodup) (hall : ∀ i, i ∈ l) : orderOf (wordProd P b l) = t.coxeterNumber := by
  cases t with
  | A n => exact Coxeter.orderOf_wordProd_of_hasCartanType_A (DynkinType.valid_A.mp ht) h hnd hall
  | B n =>
    exact Coxeter.orderOf_wordProd_of_hasCartanType_B (by have := DynkinType.valid_B.mp ht; omega)
      h hnd hall
  | C n =>
    exact Coxeter.orderOf_wordProd_of_hasCartanType_C (by have := DynkinType.valid_C.mp ht; omega)
      h hnd hall
  | D n =>
    exact Coxeter.orderOf_wordProd_of_hasCartanType_D (by have := DynkinType.valid_D.mp ht; omega)
      h hnd hall
  | E6 => exact Coxeter.orderOf_wordProd_of_hasCartanType_E6 h hnd hall
  | E7 => exact Coxeter.orderOf_wordProd_of_hasCartanType_E7 h hnd hall
  | E8 => exact Coxeter.orderOf_wordProd_of_hasCartanType_E8 h hnd hall
  | F4 => exact Coxeter.orderOf_wordProd_of_hasCartanType_F4 h hnd hall
  | G2 => exact Coxeter.orderOf_wordProd_of_hasCartanType_G2 h hnd hall

/-- **Root-count formula `|Φ| = r * h`** for a base of valid Cartan type `t`. -/
theorem HasCartanType.natCard_eq_card_support_mul_orderOf_wordProd [Finite ι] [CharZero R]
    [IsDomain R] [P.IsCrystallographic] [P.IsReduced] {b : P.Base} {t : DynkinType}
    (h : HasCartanType P b t) (ht : t.Valid) {l : List b.support} (hnd : l.Nodup)
    (hall : ∀ i, i ∈ l) :
    Nat.card ι = b.support.card * orderOf (wordProd P b l) := by
  rw [h.natCard_eq_numRoots ht, t.numRoots_eq_rank_mul_coxeterNumber, h.card_support,
    h.orderOf_wordProd ht hnd hall]

/-- **Positive-root count `2 * |Φ⁺| = r * h`** for a base of valid Cartan type `t`. -/
theorem HasCartanType.two_mul_ncard_posRoots_eq_card_support_mul_orderOf_wordProd [Finite ι]
    [CharZero R] [IsDomain R] [P.IsCrystallographic] [P.IsReduced] {b : P.Base} {t : DynkinType}
    (h : HasCartanType P b t) (ht : t.Valid) {l : List b.support} (hnd : l.Nodup)
    (hall : ∀ i, i ∈ l) :
    2 * (posRoots P b).ncard = b.support.card * orderOf (wordProd P b l) :=
  (two_mul_ncard_posRoots P b).trans (h.natCard_eq_card_support_mul_orderOf_wordProd ht hnd hall)

/-- **Uniform complex eigenvalue multiset on the simple roots** for any base of valid Cartan type
`t`: `exp (2πi e / h)` as `e` runs over `t.exponents`, retaining multiplicity. -/
theorem HasCartanType.roots_charpoly_of_actsBy [DecidableEq ι] [CharZero R] [IsDomain R]
    [P.IsCrystallographic] {b : P.Base} {t : DynkinType} (h : HasCartanType P b t) (ht : t.Valid)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ}
    (hW : b.ActsBy (wordProd P b l) W) :
    (W.map (Int.castRingHom ℂ)).charpoly.roots =
      Multiset.ofList (t.exponents.map fun e : ℕ =>
        Complex.exp (2 * Real.pi * Complex.I * ((e : ℂ) / (t.coxeterNumber : ℂ)))) := by
  cases t with
  | A n => rw [Coxeter.roots_charpoly_of_hasCartanType_A_of_actsBy h hnd hall hW]; simp
  | B n =>
    rw [Coxeter.roots_charpoly_of_hasCartanType_B_of_actsBy
      (by have := DynkinType.valid_B.mp ht; omega) h hnd hall hW]; simp
  | C n =>
    rw [Coxeter.roots_charpoly_of_hasCartanType_C_of_actsBy
      (by have := DynkinType.valid_C.mp ht; omega) h hnd hall hW]; simp
  | D n =>
    have hn := DynkinType.valid_D.mp ht
    rw [Coxeter.roots_charpoly_of_hasCartanType_D_of_actsBy (by omega) h hnd hall hW]
    simp [Nat.cast_sub (by omega : 1 ≤ n)]
  | E6 => rw [Coxeter.roots_charpoly_of_hasCartanType_E6_of_actsBy h hnd hall hW]; simp
  | E7 => rw [Coxeter.roots_charpoly_of_hasCartanType_E7_of_actsBy h hnd hall hW]; simp
  | E8 => rw [Coxeter.roots_charpoly_of_hasCartanType_E8_of_actsBy h hnd hall hW]; simp
  | F4 => rw [Coxeter.roots_charpoly_of_hasCartanType_F4_of_actsBy h hnd hall hW]; simp
  | G2 => rw [Coxeter.roots_charpoly_of_hasCartanType_G2_of_actsBy h hnd hall hW]; simp

/-- **Uniform weight-space eigenvalue multiset** for any complex root system whose base has valid
Cartan type `t`. -/
theorem HasCartanType.roots_charpoly_weylGroupRootRep_wordProd {ι M N : Type*} [AddCommGroup M]
    [Module ℂ M] [AddCommGroup N] [Module ℂ N] {P : RootPairing ι ℂ M N} [P.IsRootSystem]
    [P.IsCrystallographic] [Module.Finite ℂ M] {b : P.Base} {t : DynkinType}
    (h : HasCartanType P b t) (ht : t.Valid) {l : List b.support} (hnd : l.Nodup)
    (hall : ∀ i, i ∈ l) :
    (P.weylGroupRootRep (wordProd P b l)).charpoly.roots =
      Multiset.ofList (t.exponents.map fun e : ℕ =>
        Complex.exp (2 * Real.pi * Complex.I * ((e : ℂ) / (t.coxeterNumber : ℂ)))) := by
  classical
  rw [(b.actsBy_wordProd l).charpoly_weylGroupRootRep, ← Matrix.charpoly_map]
  exact h.roots_charpoly_of_actsBy ht hnd hall (b.actsBy_wordProd l)

end HasCartanType

/-! ### Galois conjugacy: every coprime residue `< h` is an exponent -/

/-- **Every natural number `a < h` coprime to the Coxeter number `h` is an exponent** of a valid
`DynkinType`. -/
theorem DynkinType.mem_exponents_of_coprime {t : DynkinType} (ht : t.Valid) {a : ℕ}
    (ha : a < t.coxeterNumber) (hcop : a.Coprime t.coxeterNumber) : a ∈ t.exponents := by
  let b₀ := t.simplyConnectedBase ht
  let l₀ : List b₀.support := Finset.univ.toList
  let W₀ : Matrix b₀.support b₀.support ℤ := (l₀.map (reflMatrix b₀.cartanMatrix)).prod
  have hct := t.hasCartanType_simplyConnectedRootDatum ht
  have hroots := hct.roots_charpoly_of_actsBy ht (Finset.nodup_toList _)
    (fun i => Finset.mem_toList.mpr (Finset.mem_univ i)) (b₀.actsBy_wordProd l₀)
  set h := t.coxeterNumber
  have hh : 0 < h := t.coxeterNumber_pos ht
  simp_rw [← exp_two_pi_I_div_pow (h : ℂ)] at hroots
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / (h : ℂ))
  have hζ : IsPrimitiveRoot ζ h := Complex.isPrimitiveRoot_exp h hh.ne'
  set p : ℚ[X] := W₀.charpoly.map (Int.castRingHom ℚ)
  have hp_map : p.map (algebraMap ℚ ℂ) = (W₀.map (Int.castRingHom ℂ)).charpoly := by
    rw [Polynomial.map_map,
      Subsingleton.elim ((algebraMap ℚ ℂ).comp (Int.castRingHom ℚ)) (Int.castRingHom ℂ),
      Matrix.charpoly_map]
  have hcard : (W₀.map (Int.castRingHom ℂ)).charpoly.roots.card =
      (W₀.map (Int.castRingHom ℂ)).charpoly.natDegree := by
    rw [hroots, Multiset.coe_card, List.length_map, t.length_exponents,
      Matrix.charpoly_natDegree_eq_dim]
    exact hct.card_support.symm.trans (Fintype.card_coe b₀.support).symm
  have hprod : p.map (algebraMap ℚ ℂ) =
      ∏ i : Fin t.exponents.length, (X - Polynomial.C (ζ ^ t.exponents[i])) := by
    rw [hp_map, ← prod_multiset_X_sub_C_of_monic_of_roots_card_eq (Matrix.charpoly_monic _) hcard,
      hroots, Multiset.map_coe, Multiset.prod_coe, List.map_map]
    conv_lhs => rw [← List.ofFn_getElem (xs := t.exponents), List.map_ofFn, Fin.prod_ofFn]
    rfl
  have hp1 : (p.map (algebraMap ℚ ℂ)).IsRoot ζ := by
    rw [hp_map, ← mem_roots (Matrix.charpoly_monic _).ne_zero, hroots, Multiset.mem_coe,
      List.mem_map]
    exact ⟨1, t.one_mem_exponents ht, pow_one ζ⟩
  obtain ⟨i, hi⟩ := IsPrimitiveRoot.exists_eq_of_isRoot_of_map_eq_prod hζ hζ hp1
    (fun i => t.lt_coxeterNumber_of_mem_exponents ht (List.getElem_mem _)) hprod ha hcop
  exact hi ▸ List.getElem_mem _

end TauCeti

/-! ### Unconditional theorems for irreducible crystallographic finite root systems -/

namespace RootPairing.Base

section Irreducible

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] {P : RootPairing ι R M N} [Finite ι] [CharZero R] [IsDomain R]
  [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible]

/-- **Every Coxeter element of an irreducible reduced crystallographic finite root system has order
the Coxeter number of its classified Dynkin type.** -/
theorem orderOf_wordProd_eq_coxeterNumber_classifiedDynkinType (b : P.Base) {l : List b.support}
    (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    orderOf (wordProd P b l) = (classifiedDynkinType b).coxeterNumber :=
  (hasCartanType_classifiedDynkinType b).orderOf_wordProd (valid_classifiedDynkinType b) hnd hall

/-- **All Coxeter elements of an irreducible reduced crystallographic finite root system — across
all bases `b, b'` and all orderings `l, l'` of their simple reflections — have the same order.** -/
theorem orderOf_wordProd_eq_orderOf_wordProd (b b' : P.Base) {l : List b.support}
    {l' : List b'.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) (hnd' : l'.Nodup)
    (hall' : ∀ i, i ∈ l') : orderOf (wordProd P b l) = orderOf (wordProd P b' l') := by
  rw [orderOf_wordProd_eq_coxeterNumber_classifiedDynkinType b hnd hall,
    orderOf_wordProd_eq_coxeterNumber_classifiedDynkinType b' hnd' hall',
    b.classifiedDynkinType_eq_classifiedDynkinType b']

/-- **The root-count identity `|Φ| = r * h`** for an irreducible reduced crystallographic finite
root system: the number of roots equals the rank times the order of any Coxeter element. -/
theorem natCard_eq_card_support_mul_orderOf_wordProd (b : P.Base) {l : List b.support}
    (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    Nat.card ι = b.support.card * orderOf (wordProd P b l) :=
  (hasCartanType_classifiedDynkinType b).natCard_eq_card_support_mul_orderOf_wordProd
    (valid_classifiedDynkinType b) hnd hall

/-- **The positive-root count `2 * |Φ⁺| = r * h`** for an irreducible reduced crystallographic
finite root system. -/
theorem two_mul_ncard_posRoots_eq_card_support_mul_orderOf_wordProd (b : P.Base)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    2 * (posRoots P b).ncard = b.support.card * orderOf (wordProd P b l) :=
  (hasCartanType_classifiedDynkinType b).two_mul_ncard_posRoots_eq_card_support_mul_orderOf_wordProd
    (valid_classifiedDynkinType b) hnd hall

end Irreducible

section ComplexIrreducible

variable {ι M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
  {P : RootPairing ι ℂ M N} [Finite ι] [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced]
  [P.IsIrreducible] [Module.Finite ℂ M]

/-- **Eigenvalue multiset of any Coxeter element on the weight space** of an irreducible reduced
crystallographic finite root system over `ℂ`, with multiplicity. -/
theorem roots_charpoly_weylGroupRootRep_wordProd (b : P.Base) {l : List b.support} (hnd : l.Nodup)
    (hall : ∀ i, i ∈ l) :
    (P.weylGroupRootRep (wordProd P b l)).charpoly.roots =
      Multiset.ofList ((classifiedDynkinType b).exponents.map fun e : ℕ =>
        Complex.exp (2 * Real.pi * Complex.I *
          ((e : ℂ) / (orderOf (wordProd P b l) : ℂ)))) := by
  rw [orderOf_wordProd_eq_coxeterNumber_classifiedDynkinType b hnd hall]
  exact (hasCartanType_classifiedDynkinType b).roots_charpoly_weylGroupRootRep_wordProd
    (valid_classifiedDynkinType b) hnd hall

/-- **Every primitive-power `exp (2πi a / h)` with `a < h` coprime to the Coxeter number `h` is a
weight-space eigenvalue** of every Coxeter element of an irreducible reduced crystallographic finite
root system over `ℂ`. -/
theorem mem_roots_charpoly_weylGroupRootRep_wordProd_of_coprime (b : P.Base) {l : List b.support}
    (hnd : l.Nodup) (hall : ∀ i, i ∈ l) {a : ℕ} (ha : a < orderOf (wordProd P b l))
    (hcop : a.Coprime (orderOf (wordProd P b l))) :
    Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) / (orderOf (wordProd P b l) : ℂ))) ∈
      (P.weylGroupRootRep (wordProd P b l)).charpoly.roots := by
  rw [roots_charpoly_weylGroupRootRep_wordProd b hnd hall, Multiset.mem_coe, List.mem_map]
  rw [orderOf_wordProd_eq_coxeterNumber_classifiedDynkinType b hnd hall] at ha hcop
  exact ⟨a, (classifiedDynkinType b).mem_exponents_of_coprime (valid_classifiedDynkinType b) ha
    hcop, rfl⟩

end ComplexIrreducible

end RootPairing.Base

end
