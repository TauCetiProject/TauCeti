/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RootsOfUnity.Complex
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.Every
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Exponents
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Classification
public import TauCeti.LinearAlgebra.RootSystem.Positive
import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.Classical
import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.Eigen
import TauCeti.LinearAlgebra.RootSystem.FiniteType.NumberOfRoots
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Assembly
import TauCeti.RingTheory.Polynomial.Cyclotomic.Exponents

/-!
# Uniform Coxeter-element and exponent theorems across all Dynkin types

Assembling the classical families (`TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.Classical`) and
the exceptional families (`TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.Every`,
`TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.Eigen`) yields uniform theorems for any base of a
valid Cartan type `t`, and hence — through `TauCeti.classifiedDynkinType` — classification-free
theorems for any irreducible reduced crystallographic finite root system:

1. **Order of Coxeter elements**: every Coxeter element `wordProd P b l` has multiplicative order
   `t.coxeterNumber`, with `Nat.card ι = b.support.card * orderOf (wordProd P b l)` (`|Φ| = r h`).
2. **Eigenvalue multiset**: the characteristic polynomial of the integer matrix `W` describing any
   Coxeter element on the simple roots has complex root multiset
   `t.exponents.map (fun e => exp (2πi e / t.coxeterNumber))`, counted with multiplicity, and
   `t.exponents.sum = (posRoots P b).ncard` (`∑ eᵢ = |Φ⁺|`).
3. **Coprime residues are exponents**: every `a < t.coxeterNumber` coprime to `t.coxeterNumber`
   belongs to `t.exponents` (`TauCeti.DynkinType.mem_exponents_of_coprime`). Instead of checking the
   nine families case by case, this is deduced conceptually from Galois conjugacy over `ℚ`
   (`IsPrimitiveRoot.exists_eq_of_isRoot_of_map_eq_prod`) applied to the integral characteristic
   polynomial of a Coxeter element on `t.simplyConnectedRootDatum` together with `1 ∈ t.exponents`.

## Main results

* `TauCeti.Coxeter.orderOf_wordProd_of_hasCartanType`: `orderOf (wordProd P b l) = t.coxeterNumber`.
* `TauCeti.Coxeter.roots_charpoly_of_hasCartanType_of_actsBy`: complex root multiset of `W.charpoly`
  is `t.exponents.map (fun e => exp (2πi e / t.coxeterNumber))`.
* `TauCeti.Coxeter.natCard_eq_card_support_mul_orderOf_wordProd_of_hasCartanType` and
  `TauCeti.Coxeter.sum_exponents_eq_ncard_posRoots_of_hasCartanType`: `|Φ| = r · orderOf c` and
  `∑ eᵢ = |Φ⁺|` for any reduced pairing of valid Cartan type `t`.
* `TauCeti.DynkinType.mem_exponents_of_coprime`: every residue `a < h` coprime to `h` lies in
  `t.exponents`.
* `TauCeti.Coxeter.orderOf_wordProd_eq_coxeterNumber`,
  `TauCeti.Coxeter.natCard_eq_card_support_mul_orderOf_wordProd`,
  `TauCeti.Coxeter.orderOf_wordProd_eq_natCard_div_card_support`,
  `TauCeti.Coxeter.roots_charpoly_eq_map_exponents_of_actsBy`, and
  `TauCeti.Coxeter.sum_exponents_eq_ncard_posRoots`: classification-free versions for any
  irreducible reduced crystallographic finite root system.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. V, §6.2, and Ch. VI, §1.11.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge University Press (1990),
  §§ 3.16–3.20.
-/

public section

open Matrix Polynomial RootPairing TauCeti

namespace TauCeti.Coxeter

section HasCartanType

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {P : RootPairing ι R M N} [P.IsCrystallographic]
  [IsDomain R] [CharZero R] {b : P.Base} {l : List b.support}

/-- **Every Coxeter element of a base of valid Cartan type `t` has order `t.coxeterNumber`.** -/
theorem orderOf_wordProd_of_hasCartanType [Finite ι] {t : DynkinType} (ht : t.Valid)
    (h : HasCartanType P b t) (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    orderOf (wordProd P b l) = t.coxeterNumber := by
  cases t with
  | A n =>
    rw [DynkinType.coxeterNumber_A]
    exact orderOf_wordProd_of_hasCartanType_A (DynkinType.valid_A.mp ht) h hnd hall
  | B n =>
    have hn : 2 ≤ n := DynkinType.valid_B.mp ht
    rw [DynkinType.coxeterNumber_B]
    exact orderOf_wordProd_of_hasCartanType_B (by omega) h hnd hall
  | C n =>
    have hn : 3 ≤ n := DynkinType.valid_C.mp ht
    rw [DynkinType.coxeterNumber_C]
    exact orderOf_wordProd_of_hasCartanType_C (by omega) h hnd hall
  | D n =>
    have hn : 4 ≤ n := DynkinType.valid_D.mp ht
    rw [DynkinType.coxeterNumber_D]
    exact orderOf_wordProd_of_hasCartanType_D (by omega) h hnd hall
  | E6 => rw [DynkinType.coxeterNumber_E6]; exact orderOf_wordProd_of_hasCartanType_E6 h hnd hall
  | E7 => rw [DynkinType.coxeterNumber_E7]; exact orderOf_wordProd_of_hasCartanType_E7 h hnd hall
  | E8 => rw [DynkinType.coxeterNumber_E8]; exact orderOf_wordProd_of_hasCartanType_E8 h hnd hall
  | F4 => rw [DynkinType.coxeterNumber_F4]; exact orderOf_wordProd_of_hasCartanType_F4 h hnd hall
  | G2 => rw [DynkinType.coxeterNumber_G2]; exact orderOf_wordProd_of_hasCartanType_G2 h hnd hall

private theorem nodup_map_exp_of_nodup {s : Multiset ℕ} {h : ℕ} (hh : h ≠ 0) (hnd : s.Nodup)
    (hlt : ∀ e ∈ s, e < h) :
    (s.map fun e : ℕ => Complex.exp (2 * Real.pi * Complex.I * (e / h))).Nodup := by
  refine hnd.map_on fun a ha b hb hab => ?_
  have hpow : ∀ k : ℕ, Complex.exp (2 * Real.pi * Complex.I * (k / h)) =
      Complex.exp (2 * Real.pi * Complex.I / h) ^ k := fun k => by
    rw [← Complex.exp_nat_mul]
    congr 1
    ring
  rw [hpow a, hpow b] at hab
  exact (Complex.isPrimitiveRoot_exp h hh).pow_inj (hlt a ha) (hlt b hb) hab

private theorem roots_eq_map_of_eigenvalues {r : Multiset ℂ} {L : List ℕ} {s : Multiset ℕ} {h : ℕ}
    (hh : h ≠ 0) (hr_nd : r.Nodup) (hs_nd : s.Nodup) (hs_lt : ∀ e ∈ s, e < h)
    (hLs : (L : Multiset ℕ) = s)
    (hmem : ∀ ζ : ℂ, ζ ∈ r ↔ ∃ e ∈ L, Complex.exp (2 * Real.pi * Complex.I * (e / h)) = ζ) :
    r = s.map fun e : ℕ => Complex.exp (2 * Real.pi * Complex.I * (e / h)) := by
  refine (hr_nd.ext (nodup_map_exp_of_nodup hh hs_nd hs_lt)).2 fun ζ => ?_
  rw [hmem, ← hLs, Multiset.mem_map]
  simp

/-- **Complex eigenvalue multiset of every Coxeter element of a base of valid Cartan type `t` on the
simple roots**: the roots of `W.charpoly` over `ℂ`, counted with multiplicity, are
`exp (2πi e / t.coxeterNumber)` as `e` ranges over `t.exponents`. -/
theorem roots_charpoly_of_hasCartanType_of_actsBy [DecidableEq ι] {t : DynkinType} (ht : t.Valid)
    (h : HasCartanType P b t) (hnd : l.Nodup) (hall : ∀ i, i ∈ l)
    {W : Matrix b.support b.support ℤ} (hW : b.ActsBy (wordProd P b l) W) :
    (W.map (Int.castRingHom ℂ)).charpoly.roots =
      t.exponents.map fun e : ℕ =>
        Complex.exp (2 * Real.pi * Complex.I * (e / t.coxeterNumber)) := by
  cases t with
  | A n =>
    simpa [DynkinType.exponents_A, DynkinType.coxeterNumber_A] using
      roots_charpoly_of_hasCartanType_A_of_actsBy h hnd hall hW
  | B n =>
    have hn : 2 ≤ n := DynkinType.valid_B.mp ht
    simpa [DynkinType.exponents_B, DynkinType.coxeterNumber_B] using
      roots_charpoly_of_hasCartanType_B_of_actsBy (by omega) h hnd hall hW
  | C n =>
    have hn : 3 ≤ n := DynkinType.valid_C.mp ht
    simpa [DynkinType.exponents_C, DynkinType.coxeterNumber_C] using
      roots_charpoly_of_hasCartanType_C_of_actsBy (by omega) h hnd hall hW
  | D n =>
    have hn : 4 ≤ n := DynkinType.valid_D.mp ht
    simpa [DynkinType.exponents_D, show n ≠ 0 by omega, DynkinType.coxeterNumber_D] using
      roots_charpoly_of_hasCartanType_D_of_actsBy (by omega) h hnd hall hW
  | E6 =>
    obtain ⟨hm, hnd_r⟩ := eigenvalues_of_hasCartanType_E6 h hnd hall hW
    simpa only [DynkinType.coxeterNumber_E6, Nat.cast_ofNat] using
      roots_eq_map_of_eigenvalues (L := e6Exponents) (h := 12) (by decide) hnd_r
        (by rw [DynkinType.exponents_E6]; decide)
        (fun e he => by
          simpa using DynkinType.lt_coxeterNumber_of_mem_exponents DynkinType.valid_E6 he)
        (by rw [DynkinType.exponents_E6]; decide) (by simpa using hm)
  | E7 =>
    obtain ⟨hm, hnd_r⟩ := eigenvalues_of_hasCartanType_E7 h hnd hall hW
    simpa only [DynkinType.coxeterNumber_E7, Nat.cast_ofNat] using
      roots_eq_map_of_eigenvalues (L := e7Exponents) (h := 18) (by decide) hnd_r
        (by rw [DynkinType.exponents_E7]; decide)
        (fun e he => by
          simpa using DynkinType.lt_coxeterNumber_of_mem_exponents DynkinType.valid_E7 he)
        (by rw [DynkinType.exponents_E7]; decide) (by simpa using hm)
  | E8 =>
    obtain ⟨hm, hnd_r⟩ := eigenvalues_of_hasCartanType_E8 h hnd hall hW
    simpa only [DynkinType.coxeterNumber_E8, Nat.cast_ofNat] using
      roots_eq_map_of_eigenvalues (L := e8Exponents) (h := 30) (by decide) hnd_r
        (by rw [DynkinType.exponents_E8]; decide)
        (fun e he => by
          simpa using DynkinType.lt_coxeterNumber_of_mem_exponents DynkinType.valid_E8 he)
        (by rw [DynkinType.exponents_E8]; decide) (by simpa using hm)
  | F4 =>
    obtain ⟨hm, hnd_r⟩ := eigenvalues_of_hasCartanType_F4 h hnd hall hW
    simpa only [DynkinType.coxeterNumber_F4, Nat.cast_ofNat] using
      roots_eq_map_of_eigenvalues (L := f4Exponents) (h := 12) (by decide) hnd_r
        (by rw [DynkinType.exponents_F4]; decide)
        (fun e he => by
          simpa using DynkinType.lt_coxeterNumber_of_mem_exponents DynkinType.valid_F4 he)
        (by rw [DynkinType.exponents_F4]; decide) (by simpa using hm)
  | G2 =>
    obtain ⟨hm, hnd_r⟩ := eigenvalues_of_hasCartanType_G2 h hnd hall hW
    simpa only [DynkinType.coxeterNumber_G2, Nat.cast_ofNat] using
      roots_eq_map_of_eigenvalues (L := g2Exponents) (h := 6) (by decide) hnd_r
        (by rw [DynkinType.exponents_G2]; decide)
        (fun e he => by
          simpa using DynkinType.lt_coxeterNumber_of_mem_exponents DynkinType.valid_G2 he)
        (by rw [DynkinType.exponents_G2]; decide) (by simpa using hm)

/-- **For any finite reduced crystallographic root pairing with a base of valid Cartan type `t`, the
number of roots equals the rank times the order of any Coxeter element**: `|Φ| = r · h`. -/
theorem natCard_eq_card_support_mul_orderOf_wordProd_of_hasCartanType [Finite ι] [P.IsReduced]
    {t : DynkinType} (ht : t.Valid) (h : HasCartanType P b t) (hnd : l.Nodup)
    (hall : ∀ i, i ∈ l) :
    Nat.card ι = b.support.card * orderOf (wordProd P b l) := by
  rw [h.natCard_eq_numRoots ht, h.card_support,
    orderOf_wordProd_of_hasCartanType ht h hnd hall,
    DynkinType.numRoots_eq_rank_mul_coxeterNumber]

/-- **For any finite reduced crystallographic root pairing with a base of valid Cartan type `t`, the
exponents of `t` sum to the number of positive roots**: `∑ eᵢ = |Φ⁺|`. -/
theorem sum_exponents_eq_ncard_posRoots_of_hasCartanType [Finite ι] [P.IsReduced]
    {t : DynkinType} (ht : t.Valid) (h : HasCartanType P b t) :
    t.exponents.sum = (posRoots P b).ncard := by
  have h1 := t.two_mul_sum_exponents_eq_numRoots
  have h2 := h.two_mul_ncard_posRoots ht
  omega

end HasCartanType

end TauCeti.Coxeter

namespace TauCeti.DynkinType

/-- **Every residue `a < h` coprime to the Coxeter number `h` is an exponent of `t`.**

Proved uniformly across all nine Dynkin types without case analysis: on the pinned integral root
datum `t.simplyConnectedRootDatum ht`, the action matrix `W` of a Coxeter element on the simple
roots has integer entries, so `W.charpoly` is defined over `ℚ`, splits into linear factors over `ℂ`
with roots `ζ ^ e` (`e ∈ t.exponents`), and has `ζ = ζ ^ 1` as a root since `1 ∈ t.exponents`. By
irreducibility of `Φ_h` over `ℚ` (`IsPrimitiveRoot.exists_eq_of_isRoot_of_map_eq_prod`), every
primitive `h`-th root `ζ ^ a` occurs among the roots `ζ ^ e`. -/
theorem mem_exponents_of_coprime {t : DynkinType} (ht : t.Valid) {a : ℕ}
    (ha : a < t.coxeterNumber) (hcop : a.Coprime t.coxeterNumber) : a ∈ t.exponents := by
  classical
  let b₀ := t.simplyConnectedBase ht
  let l₀ : List b₀.support := b₀.support.attach.toList
  have hnd : l₀.Nodup := b₀.support.attach.nodup_toList
  have hall : ∀ i, i ∈ l₀ := fun i => Finset.mem_toList.2 (Finset.mem_attach _ i)
  let W : Matrix b₀.support b₀.support ℤ := (l₀.map (reflMatrix b₀.cartanMatrix)).prod
  have hW : b₀.ActsBy (wordProd (t.simplyConnectedRootDatum ht) b₀ l₀) W :=
    b₀.actsBy_wordProd l₀
  have htype := t.hasCartanType_simplyConnectedRootDatum ht
  set h := t.coxeterNumber
  have hh0 : h ≠ 0 := (t.coxeterNumber_pos ht).ne'
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / h)
  have hζ : IsPrimitiveRoot ζ h := Complex.isPrimitiveRoot_exp h hh0
  have hpow : ∀ e : ℕ,
      Complex.exp (2 * Real.pi * Complex.I * (e / h)) = ζ ^ e := fun e => by
    rw [← Complex.exp_nat_mul]
    congr 1
    ring
  let p : ℚ[X] := W.charpoly.map (Int.castRingHom ℚ)
  let WC : Matrix b₀.support b₀.support ℂ := W.map (Int.castRingHom ℂ)
  have hpC : p.map (algebraMap ℚ ℂ) = WC.charpoly := by
    dsimp only [p, WC]
    rw [Polynomial.map_map,
      RingHom.ext_int ((algebraMap ℚ ℂ).comp (Int.castRingHom ℚ)) (Int.castRingHom ℂ),
      ← charpoly_map]
  have hroots : WC.charpoly.roots = t.exponents.map (ζ ^ ·) := by
    rw [Coxeter.roots_charpoly_of_hasCartanType_of_actsBy ht htype hnd hall hW]
    exact Multiset.map_congr rfl fun e _ => hpow e
  have hcard : WC.charpoly.roots.card = WC.charpoly.natDegree := by
    rw [hroots, Multiset.card_map, t.card_exponents, WC.charpoly_natDegree_eq_dim,
      Fintype.card_coe, htype.card_support]
  have hsplit : (WC.charpoly.roots.map fun r => X - Polynomial.C r).prod = WC.charpoly :=
    prod_multiset_X_sub_C_of_monic_of_roots_card_eq WC.charpoly_monic hcard
  let L : List ℕ := t.exponents.toList
  have hL : (L : Multiset ℕ) = t.exponents := Multiset.coe_toList _
  have hprod : p.map (algebraMap ℚ ℂ) = ∏ i : Fin L.length, (X - Polynomial.C (ζ ^ L[i])) := by
    rw [hpC, ← hsplit, hroots]
    conv_lhs => rw [← hL]
    rw [Multiset.map_map, Multiset.map_coe, Multiset.prod_coe, Fin.prod_univ_def]
    congr 1
    refine List.ext_getElem (by simp) fun k hk₁ hk₂ => ?_
    simp
  have hp_root : (p.map (algebraMap ℚ ℂ)).IsRoot ζ := by
    have hmem : ζ ∈ WC.charpoly.roots := by
      rw [hroots]
      exact Multiset.mem_map.2 ⟨1, t.one_mem_exponents ht, pow_one ζ⟩
    rw [hpC]
    exact isRoot_of_mem_roots hmem
  have hlt : ∀ i : Fin L.length, L[i] < h := fun i =>
    t.lt_coxeterNumber_of_mem_exponents ht (Multiset.mem_toList.1 (List.getElem_mem i.isLt))
  obtain ⟨i, hi⟩ := hζ.exists_eq_of_isRoot_of_map_eq_prod hζ hp_root hlt hprod ha hcop
  exact Multiset.mem_toList.1 (hi ▸ List.getElem_mem i.isLt)

end TauCeti.DynkinType

namespace TauCeti.Coxeter

section Classified

variable {ι R M N : Type*} [CommRing R] [IsDomain R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [P.IsRootSystem] [P.IsCrystallographic]
  [P.IsReduced] [P.IsIrreducible] {b : P.Base} {l : List b.support}

/-- **Every Coxeter element of an irreducible reduced crystallographic finite root system has order
equal to the Coxeter number of its classified Dynkin type.** -/
theorem orderOf_wordProd_eq_coxeterNumber (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    orderOf (wordProd P b l) = (classifiedDynkinType b).coxeterNumber :=
  orderOf_wordProd_of_hasCartanType (valid_classifiedDynkinType b)
    (hasCartanType_classifiedDynkinType b) hnd hall

/-- **For any irreducible reduced crystallographic finite root system, the number of roots equals
the rank times the order of any Coxeter element**: `|Φ| = r · h`. -/
theorem natCard_eq_card_support_mul_orderOf_wordProd (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    Nat.card ι = b.support.card * orderOf (wordProd P b l) :=
  natCard_eq_card_support_mul_orderOf_wordProd_of_hasCartanType (valid_classifiedDynkinType b)
    (hasCartanType_classifiedDynkinType b) hnd hall

/-- **The order of any Coxeter element of an irreducible reduced crystallographic finite root system
is `|Φ| / r`.** -/
theorem orderOf_wordProd_eq_natCard_div_card_support (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    orderOf (wordProd P b l) = Nat.card ι / b.support.card := by
  have hpos : 0 < b.support.card := by
    rw [← rank_classifiedDynkinType b]
    exact DynkinType.rank_pos (valid_classifiedDynkinType b)
  rw [natCard_eq_card_support_mul_orderOf_wordProd hnd hall, Nat.mul_div_right _ hpos]

/-- **Complex eigenvalue multiset of any Coxeter element of an irreducible reduced crystallographic
finite root system on the simple roots.** -/
theorem roots_charpoly_eq_map_exponents_of_actsBy [DecidableEq ι] (hnd : l.Nodup)
    (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ} (hW : b.ActsBy (wordProd P b l) W) :
    (W.map (Int.castRingHom ℂ)).charpoly.roots =
      (classifiedDynkinType b).exponents.map fun e : ℕ =>
        Complex.exp
          (2 * Real.pi * Complex.I * (e / (classifiedDynkinType b).coxeterNumber)) :=
  roots_charpoly_of_hasCartanType_of_actsBy (valid_classifiedDynkinType b)
    (hasCartanType_classifiedDynkinType b) hnd hall hW

/-- **The exponents of an irreducible reduced crystallographic finite root system sum to its number
of positive roots**: `∑ eᵢ = |Φ⁺|`. -/
theorem sum_exponents_eq_ncard_posRoots (b : P.Base) :
    (classifiedDynkinType b).exponents.sum = (posRoots P b).ncard :=
  sum_exponents_eq_ncard_posRoots_of_hasCartanType (valid_classifiedDynkinType b)
    (hasCartanType_classifiedDynkinType b)

end Classified

end TauCeti.Coxeter

end
