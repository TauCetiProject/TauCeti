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
import TauCeti.RingTheory.RootsOfUnity.Complex.Exp

/-!
# Uniform Coxeter-element and exponent theorems across all Dynkin types

Combining the classical families (`TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.Classical`) and
the exceptional families (`TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.Every`, `Eigen`) gives
uniform Coxeter-element and exponent theorems for any base of valid Cartan type `t`, and hence
classification-free theorems for any irreducible reduced crystallographic finite root system:

* **Order and root count**: `orderOf (wordProd P b l) = t.coxeterNumber` and `|Φ| = r · h`.
* **Eigenvalues and positive roots**: `(W.map _).charpoly.roots` is
  `t.exponents.map (fun e => exp (2πi e / t.coxeterNumber))`, and `t.exponents.sum = |Φ⁺|`.
* **Coprime residues are exponents** (`TauCeti.DynkinType.mem_exponents_of_coprime`): every
  `a < t.coxeterNumber` coprime to `t.coxeterNumber` belongs to `t.exponents`.

## Main results

* `TauCeti.Coxeter.orderOf_wordProd_of_hasCartanType` and
  `TauCeti.Coxeter.roots_charpoly_of_hasCartanType_of_actsBy`.
* `TauCeti.Coxeter.natCard_eq_card_support_mul_orderOf_wordProd_of_hasCartanType` and
  `TauCeti.Coxeter.sum_exponents_eq_ncard_posRoots_of_hasCartanType`.
* `TauCeti.DynkinType.mem_exponents_of_coprime`.
* `TauCeti.Coxeter.orderOf_wordProd_eq_coxeterNumber`,
  `TauCeti.Coxeter.natCard_eq_card_support_mul_orderOf_wordProd`,
  `TauCeti.Coxeter.orderOf_wordProd_eq_natCard_div_card_support`,
  `TauCeti.Coxeter.roots_charpoly_eq_map_exponents_of_actsBy`, and
  `TauCeti.Coxeter.sum_exponents_eq_ncard_posRoots`.

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
    simpa [DynkinType.coxeterNumber_A] using
      orderOf_wordProd_of_hasCartanType_A (DynkinType.valid_A.mp ht) h hnd hall
  | B n =>
    simpa [DynkinType.coxeterNumber_B] using
      orderOf_wordProd_of_hasCartanType_B (by have := DynkinType.valid_B.mp ht; omega) h hnd hall
  | C n =>
    simpa [DynkinType.coxeterNumber_C] using
      orderOf_wordProd_of_hasCartanType_C (by have := DynkinType.valid_C.mp ht; omega) h hnd hall
  | D n =>
    simpa [DynkinType.coxeterNumber_D] using
      orderOf_wordProd_of_hasCartanType_D (by have := DynkinType.valid_D.mp ht; omega) h hnd hall
  | E6 => simpa [DynkinType.coxeterNumber_E6] using orderOf_wordProd_of_hasCartanType_E6 h hnd hall
  | E7 => simpa [DynkinType.coxeterNumber_E7] using orderOf_wordProd_of_hasCartanType_E7 h hnd hall
  | E8 => simpa [DynkinType.coxeterNumber_E8] using orderOf_wordProd_of_hasCartanType_E8 h hnd hall
  | F4 => simpa [DynkinType.coxeterNumber_F4] using orderOf_wordProd_of_hasCartanType_F4 h hnd hall
  | G2 => simpa [DynkinType.coxeterNumber_G2] using orderOf_wordProd_of_hasCartanType_G2 h hnd hall

private theorem roots_eq_map_exponents {t : DynkinType} (ht : t.Valid) {r : Multiset ℂ}
    (h : (∀ ζ, ζ ∈ r ↔ ∃ e ∈ t.exponents,
      Complex.exp (2 * Real.pi * Complex.I * (e / t.coxeterNumber)) = ζ) ∧ r.Nodup)
    (hs_nd : t.exponents.Nodup := by simp) :
    r = t.exponents.map fun e : ℕ =>
      Complex.exp (2 * Real.pi * Complex.I * (e / t.coxeterNumber)) := by
  refine (h.2.ext (Complex.nodup_map_exp_two_pi_I_mul_div hs_nd fun e he =>
    t.lt_coxeterNumber_of_mem_exponents ht he)).2 fun ζ => ?_
  rw [h.1, Multiset.mem_map]

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
    simpa [DynkinType.exponents_B, DynkinType.coxeterNumber_B] using
      roots_charpoly_of_hasCartanType_B_of_actsBy
        (by have := DynkinType.valid_B.mp ht; omega) h hnd hall hW
  | C n =>
    simpa [DynkinType.exponents_C, DynkinType.coxeterNumber_C] using
      roots_charpoly_of_hasCartanType_C_of_actsBy
        (by have := DynkinType.valid_C.mp ht; omega) h hnd hall hW
  | D n =>
    have := DynkinType.valid_D.mp ht
    simpa [DynkinType.exponents_D, show n ≠ 0 by omega, DynkinType.coxeterNumber_D] using
      roots_charpoly_of_hasCartanType_D_of_actsBy (by omega) h hnd hall hW
  | E6 => exact roots_eq_map_exponents ht (eigenvalues_of_hasCartanType_E6 h hnd hall hW)
  | E7 => exact roots_eq_map_exponents ht (eigenvalues_of_hasCartanType_E7 h hnd hall hW)
  | E8 => exact roots_eq_map_exponents ht (eigenvalues_of_hasCartanType_E8 h hnd hall hW)
  | F4 => exact roots_eq_map_exponents ht (eigenvalues_of_hasCartanType_F4 h hnd hall hW)
  | G2 => exact roots_eq_map_exponents ht (eigenvalues_of_hasCartanType_G2 h hnd hall hW)

/-- **For any finite reduced crystallographic root pairing with a base of valid Cartan type `t`, the
number of roots equals the rank times the order of any Coxeter element**: `|Φ| = r · h`. -/
theorem natCard_eq_card_support_mul_orderOf_wordProd_of_hasCartanType [Finite ι] [P.IsReduced]
    {t : DynkinType} (ht : t.Valid) (h : HasCartanType P b t) (hnd : l.Nodup)
    (hall : ∀ i, i ∈ l) :
    Nat.card ι = b.support.card * orderOf (wordProd P b l) := by
  rw [h.natCard_eq_numRoots ht, h.card_support, orderOf_wordProd_of_hasCartanType ht h hnd hall,
    DynkinType.numRoots_eq_rank_mul_coxeterNumber]

/-- **For any finite reduced crystallographic root pairing with a base of valid Cartan type `t`, the
exponents of `t` sum to the number of positive roots**: `∑ eᵢ = |Φ⁺|`. -/
theorem sum_exponents_eq_ncard_posRoots_of_hasCartanType [Finite ι] [P.IsReduced]
    {t : DynkinType} (ht : t.Valid) (h : HasCartanType P b t) :
    t.exponents.sum = (posRoots P b).ncard := by
  have := t.two_mul_sum_exponents_eq_numRoots
  have := h.two_mul_ncard_posRoots_eq_numRoots ht
  omega

end HasCartanType

end TauCeti.Coxeter

namespace TauCeti.DynkinType

/-- **Every residue `a < t.coxeterNumber` coprime to `t.coxeterNumber` is an exponent of `t`.** -/
theorem mem_exponents_of_coprime {t : DynkinType} (ht : t.Valid) {a : ℕ}
    (ha : a < t.coxeterNumber) (hcop : a.Coprime t.coxeterNumber) : a ∈ t.exponents := by
  classical
  let b₀ := t.simplyConnectedBase ht
  let l₀ : List b₀.support := b₀.support.attach.toList
  let W : Matrix b₀.support b₀.support ℤ := (l₀.map (reflMatrix b₀.cartanMatrix)).prod
  have htype := t.hasCartanType_simplyConnectedRootDatum ht
  set h := t.coxeterNumber
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / h)
  have hζ : IsPrimitiveRoot ζ h := Complex.isPrimitiveRoot_exp h (t.coxeterNumber_pos ht).ne'
  let p : ℚ[X] := W.charpoly.map (Int.castRingHom ℚ)
  let WC : Matrix b₀.support b₀.support ℂ := W.map (Int.castRingHom ℂ)
  have hpC : p.map (algebraMap ℚ ℂ) = WC.charpoly := by
    dsimp only [p, WC]
    rw [Polynomial.map_map,
      RingHom.ext_int ((algebraMap ℚ ℂ).comp (Int.castRingHom ℚ)) (Int.castRingHom ℂ),
      ← charpoly_map]
  have hroots : WC.charpoly.roots = t.exponents.map (ζ ^ ·) := by
    rw [Coxeter.roots_charpoly_of_hasCartanType_of_actsBy ht htype b₀.support.attach.nodup_toList
      (fun i => Finset.mem_toList.2 (Finset.mem_attach _ i)) (b₀.actsBy_wordProd l₀)]
    exact Multiset.map_congr rfl fun e _ => Complex.exp_two_pi_I_mul_div e h
  have hsplit : (WC.charpoly.roots.map fun r => X - Polynomial.C r).prod = WC.charpoly :=
    prod_multiset_X_sub_C_of_monic_of_roots_card_eq WC.charpoly_monic <| by
      rw [hroots, Multiset.card_map, t.card_exponents, WC.charpoly_natDegree_eq_dim,
        Fintype.card_coe, htype.card_support]
  let L : List ℕ := t.exponents.toList
  have hprod : p.map (algebraMap ℚ ℂ) = ∏ i : Fin L.length, (X - Polynomial.C (ζ ^ L[i])) := by
    rw [hpC, ← hsplit, hroots]
    conv_lhs => rw [← Multiset.coe_toList t.exponents]
    rw [Multiset.map_map, Multiset.map_coe, Multiset.prod_coe, Fin.prod_univ_def]
    congr 1; exact List.ext_getElem (by simp [L]) fun _ _ _ => by simp [L]
  have hp_root : (p.map (algebraMap ℚ ℂ)).IsRoot ζ := by
    rw [hpC]
    exact isRoot_of_mem_roots (hroots ▸ Multiset.mem_map.2 ⟨1, t.one_mem_exponents ht, pow_one ζ⟩)
  obtain ⟨i, hi⟩ := hζ.exists_eq_of_isRoot_of_map_eq_prod hζ hp_root
    (fun i => t.lt_coxeterNumber_of_mem_exponents ht
      (Multiset.mem_toList.1 (List.getElem_mem i.isLt)))
    hprod ha hcop
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
  have hpos : 0 < b.support.card :=
    rank_classifiedDynkinType b ▸ DynkinType.rank_pos (valid_classifiedDynkinType b)
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
