/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.Eigen
import TauCeti.LinearAlgebra.Matrix.Cartan.Coxeter.Classical

/-!
# Coxeter elements, characteristic polynomials, and eigenvalues of classical bases

This file transports the matrix calculations of
`TauCeti.LinearAlgebra.Matrix.Cartan.Coxeter.Classical` to arbitrary Coxeter elements
`wordProd P b l` of bases of classical Cartan type (`Aₙ`, `Bₙ`, `Cₙ`, `Dₙ`), connects integer
simple-root matrices (`RootPairing.Base.ActsBy`) to the weight-space representation
`RootPairing.weylGroupRootRep` when the roots span, and computes the complex eigenvalue multisets —
retaining multiplicity — for all classical and exceptional types:

| type | rank condition | `h` | exponents `e` |
|---|---|---|---|
| `Aₙ` | `0 < n` (`charpoly`/eigenvalues all `n`) | `n + 1` | `1, 2, …, n` |
| `Bₙ` | `0 < n` | `2 * n` | `1, 3, …, 2n - 1` |
| `Cₙ` | `0 < n` | `2 * n` | `1, 3, …, 2n - 1` |
| `Dₙ` | `2 ≤ n` | `2 * (n - 1)` | `1, 3, …, 2n - 3, n - 1` |

Stating the eigenvalue theorems as equalities of `Multiset ℂ` rather than set membership is
essential in even type `D₂ₘ`, where the middle exponent `n - 1 = 2m - 1` occurs twice and `-1` is
an eigenvalue of multiplicity `2`.

## Main definitions

* `TauCeti.Coxeter.aExponents`, `bExponents`, `cExponents`, `dExponents`: the exponent lists of the
  four classical families.

## Main results

* `RootPairing.Base.ActsBy.toMatrix_weylGroupRootRep` and
  `RootPairing.Base.ActsBy.charpoly_weylGroupRootRep`: when `[P.IsRootSystem]`, an integer matrix by
  which `w` acts on the simple roots represents `P.weylGroupRootRep w` in `b.toWeightBasis` and
  determines its characteristic polynomial.
* `Polynomial.roots_sum_range_X_pow`, `Polynomial.roots_X_pow_add_one`, and
  `Polynomial.roots_X_pow_add_one_mul_X_add_one`: root multisets of `∑ k < n + 1, X ^ k`,
  `X ^ n + 1`, and `(X ^ (n - 1) + 1) * (X + 1)` over any integral domain with a primitive root of
  unity.
* `TauCeti.Coxeter.orderOf_wordProd_of_hasCartanType_A` (and `_B`, `_C`, `_D`) and
  `TauCeti.Coxeter.charpoly_of_hasCartanType_A_of_actsBy` (and `_B`, `_C`, `_D`): order and
  characteristic polynomial of every Coxeter element of a classical base.
* `TauCeti.Coxeter.roots_charpoly_of_hasCartanType_A_of_actsBy` (and `_B`, `_C`, `_D`, `_E6`, `_E7`,
  `_E8`, `_F4`, `_G2`) together with the weight-space versions for `P.weylGroupRootRep`: complex
  eigenvalue multisets `exp (2πi e / h)` with multiplicity.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. V, §6, and Plates I--IX.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge University Press (1990),
  §§ 3.16–3.20.
-/

public section

open Matrix Polynomial RootPairing TauCeti

/-! ### Simple-root matrices and the weight-space representation -/

namespace RootPairing.Base

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] {P : RootPairing ι R M N}

/-- When the roots span (`[P.IsRootSystem]`), an integer matrix `W` by which `w` acts on the simple
roots is the matrix of `P.weylGroupRootRep w` in the basis `b.toWeightBasis`. -/
theorem ActsBy.toMatrix_weylGroupRootRep [DecidableEq ι] [P.IsRootSystem] {b : P.Base}
    {w : P.weylGroup} {W : Matrix b.support b.support ℤ} (hW : b.ActsBy w W) :
    LinearMap.toMatrix b.toWeightBasis b.toWeightBasis (P.weylGroupRootRep w) =
      W.map (Int.castRingHom R) := by
  ext k j
  have hj : P.weylGroupRootRep w (b.toWeightBasis j) =
      ∑ l : b.support, (W l j : R) • b.toWeightBasis l := by
    rw [b.toWeightBasis_apply, weylGroupRootRep, Representation.ofDistribMulAction_apply_apply,
      actsBy_iff.mp hW j]
    exact Finset.sum_congr rfl fun l _ => by
      rw [b.toWeightBasis_apply, Int.cast_smul_eq_zsmul]
  rw [LinearMap.toMatrix_apply, hj, map_sum]
  simp [Finsupp.single_apply]

/-- When the roots span a finite free module (`[P.IsRootSystem] [Module.Free R M]
[Module.Finite R M]`), the characteristic polynomial of `P.weylGroupRootRep w` is the base-change of
`W.charpoly`. -/
theorem ActsBy.charpoly_weylGroupRootRep [P.IsRootSystem] [Module.Free R M] [Module.Finite R M]
    {b : P.Base} {w : P.weylGroup} {W : Matrix b.support b.support ℤ} [DecidableEq ι]
    (hW : b.ActsBy w W) :
    (P.weylGroupRootRep w).charpoly = W.charpoly.map (Int.castRingHom R) := by
  rw [← LinearMap.charpoly_toMatrix (P.weylGroupRootRep w) b.toWeightBasis,
    hW.toMatrix_weylGroupRootRep, Matrix.charpoly_map]

end RootPairing.Base

/-! ### Root multisets of the classical characteristic polynomials -/

namespace Polynomial

private theorem roots_eq_ofList_of_nodup {K : Type*} [CommRing K] [IsDomain K] {p : K[X]}
    (hp0 : p ≠ 0) {L : List K} (hnd : L.Nodup) (hmem : ∀ x ∈ L, p.IsRoot x)
    (hdeg : p.natDegree ≤ L.length) : p.roots = Multiset.ofList L := by
  classical
  symm
  refine Multiset.eq_of_le_of_card_le (Multiset.le_iff_count.mpr fun x => ?_) ?_
  · by_cases hx : x ∈ L
    · rw [Multiset.coe_count, List.count_eq_one_of_mem hnd hx]
      exact Multiset.one_le_count_iff_mem.mpr ((mem_roots hp0).mpr (hmem x hx))
    · simp [hx]
  · simpa using (card_roots' p).trans hdeg

/-- In an integral domain `K` with a primitive `(n + 1)`-th root of unity `ζ`, the root multiset of
`∑ k ∈ Finset.range (n + 1), X ^ k` consists of `ζ ^ 1, ζ ^ 2, …, ζ ^ n`, each with multiplicity
one. -/
theorem roots_sum_range_X_pow {K : Type*} [CommRing K] [IsDomain K] {ζ : K} {n : ℕ}
    (hζ : IsPrimitiveRoot ζ (n + 1)) :
    (∑ k ∈ Finset.range (n + 1), (X : K[X]) ^ k).roots =
      Multiset.ofList ((List.range n).map fun k => ζ ^ (k + 1)) := by
  set p : K[X] := ∑ k ∈ Finset.range (n + 1), X ^ k
  have hp0 : p ≠ 0 := by
    intro hp
    have hmul : p * (X - 1) = X ^ (n + 1) - 1 := geom_sum_mul (X : K[X]) (n + 1)
    rw [hp, zero_mul, sub_eq_add_neg, ← C_1, ← map_neg] at hmul
    exact X_pow_add_C_ne_zero (Nat.succ_pos n) (-1 : K) hmul.symm
  have hnd : ((List.range n).map fun k => ζ ^ (k + 1)).Nodup := by
    refine (List.nodup_map_iff_inj_on List.nodup_range).mpr fun a ha b hb hab => ?_
    rw [List.mem_range] at ha hb
    have := hζ.pow_inj (by omega : a + 1 < n + 1) (by omega : b + 1 < n + 1) hab
    omega
  refine roots_eq_ofList_of_nodup hp0 hnd (fun x hx => ?_) ?_
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
    rw [List.mem_range] at hk
    have hmul := congrArg (eval (ζ ^ (k + 1))) (geom_sum_mul (X : K[X]) (n + 1))
    rw [eval_mul, eval_sub, eval_X, eval_one, eval_sub, eval_pow, eval_X, eval_one, ← pow_mul,
      Nat.mul_comm, pow_mul, hζ.pow_eq_one, one_pow, sub_self] at hmul
    have hne1 : ζ ^ (k + 1) - 1 ≠ 0 := sub_ne_zero.mpr fun h1 => by
      have := hζ.pow_inj (by omega : k + 1 < n + 1) (Nat.succ_pos n) (h1.trans (pow_zero ζ).symm)
      omega
    exact (mul_eq_zero.mp hmul).resolve_right hne1
  · rw [List.length_map, List.length_range]
    exact natDegree_sum_le_of_forall_le (Finset.range (n + 1)) (fun k => (X : K[X]) ^ k)
      fun k hk => by
        rw [natDegree_X_pow]
        exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)

/-- In an integral domain `K` with a primitive `(2 * n)`-th root of unity `ζ` (`0 < n`), the root
multiset of `X ^ n + 1` consists of the odd powers `ζ ^ 1, ζ ^ 3, …, ζ ^ (2n - 1)`, each with
multiplicity one. -/
theorem roots_X_pow_add_one {K : Type*} [CommRing K] [IsDomain K] {ζ : K} {n : ℕ} (hn : 0 < n)
    (hζ : IsPrimitiveRoot ζ (2 * n)) :
    ((X : K[X]) ^ n + 1).roots =
      Multiset.ofList ((List.range n).map fun k => ζ ^ (2 * k + 1)) := by
  have hp0 : (X : K[X]) ^ n + 1 ≠ 0 := by simpa using X_pow_add_C_ne_zero hn (1 : K)
  have hneg : ζ ^ n = -1 :=
    (Nat.mul_div_left 2 hn ▸ hζ.pow_of_dvd hn.ne' (dvd_mul_left n 2)).eq_neg_one_of_two_right
  have hnd : ((List.range n).map fun k => ζ ^ (2 * k + 1)).Nodup := by
    refine (List.nodup_map_iff_inj_on List.nodup_range).mpr fun a ha b hb hab => ?_
    rw [List.mem_range] at ha hb
    have := hζ.pow_inj (by omega : 2 * a + 1 < 2 * n) (by omega : 2 * b + 1 < 2 * n) hab
    omega
  refine roots_eq_ofList_of_nodup hp0 hnd (fun x hx => ?_) ?_
  · obtain ⟨k, -, rfl⟩ := List.mem_map.mp hx
    rw [IsRoot.def, eval_add, eval_pow, eval_X, eval_one, ← pow_mul, Nat.mul_comm, pow_mul, hneg,
      (odd_two_mul_add_one k).neg_one_pow, neg_add_cancel]
  · simp

/-- In an integral domain `K` with a primitive `(2 * (n - 1))`-th root of unity `ζ` (`2 ≤ n`), the
root multiset of `(X ^ (n - 1) + 1) * (X + 1)` consists of `ζ ^ (2k + 1)` (`k < n - 1`) together
with `ζ ^ (n - 1) = -1` (so `-1` has multiplicity two when `n` is even). -/
theorem roots_X_pow_add_one_mul_X_add_one {K : Type*} [CommRing K] [IsDomain K] {ζ : K} {n : ℕ}
    (hn : 2 ≤ n) (hζ : IsPrimitiveRoot ζ (2 * (n - 1))) :
    (((X : K[X]) ^ (n - 1) + 1) * (X + 1)).roots =
      Multiset.ofList (((List.range (n - 1)).map (fun k => 2 * k + 1) ++ [n - 1]).map (ζ ^ ·)) := by
  have hm : 0 < n - 1 := by omega
  have hp1 : (X : K[X]) ^ (n - 1) + 1 ≠ 0 := by simpa using X_pow_add_C_ne_zero hm (1 : K)
  have hp2 : (X : K[X]) + 1 ≠ 0 := by simpa using X_pow_add_C_ne_zero zero_lt_one (1 : K)
  have hneg : ζ ^ (n - 1) = -1 :=
    (Nat.mul_div_left 2 hm ▸ hζ.pow_of_dvd hm.ne' (dvd_mul_left (n - 1) 2)).eq_neg_one_of_two_right
  have hx1 : (X + 1 : K[X]).roots = {ζ ^ (n - 1)} := by
    rw [← C_1, roots_X_add_C, hneg]
  rw [roots_mul (mul_ne_zero hp1 hp2), roots_X_pow_add_one hm hζ, hx1, List.map_append,
    List.map_map, List.map_singleton]
  rfl

end Polynomial

namespace TauCeti.Coxeter

/-! ### Exponent lists of the classical families -/

/-- The exponents `1, 2, …, n` of type `Aₙ`. -/
@[expose] def aExponents (n : ℕ) : List ℕ := (List.range n).map (· + 1)

/-- The exponents `1, 3, …, 2n - 1` of type `Bₙ`. -/
@[expose] def bExponents (n : ℕ) : List ℕ := (List.range n).map fun k => 2 * k + 1

/-- The exponents `1, 3, …, 2n - 1` of type `Cₙ`. -/
@[expose] def cExponents (n : ℕ) : List ℕ := bExponents n

/-- The exponents `1, 3, …, 2n - 3, n - 1` of type `Dₙ` (empty for `n = 0`). -/
@[expose] def dExponents (n : ℕ) : List ℕ :=
  if n = 0 then [] else (List.range (n - 1)).map (fun k => 2 * k + 1) ++ [n - 1]

/-- Type `Aₙ` has `n` exponents. -/
@[simp] theorem length_aExponents (n : ℕ) : (aExponents n).length = n := by simp [aExponents]

/-- Type `Bₙ` has `n` exponents. -/
@[simp] theorem length_bExponents (n : ℕ) : (bExponents n).length = n := by simp [bExponents]

/-- Type `Cₙ` has `n` exponents. -/
@[simp] theorem length_cExponents (n : ℕ) : (cExponents n).length = n := by simp [cExponents]

/-- Type `Dₙ` has `n` exponents (counted with multiplicity). -/
@[simp] theorem length_dExponents (n : ℕ) : (dExponents n).length = n := by
  rcases n with _ | m <;> simp [dExponents]

/-! ### Orders and characteristic polynomials of classical Coxeter elements -/

section ClassicalOrdersAndCharpoly

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] {P : RootPairing ι R M N} [P.IsCrystallographic] [IsDomain R] [CharZero R]
  {b : P.Base} {l : List b.support}

/-- **Every Coxeter element of a base of type `Aₙ` (`0 < n`) has order `n + 1`.** -/
theorem orderOf_wordProd_of_hasCartanType_A [Finite ι] {n : ℕ} (hn : 0 < n)
    (h : HasCartanType P b (.A n)) (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    orderOf (wordProd P b l) = n + 1 :=
  (orderOf_wordProd_of_isOneDegenerateOrder_of_hasCartanType (t := .A n)
    (DynkinType.cartanMatrix_A n) (isOneDegenerateOrder_A n) (List.Perm.refl _) h hnd hall).trans
    (orderOf_coxA hn)

/-- **Every Coxeter element of a base of type `Bₙ` (`0 < n`) has order `2 * n`.** -/
theorem orderOf_wordProd_of_hasCartanType_B [Finite ι] {n : ℕ} (hn : 0 < n)
    (h : HasCartanType P b (.B n)) (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    orderOf (wordProd P b l) = 2 * n :=
  (orderOf_wordProd_of_isOneDegenerateOrder_of_hasCartanType (t := .B n)
    (DynkinType.cartanMatrix_B n) (isOneDegenerateOrder_B n) (List.Perm.refl _) h hnd hall).trans
    (orderOf_coxB hn)

/-- **Every Coxeter element of a base of type `Cₙ` (`0 < n`) has order `2 * n`.** -/
theorem orderOf_wordProd_of_hasCartanType_C [Finite ι] {n : ℕ} (hn : 0 < n)
    (h : HasCartanType P b (.C n)) (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    orderOf (wordProd P b l) = 2 * n :=
  (orderOf_wordProd_of_isOneDegenerateOrder_of_hasCartanType (t := .C n)
    (DynkinType.cartanMatrix_C n) (isOneDegenerateOrder_C n) (List.Perm.refl _) h hnd hall).trans
    (orderOf_coxC hn)

/-- **Every Coxeter element of a base of type `Dₙ` (`2 ≤ n`) has order `2 * (n - 1)`.** -/
theorem orderOf_wordProd_of_hasCartanType_D [Finite ι] {n : ℕ} (hn : 2 ≤ n)
    (h : HasCartanType P b (.D n)) (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    orderOf (wordProd P b l) = 2 * (n - 1) :=
  (orderOf_wordProd_of_isOneDegenerateOrder_of_hasCartanType (t := .D n)
    (DynkinType.cartanMatrix_D n) (isOneDegenerateOrder_D n) (List.Perm.refl _) h hnd hall).trans
    (orderOf_coxD hn)

/-- **Every Coxeter element of a base of type `Aₙ`** has characteristic polynomial
`∑ k ∈ Finset.range (n + 1), X ^ k` on the simple roots. -/
theorem charpoly_of_hasCartanType_A_of_actsBy [DecidableEq ι] {n : ℕ}
    (h : HasCartanType P b (.A n)) (hnd : l.Nodup) (hall : ∀ i, i ∈ l)
    {W : Matrix b.support b.support ℤ} (hW : b.ActsBy (wordProd P b l) W) :
    W.charpoly = ∑ k ∈ Finset.range (n + 1), X ^ k :=
  (charpoly_of_isOneDegenerateOrder_of_hasCartanType_of_actsBy (t := .A n)
    (DynkinType.cartanMatrix_A n) (isOneDegenerateOrder_A n) (List.Perm.refl _) h hnd hall
    hW).trans (charpoly_coxA n)

/-- **Every Coxeter element of a base of type `Bₙ` (`0 < n`)** has characteristic polynomial
`X ^ n + 1` on the simple roots. -/
theorem charpoly_of_hasCartanType_B_of_actsBy [DecidableEq ι] {n : ℕ} (hn : 0 < n)
    (h : HasCartanType P b (.B n)) (hnd : l.Nodup) (hall : ∀ i, i ∈ l)
    {W : Matrix b.support b.support ℤ} (hW : b.ActsBy (wordProd P b l) W) :
    W.charpoly = X ^ n + 1 :=
  (charpoly_of_isOneDegenerateOrder_of_hasCartanType_of_actsBy (t := .B n)
    (DynkinType.cartanMatrix_B n) (isOneDegenerateOrder_B n) (List.Perm.refl _) h hnd hall
    hW).trans (charpoly_coxB hn)

/-- **Every Coxeter element of a base of type `Cₙ` (`0 < n`)** has characteristic polynomial
`X ^ n + 1` on the simple roots. -/
theorem charpoly_of_hasCartanType_C_of_actsBy [DecidableEq ι] {n : ℕ} (hn : 0 < n)
    (h : HasCartanType P b (.C n)) (hnd : l.Nodup) (hall : ∀ i, i ∈ l)
    {W : Matrix b.support b.support ℤ} (hW : b.ActsBy (wordProd P b l) W) :
    W.charpoly = X ^ n + 1 :=
  (charpoly_of_isOneDegenerateOrder_of_hasCartanType_of_actsBy (t := .C n)
    (DynkinType.cartanMatrix_C n) (isOneDegenerateOrder_C n) (List.Perm.refl _) h hnd hall
    hW).trans (charpoly_coxC hn)

/-- **Every Coxeter element of a base of type `Dₙ` (`2 ≤ n`)** has characteristic polynomial
`(X ^ (n - 1) + 1) * (X + 1)` on the simple roots. -/
theorem charpoly_of_hasCartanType_D_of_actsBy [DecidableEq ι] {n : ℕ} (hn : 2 ≤ n)
    (h : HasCartanType P b (.D n)) (hnd : l.Nodup) (hall : ∀ i, i ∈ l)
    {W : Matrix b.support b.support ℤ} (hW : b.ActsBy (wordProd P b l) W) :
    W.charpoly = (X ^ (n - 1) + 1) * (X + 1) :=
  (charpoly_of_isOneDegenerateOrder_of_hasCartanType_of_actsBy (t := .D n)
    (DynkinType.cartanMatrix_D n) (isOneDegenerateOrder_D n) (List.Perm.refl _) h hnd hall
    hW).trans (charpoly_coxD hn)

end ClassicalOrdersAndCharpoly

/-! ### Complex eigenvalue multisets on simple roots and on the weight space -/

private theorem exp_two_pi_I_div_pow (d : ℂ) (e : ℕ) :
    (Complex.exp (2 * Real.pi * Complex.I / d)) ^ e =
      Complex.exp (2 * Real.pi * Complex.I * ((e : ℂ) / d)) := by
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

private theorem nodup_map_exp_of_lt {h : ℕ} (hh : 0 < h) {exps : List ℕ} (hnd : exps.Nodup)
    (hlt : ∀ e ∈ exps, e < h) :
    (exps.map fun e : ℕ => Complex.exp (2 * Real.pi * Complex.I * ((e : ℂ) / (h : ℂ)))).Nodup := by
  have hζ := Complex.isPrimitiveRoot_exp h hh.ne'
  refine (List.nodup_map_iff_inj_on hnd).mpr fun a ha b hb hab => ?_
  rw [← exp_two_pi_I_div_pow, ← exp_two_pi_I_div_pow] at hab
  exact hζ.pow_inj (hlt a ha) (hlt b hb) hab

private theorem multiset_eq_ofList_of_nodup {s : Multiset ℂ} {h : ℕ} (hh : 0 < h) {exps : List ℕ}
    (hnd_exps : exps.Nodup) (hlt : ∀ e ∈ exps, e < h) (hnd_s : s.Nodup)
    (hiff : ∀ ζ : ℂ, ζ ∈ s ↔
      ∃ e ∈ exps, Complex.exp (2 * Real.pi * Complex.I * ((e : ℂ) / (h : ℂ))) = ζ) :
    s = Multiset.ofList
      (exps.map fun e : ℕ => Complex.exp (2 * Real.pi * Complex.I * ((e : ℂ) / (h : ℂ)))) := by
  refine (Multiset.Nodup.ext hnd_s ?_).mpr fun ζ => ?_
  · simpa using nodup_map_exp_of_lt hh hnd_exps hlt
  · rw [hiff, Multiset.mem_coe, List.mem_map]

section EigenvalueMultisets

variable {ι R M N : Type*} [DecidableEq ι] [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {P : RootPairing ι R M N} [P.IsCrystallographic] [IsDomain R]
  [CharZero R] {b : P.Base} {l : List b.support}

/-- **Complex eigenvalue multiset of a Coxeter element of type `Aₙ` on the simple roots**:
`exp (2πi e / (n + 1))` for `e ∈ aExponents n = [1, 2, …, n]`. -/
theorem roots_charpoly_of_hasCartanType_A_of_actsBy {n : ℕ} (h : HasCartanType P b (.A n))
    (hnd : l.Nodup) (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ}
    (hW : b.ActsBy (wordProd P b l) W) :
    (W.map (Int.castRingHom ℂ)).charpoly.roots =
      Multiset.ofList (aExponents n |>.map fun e : ℕ =>
        Complex.exp (2 * Real.pi * Complex.I * (e / (n + 1 : ℂ)))) := by
  have hmap :
      (W.map (Int.castRingHom ℂ)).charpoly = ∑ k ∈ Finset.range (n + 1), (X : ℂ[X]) ^ k := by
    rw [Matrix.charpoly_map, charpoly_of_hasCartanType_A_of_actsBy h hnd hall hW,
      Polynomial.map_sum]; simp
  rw [hmap, roots_sum_range_X_pow (Complex.isPrimitiveRoot_exp (n + 1) (Nat.succ_ne_zero n))]
  simp [aExponents, List.map_map, Function.comp_def, exp_two_pi_I_div_pow]

/-- **Complex eigenvalue multiset of a Coxeter element of type `Bₙ` (`0 < n`) on the simple
roots**: `exp (2πi e / (2n))` for `e ∈ bExponents n = [1, 3, …, 2n - 1]`. -/
theorem roots_charpoly_of_hasCartanType_B_of_actsBy {n : ℕ} (hn : 0 < n)
    (h : HasCartanType P b (.B n)) (hnd : l.Nodup) (hall : ∀ i, i ∈ l)
    {W : Matrix b.support b.support ℤ} (hW : b.ActsBy (wordProd P b l) W) :
    (W.map (Int.castRingHom ℂ)).charpoly.roots =
      Multiset.ofList (bExponents n |>.map fun e : ℕ =>
        Complex.exp (2 * Real.pi * Complex.I * (e / (2 * n : ℂ)))) := by
  have hmap : (W.map (Int.castRingHom ℂ)).charpoly = (X : ℂ[X]) ^ n + 1 := by
    rw [Matrix.charpoly_map, charpoly_of_hasCartanType_B_of_actsBy hn h hnd hall hW]; simp
  rw [hmap, roots_X_pow_add_one hn (Complex.isPrimitiveRoot_exp (2 * n) (by omega))]
  simp [bExponents, List.map_map, Function.comp_def, exp_two_pi_I_div_pow]

/-- **Complex eigenvalue multiset of a Coxeter element of type `Cₙ` (`0 < n`) on the simple
roots**: `exp (2πi e / (2n))` for `e ∈ cExponents n = [1, 3, …, 2n - 1]`. -/
theorem roots_charpoly_of_hasCartanType_C_of_actsBy {n : ℕ} (hn : 0 < n)
    (h : HasCartanType P b (.C n)) (hnd : l.Nodup) (hall : ∀ i, i ∈ l)
    {W : Matrix b.support b.support ℤ} (hW : b.ActsBy (wordProd P b l) W) :
    (W.map (Int.castRingHom ℂ)).charpoly.roots =
      Multiset.ofList (cExponents n |>.map fun e : ℕ =>
        Complex.exp (2 * Real.pi * Complex.I * (e / (2 * n : ℂ)))) := by
  have hmap : (W.map (Int.castRingHom ℂ)).charpoly = (X : ℂ[X]) ^ n + 1 := by
    rw [Matrix.charpoly_map, charpoly_of_hasCartanType_C_of_actsBy hn h hnd hall hW]; simp
  rw [hmap, roots_X_pow_add_one hn (Complex.isPrimitiveRoot_exp (2 * n) (by omega))]
  simp [cExponents, bExponents, List.map_map, Function.comp_def, exp_two_pi_I_div_pow]

/-- **Complex eigenvalue multiset of a Coxeter element of type `Dₙ` (`2 ≤ n`) on the simple
roots**: `exp (2πi e / (2(n - 1)))` for `e ∈ dExponents n = [1, 3, …, 2n - 3, n - 1]`, retaining
the double eigenvalue `-1` when `n` is even. -/
theorem roots_charpoly_of_hasCartanType_D_of_actsBy {n : ℕ} (hn : 2 ≤ n)
    (h : HasCartanType P b (.D n)) (hnd : l.Nodup) (hall : ∀ i, i ∈ l)
    {W : Matrix b.support b.support ℤ} (hW : b.ActsBy (wordProd P b l) W) :
    (W.map (Int.castRingHom ℂ)).charpoly.roots =
      Multiset.ofList (dExponents n |>.map fun e : ℕ =>
        Complex.exp (2 * Real.pi * Complex.I * (e / (2 * (n - 1 : ℂ))))) := by
  have hmap : (W.map (Int.castRingHom ℂ)).charpoly = ((X : ℂ[X]) ^ (n - 1) + 1) * (X + 1) := by
    rw [Matrix.charpoly_map, charpoly_of_hasCartanType_D_of_actsBy hn h hnd hall hW]; simp
  rw [hmap, roots_X_pow_add_one_mul_X_add_one hn
    (Complex.isPrimitiveRoot_exp (2 * (n - 1)) (by omega))]
  simp [dExponents, show n ≠ 0 by omega, List.map_map, Function.comp_def, exp_two_pi_I_div_pow,
    Nat.cast_sub (by omega : 1 ≤ n)]

/-- **Complex eigenvalue multiset of a Coxeter element of type `E₆` on the simple roots.** -/
theorem roots_charpoly_of_hasCartanType_E6_of_actsBy (h : HasCartanType P b .E6)
    (hnd : l.Nodup) (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ}
    (hW : b.ActsBy (wordProd P b l) W) :
    (W.map (Int.castRingHom ℂ)).charpoly.roots =
      Multiset.ofList (e6Exponents.map fun e : ℕ =>
        Complex.exp (2 * Real.pi * Complex.I * (e / 12))) := by
  obtain ⟨hmem, hnd_r⟩ := eigenvalues_of_hasCartanType_E6 h hnd hall hW
  simpa using multiset_eq_ofList_of_nodup (h := 12) (by norm_num) (by decide) (by decide) hnd_r
    fun ζ => by rw [hmem]; norm_num

/-- **Complex eigenvalue multiset of a Coxeter element of type `E₇` on the simple roots.** -/
theorem roots_charpoly_of_hasCartanType_E7_of_actsBy (h : HasCartanType P b .E7)
    (hnd : l.Nodup) (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ}
    (hW : b.ActsBy (wordProd P b l) W) :
    (W.map (Int.castRingHom ℂ)).charpoly.roots =
      Multiset.ofList (e7Exponents.map fun e : ℕ =>
        Complex.exp (2 * Real.pi * Complex.I * (e / 18))) := by
  obtain ⟨hmem, hnd_r⟩ := eigenvalues_of_hasCartanType_E7 h hnd hall hW
  simpa using multiset_eq_ofList_of_nodup (h := 18) (by norm_num) (by decide) (by decide) hnd_r
    fun ζ => by rw [hmem]; norm_num

/-- **Complex eigenvalue multiset of a Coxeter element of type `E₈` on the simple roots.** -/
theorem roots_charpoly_of_hasCartanType_E8_of_actsBy (h : HasCartanType P b .E8)
    (hnd : l.Nodup) (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ}
    (hW : b.ActsBy (wordProd P b l) W) :
    (W.map (Int.castRingHom ℂ)).charpoly.roots =
      Multiset.ofList (e8Exponents.map fun e : ℕ =>
        Complex.exp (2 * Real.pi * Complex.I * (e / 30))) := by
  obtain ⟨hmem, hnd_r⟩ := eigenvalues_of_hasCartanType_E8 h hnd hall hW
  simpa using multiset_eq_ofList_of_nodup (h := 30) (by norm_num) (by decide) (by decide) hnd_r
    fun ζ => by rw [hmem]; norm_num

/-- **Complex eigenvalue multiset of a Coxeter element of type `F₄` on the simple roots.** -/
theorem roots_charpoly_of_hasCartanType_F4_of_actsBy (h : HasCartanType P b .F4)
    (hnd : l.Nodup) (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ}
    (hW : b.ActsBy (wordProd P b l) W) :
    (W.map (Int.castRingHom ℂ)).charpoly.roots =
      Multiset.ofList (f4Exponents.map fun e : ℕ =>
        Complex.exp (2 * Real.pi * Complex.I * (e / 12))) := by
  obtain ⟨hmem, hnd_r⟩ := eigenvalues_of_hasCartanType_F4 h hnd hall hW
  simpa using multiset_eq_ofList_of_nodup (h := 12) (by norm_num) (by decide) (by decide) hnd_r
    fun ζ => by rw [hmem]; norm_num

/-- **Complex eigenvalue multiset of a Coxeter element of type `G₂` on the simple roots.** -/
theorem roots_charpoly_of_hasCartanType_G2_of_actsBy (h : HasCartanType P b .G2)
    (hnd : l.Nodup) (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ}
    (hW : b.ActsBy (wordProd P b l) W) :
    (W.map (Int.castRingHom ℂ)).charpoly.roots =
      Multiset.ofList (g2Exponents.map fun e : ℕ =>
        Complex.exp (2 * Real.pi * Complex.I * (e / 6))) := by
  obtain ⟨hmem, hnd_r⟩ := eigenvalues_of_hasCartanType_G2 h hnd hall hW
  simpa using multiset_eq_ofList_of_nodup (h := 6) (by norm_num) (by decide) (by decide) hnd_r
    fun ζ => by rw [hmem]; norm_num

end EigenvalueMultisets

section WeightSpaceEigenvalues

variable {ι M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
  {P : RootPairing ι ℂ M N} [P.IsRootSystem] [P.IsCrystallographic] [Module.Finite ℂ M]
  {b : P.Base} {l : List b.support}

/-- **Weight-space eigenvalue multiset of a Coxeter element of type `Aₙ`
(`P.weylGroupRootRep`).** -/
theorem roots_charpoly_weylGroupRootRep_wordProd_of_hasCartanType_A {n : ℕ}
    (h : HasCartanType P b (.A n)) (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    (P.weylGroupRootRep (wordProd P b l)).charpoly.roots =
      Multiset.ofList (aExponents n |>.map fun e : ℕ =>
        Complex.exp (2 * Real.pi * Complex.I * (e / (n + 1 : ℂ)))) := by
  classical
  rw [(b.actsBy_wordProd l).charpoly_weylGroupRootRep, ← Matrix.charpoly_map]
  exact roots_charpoly_of_hasCartanType_A_of_actsBy h hnd hall (b.actsBy_wordProd l)

/-- **Weight-space eigenvalue multiset of a Coxeter element of type `Bₙ` (`0 < n`).** -/
theorem roots_charpoly_weylGroupRootRep_wordProd_of_hasCartanType_B {n : ℕ} (hn : 0 < n)
    (h : HasCartanType P b (.B n)) (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    (P.weylGroupRootRep (wordProd P b l)).charpoly.roots =
      Multiset.ofList (bExponents n |>.map fun e : ℕ =>
        Complex.exp (2 * Real.pi * Complex.I * (e / (2 * n : ℂ)))) := by
  classical
  rw [(b.actsBy_wordProd l).charpoly_weylGroupRootRep, ← Matrix.charpoly_map]
  exact roots_charpoly_of_hasCartanType_B_of_actsBy hn h hnd hall (b.actsBy_wordProd l)

/-- **Weight-space eigenvalue multiset of a Coxeter element of type `Cₙ` (`0 < n`).** -/
theorem roots_charpoly_weylGroupRootRep_wordProd_of_hasCartanType_C {n : ℕ} (hn : 0 < n)
    (h : HasCartanType P b (.C n)) (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    (P.weylGroupRootRep (wordProd P b l)).charpoly.roots =
      Multiset.ofList (cExponents n |>.map fun e : ℕ =>
        Complex.exp (2 * Real.pi * Complex.I * (e / (2 * n : ℂ)))) := by
  classical
  rw [(b.actsBy_wordProd l).charpoly_weylGroupRootRep, ← Matrix.charpoly_map]
  exact roots_charpoly_of_hasCartanType_C_of_actsBy hn h hnd hall (b.actsBy_wordProd l)

/-- **Weight-space eigenvalue multiset of a Coxeter element of type `Dₙ` (`2 ≤ n`), including
reducible `D₂ = A₁ × A₁`.** -/
theorem roots_charpoly_weylGroupRootRep_wordProd_of_hasCartanType_D {n : ℕ} (hn : 2 ≤ n)
    (h : HasCartanType P b (.D n)) (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    (P.weylGroupRootRep (wordProd P b l)).charpoly.roots =
      Multiset.ofList (dExponents n |>.map fun e : ℕ =>
        Complex.exp (2 * Real.pi * Complex.I * (e / (2 * (n - 1 : ℂ))))) := by
  classical
  rw [(b.actsBy_wordProd l).charpoly_weylGroupRootRep, ← Matrix.charpoly_map]
  exact roots_charpoly_of_hasCartanType_D_of_actsBy hn h hnd hall (b.actsBy_wordProd l)

end WeightSpaceEigenvalues

end TauCeti.Coxeter

end
