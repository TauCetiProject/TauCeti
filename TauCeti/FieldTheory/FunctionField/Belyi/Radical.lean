/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Belyi.Basic
public import TauCeti.FieldTheory.FunctionField.Place.RatFunc.XPowSubCX
import TauCeti.FieldTheory.FunctionField.Different.Radical
import TauCeti.FieldTheory.FunctionField.Radical.Genus
import TauCeti.FieldTheory.Kummer.Extension
import TauCeti.FieldTheory.RatFunc.Transcendental

/-!
# Radical algebraic Belyi pairs

Let `F = k(t)(y)` with `y ^ n = u` for a nonzero `u ∈ k(t)`, over a field `k` of characteristic
zero. The ramification of a place of `k(t)` in `F` is governed by the order of `u` there: every
place above `P` has ramification index `n / gcd(n, ord_P u)` (Stichtenoth, Proposition 3.7.3;
this is `TauCeti.Place.ramificationIdx_eq_of_pow_eq`). So `F` is unramified outside `0`, `1` and
`∞` as soon as `n` divides `ord_P u` at every other place `P`, and `F` is then an algebraic Belyi
pair provided its constant field is still `k` (`TauCeti.IsAlgebraicBelyiPair.of_pow_eq`). A place
with `gcd(n, ord_P u) = 1` is totally ramified and keeps the constant field equal to `k`
(Stichtenoth, Corollary 3.7.4), which gives
`TauCeti.IsAlgebraicBelyiPair.of_pow_eq_of_gcd_ord_eq_one`.

The natural radicands are the functions `u = c t ^ a (t - 1) ^ b` with `c ∈ k` nonzero and
`a, b ∈ ℤ`, which are units away from the three marked places; their orders at `0`, `1` and `∞`
are `a`, `b` and `-(a + b)` (`TauCeti.Place.ord_algebraMap_mul_X_zpow_mul_X_sub_one_zpow` and its
specializations). For these, `y ^ n = u` is a Belyi pair of degree `n` as soon as `n`
is coprime to one of `a`, `b` and `a + b`
(`TauCeti.IsAlgebraicBelyiPair.of_pow_eq_X_zpow_mul_X_sub_one_zpow`), and the formula above gives
ramification index `n / gcd(n, a)` over `0`, `n / gcd(n, b)` over `1` and `n / gcd(n, a + b)` over
`∞`. The family contains:

* the **power map** `t ↦ u ^ n`, with `y ^ n = t`. Its model `k(t)[Y] / (Y ^ n - t)` has degree
  `n` (`TauCeti.finrank_adjoinRoot_X_pow_sub_C_X`) and is a Belyi pair
  (`TauCeti.isAlgebraicBelyiPair_adjoinRoot_X_pow_sub_C_X`). Whenever `n` is invertible in `k`,
  it is totally ramified over `0` and `∞` (`TauCeti.isTotallyRamified_adjoinRoot_X_pow_sub_C_X`)
  and unramified elsewhere, in particular over `1`
  (`TauCeti.ramificationIdx_adjoinRoot_X_pow_sub_C_X_eq_one`);
* the quadratic map `4s(1 - s)`, for which `y = 1 - 2s` satisfies `y ^ 2 = 1 - t`, so that
  `n = 2`, `c = -1`, `a = 0` and `b = 1`;
* the superelliptic curve `y ^ 4 = t (t - 1)`, with `n = 4` and `a = b = 1`.

## Main results

* `TauCeti.Place.ord_algebraMap_mul_X_zpow_mul_X_sub_one_zpow_of_notMem_zeroOneInfty`: the
  radicand `c t ^ a (t - 1) ^ b` is a unit away from `0`, `1` and `∞`.
* `TauCeti.IsAlgebraicBelyiPair.of_pow_eq` and
  `TauCeti.IsAlgebraicBelyiPair.of_pow_eq_of_gcd_ord_eq_one`: radical extensions unramified outside
  `0`, `1` and `∞` are algebraic Belyi pairs.
* `TauCeti.IsAlgebraicBelyiPair.of_pow_eq_X_zpow_mul_X_sub_one_zpow` and
  `TauCeti.finrank_eq_of_pow_eq_X_zpow_mul_X_sub_one_zpow`: the Belyi pair
  `y ^ n = c t ^ a (t - 1) ^ b` and its degree `n`.
* `TauCeti.isAlgebraicBelyiPair_adjoinRoot_X_pow_sub_C_X`: the power map is a Belyi pair.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Proposition 3.7.3 and Corollary 3.7.4.
-/

public section

open Polynomial

open scoped IntermediateField

namespace TauCeti

namespace Place

variable {k : Type*} [Field k]

/-- Away from `0`, `1` and `∞`, the function `c t ^ a (t - 1) ^ b` is a unit. -/
theorem ord_algebraMap_mul_X_zpow_mul_X_sub_one_zpow_of_notMem_zeroOneInfty
    {P : Place k (RatFunc k)} (hP : P ∉ zeroOneInfty k) {c : k} (hc : c ≠ 0) (a b : ℤ) :
    P.ord (algebraMap k (RatFunc k) c * RatFunc.X ^ a * (RatFunc.X - 1) ^ b) = 0 := by
  simp only [mem_zeroOneInfty_iff, not_or] at hP
  have h1 := ord_X_sub_C_eq_zero_of_ne (1 : k) hP.2.1 hP.2.2
  rw [map_one RatFunc.C] at h1
  rw [ord_algebraMap_mul_X_zpow_mul_X_sub_one_zpow _ hc, ord_X_eq_zero_of_ne hP.1 hP.2.2, h1,
    mul_zero, mul_zero, add_zero]

end Place

section Degree

variable {k F : Type*} [Field k] [Field F] [Algebra (RatFunc k) F]

/-- If `n` is coprime to one of `a`, `b` and `a + b`, then it is coprime to the order of
`c t ^ a (t - 1) ^ b` at one of the places `0`, `1` and `∞`. -/
private theorem exists_gcd_ord_eq_one {n : ℕ} {c : k} (hc : c ≠ 0) {a b : ℤ}
    (hcop : Int.gcd n a = 1 ∨ Int.gcd n b = 1 ∨ Int.gcd n (a + b) = 1) :
    ∃ P : Place k (RatFunc k), Int.gcd n
      (P.ord (algebraMap k (RatFunc k) c * RatFunc.X ^ a * (RatFunc.X - 1) ^ b)) = 1 := by
  rcases hcop with h | h | h
  · exact ⟨_, by rwa [Place.ord_adicOfIrreducible_X_algebraMap_mul_X_zpow_mul_X_sub_one_zpow hc]⟩
  · exact ⟨_, by
      rwa [Place.ord_adicOfIrreducible_X_sub_one_algebraMap_mul_X_zpow_mul_X_sub_one_zpow hc]⟩
  · exact ⟨_, by rwa [Place.ord_infty_algebraMap_mul_X_zpow_mul_X_sub_one_zpow hc, Int.gcd_neg]⟩

/-- **The degree of `y ^ n = c t ^ a (t - 1) ^ b`**: if `F = k(t)(y)` with
`y ^ n = c t ^ a (t - 1) ^ b` for a nonzero `c ∈ k`, and `n ≠ 0` is coprime to one of `a`, `b` and
`a + b`, then `[F : k(t)] = n`. -/
theorem finrank_eq_of_pow_eq_X_zpow_mul_X_sub_one_zpow {y : F} {n : ℕ} {c : k} {a b : ℤ}
    (hgen : (RatFunc k)⟮y⟯ = ⊤)
    (hy : y ^ n = algebraMap (RatFunc k) F
      (algebraMap k (RatFunc k) c * RatFunc.X ^ a * (RatFunc.X - 1) ^ b))
    (hn : n ≠ 0) (hc : c ≠ 0) (hcop : Int.gcd n a = 1 ∨ Int.gcd n b = 1 ∨ Int.gcd n (a + b) = 1) :
    Module.finrank (RatFunc k) F = n := by
  obtain ⟨P, hP⟩ := exists_gcd_ord_eq_one hc hcop
  exact P.valuation.finrank_eq_of_pow_eq_of_gcd_ord_eq_one hgen hy hn
    (by rwa [Place.ord_valuation])

end Degree

variable {k F : Type*} [Field k] [CharZero k] [Field F] [Algebra k F] [Algebra (RatFunc k) F]
  [IsScalarTower k (RatFunc k) F] [FiniteDimensional (RatFunc k) F]

namespace IsAlgebraicBelyiPair

/-- **A radical extension unramified outside `0`, `1` and `∞` is a Belyi pair**: if
`F = k(t)(y)` with `y ^ n = u` for a nonzero `u ∈ k(t)`, the constant field of `F` is `k`, and `n`
divides the order of `u` at every place of `k(t)` other than `0`, `1` and `∞`, then `F` is an
algebraic Belyi pair. -/
theorem of_pow_eq (hex : IsIntegrallyClosedIn k F) {y : F} {n : ℕ} {u : RatFunc k}
    (hgen : (RatFunc k)⟮y⟯ = ⊤) (hy : y ^ n = algebraMap (RatFunc k) F u) (hn : n ≠ 0)
    (hu : u ≠ 0) (hdvd : ∀ P ∉ Place.zeroOneInfty k, (n : ℤ) ∣ P.ord u) :
    IsAlgebraicBelyiPair k F where
  isIntegrallyClosedIn := hex
  ramificationIdx_eq_one hP :=
    Place.ramificationIdx_eq_one_of_pow_eq_of_dvd_ord k (RatFunc k) hgen hy
      (Nat.cast_ne_zero.mpr hn) hu (hdvd _ hP)

/-- **A radical extension unramified outside `0`, `1` and `∞` with a place of coprime order is a
Belyi pair**: if `F = k(t)(y)` with `y ^ n = u` for a nonzero `u ∈ k(t)`, `n` divides the order
of `u` at every place of `k(t)` other than `0`, `1` and `∞`, and `gcd(n, ord_P u) = 1` at some
place `P`, then `F` is an algebraic Belyi pair. The place `P` keeps the constant field of `F`
equal to `k`. -/
theorem of_pow_eq_of_gcd_ord_eq_one {y : F} {n : ℕ} {u : RatFunc k}
    (hgen : (RatFunc k)⟮y⟯ = ⊤) (hy : y ^ n = algebraMap (RatFunc k) F u) (hn : n ≠ 0)
    (hu : u ≠ 0) (hdvd : ∀ P ∉ Place.zeroOneInfty k, (n : ℤ) ∣ P.ord u)
    (P : Place k (RatFunc k)) (hP : Int.gcd n (P.ord u) = 1) : IsAlgebraicBelyiPair k F :=
  of_pow_eq (isIntegrallyClosedIn_of_pow_eq_of_gcd_ord_eq_one (IsFunctionField.ratFunc k)
    isIntegrallyClosedIn_ratFunc hgen hy (Nat.cast_ne_zero.mpr hn) hu P hP) hgen hy hn hu hdvd

/-- **The superelliptic Belyi pairs** `y ^ n = c t ^ a (t - 1) ^ b`: if `F = k(t)(y)` with
`y ^ n = c t ^ a (t - 1) ^ b` for a nonzero `c ∈ k`, and `n` is coprime to one of `a`, `b` and
`a + b`, then `F` is an algebraic Belyi pair. -/
theorem of_pow_eq_X_zpow_mul_X_sub_one_zpow {y : F} {n : ℕ} {c : k} {a b : ℤ}
    (hgen : (RatFunc k)⟮y⟯ = ⊤)
    (hy : y ^ n = algebraMap (RatFunc k) F
      (algebraMap k (RatFunc k) c * RatFunc.X ^ a * (RatFunc.X - 1) ^ b))
    (hn : n ≠ 0) (hc : c ≠ 0) (hcop : Int.gcd n a = 1 ∨ Int.gcd n b = 1 ∨ Int.gcd n (a + b) = 1) :
    IsAlgebraicBelyiPair k F := by
  have hdvd : ∀ P ∉ Place.zeroOneInfty k, (n : ℤ) ∣
      P.ord (algebraMap k (RatFunc k) c * RatFunc.X ^ a * (RatFunc.X - 1) ^ b) := fun P hP ↦ by
    rw [Place.ord_algebraMap_mul_X_zpow_mul_X_sub_one_zpow_of_notMem_zeroOneInfty hP hc]
    exact dvd_zero _
  obtain ⟨P, hP⟩ := exists_gcd_ord_eq_one hc hcop
  exact of_pow_eq_of_gcd_ord_eq_one hgen hy hn
    (RatFunc.algebraMap_mul_X_zpow_mul_X_sub_one_zpow_ne_zero hc a b) hdvd P hP

end IsAlgebraicBelyiPair

/-! ### The power map -/

section PowerMap

variable (k : Type*) [Field k] [CharZero k] (n : ℕ) [NeZero n]

/-- **The power map** `t ↦ u ^ n` is an algebraic Belyi pair: the function field
`k(u) = k(t)[Y] / (Y ^ n - t)` of the source, over the function field `k(t)` of the target. -/
theorem isAlgebraicBelyiPair_adjoinRoot_X_pow_sub_C_X :
    IsAlgebraicBelyiPair k (AdjoinRoot (X ^ n - C (RatFunc.X : RatFunc k))) :=
  .of_pow_eq_X_zpow_mul_X_sub_one_zpow (a := 1) (b := 0) (IntermediateField.adjoin_root_eq_top _)
    (by simpa [AdjoinRoot.algebraMap_eq] using root_X_pow_sub_C_pow n (RatFunc.X : RatFunc k))
    (NeZero.ne n) one_ne_zero (Or.inl (Int.gcd_one_right n))

end PowerMap

end TauCeti
