/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Extension.Eisenstein
public import TauCeti.FieldTheory.KummerExtension

/-!
# Ramification in a radical extension `y ^ n = u`

Let `F' / k'` be an extension of the field extension `F / k`, and let `y ∈ F'` satisfy
`y ^ n = u` for some `u ∈ F`. At a place `P'` of `F'` over the place `P` of `F`, taking orders
in `y ^ n = u` gives

`n · ord_{P'} y = e(P' ∣ P) · ord_P u`.

Writing `r_P = gcd(n, ord_P u)`, the two quotients `n / r_P` and `ord_P u / r_P` are coprime, so
`n / r_P` divides the ramification index. This is the lower half of the ramification data of a
Kummer extension (Stichtenoth, Proposition 3.7.3(b), where `e(P' ∣ P) = n / r_P`), and it holds
in every characteristic and without any root of unity in the constants. The upper half needs
`char k ∤ n`: it is the statement that adjoining an `r_P`-th root of a unit of `𝒪_P` is
unramified.

When `n` is coprime to `ord_P u` the lower bound is already the whole degree. If `y` generates
`F'` over `F`, then `X ^ n - C u` is irreducible by the valuative criterion
`Valuation.X_pow_sub_C_irreducible_of_gcd_ord_eq_one`, so `[F' : F] = n`, and `n ∣ e(P' ∣ P)`
forces `e(P' ∣ P) = n`: the place `P` is totally ramified in `F'`, and `ord_{P'} y = ord_P u`.
This covers, for instance, the places of `k(x)` at the simple zeros of a squarefree `f` in
`y ^ 2 = f(x)`, and the place at infinity when `f` has odd degree.

## Main results

* `TauCeti.Place.natCast_mul_ord_eq_ramificationIdx_mul_ord_of_pow_eq`:
  `n · ord_{P'} y = e(P' ∣ P) · ord_P u`.
* `TauCeti.Place.div_gcd_ord_dvd_ramificationIdx_of_pow_eq`: `n / gcd(n, ord_P u)` divides
  `e(P' ∣ P)`.
* `TauCeti.Place.isTotallyRamified_of_pow_eq_of_gcd_ord_eq_one` and
  `TauCeti.Place.ramificationIdx_eq_of_pow_eq_of_gcd_ord_eq_one`: if `F' = F(y)` and
  `gcd(n, ord_P u) = 1`, then `P'` is totally ramified over `F` with `e(P' ∣ P) = n`.
* `TauCeti.Place.ord_eq_of_pow_eq_of_gcd_ord_eq_one`: in that case `ord_{P'} y = ord_P u`.
* `TauCeti.Place.finrank_eq_of_pow_eq_of_gcd_ord_eq_one`: `[F(y) : F] = n` as soon as one place
  of `F` has `gcd(n, ord_P u) = 1`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Proposition 3.7.3.
-/

public section

open Polynomial

open scoped IntermediateField

namespace TauCeti

namespace Place

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k' F'] [Algebra F F'] [Algebra k F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']

omit [Algebra k F'] [IsScalarTower k F F'] in
/-- **The degree of a radical extension** (Stichtenoth, Proposition 3.7.3): if `y` generates `F'`
over `F` with `y ^ n = u`, and some place `P` of `F / k` has `gcd(n, ord_P u) = 1`, then
`[F' : F] = n`, because `X ^ n - C u` is irreducible. -/
theorem finrank_eq_of_pow_eq_of_gcd_ord_eq_one (P : Place k F) {y : F'} {n : ℕ} {u : F}
    (htop : F⟮y⟯ = ⊤) (hy : y ^ n = algebraMap F F' u) (hn : n ≠ 0)
    (h : Int.gcd n (P.ord u) = 1) : Module.finrank F F' = n := by
  have hord : P.valuation.ord u = P.ord u := by rw [Valuation.ord_def, P.ord_def]
  have hirr : Irreducible (X ^ n - C u) :=
    P.valuation.X_pow_sub_C_irreducible_of_gcd_ord_eq_one hn (hord ▸ h)
  have hroot : aeval y (X ^ n - C u) = 0 := by rw [map_sub, aeval_X_pow, aeval_C, hy, sub_self]
  have hint : IsIntegral F y := ⟨X ^ n - C u, monic_X_pow_sub_C u hn, by rwa [← aeval_def]⟩
  have hmin : X ^ n - C u = minpoly F y :=
    minpoly.eq_of_irreducible_of_monic hirr hroot (monic_X_pow_sub_C u hn)
  rw [← IntermediateField.finrank_top', ← htop, IntermediateField.adjoin.finrank hint, ← hmin,
    natDegree_X_pow_sub_C]

variable (k F) [Algebra.IsIntegral F F'] {P' : Place k' F'}

/-- **Orders in a radical extension**: if `y ^ n = u` with `u ∈ F`, then at every place `P'` of
`F'` the orders of `y` and `u` are related by `n · ord_{P'} y = e(P' ∣ P) · ord_P u`, where `P` is
the place of `F` below `P'`. -/
theorem natCast_mul_ord_eq_ramificationIdx_mul_ord_of_pow_eq {y : F'} {n : ℕ} {u : F}
    (hy : y ^ n = algebraMap F F' u) :
    (n : ℤ) * P'.ord y = ramificationIdx F P' * (P'.restrict k F).ord u := by
  rw [← ord_pow, hy, ord_algebraMap_restrict k F P']

/-- **The ramification lower bound of a radical extension** (Stichtenoth, Proposition 3.7.3(b)):
if `y ^ n = u` with `u ∈ F` and `n ≠ 0`, then `n / gcd(n, ord_P u)` divides the ramification index
`e(P' ∣ P)`. No hypothesis on the characteristic or on roots of unity is needed; for `u = 0` the
order is the junk value `0` and the statement is trivial. -/
theorem div_gcd_ord_dvd_ramificationIdx_of_pow_eq {y : F'} {n : ℕ} {u : F} (hn : n ≠ 0)
    (hy : y ^ n = algebraMap F F' u) :
    n / Int.gcd n ((P'.restrict k F).ord u) ∣ ramificationIdx F P' := by
  set m := (P'.restrict k F).ord u
  set r := Int.gcd n m
  have hr : 0 < r := Int.gcd_pos_of_ne_zero_left m (by exact_mod_cast hn)
  -- Divide `n · ord_{P'} y = e · m` by `r = gcd(n, m)`.
  have hkey := natCast_mul_ord_eq_ramificationIdx_mul_ord_of_pow_eq k F (P' := P') hy
  have hn' : (n : ℤ) = (n : ℤ) / r * r := (Int.ediv_mul_cancel (Int.gcd_dvd_left _ _)).symm
  have hm' : m = m / r * r := (Int.ediv_mul_cancel (Int.gcd_dvd_right _ _)).symm
  have hdiv : (n : ℤ) / r * P'.ord y = ramificationIdx F P' * (m / r) := by
    have hr0 : (r : ℤ) ≠ 0 := by exact_mod_cast hr.ne'
    apply mul_right_cancel₀ hr0
    calc (n : ℤ) / r * P'.ord y * r = (n : ℤ) / r * r * P'.ord y := by ring
      _ = ramificationIdx F P' * (m / r * r) := by rw [← hn', ← hm', hkey]
      _ = ramificationIdx F P' * (m / r) * r := by ring
  have hdvd : (n : ℤ) / r ∣ ramificationIdx F P' :=
    Int.dvd_of_dvd_mul_left_of_gcd_one ⟨_, hdiv.symm⟩ (Int.gcd_div_gcd_div_gcd hr)
  rw [← Int.natCast_dvd_natCast, Int.natCast_div]
  exact hdvd

private theorem ramificationIdx_eq_and_finrank_eq {y : F'} {n : ℕ} {u : F}
    (htop : F⟮y⟯ = ⊤) (hy : y ^ n = algebraMap F F' u) (hn : n ≠ 0)
    (h : Int.gcd n ((P'.restrict k F).ord u) = 1) :
    ramificationIdx F P' = n ∧ Module.finrank F F' = n := by
  have hfr := finrank_eq_of_pow_eq_of_gcd_ord_eq_one (P'.restrict k F) htop hy hn h
  have hfin : FiniteDimensional F F' := FiniteDimensional.of_finrank_pos (by
    rw [hfr]
    exact Nat.pos_of_ne_zero hn)
  have hdvd := div_gcd_ord_dvd_ramificationIdx_of_pow_eq k F (P' := P') hn hy
  rw [h, Nat.div_one] at hdvd
  have hle : ramificationIdx F P' ≤ n :=
    hfr ▸ @ramificationIdx_le_finrank k' F F' _ _ _ _ _ P' hfin
  exact ⟨hle.antisymm (Nat.le_of_dvd (ramificationIdx_pos F P') hdvd), hfr⟩

/-- **Total ramification in a radical extension** (Stichtenoth, Proposition 3.7.3(b)): if
`F' = F(y)` with `y ^ n = u`, `n ≠ 0`, and `n` is coprime to the order of `u` at the place `P`
of `F` below `P'`, then `e(P' ∣ P) = n`. -/
theorem ramificationIdx_eq_of_pow_eq_of_gcd_ord_eq_one {y : F'} {n : ℕ} {u : F}
    (htop : F⟮y⟯ = ⊤) (hy : y ^ n = algebraMap F F' u) (hn : n ≠ 0)
    (h : Int.gcd n ((P'.restrict k F).ord u) = 1) :
    ramificationIdx F P' = n :=
  (ramificationIdx_eq_and_finrank_eq k F htop hy hn h).1

/-- **Total ramification in a radical extension** (Stichtenoth, Proposition 3.7.3(b)): if
`F' = F(y)` with `y ^ n = u`, `n ≠ 0`, and `n` is coprime to the order of `u` at the place `P`
of `F` below `P'`, then `P'` is totally ramified over `F`. With
`TauCeti.Place.setOf_restrict_eq_eq_singleton_of_isTotallyRamified` this says that `P'` is the
only place of `F'` over `P`, with relative degree `1`. -/
theorem isTotallyRamified_of_pow_eq_of_gcd_ord_eq_one {y : F'} {n : ℕ} {u : F}
    (htop : F⟮y⟯ = ⊤) (hy : y ^ n = algebraMap F F' u) (hn : n ≠ 0)
    (h : Int.gcd n ((P'.restrict k F).ord u) = 1) :
    IsTotallyRamified F P' := by
  obtain ⟨he, hfr⟩ := ramificationIdx_eq_and_finrank_eq k F htop hy hn h
  rw [isTotallyRamified_iff, he, hfr]

/-- **The order of the radical at a totally ramified place**: if `F' = F(y)` with `y ^ n = u`,
`n ≠ 0`, and `n` is coprime to the order of `u` at the place `P` of `F` below `P'`, then
`ord_{P'} y = ord_P u`. In particular `y` is a prime element at `P'` when `u` is one at `P`. -/
theorem ord_eq_of_pow_eq_of_gcd_ord_eq_one {y : F'} {n : ℕ} {u : F}
    (htop : F⟮y⟯ = ⊤) (hy : y ^ n = algebraMap F F' u) (hn : n ≠ 0)
    (h : Int.gcd n ((P'.restrict k F).ord u) = 1) :
    P'.ord y = (P'.restrict k F).ord u := by
  have hkey := natCast_mul_ord_eq_ramificationIdx_mul_ord_of_pow_eq k F (P' := P') hy
  rw [ramificationIdx_eq_of_pow_eq_of_gcd_ord_eq_one k F htop hy hn h] at hkey
  exact mul_left_cancel₀ (by exact_mod_cast hn) hkey

end Place

end TauCeti
