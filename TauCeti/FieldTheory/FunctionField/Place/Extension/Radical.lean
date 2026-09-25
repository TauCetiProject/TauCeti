/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Extension.Eisenstein
import TauCeti.FieldTheory.KummerExtension
import Mathlib.Data.Nat.Prime.Int

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

When `n` is coprime to `ord_P u` the lower bound is already the whole degree if `[F' : F] = n`.
If `y` generates `F'` over `F`, this degree equality follows from
`Valuation.finrank_eq_of_pow_eq_of_gcd_ord_eq_one`. Then `n ∣ e(P' ∣ P)` forces
`e(P' ∣ P) = n`: the place `P` is totally ramified in `F'`, and `ord_{P'} y = ord_P u`.
This covers, for instance, the places of `k(x)` at the simple zeros of a squarefree `f` in
`y ^ 2 = f(x)`, and the place at infinity when `f` has odd degree.

## Main results

* `TauCeti.Place.natCast_mul_ord_eq_ramificationIdx_mul_ord_of_pow_eq`:
  `n · ord_{P'} y = e(P' ∣ P) · ord_P u`.
* `TauCeti.Place.div_gcd_ord_dvd_ramificationIdx_of_pow_eq`: `n / gcd(n, ord_P u)` divides
  `e(P' ∣ P)`.
* `TauCeti.Place.isTotallyRamified_of_pow_eq_of_gcd_ord_eq_one` and
  `TauCeti.Place.ramificationIdx_eq_of_pow_eq_of_gcd_ord_eq_one`: if `[F' : F] = n` and
  `gcd(n, ord_P u) = 1`, then `P'` is totally ramified over `F` with `e(P' ∣ P) = n`.
* `TauCeti.Place.ord_eq_of_pow_eq_of_gcd_ord_eq_one`: in that case `ord_{P'} y = ord_P u`.
* `TauCeti.Place.finrank_eq_of_pow_eq_of_prime_of_not_dvd_ord`: a place whose order is not
  divisible by a prime exponent witnesses that the degree is that exponent.

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

omit [Algebra k F'] [IsScalarTower k F F'] [Algebra.IsIntegral F F'] in
/-- **The degree of a radical extension of prime exponent**: if `y` generates `F'` over `F`,
satisfies `y ^ n = u`, and `n` does not divide the order of `u` at the place `P`, then
`[F' : F] = n`. -/
theorem finrank_eq_of_pow_eq_of_prime_of_not_dvd_ord (P : Place k F) {y : F'} {n : ℕ} {u : F}
    (hp : n.Prime) (hgen : F⟮y⟯ = ⊤) (hy : y ^ n = algebraMap F F' u)
    (h : ¬ (n : ℤ) ∣ P.ord u) :
    Module.finrank F F' = n := by
  refine Valuation.finrank_eq_of_pow_eq_of_gcd_ord_eq_one P.valuation hgen hy hp.ne_zero ?_
  rw [Valuation.ord_def, ← P.ord_def]
  exact Int.isCoprime_iff_gcd_eq_one.mp
    ((Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd.mpr h)

omit [Algebra k F'] [IsScalarTower k F F'] [Algebra.IsIntegral F F'] in
/-- If `F' = F(y)` with `y ^ n = u` and `n` coprime to `ord_P u`, then some generator `z` of
`F' / F` has `z ^ n` of order one at `P`. -/
theorem exists_adjoin_eq_top_pow_eq_ord_eq_one (P : Place k F) {y : F'} {n : ℕ} {u : F}
    (hgen : F⟮y⟯ = ⊤) (hy : y ^ n = algebraMap F F' u) (hu : u ≠ 0) (hn0 : n ≠ 0)
    (h : Int.gcd n (P.ord u) = 1) :
    ∃ z : F', ∃ c : F, F⟮z⟯ = ⊤ ∧ z ^ n = algebraMap F F' c ∧ P.ord c = 1 ∧ z ≠ 0 := by
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [zero_pow hn0, eq_comm, map_eq_zero] at hy
    exact hu hy
  set α := Int.gcdA n (P.ord u)
  set β := Int.gcdB n (P.ord u)
  have hab : (n : ℤ) * α + P.ord u * β = 1 := by
    rw [← Int.gcd_eq_gcd_ab, h, Nat.cast_one]
  obtain ⟨w, hw0, hw⟩ := P.exists_ne_zero_ord_eq 1
  have hW0 : algebraMap F F' w ≠ 0 := (_root_.map_ne_zero _).mpr hw0
  set z := y ^ β * algebraMap F F' w ^ α with hz_def
  refine ⟨z, u ^ β * w ^ (α * n), ?_, ?_, ?_, mul_ne_zero (zpow_ne_zero _ hy0) (zpow_ne_zero _ hW0)⟩
  · have hyz : y = (z * algebraMap F F' w ^ (-α)) ^ P.ord u * algebraMap F F' u ^ α := by
      calc
        y = y ^ ((n : ℤ) * α + P.ord u * β) := by rw [hab, zpow_one]
        _ = y ^ (P.ord u * β) * y ^ ((n : ℤ) * α) := by
          rw [zpow_add₀ hy0]
          exact mul_comm _ _
        _ = (z * algebraMap F F' w ^ (-α)) ^ P.ord u * algebraMap F F' u ^ α := by
          rw [hz_def, zpow_neg, mul_inv_cancel_right₀ (zpow_ne_zero _ hW0), ← hy,
            ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm β]
    have hymem : y ∈ F⟮z⟯ := by
      rw [hyz]
      exact mul_mem (zpow_mem (mul_mem (IntermediateField.mem_adjoin_simple_self F z)
        (zpow_mem (IntermediateField.algebraMap_mem _ w) _)) _)
        (zpow_mem (IntermediateField.algebraMap_mem _ u) _)
    rw [eq_top_iff, ← hgen, IntermediateField.adjoin_simple_le_iff]
    exact hymem
  · calc
      z ^ n = (y ^ β) ^ n * (algebraMap F F' w ^ α) ^ n := by rw [hz_def, mul_pow]
      _ = y ^ (β * n) * (algebraMap F F' w) ^ (α * n) := by
        rw [← zpow_natCast (y ^ β), ← zpow_natCast (algebraMap F F' w ^ α), zpow_mul,
          zpow_mul]
      _ = algebraMap F F' u ^ β * (algebraMap F F' w) ^ (α * n) := by
        rw [mul_comm β, zpow_mul, zpow_natCast, hy]
      _ = algebraMap F F' (u ^ β * w ^ (α * n)) := by rw [map_mul, map_zpow₀, map_zpow₀]
  · rw [P.ord_mul (zpow_ne_zero _ hu) (zpow_ne_zero _ hw0), ord_zpow, ord_zpow, hw]
    linarith

/-- **Total ramification in a radical extension** (Stichtenoth, Proposition 3.7.3(b)): if
`[F' : F] = n` with `y ^ n = u`, `n ≠ 0`, and `n` is coprime to the order of `u` at the place `P`
of `F` below `P'`, then `e(P' ∣ P) = n`. -/
theorem ramificationIdx_eq_of_pow_eq_of_gcd_ord_eq_one {y : F'} {n : ℕ} {u : F}
    (hfr : Module.finrank F F' = n) (hy : y ^ n = algebraMap F F' u) (hn : n ≠ 0)
    (h : Int.gcd n ((P'.restrict k F).ord u) = 1) :
    ramificationIdx F P' = n := by
  have hfin : FiniteDimensional F F' := FiniteDimensional.of_finrank_pos (by
    rw [hfr]
    exact Nat.pos_of_ne_zero hn)
  have hdvd := div_gcd_ord_dvd_ramificationIdx_of_pow_eq k F (P' := P') hn hy
  rw [h, Nat.div_one] at hdvd
  have hle : ramificationIdx F P' ≤ n :=
    hfr ▸ @ramificationIdx_le_finrank k' F F' _ _ _ _ _ P' hfin
  exact hle.antisymm (Nat.le_of_dvd (ramificationIdx_pos F P') hdvd)

/-- **Total ramification in a radical extension** (Stichtenoth, Proposition 3.7.3(b)): if
`[F' : F] = n` with `y ^ n = u`, `n ≠ 0`, and `n` is coprime to the order of `u` at the place `P`
of `F` below `P'`, then `P'` is totally ramified over `F`. With
`TauCeti.Place.setOf_restrict_eq_eq_singleton_of_isTotallyRamified` this says that `P'` is the
only place of `F'` over `P`, with relative degree `1`. -/
theorem isTotallyRamified_of_pow_eq_of_gcd_ord_eq_one {y : F'} {n : ℕ} {u : F}
    (hfr : Module.finrank F F' = n) (hy : y ^ n = algebraMap F F' u) (hn : n ≠ 0)
    (h : Int.gcd n ((P'.restrict k F).ord u) = 1) :
    IsTotallyRamified F P' := by
  have he := ramificationIdx_eq_of_pow_eq_of_gcd_ord_eq_one k F hfr hy hn h
  rw [isTotallyRamified_iff, he, hfr]

/-- **The order of the radical at a totally ramified place**: if `[F' : F] = n` with `y ^ n = u`,
`n ≠ 0`, and `n` is coprime to the order of `u` at the place `P` of `F` below `P'`, then
`ord_{P'} y = ord_P u`. In particular `y` is a prime element at `P'` when `u` is one at `P`. -/
theorem ord_eq_of_pow_eq_of_gcd_ord_eq_one {y : F'} {n : ℕ} {u : F}
    (hfr : Module.finrank F F' = n) (hy : y ^ n = algebraMap F F' u) (hn : n ≠ 0)
    (h : Int.gcd n ((P'.restrict k F).ord u) = 1) :
    P'.ord y = (P'.restrict k F).ord u := by
  have hkey := natCast_mul_ord_eq_ramificationIdx_mul_ord_of_pow_eq k F (P' := P') hy
  rw [ramificationIdx_eq_of_pow_eq_of_gcd_ord_eq_one k F hfr hy hn h] at hkey
  exact mul_left_cancel₀ (by exact_mod_cast hn) hkey

end Place

end TauCeti
