/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Extension.Eisenstein
public import TauCeti.RingTheory.Valuation.Discrete.PowerSubSelf

/-!
# Total ramification at a prime-to-characteristic Artin–Schreier pole

Suppose `F' = F(y)` and `y ^ p - y = u` in characteristic `p`. If `u` has a pole at `P`
whose order is not divisible by `p`, every place `P'` above `P` is totally ramified:
`[F' : F] = e(P' ∣ P) = p` and `ord_{P'} y = ord_P u`. The existing total-ramification
API then gives relative degree one and uniqueness of the place above `P`.

The results are stated in the characteristic-independent form `y ^ n - y = u`, `n > 1`,
and `gcd(n, ord_P u) = 1`. Taking orders gives `n · ord_{P'} y = e(P' ∣ P) · ord_P u`,
so `n` divides `e`. The polynomial relation bounds the degree by `n`, and the fundamental
inequality bounds `e` by that degree. Thus the extension degree is proved, rather than
assumed. No existence of a reduced representative is claimed: in the Artin–Schreier
application, the prime-to-`p` pole is an explicit input.

The base-field obstruction is
`Valuation.ne_pow_sub_self_of_ord_neg_of_not_dvd`: such a pole also ensures
`u ≠ w ^ p - w` for every `w ∈ F`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Proposition 3.7.8.
-/

public section

open Polynomial
open scoped IntermediateField

namespace TauCeti.Place

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k' F'] [Algebra F F'] [Algebra k F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']
variable (k F) [Algebra.IsIntegral F F'] {P' : Place k' F'}

/-- Orders in `y ^ n - y = u` at a pole of `u`: the power term dominates, giving
`n · ord_{P'} y = e(P' ∣ P) · ord_P u`. -/
theorem natCast_mul_ord_eq_ramificationIdx_mul_ord_of_pow_sub_self_eq
    {y : F'} {n : ℕ} {u : F} (hn : 1 < n)
    (hy : y ^ n - y = algebraMap F F' u) (hu : (P'.restrict k F).ord u < 0) :
    (n : ℤ) * P'.ord y = ramificationIdx F P' * (P'.restrict k F).ord u := by
  have hneg : P'.ord (y ^ n - y) < 0 := by
    rw [hy, ord_algebraMap_restrict k F P']
    exact mul_neg_of_pos_of_neg (by exact_mod_cast ramificationIdx_pos F P') hu
  have hyneg : P'.valuation.ord y < 0 :=
    (P'.valuation.ord_pow_sub_self_neg_iff hn y).mp (by
      rwa [Valuation.ord_def, ← P'.ord_def])
  calc
    (n : ℤ) * P'.ord y = P'.ord (y ^ n - y) := by
      simpa only [Valuation.ord_def, ← P'.ord_def] using
        (P'.valuation.ord_pow_sub_self_of_ord_neg hn hyneg).symm
    _ = ramificationIdx F P' * (P'.restrict k F).ord u := by
      rw [hy, ord_algebraMap_restrict k F P']

private theorem finrank_eq_and_ramificationIdx_eq_of_pow_sub_self_eq
    {y : F'} {n : ℕ} {u : F} (hn : 1 < n) (hgen : F⟮y⟯ = ⊤)
    (hy : y ^ n - y = algebraMap F F' u) (hu : (P'.restrict k F).ord u < 0)
    (hcop : Int.gcd n ((P'.restrict k F).ord u) = 1) :
    Module.finrank F F' = n ∧ ramificationIdx F P' = n := by
  have hint : IsIntegral F y := Algebra.IsIntegral.isIntegral y
  have hfr : Module.finrank F F' = (minpoly F y).natDegree := by
    rw [← IntermediateField.finrank_top', ← hgen, IntermediateField.adjoin.finrank hint]
  have hfin : FiniteDimensional F F' := FiniteDimensional.of_finrank_pos (by
    rw [hfr]
    exact minpoly.natDegree_pos hint)
  have hmonic : (X ^ n - (X + C u) : F[X]).Monic :=
    monic_X_pow_sub (by rw [degree_X_add_C]; exact_mod_cast hn)
  have hroot : aeval y (X ^ n - (X + C u)) = 0 := by
    simp only [map_sub, map_pow, aeval_X, map_add, aeval_C]
    rw [sub_add_eq_sub_sub, hy, sub_self]
  have hdeg : (X ^ n - (X + C u) : F[X]).natDegree = n := by
    rw [natDegree_sub_eq_left_of_natDegree_lt (by
      rw [natDegree_X_add_C, natDegree_X_pow]
      exact hn), natDegree_X_pow]
  have hle : Module.finrank F F' ≤ n := by
    rw [hfr, ← hdeg]
    exact natDegree_le_natDegree (minpoly.min F y hmonic hroot)
  have hkey := natCast_mul_ord_eq_ramificationIdx_mul_ord_of_pow_sub_self_eq k F hn hy hu
  have hdvd : (n : ℤ) ∣ (ramificationIdx F P' : ℤ) :=
    Int.dvd_of_dvd_mul_left_of_gcd_one ⟨P'.ord y, hkey.symm⟩ hcop
  have hlow : n ≤ ramificationIdx F P' :=
    Nat.le_of_dvd (ramificationIdx_pos F P') (Int.natCast_dvd_natCast.mp hdvd)
  have he : ramificationIdx F P' ≤ Module.finrank F F' := ramificationIdx_le_finrank F P'
  omega

/-- A generator satisfying `y ^ n - y = u` has degree `n` if `u` has a pole of order
coprime to `n`. In particular this proves degree `p` for an Artin–Schreier equation with a
prime-to-`p` pole. -/
theorem finrank_eq_of_pow_sub_self_eq_of_gcd_ord_eq_one
    {y : F'} {n : ℕ} {u : F} (hn : 1 < n) (hgen : F⟮y⟯ = ⊤)
    (hy : y ^ n - y = algebraMap F F' u) (hu : (P'.restrict k F).ord u < 0)
    (hcop : Int.gcd n ((P'.restrict k F).ord u) = 1) : Module.finrank F F' = n :=
  (finrank_eq_and_ramificationIdx_eq_of_pow_sub_self_eq k F hn hgen hy hu hcop).1

/-- A pole of order coprime to `n` is totally ramified in a generated extension
`y ^ n - y = u`: the ramification index equals `n`. -/
theorem ramificationIdx_eq_of_pow_sub_self_eq_of_gcd_ord_eq_one
    {y : F'} {n : ℕ} {u : F} (hn : 1 < n) (hgen : F⟮y⟯ = ⊤)
    (hy : y ^ n - y = algebraMap F F' u) (hu : (P'.restrict k F).ord u < 0)
    (hcop : Int.gcd n ((P'.restrict k F).ord u) = 1) : ramificationIdx F P' = n :=
  (finrank_eq_and_ramificationIdx_eq_of_pow_sub_self_eq k F hn hgen hy hu hcop).2

/-- A pole of order coprime to `n` is totally ramified in `F(y) / F` when
`y ^ n - y = u`. The existing total-ramification API gives relative degree one and a
singleton fibre over the restricted place. -/
theorem isTotallyRamified_of_pow_sub_self_eq_of_gcd_ord_eq_one
    {y : F'} {n : ℕ} {u : F} (hn : 1 < n) (hgen : F⟮y⟯ = ⊤)
    (hy : y ^ n - y = algebraMap F F' u) (hu : (P'.restrict k F).ord u < 0)
    (hcop : Int.gcd n ((P'.restrict k F).ord u) = 1) : IsTotallyRamified F P' := by
  have h := finrank_eq_and_ramificationIdx_eq_of_pow_sub_self_eq k F hn hgen hy hu hcop
  rw [isTotallyRamified_iff, h.1, h.2]

/-- The generator has the same order as `u` below a totally ramified pole of
`y ^ n - y = u`, provided the pole order is coprime to `n`. -/
theorem ord_eq_of_pow_sub_self_eq_of_gcd_ord_eq_one
    {y : F'} {n : ℕ} {u : F} (hn : 1 < n) (hgen : F⟮y⟯ = ⊤)
    (hy : y ^ n - y = algebraMap F F' u) (hu : (P'.restrict k F).ord u < 0)
    (hcop : Int.gcd n ((P'.restrict k F).ord u) = 1) :
    P'.ord y = (P'.restrict k F).ord u := by
  have hkey := natCast_mul_ord_eq_ramificationIdx_mul_ord_of_pow_sub_self_eq k F hn hy hu
  rw [ramificationIdx_eq_of_pow_sub_self_eq_of_gcd_ord_eq_one k F hn hgen hy hu hcop] at hkey
  exact mul_left_cancel₀ (by exact_mod_cast (by omega : n ≠ 0)) hkey

end TauCeti.Place
