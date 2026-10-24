/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.AdjoinRoot
public import TauCeti.FieldTheory.FunctionField.Place.RatFunc.Order
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Eisenstein
import Mathlib.FieldTheory.SeparableDegree
import TauCeti.FieldTheory.FunctionField.Different.Radical
import TauCeti.FieldTheory.Kummer.Extension

/-!
# The extension `k(t)[Y] / (Y ^ n - t)`

For `n ≠ 0`, the polynomial `Y ^ n - t` is irreducible over the rational function field `k(t)`,
since `t` has order one at the place `t = 0`. So `k(t)[Y] / (Y ^ n - t)` is a field extension of
`k(t)` of degree `n`, and it is separable when `n` is invertible in `k`. It is the function field
of the source of the power map `u ↦ u ^ n` of the projective line.

## Main results

* `TauCeti.irreducible_X_pow_sub_C_X`: `Y ^ n - t` is irreducible over `k(t)`.
* `TauCeti.finrank_adjoinRoot_X_pow_sub_C_X`: `k(t)[Y] / (Y ^ n - t)` has degree `n` over `k(t)`.
* `TauCeti.isSeparable_adjoinRoot_X_pow_sub_C_X`: it is separable over `k(t)` when `n` is
  invertible in `k`.
* `TauCeti.isTotallyRamified_adjoinRoot_X_pow_sub_C_X` and
  `TauCeti.ramificationIdx_adjoinRoot_X_pow_sub_C_X_eq_one`: when `n` is invertible in `k`, it is
  totally ramified over `t = 0` and `t = ∞` and unramified elsewhere.
-/

public section

open Polynomial

namespace TauCeti

variable (k : Type*) [Field k] (n : ℕ) [NeZero n]

/-- `Y ^ n - t` is irreducible over `k(t)`, because `t` has order one at the place `t = 0`. -/
theorem irreducible_X_pow_sub_C_X : Irreducible (X ^ n - C (RatFunc.X : RatFunc k)) :=
  (Place.adicOfIrreducible (irreducible_X (R := k))).valuation
    |>.X_pow_sub_C_irreducible_of_gcd_ord_eq_one (NeZero.ne n) (by
      rw [Place.ord_valuation, Place.ord_adicOfIrreducible_X_self, Int.gcd_one_right])

instance : Fact (Irreducible (X ^ n - C (RatFunc.X : RatFunc k))) :=
  ⟨irreducible_X_pow_sub_C_X k n⟩

instance : FiniteDimensional (RatFunc k) (AdjoinRoot (X ^ n - C (RatFunc.X : RatFunc k))) :=
  (monic_X_pow_sub_C _ (NeZero.ne n)).finite_adjoinRoot

/-- `k(t)[Y] / (Y ^ n - t)` has degree `n` over `k(t)`. -/
theorem finrank_adjoinRoot_X_pow_sub_C_X :
    Module.finrank (RatFunc k) (AdjoinRoot (X ^ n - C (RatFunc.X : RatFunc k))) = n := by
  rw [(AdjoinRoot.powerBasis (X_pow_sub_C_ne_zero (NeZero.pos n) _)).finrank,
    AdjoinRoot.powerBasis_dim, natDegree_X_pow_sub_C]

open _root_.IntermediateField in
/-- `k(t)[Y] / (Y ^ n - t)` is separable over `k(t)` when `n` is invertible in `k`. -/
theorem isSeparable_adjoinRoot_X_pow_sub_C_X (hn : (n : k) ≠ 0) :
    Algebra.IsSeparable (RatFunc k) (AdjoinRoot (X ^ n - C (RatFunc.X : RatFunc k))) := by
  have hn' : (n : RatFunc k) ≠ 0 := by
    rwa [← map_natCast (algebraMap k (RatFunc k)), _root_.map_ne_zero]
  have hsep : IsSeparable (RatFunc k) (AdjoinRoot.root (X ^ n - C (RatFunc.X : RatFunc k))) :=
    (separable_X_pow_sub_C _ hn' RatFunc.X_ne_zero).of_dvd
      (minpoly.dvd _ _ (by rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]))
  have h := (isSeparable_adjoin_simple_iff_isSeparable (RatFunc k) _).2 hsep
  rw [adjoin_root_eq_top] at h
  exact (isSeparable_top (RatFunc k) _).mp h

/-- The root of `Y ^ n - t` is an `n`-th root of `t`, written in the form
`y ^ n = c t ^ a (t - 1) ^ b` with `c = 1`, `a = 1` and `b = 0`. -/
private theorem root_pow_eq :
    AdjoinRoot.root (X ^ n - C (RatFunc.X : RatFunc k)) ^ n =
      algebraMap (RatFunc k) (AdjoinRoot (X ^ n - C (RatFunc.X : RatFunc k)))
        (algebraMap k (RatFunc k) 1 * RatFunc.X ^ (1 : ℤ) * (RatFunc.X - 1) ^ (0 : ℤ)) := by
  have h := AdjoinRoot.aeval_eq (f := X ^ n - C (RatFunc.X : RatFunc k)) (X ^ n - C RatFunc.X)
  rw [AdjoinRoot.mk_self, map_sub, aeval_X_pow, aeval_C, sub_eq_zero] at h
  simpa using h

/-- **The power map is totally ramified over `0` and `∞`**: if `n` is invertible in `k`, every
place of `k(t)[Y] / (Y ^ n - t)` over `t = 0` or `t = ∞` has ramification index `n`, so it is the
only place over that point and has relative degree one. -/
theorem isTotallyRamified_adjoinRoot_X_pow_sub_C_X (hn : (n : k) ≠ 0)
    {P : Place k (AdjoinRoot (X ^ n - C (RatFunc.X : RatFunc k)))}
    (hP : P.restrict k (RatFunc k) = Place.adicOfIrreducible (irreducible_X (R := k)) ∨
      P.restrict k (RatFunc k) = Place.infty k) :
    Place.IsTotallyRamified (RatFunc k) P := by
  have := isSeparable_adjoinRoot_X_pow_sub_C_X k n hn
  rw [Place.isTotallyRamified_iff, finrank_adjoinRoot_X_pow_sub_C_X,
    Place.ramificationIdx_eq_of_pow_eq k (RatFunc k) (IntermediateField.adjoin_root_eq_top _)
      (root_pow_eq k n) hn
      (RatFunc.algebraMap_mul_X_zpow_mul_X_sub_one_zpow_ne_zero one_ne_zero 1 0)]
  rcases hP with hP | hP <;> rw [hP]
  · rw [Place.ord_adicOfIrreducible_X_algebraMap_mul_X_zpow_mul_X_sub_one_zpow one_ne_zero,
      Int.gcd_one_right, Nat.div_one]
  · rw [Place.ord_infty_algebraMap_mul_X_zpow_mul_X_sub_one_zpow one_ne_zero, add_zero,
      Int.gcd_neg, Int.gcd_one_right, Nat.div_one]

/-- **The power map is unramified away from `0` and `∞`**: if `n` is invertible in `k`, every
place of `k(t)[Y] / (Y ^ n - t)` over a place of `k(t)` other than `t = 0` and `t = ∞`, in
particular over `t = 1`, has ramification index `1`. -/
theorem ramificationIdx_adjoinRoot_X_pow_sub_C_X_eq_one (hn : (n : k) ≠ 0)
    {P : Place k (AdjoinRoot (X ^ n - C (RatFunc.X : RatFunc k)))}
    (hP0 : P.restrict k (RatFunc k) ≠ Place.adicOfIrreducible (irreducible_X (R := k)))
    (hPinf : P.restrict k (RatFunc k) ≠ Place.infty k) :
    Place.ramificationIdx (RatFunc k) P = 1 := by
  have := isSeparable_adjoinRoot_X_pow_sub_C_X k n hn
  refine Place.ramificationIdx_eq_one_of_pow_eq_of_dvd_ord k (RatFunc k)
    (IntermediateField.adjoin_root_eq_top _) (root_pow_eq k n) hn
    (RatFunc.algebraMap_mul_X_zpow_mul_X_sub_one_zpow_ne_zero one_ne_zero 1 0) ?_
  rw [Place.ord_algebraMap_mul_X_zpow_mul_X_sub_one_zpow _ one_ne_zero,
    Place.ord_X_eq_zero_of_ne hP0 hPinf]
  simp

end TauCeti
