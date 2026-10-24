/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.AdjoinRoot
public import TauCeti.FieldTheory.FunctionField.Place.RatFunc.Order
import Mathlib.FieldTheory.SeparableDegree
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

open IntermediateField in
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

end TauCeti
