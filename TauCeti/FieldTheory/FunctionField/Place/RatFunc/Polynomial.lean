/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Extension.Basic
public import TauCeti.FieldTheory.FunctionField.Place.RatFunc.Order
import TauCeti.FieldTheory.RatFunc.Transcendental

/-!
# Places over `k(t)` for a polynomial map `t = q(x)`

Let `F` be an extension of `k(t)` in which `t` acts as `q(x)`, for an element `x ∈ F` and a
polynomial `q ∈ k[X]`. This file locates the place of `k(t)` under a place `P` of `F` in terms of
`x`: if `P` does not lie over `t = ∞`, then `x` is regular at `P`; and if `x` is regular at `P`
with `q(x(P)) = c`, then `P` lies over `t = c`.

## Main results

* `TauCeti.Place.mem_integers_of_restrict_ne_infty`: `x` is regular at every place of `F` that does
  not lie over `t = ∞`.
* `TauCeti.Place.restrict_eq_adicOfIrreducible_X_sub_C_of_aeval_residue_eq`: a place of `F` at
  which `x` is regular lies over `t = q(x(P))`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Proposition 1.2.1 and Theorem 3.1.4.
-/

public section

open Polynomial

namespace TauCeti

namespace Place

universe u v

variable {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F] [Algebra (RatFunc k) F]
  [IsScalarTower k (RatFunc k) F] [Algebra.IsIntegral (RatFunc k) F] {x : F} {q : k[X]}

/-- **Poles of `x` lie over `t = ∞`**: if `t = q(x)` for a polynomial `q`, then `x` is regular at
every place of `F` that does not lie over the place `t = ∞` of `k(t)`. -/
theorem mem_integers_of_restrict_ne_infty (hq : algebraMap (RatFunc k) F RatFunc.X = aeval x q)
    {P' : Place k F} (hP : P'.restrict k (RatFunc k) ≠ infty k) : x ∈ P'.integers := by
  have hX : (RatFunc.X : RatFunc k) ∈ (P'.restrict k (RatFunc k)).integers :=
    not_not.mp (X_notMem_integers_iff_eq_infty.not.mpr hP)
  -- `t` is regular at `P'`, so `x` is a root of `q(X) - t`, a polynomial over the valuation ring
  -- of `P'` whose leading coefficient is the nonzero constant `lc(q)`.
  set a := algebraMap (RatFunc k) F RatFunc.X
  have ha : a ∈ P'.integers := (mem_integers_restrict_iff k (RatFunc k) P' _).mp hX
  have hdeg := natDegree_pos_of_aeval_eq hq
  have hq0 : q ≠ 0 := ne_zero_of_natDegree_gt hdeg
  let p : P'.integers[X] := q.map (algebraMap k P'.integers) - C ⟨a, ha⟩
  have hp : aeval x p = 0 := by
    simp [p, aeval_map_algebraMap, a, hq]
  have hlc : p.leadingCoeff = algebraMap k P'.integers q.leadingCoeff := by
    rw [leadingCoeff_sub_of_degree_lt, leadingCoeff_map]
    rw [degree_map_eq_of_injective (algebraMap k P'.integers).injective, degree_eq_natDegree hq0]
    exact degree_C_le.trans_lt (mod_cast hdeg)
  have hint := isIntegral_leadingCoeff_smul p x hp
  rw [hlc, algebraMap_smul] at hint
  refine P'.mem_integers_of_isIntegral (R := P'.integers) (fun r ↦ r.2) ?_
  convert (isIntegral_algebraMap (R := P'.integers) (x := algebraMap k P'.integers
    q.leadingCoeff⁻¹)).mul hint using 1
  rw [← IsScalarTower.algebraMap_apply, Algebra.smul_def, ← mul_assoc, ← map_mul,
    inv_mul_cancel₀ (leadingCoeff_ne_zero.mpr hq0), map_one, one_mul]

/-- **The place of `k(t)` under a place where `q(x)` takes the value `c`**: if `t = q(x)` for a
polynomial `q`, and `x` is regular at a place `P'` of `F` with `q(x(P')) = c`, then `P'` lies over
the place `t = c` of `k(t)`. -/
theorem restrict_eq_adicOfIrreducible_X_sub_C_of_aeval_residue_eq
    (hq : algebraMap (RatFunc k) F RatFunc.X = aeval x q) {P' : Place k F}
    (hx : x ∈ P'.integers) {c : k}
    (hc : aeval (IsLocalRing.residue P'.integers ⟨x, hx⟩) q = algebraMap k P'.ResidueField c) :
    P'.restrict k (RatFunc k) = adicOfIrreducible (irreducible_X_sub_C c) := by
  -- `t - c` vanishes at `P'`, so `X - c` has positive order at the place under `P'`.
  have h0 : IsLocalRing.residue P'.integers (aeval ⟨x, hx⟩ q - algebraMap k P'.integers c) = 0 := by
    rw [map_sub, residue_aeval, hc, ← IsLocalRing.ResidueField.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply, sub_self]
  have hX : RatFunc.X - RatFunc.C c ≠ (0 : RatFunc k) := by
    rw [← RatFunc.algebraMap_X, ← RatFunc.algebraMap_C, ← map_sub]
    exact (map_ne_zero_iff _ (IsFractionRing.injective k[X] (RatFunc k))).mpr (X_sub_C_ne_zero c)
  have hsub : algebraMap (RatFunc k) F (RatFunc.X - RatFunc.C c) =
      ((aeval ⟨x, hx⟩ q - algebraMap k P'.integers c : P'.integers) : F) := by
    rw [map_sub, hq, ← RatFunc.algebraMap_eq_C, ← IsScalarTower.algebraMap_apply,
      AddSubgroupClass.coe_sub, coe_aeval_integers]
    exact congrArg _ (IsScalarTower.algebraMap_apply k P'.integers F c)
  rw [residue_eq_zero_iff_valuation_lt_one, ← hsub, valuation_algebraMap_restrict k (RatFunc k) P',
    pow_lt_one_iff (ramificationIdx_pos (RatFunc k) P').ne',
    valuation_lt_one_iff_ord_pos _ hX] at h0
  exact ord_X_sub_C_pos_iff.mp h0

end Place

end TauCeti
