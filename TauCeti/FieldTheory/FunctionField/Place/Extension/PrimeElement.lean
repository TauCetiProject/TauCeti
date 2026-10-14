/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Degree
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Basic

/-!
# Prime elements at a rational place above

Let `F' / F` be an integral extension, with `F` a field over `k` and `F'` a field over `k'`, and
let `P'` be a rational place of `F' / k'` lying over the place `P` of `F / k` with
`e(P' ∣ P) = 1`.  A prime element of `P` of the form `q(z)`, with `q` separable over `k` and `z`
regular at `P`, yields the prime element `z - a` of `P'`, where `a` is the value of `z` at `P'`.

## Main results

* `TauCeti.Place.exists_ord_sub_algebraMap_eq_one_of_ord_aeval_eq_one`: at a rational place `P'`
  unramified over `P`, a prime element `q(z)` of `P` with `q` separable yields a prime element
  `z - a` of `P'`.
-/

public section

namespace TauCeti

namespace Place

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']

open _root_.Polynomial in
/-- **A prime element `q(z)` below gives a prime element `z - a` at a rational place above**: at a
rational place `P'` of `F'` over a place `P` of `F` with `e(P' ∣ P) = 1`, a prime element `q(z)` of
`P`, with `q` separable over `k` and `z` regular at `P`, gives a prime element `z - a` of `P'` for
some constant `a`, namely the value of `z` at `P'`, which is a simple root of `q`. -/
theorem exists_ord_sub_algebraMap_eq_one_of_ord_aeval_eq_one [Algebra.IsIntegral F F']
    {P' : Place k' F'} (hdeg : P'.degree = 1) (he : P'.ramificationIdx F = 1) {z : F}
    (hz : 0 ≤ (P'.restrict k F).ord z) {q : Polynomial k} (hq : q.Separable)
    (hqz : (P'.restrict k F).ord (Polynomial.aeval z q) = 1) :
    ∃ a : k', P'.ord (algebraMap F F' z - algebraMap k' F' a) = 1 := by
  set z' := algebraMap F F' z
  have hzint : z' ∈ P'.integers := (mem_integers_restrict_iff k F P' z).mp
    ((P'.restrict k F).mem_integers_iff_ord_nonneg.mpr hz)
  obtain ⟨a, ha⟩ := (degree_eq_one_iff_forall_exists_valuation_sub_lt_one P').mp hdeg z' hzint
  refine ⟨a, ?_⟩
  -- `Q(z')`, with `Q` the image of `q` over `k'`, is a prime element of `P'`.
  set Q := q.map (algebraMap k k')
  have hQz : P'.ord (aeval z' Q) = 1 := by
    rw [aeval_map_algebraMap, aeval_algebraMap_apply, ord_algebraMap_restrict k F P', he, hqz]
    simp
  have hord_eq_zero {w : F'} (hw : P'.valuation w = 1) : P'.ord w = 0 := by
    rw [ord_def, hw, WithZero.log_one, neg_zero]
  -- `a` is a root of `Q`, simple because `Q` is separable, so `Q = (X - a) R` with `R(a) ≠ 0`.
  have hQa : Q.eval a = 0 := by
    by_contra hne
    rw [hord_eq_zero (valuation_aeval_eq_one_of_valuation_sub_lt_one ha hne)] at hQz
    exact zero_ne_one hQz
  set R := Q /ₘ (X - C a)
  have hQR : (X - C a) * R = Q := mul_divByMonic_eq_iff_isRoot.mpr hQa
  have hRa : R.eval a ≠ 0 := by
    have hsep : Q.Separable := hq.map
    have hder := hsep.aeval_derivative_ne_zero (x := a) (by rwa [coe_aeval_eq_eval])
    rw [coe_aeval_eq_eval] at hder
    rw [← hQR] at hder
    simpa using hder
  -- So `ord (z' - a) = ord Q(z') - ord R(z') = 1 - 0`.
  have hRz := hord_eq_zero (valuation_aeval_eq_one_of_valuation_sub_lt_one ha hRa)
  have hfac : aeval z' Q = (z' - algebraMap k' F' a) * aeval z' R := by
    rw [← hQR, map_mul, map_sub, aeval_X, aeval_C]
  have hne : aeval z' Q ≠ 0 := fun h0 ↦ by rw [h0, ord_zero] at hQz; exact zero_ne_one hQz
  rw [hfac] at hQz hne
  rw [P'.ord_mul (left_ne_zero_of_mul hne) (right_ne_zero_of_mul hne), hRz, add_zero] at hQz
  exact hQz

end Place

end TauCeti
