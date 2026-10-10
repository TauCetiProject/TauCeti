/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Different.Divisor
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Degree
public import TauCeti.FieldTheory.FunctionField.Place.RatFunc.Basic
public import TauCeti.FieldTheory.FunctionField.Place.RatFunc.Order
public import TauCeti.FieldTheory.RatFunc.Transcendental

/-!
# Translates of a separating element are almost always prime elements

Let `F / k` be an algebraic function field and `x` a separating element, so that `F / k(x)` is a
finite separable extension. Only finitely many places of `F` ramify over `k(x)`
(`TauCeti.Place.finite_setOf_differentExponent_ne_zero`). A rational place `P` of `F` that is not
a pole of `x` lies over a rational finite place of `k(x)`, the zero of `X - a` for some `a ∈ k`;
if `P` is unramified there, `x - a` is a prime element at `P`.

## Main results

* `TauCeti.Place.finite_setOf_forall_ord_sub_algebraMap_ne_one`: at all but finitely many rational
  places that are not poles of a separating `x`, some `x - a` is a prime element.
-/

public section

open scoped IntermediateField

namespace TauCeti

namespace Place

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- **Almost every rational place has a translate of `x` as a prime element**: for a separating
element `x`, only finitely many rational places `P` with `ord_P x ≥ 0` admit no constant `a` with
`ord_P (x - a) = 1`. -/
theorem finite_setOf_forall_ord_sub_algebraMap_ne_one (hF : IsFunctionField k F) {x : F}
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F] :
    {P : Place k F | P.degree = 1 ∧ 0 ≤ P.ord x ∧
      ∀ a : k, P.ord (x - algebraMap k F a) ≠ 1}.Finite := by
  let _ := ratFuncAlgebraOfTranscendental hx
  let _ := isScalarTower_ratFuncAlgebraOfTranscendental hx
  let _ := isFunctionField_iff_functionField.mp hF
  let _ := isSeparable_ratFuncAlgebraOfTranscendental hx
  have hX := algebraMap_ratFuncAlgebraOfTranscendental_X hx
  refine (finite_setOf_differentExponent_ne_zero (k' := k) (F' := F) k (RatFunc k)
    (IsFunctionField.ratFunc k)).subset fun P ⟨hP, hx0, hne⟩ ↦ ?_
  refine (differentExponent_pos_of_one_lt_ramificationIdx k (RatFunc k) P ?_).ne'
  refine lt_of_le_of_ne (ramificationIdx_pos (RatFunc k) P) fun he ↦ ?_
  rcases eq_infty_or_exists_eq_adicOfIrreducible_X_sub_C (Nat.eq_one_of_mul_eq_one_right
    (hP ▸ degree_eq_degree_restrict_mul_relativeDegree k (RatFunc k) P).symm) with h | ⟨a, h⟩
  · -- `x` would have a pole at `P`, lying over the pole of `X`.
    rw [← hX, ord_algebraMap_restrict k (RatFunc k) P, h, ord_infty, RatFunc.intDegree_X,
      ← he] at hx0
    omega
  · -- `x - a` is a prime element at `P`, lying unramified over the zero of `X - a`.
    refine hne a ?_
    rw [← hX, IsScalarTower.algebraMap_apply k (RatFunc k) F, RatFunc.algebraMap_eq_C, ← map_sub,
      ord_algebraMap_restrict k (RatFunc k) P, h, ord_adicOfIrreducible_X_sub_C_self, ← he,
      Nat.cast_one, mul_one]

end Place

end TauCeti
