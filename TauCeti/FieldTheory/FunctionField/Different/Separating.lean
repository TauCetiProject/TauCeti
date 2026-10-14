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
import TauCeti.FieldTheory.FunctionField.Different.Tame
import TauCeti.FieldTheory.FunctionField.Place.Extension.Existence

/-!
# Translates of a separating element are almost always prime elements

Let `F / k` be an algebraic function field and `x` a separating element, so that `F / k(x)` is a
finite separable extension. Only finitely many places of `F` ramify over `k(x)`
(`TauCeti.Place.finite_setOf_differentExponent_ne_zero`). A rational place `P` of `F` that is not
a pole of `x` lies over a rational finite place of `k(x)`, the zero of `X - a` for some `a ∈ k`;
if `P` is unramified there, `x - a` is a prime element at `P`. A place of arbitrary degree that
is not a pole of `x` lies over the zero of some irreducible `q ∈ k[X]`, and if it is unramified
there, `q(x)` is a prime element.

An unramified place has a separable residue extension over the place below it. Over an infinite
field `k` there are infinitely many rational places `X - a` of `k(x)`, and the places of `F` above
all but finitely many of them are unramified, so their residue fields are separable over `k`. Over
a finite field every residue field is separable. Either way a separably generated function field
has infinitely many places with residue field separable over `k`, even when `k` is imperfect and
`F` has only finitely many rational places.

## Main results

* `TauCeti.Place.finite_setOf_forall_ord_sub_algebraMap_ne_one`: at all but finitely many rational
  places that are not poles of a separating `x`, some `x - a` is a prime element.
* `TauCeti.Place.finite_setOf_forall_irreducible_ord_aeval_ne_one`: at all but finitely many places
  that are not poles of a separating `x`, some `q(x)` with `q` irreducible is a prime element.
* `TauCeti.Place.infinite_setOf_isSeparable_residueField`: if `F / k` has a separating element,
  infinitely many places of `F` have residue field separable over `k`.
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

/-- **Almost every place has a prime element `q(x)`**: for a separating element `x`, only finitely
many places `P` with `ord_P x ≥ 0` admit no irreducible `q ∈ k[X]` with `ord_P q(x) = 1`. -/
theorem finite_setOf_forall_irreducible_ord_aeval_ne_one (hF : IsFunctionField k F) {x : F}
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F] :
    {P : Place k F | 0 ≤ P.ord x ∧
      ∀ q : Polynomial k, Irreducible q → P.ord (Polynomial.aeval x q) ≠ 1}.Finite := by
  let _ := ratFuncAlgebraOfTranscendental hx
  let _ := isScalarTower_ratFuncAlgebraOfTranscendental hx
  let _ := isFunctionField_iff_functionField.mp hF
  let _ := isSeparable_ratFuncAlgebraOfTranscendental hx
  have hX := algebraMap_ratFuncAlgebraOfTranscendental_X hx
  refine (finite_setOf_differentExponent_ne_zero (k' := k) (F' := F) k (RatFunc k)
    (IsFunctionField.ratFunc k)).subset fun P ⟨hx0, hne⟩ ↦ ?_
  refine (differentExponent_pos_of_one_lt_ramificationIdx k (RatFunc k) P ?_).ne'
  refine lt_of_le_of_ne (ramificationIdx_pos (RatFunc k) P) fun he ↦ ?_
  rcases eq_infty_or_exists_eq_adicOfIrreducible (P.restrict k (RatFunc k)) with h | ⟨q, hq, h⟩
  · -- `x` would have a pole at `P`, lying over the pole of `X`.
    rw [← hX, ord_algebraMap_restrict k (RatFunc k) P, h, ord_infty, RatFunc.intDegree_X,
      ← he] at hx0
    omega
  · -- `q(x)` is a prime element at `P`, lying unramified over the zero of `q`.
    classical
    refine hne q hq ?_
    rw [← hX, Polynomial.aeval_algebraMap_apply, RatFunc.aeval_X_left_eq_algebraMap,
      ord_algebraMap_restrict k (RatFunc k) P, h,
      ord_adicOfIrreducible_algebraMap_irreducible hq hq, ite_eq_left (Associated.refl _), ← he,
      Nat.cast_one, mul_one]

/-- **Infinitely many places have a separable residue field**: if `F / k` has a separating element
`x`, then infinitely many places of `F` have residue field separable over `k`. Over an infinite
field these include the places above all but finitely many rational places `X - a` of `k(x)`, where
`F / k(x)` is unramified; over a finite field every place qualifies. -/
theorem infinite_setOf_isSeparable_residueField (hF : IsFunctionField k F) {x : F}
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F] :
    {P : Place k F | Algebra.IsSeparable k P.ResidueField}.Infinite := by
  rcases finite_or_infinite k with hk | hk
  · -- A finite field is perfect, so every residue field is separable over it.
    have := infinite hF
    simpa [isSeparable_residueField_of_perfectField _ hF] using Set.infinite_univ (α := Place k F)
  let _ := ratFuncAlgebraOfTranscendental hx
  let _ := isScalarTower_ratFuncAlgebraOfTranscendental hx
  let _ := isFunctionField_iff_functionField.mp hF
  let _ := isSeparable_ratFuncAlgebraOfTranscendental hx
  -- Choose a place `P a` of `F` above the rational place `X - a` of `k(x)`, for each `a ∈ k`.
  choose P hP using fun a : k ↦ restrict_surjective (k := k) (F := RatFunc k) hF
    (adicOfIrreducible (Polynomial.irreducible_X_sub_C a))
  replace hP (a : k) :
      (P a).restrict k (RatFunc k) = adicOfIrreducible (Polynomial.irreducible_X_sub_C a) :=
    hP a
  have hinj : Function.Injective P := fun a b h ↦ adicOfIrreducible_X_sub_C_injective (by
    simp only
    rw [← hP a, ← hP b, h])
  refine ((Set.infinite_range_of_injective hinj).sdiff (finite_setOf_differentExponent_ne_zero
    (k' := k) (F' := F) k (RatFunc k) (IsFunctionField.ratFunc k))).mono ?_
  rintro _ ⟨⟨a, rfl⟩, hd⟩
  simp only [Set.mem_ofPred_eq, not_not] at hd
  -- `P a` is unramified over `X - a`, hence tame, so its residue extension is separable.
  have hle := ramificationIdx_le_differentExponent_add_one k (RatFunc k) (P a)
  have hpos := ramificationIdx_pos (RatFunc k) (P a)
  have htame := (ramificationIdx_eq_differentExponent_add_one_iff k (RatFunc k) (P a)).mp
    (by omega)
  have := ((isTame_iff_isSeparable_residueField k (RatFunc k) (P a)).mp htame).1
  -- The residue field of `X - a` is `k`.
  have := ((P a).restrict k (RatFunc k)).isSeparable_residueField_of_degree_eq_one
    (by rw [hP a]; exact degree_adicOfIrreducible_X_sub_C a)
  exact Algebra.IsSeparable.trans k ((P a).restrict k (RatFunc k)).ResidueField (P a).ResidueField

end Place

end TauCeti
