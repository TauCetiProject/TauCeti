/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Belyi.Basic
public import TauCeti.FieldTheory.FunctionField.ConstantExtension.Basic
public import TauCeti.FieldTheory.FunctionField.ConstantExtension.Transcendental
import TauCeti.FieldTheory.FunctionField.Place.RatFunc.Order
import TauCeti.FieldTheory.RatFunc.Transcendental
import TauCeti.FieldTheory.Separable.Regular

/-!
# Base change of algebraic Belyi pairs

Let `F / k(t)` be a function field over the rational function field over a field `k` of
characteristic zero, and let `k' / k` be any field extension, algebraic or transcendental (such as
`ℂ` over a number field). The **base change** of `F` to `k'` is a compositum `F' = F · k'`,
regarded as a field over `k'(t)` through the same function `t`. When `k` is the exact constant
field of `F`, `F'` is the fraction field of `F ⊗[k] k'`, i.e. the function field of the base
change of the curve of `F` to `k'`, with the base change of the map to the projective line.

This file shows that `F'` is an algebraic Belyi pair over `k'` exactly when `F` is one over `k`,
provided `k` is the exact constant field of `F`
(`TauCeti.isAlgebraicBelyiPair_iff_of_constantCompositum_eq_top`). No algebraicity hypothesis on
`k' / k` is required.

Three properties are compared across arbitrary constant extensions:
* Exactness of the constant field passes from `F` to `F'`
  (`IsIntegrallyClosedIn.of_constantCompositum_eq_top_of_transcendental`); in the other direction
  it is a hypothesis, since for `k' ≠ k` the field `F = k'(t)` is its own compositum with `k'` and
  is an algebraic Belyi pair over `k'`, while its constants over `k` contain `k'`.
* Places `Q'` of `F' / k'` split into two kinds according to whether their restriction to `F` is
  nontrivial (`ramificationIdx F Q' ≠ 0`) or trivial (`ramificationIdx F Q' = 0`). Places trivial
  on `F` avoid `0, 1, ∞` (`TauCeti.Place.restrict_notMem_zeroOneInfty_of_ramificationIdx_eq_zero`)
  and are unramified (`TauCeti.Place.ramificationIdx_ratFunc_eq_one_of_ramificationIdx_eq_zero`).
* Places nontrivial on `F` restrict to places of `F / k` with the same ramification index over
  `k(t)` (`TauCeti.Place.ramificationIdx_ratFunc_eq_of_ramificationIdx_ne_zero`) and match the
  three marked fibres (`TauCeti.Place.restrictOfRamificationIdxNeZero_restrict_eq_markedPlace_iff`
  and `TauCeti.Place.restrictOfRamificationIdxNeZero_restrict_mem_zeroOneInfty_iff`). Conversely,
  every place of `F / k` lifts to a place of `F' / k'` nontrivial on `F`
  (`TauCeti.Place.exists_restrictOfRamificationIdxNeZero_eq`).

## Main results

* `TauCeti.Place.restrictOfRamificationIdxNeZero_restrict_eq_markedPlace_iff` and
  `TauCeti.Place.restrict_restrict_eq_markedPlace_iff`: base change matches the places over each
  marked place.
* `TauCeti.Place.restrictOfRamificationIdxNeZero_restrict_mem_zeroOneInfty_iff` and
  `TauCeti.Place.restrict_restrict_mem_zeroOneInfty_iff`: base change matches the places over the
  marked places.
* `TauCeti.Place.restrict_notMem_zeroOneInfty_of_ramificationIdx_eq_zero`: places of `F' / k'`
  trivial on `F` do not lie over `0, 1, ∞`.
* `TauCeti.Place.ramificationIdx_ratFunc_eq_of_restrict_eq_markedPlace`: at each marked fibre,
  base change preserves ramification indices over any perfect constant field.
* `TauCeti.isAlgebraicBelyiPair_iff_of_constantCompositum_eq_top`: the base change of `F` to `k'`
  is an algebraic Belyi pair over `k'` exactly when `F` is one over `k`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section III.6.
* B. Köck, *Belyi's theorem revisited*, Beiträge zur Algebra und Geometrie 45 (2004), 253–265.
-/

public section

open Polynomial
open scoped IntermediateField TensorProduct

namespace TauCeti

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F']
  [Algebra F F'] [IsScalarTower k k' F'] [IsScalarTower k F F']
  [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
  [Algebra (RatFunc k') F'] [IsScalarTower k' (RatFunc k') F']

namespace Place

section Integral

variable [Algebra.IsIntegral (RatFunc k) F] [Algebra.IsIntegral (RatFunc k') F']

/-- Under base change, a function of `k(t)` and one of `k'(t)` with the same image in `F'` have a
zero at the places below `Q'` together, when `Q'` is nontrivial on `F`. -/
private theorem ord_restrictOfRamificationIdxNeZero_restrict_pos_iff (Q' : Place k' F')
    (h : ramificationIdx F Q' ≠ 0) {f : RatFunc k} {f' : RatFunc k'}
    (hf : algebraMap F F' (algebraMap (RatFunc k) F f) = algebraMap (RatFunc k') F' f') :
    0 < ((Q'.restrictOfRamificationIdxNeZero k h).restrict k (RatFunc k)).ord f ↔
      0 < (Q'.restrict k' (RatFunc k')).ord f' := by
  rw [← ord_algebraMap_pos_iff k' (RatFunc k') Q', ← hf,
    ord_algebraMap_restrictOfRamificationIdxNeZero (k := k) Q' h,
    mul_pos_iff_of_pos_left (by exact_mod_cast Nat.pos_of_ne_zero h),
    ord_algebraMap_pos_iff k (RatFunc k)]

/-- **Base change keeps each marked fibre** for places nontrivial on `F`: if `t` acts on `F'` as
it does on `F`, then a place `Q'` of `F'` with `e(Q' ∣ F) ≠ 0` lies over the marked place of
`k'(t)` numbered `i` exactly when the place of `F` below it lies over the marked place of `k(t)`
numbered `i`. -/
theorem restrictOfRamificationIdxNeZero_restrict_eq_markedPlace_iff
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X)
    (Q' : Place k' F') (h : ramificationIdx F Q' ≠ 0) (i : Fin 3) :
    (Q'.restrictOfRamificationIdxNeZero k h).restrict k (RatFunc k) = markedPlace k i ↔
      Q'.restrict k' (RatFunc k') = markedPlace k' i := by
  fin_cases i
  · simp only [Fin.zero_eta, markedPlace_zero, ← ord_X_pos_iff]
    exact ord_restrictOfRamificationIdxNeZero_restrict_pos_iff Q' h hX
  · simp only [Fin.mk_one, markedPlace_one, ← ord_X_sub_C_pos_iff]
    exact ord_restrictOfRamificationIdxNeZero_restrict_pos_iff Q' h
      (by simp only [map_one, map_sub, hX])
  · simp only [Fin.reduceFinMk, markedPlace_two, ← X_notMem_integers_iff_eq_infty]
    rw [mem_integers_restrict_iff k (RatFunc k),
      mem_integers_restrictOfRamificationIdxNeZero_iff,
      mem_integers_restrict_iff k' (RatFunc k'), hX]

/-- **Base change matches the marked places** for places nontrivial on `F`. -/
theorem restrictOfRamificationIdxNeZero_restrict_mem_zeroOneInfty_iff
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X)
    (Q' : Place k' F') (h : ramificationIdx F Q' ≠ 0) :
    (Q'.restrictOfRamificationIdxNeZero k h).restrict k (RatFunc k) ∈ zeroOneInfty k ↔
      Q'.restrict k' (RatFunc k') ∈ zeroOneInfty k' := by
  simp only [← range_markedPlace, Set.mem_range, eq_comm (b := Place.restrict _ _ _),
    restrictOfRamificationIdxNeZero_restrict_eq_markedPlace_iff hX Q' h]

omit [Algebra k k'] [Algebra k F] [Algebra k F'] [IsScalarTower k k' F'] [IsScalarTower k F F']
  [IsScalarTower k (RatFunc k) F] [Algebra.IsIntegral (RatFunc k) F] in
/-- **Places trivial on `F` avoid the marked fibres `0, 1, ∞`**: if `t` acts on `F'` as it does
on `F` and `Q'` is trivial on `F`, then `t` and `t - 1` are units at `Q'`, so `Q'` cannot lie over
`t = 0`, `t = 1`, or `t = ∞`. -/
theorem restrict_notMem_zeroOneInfty_of_ramificationIdx_eq_zero
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X)
    {Q' : Place k' F'} (h : ramificationIdx F Q' = 0) :
    Q'.restrict k' (RatFunc k') ∉ zeroOneInfty k' := by
  have hord0 := ord_algebraMap_eq_zero_of_ramificationIdx_eq_zero h
  rw [← range_markedPlace]
  rintro ⟨i, hi⟩
  fin_cases i
  · have hpos : 0 < Q'.ord (algebraMap (RatFunc k') F' RatFunc.X) := by
      rw [ord_algebraMap_pos_iff k' (RatFunc k'), ord_X_pos_iff]
      exact hi.symm.trans markedPlace_zero
    rw [← hX, hord0] at hpos
    omega
  · have hpos : 0 < Q'.ord (algebraMap (RatFunc k') F' (RatFunc.X - RatFunc.C 1)) := by
      rw [ord_algebraMap_pos_iff k' (RatFunc k'), ord_X_sub_C_pos_iff]
      exact hi.symm.trans markedPlace_one
    have hX1 : algebraMap F F' (algebraMap (RatFunc k) F (RatFunc.X - RatFunc.C 1)) =
        algebraMap (RatFunc k') F' (RatFunc.X - RatFunc.C 1) := by
      simp only [map_sub, map_one, hX]
    rw [← hX1, hord0] at hpos
    omega
  · have hnot : RatFunc.X ∉ (Q'.restrict k' (RatFunc k')).integers :=
      X_notMem_integers_iff_eq_infty.mpr (hi.symm.trans markedPlace_two)
    rw [mem_integers_restrict_iff k' (RatFunc k'), ← hX, mem_integers_iff_ord_nonneg,
      hord0] at hnot
    exact hnot le_rfl

/-- **Base change keeps each marked fibre** in an integral extension `F' / F`. -/
theorem restrict_restrict_eq_markedPlace_iff [Algebra.IsIntegral F F']
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X) (Q' : Place k' F') (i : Fin 3) :
    (Q'.restrict k F).restrict k (RatFunc k) = markedPlace k i ↔
      Q'.restrict k' (RatFunc k') = markedPlace k' i := by
  have hne : ramificationIdx F Q' ≠ 0 := (ramificationIdx_pos F Q').ne'
  simpa only [restrictOfRamificationIdxNeZero_eq_restrict] using
    restrictOfRamificationIdxNeZero_restrict_eq_markedPlace_iff hX Q' hne i

/-- **Base change matches the marked places** in an integral extension `F' / F`. -/
theorem restrict_restrict_mem_zeroOneInfty_iff [Algebra.IsIntegral F F']
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X) (Q' : Place k' F') :
    (Q'.restrict k F).restrict k (RatFunc k) ∈ zeroOneInfty k ↔
      Q'.restrict k' (RatFunc k') ∈ zeroOneInfty k' := by
  simp only [← range_markedPlace, Set.mem_range, eq_comm (b := Place.restrict _ _ _),
    restrict_restrict_eq_markedPlace_iff hX]

/-- **At each marked fibre, base change preserves ramification indices** over any perfect constant
field `k`, without requiring `F / k(t)` to be separable: any place over a marked point is
nontrivial on `F`, so `ramificationIdx_ratFunc_eq_of_ramificationIdx_ne_zero` applies. -/
theorem ramificationIdx_ratFunc_eq_of_restrict_eq_markedPlace [PerfectField k]
    (hF : IsFunctionField k F) (hcomp : constantCompositum F k' F' = ⊤)
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X)
    {Q' : Place k' F'} {i : Fin 3} (hi : Q'.restrict k' (RatFunc k') = markedPlace k' i) :
    have hne : ramificationIdx F Q' ≠ 0 := fun h0 ↦
      restrict_notMem_zeroOneInfty_of_ramificationIdx_eq_zero hX h0
        (hi ▸ range_markedPlace k' ▸ ⟨i, rfl⟩)
    ramificationIdx (RatFunc k') Q' =
      ramificationIdx (RatFunc k) (Q'.restrictOfRamificationIdxNeZero k hne) :=
  ramificationIdx_ratFunc_eq_of_ramificationIdx_ne_zero hF hcomp hX _

end Integral

end Place

variable [CharZero k] [FiniteDimensional (RatFunc k) F] [FiniteDimensional (RatFunc k') F']

open Place in
/-- **Base change of algebraic Belyi pairs**: let `F / k(t)` have exact constant field `k`, of
characteristic zero, and let `F' = F · k'` be its compositum with any extension `k' / k` (algebraic
or transcendental), with `t` acting on `F'` as it does on `F`. Then `F' / k'(t)` is an algebraic
Belyi pair over `k'` exactly when `F / k(t)` is one over `k`. -/
theorem isAlgebraicBelyiPair_iff_of_constantCompositum_eq_top [CharZero k']
    (hex : IsIntegrallyClosedIn k F) (hcomp : constantCompositum F k' F' = ⊤)
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X) :
    IsAlgebraicBelyiPair k' F' ↔ IsAlgebraicBelyiPair k F := by
  have hF : IsFunctionField k F := (IsFunctionField.ratFunc k).finite_extension
  let t : F := algebraMap (RatFunc k) F RatFunc.X
  have ht : Transcendental k t :=
    (transcendental_algebraMap_iff (algebraMap (RatFunc k) F).injective).mpr
      RatFunc.transcendental_X
  have ht' : Transcendental k' (algebraMap F F' t) := by
    change Transcendental k' (algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X))
    rw [hX]
    exact (transcendental_algebraMap_iff (algebraMap (RatFunc k') F').injective).mpr
      RatFunc.transcendental_X
  have : FiniteDimensional k⟮t⟯ F := hF.finiteDimensional_adjoin ht
  have : Algebra.IsSeparable k⟮t⟯ F := isSeparable_adjoin_algebraMap_X_iff.mpr inferInstance
  have : Algebra.IsGeometricallyReduced k F := isGeometricallyReduced_of_separating ht
  have : IsDomain (F ⊗[k] k') := isDomain_tensorProduct_of_isGeometricallyReduced hex k'
  have hld : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F :=
    linearDisjoint_of_constantCompositum_eq_top_of_transcendental ht' hcomp
  refine ⟨fun h' ↦ ⟨hex, fun {Q} hQ ↦ ?_⟩, fun h ↦
    ⟨.of_constantCompositum_eq_top_of_transcendental hex ht' hcomp, fun {Q'} hQ' ↦ ?_⟩⟩
  · obtain ⟨Q', hne, rfl⟩ := exists_restrictOfRamificationIdxNeZero_eq hF hld hcomp Q
    rw [← ramificationIdx_ratFunc_eq_of_ramificationIdx_ne_zero hF hcomp hX hne]
    exact h'.ramificationIdx_eq_one
      ((restrictOfRamificationIdxNeZero_restrict_mem_zeroOneInfty_iff hX Q' hne).not.mp hQ)
  · rcases eq_or_ne (ramificationIdx F Q') 0 with h0 | hne
    · exact ramificationIdx_ratFunc_eq_one_of_ramificationIdx_eq_zero hcomp hX h0
    · rw [ramificationIdx_ratFunc_eq_of_ramificationIdx_ne_zero hF hcomp hX hne]
      exact h.ramificationIdx_eq_one
        ((restrictOfRamificationIdxNeZero_restrict_mem_zeroOneInfty_iff hX Q' hne).not.mpr hQ')

end TauCeti
