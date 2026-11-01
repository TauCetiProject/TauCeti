/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Belyi.Basic
public import TauCeti.FieldTheory.FunctionField.ConstantExtension.Basic
import TauCeti.FieldTheory.FunctionField.ConstantExtension.Algebraic
import TauCeti.FieldTheory.FunctionField.ConstantExtension.Basis
import TauCeti.FieldTheory.FunctionField.ConstantExtension.Ramification
import TauCeti.FieldTheory.FunctionField.Place.Extension.Existence

/-!
# Base change of algebraic Belyi pairs

Let `F / k(t)` be a function field over the rational function field over a field `k` of
characteristic zero, and let `k' / k` be an algebraic extension, finite or not, such as an
algebraic closure of `k`. The **base change** of `F` to `k'` is the compositum `F' = F · k'`,
regarded as a field over `k'(t)` through the same function `t`. It is the function field of the
base change of the curve of `F` to `k'`, with the base change of the map to the projective line.

This file shows that `F'` is an algebraic Belyi pair over `k'` exactly when `F` is one over `k`,
provided `k` is the exact constant field of `F`
(`TauCeti.isAlgebraicBelyiPair_iff_of_constantCompositum_eq_top`). Its degree is unchanged
(`TauCeti.finrank_ratFunc_eq_of_constantCompositum_eq_top`), and `F'` is finite over `k'(t)` as
soon as `F` is finite over `k(t)`
(`TauCeti.finiteDimensional_ratFunc_of_constantCompositum_eq_top`).

Three properties are compared. Exactness of the constant field passes from `F` to `F'`
(`IsIntegrallyClosedIn.of_constantCompositum_eq_top`); in the other direction it is a hypothesis.
For a finite extension `k' ≠ k`, the field `F = k'(t)` is its own compositum with `k'`, and is an
algebraic Belyi pair over `k'`, but its constants over `k` are all of `k'`. Ramification over
`k(t)` does not change under extension of the constants
(`TauCeti.Place.ramificationIdx_ratFunc_eq_of_constantCompositum_eq_top`). Finally the three
marked places correspond: a place of `F'` lies over one of `t = 0`, `t = 1`, `t = ∞` of `k'(t)`
exactly when the place of `F` below it lies over one of the marked places of `k(t)`
(`TauCeti.Place.restrict_restrict_mem_zeroOneInfty_iff_of_constantCompositum_eq_top`), because
the marked places are the zeros and poles of `t` and `t - 1`, whose orders do not change either.
In the descending direction every place of `F` has a place of `F'` above it, `F'` being a
function field algebraic over `F`.

The ascending direction carries a Belyi map defined over a number field to one over an algebraic
closure. The descending direction shows that a model of a Belyi map over a smaller field, as
produced by descent, is again unramified outside `0`, `1` and `∞`.

## Main results

* `TauCeti.Place.restrict_restrict_mem_zeroOneInfty_iff_of_constantCompositum_eq_top`: base change
  matches the places over the marked places.
* `TauCeti.isAlgebraicBelyiPair_iff_of_constantCompositum_eq_top`: the base change of `F` to `k'`
  is an algebraic Belyi pair exactly when `F` is.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section III.6.
* B. Köck, *Belyi's theorem revisited*, Beiträge zur Algebra und Geometrie 45 (2004), 253–265.
-/

public section

open Polynomial

namespace TauCeti

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F'] [CharZero k]
  [Algebra k k'] [Algebra.IsAlgebraic k k'] [Algebra k F] [Algebra k F'] [Algebra k' F']
  [Algebra F F'] [IsScalarTower k k' F'] [IsScalarTower k F F']
  [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
  [Algebra (RatFunc k') F'] [IsScalarTower k' (RatFunc k') F'] [FiniteDimensional (RatFunc k') F']

namespace Place

/-- **Base change matches the marked places**: if `F' = F · k'` and `t` acts on `F'` as it does
on `F`, then a place `Q'` of `F'` lies over one of the marked places `t = 0`, `t = 1`, `t = ∞` of
`k'(t)` exactly when the place of `F` below it lies over one of those of `k(t)`. -/
theorem restrict_restrict_mem_zeroOneInfty_iff_of_constantCompositum_eq_top
    [Algebra.IsIntegral F F'] (hcomp : constantCompositum F k' F' = ⊤)
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X) (Q' : Place k' F') :
    (Q'.restrict k F).restrict k (RatFunc k) ∈ zeroOneInfty k ↔
      Q'.restrict k' (RatFunc k') ∈ zeroOneInfty k' := by
  have h₀ := ord_restrict_algebraMap_eq_of_constantCompositum_eq_top hcomp hX Q' X
  have h₁ := ord_restrict_algebraMap_eq_of_constantCompositum_eq_top hcomp hX Q' (X - 1)
  simp only [Polynomial.map_X, Polynomial.map_sub, Polynomial.map_one, map_sub, map_one,
    RatFunc.algebraMap_X] at h₀ h₁
  rw [← not_iff_not, notMem_zeroOneInfty_iff, notMem_zeroOneInfty_iff, h₀, h₁]

end Place

open Place in
/-- **Base change of algebraic Belyi pairs**: let `F / k(t)` have exact constant field `k`, of
characteristic zero, and let `F' = F · k'` be its compositum with an algebraic extension `k' / k`,
with `t` acting on `F'` as it does on `F`. Then `F' / k'(t)` is an algebraic Belyi pair exactly
when `F / k(t)` is. -/
theorem isAlgebraicBelyiPair_iff_of_constantCompositum_eq_top [CharZero k']
    (hex : IsIntegrallyClosedIn k F) (hcomp : constantCompositum F k' F' = ⊤)
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X) :
    IsAlgebraicBelyiPair k' F' ↔ IsAlgebraicBelyiPair k F := by
  have : Algebra.IsIntegral F F' :=
    (isAlgebraic_of_constantCompositum_eq_top (k := k) hcomp).isIntegral
  have hmark := restrict_restrict_mem_zeroOneInfty_iff_of_constantCompositum_eq_top hcomp hX
  have he := ramificationIdx_ratFunc_eq_of_constantCompositum_eq_top hcomp hX
  refine ⟨fun h' ↦ ⟨hex, fun {Q} hQ ↦ ?_⟩,
    fun h ↦ ⟨.of_constantCompositum_eq_top hex hcomp, fun {Q'} hQ' ↦ ?_⟩⟩
  · -- every place of `F` lies under a place of the function field `F'`
    obtain ⟨Q', rfl⟩ := restrict_surjective (k := k) (F := F)
      (isFunctionField_iff_functionField.mpr (inferInstance : FunctionField k' F')) Q
    rw [← he]
    exact h'.ramificationIdx_eq_one ((hmark Q').not.mp hQ)
  · rw [he]
    exact h.ramificationIdx_eq_one ((hmark Q').not.mpr hQ')

end TauCeti
