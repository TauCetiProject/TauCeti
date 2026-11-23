/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Belyi.Basic
public import TauCeti.FieldTheory.FunctionField.ConstantExtension.Basic
import TauCeti.FieldTheory.FunctionField.ConstantExtension.Place
import TauCeti.FieldTheory.FunctionField.ConstantExtension.Ramification
import TauCeti.FieldTheory.FunctionField.ConstantExtension.Regular
import TauCeti.FieldTheory.FunctionField.Place.RatFunc.Order
import TauCeti.RingTheory.TensorProduct.Reduced

/-!
# Base change of algebraic Belyi pairs

Let `F / k(t)` be a function field over the rational function field over a field `k` of
characteristic zero, and let `k' / k` be an arbitrary field extension, algebraic or transcendental.
The **base change** of `F` to `k'` is the compositum `F' = F · k'`,
regarded as a field over `k'(t)` through the same function `t`. When `k` is the exact constant
field of `F`, it is the function field of the base change of the curve of `F` to `k'`, with the
base change of the map to the projective line.

This file shows that `F'` is an algebraic Belyi pair over `k'` exactly when `F` is one over `k`,
provided `k` is the exact constant field of `F`
(`TauCeti.isAlgebraicBelyiPair_iff_of_constantCompositum_eq_top`), and descends Belyi pairs across
arbitrary constant extensions under degree equality (`TauCeti.IsAlgebraicBelyiPair.of_finrank_eq`).

Three ingredients enter the comparison:
* Exactness of the constant field passes from `F` to `F'` along the regular extension `F / k`
  (`IsIntegrallyClosedIn.of_constantCompositum_eq_top_of_linearDisjoint`); in the descending
  direction it is either a hypothesis or recovered from degree equality via linear disjointness.
* Places of `F' / k'` that are trivial on `F` are unramified over `k'(t)` and never lie over `0`,
  `1`, or `∞` (`TauCeti.Place.restrict_notMem_zeroOneInfty_of_isTrivialOn`).
* Places of `F' / k'` that are nontrivial on `F` contract to places of `F / k` with the same
  ramification index over `t` and match the three marked places with the same index
  (`TauCeti.Place.restrict_eq_markedPlace_iff_of_integers_comap_eq`,
  `TauCeti.Place.restrict_mem_zeroOneInfty_iff_of_integers_comap_eq`); when `F' / F` is integral,
  every place contracts via `TauCeti.Place.restrict`
  (`TauCeti.Place.restrict_restrict_eq_markedPlace_iff`,
  `TauCeti.Place.restrict_restrict_mem_zeroOneInfty_iff`).

## Main results

* `TauCeti.Place.restrict_notMem_zeroOneInfty_of_isTrivialOn`: a place of `F'` trivial on `F` never
  lies over `0`, `1`, or `∞`.
* `TauCeti.Place.restrict_eq_markedPlace_iff_of_integers_comap_eq` and
  `TauCeti.Place.restrict_mem_zeroOneInfty_iff_of_integers_comap_eq`: places linked by contraction
  of valuation rings match each marked place across arbitrary constant extensions.
* `TauCeti.Place.restrict_restrict_eq_markedPlace_iff` and
  `TauCeti.Place.restrict_restrict_mem_zeroOneInfty_iff`: specializations via `Place.restrict` when
  `F' / F` is integral.
* `TauCeti.isAlgebraicBelyiPair_iff_of_constantCompositum_eq_top`: the base change of `F` to an
  arbitrary extension `k' / k` is an algebraic Belyi pair exactly when `F` is.
* `TauCeti.IsAlgebraicBelyiPair.of_finrank_eq`: degree-preserving descent of an algebraic Belyi
  pair across an arbitrary constant extension.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section III.6.
* B. Köck, *Belyi's theorem revisited*, Beiträge zur Algebra und Geometrie 45 (2004), 253–265.
-/

public section

open Polynomial

namespace TauCeti

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F']
  [Algebra F F'] [IsScalarTower k k' F'] [IsScalarTower k F F']
  [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
  [Algebra (RatFunc k') F'] [IsScalarTower k' (RatFunc k') F']

namespace Place

variable [Algebra.IsIntegral (RatFunc k) F] [Algebra.IsIntegral (RatFunc k') F']

omit [Algebra.IsIntegral (RatFunc k) F] in
/-- **A place of `F'` trivial on `F` never lies over `0`, `1` or `∞`.** -/
theorem restrict_notMem_zeroOneInfty_of_isTrivialOn
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X) {Q' : Place k' F'}
    (hQ' : Q'.valuation.IsTrivialOn F) :
    Q'.restrict k' (RatFunc k') ∉ zeroOneInfty k' := by
  rw [notMem_zeroOneInfty_iff]
  exact ⟨by simpa using ord_restrict_algebraMap_eq_zero_of_isTrivialOn hX hQ' X_ne_zero, by
    simpa [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C] using
      ord_restrict_algebraMap_eq_zero_of_isTrivialOn hX hQ' (X_sub_C_ne_zero (1 : k))⟩

omit [Algebra k k'] [Algebra k F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] in
private theorem ord_restrict_pos_iff_of_integers_comap_eq {Q : Place k F} {Q' : Place k' F'}
    (hQ' : Q'.integers.comap (algebraMap F F') = Q.integers) {f : RatFunc k} {f' : RatFunc k'}
    (h : algebraMap F F' (algebraMap (RatFunc k) F f) = algebraMap (RatFunc k') F' f') :
    0 < (Q.restrict k (RatFunc k)).ord f ↔ 0 < (Q'.restrict k' (RatFunc k')).ord f' := by
  obtain ⟨he_pos, hord⟩ := ramificationIdx_pos_and_ord_algebraMap_eq_of_integers_comap_eq hQ'
  rw [← ord_algebraMap_pos_iff k (RatFunc k) Q, ← ord_algebraMap_pos_iff k' (RatFunc k') Q', ← h,
    hord, mul_pos_iff_of_pos_left (by exact_mod_cast he_pos)]

omit [Algebra k k'] [Algebra k F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] in
/-- **Contracting places preserve each marked fibre across arbitrary constant extensions.** -/
theorem restrict_eq_markedPlace_iff_of_integers_comap_eq
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X) {Q : Place k F} {Q' : Place k' F'}
    (hQ' : Q'.integers.comap (algebraMap F F') = Q.integers) (i : Fin 3) :
    Q.restrict k (RatFunc k) = markedPlace k i ↔
      Q'.restrict k' (RatFunc k') = markedPlace k' i := by
  fin_cases i
  · simp only [Fin.zero_eta, markedPlace_zero, ← ord_X_pos_iff]
    exact ord_restrict_pos_iff_of_integers_comap_eq hQ' hX
  · simp only [Fin.mk_one, markedPlace_one, ← ord_X_sub_C_pos_iff]
    exact ord_restrict_pos_iff_of_integers_comap_eq hQ' (by simp only [map_one, map_sub, hX])
  · simp only [Fin.reduceFinMk, markedPlace_two, ← X_notMem_integers_iff_eq_infty]
    rw [mem_integers_restrict_iff k (RatFunc k), ← hQ', ValuationSubring.mem_comap, hX,
      mem_integers_restrict_iff k' (RatFunc k')]

omit [Algebra k k'] [Algebra k F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] in
/-- **Contracting places match `{0, 1, ∞}` across arbitrary constant extensions.** -/
theorem restrict_mem_zeroOneInfty_iff_of_integers_comap_eq
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X) {Q : Place k F} {Q' : Place k' F'}
    (hQ' : Q'.integers.comap (algebraMap F F') = Q.integers) :
    Q.restrict k (RatFunc k) ∈ zeroOneInfty k ↔
      Q'.restrict k' (RatFunc k') ∈ zeroOneInfty k' := by
  simp only [← range_markedPlace, Set.mem_range, eq_comm (b := Place.restrict _ _ _),
    restrict_eq_markedPlace_iff_of_integers_comap_eq hX hQ']

/-- **Integral base change keeps each marked fibre**: when `F' / F` is integral and `t` acts on `F'`
as it does on `F`, a place `Q'` of `F'` lies over the marked place of `k'(t)` numbered `i` exactly
when the place of `F` below it lies over the marked place of `k(t)` numbered `i`. -/
theorem restrict_restrict_eq_markedPlace_iff [Algebra.IsIntegral F F']
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X) (Q' : Place k' F') (i : Fin 3) :
    (Q'.restrict k F).restrict k (RatFunc k) = markedPlace k i ↔
      Q'.restrict k' (RatFunc k') = markedPlace k' i :=
  restrict_eq_markedPlace_iff_of_integers_comap_eq hX
    (by ext f; exact (mem_integers_restrict_iff k F Q' f).symm) i

/-- **Integral base change matches the marked places**: when `F' / F` is integral and `t` acts on
`F'` as it does on `F`, a place `Q'` of `F'` lies over one of the marked places `t = 0`, `t = 1`,
`t = ∞` of `k'(t)` exactly when the place of `F` below it lies over one of those of `k(t)`. -/
theorem restrict_restrict_mem_zeroOneInfty_iff [Algebra.IsIntegral F F']
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X) (Q' : Place k' F') :
    (Q'.restrict k F).restrict k (RatFunc k) ∈ zeroOneInfty k ↔
      Q'.restrict k' (RatFunc k') ∈ zeroOneInfty k' :=
  restrict_mem_zeroOneInfty_iff_of_integers_comap_eq hX
    (by ext f; exact (mem_integers_restrict_iff k F Q' f).symm)

end Place

variable [CharZero k] [FiniteDimensional (RatFunc k) F] [FiniteDimensional (RatFunc k') F']

open Place in
/-- **Base change of algebraic Belyi pairs**: let `F / k(t)` have exact constant field `k`, of
characteristic zero, and let `F' = F · k'` be its compositum with any field extension `k' / k`,
with `t` acting on `F'` as it does on `F`. Then `F' / k'(t)` is an algebraic Belyi pair exactly
when `F / k(t)` is. -/
theorem isAlgebraicBelyiPair_iff_of_constantCompositum_eq_top [CharZero k']
    (hex : IsIntegrallyClosedIn k F) (hcomp : constantCompositum F k' F' = ⊤)
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X) :
    IsAlgebraicBelyiPair k' F' ↔ IsAlgebraicBelyiPair k F := by
  have hF : IsFunctionField k F := (IsFunctionField.ratFunc k).finite_extension
  have H := linearDisjoint_of_isGeometricallyReduced_ratFunc hex hX
  refine ⟨fun h' ↦ ⟨hex, fun {Q} hQ ↦ ?_⟩,
    fun h ↦ ⟨hex.of_constantCompositum_eq_top_of_linearDisjoint H hcomp, fun {Q'} hQ' ↦ ?_⟩⟩
  · obtain ⟨Q', hQ'⟩ := exists_integers_comap_eq hF H hcomp Q
    rw [← ramificationIdx_ratFunc_eq_of_integers_comap_eq hex hcomp hX hQ']
    exact h'.ramificationIdx_eq_one
      ((restrict_mem_zeroOneInfty_iff_of_integers_comap_eq hX hQ').not.mp hQ)
  · rcases isTrivialOn_or_existsUnique_integers_comap_eq hF Q' with htriv | ⟨Q, hQ, -⟩
    · exact ramificationIdx_ratFunc_eq_one_of_isTrivialOn hcomp hX htriv
    · rw [ramificationIdx_ratFunc_eq_of_integers_comap_eq hex hcomp hX hQ]
      exact h.ramificationIdx_eq_one
        ((restrict_mem_zeroOneInfty_iff_of_integers_comap_eq hX hQ).not.mpr hQ')

/-- **Degree-preserving descent of an algebraic Belyi pair** across an arbitrary constant
extension. -/
theorem IsAlgebraicBelyiPair.of_finrank_eq [CharZero k'] (h' : IsAlgebraicBelyiPair k' F')
    (hcomp : constantCompositum F k' F' = ⊤)
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X)
    (hfin : Module.finrank (RatFunc k) F = Module.finrank (RatFunc k') F') :
    IsAlgebraicBelyiPair k F :=
  have H := linearDisjoint_of_finrank_ratFunc_eq hcomp hX hfin.symm
  (isAlgebraicBelyiPair_iff_of_constantCompositum_eq_top
    (H.isIntegrallyClosedIn h'.isIntegrallyClosedIn) hcomp hX).mp h'

end TauCeti
