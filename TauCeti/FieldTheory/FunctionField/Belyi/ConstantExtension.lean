/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Belyi.Basic
public import TauCeti.FieldTheory.FunctionField.ConstantExtension.Algebraic
import TauCeti.FieldTheory.FunctionField.ConstantExtension.Basis
import TauCeti.FieldTheory.FunctionField.ConstantExtension.Unramified
import TauCeti.FieldTheory.FunctionField.Place.RatFunc.Order

/-!
# Extending the constants of an algebraic Belyi pair

Let `F / k(t)` be an algebraic Belyi pair over a field `k` of characteristic zero, and let `k'` be
an algebraic extension of `k`, for instance an algebraic closure of a number field `k`. Let `F'` be
the compositum `F · k'`, over a rational function field `k'(t)` whose variable is the image of the
variable of `k(t)`. This is the function-field form of base change of the Belyi map from `k` to
`k'`. Then `F' / k'(t)` is again an algebraic Belyi pair
(`TauCeti.IsAlgebraicBelyiPair.of_constantCompositum_eq_top`).

The exact constant field of `F'` is `k'` because `k'` is separable over `k`
(`IsIntegrallyClosedIn.of_constantCompositum_eq_top`), and `F'` is finite over `k'(t)`
(`TauCeti.finiteDimensional_ratFunc_of_constantCompositum_eq_top`). For the ramification, let `P'`
be a place of `F'`, let `P` be the place of `F` below it, and compare the places `Q` of `k(t)`
and `Q'` of `k'(t)` below `P'`. The orders at `P'` of `t` and of `t - 1` are positive multiples of
their orders at `Q`, and also of their orders at `Q'`, so `Q` is the marked place numbered `i`
exactly when `Q'` is (`TauCeti.Place.restrict_restrict_eq_markedPlace_iff`). If `Q'` is not
marked, then `P` is unramified over `Q` because `F` is a Belyi pair, and `P'` is unramified over
`P` because extending the constants is unramified. So a uniformizer `q(t)` of `Q`, for an
irreducible polynomial `q` over `k`, still has order one at `P'`. Since its order at `P'` is a
multiple of the ramification index of `P'` over `Q'`, that index is one.

A Belyi pair defined over a number field `k` therefore gives a Belyi pair over an algebraic closure
of `k`, or over `ℂ`. This is what a model of a Belyi pair over a field of definition is compared
with.

## Main results

* `TauCeti.Place.restrict_restrict_eq_markedPlace_iff`: a place of `F'` lies over the marked place
  of `k(t)` numbered `i` exactly when it lies over the marked place of `k'(t)` numbered `i`.
* `TauCeti.IsAlgebraicBelyiPair.of_constantCompositum_eq_top`: extending the constants of an
  algebraic Belyi pair by an algebraic extension gives an algebraic Belyi pair.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section III.6, Proposition 3.6.1 and Theorem 3.6.3.
* B. Köck, *Belyi's theorem revisited*, Beiträge zur Algebra und Geometrie 45 (2004), 253–265,
  proof of (2.2) Theorem.
-/

public section

open Polynomial

namespace TauCeti

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F']
  [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
  [Algebra (RatFunc k') F'] [IsScalarTower k' (RatFunc k') F']

namespace Place

variable [Algebra.IsIntegral F F'] [Algebra.IsIntegral (RatFunc k) F]
  [Algebra.IsIntegral (RatFunc k') F']

/-- Along `F → F'`, the order at a place `P'` of `F'` of an element of `k(t)` is a positive multiple
of its order at the place of `k(t)` below `P'`; when that element is also the image of an element of
`k'(t)`, it is a positive multiple of the order of the latter at the place of `k'(t)` below `P'`. -/
private theorem ramificationIdx_mul_ord_eq (P' : Place k' F') {f : RatFunc k} {f' : RatFunc k'}
    (hf : algebraMap F F' (algebraMap (RatFunc k) F f) = algebraMap (RatFunc k') F' f') :
    (ramificationIdx (RatFunc k') P' : ℤ) * (P'.restrict k' (RatFunc k')).ord f' =
      (ramificationIdx F P' * ramificationIdx (RatFunc k) (P'.restrict k F) : ℕ) *
        ((P'.restrict k F).restrict k (RatFunc k)).ord f := by
  rw [← ord_algebraMap_restrict k' (RatFunc k') P', ← hf, ord_algebraMap_restrict k F P',
    ord_algebraMap_restrict k (RatFunc k) (P'.restrict k F), Nat.cast_mul, mul_assoc]

/-- Under the hypotheses of `ramificationIdx_mul_ord_eq`, the two orders have the same sign. -/
private theorem ord_pos_iff_and_ord_neg_iff (P' : Place k' F') {f : RatFunc k} {f' : RatFunc k'}
    (hf : algebraMap F F' (algebraMap (RatFunc k) F f) = algebraMap (RatFunc k') F' f') :
    (0 < (P'.restrict k' (RatFunc k')).ord f' ↔
        0 < ((P'.restrict k F).restrict k (RatFunc k)).ord f) ∧
      ((P'.restrict k' (RatFunc k')).ord f' < 0 ↔
        ((P'.restrict k F).restrict k (RatFunc k)).ord f < 0) := by
  have h := ramificationIdx_mul_ord_eq P' hf
  have he' : (0 : ℤ) < ramificationIdx (RatFunc k') P' := by
    exact_mod_cast ramificationIdx_pos (RatFunc k') P'
  have he : (0 : ℤ) < (ramificationIdx F P' * ramificationIdx (RatFunc k) (P'.restrict k F) : ℕ) :=
    by exact_mod_cast Nat.mul_pos (ramificationIdx_pos F P') (ramificationIdx_pos _ _)
  constructor
  · rw [← mul_pos_iff_of_pos_left he', h, mul_pos_iff_of_pos_left he]
  · rw [← neg_pos, ← mul_pos_iff_of_pos_left he', mul_neg, h, ← mul_neg,
      mul_pos_iff_of_pos_left he, neg_pos]

/-- **Extending the constants keeps the fibres over the marked places**: if the variable of `k(t)`
is carried into `F'` to the variable of `k'(t)`, then a place of `F'` lies, through `F`, over the
marked place of `k(t)` numbered `i` exactly when it lies over the marked place of `k'(t)` numbered
`i`. -/
theorem restrict_restrict_eq_markedPlace_iff
    (ht : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X)
    {P' : Place k' F'} {i : Fin 3} :
    (P'.restrict k F).restrict k (RatFunc k) = markedPlace k i ↔
      P'.restrict k' (RatFunc k') = markedPlace k' i := by
  have ht1 : algebraMap F F' (algebraMap (RatFunc k) F (RatFunc.X - RatFunc.C 1)) =
      algebraMap (RatFunc k') F' (RatFunc.X - RatFunc.C 1) := by
    simp only [map_one, map_sub, ht]
  fin_cases i
  · simp only [Fin.zero_eta, markedPlace_zero, ← ord_X_pos_iff]
    exact (ord_pos_iff_and_ord_neg_iff P' ht).1.symm
  · simp only [Fin.mk_one, markedPlace_one, ← ord_X_sub_C_pos_iff]
    exact (ord_pos_iff_and_ord_neg_iff P' ht1).1.symm
  · simp only [Fin.reduceFinMk, markedPlace_two, ← X_notMem_integers_iff_eq_infty,
      mem_integers_iff_ord_nonneg, not_le]
    exact (ord_pos_iff_and_ord_neg_iff P' ht).2.symm

/-- **Extending the constants keeps the three marked fibres**: a place of `F'` lies, through `F`,
over one of the three marked places of `k(t)` exactly when it lies over one of the three marked
places of `k'(t)`. -/
theorem restrict_restrict_mem_zeroOneInfty_iff
    (ht : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X)
    {P' : Place k' F'} :
    (P'.restrict k F).restrict k (RatFunc k) ∈ zeroOneInfty k ↔
      P'.restrict k' (RatFunc k') ∈ zeroOneInfty k' := by
  simp only [← range_markedPlace, Set.mem_range, eq_comm (b := Place.restrict _ _ _),
    restrict_restrict_eq_markedPlace_iff ht]

end Place

/-- **Extending the constants of an algebraic Belyi pair** gives an algebraic Belyi pair. Let
`F / k(t)` be an algebraic Belyi pair, let `k'` be an algebraic extension of `k`, and let `F'` be
the compositum `F · k'`, with the variable of `k(t)` carried to the variable of `k'(t)`. Then
`F' / k'(t)` is an algebraic Belyi pair. For instance, a Belyi pair over a number field `k` gives
one over an algebraic closure of `k`.

The finiteness of `F'` over `k'(t)` that the statement presupposes is
`TauCeti.finiteDimensional_ratFunc_of_constantCompositum_eq_top`. -/
theorem IsAlgebraicBelyiPair.of_constantCompositum_eq_top [CharZero k] [CharZero k']
    [Algebra.IsAlgebraic k k'] [FiniteDimensional (RatFunc k) F]
    [FiniteDimensional (RatFunc k') F'] (h : IsAlgebraicBelyiPair k F)
    (hcomp : constantCompositum F k' F' = ⊤)
    (ht : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X) :
    IsAlgebraicBelyiPair k' F' where
  isIntegrallyClosedIn := .of_constantCompositum_eq_top h.isIntegrallyClosedIn hcomp
  ramificationIdx_eq_one {P'} hP' := by
    classical
    have : Algebra.IsIntegral F F' :=
      have := isAlgebraic_of_constantCompositum_eq_top (k := k) hcomp
      inferInstance
    -- The place `Q` of `k(t)` below `P'` is not marked, so it is the place of an irreducible
    -- polynomial `q`, and `P'` is unramified over it.
    have hQ := mt (Place.restrict_restrict_mem_zeroOneInfty_iff ht).mp hP'
    obtain ⟨q, hq, hQq⟩ :=
      (Place.eq_infty_or_exists_eq_adicOfIrreducible ((P'.restrict k F).restrict k (RatFunc k))
        ).resolve_left fun hinf ↦ hQ (hinf ▸ Place.infty_mem_zeroOneInfty)
    -- The uniformizer `q(t)` of `Q` therefore has order one at `P'`.
    have hqt : algebraMap F F' (algebraMap (RatFunc k) F (algebraMap k[X] (RatFunc k) q)) =
        algebraMap (RatFunc k') F' (algebraMap k'[X] (RatFunc k') (q.map (algebraMap k k'))) := by
      rw [← RatFunc.aeval_X_left_eq_algebraMap, ← RatFunc.aeval_X_left_eq_algebraMap,
        ← aeval_algebraMap_apply, ← aeval_algebraMap_apply, ← aeval_algebraMap_apply, ht,
        aeval_map_algebraMap]
    have h1 := Place.ramificationIdx_mul_ord_eq P' hqt
    rw [Place.ramificationIdx_eq_one_of_constantCompositum_eq_top (k := k) hcomp,
      h.ramificationIdx_eq_one hQ, hQq, Place.ord_adicOfIrreducible_algebraMap_irreducible hq hq,
      ite_eq_left (Associated.refl q)] at h1
    exact_mod_cast Int.eq_one_of_mul_eq_one_right (Nat.cast_nonneg _) h1

end TauCeti
