/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.Belyi
public import TauCeti.FieldTheory.FunctionField.Belyi.Basic
public import TauCeti.FieldTheory.FunctionField.Different.Derivative
import TauCeti.FieldTheory.FunctionField.AffineModel.Place
import TauCeti.FieldTheory.FunctionField.Belyi.Radical
import TauCeti.FieldTheory.RatFunc.Transcendental

/-!
# Polynomial Belyi maps

Let `k` be a field and `q ∈ k[X]` a polynomial with `q′ ≠ 0`. Regarded as a map of the
projective line, `x ↦ q(x)` is branched only over `∞` and over the critical values of `q`, the
values `q(ξ)` at the roots `ξ` of `q′` (`Polynomial.criticalValues`). This file proves that
containment in the language of function fields: if `F = k(x)` over `k(t)`, where `t = q(x)`,
then every place of `k(t)` at which `t` is regular and `r(t)` is a unit, for some
polynomial `r` vanishing at every critical value of `q`, is unramified in `F`
(`TauCeti.Place.ramificationIdx_eq_one_of_aeval_eq`).

The proof is the derivative criterion for the different (Stichtenoth, Theorem 3.5.10(a)): `x` is
a root of the monic polynomial `(q(X) - t) / lc(q)`, whose coefficients are regular at such a
place `P`, so a place `P'` of `F` over `P` is unramified as soon as `q′(x)` is a unit at `P'`.
If it is not, then evaluating at `P'` makes the residue `x(P')` a root of `q′` in the residue
field, so `t(P') = q(x(P'))` is a critical value of `q` there, and `r(t)` vanishes at `P`.

In characteristic zero, taking `r = X (X - 1)` gives the criterion for Belyi maps: if the critical
values of `q`, in every field extension of `k`, lie in `{0, 1}`, then `F = k(x)` over `k(t)`,
`t = q(x)`, is an algebraic Belyi pair (`TauCeti.IsAlgebraicBelyiPair.of_criticalValues_subset`).
This applies to the Belyi polynomials `B_{m,n}`
(`TauCeti.IsAlgebraicBelyiPair.of_aeval_belyiPolynomial`) and, over `ℚ`, to the polynomials
produced by polynomial Belyification (`TauCeti.exists_polynomial_eval_mem_criticalValues_subset`).
In Belyi's theorem it is the ramification computation for the last step, which composes a map
`t₀` with such a polynomial `q`: the extension `k(t₀) / k(q(t₀))` is unramified away from `0`, `1`
and `∞`.

## Main results

* `TauCeti.Place.ramificationIdx_eq_one_of_aeval_eq`: the places of `k(t)` away from `∞` and
  from the critical values of `q` are unramified in `k(x)`.
* `TauCeti.IsAlgebraicBelyiPair.of_criticalValues_subset`: a polynomial whose critical values lie
  in `{0, 1}` is an algebraic Belyi pair.
* `TauCeti.IsAlgebraicBelyiPair.of_aeval_belyiPolynomial`: the Belyi polynomials are algebraic
  Belyi pairs.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Theorem 3.5.10.
* Bernhard Köck, *Belyi's theorem revisited*, Beiträge zur Algebra und Geometrie 45 (2004),
  253–265, §3.
-/

public section

open Polynomial

open scoped IntermediateField

namespace TauCeti

universe u v

variable {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F] [Algebra (RatFunc k) F]
  [IsScalarTower k (RatFunc k) F] {x : F} {q : k[X]}

/-- The monic equation `(q(X) - a) / lc(q)` over a `k`-algebra `R`, satisfied by `x` when
`a = q(x)`. -/
private noncomputable def monicEquation {R : Type*} [CommRing R] [Algebra k R] (q : k[X]) (a : R) :
    R[X] :=
  (C q.leadingCoeff⁻¹ * q).map (algebraMap k R) - C (algebraMap k R q.leadingCoeff⁻¹ * a)

private theorem monic_monicEquation {R : Type*} [CommRing R] [Nontrivial R] [Algebra k R]
    (hq : 0 < q.natDegree) (a : R) : (monicEquation q a).Monic := by
  have hq0 : q ≠ 0 := ne_zero_of_natDegree_gt hq
  have hm : (C q.leadingCoeff⁻¹ * q).Monic :=
    monic_C_mul_of_mul_leadingCoeff_eq_one (inv_mul_cancel₀ (leadingCoeff_ne_zero.mpr hq0))
  refine (hm.map _).sub_of_left (degree_C_le.trans_lt ?_)
  rw [hm.degree_map, degree_C_mul (inv_ne_zero (leadingCoeff_ne_zero.mpr hq0)),
    degree_eq_natDegree hq0]
  exact_mod_cast hq

private theorem aeval_monicEquation {R S : Type*} [CommRing R] [Algebra k R] [CommRing S]
    [Algebra k S] [Algebra R S] [IsScalarTower k R S] (a : R) (y : S) :
    aeval y (monicEquation q a) =
      algebraMap k S q.leadingCoeff⁻¹ * (aeval y q - algebraMap R S a) := by
  simp [monicEquation, aeval_map_algebraMap, mul_sub, ← IsScalarTower.algebraMap_apply]

private theorem aeval_derivative_monicEquation {R S : Type*} [CommRing R] [Algebra k R]
    [CommRing S] [Algebra k S] [Algebra R S] [IsScalarTower k R S] (a : R) (y : S) :
    aeval y (derivative (monicEquation q a)) =
      algebraMap k S q.leadingCoeff⁻¹ * aeval y (derivative q) := by
  simp [monicEquation, derivative_map, aeval_map_algebraMap, ← IsScalarTower.algebraMap_apply]

/-- The coefficients of the monic equation are regular wherever `t` is. -/
private theorem coeff_monicEquation_mem_integers {P : Place k (RatFunc k)}
    (hX : (RatFunc.X : RatFunc k) ∈ P.integers) (i : ℕ) :
    (monicEquation q RatFunc.X).coeff i ∈ P.integers := by
  rw [monicEquation, coeff_sub, coeff_map, coeff_C]
  refine sub_mem (P.algebraMap_mem_integers _) ?_
  split_ifs
  exacts [mul_mem (P.algebraMap_mem_integers _) hX, zero_mem _]

namespace Place

omit [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] in
/-- **Evaluation at a place sends a critical point to a critical value**: if `x` and `a = q(x)` are
regular at a place `P` and `q′(x)` vanishes at `P`, then the value `a(P)` is a critical value of
`q` in the residue field. -/
private theorem residue_mem_criticalValues {P : Place k F} {x a : P.integers}
    (hd : derivative q ≠ 0)
    (hxa : aeval x q = a) (hlt : P.valuation (aeval (x : F) (derivative q)) < 1) :
    IsLocalRing.residue P.integers a ∈ q.criticalValues P.ResidueField := by
  refine mem_criticalValues.mpr ⟨IsLocalRing.residue P.integers x, (mem_rootSet_of_ne hd).mpr ?_,
    by rw [← residue_aeval, hxa]⟩
  rw [← residue_aeval, residue_eq_zero_iff_valuation_lt_one, coe_aeval_integers]
  exact hlt

variable [Algebra.IsIntegral (RatFunc k) F]

/-- **A polynomial map is unramified away from `∞` and its critical values**: let `F = k(x)` over
`k(t)`, where `t = q(x)` for a polynomial `q` with `q′ ≠ 0`, so that `F` is finite and separable
over `k(t)`. If `r ∈ k[X]` vanishes
at every critical value of `q`, in every field extension of `k`, then every place of `F` over a
place of `k(t)` other than `∞` at which `r(t)` is a unit has ramification index `1`. -/
theorem ramificationIdx_eq_one_of_aeval_eq (hx : k⟮x⟯ = ⊤)
    (hq : algebraMap (RatFunc k) F RatFunc.X = aeval x q) (hd : derivative q ≠ 0) {r : k[X]}
    (hr : ∀ (L : Type v) [Field L] [Algebra k L], ∀ c ∈ q.criticalValues L, aeval c r = 0)
    {P' : Place k F} (hP : P'.restrict k (RatFunc k) ≠ infty k)
    (hr1 : (P'.restrict k (RatFunc k)).valuation (aeval RatFunc.X r) = 1) :
    ramificationIdx (RatFunc k) P' = 1 := by
  have := finiteDimensional_of_aeval_eq hx hq
  have := isSeparable_of_aeval_eq hx hq hd
  have hdeg := natDegree_pos_of_aeval_eq hq
  have hX : (RatFunc.X : RatFunc k) ∈ (P'.restrict k (RatFunc k)).integers :=
    not_not.mp (X_notMem_integers_iff_eq_infty.not.mpr hP)
  -- `t` is regular at `P'`, and so is `x`, which is integral over the valuation ring of `P'`.
  set a := algebraMap (RatFunc k) F RatFunc.X
  have ha : a ∈ P'.integers := (mem_integers_restrict_iff k (RatFunc k) P' _).mp hX
  have hxO : x ∈ P'.integers := by
    refine P'.mem_integers_of_isIntegral (R := P'.integers) (fun r ↦ r.2)
      ⟨_, monic_monicEquation hdeg (⟨a, ha⟩ : P'.integers), ?_⟩
    rw [← aeval_def, aeval_monicEquation, ValuationSubring.algebraMap_apply]
    simp [← hq]
  -- The derivative criterion reduces the claim to `q′(x)` being a unit at `P'`.
  suffices hval : P'.valuation (aeval x (derivative q)) = 1 by
    have h0 := differentExponent_eq_zero_of_valuation_aeval_derivative_eq_one k (RatFunc k)
      (IntermediateField.adjoin_eq_top_of_adjoin_eq_top k hx) (monic_monicEquation hdeg _)
      (coeff_monicEquation_mem_integers hX) (by rw [aeval_monicEquation, ← hq, sub_self, mul_zero])
      (by
        rw [aeval_derivative_monicEquation, map_mul, hval, mul_one,
          P'.valuation_eq_one_of_isAlgebraic (isAlgebraic_algebraMap _)
            ((_root_.map_ne_zero _).mpr (inv_ne_zero (leadingCoeff_ne_zero.mpr
              (ne_zero_of_natDegree_gt hdeg))))])
    have := ramificationIdx_le_differentExponent_add_one k (RatFunc k) P'
    have := ramificationIdx_pos (RatFunc k) P'
    omega
  -- Otherwise `t(P')` is a critical value of `q`, at which `r` vanishes; so `r(t)` would vanish at
  -- `P'`, while it is a unit at `P`.
  refine le_antisymm (P'.mem_integers_iff.mp
    (P'.adjoin_le_integers_iff.mpr hxO _ (aeval_mem_adjoin_singleton k x)))
    (not_lt.mp fun hlt ↦ ?_)
  have hcrit := residue_mem_criticalValues (x := ⟨x, hxO⟩) (a := ⟨a, ha⟩) hd
    (Subtype.ext ((P'.coe_aeval_integers q _).trans hq.symm)) hlt
  have hzero : IsLocalRing.residue P'.integers (aeval (⟨a, ha⟩ : P'.integers) r) = 0 := by
    rw [residue_aeval]
    exact hr _ _ hcrit
  rw [residue_eq_zero_iff_valuation_lt_one, coe_aeval_integers] at hzero
  have hra : aeval a r = algebraMap (RatFunc k) F (aeval RatFunc.X r) :=
    aeval_algebraMap_apply (R := k) (B := F) RatFunc.X r
  rw [hra, valuation_algebraMap_restrict k (RatFunc k) P', hr1, one_pow] at hzero
  exact hzero.false

end Place

namespace IsAlgebraicBelyiPair

variable [CharZero k] [FiniteDimensional (RatFunc k) F]

/-- **Polynomials with critical values in `{0, 1}` are Belyi maps**: if `F = k(x)` over `k(t)`,
where `t = q(x)` for a polynomial `q` whose critical values in every field extension of `k` lie in
`{0, 1}`, then `F` is an algebraic Belyi pair. -/
theorem of_criticalValues_subset (hx : k⟮x⟯ = ⊤)
    (hq : algebraMap (RatFunc k) F RatFunc.X = aeval x q)
    (hcrit : ∀ (L : Type v) [Field L] [Algebra k L], q.criticalValues L ⊆ {0, 1}) :
    IsAlgebraicBelyiPair k F where
  isIntegrallyClosedIn := by
    exact ((IntermediateField.equivOfEq hx).trans
      IntermediateField.topEquiv).isIntegrallyClosedIn.mp
        (transcendental_of_aeval_eq hq).isIntegrallyClosedIn_adjoin
  ramificationIdx_eq_one {P'} hP := by
    refine Place.ramificationIdx_eq_one_of_aeval_eq hx hq
      (fun h ↦ (natDegree_pos_of_aeval_eq hq).ne' (derivative_eq_zero.mp h)) (r := X * (X - 1))
      (fun L _ _ c hc ↦ ?_) (fun h ↦ hP (h ▸ Place.infty_mem_zeroOneInfty)) ?_
    · rcases hcrit L hc with rfl | rfl <;> simp
    · have he : aeval (RatFunc.X : RatFunc k) (X * (X - 1) : k[X]) =
          algebraMap k (RatFunc k) 1 * RatFunc.X ^ (1 : ℤ) * (RatFunc.X - 1) ^ (1 : ℤ) := by
        simp
      rw [he, Place.valuation_eq_exp_neg_ord _
        (RatFunc.algebraMap_mul_X_zpow_mul_X_sub_one_zpow_ne_zero one_ne_zero 1 1),
        Place.ord_algebraMap_mul_X_zpow_mul_X_sub_one_zpow_of_notMem_zeroOneInfty hP one_ne_zero,
        neg_zero, WithZero.exp_zero]

/-- **The Belyi polynomials are Belyi maps**: if `F = k(x)` over `k(t)`, where
`t = B_{m,n}(x)` for the Belyi polynomial `B_{m,n}`, then `F` is an algebraic Belyi pair. -/
theorem of_aeval_belyiPolynomial (hx : k⟮x⟯ = ⊤) {m n : ℕ}
    (hq : algebraMap (RatFunc k) F RatFunc.X = aeval x (belyiPolynomial k m n)) :
    IsAlgebraicBelyiPair k F :=
  of_criticalValues_subset hx hq fun L _ _ ↦ criticalValues_belyiPolynomial_subset L m n

end IsAlgebraicBelyiPair

end TauCeti
