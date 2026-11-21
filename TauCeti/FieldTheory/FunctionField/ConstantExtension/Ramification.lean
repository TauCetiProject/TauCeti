/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.ConstantExtension.Basic
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Basic
import TauCeti.FieldTheory.FunctionField.ConstantExtension.Degree
import TauCeti.FieldTheory.FunctionField.ConstantExtension.Place
import TauCeti.FieldTheory.FunctionField.ConstantExtension.Unramified
import TauCeti.FieldTheory.FunctionField.Place.RatFunc.Order
import TauCeti.FieldTheory.RatFunc.Map
import TauCeti.FieldTheory.RatFunc.Transcendental

/-!
# Ramification over the rational function field after extending constants

Let `F` be a field over `k(t)` and let `F' = F · k'` be its compositum with an extension `k' / k`
of a perfect field, carrying the `k'(t)`-algebra structure in which `t` acts as it does on `F`.
Geometrically, `F / k(t)` is a finite map from a curve to the projective line, and `F' / k'(t)` is
its base change to `k'`. This file shows that base change does not change ramification over the
line: when `k' / k` is algebraic, a place `Q'` of `F'` has the same ramification index over `k'(t)`
as the place `Q` of `F` below it has over `k(t)`, and the place of `k'(t)` below `Q'` gives every
polynomial in `t` with coefficients in `k` the same order as the place of `k(t)` below `Q`.

Both statements come from comparing the orders at `Q'` of a polynomial in `t` computed through
`F` and through `k'(t)`. Whenever `Q'` preserves normalized orders on `F` (`Q'.ord = Q.ord` on `F`),
through `F` the order is `e(Q ∣ k(t))` times the order at the place of `k(t)` below `Q`, and
through `k'(t)` it is `e(Q' ∣ k'(t))` times the order at the place of `k'(t)` below `Q'`. At the
place at infinity the polynomial `t` has a simple pole on both sides. At the place of an
irreducible `q` the polynomial `q` has order one, and it has order at most one at every finite
place of `k'(t)`, because `q` stays squarefree over `k'`, `k` being perfect.

For arbitrary (possibly transcendental) extensions `k' / k`, places of `F'` trivial on `F` are
unramified over `k'(t)` when `F / k(t)` is finite separable, while places contracting to `Q` on `F`
preserve `e(Q ∣ k(t))` and polynomial orders whenever `k` is perfect and exact in `F`.

For a Belyi map this is what makes being unramified outside `t = 0`, `t = 1` and `t = ∞`
invariant under extension of the constant field
(`TauCeti.isAlgebraicBelyiPair_iff_of_constantCompositum_eq_top`).

## Main results

* `TauCeti.Place.ramificationIdx_ratFunc_eq_of_ord_algebraMap_eq` and
  `TauCeti.Place.ord_restrict_algebraMap_eq_of_ord_algebraMap_eq`: any pair of places `Q` of `F`
  and `Q'` of `F'` with `Q'.ord = Q.ord` on `F` (over perfect `k`) have the same ramification index
  over `k(t)` and `k'(t)` and give polynomials over `k` the same order below.
* `TauCeti.Place.ramificationIdx_ratFunc_eq_of_constantCompositum_eq_top` and
  `TauCeti.Place.ord_restrict_algebraMap_eq_of_constantCompositum_eq_top`: the algebraic
  constant-extension case (`Q = Q'.restrict k F`).
* `TauCeti.Place.ramificationIdx_ratFunc_eq_one_of_isTrivialOn`,
  `TauCeti.Place.ramificationIdx_ratFunc_eq_of_integers_comap_eq`, and
  `TauCeti.Place.ord_restrict_algebraMap_eq_of_integers_comap_eq`: ramification and polynomial
  orders under arbitrary constant extensions.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Proposition 3.1.6 and Theorem 3.6.3.
-/

public section

open Polynomial
open scoped IntermediateField

namespace TauCeti

namespace Place

section OrderComparison

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F']
  [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [Algebra.IsIntegral (RatFunc k) F]
  [Algebra (RatFunc k') F'] [IsScalarTower k' (RatFunc k') F']
  [Algebra.IsIntegral (RatFunc k') F'] [PerfectField k]

/-- **Order preservation on `F` preserves ramification over the line**: over a perfect field `k`, if
`t` acts on `F'` as it does on `F` and `Q'` agrees with `Q` on normalized orders of `F`, then `Q'`
has the same ramification index over `k'(t)` as `Q` has over `k(t)`. -/
theorem ramificationIdx_ratFunc_eq_of_ord_algebraMap_eq
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X)
    {Q : Place k F} {Q' : Place k' F'} (hord : ∀ f : F, Q'.ord (algebraMap F F' f) = Q.ord f) :
    ramificationIdx (RatFunc k') Q' = ramificationIdx (RatFunc k) Q := by
  have he := ramificationIdx_pos (RatFunc k) Q
  have hmul (p : k[X]) :
      (ramificationIdx (RatFunc k) Q : ℤ) *
          (Q.restrict k (RatFunc k)).ord (algebraMap k[X] (RatFunc k) p) =
        ramificationIdx (RatFunc k') Q' * (Q'.restrict k' (RatFunc k')).ord
          (algebraMap k'[X] (RatFunc k') (p.map (algebraMap k k'))) := by
    rw [← ord_algebraMap_restrict k (RatFunc k) Q, ← ord_algebraMap_restrict k' (RatFunc k') Q',
      ← algebraMap_algebraMap_polynomial hX, hord]
  rcases eq_infty_or_exists_eq_adicOfIrreducible (Q.restrict k (RatFunc k)) with hP | ⟨q, hq, hP⟩
  · -- At infinity `t` has a simple pole, below `Q` in `k(t)` and hence below `Q'` in `k'(t)`.
    have h := hmul X
    rw [Polynomial.map_X, RatFunc.algebraMap_X, RatFunc.algebraMap_X, hP, ord_infty,
      RatFunc.intDegree_X] at h
    have hP' : Q'.restrict k' (RatFunc k') = infty k' :=
      X_notMem_integers_iff_eq_infty.mp fun hmem ↦ by
        have := (Q'.restrict k' (RatFunc k')).mem_integers_iff_ord_nonneg.mp hmem
        nlinarith
    rw [hP', ord_infty, RatFunc.intDegree_X] at h
    omega
  -- At the place of `q`, the order of `q` is one, and `q` stays squarefree over `k'`.
  have h := hmul q
  rw [hP, ord_adicOfIrreducible_algebraMap_irreducible hq hq, ite_eq_left (Associated.refl q),
    mul_one] at h
  have hsq : Squarefree (q.map (algebraMap k k')) :=
    (PerfectField.separable_of_irreducible hq).map.squarefree
  rcases eq_infty_or_exists_eq_adicOfIrreducible (Q'.restrict k' (RatFunc k')) with
    hP' | ⟨q', hq', hP'⟩
  · rw [hP', ord_infty, RatFunc.intDegree_polynomial] at h
    nlinarith
  rw [hP', ord_adicOfIrreducible_algebraMap_of_squarefree hq' hsq] at h
  split_ifs at h <;> omega

/-- **Order preservation on `F` preserves orders of polynomials in `t`**: under the hypotheses of
`TauCeti.Place.ramificationIdx_ratFunc_eq_of_ord_algebraMap_eq`, the places of `k(t)` and `k'(t)`
below `Q` and `Q'` give every polynomial in `t` over `k` the same order. -/
theorem ord_restrict_algebraMap_eq_of_ord_algebraMap_eq
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X)
    {Q : Place k F} {Q' : Place k' F'} (hord : ∀ f : F, Q'.ord (algebraMap F F' f) = Q.ord f)
    (p : k[X]) :
    (Q.restrict k (RatFunc k)).ord (algebraMap k[X] (RatFunc k) p) =
      (Q'.restrict k' (RatFunc k')).ord
        (algebraMap k'[X] (RatFunc k') (p.map (algebraMap k k'))) := by
  have h : (ramificationIdx (RatFunc k) Q : ℤ) *
      (Q.restrict k (RatFunc k)).ord (algebraMap k[X] (RatFunc k) p) =
      ramificationIdx (RatFunc k') Q' * (Q'.restrict k' (RatFunc k')).ord
        (algebraMap k'[X] (RatFunc k') (p.map (algebraMap k k'))) := by
    rw [← ord_algebraMap_restrict k (RatFunc k) Q, ← ord_algebraMap_restrict k' (RatFunc k') Q',
      ← algebraMap_algebraMap_polynomial hX, hord]
  rw [ramificationIdx_ratFunc_eq_of_ord_algebraMap_eq hX hord] at h
  exact mul_left_cancel₀ (by exact_mod_cast (ramificationIdx_pos _ _).ne') h

end OrderComparison

section Algebraic

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F']
  [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [Algebra.IsIntegral (RatFunc k) F]
  [Algebra (RatFunc k') F'] [IsScalarTower k' (RatFunc k') F']
  [Algebra.IsIntegral (RatFunc k') F'] [Algebra.IsIntegral F F']
  [Algebra.IsSeparable k k'] [PerfectField k]

/-- **Extending constants does not change ramification over the line**: if `F' = F · k'` for an
algebraic extension `k' / k` of a perfect field and `t` acts on `F'` as it does on `F`, then every
place `Q'` of `F'` has the same ramification index over `k'(t)` as the place of `F` below it has
over `k(t)`. -/
theorem ramificationIdx_ratFunc_eq_of_constantCompositum_eq_top
    (hcomp : constantCompositum F k' F' = ⊤)
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X) (Q' : Place k' F') :
    ramificationIdx (RatFunc k') Q' = ramificationIdx (RatFunc k) (Q'.restrict k F) :=
  ramificationIdx_ratFunc_eq_of_ord_algebraMap_eq hX fun f ↦ by
    rw [ord_algebraMap_restrict k F Q',
      ramificationIdx_eq_one_of_constantCompositum_eq_top (k := k) hcomp, Nat.cast_one, one_mul]

/-- **Extending constants does not change orders of polynomials in `t`**: under the hypotheses of
`TauCeti.Place.ramificationIdx_ratFunc_eq_of_constantCompositum_eq_top`, the place of `k(t)` below
the place `Q` of `F` under `Q'` and the place of `k'(t)` below `Q'` give every polynomial in `t`
over `k` the same order. -/
theorem ord_restrict_algebraMap_eq_of_constantCompositum_eq_top
    (hcomp : constantCompositum F k' F' = ⊤)
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X) (Q' : Place k' F') (p : k[X]) :
    ((Q'.restrict k F).restrict k (RatFunc k)).ord (algebraMap k[X] (RatFunc k) p) =
      (Q'.restrict k' (RatFunc k')).ord
        (algebraMap k'[X] (RatFunc k') (p.map (algebraMap k k'))) :=
  ord_restrict_algebraMap_eq_of_ord_algebraMap_eq hX (fun f ↦ by
    rw [ord_algebraMap_restrict k F Q',
      ramificationIdx_eq_one_of_constantCompositum_eq_top (k := k) hcomp, Nat.cast_one, one_mul]) p

end Algebraic

section ArbitraryExtension

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F']
  [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
  [Algebra (RatFunc k') F'] [IsScalarTower k' (RatFunc k') F']

private theorem ord_restrict_ratFuncMapRingHom_eq_zero_of_isTrivialOn
    [Algebra.IsIntegral (RatFunc k') F']
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X) {Q' : Place k' F'}
    (hQ' : Q'.valuation.IsTrivialOn F) {r : RatFunc k} (hr : r ≠ 0) :
    (Q'.restrict k' (RatFunc k')).ord (ratFuncMapRingHom k k' r) = 0 := by
  have hf0 : algebraMap (RatFunc k) F r ≠ 0 := (_root_.map_ne_zero _).mpr hr
  have hord0 : Q'.ord (algebraMap F F' (algebraMap (RatFunc k) F r)) = 0 :=
    (Q'.ord_eq_iff_valuation_eq_exp_neg ((_root_.map_ne_zero _).mpr hf0)).mpr
      (by simp [hQ'.eq_one _ hf0])
  rw [← algebraMap_ratFuncMapRingHom hX, ord_algebraMap_restrict k' (RatFunc k') Q'] at hord0
  exact (mul_eq_zero.mp hord0).resolve_left
    (by exact_mod_cast (ramificationIdx_pos (RatFunc k') Q').ne')

/-- **At a place of `F'` trivial on `F`, every nonzero polynomial over `k` has order zero.** -/
theorem ord_restrict_algebraMap_eq_zero_of_isTrivialOn [Algebra.IsIntegral (RatFunc k') F']
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X) {Q' : Place k' F'}
    (hQ' : Q'.valuation.IsTrivialOn F) {p : k[X]} (hp : p ≠ 0) :
    (Q'.restrict k' (RatFunc k')).ord
      (algebraMap k'[X] (RatFunc k') (p.map (algebraMap k k'))) = 0 :=
  have hr : algebraMap k[X] (RatFunc k) p ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective k[X] (RatFunc k))).mpr hp
  by simpa [ratFuncMapRingHom_algebraMap] using
    ord_restrict_ratFuncMapRingHom_eq_zero_of_isTrivialOn hX hQ' hr

private theorem adjoin_ratFunc_eq_top_of_adjoin_eq_top
    (hcomp : constantCompositum F k' F' = ⊤)
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X) {y : F} (hy : (RatFunc k)⟮y⟯ = ⊤) :
    (RatFunc k')⟮algebraMap F F' y⟯ = ⊤ := by
  let _ : Algebra (RatFunc k) (RatFunc k') := (ratFuncMapRingHom k k').toAlgebra
  let _ : Algebra (RatFunc k) F' := ((algebraMap F F').comp (algebraMap (RatFunc k) F)).toAlgebra
  have : IsScalarTower (RatFunc k) F F' := .of_algebraMap_eq' rfl
  have : IsScalarTower (RatFunc k) (RatFunc k') F' :=
    .of_algebraMap_eq fun r ↦ (algebraMap_ratFuncMapRingHom hX r).symm
  have hcomp_rat : constantCompositum F (RatFunc k') F' = ⊤ :=
    eq_top_iff.mpr (hcomp ▸ (constantCompositum_le_iff F k' F').mpr fun c ↦ by
      rw [IsScalarTower.algebraMap_apply k' (RatFunc k') F']
      exact algebraMap_mem_constantCompositum F (RatFunc k') F' _)
  simpa using adjoin_image_eq_top_of_constantCompositum_eq_top
    (k := RatFunc k) (k' := RatFunc k') (S := {y}) hy hcomp_rat

/-- Places of `F' = F · k'` trivial on `F` are unramified over `k'(t)` (`F / k(t)` separable). -/
theorem ramificationIdx_ratFunc_eq_one_of_isTrivialOn [FiniteDimensional (RatFunc k) F]
    [Algebra.IsSeparable (RatFunc k) F] (hcomp : constantCompositum F k' F' = ⊤)
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X) {Q' : Place k' F'}
    (hQ' : Q'.valuation.IsTrivialOn F) :
    ramificationIdx (RatFunc k') Q' = 1 := by
  have : FiniteDimensional (RatFunc k') F' :=
    finiteDimensional_ratFunc_of_constantCompositum_eq_top hcomp hX
  obtain ⟨y, hy⟩ := Field.exists_primitive_element (RatFunc k) F
  let y' : F' := algebraMap F F' y
  have hgen : (RatFunc k')⟮y'⟯ = ⊤ := adjoin_ratFunc_eq_top_of_adjoin_eq_top hcomp hX hy
  have : Algebra.IsSeparable (RatFunc k') F' := by
    have : Algebra.IsSeparable k⟮algebraMap (RatFunc k) F RatFunc.X⟯ F :=
      isSeparable_adjoin_algebraMap_X_iff.mpr inferInstance
    have hsep' := isSeparable_adjoin_image_of_constantCompositum_eq_top (k := k) (k' := k')
      (S := {algebraMap (RatFunc k) F RatFunc.X}) hcomp
    rwa [Set.image_singleton, hX, isSeparable_adjoin_algebraMap_X_iff] at hsep'
  let p := minpoly (RatFunc k) y
  let p' := p.map (ratFuncMapRingHom k k')
  have hcomp_rh : (algebraMap (RatFunc k') F').comp (ratFuncMapRingHom k k') =
      (algebraMap F F').comp (algebraMap (RatFunc k) F) :=
    RingHom.ext (algebraMap_ratFuncMapRingHom hX)
  have hmap_eval (q : (RatFunc k)[X]) :
      aeval y' (q.map (ratFuncMapRingHom k k')) = algebraMap F F' (aeval y q) := by
    rw [aeval_def, eval₂_map, hcomp_rh,
      ← hom_eval₂ q (algebraMap (RatFunc k) F) (algebraMap F F') y, ← aeval_def]
  have hroot : aeval y' p' = 0 := by rw [hmap_eval, minpoly.aeval, map_zero]
  have hpcoeff : ∀ i, p'.coeff i ∈ (Q'.restrict k' (RatFunc k')).integers := fun i ↦ by
    rw [coeff_map]
    rcases eq_or_ne (p.coeff i) 0 with h0 | h0
    · simp [h0]
    · rw [(Q'.restrict k' (RatFunc k')).mem_integers_iff_ord_nonneg,
        ord_restrict_ratFuncMapRingHom_eq_zero_of_isTrivialOn hX hQ' h0]
  have hderiv : Q'.valuation (aeval y' (derivative p')) = 1 := by
    rw [derivative_map, hmap_eval]
    exact hQ'.eq_one _ ((Algebra.IsSeparable.isSeparable (RatFunc k) y).aeval_derivative_ne_zero
      (minpoly.aeval (RatFunc k) y))
  have hunram : Algebra.IsUnramifiedAt (Q'.restrict k' (RatFunc k')).integers
      (centerIntegralClosure k' (RatFunc k') Q').asIdeal :=
    (differentExponent_eq_zero_iff k' (RatFunc k') Q').mp
      (differentExponent_eq_zero_of_valuation_aeval_derivative_eq_one k' (RatFunc k') hgen
        ((minpoly.monic (Algebra.IsSeparable.isIntegral (RatFunc k) y)).map _) hpcoeff hroot hderiv)
  rw [ramificationIdx_eq_ramificationIdx_center (R := (Q'.restrict k' (RatFunc k')).integers)
    k' (RatFunc k') Q' (algebraMap_mem_integers_of_mem_integralClosure k' (RatFunc k') Q'),
    ← centerIntegralClosure_def]
  exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt

/-- Extending constants by an arbitrary extension preserves ramification over `k(t)` at contracting
places (`k` perfect and exact in `F`). -/
theorem ramificationIdx_ratFunc_eq_of_integers_comap_eq [PerfectField k]
    [FiniteDimensional (RatFunc k) F]
    (hex : IsIntegrallyClosedIn k F) (hcomp : constantCompositum F k' F' = ⊤)
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X) {Q : Place k F} {Q' : Place k' F'}
    (hQ' : Q'.integers.comap (algebraMap F F') = Q.integers) :
    ramificationIdx (RatFunc k') Q' = ramificationIdx (RatFunc k) Q := by
  have : FiniteDimensional (RatFunc k') F' :=
    finiteDimensional_ratFunc_of_constantCompositum_eq_top hcomp hX
  have hF : IsFunctionField k F := (IsFunctionField.ratFunc k).finite_extension
  exact ramificationIdx_ratFunc_eq_of_ord_algebraMap_eq hX
    (ord_algebraMap_eq_of_integers_comap_eq hF hex hcomp hQ')

/-- Extending constants preserves orders of polynomials over `k` at contracting places (`k` perfect
and exact in `F`). -/
theorem ord_restrict_algebraMap_eq_of_integers_comap_eq [PerfectField k]
    [FiniteDimensional (RatFunc k) F] [Algebra.IsIntegral (RatFunc k') F']
    (hex : IsIntegrallyClosedIn k F) (hcomp : constantCompositum F k' F' = ⊤)
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X) {Q : Place k F} {Q' : Place k' F'}
    (hQ' : Q'.integers.comap (algebraMap F F') = Q.integers) (p : k[X]) :
    (Q.restrict k (RatFunc k)).ord (algebraMap k[X] (RatFunc k) p) =
      (Q'.restrict k' (RatFunc k')).ord
        (algebraMap k'[X] (RatFunc k') (p.map (algebraMap k k'))) :=
  ord_restrict_algebraMap_eq_of_ord_algebraMap_eq hX
    (ord_algebraMap_eq_of_integers_comap_eq (IsFunctionField.ratFunc k).finite_extension
      hex hcomp hQ') p

end ArbitraryExtension

end Place

end TauCeti
