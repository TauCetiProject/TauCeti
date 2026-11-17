/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.ConstantExtension.Basic
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Basic
import TauCeti.FieldTheory.FunctionField.ConstantExtension.Unramified
import TauCeti.FieldTheory.FunctionField.Place.RatFunc.Order
import TauCeti.FieldTheory.RatFunc.Map

/-!
# Ramification over the rational function field after extending constants

Let `F` be a field over `k(t)` and let `F'` be a field over `k'(t)` extending `F` and `k'`, where
`k` is a perfect field and `t` acts on `F'` as it does on `F`. Geometrically, `F / k(t)` is a
finite map from a curve to the projective line, and when `F' = F · k'` the extension `F' / k'(t)` is
its base change to `k'`.

Without assuming `F' / F` is integral or `k' / k` is algebraic, comparing the orders at a place
`Q'` of `F'` nontrivial on `F` (`ramificationIdx F Q' ≠ 0`) of a polynomial in `t` over `k`
computed through `F` and through `k'(t)` gives
`e(Q' ∣ k'(t)) = e(Q' ∣ F) · e(Q ∣ k(t))`
(`TauCeti.Place.ramificationIdx_ratFunc_eq_mul_of_ramificationIdx_ne_zero`), where
`Q = Q'.restrictOfRamificationIdxNeZero k h`. At the place at infinity the polynomial `t` has
a simple pole on both sides. At the place of an irreducible `q` the polynomial `q` has order one,
and it has order at most one at every finite place of `k'(t)`, because `q` stays squarefree over
`k'`, `k` being perfect. Cancelling the common nonzero ramification factor shows that the place of
`k(t)` below `Q` and the place of `k'(t)` below `Q'` give every polynomial over `k` the same order
(`TauCeti.Place.ord_restrict_algebraMap_eq_of_ramificationIdx_ne_zero`).

When `F' = F · k'` for a separable algebraic constant extension `k' / k`, the constant field
extension `F' / F` is unramified
(`TauCeti.Place.ramificationIdx_eq_one_of_constantCompositum_eq_top`), so the factor `e(Q' ∣ F)` is
`1` and `e(Q' ∣ k'(t)) = e(Q ∣ k(t))`. For a Belyi map this is what makes being unramified outside
`t = 0`, `t = 1` and `t = ∞` invariant under extension of the constant field
(`TauCeti.isAlgebraicBelyiPair_iff_of_constantCompositum_eq_top`).

## Main results

* `TauCeti.Place.ramificationIdx_ratFunc_eq_mul_of_ramificationIdx_ne_zero`:
  `e(Q' ∣ k'(t)) = e(Q' ∣ F) · e(Q ∣ k(t))` for any place `Q'` nontrivial on `F`.
* `TauCeti.Place.ord_restrict_algebraMap_eq_of_ramificationIdx_ne_zero`: the places of `k(t)` and
  `k'(t)` below a place `Q'` nontrivial on `F` give every polynomial over `k` the same order.
* `TauCeti.Place.ramificationIdx_ratFunc_eq_of_constantCompositum_eq_top`:
  `e(Q' ∣ k'(t)) = e(Q ∣ k(t))` for an algebraic separable constant extension `F' = F · k'`.
* `TauCeti.Place.ord_restrict_algebraMap_eq_of_constantCompositum_eq_top`: the integral-extension
  form comparing orders of polynomials over `k`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Proposition 3.1.6 and Theorem 3.6.3.
-/

public section

open Polynomial

namespace TauCeti

namespace Place

section General

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F']
  [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [Algebra.IsIntegral (RatFunc k) F]
  [Algebra (RatFunc k') F'] [IsScalarTower k' (RatFunc k') F']
  [Algebra.IsIntegral (RatFunc k') F']

/-- The order at `Q'` of a polynomial in `t`, computed through `F` and through `k'(t)`,
for any place `Q'` nontrivial on `F`. -/
private theorem ramificationIdx_mul_ord_eq_of_ramificationIdx_ne_zero
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X)
    {Q' : Place k' F'} (h : ramificationIdx F Q' ≠ 0) (p : k[X]) :
    (ramificationIdx F Q' * ramificationIdx (RatFunc k)
        (Q'.restrictOfRamificationIdxNeZero k h) : ℤ) *
        ((Q'.restrictOfRamificationIdxNeZero k h).restrict k (RatFunc k)).ord
          (algebraMap k[X] (RatFunc k) p) =
      ramificationIdx (RatFunc k') Q' * (Q'.restrict k' (RatFunc k')).ord
        (algebraMap k'[X] (RatFunc k') (p.map (algebraMap k k'))) := by
  set Q := Q'.restrictOfRamificationIdxNeZero k h
  calc
    (ramificationIdx F Q' * ramificationIdx (RatFunc k) Q : ℤ) *
        (Q.restrict k (RatFunc k)).ord (algebraMap k[X] (RatFunc k) p)
      = (ramificationIdx F Q' : ℤ) *
          ((ramificationIdx (RatFunc k) Q : ℤ) *
            (Q.restrict k (RatFunc k)).ord (algebraMap k[X] (RatFunc k) p)) := by
          ring
    _ = (ramificationIdx F Q' : ℤ) *
          Q.ord (algebraMap (RatFunc k) F (algebraMap k[X] (RatFunc k) p)) := by
          rw [← ord_algebraMap_restrict k (RatFunc k) Q]
    _ = Q'.ord (algebraMap F F' (algebraMap (RatFunc k) F (algebraMap k[X] (RatFunc k) p))) :=
          (ord_algebraMap_restrictOfRamificationIdxNeZero (k := k) Q' h _).symm
    _ = Q'.ord (algebraMap (RatFunc k') F'
          (algebraMap k'[X] (RatFunc k') (p.map (algebraMap k k')))) := by
          rw [algebraMap_algebraMap_polynomial hX]
    _ = ramificationIdx (RatFunc k') Q' * (Q'.restrict k' (RatFunc k')).ord
          (algebraMap k'[X] (RatFunc k') (p.map (algebraMap k k'))) :=
          ord_algebraMap_restrict k' (RatFunc k') Q' _

variable [PerfectField k]

/-- **Multiplicativity of ramification over the line for arbitrary constant extensions**: over a
perfect field `k`, if `t` acts on `F'` as it does on `F`, then any place `Q'` of `F'` nontrivial on
`F` satisfies `e(Q' ∣ k'(t)) = e(Q' ∣ F) · e(Q ∣ k(t))`, where `Q` is its normalized restriction
to `F`. Neither `F' / F` integral nor `F' = F · k'` is required. -/
theorem ramificationIdx_ratFunc_eq_mul_of_ramificationIdx_ne_zero
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X)
    {Q' : Place k' F'} (h : ramificationIdx F Q' ≠ 0) :
    ramificationIdx (RatFunc k') Q' =
      ramificationIdx F Q' * ramificationIdx (RatFunc k)
        (Q'.restrictOfRamificationIdxNeZero k h) := by
  set Q := Q'.restrictOfRamificationIdxNeZero k h
  set e : ℕ := ramificationIdx F Q' * ramificationIdx (RatFunc k) Q
  have he : 0 < e := Nat.mul_pos (Nat.pos_of_ne_zero h) (ramificationIdx_pos (RatFunc k) Q)
  have hord (p : k[X]) :
      (e : ℤ) * (Q.restrict k (RatFunc k)).ord (algebraMap k[X] (RatFunc k) p) =
        ramificationIdx (RatFunc k') Q' * (Q'.restrict k' (RatFunc k')).ord
          (algebraMap k'[X] (RatFunc k') (p.map (algebraMap k k'))) := by
    simpa only [e, Nat.cast_mul] using
      ramificationIdx_mul_ord_eq_of_ramificationIdx_ne_zero hX h p
  rcases eq_infty_or_exists_eq_adicOfIrreducible (Q.restrict k (RatFunc k)) with
    hP | ⟨q, hq, hP⟩
  · -- At infinity `t` has a simple pole, below `Q'` in `k(t)` and hence also in `k'(t)`.
    have h1 := hord X
    rw [Polynomial.map_X, RatFunc.algebraMap_X, RatFunc.algebraMap_X, hP, ord_infty,
      RatFunc.intDegree_X] at h1
    have hP' : Q'.restrict k' (RatFunc k') = infty k' := by
      refine X_notMem_integers_iff_eq_infty.mp fun hmem ↦ ?_
      have := (Q'.restrict k' (RatFunc k')).mem_integers_iff_ord_nonneg.mp hmem
      nlinarith
    rw [hP', ord_infty, RatFunc.intDegree_X] at h1
    omega
  -- At the place of `q`, the order of `q` is one, and `q` stays squarefree over `k'`.
  have h1 := hord q
  rw [hP, ord_adicOfIrreducible_algebraMap_irreducible hq hq, ite_eq_left (Associated.refl q),
    mul_one] at h1
  have hsq : Squarefree (q.map (algebraMap k k')) :=
    (PerfectField.separable_of_irreducible hq).map.squarefree
  rcases eq_infty_or_exists_eq_adicOfIrreducible (Q'.restrict k' (RatFunc k')) with
    hP' | ⟨q', hq', hP'⟩
  · rw [hP', ord_infty, RatFunc.intDegree_polynomial] at h1
    nlinarith
  rw [hP', ord_adicOfIrreducible_algebraMap_of_squarefree hq' hsq] at h1
  split_ifs at h1 <;> omega

/-- **Polynomial orders at places nontrivial on `F`**: over a perfect field `k`, if `t` acts on `F'`
as it does on `F`, then for any place `Q'` of `F'` nontrivial on `F`, the place of `k(t)` below
`Q'.restrictOfRamificationIdxNeZero k h` and the place of `k'(t)` below `Q'` give every polynomial
in `t` over `k` the same order. Neither `F' / F` integral nor `F' = F · k'` is required. -/
theorem ord_restrict_algebraMap_eq_of_ramificationIdx_ne_zero
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X)
    {Q' : Place k' F'} (h : ramificationIdx F Q' ≠ 0) (p : k[X]) :
    ((Q'.restrictOfRamificationIdxNeZero k h).restrict k (RatFunc k)).ord
        (algebraMap k[X] (RatFunc k) p) =
      (Q'.restrict k' (RatFunc k')).ord
        (algebraMap k'[X] (RatFunc k') (p.map (algebraMap k k'))) := by
  have h1 := ramificationIdx_mul_ord_eq_of_ramificationIdx_ne_zero hX h p
  have hmul := ramificationIdx_ratFunc_eq_mul_of_ramificationIdx_ne_zero hX h
  have hpos : (ramificationIdx (RatFunc k') Q' : ℤ) ≠ 0 := by
    exact_mod_cast (ramificationIdx_pos (RatFunc k') Q').ne'
  rw [← Nat.cast_mul, ← hmul] at h1
  exact mul_left_cancel₀ hpos h1

end General

section Integral

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
    ramificationIdx (RatFunc k') Q' = ramificationIdx (RatFunc k) (Q'.restrict k F) := by
  have hne : ramificationIdx F Q' ≠ 0 := (ramificationIdx_pos F Q').ne'
  rw [ramificationIdx_ratFunc_eq_mul_of_ramificationIdx_ne_zero hX hne,
    ramificationIdx_eq_one_of_constantCompositum_eq_top (k := k) hcomp,
    restrictOfRamificationIdxNeZero_eq_restrict, one_mul]

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
        (algebraMap k'[X] (RatFunc k') (p.map (algebraMap k k'))) := by
  have hne : ramificationIdx F Q' ≠ 0 := (ramificationIdx_pos F Q').ne'
  have h1 := ramificationIdx_mul_ord_eq_of_ramificationIdx_ne_zero hX hne p
  rw [ramificationIdx_eq_one_of_constantCompositum_eq_top (k := k) hcomp,
    restrictOfRamificationIdxNeZero_eq_restrict, Nat.cast_one, one_mul,
    ramificationIdx_ratFunc_eq_of_constantCompositum_eq_top hcomp hX Q'] at h1
  exact mul_left_cancel₀ (by exact_mod_cast (ramificationIdx_pos _ _).ne') h1

end Integral

end Place

end TauCeti
