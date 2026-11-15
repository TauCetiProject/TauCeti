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

/-!
# Ramification over the rational function field after extending constants

Let `F` be a field over `k(t)` and let `F' = F · k'` be its compositum with an algebraic
extension `k' / k` of a perfect field, finite or not, carrying the `k'(t)`-algebra structure in
which `t` acts as it does on `F`. Geometrically, `F / k(t)` is a finite map from a curve to the
projective line, and `F' / k'(t)` is its base change to `k'`. This file shows that base change
does not change ramification over the line: a place `Q'` of `F'` has the same ramification index
over `k'(t)` as the place `Q` of `F` below it has over `k(t)`, and the place of `k'(t)` below `Q'`
gives every polynomial in `t` with coefficients in `k` the same order as the place of `k(t)`
below `Q`.

Both statements come from comparing the orders at `Q'` of a polynomial in `t` computed through
`F` and through `k'(t)`. The constant field extension `F' / F` is unramified
(`TauCeti.Place.ramificationIdx_eq_one_of_constantCompositum_eq_top`), so through `F` the order is
`e(Q ∣ k(t))` times the order at the place of `k(t)` below `Q`, and through `k'(t)` it is
`e(Q' ∣ k'(t))` times the order at the place of `k'(t)` below `Q'`. At the place at infinity the
polynomial `t` has a simple pole on both sides. At the place of an irreducible `q` the polynomial
`q` has order one, and it has order at most one at every finite place of `k'(t)`, because `q`
stays squarefree over `k'`, `k` being perfect.

For a Belyi map this is what makes being unramified outside `t = 0`, `t = 1` and `t = ∞`
invariant under extension of the constant field
(`TauCeti.isAlgebraicBelyiPair_iff_of_constantCompositum_eq_top`).

## Main results

* `TauCeti.Place.ramificationIdx_ratFunc_eq_of_constantCompositum_eq_top`:
  `e(Q' ∣ k'(t)) = e(Q ∣ k(t))`.
* `TauCeti.Place.ord_restrict_algebraMap_eq_of_constantCompositum_eq_top`: the places of `k(t)`
  and `k'(t)` below `Q'` give a polynomial over `k` the same order.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Proposition 3.1.6 and Theorem 3.6.3.
-/

public section

open Polynomial

namespace TauCeti

namespace Place

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F']
  [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [Algebra.IsIntegral (RatFunc k) F]
  [Algebra (RatFunc k') F'] [IsScalarTower k' (RatFunc k') F']
  [Algebra.IsIntegral (RatFunc k') F'] [Algebra.IsIntegral F F']

omit [Algebra.IsIntegral (RatFunc k) F] [Algebra.IsIntegral (RatFunc k') F']
  [Algebra.IsIntegral F F'] in
/-- A polynomial in `t` over `k` has the same image in `F'` through `F` as through `k'(t)`. -/
private theorem algebraMap_algebraMap_polynomial
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X) (p : k[X]) :
    algebraMap F F' (algebraMap (RatFunc k) F (algebraMap k[X] (RatFunc k) p)) =
      algebraMap (RatFunc k') F' (algebraMap k'[X] (RatFunc k') (p.map (algebraMap k k'))) := by
  have h₁ := aeval_algHom_apply
    ((IsScalarTower.toAlgHom k F F').comp (IsScalarTower.toAlgHom k (RatFunc k) F)) RatFunc.X p
  have h₂ := aeval_algHom_apply (IsScalarTower.toAlgHom k' (RatFunc k') F') RatFunc.X
    (p.map (algebraMap k k'))
  simp only [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply,
    RatFunc.aeval_X_left_eq_algebraMap] at h₁ h₂
  rw [← h₁, ← h₂, hX, aeval_map_algebraMap]

variable [Algebra.IsSeparable k k']

/-- The order at `Q'` of a polynomial in `t`, computed through `F` and through `k'(t)`. -/
private theorem ramificationIdx_mul_ord_eq (hcomp : constantCompositum F k' F' = ⊤)
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X) (Q' : Place k' F') (p : k[X]) :
    (ramificationIdx (RatFunc k) (Q'.restrict k F) : ℤ) *
        ((Q'.restrict k F).restrict k (RatFunc k)).ord (algebraMap k[X] (RatFunc k) p) =
      ramificationIdx (RatFunc k') Q' * (Q'.restrict k' (RatFunc k')).ord
        (algebraMap k'[X] (RatFunc k') (p.map (algebraMap k k'))) := by
  rw [← ord_algebraMap_restrict k (RatFunc k) (Q'.restrict k F),
    ← ord_algebraMap_restrict k' (RatFunc k') Q', ← algebraMap_algebraMap_polynomial hX,
    ord_algebraMap_restrict k F Q',
    ramificationIdx_eq_one_of_constantCompositum_eq_top (k := k) hcomp,
    Nat.cast_one, one_mul]

variable [PerfectField k]

/-- **Extending constants does not change ramification over the line**: if `F' = F · k'` for an
algebraic extension `k' / k` of a perfect field and `t` acts on `F'` as it does on `F`, then every
place `Q'` of `F'` has the same ramification index over `k'(t)` as the place of `F` below it has
over `k(t)`. -/
theorem ramificationIdx_ratFunc_eq_of_constantCompositum_eq_top
    (hcomp : constantCompositum F k' F' = ⊤)
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X) (Q' : Place k' F') :
    ramificationIdx (RatFunc k') Q' = ramificationIdx (RatFunc k) (Q'.restrict k F) := by
  have he := ramificationIdx_pos (RatFunc k) (Q'.restrict k F)
  have hord := ramificationIdx_mul_ord_eq hcomp hX Q'
  rcases eq_infty_or_exists_eq_adicOfIrreducible ((Q'.restrict k F).restrict k (RatFunc k)) with
    hP | ⟨q, hq, hP⟩
  · -- At infinity `t` has a simple pole, below `Q'` in `k(t)` and hence also in `k'(t)`.
    have h := hord X
    rw [Polynomial.map_X, RatFunc.algebraMap_X, RatFunc.algebraMap_X, hP, ord_infty,
      RatFunc.intDegree_X] at h
    have hP' : Q'.restrict k' (RatFunc k') = infty k' := by
      refine X_notMem_integers_iff_eq_infty.mp fun hmem ↦ ?_
      have := (Q'.restrict k' (RatFunc k')).mem_integers_iff_ord_nonneg.mp hmem
      nlinarith
    rw [hP', ord_infty, RatFunc.intDegree_X] at h
    omega
  -- At the place of `q`, the order of `q` is one, and `q` stays squarefree over `k'`.
  have h := hord q
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
  have h := ramificationIdx_mul_ord_eq hcomp hX Q' p
  rw [ramificationIdx_ratFunc_eq_of_constantCompositum_eq_top hcomp hX Q'] at h
  exact mul_left_cancel₀ (by exact_mod_cast (ramificationIdx_pos _ _).ne') h

end Place

end TauCeti
