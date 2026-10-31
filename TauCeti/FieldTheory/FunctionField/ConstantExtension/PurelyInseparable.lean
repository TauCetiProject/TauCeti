/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.KummerPolynomial
public import TauCeti.FieldTheory.FunctionField.ConstantExtension.RatFunc
public import TauCeti.FieldTheory.FunctionField.Divisor.Conorm
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Unramified
import TauCeti.Algebra.Polynomial.XPowSubC

/-!
# Ramification in an inseparable constant field extension

Over a perfect constant field, extending the constants never ramifies a place and never makes a
residue extension inseparable. Over an imperfect field both fail, and they fail independently.
This file proves both failures on the rational function field.

Let `k` have characteristic `p`, let `a ∈ k` not be a `p`-th power, and let `K` be an extension
of `k` containing a root `α` of `X ^ p - a`. Embed `k(t)` in `K(t)` by `t ↦ t`.

* At the place `P` of `k(t)` where `t ^ p - a` vanishes, a place of degree `p`, the extension is
  **ramified although the field `K(t)` is a constant extension**: `t ^ p - a = (t - α) ^ p` in
  `K[t]`, so the place `Q` of `t - α` is the only place over `P`, with `e(Q ∣ P) = p` and
  `Con P = p Q`.
* At the rational place `P₀` where `t` vanishes, and likewise where `t - c` vanishes for any
  `c ∈ k`, the place `Q₀` of `t - c` in `K(t)` is the only place above it, with
  `e(Q₀ ∣ P₀) = 1` and `Con P₀ = Q₀`
  (`TauCeti.Place.restrict_eq_adicOfIrreducible_X_sub_C_iff`,
  `TauCeti.Place.ramificationIdx_adicOfIrreducible_X_sub_C_algebraMap` and
  `TauCeti.Place.conorm_ofPoint_adicOfIrreducible_X_sub_C`), and `deg Q₀ = deg P₀ = 1`
  (`TauCeti.Place.degree_adicOfIrreducible_X_sub_C`). Yet the residue extension is `K / k`, which
  contains the purely inseparable `α`, so **`P₀` is not unramified**
  (`TauCeti.Place.not_isUnramified_of_degree_eq_one`).

The two places separate the two ways a constant extension can fail to be unramified: a
ramification index above one, and an inseparable residue extension with index one. The underlying
model, the projective line, is smooth and its genus stays zero, so neither phenomenon is detected
by the smoothness of the model or by the genus.

## Main results

* `TauCeti.Place.restrict_eq_adicOfIrreducible_X_pow_sub_C_iff`: the place of `t - α` is the only
  place of `K(t)` over the place of `t ^ p - a`.
* `TauCeti.Place.ramificationIdx_adicOfIrreducible_X_sub_C_of_pow_eq`: its ramification index is
  `p`.
* `TauCeti.Place.conorm_ofPoint_adicOfIrreducible_X_pow_sub_C`: `Con P = p Q`.
* `TauCeti.Place.not_isUnramified_adicOfIrreducible_X_sub_C_of_pow_eq`: the place of `t - c` in
  `k(t)` is not unramified in `K(t)`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Theorem 3.6.3, which assumes `k` perfect; the example shows that part (a) of that theorem,
  unramifiedness, needs this assumption.
-/

public section

open Polynomial

namespace TauCeti

namespace Place

/-! ### The example on the rational function field -/

section RatFunc

variable {k K : Type*} [Field k] [Field K] [Algebra k K]
variable [Algebra (RatFunc k) (RatFunc K)] [IsScalarTower k (RatFunc k) (RatFunc K)]
variable [Algebra.IsIntegral (RatFunc k) (RatFunc K)]

/-! #### Rational places: an inseparable residue extension -/

variable {p : ℕ} [Fact p.Prime] [CharP k p] {a : k} {α : K}

/-- **A rational finite place of `k(t)` is not unramified in `K(t)`** when `K` contains a `p`-th
root `α` of an element `a` that is not a `p`-th power in `k`: the residue extension at the place
of `t - c` in `K(t)` is `K / k`, which is not separable. This holds for every embedding of `k(t)`
in `K(t)`; when the embedding sends `t` to `t`, the ramification index there is moreover `e = 1`
(`TauCeti.Place.ramificationIdx_adicOfIrreducible_X_sub_C_algebraMap`). -/
theorem not_isUnramified_adicOfIrreducible_X_sub_C_of_pow_eq (c : k) (ha : ∀ c : k, c ^ p ≠ a)
    (hα : α ^ p = algebraMap k K a) :
    ¬ (adicOfIrreducible (irreducible_X_sub_C c)).IsUnramified (k' := K) (F' := RatFunc K) := by
  have : ExpChar k p := ExpChar.prime Fact.out
  refine not_isUnramified_of_degree_eq_one (by simp) p ?_ (n := 1) ⟨a, by rw [pow_one, hα]⟩
  rintro ⟨d, rfl⟩
  exact ha d ((algebraMap k K).injective (by rw [map_pow, hα]))

/-! #### The place of `t ^ p - a`: ramification without a separable extension of the field -/

/-- The place of `t - α` in `K(t)` lies over the place of `t ^ p - a` in `k(t)`. -/
theorem restrict_adicOfIrreducible_X_sub_C_of_pow_eq
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X) (ha : ∀ c : k, c ^ p ≠ a)
    (hα : α ^ p = algebraMap k K a) :
    (adicOfIrreducible (irreducible_X_sub_C α)).restrict k (RatFunc k) =
      adicOfIrreducible (X_pow_sub_C_irreducible_of_prime Fact.out ha) := by
  have := expChar_of_injective_algebraMap (algebraMap k K).injective p
  rw [restrict_adicOfIrreducible_eq_iff hX, map_X_pow_sub_C_eq_X_sub_C_pow p hα]
  exact dvd_pow_self _ (Fact.out : p.Prime).ne_zero

/-- **The place of `t - α` is the only place of `K(t)` over the place of `t ^ p - a`.** -/
theorem restrict_eq_adicOfIrreducible_X_pow_sub_C_iff
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X) (ha : ∀ c : k, c ^ p ≠ a)
    (hα : α ^ p = algebraMap k K a) (Q : Place K (RatFunc K)) :
    Q.restrict k (RatFunc k) = adicOfIrreducible (X_pow_sub_C_irreducible_of_prime Fact.out ha) ↔
      Q = adicOfIrreducible (irreducible_X_sub_C α) := by
  have := expChar_of_injective_algebraMap (algebraMap k K).injective p
  rw [restrict_eq_adicOfIrreducible_iff hX, map_X_pow_sub_C_eq_X_sub_C_pow p hα]
  constructor
  · rintro ⟨q', hq', hdvd, rfl⟩
    exact (adicOfIrreducible_eq_adicOfIrreducible_iff hq' (irreducible_X_sub_C α)).mpr
      (hq'.associated_of_dvd (irreducible_X_sub_C α) (hq'.prime.dvd_of_dvd_pow hdvd))
  · rintro rfl
    exact ⟨X - C α, irreducible_X_sub_C α, dvd_pow_self _ (Fact.out : p.Prime).ne_zero, rfl⟩

/-- **The place of `t ^ p - a` ramifies in the constant extension `K(t) / k(t)`**: the place of
`t - α` above it has ramification index `e = p`. -/
theorem ramificationIdx_adicOfIrreducible_X_sub_C_of_pow_eq
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X) (ha : ∀ c : k, c ^ p ≠ a)
    (hα : α ^ p = algebraMap k K a) :
    ramificationIdx (RatFunc k) (adicOfIrreducible (irreducible_X_sub_C α)) = p := by
  have := expChar_of_injective_algebraMap (algebraMap k K).injective p
  have hmap := map_X_pow_sub_C_eq_X_sub_C_pow p hα
  rw [ramificationIdx_adicOfIrreducible_eq_multiplicity hX (irreducible_X_sub_C α)
    (X_pow_sub_C_irreducible_of_prime Fact.out ha)
    (hmap ▸ dvd_pow_self _ (Fact.out : p.Prime).ne_zero),
    hmap, multiplicity_pow_self (X_sub_C_ne_zero α) (not_isUnit_X_sub_C α)]

/-- **The conorm of the place of `t ^ p - a` is `p` times the place of `t - α`.** -/
theorem conorm_ofPoint_adicOfIrreducible_X_pow_sub_C
    [∀ P : Place k (RatFunc k), Finite {Q : Place K (RatFunc K) // Q.restrict k (RatFunc k) = P}]
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X) (ha : ∀ c : k, c ^ p ≠ a)
    (hα : α ^ p = algebraMap k K a) :
    Divisor.conorm K (RatFunc K) (AlgebraicGeometry.WeilDivisor.ofPoint
        (adicOfIrreducible (X_pow_sub_C_irreducible_of_prime Fact.out ha))) =
      (p : ℤ) •
        AlgebraicGeometry.WeilDivisor.ofPoint (adicOfIrreducible (irreducible_X_sub_C α)) := by
  refine AlgebraicGeometry.WeilDivisor.ext fun Q ↦ ?_
  rw [Divisor.coeff_conorm, AlgebraicGeometry.WeilDivisor.coeff_zsmul]
  by_cases hQ : Q = adicOfIrreducible (irreducible_X_sub_C α)
  · rw [hQ, restrict_adicOfIrreducible_X_sub_C_of_pow_eq hX ha hα,
      ramificationIdx_adicOfIrreducible_X_sub_C_of_pow_eq hX ha hα,
      AlgebraicGeometry.WeilDivisor.coeff_ofPoint_self,
      AlgebraicGeometry.WeilDivisor.coeff_ofPoint_self]
  · rw [AlgebraicGeometry.WeilDivisor.coeff_ofPoint_of_ne
      (mt (restrict_eq_adicOfIrreducible_X_pow_sub_C_iff hX ha hα Q).mp hQ),
      AlgebraicGeometry.WeilDivisor.coeff_ofPoint_of_ne hQ, mul_zero, mul_zero]

end RatFunc

end Place

end TauCeti
