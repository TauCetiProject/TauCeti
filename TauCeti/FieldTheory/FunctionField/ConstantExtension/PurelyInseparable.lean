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
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure

/-!
# Ramification in an inseparable constant field extension

Over a perfect constant field, extending the constants never ramifies a place and never makes a
residue extension inseparable. Over an imperfect field both fail, and they fail independently.
This file proves both failures on the rational function field, and the general fact behind the
second one.

**Inseparable residue extensions.** Let `P'` be a place of `F' / k'` over a place `P` of `F / k`
of degree one, and suppose that `k'` contains an element `α ∉ k` with `α ^ (q ^ n) ∈ k`, where
`q` is the exponential characteristic. Then the residue extension `F'_{P'} / F_P` is not
separable: `F_P` is `k`, and the residue of `α` would be separable over `k` and purely inseparable
over it, hence in `k`. In particular `P` is not unramified in `F'` in the sense of
`TauCeti.Place.IsUnramified`, even when `e(P' ∣ P) = 1`.

**The example.** Let `k` have characteristic `p`, let `a ∈ k` not be a `p`-th power, and let `K`
be an extension of `k` containing a root `α` of `X ^ p - a`. Embed `k(t)` in `K(t)` by `t ↦ t`.

* At the place `P` of `k(t)` where `t ^ p - a` vanishes, a place of degree `p`, the extension is
  **ramified although the field `K(t)` is a constant extension**: `t ^ p - a = (t - α) ^ p` in
  `K[t]`, so the place `Q` of `t - α` is the only place over `P`, with `e(Q ∣ P) = p` and
  `Con P = p Q`.
* At the rational place `P₀` where `t` vanishes, and likewise where `t - c` vanishes for any
  `c ∈ k`, the place `Q₀` of `t - c` in `K(t)` is the only place above it, with
  `e(Q₀ ∣ P₀) = 1`, `Con P₀ = Q₀` and `deg Q₀ = deg P₀ = 1`
  (`TauCeti.Place.degree_adicOfIrreducible_X_sub_C`). Yet the residue extension is `K / k`, which
  contains the purely inseparable `α`, so **`P₀` is not unramified**.

The two places separate the two ways a constant extension can fail to be unramified: a
ramification index above one, and an inseparable residue extension with index one. The underlying
model, the projective line, is smooth and its genus stays zero, so neither phenomenon is detected
by the smoothness of the model or by the genus.

## Main results

* `TauCeti.Place.not_isSeparable_residueField_of_degree_eq_one`: over a rational place, the
  residue extension is not separable once the constants contain a purely inseparable element
  outside `k`.
* `TauCeti.Place.not_isUnramified_of_degree_eq_one`: such a rational place is not unramified.
* `TauCeti.Place.restrict_eq_adicOfIrreducible_X_pow_sub_C_iff`: the place of `t - α` is the only
  place of `K(t)` over the place of `t ^ p - a`.
* `TauCeti.Place.ramificationIdx_adicOfIrreducible_X_sub_C_of_pow_eq`: its ramification index is
  `p`.
* `TauCeti.Place.conorm_ofPoint_adicOfIrreducible_X_pow_sub_C`: `Con P = p Q`.
* `TauCeti.Place.restrict_eq_adicOfIrreducible_X_sub_C_iff`,
  `TauCeti.Place.ramificationIdx_adicOfIrreducible_X_sub_C_algebraMap` and
  `TauCeti.Place.conorm_ofPoint_adicOfIrreducible_X_sub_C`: for `c ∈ k`, the place of `t - c` in
  `K(t)` is the only place over the place of `t - c` in `k(t)`, with `e = 1` and `Con P₀ = Q₀`.
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

/-! ### Inseparable residue extensions over a rational place -/

section Residue

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k' F'] [Algebra F F'] [Algebra k F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F'] [Algebra.IsIntegral F F']

/-- A constant of `k`, reduced at the place below `P'` and carried up to `F'_{P'}`, is the
residue at `P'` of the same constant seen in `k'`. -/
private theorem algebraMap_residueField_algebraMap (P' : Place k' F') (c : k) :
    algebraMap (P'.restrict k F).ResidueField P'.ResidueField
        (algebraMap k (P'.restrict k F).ResidueField c) =
      algebraMap k' P'.ResidueField (algebraMap k k' c) := by
  rw [algebraMap_residueField (R := k), algebraMap_residueField (R := k'),
    IsLocalRing.ResidueField.algebraMap_residue]
  congr 1
  apply Subtype.ext
  rw [coe_algebraMap_integers, coe_algebraMap_constants, coe_algebraMap_constants,
    ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

/-- **A purely inseparable constant makes the residue extension at a rational place
inseparable**: if `P'` lies over a place of degree one and `k'` contains `α ∉ k` with
`α ^ (q ^ n) ∈ k`, where `q` is the exponential characteristic of `k`, then `F'_{P'}` is not
separable over the residue field of the place below. -/
theorem not_isSeparable_residueField_of_degree_eq_one (P' : Place k' F')
    (hP : (P'.restrict k F).degree = 1) (q : ℕ) [ExpChar k q] {α : k'}
    (hα : α ∉ (algebraMap k k').range) {n : ℕ} (hn : α ^ q ^ n ∈ (algebraMap k k').range) :
    ¬ Algebra.IsSeparable (P'.restrict k F).ResidueField P'.ResidueField := by
  -- The residue of `α` would lie in the perfect closure of `F_P = k`, hence in `F_P = k`.
  intro hsep
  set S := (P'.restrict k F).ResidueField
  have := expChar_of_injective_algebraMap (algebraMap k S).injective q
  obtain ⟨c, hc⟩ := hn
  have hmem : algebraMap k' P'.ResidueField α ∈ perfectClosure S P'.ResidueField := by
    rw [mem_perfectClosure_iff_pow_mem q]
    exact ⟨n, algebraMap k S c, by rw [algebraMap_residueField_algebraMap, hc, map_pow]⟩
  rw [perfectClosure.eq_bot_of_isSeparable, IntermediateField.mem_bot] at hmem
  obtain ⟨s, hs⟩ := hmem
  obtain ⟨d, rfl⟩ := (degree_eq_one_iff_algebraMap_surjective _).mp hP s
  rw [algebraMap_residueField_algebraMap] at hs
  exact hα ⟨d, (algebraMap k' P'.ResidueField).injective hs⟩

/-- **A rational place is not unramified in a purely inseparable extension of constants**: if `P`
has degree one and `k'` contains `α ∉ k` with `α ^ (q ^ n) ∈ k`, then `P` is not unramified in
`F' / k'`, whatever the ramification indices are. -/
theorem not_isUnramified_of_degree_eq_one {P : Place k F} (hP : P.degree = 1) (q : ℕ)
    [ExpChar k q] {α : k'} (hα : α ∉ (algebraMap k k').range) {n : ℕ}
    (hn : α ^ q ^ n ∈ (algebraMap k k').range) :
    ¬ P.IsUnramified (k' := k') (F' := F') := by
  intro hU
  obtain ⟨P', hP'⟩ := hU.exists_restrict_eq
  exact not_isSeparable_residueField_of_degree_eq_one P' (hP' ▸ hP) q hα hn
    (hU.isSeparable hP')

end Residue

/-! ### The example on the rational function field -/

section RatFunc

variable {k K : Type*} [Field k] [Field K] [Algebra k K]
variable [Algebra (RatFunc k) (RatFunc K)] [IsScalarTower k (RatFunc k) (RatFunc K)]
variable [Algebra.IsIntegral (RatFunc k) (RatFunc K)]

/-! #### Rational places: unramified index, inseparable residue extension -/

omit [Algebra (RatFunc k) (RatFunc K)] [IsScalarTower k (RatFunc k) (RatFunc K)]
  [Algebra.IsIntegral (RatFunc k) (RatFunc K)] in
/-- In `K[t]`, the image of `t - c` is `t - c`. -/
private theorem map_X_sub_C (c : k) :
    (X - C c).map (algebraMap k K) = X - C (algebraMap k K c) := by
  rw [Polynomial.map_sub, map_X, map_C]

/-- The place of `t - c` in `K(t)`, for `c ∈ k`, lies over the place of `t - c` in `k(t)`. -/
theorem restrict_adicOfIrreducible_X_sub_C_algebraMap
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X) (c : k) :
    (adicOfIrreducible (irreducible_X_sub_C (algebraMap k K c))).restrict k (RatFunc k) =
      adicOfIrreducible (irreducible_X_sub_C c) :=
  (restrict_adicOfIrreducible_eq_iff hX _ _).mpr (map_X_sub_C (K := K) c).symm.dvd

/-- **Over a rational finite place there is only one place**: for `c ∈ k`, the place of `t - c`
in `K(t)` is the only place over the place of `t - c` in `k(t)`. -/
theorem restrict_eq_adicOfIrreducible_X_sub_C_iff
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X) (c : k)
    (Q : Place K (RatFunc K)) :
    Q.restrict k (RatFunc k) = adicOfIrreducible (irreducible_X_sub_C c) ↔
      Q = adicOfIrreducible (irreducible_X_sub_C (algebraMap k K c)) := by
  rw [restrict_eq_adicOfIrreducible_iff hX]
  constructor
  · rintro ⟨q', hq', hdvd, rfl⟩
    rw [map_X_sub_C] at hdvd
    exact (adicOfIrreducible_eq_adicOfIrreducible_iff hq' (irreducible_X_sub_C _)).mpr
      (hq'.associated_of_dvd (irreducible_X_sub_C _) hdvd)
  · rintro rfl
    exact ⟨_, irreducible_X_sub_C _, (map_X_sub_C c).symm.dvd, rfl⟩

/-- **A rational finite place has ramification index one in `K(t) / k(t)`**: for `c ∈ k`,
`e = 1` at the place of `t - c` in `K(t)`. -/
theorem ramificationIdx_adicOfIrreducible_X_sub_C_algebraMap
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X) (c : k) :
    ramificationIdx (RatFunc k) (adicOfIrreducible (irreducible_X_sub_C (algebraMap k K c))) =
      1 := by
  rw [ramificationIdx_adicOfIrreducible_eq_multiplicity hX (irreducible_X_sub_C _)
    (irreducible_X_sub_C c) (map_X_sub_C c).symm.dvd, map_X_sub_C,
    multiplicity_self (.of_not_isUnit (not_isUnit_X_sub_C _) (X_sub_C_ne_zero _))]

/-- **The conorm of a rational finite place is a single place**: for `c ∈ k`, the conorm of the
place of `t - c` in `k(t)` is the place of `t - c` in `K(t)`. -/
theorem conorm_ofPoint_adicOfIrreducible_X_sub_C
    [∀ P : Place k (RatFunc k), Finite {Q : Place K (RatFunc K) // Q.restrict k (RatFunc k) = P}]
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X) (c : k) :
    Divisor.conorm K (RatFunc K) (AlgebraicGeometry.WeilDivisor.ofPoint
        (adicOfIrreducible (irreducible_X_sub_C c))) =
      AlgebraicGeometry.WeilDivisor.ofPoint
        (adicOfIrreducible (irreducible_X_sub_C (algebraMap k K c))) := by
  refine AlgebraicGeometry.WeilDivisor.ext fun Q ↦ ?_
  rw [Divisor.coeff_conorm]
  by_cases hQ : Q = adicOfIrreducible (irreducible_X_sub_C (algebraMap k K c))
  · rw [hQ, restrict_adicOfIrreducible_X_sub_C_algebraMap hX,
      ramificationIdx_adicOfIrreducible_X_sub_C_algebraMap hX,
      AlgebraicGeometry.WeilDivisor.coeff_ofPoint_self,
      AlgebraicGeometry.WeilDivisor.coeff_ofPoint_self, Nat.cast_one, one_mul]
  · rw [AlgebraicGeometry.WeilDivisor.coeff_ofPoint_of_ne
      (mt (restrict_eq_adicOfIrreducible_X_sub_C_iff hX c Q).mp hQ),
      AlgebraicGeometry.WeilDivisor.coeff_ofPoint_of_ne hQ, mul_zero]

variable {p : ℕ} [Fact p.Prime] [CharP k p] {a : k} {α : K}

/-- **A rational finite place of `k(t)` is not unramified in `K(t)`** when `K` contains a `p`-th
root `α` of an element `a` that is not a `p`-th power in `k`: the residue extension at the place
of `t - c` in `K(t)` is `K / k`, which is not separable. This holds although `e = 1` there
(`TauCeti.Place.ramificationIdx_adicOfIrreducible_X_sub_C_algebraMap`). -/
theorem not_isUnramified_adicOfIrreducible_X_sub_C_of_pow_eq (c : k) (ha : ∀ c : k, c ^ p ≠ a)
    (hα : α ^ p = algebraMap k K a) :
    ¬ (adicOfIrreducible (irreducible_X_sub_C c)).IsUnramified (k' := K) (F' := RatFunc K) := by
  have : ExpChar k p := ExpChar.prime Fact.out
  refine not_isUnramified_of_degree_eq_one (by simp) p ?_ (n := 1) ⟨a, by rw [pow_one, hα]⟩
  rintro ⟨d, rfl⟩
  exact ha d ((algebraMap k K).injective (by rw [map_pow, hα]))

/-! #### The place of `t ^ p - a`: ramification without a separable extension of the field -/

omit [Algebra (RatFunc k) (RatFunc K)] [IsScalarTower k (RatFunc k) (RatFunc K)]
  [Algebra.IsIntegral (RatFunc k) (RatFunc K)] in
/-- In `K[t]`, the polynomial `t ^ p - a` is `(t - α) ^ p`. -/
private theorem map_X_pow_sub_C_eq (hα : α ^ p = algebraMap k K a) :
    (X ^ p - C a).map (algebraMap k K) = (X - C α) ^ p := by
  have := charP_of_injective_algebraMap (algebraMap k K).injective p
  rw [sub_pow_char, ← C_pow, hα, Polynomial.map_sub, Polynomial.map_pow, map_X, map_C]

/-- The place of `t - α` in `K(t)` lies over the place of `t ^ p - a` in `k(t)`. -/
theorem restrict_adicOfIrreducible_X_sub_C_of_pow_eq
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X) (ha : ∀ c : k, c ^ p ≠ a)
    (hα : α ^ p = algebraMap k K a) :
    (adicOfIrreducible (irreducible_X_sub_C α)).restrict k (RatFunc k) =
      adicOfIrreducible (X_pow_sub_C_irreducible_of_prime Fact.out ha) :=
  (restrict_adicOfIrreducible_eq_iff hX _ _).mpr
    (by rw [map_X_pow_sub_C_eq hα]; exact dvd_pow_self _ (Fact.out : p.Prime).ne_zero)

/-- **The place of `t - α` is the only place of `K(t)` over the place of `t ^ p - a`.** -/
theorem restrict_eq_adicOfIrreducible_X_pow_sub_C_iff
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X) (ha : ∀ c : k, c ^ p ≠ a)
    (hα : α ^ p = algebraMap k K a) (Q : Place K (RatFunc K)) :
    Q.restrict k (RatFunc k) = adicOfIrreducible (X_pow_sub_C_irreducible_of_prime Fact.out ha) ↔
      Q = adicOfIrreducible (irreducible_X_sub_C α) := by
  rw [restrict_eq_adicOfIrreducible_iff hX]
  constructor
  · rintro ⟨q', hq', hdvd, rfl⟩
    rw [map_X_pow_sub_C_eq hα] at hdvd
    exact (adicOfIrreducible_eq_adicOfIrreducible_iff hq' (irreducible_X_sub_C α)).mpr
      (hq'.associated_of_dvd (irreducible_X_sub_C α) (hq'.prime.dvd_of_dvd_pow hdvd))
  · rintro rfl
    exact ⟨X - C α, irreducible_X_sub_C α, by
      rw [map_X_pow_sub_C_eq hα]; exact dvd_pow_self _ (Fact.out : p.Prime).ne_zero, rfl⟩

/-- **The place of `t ^ p - a` ramifies in the constant extension `K(t) / k(t)`**: the place of
`t - α` above it has ramification index `e = p`. -/
theorem ramificationIdx_adicOfIrreducible_X_sub_C_of_pow_eq
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X) (ha : ∀ c : k, c ^ p ≠ a)
    (hα : α ^ p = algebraMap k K a) :
    ramificationIdx (RatFunc k) (adicOfIrreducible (irreducible_X_sub_C α)) = p := by
  rw [ramificationIdx_adicOfIrreducible_eq_multiplicity hX (irreducible_X_sub_C α)
    (X_pow_sub_C_irreducible_of_prime Fact.out ha)
    (by rw [map_X_pow_sub_C_eq hα]; exact dvd_pow_self _ (Fact.out : p.Prime).ne_zero),
    map_X_pow_sub_C_eq hα, multiplicity_pow_self (X_sub_C_ne_zero α) (not_isUnit_X_sub_C α)]

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
