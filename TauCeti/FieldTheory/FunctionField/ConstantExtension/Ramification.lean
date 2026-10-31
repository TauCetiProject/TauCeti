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
# Ramification in a constant field extension of the rational function field

Let `K / k` be an algebraic field extension and view `K(t)` as the constant field extension
`k(t) · K` of `k(t)`. A finite separable `K / k` is unramified at every place of `k(t)`
(`TauCeti.Place.isUnramifiedAt_of_constantCompositum_eq_top`). This file computes, place by
place, what happens over an imperfect `k` when `K / k` is inseparable, separating the two ways in
which a place can fail to be unramified.

* **A rational place keeps ramification index one, but its residue extension is `K / k`.** For
  `c ∈ k`, the place `t = c` of `k(t)` has exactly one place above it, the place `t = c` of `K(t)`.
  Both are rational, the ramification index is `1` and the relative degree is `[K : k]`, because
  the residue extension is `K / k` itself. So the place `t = c` is unramified in `K(t)` exactly
  when `K / k` is separable.
* **An inseparable irreducible polynomial becomes a `p`-th power.** Let `k` have characteristic
  `p` and let `a ∈ k` not be a `p`-th power, so that `t ^ p - a` is irreducible over `k`. If `K`
  contains a `p`-th root `b` of `a`, then `t ^ p - a = (t - b) ^ p` in `K(t)`. The place of
  `t ^ p - a` has the place `t = b` as its only place above it, with ramification index `p`, so
  its conorm is `p` times the place `t = b`.

For `k = 𝔽_p(a)` and `K = k(a^{1/p})`, the projective line stays smooth of genus zero under the
extension of constants from `k` to `K`. Still, the place of `t ^ p - a` has `e = p`, and the place
`t = 0` has `e = 1` with residue extension purely inseparable of degree `p`, so that neither is
unramified. Neither failure is visible from the genus or from smoothness of the curve.

The algebra structure of `K(t)` over `k(t)` is any one compatible with `k` and sending `t` to `t`,
as in `TauCeti.constantCompositum_ratFunc_eq_top`. The places over a finite place of `k(t)` are
found with `TauCeti.Place.restrict_eq_adicOfIrreducible_iff`.

## Main results

* `TauCeti.Place.isSeparable_residueField_iff_of_degree_eq_one`: at a rational place over a
  rational place, the residue extension is separable exactly when the constant extension is.
* `TauCeti.Place.restrict_eq_adicOfIrreducible_X_sub_C_iff`,
  `TauCeti.Place.ramificationIdx_adicOfIrreducible_X_sub_C_algebraMap` and
  `TauCeti.Place.relativeDegree_adicOfIrreducible_X_sub_C_algebraMap`: the place `t = c` of
  `K(t)` is the only place over the place `t = c` of `k(t)`, with `e = 1` and `f = [K : k]`.
* `TauCeti.Place.isUnramified_adicOfIrreducible_X_sub_C_iff`: the place `t = c` of `k(t)` is
  unramified in `K(t)` exactly when `K / k` is separable.
* `TauCeti.Place.not_isUnramified_adicOfIrreducible_X_sub_C_of_pow_eq`: it is not unramified when
  `K` contains a `p`-th root of an element of `k` which is not a `p`-th power in `k`.
* `TauCeti.Place.restrict_eq_adicOfIrreducible_X_pow_sub_C_iff` and
  `TauCeti.Place.ramificationIdx_adicOfIrreducible_X_sub_C_of_pow_eq`: the place `t = b` of `K(t)`
  is the only place over the place of `t ^ p - a`, with `e = p`.
* `TauCeti.Divisor.conorm_ofPoint_adicOfIrreducible_X_sub_C` and
  `TauCeti.Divisor.conorm_ofPoint_adicOfIrreducible_X_pow_sub_C`: the conorm of the place `t = c`
  is the place `t = c`, and the conorm of the place of `t ^ p - a` is `p` times the place `t = b`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section III.6, where the constant field is assumed perfect.
-/

public section

open Polynomial

namespace TauCeti

namespace Place

/-! ### Residue extensions at rational places -/

section ResidueField

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k' F'] [Algebra F F'] [Algebra k F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F'] [Algebra.IsIntegral F F']

/-- **At a rational place over a rational place, the residue extension is the constant
extension**: if `P'` and the place `P` below it have degree one, then `F'_{P'} / F_P` is
separable exactly when `k' / k` is, since the residue fields are `k'` and `k`. -/
theorem isSeparable_residueField_iff_of_degree_eq_one (P' : Place k' F') (h' : P'.degree = 1)
    (h : (P'.restrict k F).degree = 1) :
    Algebra.IsSeparable (P'.restrict k F).ResidueField P'.ResidueField ↔
      Algebra.IsSeparable k k' := by
  refine (Algebra.IsSeparable.iff_of_equiv_equiv
    ((P'.restrict k F).residueFieldEquivOfDegreeEqOne h).toRingEquiv
    (P'.residueFieldEquivOfDegreeEqOne h').toRingEquiv (RingHom.ext fun c ↦ ?_)).symm
  -- Both sides are the residue at `P'` of the constant `c`, viewed in `F'`.
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.coe_toRingHom,
    AlgEquiv.coe_toRingEquiv, residueFieldEquivOfDegreeEqOne_apply, algebraMap_residueField]
  rw [IsLocalRing.ResidueField.algebraMap_residue]
  congr 1
  apply Subtype.ext
  rw [coe_algebraMap_integers, coe_algebraMap_constants, coe_algebraMap_constants,
    ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

end ResidueField

/-! ### The constant field extension `K(t) / k(t)` -/

section RatFunc

variable {k K : Type*} [Field k] [Field K] [Algebra k K]
variable [Algebra (RatFunc k) (RatFunc K)] [IsScalarTower k (RatFunc k) (RatFunc K)]
variable [Algebra.IsIntegral (RatFunc k) (RatFunc K)]

/-- **The place `t = c` of `K(t)` is the only place over the place `t = c` of `k(t)`**, for
`c ∈ k`. -/
theorem restrict_eq_adicOfIrreducible_X_sub_C_iff
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X) (c : k)
    (Q : Place K (RatFunc K)) :
    Q.restrict k (RatFunc k) = adicOfIrreducible (irreducible_X_sub_C c) ↔
      Q = adicOfIrreducible (irreducible_X_sub_C (algebraMap k K c)) := by
  rw [restrict_eq_adicOfIrreducible_iff, algebraMap_ratFunc_algebraMap_polynomial hX,
    Polynomial.map_sub, map_X, map_C, ord_algebraMap_pos_iff]

/-- **The place `t = c` of `K(t)` has ramification index `1`** over the place `t = c` of
`k(t)`. -/
theorem ramificationIdx_adicOfIrreducible_X_sub_C_algebraMap
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X) (c : k) :
    ramificationIdx (RatFunc k) (adicOfIrreducible (irreducible_X_sub_C (algebraMap k K c))) =
      1 := by
  classical
  set Q := adicOfIrreducible (irreducible_X_sub_C (algebraMap k K c))
  have hQ := (restrict_eq_adicOfIrreducible_X_sub_C_iff hX c Q).mpr rfl
  have h := ord_algebraMap_restrict k (RatFunc k) Q (algebraMap k[X] (RatFunc k) (X - C c))
  simp only [hQ, algebraMap_ratFunc_algebraMap_polynomial hX, Polynomial.map_sub, map_X, map_C,
    ord_adicOfIrreducible_algebraMap_irreducible _ (irreducible_X_sub_C (algebraMap k K c)),
    ord_adicOfIrreducible_algebraMap_irreducible _ (irreducible_X_sub_C c), Associated.refl,
    ↓reduceIte, mul_one, Q] at h
  exact_mod_cast h.symm

/-- **The relative degree of the place `t = c` of `K(t)` over `k(t)` is `[K : k]`**: both places
are rational, so the residue extension is the constant extension `K / k`. -/
theorem relativeDegree_adicOfIrreducible_X_sub_C_algebraMap
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X) (c : k) :
    relativeDegree k (RatFunc k) (adicOfIrreducible (irreducible_X_sub_C (algebraMap k K c))) =
      Module.finrank k K := by
  have h := finrank_mul_degree_eq_relativeDegree_mul_degree_restrict k (RatFunc k)
    (adicOfIrreducible (irreducible_X_sub_C (algebraMap k K c)))
  rwa [(restrict_eq_adicOfIrreducible_X_sub_C_iff hX c _).mpr rfl,
    degree_adicOfIrreducible_X_sub_C, degree_adicOfIrreducible_X_sub_C, mul_one, mul_one,
    eq_comm] at h

/-- **The place `t = c` of `k(t)` is unramified in `K(t)` exactly when `K / k` is separable.** The
only place above it has ramification index `1` in either case, and its residue extension is
`K / k`. -/
theorem isUnramified_adicOfIrreducible_X_sub_C_iff
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X) (c : k) :
    (adicOfIrreducible (irreducible_X_sub_C c)).IsUnramified (k' := K) (F' := RatFunc K) ↔
      Algebra.IsSeparable k K := by
  set Q := adicOfIrreducible (irreducible_X_sub_C (algebraMap k K c))
  have hQ := (restrict_eq_adicOfIrreducible_X_sub_C_iff hX c Q).mpr rfl
  have hsep := isSeparable_residueField_iff_of_degree_eq_one Q
    (degree_adicOfIrreducible_X_sub_C _) (hQ ▸ degree_adicOfIrreducible_X_sub_C c)
  refine ⟨fun h ↦ hsep.mp (h.isSeparable hQ), fun h ↦
    (isUnramified_iff _).mpr ⟨⟨Q, hQ⟩, fun Q' hQ' ↦ ?_⟩⟩
  obtain rfl := (restrict_eq_adicOfIrreducible_X_sub_C_iff hX c Q').mp hQ'
  exact ⟨ramificationIdx_adicOfIrreducible_X_sub_C_algebraMap hX c, hsep.mpr h⟩

section CharP

variable {p : ℕ} [hp : Fact p.Prime] [CharP k p] {a : k} {b : K}

/-- **A rational place of `k(t)` with an inseparable residue extension**: if `K` contains a `p`-th
root of an element of `k` which is not a `p`-th power, the place `t = c` of `k(t)` is not
unramified in `K(t)`, although the only place above it has ramification index `1` and both are
rational. -/
theorem not_isUnramified_adicOfIrreducible_X_sub_C_of_pow_eq
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X) (c : k)
    (ha : ∀ c : k, c ^ p ≠ a) (hb : b ^ p = algebraMap k K a) :
    ¬ (adicOfIrreducible (irreducible_X_sub_C c)).IsUnramified (k' := K) (F' := RatFunc K) := by
  -- `b` would be separable and purely inseparable over `k`, hence in `k`.
  rw [isUnramified_adicOfIrreducible_X_sub_C_iff hX c]
  intro hsep
  have hmem : b ∈ perfectClosure k K :=
    (mem_perfectClosure_iff_pow_mem p).mpr ⟨1, a, by rw [pow_one, hb]⟩
  rw [perfectClosure.eq_bot_of_isSeparable, IntermediateField.mem_bot] at hmem
  obtain ⟨c, rfl⟩ := hmem
  exact ha c ((algebraMap k K).injective (by rw [map_pow, hb]))

omit [Algebra.IsIntegral (RatFunc k) (RatFunc K)] in
/-- `t ^ p - a = (t - b) ^ p` in `K(t)`, for `b ^ p = a`. -/
private theorem algebraMap_X_pow_sub_C
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X)
    (hb : b ^ p = algebraMap k K a) :
    algebraMap (RatFunc k) (RatFunc K) (algebraMap k[X] (RatFunc k) (X ^ p - C a)) =
      algebraMap K[X] (RatFunc K) (X - C b) ^ p := by
  have : CharP K p := charP_of_injective_algebraMap (algebraMap k K).injective p
  rw [algebraMap_ratFunc_algebraMap_polynomial hX, Polynomial.map_sub, Polynomial.map_pow, map_X,
    map_C, ← hb, ← map_pow, sub_pow_char, ← C_pow]

/-- **The place `t = b` of `K(t)` is the only place over the place of `t ^ p - a` of `k(t)`**, for
`a` not a `p`-th power in `k` and `b ^ p = a`. -/
theorem restrict_eq_adicOfIrreducible_X_pow_sub_C_iff
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X) (ha : ∀ c : k, c ^ p ≠ a)
    (hb : b ^ p = algebraMap k K a) (Q : Place K (RatFunc K)) :
    Q.restrict k (RatFunc k) = adicOfIrreducible (X_pow_sub_C_irreducible_of_prime hp.out ha) ↔
      Q = adicOfIrreducible (irreducible_X_sub_C b) := by
  rw [restrict_eq_adicOfIrreducible_iff, algebraMap_X_pow_sub_C hX hb, ord_pow,
    ← ord_algebraMap_pos_iff (irreducible_X_sub_C b)]
  exact ⟨fun h ↦ pos_of_mul_pos_right h (Nat.cast_nonneg p),
    fun h ↦ mul_pos (by exact_mod_cast hp.out.pos) h⟩

/-- **The place of `t ^ p - a` is totally ramified in `K(t)`**: the place `t = b` of `K(t)` above
it has ramification index `p`, for `a` not a `p`-th power in `k` and `b ^ p = a`. -/
theorem ramificationIdx_adicOfIrreducible_X_sub_C_of_pow_eq
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X) (ha : ∀ c : k, c ^ p ≠ a)
    (hb : b ^ p = algebraMap k K a) :
    ramificationIdx (RatFunc k) (adicOfIrreducible (irreducible_X_sub_C b)) = p := by
  classical
  set Q := adicOfIrreducible (irreducible_X_sub_C b)
  have hQ := (restrict_eq_adicOfIrreducible_X_pow_sub_C_iff hX ha hb Q).mpr rfl
  have h := ord_algebraMap_restrict k (RatFunc k) Q (algebraMap k[X] (RatFunc k) (X ^ p - C a))
  rw [hQ, algebraMap_X_pow_sub_C hX hb, ord_pow,
    ord_adicOfIrreducible_algebraMap_irreducible _ (irreducible_X_sub_C b),
    ord_adicOfIrreducible_algebraMap_irreducible _
      (X_pow_sub_C_irreducible_of_prime hp.out ha)] at h
  simp only [Associated.refl, ↓reduceIte, mul_one] at h
  exact_mod_cast h.symm

end CharP

end RatFunc

end Place

namespace Divisor

variable {k K : Type*} [Field k] [Field K] [Algebra k K]
variable [Algebra (RatFunc k) (RatFunc K)] [IsScalarTower k (RatFunc k) (RatFunc K)]
variable [Algebra.IsIntegral (RatFunc k) (RatFunc K)]
variable
  [∀ P : Place k (RatFunc k), Finite {Q : Place K (RatFunc K) // Q.restrict k (RatFunc k) = P}]

open Place

/-- **The conorm of the place `t = c` of `k(t)` is the place `t = c` of `K(t)`.** -/
theorem conorm_ofPoint_adicOfIrreducible_X_sub_C
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X) (c : k) :
    conorm K (RatFunc K) (AlgebraicGeometry.WeilDivisor.ofPoint
        (adicOfIrreducible (irreducible_X_sub_C c))) =
      AlgebraicGeometry.WeilDivisor.ofPoint
        (adicOfIrreducible (irreducible_X_sub_C (algebraMap k K c))) := by
  refine AlgebraicGeometry.WeilDivisor.ext fun Q ↦ ?_
  rw [coeff_conorm]
  by_cases hQ : Q = adicOfIrreducible (irreducible_X_sub_C (algebraMap k K c))
  · subst hQ
    rw [(restrict_eq_adicOfIrreducible_X_sub_C_iff hX c _).mpr rfl,
      ramificationIdx_adicOfIrreducible_X_sub_C_algebraMap hX c]
    simp
  · rw [AlgebraicGeometry.WeilDivisor.coeff_ofPoint_of_ne hQ,
      AlgebraicGeometry.WeilDivisor.coeff_ofPoint_of_ne
        (mt (restrict_eq_adicOfIrreducible_X_sub_C_iff hX c Q).mp hQ), mul_zero]

variable {p : ℕ} [hp : Fact p.Prime] [CharP k p] {a : k} {b : K}

/-- **The conorm of the place of `t ^ p - a` is `p` times the place `t = b`** of `K(t)`, for `a`
not a `p`-th power in `k` and `b ^ p = a`. -/
theorem conorm_ofPoint_adicOfIrreducible_X_pow_sub_C
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X) (ha : ∀ c : k, c ^ p ≠ a)
    (hb : b ^ p = algebraMap k K a) :
    conorm K (RatFunc K) (AlgebraicGeometry.WeilDivisor.ofPoint
        (adicOfIrreducible (X_pow_sub_C_irreducible_of_prime hp.out ha))) =
      (p : ℤ) •
        AlgebraicGeometry.WeilDivisor.ofPoint (adicOfIrreducible (irreducible_X_sub_C b)) := by
  refine AlgebraicGeometry.WeilDivisor.ext fun Q ↦ ?_
  rw [coeff_conorm]
  by_cases hQ : Q = adicOfIrreducible (irreducible_X_sub_C b)
  · subst hQ
    rw [(restrict_eq_adicOfIrreducible_X_pow_sub_C_iff hX ha hb _).mpr rfl,
      ramificationIdx_adicOfIrreducible_X_sub_C_of_pow_eq hX ha hb]
    simp
  · rw [AlgebraicGeometry.WeilDivisor.coeff_zsmul,
      AlgebraicGeometry.WeilDivisor.coeff_ofPoint_of_ne hQ,
      AlgebraicGeometry.WeilDivisor.coeff_ofPoint_of_ne
        (mt (restrict_eq_adicOfIrreducible_X_pow_sub_C_iff hX ha hb Q).mp hQ), mul_zero, mul_zero]

end Divisor

end TauCeti
