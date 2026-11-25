/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.Jacobson.Radical
import TauCeti.RingTheory.Jacobson.Basic

/-!
# Idempotents modulo an ideal in the Jacobson radical

In any ring, an idempotent `e` in the Jacobson radical is zero: `1 - e` is then an idempotent
unit, hence `1`. Consequently, commuting idempotents `e` and `e'` whose difference lies in the
Jacobson radical are equal: `e (1 - e') = e (e - e')` and `e' (1 - e) = e' (e' - e)` are
idempotents in the Jacobson radical, hence zero, and `e = e e' = e' e = e'`. In particular, in a
commutative ring, idempotents are determined by their residues modulo any ideal contained in the
Jacobson radical.

This is the uniqueness half of lifting idempotents along a Henselian pair, and it needs no
Henselian hypothesis. The commutation hypothesis cannot be dropped: for example, in the upper
triangular `2 × 2` matrices over a field, `E₁₁` and `E₁₁ + E₁₂` are distinct, non-commuting
idempotents whose difference lies in the Jacobson radical.

## Main results

* `IsIdempotentElem.eq_zero_of_mem_jacobson`: an idempotent in the Jacobson radical
  `Ring.jacobson R` of a not necessarily commutative ring is zero.
* `IsIdempotentElem.mem_jacobson_iff`: an idempotent lies in `Ring.jacobson R` if and only if it is
  zero.
* `IsIdempotentElem.eq_of_commute_of_sub_mem_jacobson`: in a not necessarily commutative ring,
  commuting idempotents whose difference lies in the Jacobson radical are equal.
* `Ideal.injOn_quotient_mk_isIdempotentElem`: modulo an ideal in the Jacobson radical of a
  commutative ring, the quotient map is injective on idempotents.

## References

* [Stacks Project, Lemma 15.11.6](https://stacks.math.columbia.edu/tag/09XI), the uniqueness of
  lifts in condition (3).
* Ported from T. Dupuy, T. Tucker and Z. Wang,
  [pcfawd-formalization](https://github.com/tdupu/pcfawd-formalization) at commit
  `a39c3781b9850b9f3d5cbc9920322a3b8e365ef2` (Apache-2.0),
  `lean/Pcf/Stacks/Purity/HenselianIdempotents.lean`: `eq_zero_of_mem_jacobson` is its
  `Pcf.Stacks.isIdempotentElem_eq_zero_of_mem_jacobson`, `eq_of_commute_of_sub_mem_jacobson`
  generalizes its commutative `Pcf.Stacks.eq_of_isIdempotentElem_of_sub_mem_of_le_jacobson` to
  commuting idempotents, and `injOn_quotient_mk_isIdempotentElem` restates as `Set.InjOn` the
  injectivity step of its `Pcf.Stacks.bijective_idempotentQuotientMap_of_henselian`.
-/

public section

/-- An idempotent in the Jacobson radical `Ring.jacobson R` of a (not necessarily commutative)
ring is zero. -/
theorem IsIdempotentElem.eq_zero_of_mem_jacobson {R : Type*} [Ring R] {e : R}
    (he : IsIdempotentElem e) (hJ : e ∈ Ring.jacobson R) : e = 0 := by
  -- `1 - e` is a unit, and the only idempotent unit is `1`.
  have hu : IsUnit (1 - e) := by
    simpa only [one_mul, ← sub_eq_add_neg] using
      TauCeti.Ring.mem_jacobson_iff_isUnit_one_add_mul_left.mp (neg_mem hJ) 1
  exact sub_eq_self.mp ((IsIdempotentElem.iff_eq_one_of_isUnit hu).mp he.one_sub)

/-- An idempotent lies in the Jacobson radical `Ring.jacobson R` if and only if it is zero. -/
@[simp]
theorem IsIdempotentElem.mem_jacobson_iff {R : Type*} [Ring R] {e : R}
    (he : IsIdempotentElem e) : e ∈ Ring.jacobson R ↔ e = 0 :=
  ⟨he.eq_zero_of_mem_jacobson, fun h ↦ h ▸ zero_mem _⟩

/-- **Idempotent lifts are unique modulo the Jacobson radical.** In a (not necessarily
commutative) ring, commuting idempotents whose difference lies in the Jacobson radical are
equal. -/
theorem IsIdempotentElem.eq_of_commute_of_sub_mem_jacobson {R : Type*} [Ring R] {e e' : R}
    (he : IsIdempotentElem e) (he' : IsIdempotentElem e') (hc : Commute e e')
    (h : e - e' ∈ Ring.jacobson R) : e = e' := by
  -- For commuting idempotents `a`, `b` with `a - b` in the radical, `a (1 - b) = a (a - b)` is an
  -- idempotent in the radical, hence zero, so `a = a b`.
  have key {a b : R} (ha : IsIdempotentElem a) (hb : IsIdempotentElem b) (hab : Commute a b)
      (h : a - b ∈ Ring.jacobson R) : a = a * b := by
    have hab' : a * (1 - b) = a * (a - b) := by simp only [mul_sub, mul_one, ha.eq]
    have h0 := (ha.mul_of_commute ((Commute.one_right a).sub_right hab)
      hb.one_sub).eq_zero_of_mem_jacobson (hab' ▸ Ideal.mul_mem_left _ a h)
    rwa [mul_one_sub, sub_eq_zero] at h0
  calc e = e * e' := key he he' hc h
    _ = e' * e := hc.eq
    _ = e' := (key he' he hc.symm (by rwa [← neg_mem_iff, neg_sub])).symm

/-- Modulo an ideal in the Jacobson radical of a commutative ring, the quotient map is injective
on idempotents. -/
theorem Ideal.injOn_quotient_mk_isIdempotentElem {R : Type*} [CommRing R] {I : Ideal R}
    (hI : I ≤ Ring.jacobson R) : Set.InjOn (Ideal.Quotient.mk I) {e | IsIdempotentElem e} :=
  fun _ he _ he' h ↦
    he.eq_of_commute_of_sub_mem_jacobson he' (.all _ _) (hI (Ideal.Quotient.eq.mp h))
