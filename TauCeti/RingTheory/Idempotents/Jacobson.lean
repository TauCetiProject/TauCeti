/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.Tactic.LinearCombination

/-!
# Idempotents modulo an ideal in the Jacobson radical

In a commutative ring, an idempotent `e` in the Jacobson radical is zero: `1 - e` is a unit and
`e (1 - e) = 0`. Consequently idempotents are determined by their residues modulo any ideal `I`
contained in the Jacobson radical. If `e` and `e'` are idempotents with `e - e'` in `I`, then
`e (1 - e')` and `(1 - e) e'` are idempotents in the Jacobson radical, hence zero, and
`e - e' = e (1 - e') - (1 - e) e' = 0`.

This is the uniqueness half of lifting idempotents along a Henselian pair, and it needs no
Henselian hypothesis.

## Main results

* `IsIdempotentElem.eq_zero_of_mem_jacobson_bot`: an idempotent in the Jacobson radical is zero.
* `IsIdempotentElem.eq_of_sub_mem_of_le_jacobson_bot`: idempotents congruent modulo an ideal in
  the Jacobson radical are equal.
* `Ideal.injOn_quotient_mk_isIdempotentElem`: modulo an ideal in the Jacobson radical, the quotient
  map is injective on idempotents.

## References

* [Stacks Project, Lemma 15.11.6](https://stacks.math.columbia.edu/tag/09XI), the uniqueness of
  lifts in condition (3).
* Ported from T. Dupuy, T. Tucker and Z. Wang,
  [pcfawd-formalization](https://github.com/tdupu/pcfawd-formalization) at commit
  `a39c3781b9850b9f3d5cbc9920322a3b8e365ef2` (Apache-2.0),
  `lean/Pcf/Stacks/Purity/HenselianIdempotents.lean`: `eq_zero_of_mem_jacobson_bot` and
  `eq_of_sub_mem_of_le_jacobson_bot` are its `Pcf.Stacks.isIdempotentElem_eq_zero_of_mem_jacobson`
  and `Pcf.Stacks.eq_of_isIdempotentElem_of_sub_mem_of_le_jacobson`, and
  `injOn_quotient_mk_isIdempotentElem` restates as `Set.InjOn` the injectivity step of its
  `Pcf.Stacks.bijective_idempotentQuotientMap_of_henselian`.
-/

public section

variable {R : Type*} [CommRing R]

/-- An idempotent in the Jacobson radical is zero: `1 - e` is a unit and `e (1 - e) = 0`. -/
theorem IsIdempotentElem.eq_zero_of_mem_jacobson_bot {e : R} (he : IsIdempotentElem e)
    (hJ : e ∈ Ideal.jacobson (⊥ : Ideal R)) : e = 0 := by
  have hu : IsUnit (1 - e) := by
    simpa [sub_eq_add_neg, add_comm] using Ideal.mem_jacobson_bot.mp hJ (-1)
  exact hu.mul_right_cancel (by simpa using he.mul_one_sub_self)

/-- **Idempotent lifts are unique modulo the Jacobson radical.** Idempotents that are congruent
modulo an ideal contained in the Jacobson radical are equal. -/
theorem IsIdempotentElem.eq_of_sub_mem_of_le_jacobson_bot {I : Ideal R}
    (hI : I ≤ Ideal.jacobson ⊥) {e e' : R} (he : IsIdempotentElem e)
    (he' : IsIdempotentElem e') (h : e - e' ∈ I) : e = e' := by
  -- Both `e (1 - e')` and `(1 - e) e'` are multiples of `e - e'`, using `e² = e` and `e'² = e'`.
  have hleft : e * (1 - e') = e * (e - e') := by linear_combination -he.eq
  have hright : (1 - e) * e' = -((e - e') * e') := by linear_combination -he'.eq
  have h₁ : e * (1 - e') = 0 := (he.mul he'.one_sub).eq_zero_of_mem_jacobson_bot <| hI <| by
    rw [hleft]
    exact I.mul_mem_left e h
  have h₂ : (1 - e) * e' = 0 := (he.one_sub.mul he').eq_zero_of_mem_jacobson_bot <| hI <| by
    rw [hright]
    exact I.neg_mem (I.mul_mem_right e' h)
  linear_combination h₁ - h₂

/-- Modulo an ideal in the Jacobson radical, the quotient map is injective on idempotents. -/
theorem Ideal.injOn_quotient_mk_isIdempotentElem {I : Ideal R} (hI : I ≤ Ideal.jacobson ⊥) :
    Set.InjOn (Ideal.Quotient.mk I) {e | IsIdempotentElem e} :=
  fun _ he _ he' h ↦ he.eq_of_sub_mem_of_le_jacobson_bot hI he' (Ideal.Quotient.eq.mp h)
