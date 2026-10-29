/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.Nakayama
import Mathlib.Tactic.LinearCombination

/-!
# Idempotents modulo an ideal in the Jacobson radical

In any ring, an idempotent `e` in the Jacobson radical is zero: `1 - e` has a left inverse and
`(1 - e) e = 0`. Consequently, in a commutative ring, idempotents are determined by their
residues modulo any ideal `I` contained in the Jacobson radical. If `e` and `e'` are idempotents
with `e - e'` in `I`, then `e (1 - e')` and `(1 - e) e'` are idempotents in the Jacobson radical,
hence zero, and `e - e' = e (1 - e') - (1 - e) e' = 0`.

This is the uniqueness half of lifting idempotents along a Henselian pair, and it needs no
Henselian hypothesis. The second step needs commutativity: for example, in the upper triangular
`2 × 2` matrices over a field, `E₁₁` and `E₁₁ + E₁₂` are distinct idempotents whose difference
lies in the Jacobson radical.

## Main results

* `IsIdempotentElem.eq_zero_of_mem_jacobson_bot`: an idempotent in the Jacobson radical
  `Ideal.jacobson ⊥` of a not necessarily commutative ring is zero.
* `IsIdempotentElem.eq_of_sub_mem_of_le_jacobson_bot`: idempotents congruent modulo an ideal in
  the Jacobson radical are equal.
* `Ideal.injOn_quotient_mk_isIdempotentElem`: modulo an ideal in the Jacobson radical, the quotient
  map is injective on idempotents.
* `IsIdempotentElem.exists_smul_eq_mul_of_mul_sub_smul_mem`: in a module-finite `S`-algebra `T`, an
  idempotent `e` with `e T ⊆ S e + JT`, for `J` in the Jacobson radical of `S`, has `e T = S e`.

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

/-- An idempotent in the Jacobson radical `Ideal.jacobson ⊥` of a (not necessarily commutative)
ring is zero. -/
theorem IsIdempotentElem.eq_zero_of_mem_jacobson_bot {R : Type*} [Ring R] {e : R}
    (he : IsIdempotentElem e) (hJ : e ∈ Ideal.jacobson (⊥ : Ideal R)) : e = 0 := by
  obtain ⟨z, hz⟩ := Ideal.exists_mul_add_sub_mem_of_mem_jacobson (-e) (neg_mem hJ)
  have hz' : z * (1 - e) = 1 := by
    rw [← neg_add_eq_sub]
    exact sub_eq_zero.mp ((Submodule.mem_bot R).mp hz)
  calc e = z * (1 - e) * e := by rw [hz', one_mul]
    _ = 0 := by rw [mul_assoc, he.one_sub_mul_self, mul_zero]

variable {R : Type*} [CommRing R]

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

/-- **Nakayama's lemma for an idempotent.** Let `T` be a module-finite `S`-algebra and `J` an
ideal of `S` in the Jacobson radical. If an idempotent `e` of `T` satisfies `e T ⊆ S e + JT`, then
`e T = S e`. -/
theorem IsIdempotentElem.exists_smul_eq_mul_of_mul_sub_smul_mem {S T : Type*} [CommRing S]
    [CommRing T] [Algebra S T] [Module.Finite S T] {J : Ideal S} (hJ : J ≤ Ideal.jacobson ⊥)
    {e : T} (he : IsIdempotentElem e)
    (h : ∀ x : T, ∃ s : S, e * x - s • e ∈ J.map (algebraMap S T)) (x : T) :
    ∃ s : S, s • e = e * x := by
  let f := LinearMap.mulLeft S e
  have hfg : (LinearMap.range f).FG := by
    rw [LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map f
  have hle : LinearMap.range f ≤ S ∙ e := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot hfg hJ ?_
    rintro _ ⟨y, rfl⟩
    obtain ⟨s, hs⟩ := h y
    have hmem : e * (e * y - s • e) ∈ J • LinearMap.range f := by
      rw [LinearMap.range_eq_map, ← Submodule.map_smul'']
      exact ⟨_, by simpa using hs, rfl⟩
    have hy : f y = s • e + e * (e * y - s • e) := by
      simp only [f, LinearMap.mulLeft_apply, mul_sub, ← mul_assoc, he.eq, mul_smul_comm]
      abel
    rw [hy]
    exact Submodule.add_mem_sup (Submodule.smul_mem _ s (Submodule.mem_span_singleton_self e)) hmem
  exact Submodule.mem_span_singleton.mp (hle ⟨x, rfl⟩)
