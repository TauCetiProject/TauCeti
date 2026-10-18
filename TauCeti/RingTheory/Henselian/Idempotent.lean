/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Henselian
public import TauCeti.RingTheory.Ideal.GoingUp
public import TauCeti.RingTheory.Idempotents.Jacobson

/-!
# Idempotents and locality in Henselian rings

A commutative ring that is Henselian along an ideal `J` lifts idempotents from `S ⧸ J`: an
idempotent is a root of `X² - X`, and every root of `X² - X` modulo `J` is simple, since
`(2a - 1)² = 4(a² - a) + 1`. Consequently, when `S ⧸ J` is Artinian, the idempotents of `S`
control whether `S` is local. An Artinian ring with only the trivial idempotents is local, and a
ring whose quotient by an ideal in its Jacobson radical is local is itself local.

Lifts of idempotents are unique modulo any ideal in the Jacobson radical
(`IsIdempotentElem.eq_of_sub_mem_of_le_jacobson_bot`), and along an integral ring map the
extension of an ideal in the Jacobson radical stays in the Jacobson radical
(`Ideal.map_le_jacobson_bot_of_isIntegral`). Since a Henselian ideal lies in the Jacobson radical,
lifts are unique over a Henselian pair and in every integral, in particular every finite, algebra
over it.

The typical example is a finite algebra over a complete Noetherian local ring, Henselian along the
extension of the maximal ideal: such an algebra with no nontrivial idempotents is local. This is
the mechanism behind the locality of endomorphism rings of indecomposable modules over complete
local rings.

## Main results

* `TauCeti.IsArtinianRing.isLocalRing_of_forall_isIdempotentElem`: a nontrivial commutative
  Artinian ring whose only idempotents are `0` and `1` is local.
* `TauCeti.HenselianRing.exists_isIdempotentElem_sub_mem`: idempotents lift modulo an ideal along
  which the ring is Henselian.
* `TauCeti.HenselianRing.bijOn_quotient_mk_isIdempotentElem`: for a Henselian pair `(S, J)`, the
  quotient map `S → S ⧸ J` is a bijection on idempotents (Stacks, Lemma 15.11.6 (09XI), condition
  (3) for the algebra `S` itself).
* `TauCeti.HenselianRing.injOn_quotient_mk_map_isIdempotentElem`: for a Henselian pair `(S, J)`
  and an integral `S`-algebra `T`, the quotient map `T → T ⧸ JT` is injective on idempotents (the
  injectivity half of conditions (3) and (4) of 09XI).
* `TauCeti.HenselianRing.isLocalRing_of_forall_isIdempotentElem`: a nontrivial commutative ring,
  Henselian along an ideal with Artinian quotient, whose only idempotents are `0` and `1`, is
  local.

## References

* C. W. Curtis, I. Reiner, *Methods of Representation Theory, Vol. I*, §6.
* T. Y. Lam, *A First Course in Noncommutative Rings*, §21 and §23.
* [Stacks Project, Lemma 15.11.6](https://stacks.math.columbia.edu/tag/09XI).
* The uniqueness of lifts is ported from T. Dupuy, T. Tucker and Z. Wang,
  [pcfawd-formalization](https://github.com/tdupu/pcfawd-formalization) at commit
  `a39c3781b9850b9f3d5cbc9920322a3b8e365ef2` (Apache-2.0). From
  `lean/Pcf/Stacks/Purity/HenselianIdempotents.lean`: `existsUnique_isIdempotentElem_mk_eq` is its
  `Pcf.Stacks.existsUnique_isIdempotentElem_lift_of_henselian`, and
  `bijOn_quotient_mk_isIdempotentElem` restates as `Set.BijOn` its
  `Pcf.Stacks.bijective_idempotentQuotientMap_of_henselian`. From
  `lean/Pcf/Stacks/Purity/FiniteAlgebraIdempotents.lean`: `injOn_quotient_mk_map_isIdempotentElem`
  restates as `Set.InjOn` its `Pcf.Stacks.injective_idempotentQuotientMap_of_isIntegral`, which
  subsumes its `Pcf.Stacks.injective_idempotentQuotientMap_of_finite_henselian`.
-/

public section

namespace TauCeti

open Polynomial

variable {S : Type*} [CommRing S]

/-- **A connected Artinian ring is local.** A nontrivial commutative Artinian ring whose only
idempotents are `0` and `1` is local. -/
theorem IsArtinianRing.isLocalRing_of_forall_isIdempotentElem [IsArtinianRing S] [Nontrivial S]
    (h : ∀ e : S, IsIdempotentElem e → e = 0 ∨ e = 1) : IsLocalRing S := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun s ↦ ?_
  -- The descending chain `s ^ n • S` stabilizes, so `s ^ (m + 1) * y = s ^ m` for some `m ≥ 1`;
  -- then `s ^ m * y ^ m` is an idempotent, which is `0` (so `s` is nilpotent) or `1`.
  obtain ⟨n, y, hy⟩ := IsArtinian.exists_pow_succ_smul_dvd s (1 : S)
  simp only [smul_eq_mul, mul_one, Nat.succ_eq_add_one] at hy
  set m := n + 1
  have hm : s ^ (m + 1) * y = s ^ m :=
    calc s ^ (m + 1) * y = s * (s ^ (n + 1) * y) := by simp only [m]; ring
      _ = s ^ m := by rw [hy, pow_succ']
  have hpow : ∀ k, s ^ (m + k) * y ^ k = s ^ m := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc s ^ (m + (k + 1)) * y ^ (k + 1) = s ^ (m + 1) * y * (s ^ k * y ^ k) := by ring
        _ = s ^ (m + k) * y ^ k := by rw [hm]; ring
        _ = s ^ m := ih
  have hidem : IsIdempotentElem (s ^ m * y ^ m) := by
    rw [IsIdempotentElem]
    calc s ^ m * y ^ m * (s ^ m * y ^ m) = s ^ (m + m) * y ^ m * y ^ m := by ring
      _ = s ^ m * y ^ m := by rw [hpow]
  rcases h _ hidem with h0 | h1
  · right
    refine IsNilpotent.isUnit_one_sub ⟨m, ?_⟩
    rw [← hpow m, pow_add, mul_assoc, h0, mul_zero]
  · left
    refine IsUnit.of_mul_eq_one (s ^ n * y ^ m) ?_
    rw [← h1, ← mul_assoc, ← pow_succ']

namespace HenselianRing

/-- **Idempotents lift along a Henselian pair.** If `S` is Henselian along `J` and `a` is
idempotent modulo `J`, then some idempotent of `S` is congruent to `a` modulo `J`. -/
theorem exists_isIdempotentElem_sub_mem (J : Ideal S) [HenselianRing S J] {a : S}
    (ha : a * a - a ∈ J) : ∃ e : S, IsIdempotentElem e ∧ e - a ∈ J := by
  have hmonic : (X ^ 2 - X : S[X]).Monic := Polynomial.monic_X_pow_sub
    (degree_X_le.trans_lt (by exact_mod_cast one_lt_two))
  have hsimple : IsUnit (Ideal.Quotient.mk J (eval a (derivative (X ^ 2 - X : S[X])))) := by
    refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk J (2 * a - 1)) ?_
    rw [← map_mul, ← map_one (Ideal.Quotient.mk J), Ideal.Quotient.eq]
    convert J.mul_mem_left 4 ha using 1
    simp only [derivative_sub, derivative_X_pow, derivative_X, eval_sub, eval_mul, eval_C,
      eval_pow, eval_X, eval_one]
    ring
  obtain ⟨e, he, hea⟩ := HenselianRing.is_henselian (X ^ 2 - X) hmonic a
    (by simpa [sq] using ha) hsimple
  refine ⟨e, ?_, hea⟩
  rw [IsIdempotentElem, ← sub_eq_zero]
  simpa [IsRoot, sq] using he

/-- **Idempotents lift uniquely along a Henselian pair.** If `S` is Henselian along `J`, every
idempotent of `S ⧸ J` is the image of exactly one idempotent of `S`. -/
theorem existsUnique_isIdempotentElem_mk_eq (J : Ideal S) [HenselianRing S J] {t : S ⧸ J}
    (ht : IsIdempotentElem t) : ∃! e : S, IsIdempotentElem e ∧ Ideal.Quotient.mk J e = t := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective t
  obtain ⟨e, he, hea⟩ := exists_isIdempotentElem_sub_mem J
    (Ideal.Quotient.eq_zero_iff_mem.mp (by rw [map_sub, map_mul, ht.eq, sub_self]))
  refine ⟨e, ⟨he, Ideal.Quotient.eq.mpr hea⟩, fun e' ⟨he', h⟩ ↦ ?_⟩
  exact Ideal.injOn_quotient_mk_isIdempotentElem HenselianRing.jac he' he
    (h.trans (Ideal.Quotient.eq.mpr hea).symm)

/-- **Locality from the idempotents.** A nontrivial commutative ring that is Henselian along an
ideal `J` with `S ⧸ J` Artinian, and whose only idempotents are `0` and `1`, is local. -/
theorem isLocalRing_of_forall_isIdempotentElem [Nontrivial S] (J : Ideal S) [HenselianRing S J]
    [IsArtinianRing (S ⧸ J)] (h : ∀ e : S, IsIdempotentElem e → e = 0 ∨ e = 1) :
    IsLocalRing S := by
  have hJ : J ≠ ⊤ := fun hJ ↦ by
    have hjac : J ≤ Ideal.jacobson ⊥ := HenselianRing.jac
    rw [hJ, top_le_iff, Ideal.jacobson_eq_top_iff] at hjac
    exact bot_ne_top hjac
  have : IsLocalHom (Ideal.Quotient.mk J) := isLocalHom_of_le_jacobson_bot J HenselianRing.jac
  have : Nontrivial (S ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  have : IsLocalRing (S ⧸ J) := by
    refine IsArtinianRing.isLocalRing_of_forall_isIdempotentElem fun t ht ↦ ?_
    obtain ⟨e, he, rfl⟩ := (existsUnique_isIdempotentElem_mk_eq J ht).exists
    rcases h e he with rfl | rfl
    · exact Or.inl (map_zero _)
    · exact Or.inr (map_one _)
  exact RingHom.domain_isLocalRing (Ideal.Quotient.mk J)

/-- **Idempotents of a Henselian pair.** If `S` is Henselian along `J`, the quotient map
`S → S ⧸ J` restricts to a bijection between the idempotents of `S` and those of `S ⧸ J`. -/
@[stacks 09XI "(1) ⇒ (3), for the finite algebra `B = A` only"]
theorem bijOn_quotient_mk_isIdempotentElem (J : Ideal S) [HenselianRing S J] :
    Set.BijOn (Ideal.Quotient.mk J) {e | IsIdempotentElem e} {t | IsIdempotentElem t} :=
  ⟨fun _ he ↦ he.map _, Ideal.injOn_quotient_mk_isIdempotentElem HenselianRing.jac,
    fun _ ht ↦ (existsUnique_isIdempotentElem_mk_eq J ht).exists⟩

/-- **Uniqueness of idempotent lifts in integral algebras.** If `S` is Henselian along `J` and `T`
is an integral `S`-algebra, for instance a finite one, then idempotents of `T` congruent modulo
`JT` are equal. -/
@[stacks 09XI "(1) ⇒ (3) and (4), injectivity on idempotents only"]
theorem injOn_quotient_mk_map_isIdempotentElem {T : Type*} [CommRing T] [Algebra S T]
    [Algebra.IsIntegral S T] (J : Ideal S) [HenselianRing S J] :
    Set.InjOn (Ideal.Quotient.mk (J.map (algebraMap S T))) {e | IsIdempotentElem e} :=
  Ideal.injOn_quotient_mk_isIdempotentElem (Ideal.map_le_jacobson_bot_of_isIntegral
    HenselianRing.jac)

end HenselianRing

end TauCeti
