/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Henselian

/-!
# Idempotents and locality in Henselian rings

A commutative ring that is Henselian along an ideal `J` lifts idempotents from `S ⧸ J`: an
idempotent is a root of `X² - X`, and every root of `X² - X` modulo `J` is simple, since
`(2a - 1)² = 4(a² - a) + 1`. Consequently, when `S ⧸ J` is Artinian, the idempotents of `S`
control whether `S` is local. An Artinian ring with only the trivial idempotents is local, and a
ring whose quotient by an ideal in its Jacobson radical is local is itself local.

The typical example is a finite algebra over a complete Noetherian local ring, Henselian along the
extension of the maximal ideal: such an algebra with no nontrivial idempotents is local. This is
the mechanism behind the locality of endomorphism rings of indecomposable modules over complete
local rings.

## Main results

* `TauCeti.IsArtinianRing.isLocalRing_of_forall_isIdempotentElem`: a nontrivial commutative
  Artinian ring whose only idempotents are `0` and `1` is local.
* `TauCeti.HenselianRing.exists_isIdempotentElem_sub_mem`: idempotents lift modulo an ideal along
  which the ring is Henselian.
* `TauCeti.HenselianRing.isLocalRing_of_forall_isIdempotentElem`: a nontrivial commutative ring,
  Henselian along an ideal with Artinian quotient, whose only idempotents are `0` and `1`, is
  local.

## References

* C. W. Curtis, I. Reiner, *Methods of Representation Theory, Vol. I*, §6.
* T. Y. Lam, *A First Course in Noncommutative Rings*, §21 and §23.
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
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective t
    obtain ⟨e, he, hea⟩ := exists_isIdempotentElem_sub_mem J
      (Ideal.Quotient.eq_zero_iff_mem.mp (by rw [map_sub, map_mul, ht.eq, sub_self]))
    rw [← Ideal.Quotient.eq.mpr hea]
    rcases h e he with rfl | rfl
    · exact Or.inl (map_zero _)
    · exact Or.inr (map_one _)
  exact RingHom.domain_isLocalRing (Ideal.Quotient.mk J)

end HenselianRing

end TauCeti
