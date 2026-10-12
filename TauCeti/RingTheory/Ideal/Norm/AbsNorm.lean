/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import TauCeti.Data.ZMod.Divisibility
import TauCeti.RingTheory.Norm.Congruence

/-!
# The absolute ideal norm under a ring isomorphism, and congruences of norms

Identifying two rings along an isomorphism identifies their ideals, and the absolute norm is
insensitive to that identification.

In a Dedekind domain that is free of finite rank over `ℤ`, congruent elements whose norms
have nonnegative product generate principal ideals with congruent absolute norms.

## Main results

* `Ideal.absNorm_comap_of_ringEquiv`, `Ideal.absNorm_map_of_ringEquiv`: the absolute norm of an
  ideal is unchanged by transporting it along a ring isomorphism, in either direction.
* `Ideal.natCast_absNorm_span_singleton_eq_of_sub_mem`: congruent elements whose norms have
  nonnegative product generate ideals with absolute norms congruent modulo `m`.
-/

public section

namespace Ideal

variable {R R' : Type*} [CommRing R] [CommRing R'] [IsDedekindDomain R] [IsDedekindDomain R']

/-- The absolute norm is invariant under transporting an ideal backwards along an isomorphism of
Dedekind domains.  Use this to move a norm computation to whichever of two identified rings it is
easier to carry out in. -/
@[simp]
theorem absNorm_comap_of_ringEquiv [Infinite R] [Infinite R'] (e : R ≃+* R') (I : Ideal R') :
    absNorm (Ideal.comap e I) = absNorm I := by
  rw [absNorm_apply, absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr (Ideal.quotientEquiv _ _ e (Ideal.map_comap_eq_self_of_equiv e I).symm)

/-- The absolute norm is invariant under transporting an ideal forwards along an isomorphism of
Dedekind domains.  This is the form to use when the ideal is given on the source side. -/
@[simp]
theorem absNorm_map_of_ringEquiv [Infinite R] [Infinite R'] (e : R ≃+* R') (I : Ideal R) :
    absNorm (I.map e) = absNorm I := by
  rw [← Ideal.comap_symm]
  exact absNorm_comap_of_ringEquiv e.symm I

end Ideal

section AbsNormCongruence

variable {S : Type*} [CommRing S] [Module.Free ℤ S] [Module.Finite ℤ S]

/-- **Congruent elements with norms of nonnegative product generate ideals of congruent norms.**
If `a ≡ b` modulo the ideal `(m)` of a Dedekind domain `S` that is free of finite rank over `ℤ`,
and `N(a) N(b) ≥ 0`, then the absolute norms of `(a)` and `(b)` are congruent modulo `m`. -/
theorem Ideal.natCast_absNorm_span_singleton_eq_of_sub_mem [IsDedekindDomain S] [Infinite S]
    {m : ℕ}
    {a b : S} (hab : 0 ≤ Algebra.norm ℤ a * Algebra.norm ℤ b)
    (h : a - b ∈ Ideal.span {(m : S)}) :
    (Ideal.absNorm (Ideal.span {a}) : ZMod m) = Ideal.absNorm (Ideal.span {b}) := by
  rw [Ideal.absNorm_span_singleton, Ideal.absNorm_span_singleton]
  exact ZMod.natCast_natAbs_eq_of_mul_nonneg hab (Algebra.intCast_norm_eq_of_sub_mem_span_natCast h)

end AbsNormCongruence
