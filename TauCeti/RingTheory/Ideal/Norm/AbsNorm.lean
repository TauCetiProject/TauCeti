/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import TauCeti.Data.ZMod.Divisibility

/-!
# The absolute ideal norm under a ring isomorphism, and congruences of norms

Identifying two rings along an isomorphism identifies their ideals, and the absolute norm is
insensitive to that identification.

In a ring that is free of finite rank over `ℤ`, elements congruent modulo `(m)` have norms
congruent modulo `m`; for principal ideals whose generators have norms with nonnegative product,
the congruence passes to the absolute norms.

## Main results

* `Ideal.absNorm_comap_of_ringEquiv`, `Ideal.absNorm_map_of_ringEquiv`: the absolute norm of an
  ideal is unchanged by transporting it along a ring isomorphism, in either direction.
* `Algebra.intCast_norm_eq_of_sub_mem_span_natCast`: elements congruent modulo `(m)` have norms
  congruent modulo `m`.
* `Ideal.span_singleton_natCast_eq_top_iff`: the ideal `(m)` is the unit ideal only for `m = 1`.
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

section Congruence

variable {S : Type*} [CommRing S] [Module.Free ℤ S] [Module.Finite ℤ S]

/-- **Congruent elements have congruent norms.** If `a ≡ b` modulo the ideal `(m)` of a ring `S`
that is free of finite rank over `ℤ`, then `N(a) ≡ N(b)` modulo `m`. -/
theorem Algebra.intCast_norm_eq_of_sub_mem_span_natCast {m : ℕ} {a b : S}
    (h : a - b ∈ Ideal.span {(m : S)}) :
    ((Algebra.norm ℤ a : ℤ) : ZMod m) = ((Algebra.norm ℤ b : ℤ) : ZMod m) := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h
  let B := Module.Free.chooseBasis ℤ S
  rw [Algebra.norm_eq_matrix_det B, Algebra.norm_eq_matrix_det B,
    ← eq_intCast (Int.castRingHom (ZMod m)) (Algebra.leftMulMatrix B a).det,
    ← eq_intCast (Int.castRingHom (ZMod m)) (Algebra.leftMulMatrix B b).det, RingHom.map_det,
    RingHom.map_det, sub_eq_iff_eq_add.mp hc.symm, map_add, map_mul, map_natCast, map_add,
    map_mul, map_natCast, ← Matrix.diagonal_natCast, ZMod.natCast_self, Matrix.diagonal_zero,
    mul_zero, zero_add]

/-- **The ideal `(m)` is the unit ideal only for `m = 1`**, in a nontrivial ring that is free of
finite rank over `ℤ`. -/
theorem Ideal.span_singleton_natCast_eq_top_iff [Nontrivial S] {m : ℕ} :
    Ideal.span {(m : S)} = ⊤ ↔ m = 1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  -- the norm `m ^ [S : ℤ]` of the unit `m` is a unit of `ℤ`
  have hu := Int.isUnit_iff_natAbs_eq.mp
    ((Ideal.span_singleton_eq_top.mp h).map (Algebra.norm ℤ (S := S)))
  rw [Algebra.norm_natCast, Int.natAbs_pow, Int.natAbs_natCast] at hu
  exact (Nat.pow_eq_one.mp hu).resolve_right Module.finrank_pos.ne'

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

end Congruence


