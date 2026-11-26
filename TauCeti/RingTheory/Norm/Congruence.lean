/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.Data.ZMod.Basic

/-!
# Congruences of norms

Let `S` be a possibly noncommutative `R`-algebra over a commutative ring `R`, and `I` an ideal of
`R`. Elements of `S` congruent modulo the extended ideal `IS` have norms congruent modulo `I`; the
norms are the determinants of left multiplication, and they are `1` outside the algebras that are
free of finite rank. Over `R = ℤ` and `I = (m)` this gives congruences of integer norms modulo `m`,
which supply congruences for absolute norms of principal ideals when the integer norms have
nonnegative product.

## Main results

* `Algebra.norm_sub_norm_mem_of_sub_mem_map`: elements congruent modulo `IS` have norms
  congruent modulo `I`.
* `Algebra.intCast_norm_eq_of_sub_mem_span_natCast`: congruent elements have congruent integer
  norms.
* `Algebra.norm_eq_one_of_isUnit_of_sub_one_mem_span_natCast`: a unit congruent to `1` modulo
  `m > 2` has integer norm `1`.
-/

public section

section Congruence

variable {R S : Type*} [CommRing R] [Ring S] [Algebra R S]

/-- **Congruent elements have congruent norms.** If `a ≡ b` modulo the extension `IS` of an ideal
`I` of `R` to an `R`-algebra `S`, then `N(a) ≡ N(b)` modulo `I`. Commutativity of `S` is not
required: the norm is the determinant of left multiplication. When `S` is not free of finite rank
both norms are `1`. -/
theorem Algebra.norm_sub_norm_mem_of_sub_mem_map {I : Ideal R} {a b : S}
    (h : a - b ∈ I.map (algebraMap R S)) :
    Algebra.norm R a - Algebra.norm R b ∈ I := by
  classical
  by_cases hB : ∃ s : Finset S, Nonempty (Module.Basis s R S)
  swap
  · simp [Algebra.norm_eq_one_of_not_exists_basis R hB]
  obtain ⟨s, ⟨B⟩⟩ := hB
  -- Left multiplication matrices reduced modulo `I`; this ring map kills `IS`.
  let g := (Ideal.Quotient.mk I).mapMatrix.comp (Algebra.leftMulMatrix B).toRingHom
  have hI : I.map (algebraMap R S) ≤ RingHom.ker g :=
    Ideal.map_le_iff_le_comap.mpr fun r hr ↦ by
      simp [g, IsScalarTower.algebraMap_apply R (R ⧸ I), Ideal.Quotient.eq_zero_iff_mem.mpr hr]
  rw [← Ideal.Quotient.eq, Algebra.norm_eq_matrix_det B, Algebra.norm_eq_matrix_det B,
    RingHom.map_det, RingHom.map_det]
  exact congrArg Matrix.det ((RingHom.sub_mem_ker_iff g).mp (hI h))

end Congruence

section IntCongruence

variable {S : Type*} [Ring S]

/-- **Congruent elements have congruent integer norms.** If `a ≡ b` modulo the ideal `(m)` of a
ring `S`, then `N(a) ≡ N(b)` modulo `m`. The ring need not be commutative. -/
theorem Algebra.intCast_norm_eq_of_sub_mem_span_natCast {m : ℕ} {a b : S}
    (h : a - b ∈ Ideal.span {(m : S)}) :
    ((Algebra.norm ℤ a : ℤ) : ZMod m) = ((Algebra.norm ℤ b : ℤ) : ZMod m) := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub, ← neg_sub, dvd_neg, ← Ideal.mem_span_singleton]
  exact Algebra.norm_sub_norm_mem_of_sub_mem_map (by simpa [Ideal.map_span] using h)

/-- **Units congruent to one modulo `m > 2` have integer norm one.** Since `a` is a unit, its
integer norm is `±1`, while congruence `a ≡ 1 (mod m)` makes the norm congruent to `1` modulo `m`,
ruling out `-1` when `2 < m`. -/
theorem Algebra.norm_eq_one_of_isUnit_of_sub_one_mem_span_natCast {m : ℕ} (hm : 2 < m)
    {a : S} (ha : IsUnit a) (h : a - 1 ∈ Ideal.span {(m : S)}) :
    Algebra.norm ℤ a = 1 := by
  rcases Int.isUnit_iff.mp (ha.map (Algebra.norm ℤ)) with h1 | hneg
  · exact h1
  · have hc := Algebra.intCast_norm_eq_of_sub_mem_span_natCast (a := a) (b := 1) h
    rw [hneg, map_one, Int.cast_neg, Int.cast_one, neg_eq_iff_add_eq_zero, one_add_one_eq_two,
      ← Nat.cast_two, ZMod.natCast_eq_zero_iff] at hc
    exact absurd (Nat.le_of_dvd (by decide) hc) (not_le_of_gt hm)

end IntCongruence
