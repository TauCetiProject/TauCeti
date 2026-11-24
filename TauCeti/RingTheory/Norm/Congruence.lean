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

end IntCongruence
