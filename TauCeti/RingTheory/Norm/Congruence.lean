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

Let `S` be a possibly noncommutative algebra that is free of finite rank over a commutative ring
`R`, and `I` an ideal of `R`. Elements of `S` congruent modulo the extended ideal `IS` have norms
congruent modulo `I`; the norms are the determinants of left multiplication. Consequently, if `S`
is nontrivial, then `IS` is the unit ideal only when `I` is. Over `R = ℤ` and `I = (m)` this gives
congruences of integer norms modulo `m`, which supply congruences for absolute norms of principal
ideals when the integer norms have nonnegative product.

## Main results

* `Algebra.norm_sub_norm_mem_of_sub_mem_map`: elements congruent modulo `IS` have norms
  congruent modulo `I`.
* `Ideal.map_algebraMap_eq_top_iff`: in a nontrivial finite free `R`-algebra, the extension of
  `I` is the unit ideal exactly when `I` is.
* `Algebra.intCast_norm_eq_of_sub_mem_span_natCast`: congruent elements have congruent integer
  norms.
* `Ideal.span_singleton_natCast_eq_top_iff`: in a nontrivial finite free `ℤ`-algebra,
  the ideal `(m)` is the unit ideal exactly when `m = 1`.
-/

public section

section Congruence

variable {R S : Type*} [CommRing R] [Ring S] [Algebra R S] [Module.Free R S] [Module.Finite R S]

/-- **Congruent elements have congruent norms.** If `a ≡ b` modulo the extension `IS` of an ideal
`I` of `R` to an `R`-algebra `S` that is free of finite rank, then `N(a) ≡ N(b)` modulo `I`.
Commutativity of `S` is not required: the norm is the determinant of left multiplication. -/
theorem Algebra.norm_sub_norm_mem_of_sub_mem_map {I : Ideal R} {a b : S}
    (h : a - b ∈ I.map (algebraMap R S)) :
    Algebra.norm R a - Algebra.norm R b ∈ I := by
  let B := Module.Free.chooseBasis R S
  -- Left multiplication matrices reduced modulo `I`; this ring map kills `IS`.
  let g := (Ideal.Quotient.mk I).mapMatrix.comp (Algebra.leftMulMatrix B).toRingHom
  have hI : I.map (algebraMap R S) ≤ RingHom.ker g :=
    Ideal.map_le_iff_le_comap.mpr fun r hr ↦ by
      simp [g, IsScalarTower.algebraMap_apply R (R ⧸ I), Ideal.Quotient.eq_zero_iff_mem.mpr hr]
  rw [← Ideal.Quotient.eq, Algebra.norm_eq_matrix_det B, Algebra.norm_eq_matrix_det B,
    RingHom.map_det, RingHom.map_det]
  exact congrArg Matrix.det ((RingHom.sub_mem_ker_iff g).mp (hI h))

/-- **An extended ideal is the unit ideal only if the ideal is.** If `S` is a nontrivial
`R`-algebra that is free of finite rank, then `IS = S` exactly when `I = R`. The algebra need not
be commutative. -/
theorem Ideal.map_algebraMap_eq_top_iff [Nontrivial S] {I : Ideal R} :
    I.map (algebraMap R S) = ⊤ ↔ I = ⊤ := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ Ideal.map_top _⟩
  -- `1 ≡ 0` modulo `IS`, so `1 = N(1) ≡ N(0) = 0` modulo `I`.
  have := Algebra.norm_sub_norm_mem_of_sub_mem_map (a := (1 : S)) (b := 0) (h ▸ Submodule.mem_top)
  simpa [Ideal.eq_top_iff_one] using this

end Congruence

section IntCongruence

variable {S : Type*} [Ring S] [Module.Free ℤ S] [Module.Finite ℤ S]

/-- **Congruent elements have congruent integer norms.** If `a ≡ b` modulo the ideal `(m)` of a
ring `S` that is free of finite rank over `ℤ`, then `N(a) ≡ N(b)` modulo `m`. The ring need not be
commutative. -/
theorem Algebra.intCast_norm_eq_of_sub_mem_span_natCast {m : ℕ} {a b : S}
    (h : a - b ∈ Ideal.span {(m : S)}) :
    ((Algebra.norm ℤ a : ℤ) : ZMod m) = ((Algebra.norm ℤ b : ℤ) : ZMod m) := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub, ← neg_sub, dvd_neg, ← Ideal.mem_span_singleton]
  exact Algebra.norm_sub_norm_mem_of_sub_mem_map (by simpa [Ideal.map_span] using h)

/-- **The ideal `(m)` is the unit ideal only for `m = 1`**, in a nontrivial ring that is free of
finite rank over `ℤ`. The ring need not be commutative. -/
theorem Ideal.span_singleton_natCast_eq_top_iff [Nontrivial S] {m : ℕ} :
    Ideal.span {(m : S)} = ⊤ ↔ m = 1 := by
  rw [← map_natCast (algebraMap ℤ S), ← Set.image_singleton, ← Ideal.map_span,
    Ideal.map_algebraMap_eq_top_iff, Ideal.span_singleton_eq_top, Int.isUnit_iff_natAbs_eq,
    Int.natAbs_natCast]

end IntCongruence
