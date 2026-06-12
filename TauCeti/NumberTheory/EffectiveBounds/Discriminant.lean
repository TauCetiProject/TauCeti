/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.RingTheory.Trace.Basic

/-!
# An effective discriminant bound from an integral basis

For a number field `K`, the discriminant of any `ℚ`-basis consisting of algebraic integers
is a nonzero-integer-square multiple of the field discriminant `d_K`, so it bounds `|d_K|`
from above:

`|d_K| ≤ |disc b|`  for every `ℚ`-basis `b` of `𝒪_K`-integers.

This is the elementary upper half of the effective-bounds roadmap (the deep content is the
matching Minkowski lower bound). A supporting fact: in a number field, an element whose
square is rational but which is itself irrational has trace zero.

## Main results

* `TauCeti.NumberField.trace_eq_zero_of_sq_ratCast`: `x² ∈ ℚ`, `x ∉ ℚ` ⟹ `Tr x = 0`.
* `TauCeti.NumberField.abs_discr_le_of_basis_isIntegral`: `|d_K| ≤ |disc b|` for an
  integral basis `b`.

## Provenance

Migrated from
[kim-em/erdos-unit-distance](https://github.com/kim-em/erdos-unit-distance), the
formalization of L. Alpöge's disproof of the uniform-constant Erdős unit-distance
conjecture, where these were the discriminant inputs to a class-number bound; both
statements hold over an arbitrary number field.
-/

open Polynomial Module

namespace TauCeti.NumberField

/-- In a number field, an element `x` with `x² ∈ ℚ` but `x ∉ ℚ` has trace zero: its minimal
polynomial is `X² - r`, whose subleading coefficient vanishes. -/
theorem trace_eq_zero_of_sq_ratCast {K : Type*} [Field K] [NumberField K] {x : K} {r : ℚ}
    (hx2 : x ^ 2 = algebraMap ℚ K r) (hx : x ∉ (algebraMap ℚ K).range) :
    Algebra.trace ℚ K x = 0 := by
  have hmonic : (X ^ 2 - C r).Monic := Polynomial.monic_X_pow_sub_C r (by norm_num)
  have haeval : aeval x (X ^ 2 - C r : ℚ[X]) = 0 := by simp [hx2]
  have hdvd : minpoly ℚ x ∣ (X ^ 2 - C r) := minpoly.dvd ℚ x haeval
  have hint : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
  have hne : (X ^ 2 - C r : ℚ[X]) ≠ 0 := Polynomial.X_pow_sub_C_ne_zero (by norm_num) r
  have hdeg2 : (minpoly ℚ x).natDegree = 2 := by
    have hle : (minpoly ℚ x).natDegree ≤ 2 := by
      have := Polynomial.natDegree_le_of_dvd hdvd hne
      simpa [Polynomial.natDegree_X_pow_sub_C] using this
    have hge : 2 ≤ (minpoly ℚ x).natDegree := by
      by_contra h
      rw [not_le] at h
      interval_cases hh : (minpoly ℚ x).natDegree
      · exact (minpoly.natDegree_pos hint).ne' hh
      · exact hx (minpoly.natDegree_eq_one_iff.mp hh)
    omega
  have heq : minpoly ℚ x = X ^ 2 - C r :=
    (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hmonic hdvd
      (by rw [hdeg2, Polynomial.natDegree_X_pow_sub_C])).symm
  rw [trace_eq_finrank_mul_minpoly_nextCoeff, heq]
  have hnc : (X ^ 2 - C r : ℚ[X]).nextCoeff = 0 := by
    rw [Polynomial.nextCoeff_of_natDegree_pos
      (by rw [Polynomial.natDegree_X_pow_sub_C]; norm_num)]
    simp [Polynomial.coeff_X_pow]
  rw [hnc]; simp

/-- If `b` is a `ℚ`-basis of a number field `K` consisting of algebraic integers, then
`|d_K| ≤ |disc b|`. The discriminant of any basis of integers is `(index)² · d_K` with the
index a nonzero integer, so `|disc b| = index² · |d_K| ≥ |d_K|`. -/
theorem abs_discr_le_of_basis_isIntegral {K : Type*} [Field K] [NumberField K]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℚ K)
    (hb : ∀ i, IsIntegral ℤ (b i)) :
    |(NumberField.discr K : ℚ)| ≤ |Algebra.discr ℚ (b : ι → K)| := by
  classical
  -- `c` is the canonical integral basis of `K`.
  set c := NumberField.integralBasis K with hc
  -- Reindex `c` to `ι` (both have `[K : ℚ]` elements).
  obtain ⟨e, -⟩ : ∃ _ : Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers K) ≃ ι, True := by
    refine ⟨Fintype.equivOfCardEq ?_, trivial⟩
    rw [← Module.finrank_eq_card_basis c, ← Module.finrank_eq_card_basis b]
  -- Change of basis: `disc b = (det P)² · disc c = (det P)² · d_K`, with `P = c'.toMatrix b`.
  set P : Matrix ι ι ℚ := (c.reindex e).toMatrix b with hPdef
  have hdiscc : Algebra.discr ℚ (c.reindex e) = (NumberField.discr K : ℚ) := by
    rw [Module.Basis.coe_reindex, Algebra.discr_reindex, hc, NumberField.coe_discr]
  have hP : Algebra.discr ℚ b = P.det ^ 2 * (NumberField.discr K : ℚ) := by
    rw [← hdiscc]
    convert Algebra.discr_of_matrix_vecMul (c.reindex e) P using 2
    convert (Module.Basis.toMatrix_map_vecMul (c.reindex e) b).symm using 1
  -- `P` has integer entries (the `b j` are algebraic integers), so `det P` is an integer.
  obtain ⟨d, hd⟩ : ∃ d : ℤ, P.det = d := by
    have hP_int : ∀ i j, ∃ z : ℤ, P i j = z := by
      intro i j
      obtain ⟨y, hy⟩ : ∃ y : NumberField.RingOfIntegers K, b j = algebraMap _ K y :=
        ⟨⟨b j, hb j⟩, rfl⟩
      refine ⟨(NumberField.RingOfIntegers.basis K).repr y (e.symm i), ?_⟩
      rw [hPdef, Module.Basis.toMatrix_apply, Module.Basis.repr_reindex_apply, hc, hy]
      simp
    choose f hf using hP_int
    exact ⟨(Matrix.of f).det, by simp [hf, Matrix.det_apply']⟩
  rw [hP, abs_mul, hd]
  rcases eq_or_ne d 0 with hd0 | hd0
  · exact absurd (by rw [hP, hd, hd0]; push_cast; ring)
      (Algebra.discr_not_zero_of_basis ℚ b)
  · refine le_mul_of_one_le_left (abs_nonneg _) ?_
    rw [abs_pow]
    exact one_le_pow₀ (by exact_mod_cast Int.one_le_abs hd0)

end TauCeti.NumberField
