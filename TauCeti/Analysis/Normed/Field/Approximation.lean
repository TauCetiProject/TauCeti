/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Approximation
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.Minpoly.Field

import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Approximating algebraic elements by roots of polynomials over a dense subfield

Let `L` be an algebraically closed normed field over a normed field `K`, and let `k` be a field
whose image in `K` is dense. Every element of `L` algebraic over `K` is a limit of elements of
`L` algebraic over `k`: approximate the minimal polynomial over `K` by a monic polynomial over
`k` (`Polynomial.exists_monic_and_natDegree_eq_and_norm_map_algebraMap_coeff_sub_lt`), which
splits in `L` and has a root close to the original element by continuity of roots
(`Polynomial.exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt`).

For `k = ℚ` and `K = ℚ_p` this shows that the algebraic numbers are dense in `ℂ_p`, so `ℂ_p` is
separable.

## Main results

* `IsAlgebraic.mem_closure_setOf_isAlgebraic`: an element of `L` algebraic over `K` lies in the
  closure of the elements algebraic over `k`.

## References

* A. M. Robert, *A Course in p-adic Analysis*, Graduate Texts in Mathematics 198, Springer, 2000,
  Chapter 3, for the density of the algebraic numbers in `ℂ_p` and the separability of `ℂ_p`.
-/

public section

open Polynomial

variable {k K L : Type*} [Field k] [NormedField K] [NormedField L] [NormedAlgebra K L]
  [Algebra k K] [Algebra k L] [IsScalarTower k K L] [IsAlgClosed L]

/-- **Elements algebraic over `K` are limits of elements algebraic over a dense subfield `k`**,
in an algebraically closed normed field `L` over `K`. -/
theorem IsAlgebraic.mem_closure_setOf_isAlgebraic {x : L} (hx : IsAlgebraic K x)
    (hk : DenseRange (algebraMap k K)) : x ∈ closure {y : L | IsAlgebraic k y} := by
  have hfm : (minpoly K x).Monic := minpoly.monic hx.isIntegral
  have hn : (minpoly K x).natDegree ≠ 0 := (minpoly.natDegree_pos hx.isIntegral).ne'
  refine Metric.mem_closure_iff.mpr fun δ hδ ↦ ?_
  have hM : 0 < max ‖x‖ 1 := lt_max_of_lt_right one_pos
  -- the coefficient precision that continuity of roots turns into the distance `δ`
  set ε := (δ / max ‖x‖ 1) ^ (minpoly K x).natDegree / ((minpoly K x).natDegree + 1) with hε_def
  have hε : 0 < ε := by positivity
  obtain ⟨g, hgm, hdeg, hcoeff⟩ :=
    exists_monic_and_natDegree_eq_and_norm_map_algebraMap_coeff_sub_lt hk hfm hε
  obtain ⟨b, hb, hxb⟩ := exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt hε (minpoly.aeval K x) hfm
    (hgm.map _) (by rw [natDegree_map, hdeg]) hcoeff (IsAlgClosed.splits _)
  refine ⟨b, ⟨g, hgm.ne_zero, ?_⟩, ?_⟩
  · simpa only [aeval_map_algebraMap] using (mem_aroots.mp hb).2
  · have hprec : ((minpoly K x).natDegree + 1) * ε = (δ / max ‖x‖ 1) ^ (minpoly K x).natDegree :=
      by rw [hε_def]; field_simp
    rwa [hprec, Real.pow_rpow_inv_natCast (div_pos hδ hM).le hn, div_mul_cancel₀ _ hM.ne',
      ← dist_eq_norm] at hxb
