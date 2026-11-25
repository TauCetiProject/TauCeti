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

* `IsAlgebraic.exists_monic_and_natDegree_eq_and_aeval_eq_zero_and_norm_sub_lt`: an element of `L`
  algebraic over `K` is arbitrarily close to a root of a monic polynomial over `k` of the same
  degree as its minimal polynomial.
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

/-- **An element algebraic over `K` is close to a root of a polynomial over a dense subfield `k`**
of the same degree as its minimal polynomial, in an algebraically closed normed field `L` over `K`:
for every `δ > 0` there is a monic `g` over `k` with `deg g = deg (minpoly K x)` and a root `y` of
`g` in `L` with `‖x - y‖ < δ`. -/
theorem IsAlgebraic.exists_monic_and_natDegree_eq_and_aeval_eq_zero_and_norm_sub_lt {x : L}
    (hx : IsAlgebraic K x) (hk : DenseRange (algebraMap k K)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (g : k[X]) (y : L), g.Monic ∧ (minpoly K x).natDegree = g.natDegree ∧ aeval y g = 0 ∧
      ‖x - y‖ < δ := by
  have hfm : (minpoly K x).Monic := minpoly.monic hx.isIntegral
  have hn : (minpoly K x).natDegree ≠ 0 := (minpoly.natDegree_pos hx.isIntegral).ne'
  have hM : 0 < max ‖x‖ 1 := lt_max_of_lt_right one_pos
  -- the coefficient precision that continuity of roots turns into the distance `δ`
  have hε : 0 < (δ / max ‖x‖ 1) ^ (minpoly K x).natDegree / ((minpoly K x).natDegree + 1) := by
    positivity
  obtain ⟨g, hgm, hdeg, hcoeff⟩ :=
    exists_monic_and_natDegree_eq_and_norm_map_algebraMap_coeff_sub_lt hk hfm hε
  obtain ⟨b, hb, hxb⟩ := exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt hε (minpoly.aeval K x) hfm
    (hgm.map _) (by rw [natDegree_map, hdeg]) hcoeff (IsAlgClosed.splits _)
  refine ⟨g, b, hgm, hdeg, by simpa using (mem_aroots.mp hb).2, ?_⟩
  rwa [mul_div_cancel₀ _ (by positivity), Real.pow_rpow_inv_natCast (div_pos hδ hM).le hn,
    div_mul_cancel₀ _ hM.ne'] at hxb

/-- **Elements algebraic over `K` are limits of elements algebraic over a dense subfield `k`**,
in an algebraically closed normed field `L` over `K`. -/
theorem IsAlgebraic.mem_closure_setOf_isAlgebraic {x : L} (hx : IsAlgebraic K x)
    (hk : DenseRange (algebraMap k K)) : x ∈ closure {y : L | IsAlgebraic k y} := by
  refine Metric.mem_closure_iff.mpr fun δ hδ ↦ ?_
  obtain ⟨g, y, hgm, -, hgy, hxy⟩ :=
    hx.exists_monic_and_natDegree_eq_and_aeval_eq_zero_and_norm_sub_lt hk hδ
  exact ⟨y, ⟨g, hgm.ne_zero, hgy⟩, by rwa [dist_eq_norm]⟩
