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

* `Polynomial.exists_monic_natDegree_eq_aeval_eq_zero_norm_sub_lt`: a root in `L` of a monic
  polynomial over `K` can be approximated arbitrarily closely by a root of a monic polynomial of
  the same degree over the dense subfield `k`.
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

/-- **Approximating a root of a monic polynomial by a root over a dense subfield.** If `x : L` is
a root of a monic polynomial `f ∈ K[X]` in an algebraically closed normed extension `L / K` and `k`
has dense image in `K`, then for every `δ > 0` there exist a monic polynomial `g ∈ k[X]` of the
same degree as `f` and a root `β : L` of `g` within distance `δ` of `x`. -/
theorem Polynomial.exists_monic_natDegree_eq_aeval_eq_zero_norm_sub_lt
    {f : K[X]} (hfm : f.Monic) {x : L} (hx : aeval x f = 0)
    (hk : DenseRange (algebraMap k K)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (g : k[X]) (β : L), g.Monic ∧ g.natDegree = f.natDegree ∧ aeval β g = 0 ∧ ‖x - β‖ < δ := by
  have hn : f.natDegree ≠ 0 := fun h0 ↦ by
    simp [eq_one_of_monic_natDegree_zero hfm h0] at hx
  have hM : 0 < max ‖x‖ 1 := lt_max_of_lt_right one_pos
  -- the coefficient precision that continuity of roots turns into the distance `δ`
  have hε : 0 < (δ / max ‖x‖ 1) ^ f.natDegree / (f.natDegree + 1) := by positivity
  obtain ⟨g, hgm, hdeg, hcoeff⟩ :=
    exists_monic_and_natDegree_eq_and_norm_map_algebraMap_coeff_sub_lt hk hfm hε
  obtain ⟨β, hβ, hxβ⟩ := exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt hε hx hfm
    (hgm.map _) (by rw [natDegree_map, hdeg]) hcoeff (IsAlgClosed.splits _)
  rw [mul_div_cancel₀ _ (by positivity), Real.pow_rpow_inv_natCast (div_pos hδ hM).le hn,
    div_mul_cancel₀ _ hM.ne'] at hxβ
  exact ⟨g, β, hgm, hdeg.symm, by simpa [aeval_map_algebraMap] using (mem_aroots.mp hβ).2, hxβ⟩

/-- **Elements algebraic over `K` are limits of elements algebraic over a dense subfield `k`**,
in an algebraically closed normed field `L` over `K`. -/
theorem IsAlgebraic.mem_closure_setOf_isAlgebraic {x : L} (hx : IsAlgebraic K x)
    (hk : DenseRange (algebraMap k K)) : x ∈ closure {y : L | IsAlgebraic k y} := by
  refine Metric.mem_closure_iff.mpr fun δ hδ ↦ ?_
  obtain ⟨g, β, hgm, -, hβ, hxβ⟩ :=
    exists_monic_natDegree_eq_aeval_eq_zero_norm_sub_lt (minpoly.monic hx.isIntegral)
      (minpoly.aeval K x) hk hδ
  exact ⟨β, ⟨g, hgm.ne_zero, hβ⟩, by rwa [dist_eq_norm]⟩
