/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Approximation
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.Topology.UniformSpace.Completion

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.Tactic.ComputeDegree
import TauCeti.FieldTheory.Separable.Closure

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

In the same way the separable closure of a nontrivially normed field `K'` is dense in an
algebraically closed normed field `L` algebraic over `K'`. In characteristic `p > 0`, an element
`a ∈ L` has `a ^ p ^ n = b` separable over `K'` for some `n ≥ 1`. For `t ∈ K'` nonzero the
polynomial `X ^ p ^ n - t X - b` has derivative `-t`, so its roots are separable over `K'`
(`mem_separableClosure_of_pow_sub_mul_sub_eq_zero`), and by continuity of roots
(`Polynomial.exists_roots_norm_sub_lt_of_norm_coeff_sub_lt`) one of them tends to `a` as `t → 0`.

## Main results

* `IsAlgebraic.exists_monic_and_natDegree_eq_and_aeval_eq_zero_and_norm_sub_lt`: an element of `L`
  algebraic over `K` is arbitrarily close to a root of a monic polynomial over `k` of the same
  degree as its minimal polynomial.
* `IsAlgebraic.mem_closure_setOf_isAlgebraic`: an element of `L` algebraic over `K` lies in the
  closure of the elements algebraic over `k`.
* `TauCeti.dense_separableClosure` and `TauCeti.denseRange_separableClosure_completion`: in an
  algebraically closed normed field algebraic over `K'`, and in its completion, the separable
  closure of `K'` is dense.

## References

* A. M. Robert, *A Course in p-adic Analysis*, Graduate Texts in Mathematics 198, Springer, 2000,
  Chapter 3, for the density of the algebraic numbers in `ℂ_p` and the separability of `ℂ_p`.
* A. J. de Jong and M. van der Put, *Étale cohomology of rigid analytic spaces*, Documenta Math.
  1 (1996), §3.6, for the density of the separable closure.
-/

public section

open Polynomial

section DenseSubfield

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

end DenseSubfield

namespace TauCeti

/-- **The separable closure is dense** (de Jong–van der Put, §3.6). In an algebraically closed
normed field `L`, algebraic over a nontrivially normed field `K'`, the separable closure of `K'`
is dense. -/
theorem dense_separableClosure (K' L : Type*) [NontriviallyNormedField K']
    [NormedField L] [NormedAlgebra K' L] [Algebra.IsAlgebraic K' L] [IsAlgClosed L] :
    Dense (separableClosure K' L : Set L) := by
  set E := separableClosure K' L
  refine Metric.dense_iff.2 fun a δ hδ ↦ ?_
  obtain ⟨q, hq⟩ : ∃ q, ExpChar K' q := ⟨_, ringExpChar.expChar K'⟩
  have : ExpChar L q := expChar_of_injective_algebraMap
    (algebraMap K' _).injective q
  have : ExpChar E q := expChar_of_injective_algebraMap (algebraMap K' E).injective q
  obtain ⟨n, b, hb⟩ := IsPurelyInseparable.pow_mem E q a
  have hbE : a ^ q ^ n ∈ E := hb ▸ b.property
  by_cases hN : q ^ n = 1
  · exact ⟨a, Metric.mem_ball_self hδ, by simpa [hN] using hbE⟩
  set N := q ^ n
  have hN0 : N ≠ 0 := pow_ne_zero _ (expChar_ne_zero K' q)
  have hNK : (N : K') = 0 := by
    obtain _ | ⟨hq⟩ := hq
    · simp [N] at hN
    · have hn : n ≠ 0 := by rintro rfl; simp [N] at hN
      exact (CharP.cast_eq_zero_iff K' q N).2 (dvd_pow_self q hn)
  have hN2 : 1 < N := by omega
  set M := max ‖a‖ 1
  have hM : 0 < M := lt_max_of_lt_right one_pos
  have hε : 0 < (δ / M) ^ N / (N + 1) := by positivity
  obtain ⟨t, ht0, htε⟩ := NormedField.exists_norm_lt K' hε
  let f : L[X] := X ^ N - C (a ^ N)
  let g : L[X] := X ^ N - C (algebraMap K' _ t) * X - C (a ^ N)
  have hfm : f.Monic := monic_X_pow_sub_C _ hN0
  have hfdeg : f.natDegree = N := natDegree_X_pow_sub_C _
  have hgm : g.Monic := by
    simp only [g, sub_sub]
    exact monic_X_pow_sub (by compute_degree!)
  have hgdeg : g.natDegree = N := by
    simp only [g, sub_sub]
    rw [natDegree_sub_eq_left_of_natDegree_lt] <;> rw [natDegree_X_pow]
    exact natDegree_linear_le.trans_lt hN2
  have hcoeff (i : ℕ) : ‖g.coeff i - f.coeff i‖ < (δ / M) ^ N / (N + 1) := by
    have hgf : g - f = -(C (algebraMap K' _ t) * X) := by ring
    rw [← coeff_sub, hgf, coeff_neg, coeff_C_mul_X]
    split_ifs
    · rwa [norm_neg, norm_algebraMap']
    · simpa using hε
  obtain ⟨y, hy, hay⟩ := exists_roots_norm_sub_lt_of_norm_coeff_sub_lt hε (f := f) (g := g)
    (a := a) (by simp [f]) hfm hgm (hgdeg.trans hfdeg.symm) hcoeff (IsAlgClosed.splits g)
  refine ⟨y, ?_, mem_separableClosure_of_pow_sub_mul_sub_eq_zero hNK (norm_pos_iff.1 ht0) hbE ?_⟩
  · rw [hfdeg, mul_div_cancel₀ _ (by positivity), Real.pow_rpow_inv_natCast (by positivity) hN0,
      div_mul_cancel₀ _ hM.ne'] at hay
    rwa [Metric.mem_ball, dist_comm, dist_eq_norm]
  · simpa [g, sub_sub] using (mem_roots hgm.ne_zero).1 hy

/-- **The separable closure is dense in the completion.** For an algebraically closed normed field
`L`, algebraic over a nontrivially normed field `K'`, the separable closure of `K'` in `L` has
dense image in the completion of `L`. -/
theorem denseRange_separableClosure_completion (K' L : Type*) [NontriviallyNormedField K']
    [NormedField L] [NormedAlgebra K' L] [Algebra.IsAlgebraic K' L] [IsAlgClosed L] :
    DenseRange fun x : separableClosure K' L ↦ ((x : L) : UniformSpace.Completion L) :=
  UniformSpace.Completion.denseRange_coe.comp
    (dense_separableClosure K' L).denseRange_subtypeVal (UniformSpace.Completion.continuous_coe _)

end TauCeti
