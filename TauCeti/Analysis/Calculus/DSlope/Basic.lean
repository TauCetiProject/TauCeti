/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DSlope

/-!
# Elementary facts about `dslope`

Divided-slope facts that need no differentiability. Away from its base point `dslope` is the plain
difference quotient, so these are statements about a normed field and its norm, with no calculus
in them.

## Main results

* `TauCeti.dslope_comm`: `dslope` is symmetric in its two point arguments.
* `TauCeti.norm_dslope_eq_one_of_norm_sub_map_eq`: a map that moves two points exactly as far
  apart as they already are has unimodular difference quotient between them. This is the
  hypothesis the equality case of Schwarz's lemma
  (`Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div`) takes, and the two Tau Ceti consumers of
  that equality case — the Schwarz--Pick rigidity theorem and the classification of the disc
  rotations — reach it by exactly this route, at base point `0`.
* `TauCeti.sum_add_pow_sub_smul_iterate_dslope`: Taylor's formula with divided-difference
  remainder, `f b = Σ_{j<n} (b - a)^j • c_j + (b - a)^n • q_n b`, where `c_j` is the value at `a`
  of the `j`-th iterated divided difference `(swap dslope a)^[j] f` and `q_n` is the `n`-th one.
  For an analytic `f` the `c_j` are its Taylor coefficients at `a` and `q_n` is analytic.
-/

public section

namespace TauCeti

/-- `dslope` is symmetric in its two point arguments: off the diagonal both sides are the same
difference quotient, and on the diagonal they coincide trivially. -/
theorem dslope_comm {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (f : 𝕜 → E) (a b : 𝕜) : dslope f a b = dslope f b a := by
  rcases eq_or_ne b a with rfl | h
  · rfl
  · rw [dslope_of_ne f h, dslope_of_ne f h.symm, slope_comm]

/-- **A map preserving the distance between two points has unit difference quotient between
them.** For `y ≠ x` with `‖g y - g x‖ = ‖y - x‖`, the difference quotient `dslope g x y` is
unimodular.

No differentiability is involved: away from the base point `dslope` is the plain difference
quotient. -/
lemma norm_dslope_eq_one_of_norm_sub_map_eq {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {g : 𝕜 → E} {x y : 𝕜} (hxy : y ≠ x)
    (hnorm : ‖g y - g x‖ = ‖y - x‖) : ‖dslope g x y‖ = 1 := by
  rw [dslope_of_ne _ hxy, slope_def_module, norm_smul, norm_inv, hnorm,
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy))]

/-- **Taylor's formula with divided-difference remainder.** For every function `f` and every `n`,
`f b = Σ_{j<n} (b - a)^j • c_j + (b - a)^n • q_n b`, where `c_j = (swap dslope a)^[j] f a` and
`q_n = (swap dslope a)^[n] f`. This is `n` applications of `f b = f a + (b - a) • dslope f a b`.
When the `c_j` vanish this is Mathlib's `pow_sub_smul_iterate_dslope_of_zero`. -/
theorem sum_add_pow_sub_smul_iterate_dslope {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (f : 𝕜 → E) (a b : 𝕜) (n : ℕ) :
    ∑ j ∈ Finset.range n, (b - a) ^ j • (Function.swap dslope a)^[j] f a +
      (b - a) ^ n • (Function.swap dslope a)^[n] f b = f b := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    simp only [Finset.sum_range_succ', Function.iterate_succ_apply, pow_succ', mul_smul,
      ← Finset.smul_sum, pow_zero, one_smul, Function.iterate_zero_apply]
    rw [add_right_comm, ← smul_add, ih]
    exact eq_sub_iff_add_eq.1 (sub_smul_dslope f a b)

end TauCeti
