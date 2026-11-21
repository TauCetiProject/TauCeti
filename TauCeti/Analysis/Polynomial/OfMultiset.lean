/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Norm bounds for polynomials given by a multiset of roots

For a multiset `s` of elements in a seminormed commutative ring `R` with `‖1‖ = 1`, the polynomial
`Polynomial.ofMultiset s = (s.map fun ζ ↦ X - C ζ).prod` satisfies
`‖(ofMultiset s).eval w‖ ≤ B ^ s.card` whenever every `ζ ∈ s` satisfies `‖w - ζ‖ ≤ B`. In
particular, if every element of `s` and `w` itself lie in the closed ball `Metric.closedBall c r`,
then `‖(ofMultiset s).eval w‖ ≤ (2 * r) ^ s.card`.

## Main results

* `Polynomial.norm_eval_ofMultiset_le_pow`: `‖(ofMultiset s).eval w‖ ≤ B ^ s.card` when
  `∀ ζ ∈ s, ‖w - ζ‖ ≤ B`.
* `Polynomial.norm_eval_ofMultiset_le_two_mul_pow`: `‖(ofMultiset s).eval w‖ ≤ (2 * r) ^ s.card`
  when `∀ ζ ∈ s, ζ ∈ Metric.closedBall c r` and `w ∈ Metric.closedBall c r`.
-/

public section

namespace Polynomial

variable {R : Type*} [SeminormedCommRing R] [NormOneClass R]

/-- If every `ζ ∈ s` satisfies `‖w - ζ‖ ≤ B`, then `‖(ofMultiset s).eval w‖ ≤ B ^ s.card`. -/
theorem norm_eval_ofMultiset_le_pow {s : Multiset R} {w : R} {B : ℝ}
    (hB : ∀ ζ ∈ s, ‖w - ζ‖ ≤ B) :
    ‖(ofMultiset s).eval w‖ ≤ B ^ s.card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons ζ s ih =>
    have hζ : ‖w - ζ‖ ≤ B := hB ζ (Multiset.mem_cons_self _ _)
    have hB0 : 0 ≤ B := (norm_nonneg _).trans hζ
    rw [ofMultiset_apply, Multiset.map_cons, Multiset.prod_cons, eval_mul, eval_sub, eval_X,
      eval_C, Multiset.card_cons, pow_succ']
    exact (norm_mul_le _ _).trans (mul_le_mul hζ
      (ih fun η hη ↦ hB η (Multiset.mem_cons_of_mem hη)) (norm_nonneg _) hB0)

/-- If every `ζ ∈ s` and `w` belong to `Metric.closedBall c r`, then
`‖(ofMultiset s).eval w‖ ≤ (2 * r) ^ s.card`. -/
theorem norm_eval_ofMultiset_le_two_mul_pow {s : Multiset R} {c w : R} {r : ℝ}
    (hs : ∀ ζ ∈ s, ζ ∈ Metric.closedBall c r) (hw : w ∈ Metric.closedBall c r) :
    ‖(ofMultiset s).eval w‖ ≤ (2 * r) ^ s.card := by
  refine norm_eval_ofMultiset_le_pow fun ζ hζ ↦ ?_
  rw [← dist_eq_norm, two_mul]
  exact (dist_triangle_right w ζ c).trans
    (add_le_add (Metric.mem_closedBall.mp hw) (Metric.mem_closedBall.mp (hs ζ hζ)))

end Polynomial
