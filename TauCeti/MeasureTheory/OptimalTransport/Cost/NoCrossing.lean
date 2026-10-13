/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.StrictConvexSpace
public import TauCeti.MeasureTheory.OptimalTransport.Cost.CyclicalMonotonicity
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Normed.Module.Ray

/-!
# Transport segments of a cyclically monotone set do not cross

Let `E` be a strictly convex real normed space and `1 < p`. For the cost `c (x, y) = d(x, y) ^ p`,
two pairs `(x, x')` and `(y, y')` of a `c`-cyclically monotone set cannot be moved along their
segments so as to meet at an intermediate time: if
`(1 - t) • x + t • x' = (1 - t) • y + t • y'` for some `0 < t < 1`, then `x = y` and `x' = y'`.
Equivalently, for every `0 < t < 1` the interpolation `(x, x') ↦ (1 - t) • x + t • x'` is injective
on a `c`-cyclically monotone set.

Applied to the support of an optimal coupling, this says that in the displacement interpolation of
an optimal plan no two particles occupy the same position at the same intermediate time. In
Eulerian terms, the velocity of the interpolation is then the displacement itself, with no
averaging over particles.

## Proof

Suppose the two segments meet at the point `z` at time `t`, and write `a = d(x, x')` and
`b = d(y, y')`. Going through `z` gives `d(x, y') ≤ t a + (1 - t) b` and
`d(y, x') ≤ t b + (1 - t) a`, so by convexity of `s ↦ s ^ p` the swapped cost is at most
`a ^ p + b ^ p`, which by cyclical monotonicity is at most the swapped cost. Strict convexity of
`s ↦ s ^ p` forces `a = b`, and then `d(x, y') = d(x, z) + d(z, y')`. In a strictly convex space
this equality case of the triangle inequality makes `x' - x` and `y' - y` point in the same
direction; having the same length, they are equal, and the two segments coincide.

## Main statements

* `TauCeti.eq_and_eq_of_smul_add_smul_eq`: two pairs satisfying the two-point swap inequality for
  the cost `‖· - ·‖ ^ p`, `1 < p`, whose segments meet at an intermediate time are equal.
* `TauCeti.IsCyclicallyMonotone.injOn_smul_add_smul`: for `1 < p` and `0 < t < 1`, the
  interpolation at time `t` is injective on every cyclically monotone set of the cost `d ^ p`.

## References

* C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, Springer 2009, Chapter 8, for
  the absence of crossings in displacement interpolation.
* L. Ambrosio, N. Gigli and G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, Birkhäuser, 2nd ed. 2008, Lemma 7.2.1.
-/

public section

open Set

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [StrictConvexSpace ℝ E]

/-- **Two-point no-crossing.** In a strictly convex real normed space, let `1 < p` and
`0 < t < 1`. If the pairs `(x, x')` and `(y, y')` satisfy the two-point swap inequality
`‖x - x'‖ ^ p + ‖y - y'‖ ^ p ≤ ‖x - y'‖ ^ p + ‖y - x'‖ ^ p` for the cost `‖· - ·‖ ^ p` and their
segments meet at time `t`, i.e. `(1 - t) • x + t • x' = (1 - t) • y + t • y'`, then `x = y` and
`x' = y'`. -/
theorem eq_and_eq_of_smul_add_smul_eq {p t : ℝ} (hp : 1 < p) (ht : t ∈ Ioo (0 : ℝ) 1)
    {x x' y y' : E} (h : ‖x - x'‖ ^ p + ‖y - y'‖ ^ p ≤ ‖x - y'‖ ^ p + ‖y - x'‖ ^ p)
    (he : (1 - t) • x + t • x' = (1 - t) • y + t • y') : x = y ∧ x' = y' := by
  obtain ⟨ht₀, ht₁⟩ := ht
  have ht₁' : 0 < 1 - t := sub_pos.2 ht₁
  set z := (1 - t) • x + t • x' with hz
  -- the two pieces of each broken path through `z`
  have h₁ : x - z = t • (x - x') := by rw [hz]; module
  have h₂ : z - y' = (1 - t) • (y - y') := by rw [he]; module
  have h₃ : y - z = t • (y - y') := by rw [he]; module
  have h₄ : z - x' = (1 - t) • (x - x') := by rw [hz]; module
  have hxy' : ‖x - y'‖ ≤ t * ‖x - x'‖ + (1 - t) * ‖y - y'‖ := by
    calc ‖x - y'‖ = ‖(x - z) + (z - y')‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖x - z‖ + ‖z - y'‖ := norm_add_le _ _
      _ = t * ‖x - x'‖ + (1 - t) * ‖y - y'‖ := by
        rw [h₁, h₂, norm_smul, norm_smul, Real.norm_of_nonneg ht₀.le,
          Real.norm_of_nonneg ht₁'.le]
  have hyx' : ‖y - x'‖ ≤ t * ‖y - y'‖ + (1 - t) * ‖x - x'‖ := by
    calc ‖y - x'‖ = ‖(y - z) + (z - x')‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖y - z‖ + ‖z - x'‖ := norm_add_le _ _
      _ = t * ‖y - y'‖ + (1 - t) * ‖x - x'‖ := by
        rw [h₃, h₄, norm_smul, norm_smul, Real.norm_of_nonneg ht₀.le,
          Real.norm_of_nonneg ht₁'.le]
  have ha : 0 ≤ ‖x - x'‖ := norm_nonneg _
  have hb : 0 ≤ ‖y - y'‖ := norm_nonneg _
  have hp₀ : 0 ≤ p := zero_le_one.trans hp.le
  have hsum : t + (1 - t) = 1 := by ring
  -- convexity of `s ↦ s ^ p` bounds the swapped cost by the diagonal cost
  have hc₂ : ‖y - x'‖ ^ p ≤ t * ‖y - y'‖ ^ p + (1 - t) * ‖x - x'‖ ^ p :=
    (Real.rpow_le_rpow (norm_nonneg _) hyx' hp₀).trans
      ((convexOn_rpow hp.le).2 hb ha ht₀.le ht₁'.le hsum)
  -- strict convexity forces the two segments to have the same length
  have hab : ‖x - x'‖ = ‖y - y'‖ := by
    by_contra hne
    have hs := (strictConvexOn_rpow hp).2 (mem_Ici.2 ha) (mem_Ici.2 hb) hne ht₀ ht₁' hsum
    simp only [smul_eq_mul] at hs
    linarith [(Real.rpow_le_rpow (norm_nonneg _) hxy' hp₀).trans_lt hs]
  rw [← hab] at hxy' hc₂ h
  -- so the broken path from `x` to `y'` through `z` is as short as the straight one
  have hxy'_eq : ‖x - y'‖ = ‖x - z‖ + ‖z - y'‖ := by
    rw [h₁, h₂, norm_smul, norm_smul, Real.norm_of_nonneg ht₀.le, Real.norm_of_nonneg ht₁'.le,
      ← hab, ← add_mul, hsum, one_mul]
    rw [← add_mul, hsum, one_mul] at hxy' hc₂
    refine le_antisymm hxy' (not_lt.1 fun hlt ↦ ?_)
    linarith [Real.rpow_lt_rpow (norm_nonneg _) hlt (zero_lt_one.trans hp)]
  -- the equality case of the triangle inequality in a strictly convex space
  have hray : SameRay ℝ (t • (x - x')) ((1 - t) • (y - y')) := by
    rw [← h₁, ← h₂]
    exact sameRay_iff_norm_add.2 (by rw [sub_add_sub_cancel, hxy'_eq])
  have hray' : SameRay ℝ (x - x') (y - y') := by
    have := (hray.pos_smul_left (inv_pos.2 ht₀)).pos_smul_right (inv_pos.2 ht₁')
    rwa [smul_smul, smul_smul, inv_mul_cancel₀ ht₀.ne', inv_mul_cancel₀ ht₁'.ne', one_smul,
      one_smul] at this
  have hd : x - x' = y - y' := hray'.eq_of_norm_eq hab
  -- equal displacements meeting at time `t` start at the same point
  have hxy : x = y := by
    have hmeet : x - t • (x - x') = y - t • (y - y') := by
      calc x - t • (x - x') = (1 - t) • x + t • x' := by module
        _ = (1 - t) • y + t • y' := hz.symm.trans he
        _ = y - t • (y - y') := by module
    rw [hd] at hmeet
    exact sub_left_injective hmeet
  refine ⟨hxy, ?_⟩
  rw [hxy] at hd
  exact sub_right_injective hd

/-- **Transport segments do not cross.** In a strictly convex real normed space `E`, let `1 < p`
and let `S` be cyclically monotone for the cost `d(x, y) ^ p`. For every `0 < t < 1`, the
interpolation `(x, x') ↦ (1 - t) • x + t • x'` is injective on `S`: two pairs of `S` whose
segments meet at time `t` are equal. -/
theorem IsCyclicallyMonotone.injOn_smul_add_smul {p : ℝ} (hp : 1 < p) {S : Set (E × E)}
    (hS : IsCyclicallyMonotone (fun z : E × E ↦ edist z.1 z.2 ^ p) S) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    InjOn (fun z : E × E ↦ (1 - t) • z.1 + t • z.2) S := by
  rintro ⟨x, x'⟩ hx ⟨y, y'⟩ hy he
  have hp₀ : 0 ≤ p := zero_le_one.trans hp.le
  have hswap := hS.add_le_add_swap hx hy
  simp only [edist_dist, dist_eq_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp₀] at hswap
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at hswap
  obtain ⟨rfl, rfl⟩ := eq_and_eq_of_smul_add_smul_eq hp ht hswap he
  rfl

end TauCeti
