/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Affine.AddTorsor
public import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Global error bounds from a modulus of continuity

Let `g` be a function from a pseudometric space to a normed group, bounded in norm by `M`, which
moves by less than `η` over distances less than `δ` (the shape of
`Metric.uniformContinuous_iff`). Then `‖g a - g b‖ ≤ η + 2 M min(1, dist a b / δ)` for all `a`
and `b`. The second term is a continuous function of `dist a b` vanishing at `0`, which makes
this the standard pointwise input of approximate-identity arguments: integrating it against a
kernel concentrating at the origin leaves only `η`.

The weighted variant bounds `‖c • g a - g b‖` for a real scalar `|c| ≤ H`, adding the cost
`M |c - 1|` of the weight differing from one.

On a real normed space no bound on `g` is needed to control it at large distances: a segment of
length at most `n δ` splits into `n` pieces of length at most `δ`, so a function which moves by at
most `η` over distances at most `δ` moves by at most `n η` over distances at most `n δ`, hence by
at most `(1 + dist a b / δ) η` between `a` and `b`. This linear growth is what makes such a bound
integrable against kernels with a finite first moment, with a result proportional to `η`.

## Main declarations

* `TauCeti.norm_sub_le_add_mul_min_dist_div`: the modulus-of-continuity bound.
* `TauCeti.norm_smul_sub_le_add_mul_min_dist_div`: its weighted variant.
* `TauCeti.dist_le_mul_of_dist_le_mul` and `TauCeti.dist_le_one_add_dist_div_mul`: the chained
  bounds on a real normed space.
-/

public section

namespace TauCeti

variable {X E : Type*} [PseudoMetricSpace X]

/-- A function bounded in norm by `M` which moves by less than `η` over distances less than `δ`
satisfies `‖g a - g b‖ ≤ η + 2 M min(1, dist a b / δ)` for all `a` and `b`. -/
theorem norm_sub_le_add_mul_min_dist_div [SeminormedAddCommGroup E] {g : X → E} {M : ℝ}
    (hgM : ∀ x, ‖g x‖ ≤ M) {δ η : ℝ} (hδ : 0 < δ)
    (hgδ : ∀ ⦃a b : X⦄, dist a b < δ → dist (g a) (g b) < η) (a b : X) :
    ‖g a - g b‖ ≤ η + 2 * M * min 1 (dist a b / δ) := by
  by_cases hab : dist a b < δ
  · have hM : 0 ≤ M := (norm_nonneg _).trans (hgM a)
    have : 0 ≤ min 1 (dist a b / δ) := le_min zero_le_one (by positivity)
    have := hgδ hab
    rw [dist_eq_norm] at this
    nlinarith
  · rw [min_eq_left ((one_le_div hδ).2 (not_lt.1 hab))]
    -- `η` is positive, as `g` moves by less than `η` from `b` to itself.
    have hη : 0 < η := by simpa using hgδ (a := b) (b := b) (by simpa using hδ)
    linarith [norm_sub_le (g a) (g b), hgM a, hgM b]

/-- The weighted form of `norm_sub_le_add_mul_min_dist_div`: for a real scalar `c` with
`|c| ≤ H`, `‖c • g a - g b‖ ≤ H η + (2 H M min(1, dist a b / δ) + M |c - 1|)`. -/
theorem norm_smul_sub_le_add_mul_min_dist_div [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    {g : X → E} {M : ℝ} (hgM : ∀ x, ‖g x‖ ≤ M) {δ η : ℝ} (hδ : 0 < δ)
    (hgδ : ∀ ⦃a b : X⦄, dist a b < δ → dist (g a) (g b) < η) {c H : ℝ} (hcH : |c| ≤ H)
    (a b : X) :
    ‖c • g a - g b‖ ≤ H * η + (2 * H * M * min 1 (dist a b / δ) + M * |c - 1|) := by
  have hH : 0 ≤ H := (abs_nonneg _).trans hcH
  have hsplit : c • g a - g b = c • (g a - g b) + (c - 1) • g b := by
    rw [smul_sub, sub_smul, one_smul]
    abel
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
  have h1 : |c| * ‖g a - g b‖ ≤ H * (η + 2 * M * min 1 (dist a b / δ)) :=
    mul_le_mul hcH (norm_sub_le_add_mul_min_dist_div hgM hδ hgδ a b) (norm_nonneg _) hH
  have h2 : |c - 1| * ‖g b‖ ≤ M * |c - 1| := by
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (hgM b) (abs_nonneg _)
  nlinarith

section Chain

variable {V Y : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [PseudoMetricSpace Y]
  {g : V → Y} {δ η : ℝ}

/-- **Chaining a modulus of continuity.** On a real normed space, a function which moves by at
most `η` over distances at most `δ` moves by at most `n η` over distances at most `n δ`. -/
theorem dist_le_mul_of_dist_le_mul (h : ∀ a b, dist a b ≤ δ → dist (g a) (g b) ≤ η) (n : ℕ)
    {a b : V} (hab : dist a b ≤ n * δ) : dist (g a) (g b) ≤ n * η := by
  induction n generalizing a with
  | zero =>
    rw [Nat.cast_zero, zero_mul, dist_le_zero] at hab
    simp [hab]
  | succ n ih =>
    -- Split the segment from `a` to `b` at the point `z` at distance `dist a b / (n + 1)` from `a`.
    have hn : (0 : ℝ) < n + 1 := by positivity
    set z := AffineMap.lineMap a b ((n + 1 : ℝ)⁻¹) with hz
    have haz : dist a z ≤ δ := by
      rw [hz, dist_left_lineMap, Real.norm_of_nonneg (inv_nonneg.2 hn.le), inv_mul_le_iff₀ hn]
      simpa [mul_comm] using hab
    have hzb : dist z b ≤ n * δ := by
      have hc : (n + 1 : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [n.cast_nonneg (α := ℝ)])
      have hsub : 1 - (n + 1 : ℝ)⁻¹ = n / (n + 1) := by field_simp; ring
      rw [hz, dist_lineMap_right, Real.norm_of_nonneg (sub_nonneg.2 hc), hsub,
        div_mul_eq_mul_div, div_le_iff₀ hn]
      push_cast at hab
      nlinarith [Nat.cast_nonneg (α := ℝ) n, dist_nonneg (x := a) (y := b)]
    calc dist (g a) (g b) ≤ dist (g a) (g z) + dist (g z) (g b) := dist_triangle _ _ _
      _ ≤ η + n * η := add_le_add (h a z haz) (ih hzb)
      _ = (n + 1 : ℕ) * η := by push_cast; ring

/-- **Linear growth from a modulus of continuity.** On a real normed space, a function which moves
by at most `η` over distances at most `δ > 0` satisfies
`dist (g a) (g b) ≤ (1 + dist a b / δ) η` for all `a` and `b`. -/
theorem dist_le_one_add_dist_div_mul (hδ : 0 < δ)
    (h : ∀ a b, dist a b ≤ δ → dist (g a) (g b) ≤ η) (a b : V) :
    dist (g a) (g b) ≤ (1 + dist a b / δ) * η := by
  have hη : 0 ≤ η := (dist_nonneg).trans (h a a (by simpa using hδ.le))
  have hd : 0 ≤ dist a b / δ := by positivity
  have hceil := Nat.ceil_lt_add_one hd
  refine (dist_le_mul_of_dist_le_mul h ⌈dist a b / δ⌉₊ ?_).trans ?_
  · exact (div_le_iff₀ hδ).1 (Nat.le_ceil _)
  · nlinarith

end Chain

end TauCeti
