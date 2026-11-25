/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Topology.UniformSpace.HeineCantor
import TauCeti.Analysis.Calculus.MeanValue
import TauCeti.Analysis.Normed.Group.Basic

/-!
# Symmetric-endpoint, midpoint, and cross-increment Taylor estimates

When `H` has derivative `h` and `h` has derivative `h'` on a closed interval, both the endpoint
increment `H y - H x` and the symmetric (trapezoidal) rule `(h x + h y) / 2 * (y - x)` share the
second-order expansion `h x * (y - x) + 1 / 2 * h' x * (y - x) ^ 2`. Their difference is therefore
controlled solely by the oscillation of `h'` between `x` and `y` times `(y - x) ^ 2`, without any
second derivative of `h`. Along finite partitions whose step increments tend to zero and whose
quadratic sums remain bounded, the symmetric-endpoint sums converge to `H (x n) - H (x 0)`. For
affine `h`, the quadratic remainder vanishes identically on every grid without ordering or mesh
hypotheses.

The same first-order oscillation estimate controls two companion quantities used in `C¹`
Stratonovich calculus:

* the cross-increment difference `(h y - h x) * (y - x) - h' x * (y - x) ^ 2`, which reduces the
  quadratic covariation of `h ∘ X` and `X` to a `h' ∘ X`-weighted quadratic variation; and
* the comparison between a midpoint sample `h z * (y - x)` and the symmetric average
  `(h x + h y) / 2 * (y - x)`, which equals `1 / 2 * h' x * ((z - x) ^ 2 - (y - z) ^ 2)` up to an
  error controlled by `h'`-oscillation times `(z - x) ^ 2 + (y - z) ^ 2`. For the identity
  integrand `h = id`, this comparison is exact on every finite grid (`sum_mul_sub_sub_half_sq`).

All estimates are stated for derivatives within a closed interval and arbitrary index filters;
empty grids and repeated or unordered grid points are allowed.

## References

* P. E. Protter, *Stochastic Integration and Differential Equations*, second edition, Springer,
  2005, Chapter V, §5.
* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.3.
-/

public section

open Finset Filter Set
open scoped Topology

namespace TauCeti

/-- For an affine integrand `z ↦ c * z + d`, the symmetric-endpoint sum telescopes identically on
every finite grid, with no ordering or smallness hypothesis on the increments. -/
theorem sum_half_add_mul_sub_affine (x : ℕ → ℝ) (n : ℕ) (c d : ℝ) :
    ∑ i ∈ range n, ((c * x i + d) + (c * x (i + 1) + d)) / 2 * (x (i + 1) - x i) =
      c / 2 * (x n ^ 2 - x 0 ^ 2) + d * (x n - x 0) := by
  have hstep (i : ℕ) :
      ((c * x i + d) + (c * x (i + 1) + d)) / 2 * (x (i + 1) - x i) =
        (c / 2 * x (i + 1) ^ 2 + d * x (i + 1)) - (c / 2 * x i ^ 2 + d * x i) := by
    ring
  simp_rw [hstep]
  rw [sum_range_sub (fun i ↦ c / 2 * x i ^ 2 + d * x i) n]
  ring

/-- For the identity integrand, the symmetric-endpoint sum telescopes identically to half the
increment of squares on every finite grid. -/
theorem sum_half_add_mul_sub_id (x : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ range n, (x i + x (i + 1)) / 2 * (x (i + 1) - x i) = (x n ^ 2 - x 0 ^ 2) / 2 := by
  have h := sum_half_add_mul_sub_affine x n 1 0
  simp only [one_mul, add_zero, zero_mul] at h
  linarith

/-- The deviation of an intermediate-sample sum `∑ c i * (x (i + 1) - x i)` from the symmetric
value `(x n ^ 2 - x 0 ^ 2) / 2` equals half the alternating sum of squared half-step increments
`∑ 1 / 2 * ((c i - x i) ^ 2 - (x (i + 1) - c i) ^ 2)` on every finite grid. -/
theorem sum_mul_sub_sub_half_sq (x c : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ range n, c i * (x (i + 1) - x i)) - (x n ^ 2 - x 0 ^ 2) / 2 =
      ∑ i ∈ range n, 1 / 2 * ((c i - x i) ^ 2 - (x (i + 1) - c i) ^ 2) := by
  rw [← sum_half_add_mul_sub_id x n, ← sum_sub_distrib]
  exact sum_congr rfl fun _ _ ↦ by ring

/-- Deviation of the derivative `h'` from a constant slope `c` on the unordered segment `[x, y]`
bounds the linear approximation remainder `|h y - h x - c * (y - x)|` by `M * |y - x|`.
This specializes `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le'` to real functions on
`uIcc x y ⊆ s`. -/
theorem abs_sub_sub_mul_le_of_hasDerivWithinAt {h h' : ℝ → ℝ} {s : Set ℝ} {x y c M : ℝ}
    (hs : uIcc x y ⊆ s) (hh : ∀ z ∈ uIcc x y, HasDerivWithinAt h (h' z) s z)
    (hosc : ∀ z ∈ uIcc x y, |h' z - c| ≤ M) :
    |h y - h x - c * (y - x)| ≤ M * |y - x| := by
  simpa only [Real.norm_eq_abs, smul_eq_mul, mul_comm (y - x)] using
    (convex_uIcc x y).norm_image_sub_le_of_norm_hasDerivWithin_le'
      (fun z hz ↦ (hh z hz).mono hs)
      (fun z hz ↦ by simpa only [Real.norm_eq_abs] using hosc z hz)
      left_mem_uIcc right_mem_uIcc

/-- Oscillation of `h'` between `x` and `y` bounds the difference between the cross-increment
`(h y - h x) * (y - x)` and the left-weighted squared increment `h' x * (y - x) ^ 2`. -/
theorem abs_sub_mul_sub_sub_deriv_mul_sq_le {h h' : ℝ → ℝ} {s : Set ℝ} {x y M : ℝ}
    (hs : uIcc x y ⊆ s) (hh : ∀ z ∈ uIcc x y, HasDerivWithinAt h (h' z) s z)
    (hosc : ∀ z ∈ uIcc x y, |h' z - h' x| ≤ M) :
    |(h y - h x) * (y - x) - h' x * (y - x) ^ 2| ≤ M * (y - x) ^ 2 := by
  have hfac : (h y - h x) * (y - x) - h' x * (y - x) ^ 2 =
      (h y - h x - h' x * (y - x)) * (y - x) := by
    ring
  rw [hfac, abs_mul]
  calc
    |h y - h x - h' x * (y - x)| * |y - x|
        ≤ (M * |y - x|) * |y - x| :=
          mul_le_mul_of_nonneg_right (abs_sub_sub_mul_le_of_hasDerivWithinAt hs hh hosc)
            (abs_nonneg _)
    _ = M * (y - x) ^ 2 := by rw [mul_assoc, ← sq, sq_abs]

/-- When `H` has derivative `h` and `h` has derivative `h'` within `s`, oscillation of `h'` on the
unordered segment `[x, y]` bounds the second-order remainder of `H` at `x` by `M / 2 * (y - x) ^ 2`,
without requiring `H` to be differentiable outside `s`. -/
theorem abs_sub_sub_deriv_sub_half_deriv_mul_sq_le {H h h' : ℝ → ℝ} {s : Set ℝ} {x y M : ℝ}
    (hs : uIcc x y ⊆ s) (hH : ∀ z ∈ uIcc x y, HasDerivWithinAt H (h z) s z)
    (hh : ∀ z ∈ uIcc x y, HasDerivWithinAt h (h' z) s z)
    (hosc : ∀ z ∈ uIcc x y, |h' z - h' x| ≤ M) :
    |H y - H x - h x * (y - x) - 1 / 2 * h' x * (y - x) ^ 2| ≤ M / 2 * (y - x) ^ 2 := by
  -- 1. Parametrize `[x, y]` by `φ(t) = x + t (y - x)` for `t ∈ [0, 1]`.
  let φ : ℝ → ℝ := fun t ↦ x + t * (y - x)
  have hφ : MapsTo φ (Icc 0 1) (uIcc x y) := by
    intro t ht
    have hconv := (convex_uIcc x y) left_mem_uIcc right_mem_uIcc
      (sub_nonneg.2 ht.2) ht.1 (sub_add_cancel 1 t)
    have heq : (1 - t) • x + t • y = φ t := by
      dsimp [φ]
      ring
    exact heq ▸ hconv
  -- 2. Define the second-order Taylor remainder `Λ(t)` along `φ` and differentiate it on `[0, 1]`.
  have hsq_mul (C t : ℝ) : HasDerivAt (fun u : ℝ ↦ u ^ 2 / 2 * C) (t * C) t := by
    have hsq : HasDerivAt (fun u : ℝ ↦ u ^ 2 / 2) t t := by
      simpa only [Pi.pow_apply, id_eq] using
        (((hasDerivAt_id t).pow 2).div_const (2 : ℝ)).congr_deriv (by simp only [id_eq]; ring)
    exact (hsq.mul_const C).congr_deriv (by ring)
  let Λ : ℝ → ℝ := fun t ↦
    H (φ t) - H x - t * (h x * (y - x)) - t ^ 2 / 2 * (h' x * (y - x) ^ 2)
  have hΛ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt Λ
      ((h (φ t) - h x - h' x * (φ t - x)) * (y - x)) (Icc 0 1) t := by
    intro t ht
    have hφ' : HasDerivWithinAt φ (y - x) (Icc 0 1) t := by
      simpa only [φ, id_eq, one_mul, zero_add] using
        ((hasDerivWithinAt_id t (Icc 0 1)).mul_const (y - x)).const_add x
    have hcomp : HasDerivWithinAt (fun u ↦ H (φ u)) (h (φ t) * (y - x)) (Icc 0 1) t :=
      ((hH (φ t) (hφ ht)).mono hs).comp t hφ' hφ
    have ht1 : HasDerivWithinAt (fun u ↦ u * (h x * (y - x))) (h x * (y - x)) (Icc 0 1) t := by
      simpa only [id_eq, one_mul] using (hasDerivWithinAt_id t (Icc 0 1)).mul_const (h x * (y - x))
    have ht2 : HasDerivWithinAt (fun u ↦ u ^ 2 / 2 * (h' x * (y - x) ^ 2))
        (t * (h' x * (y - x) ^ 2)) (Icc 0 1) t :=
      (hsq_mul (h' x * (y - x) ^ 2) t).hasDerivWithinAt
    have hraw : HasDerivWithinAt
        (((fun u ↦ H (φ u) - H x) - fun u ↦ u * (h x * (y - x))) -
          fun u ↦ u ^ 2 / 2 * (h' x * (y - x) ^ 2))
        ((h (φ t) - h x - h' x * (φ t - x)) * (y - x)) (Icc 0 1) t :=
      (((hcomp.sub_const (H x)).sub ht1).sub ht2).congr_deriv (by dsimp [φ]; ring)
    simpa only [Λ, Pi.sub_def] using hraw
  -- 3. Compare the right derivative of `Λ` against the barrier `B(t) = t² / 2 * M (y - x)²`.
  let B : ℝ → ℝ := fun t ↦ t ^ 2 / 2 * (M * (y - x) ^ 2)
  have hB : ∀ t, HasDerivAt B (t * (M * (y - x) ^ 2)) t := hsq_mul (M * (y - x) ^ 2)
  have hright : ∀ t ∈ Ico (0 : ℝ) 1, HasDerivWithinAt Λ
      ((h (φ t) - h x - h' x * (φ t - x)) * (y - x)) (Ici t) t := by
    intro t ht
    exact (hΛ t ⟨ht.1, ht.2.le⟩).mono_of_mem_nhdsWithin
      (mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc_left ht.1))
  have hbound : ∀ t ∈ Icc (0 : ℝ) 1, ‖Λ t‖ ≤ B t := by
    refine image_norm_le_of_norm_deriv_right_le_deriv_boundary
      (fun t ht ↦ (hΛ t ht).continuousWithinAt) hright
      (by simp [Λ, φ, B]) hB fun t ht ↦ ?_
    have hsub : uIcc x (φ t) ⊆ uIcc x y := uIcc_subset_Icc left_mem_uIcc (hφ ⟨ht.1, ht.2.le⟩)
    have hstep := abs_sub_sub_mul_le_of_hasDerivWithinAt (hsub.trans hs)
      (fun z hz ↦ hh z (hsub hz)) (fun z hz ↦ hosc z (hsub hz))
    rw [Real.norm_eq_abs, abs_mul]
    calc
      |h (φ t) - h x - h' x * (φ t - x)| * |y - x|
          ≤ (M * |φ t - x|) * |y - x| := mul_le_mul_of_nonneg_right hstep (abs_nonneg _)
      _ = |t| * (M * (y - x) ^ 2) := by
            have hφx : φ t - x = t * (y - x) := by dsimp [φ]; ring
            rw [hφx, abs_mul, ← sq_abs (y - x)]
            ring
      _ = t * (M * (y - x) ^ 2) := by rw [abs_of_nonneg ht.1]
  -- 4. Evaluate `‖Λ t‖ ≤ B t` at `t = 1`.
  have h1 := hbound 1 ⟨zero_le_one, le_rfl⟩
  have hφ1 : φ 1 = y := by dsimp [φ]; ring
  have hΛ1 : Λ 1 = H y - H x - h x * (y - x) - 1 / 2 * h' x * (y - x) ^ 2 := by
    dsimp [Λ]
    rw [hφ1]
    ring
  have hB1 : B 1 = M / 2 * (y - x) ^ 2 := by
    dsimp [B]
    ring
  simpa only [Real.norm_eq_abs, hΛ1, hB1] using h1

/-- Oscillation of `h'` on `[x, y]` bounds the symmetric-endpoint remainder
`|(h x + h y) / 2 * (y - x) - (H y - H x)|` by `M * (y - x) ^ 2`. -/
theorem abs_half_add_mul_sub_sub_le {H h h' : ℝ → ℝ} {s : Set ℝ} {x y M : ℝ}
    (hs : uIcc x y ⊆ s) (hH : ∀ z ∈ uIcc x y, HasDerivWithinAt H (h z) s z)
    (hh : ∀ z ∈ uIcc x y, HasDerivWithinAt h (h' z) s z)
    (hosc : ∀ z ∈ uIcc x y, |h' z - h' x| ≤ M) :
    |(h x + h y) / 2 * (y - x) - (H y - H x)| ≤ M * (y - x) ^ 2 := by
  have hid : (h x + h y) / 2 * (y - x) - (H y - H x) =
      1 / 2 * ((h y - h x) * (y - x) - h' x * (y - x) ^ 2) -
        (H y - H x - h x * (y - x) - 1 / 2 * h' x * (y - x) ^ 2) := by
    ring
  rw [hid]
  have h₁ := abs_sub_mul_sub_sub_deriv_mul_sq_le hs hh hosc
  have h₂ := abs_sub_sub_deriv_sub_half_deriv_mul_sq_le hs hH hh hosc
  calc
    |1 / 2 * ((h y - h x) * (y - x) - h' x * (y - x) ^ 2) -
        (H y - H x - h x * (y - x) - 1 / 2 * h' x * (y - x) ^ 2)|
        ≤ |1 / 2 * ((h y - h x) * (y - x) - h' x * (y - x) ^ 2)| +
            |H y - H x - h x * (y - x) - 1 / 2 * h' x * (y - x) ^ 2| := abs_sub _ _
    _ = 1 / 2 * |(h y - h x) * (y - x) - h' x * (y - x) ^ 2| +
          |H y - H x - h x * (y - x) - 1 / 2 * h' x * (y - x) ^ 2| := by
          rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    _ ≤ 1 / 2 * (M * (y - x) ^ 2) + M / 2 * (y - x) ^ 2 := by linarith
    _ = M * (y - x) ^ 2 := by ring

/-- Comparing a sample at an intermediate state `z` with the symmetric endpoint average isolates
`1 / 2 * h' x * ((z - x) ^ 2 - (y - z) ^ 2)`, with remainder controlled by the oscillation of `h'`
relative to `x` times `(z - x) ^ 2 + (y - z) ^ 2`. The point `z` need not lie between `x` and
`y`. -/
theorem abs_midpoint_sub_half_add_sub_half_deriv_le {h h' : ℝ → ℝ} {s : Set ℝ} {x z y M : ℝ}
    (hxz : uIcc x z ⊆ s) (hzy : uIcc z y ⊆ s)
    (hh : ∀ u, u ∈ uIcc x z ∨ u ∈ uIcc z y → HasDerivWithinAt h (h' u) s u)
    (hosc : ∀ u, u ∈ uIcc x z ∨ u ∈ uIcc z y → |h' u - h' x| ≤ M) :
    |h z * (y - x) - (h x + h y) / 2 * (y - x) -
        1 / 2 * h' x * ((z - x) ^ 2 - (y - z) ^ 2)| ≤
      M * ((z - x) ^ 2 + (y - z) ^ 2) := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hosc x (Or.inl left_mem_uIcc))
  have h₁ : |h z - h x - h' x * (z - x)| ≤ M * |z - x| :=
    abs_sub_sub_mul_le_of_hasDerivWithinAt hxz
      (fun u hu ↦ hh u (Or.inl hu)) (fun u hu ↦ hosc u (Or.inl hu))
  have h₂ : |h y - h z - h' x * (y - z)| ≤ M * |y - z| :=
    abs_sub_sub_mul_le_of_hasDerivWithinAt hzy
      (fun u hu ↦ hh u (Or.inr hu)) (fun u hu ↦ hosc u (Or.inr hu))
  have hid : h z * (y - x) - (h x + h y) / 2 * (y - x) -
      1 / 2 * h' x * ((z - x) ^ 2 - (y - z) ^ 2) =
      1 / 2 * ((h z - h x - h' x * (z - x)) - (h y - h z - h' x * (y - z))) * (y - x) := by
    ring
  have htri : |y - x| ≤ |z - x| + |y - z| := by
    simpa only [Real.dist_eq, abs_sub_comm] using dist_triangle x z y
  rw [hid, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have hsum : |(h z - h x - h' x * (z - x)) - (h y - h z - h' x * (y - z))| ≤
      M * (|z - x| + |y - z|) := by
    calc
      |(h z - h x - h' x * (z - x)) - (h y - h z - h' x * (y - z))|
          ≤ |h z - h x - h' x * (z - x)| + |h y - h z - h' x * (y - z)| := abs_sub _ _
      _ ≤ M * |z - x| + M * |y - z| := add_le_add h₁ h₂
      _ = M * (|z - x| + |y - z|) := by ring
  calc
    1 / 2 * |(h z - h x - h' x * (z - x)) - (h y - h z - h' x * (y - z))| * |y - x|
        ≤ 1 / 2 * (M * (|z - x| + |y - z|)) * (|z - x| + |y - z|) := by
          have hnn : 0 ≤ 1 / 2 * |(h z - h x - h' x * (z - x)) - (h y - h z - h' x * (y - z))| :=
            by positivity
          exact (mul_le_mul_of_nonneg_left htri hnn).trans
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum (by positivity))
              (by positivity))
    _ ≤ M * ((z - x) ^ 2 + (y - z) ^ 2) := by
          have hsq : (|z - x| + |y - z|) ^ 2 ≤ 2 * ((z - x) ^ 2 + (y - z) ^ 2) := by
            have := sq_nonneg (|z - x| - |y - z|)
            nlinarith [sq_abs (z - x), sq_abs (y - z)]
          nlinarith

/-- Uniform continuity of `h'` on `[a, b]` turns a vanishing increment bound into an eventual
oscillation bound `|h' z - h' (x k i)| ≤ ε` on every subsegment `uIcc (x k i) (y k i) ⊆ [a, b]`. -/
private theorem eventually_uIcc_osc_le {h' : ℝ → ℝ} {a b : ℝ}
    (hc : ContinuousOn h' (Icc a b))
    {ι : Type*} {l : Filter ι} {n : ι → ℕ} {x y : ι → ℕ → ℝ} {δ : ι → ℝ}
    (hx : ∀ᶠ k in l, ∀ i < n k, x k i ∈ Icc a b)
    (hy : ∀ᶠ k in l, ∀ i < n k, y k i ∈ Icc a b)
    (hδ : ∀ᶠ k in l, ∀ i < n k, |y k i - x k i| ≤ δ k)
    (hδ0 : Tendsto δ l (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in l, ∀ i < n k,
      uIcc (x k i) (y k i) ⊆ Icc a b ∧ ∀ z ∈ uIcc (x k i) (y k i), |h' z - h' (x k i)| ≤ ε := by
  obtain ⟨η, hη, hosc⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hc) ε hε
  filter_upwards [(tendsto_order.1 hδ0).2 η hη, hx, hy, hδ] with k hk hxk hyk hδk i hi
  have hsub := uIcc_subset_Icc (hxk i hi) (hyk i hi)
  refine ⟨hsub, fun z hz ↦ ?_⟩
  have hzx : dist z (x k i) < η := by
    rw [Real.dist_eq]
    exact (abs_sub_left_of_mem_uIcc hz).trans_lt ((hδk i hi).trans_lt hk)
  exact (Real.dist_eq (h' z) (h' (x k i)) ▸ hosc z (hsub hz) (x k i) (hxk i hi) hzx).le

/-- For a `C¹` function `h` on `[a, b]`, the difference between the cross-increment sum
`∑ (h (x (i + 1)) - h (x i)) * (x (i + 1) - x i)` and the left-weighted quadratic sum
`∑ h' (x i) * (x (i + 1) - x i) ^ 2` tends to zero along any filter of finite grids in `[a, b]`
with vanishing increments and eventually bounded quadratic sums. -/
theorem tendsto_sum_sub_mul_sub_sub_deriv_mul_sq {h h' : ℝ → ℝ} {a b : ℝ}
    (hh : ∀ z ∈ Icc a b, HasDerivWithinAt h (h' z) (Icc a b) z)
    (hc : ContinuousOn h' (Icc a b))
    {ι : Type*} {l : Filter ι} {x : ι → ℕ → ℝ} {n : ι → ℕ} {δ : ι → ℝ}
    (hx : ∀ᶠ k in l, ∀ i ≤ n k, x k i ∈ Icc a b)
    (hδ : ∀ᶠ k in l, ∀ i < n k, |x k (i + 1) - x k i| ≤ δ k)
    (hδ0 : Tendsto δ l (𝓝 0))
    (hQ : l.IsBoundedUnder (· ≤ ·) (fun k ↦ ∑ i ∈ range (n k), (x k (i + 1) - x k i) ^ 2)) :
    Tendsto (fun k ↦ (∑ i ∈ range (n k), (h (x k (i + 1)) - h (x k i)) * (x k (i + 1) - x k i)) -
      ∑ i ∈ range (n k), h' (x k i) * (x k (i + 1) - x k i) ^ 2) l (𝓝 0) := by
  refine (tendsto_sum_zero_of_forall_norm_le_mul (w := fun k i ↦ (x k (i + 1) - x k i) ^ 2)
    (fun ε hε ↦ ?_) hQ).congr fun k ↦ sum_sub_distrib ..
  filter_upwards [eventually_uIcc_osc_le hc
    (hx.mono fun k hxk i hi ↦ hxk i hi.le)
    (hx.mono fun k hxk i hi ↦ hxk (i + 1) hi) hδ hδ0 hε] with k hk i hi
  obtain ⟨hsub, hosc⟩ := hk i (mem_range.1 hi)
  rw [Real.norm_eq_abs]
  exact abs_sub_mul_sub_sub_deriv_mul_sq_le hsub (fun z hz ↦ hh z (hsub hz)) hosc

/-- **Deterministic symmetric-endpoint chain rule.** If `H` has derivative `h` and `h` has
continuous derivative `h'` within `[a, b]`, the symmetric-endpoint sums
`∑ (h (x i) + h (x (i + 1))) / 2 * (x (i + 1) - x i)` approximate `H (x n) - H (x 0)` with
vanishing error along any filter of finite grids in `[a, b]` whose increments tend to zero and
whose quadratic sums are eventually bounded. -/
theorem tendsto_sum_half_add_mul_sub_sub {H h h' : ℝ → ℝ} {a b : ℝ}
    (hH : ∀ z ∈ Icc a b, HasDerivWithinAt H (h z) (Icc a b) z)
    (hh : ∀ z ∈ Icc a b, HasDerivWithinAt h (h' z) (Icc a b) z)
    (hc : ContinuousOn h' (Icc a b))
    {ι : Type*} {l : Filter ι} {x : ι → ℕ → ℝ} {n : ι → ℕ} {δ : ι → ℝ}
    (hx : ∀ᶠ k in l, ∀ i ≤ n k, x k i ∈ Icc a b)
    (hδ : ∀ᶠ k in l, ∀ i < n k, |x k (i + 1) - x k i| ≤ δ k)
    (hδ0 : Tendsto δ l (𝓝 0))
    (hQ : l.IsBoundedUnder (· ≤ ·) (fun k ↦ ∑ i ∈ range (n k), (x k (i + 1) - x k i) ^ 2)) :
    Tendsto (fun k ↦ (∑ i ∈ range (n k),
        (h (x k i) + h (x k (i + 1))) / 2 * (x k (i + 1) - x k i)) -
      (H (x k (n k)) - H (x k 0))) l (𝓝 0) := by
  refine (tendsto_sum_zero_of_forall_norm_le_mul
    (f := fun k i ↦
      (h (x k i) + h (x k (i + 1))) / 2 * (x k (i + 1) - x k i) - (H (x k (i + 1)) - H (x k i)))
    (w := fun k i ↦ (x k (i + 1) - x k i) ^ 2) (fun ε hε ↦ ?_) hQ).congr fun k ↦ by
      rw [sum_sub_distrib, sum_range_sub (fun i ↦ H (x k i)) (n k)]
  filter_upwards [eventually_uIcc_osc_le hc
    (hx.mono fun k hxk i hi ↦ hxk i hi.le)
    (hx.mono fun k hxk i hi ↦ hxk (i + 1) hi) hδ hδ0 hε] with k hk i hi
  obtain ⟨hsub, hosc⟩ := hk i (mem_range.1 hi)
  rw [Real.norm_eq_abs]
  exact abs_half_add_mul_sub_sub_le hsub (fun z hz ↦ hH z (hsub hz))
    (fun z hz ↦ hh z (hsub hz)) hosc

/-- Along finite families of triples `(x k i, z k i, y k i)` in `[a, b]` whose half-step increments
vanish uniformly and whose refined quadratic sums are eventually bounded, the difference between
`∑ h (z k i) * (y k i - x k i)` and `∑ (h (x k i) + h (y k i)) / 2 * (y k i - x k i)` differs from
`1 / 2 * ∑ h' (x k i) * ((z k i - x k i) ^ 2 - (y k i - z k i) ^ 2)` by a vanishing remainder. -/
theorem tendsto_sum_midpoint_sub_half_add_sub_half_deriv {h h' : ℝ → ℝ} {a b : ℝ}
    (hh : ∀ u ∈ Icc a b, HasDerivWithinAt h (h' u) (Icc a b) u)
    (hc : ContinuousOn h' (Icc a b))
    {ι : Type*} {l : Filter ι} {n : ι → ℕ} {x z y : ι → ℕ → ℝ} {δ : ι → ℝ}
    (hx : ∀ᶠ k in l, ∀ i < n k, x k i ∈ Icc a b)
    (hz : ∀ᶠ k in l, ∀ i < n k, z k i ∈ Icc a b)
    (hy : ∀ᶠ k in l, ∀ i < n k, y k i ∈ Icc a b)
    (hδ₁ : ∀ᶠ k in l, ∀ i < n k, |z k i - x k i| ≤ δ k)
    (hδ₂ : ∀ᶠ k in l, ∀ i < n k, |y k i - z k i| ≤ δ k)
    (hδ0 : Tendsto δ l (𝓝 0))
    (hQ : l.IsBoundedUnder (· ≤ ·) (fun k ↦ ∑ i ∈ range (n k),
      ((z k i - x k i) ^ 2 + (y k i - z k i) ^ 2))) :
    Tendsto (fun k ↦ ∑ i ∈ range (n k),
      (h (z k i) * (y k i - x k i) - (h (x k i) + h (y k i)) / 2 * (y k i - x k i) -
        1 / 2 * h' (x k i) * ((z k i - x k i) ^ 2 - (y k i - z k i) ^ 2))) l (𝓝 0) := by
  refine tendsto_sum_zero_of_forall_norm_le_mul
    (w := fun k i ↦ (z k i - x k i) ^ 2 + (y k i - z k i) ^ 2) (fun ε hε ↦ ?_) hQ
  filter_upwards [eventually_uIcc_osc_le hc hx hz hδ₁ hδ0 (half_pos hε),
    eventually_uIcc_osc_le hc hz hy hδ₂ hδ0 (half_pos hε)] with k h1 h2 i hi
  obtain ⟨hxz, hosc₁⟩ := h1 i (mem_range.1 hi)
  obtain ⟨hzy, hosc₂⟩ := h2 i (mem_range.1 hi)
  rw [Real.norm_eq_abs]
  refine abs_midpoint_sub_half_add_sub_half_deriv_le hxz hzy
    (fun u hu ↦ hh u (hu.elim (fun h ↦ hxz h) (fun h ↦ hzy h))) fun u hu ↦ ?_
  rcases hu with hu | hu
  · exact (hosc₁ u hu).trans (by linarith)
  · calc
      |h' u - h' (x k i)| ≤ |h' u - h' (z k i)| + |h' (z k i) - h' (x k i)| := abs_sub_le ..
      _ ≤ ε / 2 + ε / 2 := add_le_add (hosc₂ u hu) (hosc₁ (z k i) right_mem_uIcc)
      _ = ε := add_halves ε

end TauCeti
