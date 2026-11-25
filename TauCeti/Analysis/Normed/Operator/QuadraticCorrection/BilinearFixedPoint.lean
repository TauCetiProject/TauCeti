/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.MetricSpace.Contracting
import TauCeti.Analysis.Normed.Operator.Bilinear

/-!
# The bilinear fixed-point lemma

Let `X` be a Banach space and `B : X →L[𝕜] X →L[𝕜] X` a continuous bilinear map with
`‖B‖ ≤ η`. For `a : X` with `4 η ‖a‖ < 1`, the quadratic equation

`x = a + B x x`

has a solution, obtained as the limit of the Picard iterates `x₀ = a`, `xₙ₊₁ = a + B xₙ xₙ`. This
is the abstract form of the fixed-point argument that produces mild solutions of semilinear
evolution equations with a quadratic nonlinearity, such as the incompressible Navier–Stokes
equations, from a bilinear estimate on the Duhamel term.

* `ContinuousLinearMap.bilinearFixedPoint B a` is the limit of the Picard iterates. It is defined
  for every `a` (as a junk value when the iterates do not converge), so that the solution map
  `a ↦ x` is a function `X → X`.
* `ContinuousLinearMap.tendsto_iterate_bilinearFixedPoint`: the Picard iterates converge to it,
  and `ContinuousLinearMap.isFixedPt_bilinearFixedPoint`: it solves `a + B x x = x`.
* **The sharp bound.** `‖x‖ ≤ 2 ‖a‖ / (1 + √(1 - 4 η ‖a‖))`
  (`ContinuousLinearMap.norm_bilinearFixedPoint_le`). For `η > 0` the right-hand side is the
  smaller root `(1 - √(1 - 4 η ‖a‖)) / (2 η)` of `η ρ² - ρ + ‖a‖ = 0`; written as above it also
  covers `η = 0`. In particular `‖x‖ ≤ 2 ‖a‖`
  (`ContinuousLinearMap.norm_bilinearFixedPoint_le_two_mul`), and
  `2 η ‖x‖ ≤ 1 - √(1 - 4 η ‖a‖) < 1`
  (`ContinuousLinearMap.two_mul_mul_norm_bilinearFixedPoint_le`,
  `ContinuousLinearMap.two_mul_mul_norm_bilinearFixedPoint_lt_one`).
* **Uniqueness.** Any solution `x` with `2 η ‖x‖ < 1`, that is `‖x‖ < 1 / (2 η)`, is the one
  constructed (`ContinuousLinearMap.eq_bilinearFixedPoint`). This rests on the comparison
  `(1 - ‖B‖ (‖x‖ + ‖y‖)) ‖x - y‖ ≤ ‖a - b‖` of a solution `x` for `a` with a solution `y` for `b`
  (`ContinuousLinearMap.one_sub_mul_norm_sub_le_norm_sub`).
* **The lemma in its usual form.** Under the pointwise bound `‖B x y‖ ≤ η ‖x‖ ‖y‖` and
  `4 η ‖a‖ < 1`, there is a solution with `‖x‖ ≤ 2 ‖a‖`, and it is the only solution with
  `2 η ‖x‖ < 1` (`ContinuousLinearMap.exists_add_apply_apply_eq`).
* **Lipschitz dependence.** For `4 η r < 1` the solution map is Lipschitz on the closed ball of
  radius `r` with constant `(1 - 4 η r)^(-1/2)`
  (`ContinuousLinearMap.lipschitzOnWith_bilinearFixedPoint`).

The scalar equation `η x² - x + a = 0`, that is `X = ℝ` with `B = η • mul ℝ ℝ`, shows that these
constants are attained. The solution selected is the smaller root `(1 - √(1 - 4 η a)) / (2 η)`
(`ContinuousLinearMap.bilinearFixedPoint_smul_mul`); there is no real solution when `4 η a > 1`
(`ContinuousLinearMap.add_smul_mul_apply_apply_ne`); and the derivative of the solution map at `a`
is `(1 - 4 η a)^(-1/2)`, matching the Lipschitz constant above at `r = a`
(`ContinuousLinearMap.hasDerivAt_bilinearFixedPoint_smul_mul`). At `a = 0` the solution is `0`
(`ContinuousLinearMap.bilinearFixedPoint_zero`), while the other root `1 / η` lies outside the
uniqueness ball.

The general correction scheme of `TauCeti.Analysis.Normed.Operator.QuadraticCorrection.Basic`,
specialized to the identity as linearization, gives existence with `‖x‖ ≤ 2 ‖a‖` and uniqueness in
the same ball; the sharp bound, the convergence of the Picard iterates from `a` and the Lipschitz
constant above use the exact quadratic structure.

## References

* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Grundlehren der mathematischen Wissenschaften 343, Springer (2011), Chapter 5,
  Lemma 5.5.
* C. Wang, *Introduction of the Navier–Stokes equations*, lecture notes of a mini-course at
  Beijing Normal University (2013), Lemma 7.2, p. 56.
* R. Danchin, *Fourier Analysis Methods for PDE's*, lecture notes (2005), Lemma 2.3.2.
-/

public section

open Filter Metric Set Function
open scoped NNReal Topology

namespace ContinuousLinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- Comparison of two solutions: if `a + B x x = x` and `b + B y y = y`, then
`(1 - ‖B‖ (‖x‖ + ‖y‖)) ‖x - y‖ ≤ ‖a - b‖`. -/
theorem one_sub_mul_norm_sub_le_norm_sub {X : Type*} [SeminormedAddCommGroup X] [NormedSpace 𝕜 X]
    (B : X →L[𝕜] X →L[𝕜] X) {a b x y : X} (hx : a + B x x = x) (hy : b + B y y = y) :
    (1 - ‖B‖ * (‖x‖ + ‖y‖)) * ‖x - y‖ ≤ ‖a - b‖ := by
  have h : x - y = (a - b) + (B x x - B y y) := by
    nth_rw 1 [← hx, ← hy]
    abel
  have h₁ := B.norm_apply_apply_sub_apply_apply_le x y
  have h₂ := norm_add_le (a - b) (B x x - B y y)
  rw [← h] at h₂
  linarith

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] (B : X →L[𝕜] X →L[𝕜] X)

/-- The solution of the quadratic equation `x = a + B x x`, defined as the limit of the Picard
iterates `x₀ = a`, `xₙ₊₁ = a + B xₙ xₙ`. When `‖B‖ ≤ η` and `4 η ‖a‖ < 1` the iterates converge
(`ContinuousLinearMap.tendsto_iterate_bilinearFixedPoint`) and the limit is the unique solution
with `‖x‖ < 1 / (2 η)` (`ContinuousLinearMap.eq_bilinearFixedPoint`); otherwise the value is
unspecified. -/
noncomputable def bilinearFixedPoint (a : X) : X :=
  limUnder atTop fun n ↦ (fun x ↦ a + B x x)^[n] a

/-- Two solutions of `x = a + B x x` coincide when `‖B‖ (‖x‖ + ‖y‖) < 1`. -/
theorem eq_of_add_apply_apply_eq {a x y : X} (hx : a + B x x = x) (hy : a + B y y = y)
    (h : ‖B‖ * (‖x‖ + ‖y‖) < 1) : x = y := by
  have := B.one_sub_mul_norm_sub_le_norm_sub hx hy
  rw [sub_self, norm_zero] at this
  have hxy : ‖x - y‖ ≤ 0 := by nlinarith [norm_nonneg (x - y)]
  exact sub_eq_zero.1 (norm_le_zero_iff.1 hxy)

/-- For `a = 0` the Picard iterates are constant and the solution of `x = B x x` is `0`. -/
@[simp]
theorem bilinearFixedPoint_zero : B.bilinearFixedPoint 0 = 0 := by
  have h (n : ℕ) : (fun x ↦ 0 + B x x)^[n] 0 = 0 := iterate_fixed (by simp) n
  simp only [bilinearFixedPoint, h]
  exact tendsto_const_nhds.limUnder_eq

/-- The radius `ρ = 2 t / (1 + √(1 - 4 η t))` solves `t + η ρ² = ρ`. -/
private lemma add_mul_sq_radius {η t : ℝ} (h : 4 * η * t < 1) :
    t + η * (2 * t / (1 + √(1 - 4 * η * t))) ^ 2 = 2 * t / (1 + √(1 - 4 * η * t)) := by
  have hs := Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 1 - 4 * η * t)
  have hs0 := Real.sqrt_nonneg (1 - 4 * η * t)
  generalize √(1 - 4 * η * t) = s at *
  field_simp
  linear_combination t * hs

/-- The radius `ρ = 2 t / (1 + √(1 - 4 η t))` satisfies `2 η ρ = 1 - √(1 - 4 η t)`. -/
private lemma two_mul_mul_radius {η t : ℝ} (h : 4 * η * t < 1) :
    2 * η * (2 * t / (1 + √(1 - 4 * η * t))) = 1 - √(1 - 4 * η * t) := by
  have hs := Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 1 - 4 * η * t)
  have hs0 := Real.sqrt_nonneg (1 - 4 * η * t)
  generalize √(1 - 4 * η * t) = s at *
  field_simp
  linear_combination hs

section Complete

variable [CompleteSpace X] {η : ℝ} {a : X}

variable {B} in
/-- The Picard iteration contracts the closed ball of radius `2 ‖a‖ / (1 + √(1 - 4 η ‖a‖))`, so
the iterates from `a` converge to a fixed point in that ball. -/
private lemma exists_isFixedPt_tendsto_iterate (hB : ‖B‖ ≤ η) (ha : 4 * η * ‖a‖ < 1) :
    ∃ x, ‖x‖ ≤ 2 * ‖a‖ / (1 + √(1 - 4 * η * ‖a‖)) ∧ IsFixedPt (fun x ↦ a + B x x) x ∧
      Tendsto (fun n ↦ (fun x ↦ a + B x x)^[n] a) atTop (𝓝 x) := by
  set ρ := 2 * ‖a‖ / (1 + √(1 - 4 * η * ‖a‖))
  have hη : 0 ≤ η := (norm_nonneg B).trans hB
  have hρa : ‖a‖ + η * ρ ^ 2 = ρ := add_mul_sq_radius ha
  have h2ηρ : 2 * η * ρ = 1 - √(1 - 4 * η * ‖a‖) := two_mul_mul_radius ha
  have hs : 0 < √(1 - 4 * η * ‖a‖) := Real.sqrt_pos.2 (by linarith)
  have haρ : ‖a‖ ≤ ρ := by nlinarith [sq_nonneg ρ]
  have hmaps : MapsTo (fun x ↦ a + B x x) (closedBall 0 ρ) (closedBall 0 ρ) := by
    intro x hx
    rw [mem_closedBall_zero_iff] at hx ⊢
    calc ‖a + B x x‖ ≤ ‖a‖ + ‖B‖ * ‖x‖ * ‖x‖ := by
          grw [norm_add_le, B.le_opNorm₂]
      _ ≤ ‖a‖ + η * ρ ^ 2 := by rw [sq, ← mul_assoc]; gcongr
      _ = ρ := hρa
  have hlip : LipschitzOnWith (Real.toNNReal (2 * η * ρ)) (fun x ↦ a + B x x) (closedBall 0 ρ) :=
    LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ by
      rw [mem_closedBall_zero_iff] at hx hy
      rw [dist_eq_norm, dist_eq_norm, add_sub_add_left_eq_sub,
        Real.coe_toNNReal _ (by positivity)]
      calc ‖B x x - B y y‖ ≤ ‖B‖ * (‖x‖ + ‖y‖) * ‖x - y‖ :=
            B.norm_apply_apply_sub_apply_apply_le x y
        _ ≤ η * (ρ + ρ) * ‖x - y‖ := by gcongr
        _ = 2 * η * ρ * ‖x - y‖ := by ring
  have hK : ContractingWith (Real.toNNReal (2 * η * ρ)) (hmaps.restrict _ _ _) :=
    ⟨Real.toNNReal_lt_one.2 (by linarith), hlip.mapsToRestrict hmaps⟩
  obtain ⟨x, hxs, hfix, htendsto, -⟩ := hK.exists_fixedPoint' isClosed_closedBall.isComplete
    hmaps (mem_closedBall_zero_iff.2 haρ) (edist_ne_top _ _)
  exact ⟨x, mem_closedBall_zero_iff.1 hxs, hfix, htendsto⟩

/-- If `‖B‖ ≤ η` and `4 η ‖a‖ < 1`, the Picard iterates `x₀ = a`, `xₙ₊₁ = a + B xₙ xₙ` converge
to `B.bilinearFixedPoint a`. -/
theorem tendsto_iterate_bilinearFixedPoint (hB : ‖B‖ ≤ η) (ha : 4 * η * ‖a‖ < 1) :
    Tendsto (fun n ↦ (fun x ↦ a + B x x)^[n] a) atTop (𝓝 (B.bilinearFixedPoint a)) := by
  obtain ⟨x, -, -, h⟩ := exists_isFixedPt_tendsto_iterate hB ha
  rwa [bilinearFixedPoint, h.limUnder_eq]

/-- If `‖B‖ ≤ η` and `4 η ‖a‖ < 1`, then `x = B.bilinearFixedPoint a` solves `a + B x x = x`. -/
theorem isFixedPt_bilinearFixedPoint (hB : ‖B‖ ≤ η) (ha : 4 * η * ‖a‖ < 1) :
    IsFixedPt (fun x ↦ a + B x x) (B.bilinearFixedPoint a) := by
  obtain ⟨x, -, hx, h⟩ := exists_isFixedPt_tendsto_iterate hB ha
  rwa [bilinearFixedPoint, h.limUnder_eq]

/-- **The sharp bound.** If `‖B‖ ≤ η` and `4 η ‖a‖ < 1`, the solution of `x = a + B x x`
satisfies `‖x‖ ≤ 2 ‖a‖ / (1 + √(1 - 4 η ‖a‖))`. For `η > 0` the right-hand side equals
`(1 - √(1 - 4 η ‖a‖)) / (2 η)`, the smaller root of `η ρ² - ρ + ‖a‖ = 0`. -/
theorem norm_bilinearFixedPoint_le (hB : ‖B‖ ≤ η) (ha : 4 * η * ‖a‖ < 1) :
    ‖B.bilinearFixedPoint a‖ ≤ 2 * ‖a‖ / (1 + √(1 - 4 * η * ‖a‖)) := by
  obtain ⟨x, hx, -, h⟩ := exists_isFixedPt_tendsto_iterate hB ha
  rwa [bilinearFixedPoint, h.limUnder_eq]

/-- If `‖B‖ ≤ η` and `4 η ‖a‖ < 1`, the solution of `x = a + B x x` satisfies `‖x‖ ≤ 2 ‖a‖`. -/
theorem norm_bilinearFixedPoint_le_two_mul (hB : ‖B‖ ≤ η) (ha : 4 * η * ‖a‖ < 1) :
    ‖B.bilinearFixedPoint a‖ ≤ 2 * ‖a‖ :=
  (B.norm_bilinearFixedPoint_le hB ha).trans <|
    div_le_self (by positivity) (le_add_of_nonneg_right (Real.sqrt_nonneg _))

/-- If `‖B‖ ≤ η` and `4 η ‖a‖ < 1`, the solution `x` of `x = a + B x x` satisfies
`2 η ‖x‖ ≤ 1 - √(1 - 4 η ‖a‖)`. -/
theorem two_mul_mul_norm_bilinearFixedPoint_le (hB : ‖B‖ ≤ η) (ha : 4 * η * ‖a‖ < 1) :
    2 * η * ‖B.bilinearFixedPoint a‖ ≤ 1 - √(1 - 4 * η * ‖a‖) := by
  have hη : 0 ≤ η := (norm_nonneg B).trans hB
  calc 2 * η * ‖B.bilinearFixedPoint a‖ ≤ 2 * η * (2 * ‖a‖ / (1 + √(1 - 4 * η * ‖a‖))) := by
        gcongr; exact B.norm_bilinearFixedPoint_le hB ha
    _ = 1 - √(1 - 4 * η * ‖a‖) := two_mul_mul_radius ha

/-- If `‖B‖ ≤ η` and `4 η ‖a‖ < 1`, the solution `x` of `x = a + B x x` satisfies `2 η ‖x‖ < 1`,
that is, it lies in the ball of radius `1 / (2 η)` where solutions are unique. -/
theorem two_mul_mul_norm_bilinearFixedPoint_lt_one (hB : ‖B‖ ≤ η) (ha : 4 * η * ‖a‖ < 1) :
    2 * η * ‖B.bilinearFixedPoint a‖ < 1 := by
  have hs : 0 < √(1 - 4 * η * ‖a‖) := Real.sqrt_pos.2 (by linarith)
  linarith [B.two_mul_mul_norm_bilinearFixedPoint_le hB ha]

variable {B} in
/-- **Uniqueness.** If `‖B‖ ≤ η` and `4 η ‖a‖ < 1`, every solution of `x = a + B x x` with
`2 η ‖x‖ < 1`, that is with `‖x‖ < 1 / (2 η)`, is `B.bilinearFixedPoint a`. -/
theorem eq_bilinearFixedPoint (hB : ‖B‖ ≤ η) (ha : 4 * η * ‖a‖ < 1) {x : X} (hx : a + B x x = x)
    (hxη : 2 * η * ‖x‖ < 1) : x = B.bilinearFixedPoint a := by
  refine B.eq_of_add_apply_apply_eq hx (B.isFixedPt_bilinearFixedPoint hB ha) ?_
  have := B.two_mul_mul_norm_bilinearFixedPoint_lt_one hB ha
  calc ‖B‖ * (‖x‖ + ‖B.bilinearFixedPoint a‖)
        ≤ η * (‖x‖ + ‖B.bilinearFixedPoint a‖) := by gcongr
    _ < 1 := by linarith

/-- **The bilinear fixed-point lemma.** If `‖B x y‖ ≤ η ‖x‖ ‖y‖` for all `x y`, with `0 ≤ η`, and
`4 η ‖a‖ < 1`, then `x = a + B x x` has a solution with `‖x‖ ≤ 2 ‖a‖`, and it is the only solution
with `2 η ‖x‖ < 1`, that is with `‖x‖ < 1 / (2 η)`. -/
theorem exists_add_apply_apply_eq (hη : 0 ≤ η) (hB : ∀ x y, ‖B x y‖ ≤ η * ‖x‖ * ‖y‖)
    (ha : 4 * η * ‖a‖ < 1) :
    ∃ x, a + B x x = x ∧ ‖x‖ ≤ 2 * ‖a‖ ∧ ∀ y, a + B y y = y → 2 * η * ‖y‖ < 1 → y = x := by
  have hB' : ‖B‖ ≤ η := opNorm_le_bound₂ B hη hB
  exact ⟨B.bilinearFixedPoint a, B.isFixedPt_bilinearFixedPoint hB' ha,
    B.norm_bilinearFixedPoint_le_two_mul hB' ha, fun _ hy hyη ↦ eq_bilinearFixedPoint hB' ha hy hyη⟩

/-- **Lipschitz dependence on the data.** If `‖B‖ ≤ η` and `4 η r < 1`, the solution map
`a ↦ B.bilinearFixedPoint a` is Lipschitz on the closed ball of radius `r`, with constant
`(1 - 4 η r)^(-1/2)`. -/
theorem lipschitzOnWith_bilinearFixedPoint (hB : ‖B‖ ≤ η) {r : ℝ} (hr : 4 * η * r < 1) :
    LipschitzOnWith (Real.toNNReal (√(1 - 4 * η * r))⁻¹) B.bilinearFixedPoint
      (closedBall 0 r) := by
  have hη : 0 ≤ η := (norm_nonneg B).trans hB
  have hs : 0 < √(1 - 4 * η * r) := Real.sqrt_pos.2 (by linarith)
  -- For `‖a‖ ≤ r`, the solution satisfies `2 η ‖x‖ ≤ 1 - √(1 - 4 η ‖a‖) ≤ 1 - √(1 - 4 η r)`.
  have hsol {a : X} (ha : ‖a‖ ≤ r) :
      2 * η * ‖B.bilinearFixedPoint a‖ ≤ 1 - √(1 - 4 * η * r) := by
    have ha' : 4 * η * ‖a‖ < 1 := lt_of_le_of_lt (by gcongr) hr
    calc 2 * η * ‖B.bilinearFixedPoint a‖ ≤ 1 - √(1 - 4 * η * ‖a‖) :=
          B.two_mul_mul_norm_bilinearFixedPoint_le hB ha'
      _ ≤ 1 - √(1 - 4 * η * r) := by gcongr
  refine LipschitzOnWith.of_dist_le_mul fun a ha b hb ↦ ?_
  rw [mem_closedBall_zero_iff] at ha hb
  have ha' : 4 * η * ‖a‖ < 1 := lt_of_le_of_lt (by gcongr) hr
  have hb' : 4 * η * ‖b‖ < 1 := lt_of_le_of_lt (by gcongr) hr
  have h := B.one_sub_mul_norm_sub_le_norm_sub (B.isFixedPt_bilinearFixedPoint hB ha')
    (B.isFixedPt_bilinearFixedPoint hB hb')
  have hBxy : ‖B‖ * (‖B.bilinearFixedPoint a‖ + ‖B.bilinearFixedPoint b‖) ≤
      1 - √(1 - 4 * η * r) := by
    have := hsol ha
    have := hsol hb
    calc ‖B‖ * (‖B.bilinearFixedPoint a‖ + ‖B.bilinearFixedPoint b‖)
          ≤ η * (‖B.bilinearFixedPoint a‖ + ‖B.bilinearFixedPoint b‖) := by gcongr
      _ ≤ 1 - √(1 - 4 * η * r) := by linarith
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by positivity), inv_mul_eq_div,
    le_div_iff₀ hs]
  nlinarith [norm_nonneg (B.bilinearFixedPoint a - B.bilinearFixedPoint b)]

end Complete

/-! ### The scalar equation

For `X = ℝ` and `B x y = η x y` the equation `x = a + B x x` is `η x² - x + a = 0`. -/

variable {η a : ℝ}

/-- The scalar quadratic equation `η x² - x + a = 0` has no real solution when `4 η a > 1`. -/
theorem add_smul_mul_apply_apply_ne (ha : 1 < 4 * η * a) (x : ℝ) :
    a + (η • mul ℝ ℝ) x x ≠ x := by
  simp only [smul_apply, mul_apply', smul_eq_mul]
  intro h
  have h' : 4 * η * (a + η * (x * x)) = 4 * η * x := by rw [h]
  nlinarith [sq_nonneg (2 * η * x - 1)]

/-- For the scalar equation `η x² - x + a = 0` with `η > 0` and `4 η |a| < 1`, the solution
constructed is the smaller root `(1 - √(1 - 4 η a)) / (2 η)`. -/
theorem bilinearFixedPoint_smul_mul (hη : 0 < η) (ha : 4 * η * |a| < 1) :
    (η • mul ℝ ℝ).bilinearFixedPoint a = (1 - √(1 - 4 * η * a)) / (2 * η) := by
  have hle : 4 * η * a < 1 := lt_of_le_of_lt (by gcongr; exact le_abs_self a) ha
  have hge : -1 < 4 * η * a := by
    have := neg_abs_le a
    nlinarith
  have hs := Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 1 - 4 * η * a)
  have hs0 : 0 < √(1 - 4 * η * a) := Real.sqrt_pos.2 (by linarith)
  have hs2 : √(1 - 4 * η * a) < 2 := by nlinarith
  have hB : ‖η • mul ℝ ℝ‖ ≤ η := opNorm_le_bound₂ _ hη.le fun x y ↦ by
    simp [abs_of_pos hη, mul_assoc]
  refine (eq_bilinearFixedPoint hB (by rwa [Real.norm_eq_abs]) ?_ ?_).symm
  · simp only [smul_apply, mul_apply', smul_eq_mul]
    generalize √(1 - 4 * η * a) = s at *
    field_simp
    linear_combination hs
  · have h2η : 0 < 2 * η := by positivity
    rw [Real.norm_eq_abs, abs_div, abs_of_pos h2η, mul_div_cancel₀ _ h2η.ne', abs_lt]
    constructor <;> linarith

/-- For the scalar equation `η x² - x + a = 0` with `η > 0` and `4 η |a| < 1`, the derivative of
the solution map at `a` is `(1 - 4 η a)^(-1/2)`. For `a = r ≥ 0` this matches the Lipschitz
constant of `ContinuousLinearMap.lipschitzOnWith_bilinearFixedPoint` on the ball of radius `r`. -/
theorem hasDerivAt_bilinearFixedPoint_smul_mul (hη : 0 < η) (ha : 4 * η * |a| < 1) :
    HasDerivAt (η • mul ℝ ℝ).bilinearFixedPoint (√(1 - 4 * η * a))⁻¹ a := by
  have hle : 4 * η * a < 1 := lt_of_le_of_lt (by gcongr; exact le_abs_self a) ha
  have hs0 : √(1 - 4 * η * a) ≠ 0 := (Real.sqrt_pos.2 (by linarith)).ne'
  have hev : ∀ᶠ b in 𝓝 a, 4 * η * |b| < 1 :=
    (continuous_const.mul continuous_abs).continuousAt.eventually_lt continuousAt_const ha
  refine HasDerivAt.congr_of_eventuallyEq ?_
    (hev.mono fun b hb ↦ bilinearFixedPoint_smul_mul hη hb)
  have h₁ : HasDerivAt (fun b ↦ 1 - 4 * η * b) (-(4 * η)) a := by
    simpa using ((hasDerivAt_id a).const_mul (4 * η)).const_sub 1
  convert ((h₁.sqrt (sub_pos.2 hle).ne').const_sub 1).div_const (2 * η) using 1
  field_simp
  ring

end ContinuousLinearMap
