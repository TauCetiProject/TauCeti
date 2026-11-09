/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.ODE.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import TauCeti.Analysis.Calculus.Morse.OneDimensional
public import TauCeti.Analysis.Calculus.Morse.Pi
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The negative gradient flow of the Euclidean quartic

The quartic `quarticWell x = (x² - 1)² / 4` on `ℝ` has a local maximum at `0` and minima at `±1`.
Its negative gradient field is `x ↦ x (1 - x²)`, whose linearization is `1` at `0` and `-2` at
`±1`, so trajectories leave `0` at rate `1` and approach `±1` at rate `2`. The normalization by
`1 / 4` is the one making these rates `1` and `2`; the double well `(x² - 1)²` of
`TauCeti.Geometry.Manifold.Morse.Cell.Examples.DoubleWell` has the same flow run four times as
fast.

Unlike the linear models, this flow can be written down in closed form. For `x² ≤ 1` the
trajectory through `x` is

`quarticFlow t x = x eᵗ / √(1 - x² + x² e^{2t})`,

defined for all times (`TauCeti.hasDerivAt_quarticFlow`). It is a flow
(`TauCeti.quarticFlow_add`), it keeps `[-1, 1]` and `(-1, 1)` invariant, and as `t → ∞` it tends
to the sign of `x` (`TauCeti.tendsto_quarticFlow_atTop`), while for `x² < 1` it tends to `0` as
`t → -∞` (`TauCeti.tendsto_quarticFlow_atBot`). Since the field is Lipschitz on `[-1, 1]`, these
are the only negative gradient trajectories staying in `[-1, 1]`
(`TauCeti.eq_quarticFlow_of_isIntegralCurve`). Outside `[-1, 1]` the backward flow escapes in
finite time; it is not used here.

On `(0, 1)` the function `quarticTime x = log x - log (1 - x²) / 2` is a time coordinate: the
flow translates it, `quarticTime (quarticFlow t x) = quarticTime x + t`
(`TauCeti.quarticTime_quarticFlow`), and it identifies `(0, 1)` with `ℝ`, with inverse
`quarticOrbit s = eˢ / √(1 + e^{2s})`. Hence the trajectories from `0` to `1` form a single orbit,
and in the time coordinate `s` the identities `x² = e^{2s} / (1 + e^{2s})` and
`1 - x² = 1 / (1 + e^{2s})` display the two asymptotic rates exactly.

The separated sum `quarticWellSum y = ∑ i, quarticWell (y i)` on `ι → ℝ` is the standard model
for compactified spaces of broken trajectories and for the comparison of Morse chains with
cellular chains of the cube. Its critical points are the points of `{-1, 0, 1}^ι`, all
nondegenerate, and the Morse index of such a point is the number of its zero coordinates
(`TauCeti.morseIndex_quarticWellSum`). Its partial derivatives are those of the summands
(`TauCeti.fderiv_quarticWellSum_apply`), so its negative gradient field for the Euclidean inner
product acts coordinatewise, and its flow `quarticWellSumFlow` is the coordinatewise quartic flow.
It keeps the cube `[-1, 1]^ι` invariant, and every point of the cube has a forward limit, the
coordinatewise sign, and a backward limit, which keeps the coordinates equal to `±1` and replaces
the others by `0`. So the points of the cube flowing backward to a critical point `p` form the open
face of the cube centred at `p`. A point `y` of the cube lies on a trajectory from `p` to `q`
exactly when, coordinatewise, either `p i = 0`, `y i ∈ (-1, 1)` and `q i` is the sign of `y i`, or
`y i = p i = q i = ±1` (`TauCeti.tendsto_quarticWellSumFlow_atBot_atTop_iff`). The coordinates
that move are those with `p i = 0 ≠ q i`, and their number is the index difference.

## Main definitions

* `TauCeti.quarticWell`: the quartic `(x² - 1)² / 4`.
* `TauCeti.quarticFlow`: its negative gradient flow on `[-1, 1]`.
* `TauCeti.quarticTime`, `TauCeti.quarticOrbit`: the time coordinate on `(0, 1)` and its inverse.
* `TauCeti.quarticWellSum`, `TauCeti.quarticWellSumFlow`: the separated sum on `ι → ℝ` and its
  coordinatewise flow.

## Main results

* `TauCeti.isNondegenerateCriticalPoint_quarticWell_iff`, `TauCeti.morseIndex_quarticWell_zero`,
  `TauCeti.morseIndex_quarticWell_one`, `TauCeti.morseIndex_quarticWell_neg_one`: the critical
  points and their indices.
* `TauCeti.isIntegralCurve_quarticFlow`, `TauCeti.eq_quarticFlow_of_isIntegralCurve`: the
  trajectories in `[-1, 1]` are the curves `t ↦ quarticFlow t x`.
* `TauCeti.quarticFlow_add`: the flow property.
* `TauCeti.tendsto_quarticFlow_atTop`, `TauCeti.tendsto_quarticFlow_atBot`: the limits.
* `TauCeti.quarticTime_quarticFlow`, `TauCeti.quarticFlow_eq_quarticOrbit`: the time coordinate.
* `TauCeti.isNondegenerateCriticalPoint_quarticWellSum_iff`, `TauCeti.morseIndex_quarticWellSum`:
  the critical points of the separated sum and their indices.
* `TauCeti.hasDerivAt_quarticWellSumFlow`, `TauCeti.fderiv_quarticWellSum_apply`: the coordinatewise
  flow integrates the negative Euclidean gradient.
* `TauCeti.tendsto_quarticWellSumFlow_atTop`, `TauCeti.tendsto_quarticWellSumFlow_atBot`,
  `TauCeti.tendsto_quarticWellSumFlow_atBot_atTop_iff`: limits and connecting trajectories in the
  cube.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §3 (the comparison of the Morse complex with cellular
  homology, which this quartic on the cube models).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 2 (negative gradient trajectories and their limits).
-/

public section

noncomputable section

open Real Set Filter Topology
open scoped Gradient

namespace TauCeti

/-! ### The quartic and its critical points -/

/-- The **Euclidean quartic** `(x² - 1)² / 4` on `ℝ`, normalized so that its negative gradient
field is `x (1 - x²)`. -/
def quarticWell (x : ℝ) : ℝ := (x ^ 2 - 1) ^ 2 / 4

theorem quarticWell_def (x : ℝ) : quarticWell x = (x ^ 2 - 1) ^ 2 / 4 := (rfl)

theorem hasDerivAt_quarticWell (x : ℝ) : HasDerivAt quarticWell (x ^ 3 - x) x := by
  have h := (((hasDerivAt_pow 2 x).sub_const 1).pow 2).div_const 4
  convert h using 1
  · exact funext quarticWell_def
  · push_cast
    ring

@[simp]
theorem deriv_quarticWell (x : ℝ) : deriv quarticWell x = x ^ 3 - x :=
  (hasDerivAt_quarticWell x).deriv

theorem deriv_quarticWell_eq : deriv quarticWell = fun x ↦ x ^ 3 - x :=
  funext deriv_quarticWell

/-- The negative gradient of the quartic is `x (1 - x²)`. -/
@[simp]
theorem neg_gradient_quarticWell (x : ℝ) : -∇ quarticWell x = x * (1 - x ^ 2) := by
  rw [gradient_eq_deriv', deriv_quarticWell]
  ring

@[fun_prop]
theorem contDiff_quarticWell {n : WithTop ℕ∞} : ContDiff ℝ n quarticWell := by
  unfold quarticWell
  fun_prop

theorem deriv_deriv_quarticWell (x : ℝ) : deriv (deriv quarticWell) x = 3 * x ^ 2 - 1 := by
  rw [deriv_quarticWell_eq]
  have h : HasDerivAt (fun x : ℝ ↦ x ^ 3 - x) (3 * x ^ 2 - 1) x := by
    simpa using (hasDerivAt_pow 3 x).fun_sub (hasDerivAt_id' x)
  exact h.deriv

theorem iteratedDeriv_two_quarticWell (x : ℝ) : iteratedDeriv 2 quarticWell x = 3 * x ^ 2 - 1 := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, deriv_deriv_quarticWell]

/-- The critical points of the quartic are `-1`, `0` and `1`. -/
theorem deriv_quarticWell_eq_zero_iff {x : ℝ} :
    deriv quarticWell x = 0 ↔ x = -1 ∨ x = 0 ∨ x = 1 := by
  rw [deriv_quarticWell, show x ^ 3 - x = x * (x + 1) * (x - 1) by ring]
  simp only [mul_eq_zero, add_eq_zero_iff_eq_neg, sub_eq_zero]
  tauto

/-- **The quartic is a Morse function**: its critical points `-1`, `0` and `1` are nondegenerate. -/
theorem isNondegenerateCriticalPoint_quarticWell_iff {x : ℝ} :
    IsNondegenerateCriticalPoint quarticWell x ↔ x = -1 ∨ x = 0 ∨ x = 1 := by
  rw [isNondegenerateCriticalPoint_real_iff contDiff_quarticWell.contDiffAt,
    deriv_quarticWell_eq_zero_iff, iteratedDeriv_two_quarticWell]
  refine ⟨And.left, fun h ↦ ⟨h, ?_⟩⟩
  rcases h with rfl | rfl | rfl <;> norm_num

/-- The local maximum `0` of the quartic has Morse index `1`. -/
@[simp]
theorem morseIndex_quarticWell_zero : morseIndex quarticWell 0 = 1 :=
  (isNondegenerateCriticalPoint_quarticWell_iff.2 (by simp)).morseIndex_real_of_neg
    (by rw [iteratedDeriv_two_quarticWell]; norm_num)

/-- The minimum `1` of the quartic has Morse index `0`. -/
@[simp]
theorem morseIndex_quarticWell_one : morseIndex quarticWell 1 = 0 :=
  (isNondegenerateCriticalPoint_quarticWell_iff.2 (by simp)).morseIndex_real_of_pos
    (by rw [iteratedDeriv_two_quarticWell]; norm_num)

/-- The minimum `-1` of the quartic has Morse index `0`. -/
@[simp]
theorem morseIndex_quarticWell_neg_one : morseIndex quarticWell (-1) = 0 :=
  (isNondegenerateCriticalPoint_quarticWell_iff.2 (by simp)).morseIndex_real_of_pos
    (by rw [iteratedDeriv_two_quarticWell]; norm_num)

/-! ### The flow on `[-1, 1]` -/

/-- The **negative gradient flow of the quartic**, `x eᵗ / √(1 - x² + x² e^{2t})`. For `x² ≤ 1`
it is the trajectory through `x` (`TauCeti.hasDerivAt_quarticFlow`); for `x² > 1` the backward
flow escapes in finite time, and the formula has no dynamical meaning once the radicand is
negative. -/
def quarticFlow (t x : ℝ) : ℝ := x * exp t / √(1 - x ^ 2 + x ^ 2 * exp (2 * t))

theorem quarticFlow_def (t x : ℝ) :
    quarticFlow t x = x * exp t / √(1 - x ^ 2 + x ^ 2 * exp (2 * t)) := (rfl)

/-- The radicand of the flow is positive for `x² ≤ 1`. -/
private theorem quarticFlow_radicand_pos {x : ℝ} (hx : x ^ 2 ≤ 1) (t : ℝ) :
    0 < 1 - x ^ 2 + x ^ 2 * exp (2 * t) := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  · have := mul_pos (pow_pos (abs_pos.2 hx0) 2) (exp_pos (2 * t))
    rw [sq_abs] at this
    linarith

private theorem exp_two_mul_eq_sq (t : ℝ) : exp (2 * t) = exp t ^ 2 := by
  rw [← exp_nat_mul]
  norm_num

/-- The square of the flow, `x² e^{2t} / (1 - x² + x² e^{2t})`. -/
theorem sq_quarticFlow {x : ℝ} (hx : x ^ 2 ≤ 1) (t : ℝ) :
    quarticFlow t x ^ 2 = x ^ 2 * exp (2 * t) / (1 - x ^ 2 + x ^ 2 * exp (2 * t)) := by
  rw [quarticFlow_def, div_pow, sq_sqrt (quarticFlow_radicand_pos hx t).le, mul_pow,
    exp_two_mul_eq_sq]

/-- One minus the square of the flow, `(1 - x²) / (1 - x² + x² e^{2t})`. -/
theorem one_sub_sq_quarticFlow {x : ℝ} (hx : x ^ 2 ≤ 1) (t : ℝ) :
    1 - quarticFlow t x ^ 2 = (1 - x ^ 2) / (1 - x ^ 2 + x ^ 2 * exp (2 * t)) := by
  have h := (quarticFlow_radicand_pos hx t).ne'
  rw [sq_quarticFlow hx, eq_div_iff h, sub_mul, div_mul_cancel₀ _ h]
  ring

@[simp]
theorem quarticFlow_zero_left (x : ℝ) : quarticFlow 0 x = x := by
  simp [quarticFlow_def]

@[simp]
theorem quarticFlow_zero_right (t : ℝ) : quarticFlow t 0 = 0 := by
  simp [quarticFlow_def]

@[simp]
theorem quarticFlow_one (t : ℝ) : quarticFlow t 1 = 1 := by
  rw [quarticFlow_def, exp_two_mul_eq_sq]
  simp [sqrt_sq (exp_pos t).le, (exp_pos t).ne']

@[simp]
theorem quarticFlow_neg (t x : ℝ) : quarticFlow t (-x) = -quarticFlow t x := by
  simp [quarticFlow_def, neg_div]

theorem quarticFlow_neg_one (t : ℝ) : quarticFlow t (-1) = -1 := by
  simp

theorem quarticFlow_pos {x : ℝ} (hx : 0 < x) (hx1 : x ^ 2 ≤ 1) (t : ℝ) : 0 < quarticFlow t x :=
  div_pos (mul_pos hx (exp_pos t)) (sqrt_pos.2 (quarticFlow_radicand_pos hx1 t))

theorem quarticFlow_neg_of_neg {x : ℝ} (hx : x < 0) (hx1 : x ^ 2 ≤ 1) (t : ℝ) :
    quarticFlow t x < 0 := by
  have := quarticFlow_pos (neg_pos.2 hx) (by rwa [neg_sq]) t
  rw [quarticFlow_neg] at this
  linarith

theorem sq_quarticFlow_le_one {x : ℝ} (hx : x ^ 2 ≤ 1) (t : ℝ) : quarticFlow t x ^ 2 ≤ 1 := by
  have := one_sub_sq_quarticFlow hx t
  have : 0 ≤ 1 - quarticFlow t x ^ 2 := by
    rw [this]
    exact div_nonneg (by linarith) (quarticFlow_radicand_pos hx t).le
  linarith

theorem sq_quarticFlow_lt_one {x : ℝ} (hx : x ^ 2 < 1) (t : ℝ) : quarticFlow t x ^ 2 < 1 := by
  have := one_sub_sq_quarticFlow hx.le t
  have : 0 < 1 - quarticFlow t x ^ 2 := by
    rw [this]
    exact div_pos (by linarith) (quarticFlow_radicand_pos hx.le t)
  linarith

private theorem sq_le_one_iff_mem_Icc {x : ℝ} : x ^ 2 ≤ 1 ↔ x ∈ Icc (-1) 1 := by
  rw [sq_le_one_iff_abs_le_one, abs_le, mem_Icc]

private theorem sq_lt_one_iff_mem_Ioo {x : ℝ} : x ^ 2 < 1 ↔ x ∈ Ioo (-1) 1 := by
  rw [sq_lt_one_iff_abs_lt_one, abs_lt, mem_Ioo]

private theorem eq_or_eq_of_mem_Icc_of_notMem_Ioo {x : ℝ} (hx : x ∈ Icc (-1) 1)
    (hx' : x ∉ Ioo (-1) 1) : x = -1 ∨ x = 1 := by
  rw [mem_Icc] at hx
  rw [mem_Ioo, not_and_or, not_lt, not_lt] at hx'
  rcases hx' with h | h
  · exact .inl (le_antisymm h hx.1)
  · exact .inr (le_antisymm hx.2 h)

/-- The flow keeps `[-1, 1]` invariant. -/
theorem quarticFlow_mem_Icc {x : ℝ} (hx : x ∈ Icc (-1) 1) (t : ℝ) :
    quarticFlow t x ∈ Icc (-1) 1 :=
  sq_le_one_iff_mem_Icc.1 (sq_quarticFlow_le_one (sq_le_one_iff_mem_Icc.2 hx) t)

/-- The flow keeps `(-1, 1)` invariant. -/
theorem quarticFlow_mem_Ioo {x : ℝ} (hx : x ∈ Ioo (-1) 1) (t : ℝ) :
    quarticFlow t x ∈ Ioo (-1) 1 :=
  sq_lt_one_iff_mem_Ioo.1 (sq_quarticFlow_lt_one (sq_lt_one_iff_mem_Ioo.2 hx) t)

/-- **The flow solves the negative gradient equation** `x' = x (1 - x²)`. -/
theorem hasDerivAt_quarticFlow {x : ℝ} (hx : x ^ 2 ≤ 1) (t : ℝ) :
    HasDerivAt (fun t ↦ quarticFlow t x) (quarticFlow t x * (1 - quarticFlow t x ^ 2)) t := by
  have hD := quarticFlow_radicand_pos hx t
  have hD' : HasDerivAt (fun t ↦ 1 - x ^ 2 + x ^ 2 * exp (2 * t))
      (x ^ 2 * (exp (2 * t) * 2)) t := by
    simpa using (((hasDerivAt_id t).const_mul 2).exp.const_mul (x ^ 2)).const_add (1 - x ^ 2)
  have h : HasDerivAt (fun t ↦ quarticFlow t x) _ t :=
    ((hasDerivAt_exp t).const_mul x).fun_div (hD'.sqrt hD.ne') (sqrt_pos.2 hD).ne'
  convert h using 1
  rw [one_sub_sq_quarticFlow hx, quarticFlow_def]
  have hs := sq_sqrt hD.le
  set r := √(1 - x ^ 2 + x ^ 2 * exp (2 * t))
  have hr : 0 < r := sqrt_pos.2 hD
  rw [← hs]
  field_simp
  rw [exp_two_mul_eq_sq] at hs ⊢
  linear_combination (-x) * hs

/-- The flow is an integral curve of the negative gradient field of the quartic. -/
theorem isIntegralCurve_quarticFlow {x : ℝ} (hx : x ∈ Icc (-1) 1) :
    IsIntegralCurve (fun t ↦ quarticFlow t x) (fun _ y ↦ -∇ quarticWell y) := fun t ↦ by
  simpa using hasDerivAt_quarticFlow (sq_le_one_iff_mem_Icc.2 hx) t

/-- **The flow property** `φ (s + t) = φ s ∘ φ t` on `[-1, 1]`. -/
theorem quarticFlow_add {x : ℝ} (hx : x ^ 2 ≤ 1) (s t : ℝ) :
    quarticFlow (s + t) x = quarticFlow s (quarticFlow t x) := by
  have hD := quarticFlow_radicand_pos hx t
  have hD' := quarticFlow_radicand_pos hx (s + t)
  have hrad : 1 - quarticFlow t x ^ 2 + quarticFlow t x ^ 2 * exp (2 * s) =
      (1 - x ^ 2 + x ^ 2 * exp (2 * (s + t))) / (1 - x ^ 2 + x ^ 2 * exp (2 * t)) := by
    rw [one_sub_sq_quarticFlow hx, sq_quarticFlow hx, mul_add, exp_add]
    field_simp
  rw [quarticFlow_def s, hrad, sqrt_div hD'.le, quarticFlow_def, quarticFlow_def, exp_add]
  have := (sqrt_pos.2 hD).ne'
  have := (sqrt_pos.2 hD').ne'
  field_simp

/-- The flow written as `x / √((1 - x²) e^{-2t} + x²)`, the form in which its forward limit is
visible. -/
private theorem quarticFlow_eq_div_sqrt (x t : ℝ) :
    quarticFlow t x = x / √((1 - x ^ 2) * exp (-(2 * t)) + x ^ 2) := by
  have hE : 1 - x ^ 2 + x ^ 2 * exp (2 * t) =
      exp t ^ 2 * ((1 - x ^ 2) * exp (-(2 * t)) + x ^ 2) := by
    rw [← exp_two_mul_eq_sq, mul_add, ← mul_assoc, mul_comm (exp _), mul_assoc, ← exp_add]
    simp only [add_neg_cancel, exp_zero, mul_one]
    ring
  rw [quarticFlow_def, hE, sqrt_mul (sq_nonneg _), sqrt_sq (exp_pos t).le, mul_comm (exp t),
    mul_div_mul_right _ _ (exp_pos t).ne']

/-- **Forward limit**: as `t → ∞` the flow from `x ∈ [-1, 1]` tends to the sign of `x`, the
minimum `±1` on its side of `0`, or `0` if `x = 0`. -/
theorem tendsto_quarticFlow_atTop {x : ℝ} (hx : x ∈ Icc (-1) 1) :
    Tendsto (fun t ↦ quarticFlow t x) atTop (𝓝 (SignType.sign x)) := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  simp_rw [quarticFlow_eq_div_sqrt x]
  have hexp : Tendsto (fun t : ℝ ↦ exp (-(2 * t))) atTop (𝓝 0) :=
    tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop two_pos)
  have hlim := ((hexp.const_mul (1 - x ^ 2)).add_const (x ^ 2)).sqrt
  rw [mul_zero, zero_add, sqrt_sq_eq_abs] at hlim
  have h := (tendsto_const_nhds (x := x)).div hlim (abs_pos.2 hx0).ne'
  rwa [show (SignType.sign x : ℝ) = x / |x| by
    rw [eq_div_iff (abs_pos.2 hx0).ne', sign_mul_abs]]

/-- **Backward limit**: as `t → -∞` the flow from `x ∈ (-1, 1)` tends to the maximum `0`. -/
theorem tendsto_quarticFlow_atBot {x : ℝ} (hx : x ∈ Ioo (-1) 1) :
    Tendsto (fun t ↦ quarticFlow t x) atBot (𝓝 0) := by
  have hx1 := sq_lt_one_iff_mem_Ioo.2 hx
  have hexp : Tendsto (fun t : ℝ ↦ exp (2 * t)) atBot (𝓝 0) :=
    tendsto_exp_atBot.comp (tendsto_id.const_mul_atBot two_pos)
  have h := (tendsto_exp_atBot.const_mul x).div
    (((hexp.const_mul (x ^ 2)).const_add (1 - x ^ 2)).sqrt)
    (sqrt_pos.2 (by simpa using sub_pos.2 hx1)).ne'
  rw [mul_zero, zero_div] at h
  exact h

/-- The backward limit of the flow from `x ∈ [-1, 1]`: `0` if `x ∈ (-1, 1)`, and `x` itself if
`x = ±1`, where the flow is stationary. -/
theorem tendsto_quarticFlow_atBot_ite {x : ℝ} (hx : x ∈ Icc (-1) 1) :
    Tendsto (fun t ↦ quarticFlow t x) atBot (𝓝 (if x ∈ Ioo (-1) 1 then 0 else x)) := by
  split_ifs with hx'
  · exact tendsto_quarticFlow_atBot hx'
  · rcases eq_or_eq_of_mem_Icc_of_notMem_Ioo hx hx' with rfl | rfl <;> simp

/-- The negative gradient field of the quartic is `2`-Lipschitz on `[-1, 1]`: the difference
quotient of `x (1 - x²)` is `1 - (x² + x y + y²)`. -/
theorem lipschitzOnWith_neg_gradient_quarticWell :
    LipschitzOnWith 2 (fun y ↦ -∇ quarticWell y) (Icc (-1) 1) := by
  refine LipschitzOnWith.of_dist_le_mul fun a ha b hb ↦ ?_
  rw [mem_Icc] at ha hb
  simp only [neg_gradient_quarticWell, dist_eq_norm, norm_eq_abs, NNReal.coe_ofNat]
  rw [show a * (1 - a ^ 2) - b * (1 - b ^ 2) = (a - b) * (1 - (a ^ 2 + a * b + b ^ 2)) by ring,
    abs_mul, mul_comm]
  gcongr
  rw [abs_le]
  constructor <;> nlinarith

/-- **Uniqueness of captured trajectories**: a negative gradient trajectory of the quartic which
stays in `[-1, 1]` is the flow line through its initial point. -/
theorem eq_quarticFlow_of_isIntegralCurve {γ : ℝ → ℝ}
    (hγ : IsIntegralCurve γ (fun _ y ↦ -∇ quarticWell y)) (hmem : ∀ t, γ t ∈ Icc (-1) 1) :
    γ = fun t ↦ quarticFlow t (γ 0) :=
  ODE_solution_unique_univ (v := fun _ y ↦ -∇ quarticWell y) (s := fun _ ↦ Icc (-1) 1)
    (fun _ ↦ lipschitzOnWith_neg_gradient_quarticWell) (fun t ↦ ⟨hγ t, hmem t⟩)
    (fun t ↦ ⟨isIntegralCurve_quarticFlow (hmem 0) t, quarticFlow_mem_Icc (hmem 0) t⟩)
    (t₀ := 0) (by simp)

/-! ### The time coordinate on `(0, 1)` -/

/-- The **time coordinate** `log x - log (1 - x²) / 2` on `(0, 1)`, which the flow translates. -/
def quarticTime (x : ℝ) : ℝ := log x - log (1 - x ^ 2) / 2

theorem quarticTime_def (x : ℝ) : quarticTime x = log x - log (1 - x ^ 2) / 2 := (rfl)

/-- The flow translates the time coordinate: `quarticTime (quarticFlow t x) = quarticTime x + t`. -/
theorem quarticTime_quarticFlow {x : ℝ} (hx : x ∈ Ioo 0 1) (t : ℝ) :
    quarticTime (quarticFlow t x) = quarticTime x + t := by
  have hx1 : x ^ 2 < 1 := by nlinarith [hx.1, hx.2]
  have hD := quarticFlow_radicand_pos hx1.le t
  rw [quarticTime_def, one_sub_sq_quarticFlow hx1.le, quarticFlow_def, quarticTime_def,
    log_div (mul_pos hx.1 (exp_pos t)).ne' (sqrt_pos.2 hD).ne', log_mul hx.1.ne' (exp_pos t).ne',
    log_exp, log_sqrt hD.le, log_div (by linarith) hD.ne']
  ring

/-- The **unit-speed orbit** `eˢ / √(1 + e^{2s})` from `0` to `1`, the inverse of the time
coordinate. -/
def quarticOrbit (s : ℝ) : ℝ := exp s / √(1 + exp (2 * s))

theorem quarticOrbit_def (s : ℝ) : quarticOrbit s = exp s / √(1 + exp (2 * s)) := (rfl)

theorem quarticOrbit_pos (s : ℝ) : 0 < quarticOrbit s :=
  div_pos (exp_pos s) (sqrt_pos.2 (by positivity))

/-- In the time coordinate `s`, `x² = e^{2s} / (1 + e^{2s})`: the orbit leaves `0` at rate `1`. -/
theorem sq_quarticOrbit (s : ℝ) : quarticOrbit s ^ 2 = exp (2 * s) / (1 + exp (2 * s)) := by
  rw [quarticOrbit_def, div_pow, sq_sqrt (by positivity), exp_two_mul_eq_sq]

/-- In the time coordinate `s`, `1 - x² = 1 / (1 + e^{2s})`: the orbit approaches `1` at
rate `2`. -/
theorem one_sub_sq_quarticOrbit (s : ℝ) : 1 - quarticOrbit s ^ 2 = 1 / (1 + exp (2 * s)) := by
  have : 0 < 1 + exp (2 * s) := by positivity
  rw [sq_quarticOrbit]
  field_simp
  ring

theorem quarticOrbit_mem_Ioo (s : ℝ) : quarticOrbit s ∈ Ioo 0 1 := by
  refine ⟨quarticOrbit_pos s, ?_⟩
  have h := one_sub_sq_quarticOrbit s
  have : 0 < 1 - quarticOrbit s ^ 2 := by rw [h]; positivity
  nlinarith [quarticOrbit_pos s]

@[simp]
theorem quarticTime_quarticOrbit (s : ℝ) : quarticTime (quarticOrbit s) = s := by
  have : 0 < 1 + exp (2 * s) := by positivity
  rw [quarticTime_def, one_sub_sq_quarticOrbit, quarticOrbit_def,
    log_div (exp_pos s).ne' (sqrt_pos.2 this).ne', log_exp, log_sqrt this.le, one_div, log_inv]
  ring

theorem quarticOrbit_quarticTime {x : ℝ} (hx : x ∈ Ioo 0 1) : quarticOrbit (quarticTime x) = x := by
  have hx1 : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  have he : exp (2 * quarticTime x) = x ^ 2 / (1 - x ^ 2) := by
    rw [quarticTime_def, show 2 * (log x - log (1 - x ^ 2) / 2) = 2 * log x - log (1 - x ^ 2) by
      ring, exp_sub, exp_log hx1, exp_two_mul_eq_sq, exp_log hx.1]
  refine (pow_left_inj₀ (quarticOrbit_pos _).le hx.1.le two_ne_zero).1 ?_
  rw [sq_quarticOrbit, he]
  field_simp
  ring

/-- The time coordinate identifies `(0, 1)` with `ℝ`. -/
theorem bijOn_quarticTime : BijOn quarticTime (Ioo 0 1) univ :=
  ⟨fun _ _ ↦ mem_univ _,
    fun x hx y hy h ↦ by rw [← quarticOrbit_quarticTime hx, h, quarticOrbit_quarticTime hy],
    fun s _ ↦ ⟨quarticOrbit s, quarticOrbit_mem_Ioo s, quarticTime_quarticOrbit s⟩⟩

/-- **The trajectories from `0` to `1` form one orbit**: in the time coordinate the flow from
`x ∈ (0, 1)` is the unit-speed orbit started at time `quarticTime x`. -/
theorem quarticFlow_eq_quarticOrbit {x : ℝ} (hx : x ∈ Ioo 0 1) (t : ℝ) :
    quarticFlow t x = quarticOrbit (quarticTime x + t) := by
  have hx' : x ∈ Ioo (-1) 1 := ⟨by linarith [hx.1], hx.2⟩
  have hy : quarticFlow t x ∈ Ioo 0 1 :=
    ⟨quarticFlow_pos hx.1 (sq_le_one_iff_mem_Icc.2 (Ioo_subset_Icc_self hx')) t,
      (quarticFlow_mem_Ioo hx' t).2⟩
  rw [← quarticTime_quarticFlow hx, quarticOrbit_quarticTime hy]

/-! ### The quartic on the cube -/

section Sum

variable {ι : Type*}

/-- The **negative gradient flow of the Euclidean quartic** on the cube `[-1, 1]^ι`: the quartic
flow in each coordinate. -/
def quarticWellSumFlow (t : ℝ) (y : ι → ℝ) : ι → ℝ := fun i ↦ quarticFlow t (y i)

@[simp]
theorem quarticWellSumFlow_apply (t : ℝ) (y : ι → ℝ) (i : ι) :
    quarticWellSumFlow t y i = quarticFlow t (y i) := (rfl)

private theorem mem_Icc_neg_one_one_iff {y : ι → ℝ} : y ∈ Icc (-1) 1 ↔ ∀ i, y i ∈ Icc (-1) 1 := by
  simp only [mem_Icc, Pi.le_def, Pi.neg_apply, Pi.one_apply, forall_and]

@[simp]
theorem quarticWellSumFlow_zero_left (y : ι → ℝ) : quarticWellSumFlow 0 y = y :=
  funext fun i ↦ quarticFlow_zero_left (y i)

/-- The flow property of the coordinatewise flow on the cube. -/
theorem quarticWellSumFlow_add {y : ι → ℝ} (hy : y ∈ Icc (-1) 1) (s t : ℝ) :
    quarticWellSumFlow (s + t) y = quarticWellSumFlow s (quarticWellSumFlow t y) :=
  funext fun i ↦ quarticFlow_add (sq_le_one_iff_mem_Icc.2 (mem_Icc_neg_one_one_iff.1 hy i)) s t

/-- The flow keeps the cube `[-1, 1]^ι` invariant. -/
theorem quarticWellSumFlow_mem_Icc {y : ι → ℝ} (hy : y ∈ Icc (-1) 1) (t : ℝ) :
    quarticWellSumFlow t y ∈ Icc (-1) 1 :=
  mem_Icc_neg_one_one_iff.2 fun i ↦ quarticFlow_mem_Icc (mem_Icc_neg_one_one_iff.1 hy i) t

/-- The coordinatewise flow solves the negative gradient equation `yᵢ' = -(yᵢ³ - yᵢ)` of the
Euclidean quartic. -/
theorem hasDerivAt_quarticWellSumFlow {y : ι → ℝ} (hy : y ∈ Icc (-1) 1) (t : ℝ) :
    HasDerivAt (fun t ↦ quarticWellSumFlow t y)
      (fun i ↦ -deriv quarticWell (quarticWellSumFlow t y i)) t :=
  hasDerivAt_pi.2 fun i ↦ by
    simpa [gradient_eq_deriv'] using
      isIntegralCurve_quarticFlow (mem_Icc_neg_one_one_iff.1 hy i) t

/-- **Forward limits on the cube**: every point of `[-1, 1]^ι` flows to the critical point given
by the signs of its coordinates. -/
theorem tendsto_quarticWellSumFlow_atTop {y : ι → ℝ} (hy : y ∈ Icc (-1) 1) :
    Tendsto (fun t ↦ quarticWellSumFlow t y) atTop (𝓝 fun i ↦ (SignType.sign (y i) : ℝ)) :=
  tendsto_pi_nhds.2 fun i ↦ tendsto_quarticFlow_atTop (mem_Icc_neg_one_one_iff.1 hy i)

/-- **Backward limits on the cube**: as `t → -∞` a point of `[-1, 1]^ι` tends to the critical
point keeping its coordinates equal to `±1` and replacing the others by `0`. -/
theorem tendsto_quarticWellSumFlow_atBot {y : ι → ℝ} (hy : y ∈ Icc (-1) 1) :
    Tendsto (fun t ↦ quarticWellSumFlow t y) atBot
      (𝓝 fun i ↦ if y i ∈ Ioo (-1) 1 then 0 else y i) :=
  tendsto_pi_nhds.2 fun i ↦ tendsto_quarticFlow_atBot_ite (mem_Icc_neg_one_one_iff.1 hy i)

/-- **Connecting trajectories in the cube.** A point `y` of `[-1, 1]^ι` lies on a trajectory from
`p` to `q` exactly when each coordinate either moves, with `p i = 0`, `y i ∈ (-1, 1)` and `q i`
the sign of `y i`, or stays at `y i = p i = q i = ±1`. -/
theorem tendsto_quarticWellSumFlow_atBot_atTop_iff {y p q : ι → ℝ} (hy : y ∈ Icc (-1) 1) :
    Tendsto (fun t ↦ quarticWellSumFlow t y) atBot (𝓝 p) ∧
        Tendsto (fun t ↦ quarticWellSumFlow t y) atTop (𝓝 q) ↔
      ∀ i, (y i ∈ Ioo (-1) 1 ∧ p i = 0 ∧ q i = SignType.sign (y i)) ∨
        ((y i = -1 ∨ y i = 1) ∧ p i = y i ∧ q i = y i) := by
  have hbot := tendsto_quarticWellSumFlow_atBot hy
  have htop := tendsto_quarticWellSumFlow_atTop hy
  have key : ∀ i, (p i = (if y i ∈ Ioo (-1) 1 then 0 else y i) ∧
      q i = SignType.sign (y i)) ↔ ((y i ∈ Ioo (-1) 1 ∧ p i = 0 ∧ q i = SignType.sign (y i)) ∨
        ((y i = -1 ∨ y i = 1) ∧ p i = y i ∧ q i = y i)) := fun i ↦ by
    by_cases hi : y i ∈ Ioo (-1) 1
    · have : ¬(y i = -1 ∨ y i = 1) := by rintro (h | h) <;> simp [h] at hi
      simp [hi, this]
    · have h := eq_or_eq_of_mem_Icc_of_notMem_Ioo (mem_Icc_neg_one_one_iff.1 hy i) hi
      have hs : (SignType.sign (y i) : ℝ) = y i := by rcases h with h | h <;> simp [h]
      simp [hi, h, hs]
  refine ⟨fun ⟨hp, hq⟩ i ↦ (key i).1 ⟨congrFun (tendsto_nhds_unique hp hbot) i,
    congrFun (tendsto_nhds_unique hq htop) i⟩, fun h ↦ ?_⟩
  have hp : p = fun i ↦ if y i ∈ Ioo (-1) 1 then 0 else y i := funext fun i ↦ ((key i).2 (h i)).1
  have hq : q = fun i ↦ (SignType.sign (y i) : ℝ) := funext fun i ↦ ((key i).2 (h i)).2
  exact ⟨hp ▸ hbot, hq ▸ htop⟩

variable [Fintype ι]

/-- The **Euclidean quartic** `∑ i, (yᵢ² - 1)² / 4` on `ι → ℝ`, the separated sum of copies of
`TauCeti.quarticWell`. -/
def quarticWellSum (y : ι → ℝ) : ℝ := ∑ i, quarticWell (y i)

theorem quarticWellSum_def (y : ι → ℝ) :
    quarticWellSum y = ∑ i, quarticWell (y i) := (rfl)

private theorem quarticWellSum_eq :
    (quarticWellSum : (ι → ℝ) → ℝ) = fun z ↦ ∑ i, quarticWell (z i) :=
  funext quarticWellSum_def

/-- The partial derivatives of the Euclidean quartic are those of its summands, so its gradient
for the Euclidean inner product is `(yᵢ³ - yᵢ)ᵢ`. -/
theorem fderiv_quarticWellSum_apply (y v : ι → ℝ) :
    fderiv ℝ quarticWellSum y v = ∑ i, deriv quarticWell (y i) * v i := by
  rw [quarticWellSum_eq,
    fderiv_sum_comp_eval fun _ ↦ (hasDerivAt_quarticWell _).differentiableAt]
  simp

/-- **The Euclidean quartic is a Morse function**: its critical points are the points of
`{-1, 0, 1}^ι`, all nondegenerate. -/
theorem isNondegenerateCriticalPoint_quarticWellSum_iff {y : ι → ℝ} :
    IsNondegenerateCriticalPoint quarticWellSum y ↔ ∀ i, y i = -1 ∨ y i = 0 ∨ y i = 1 := by
  rw [quarticWellSum_eq,
    isNondegenerateCriticalPoint_sum_comp_eval_iff fun _ ↦ contDiff_quarticWell.contDiffAt]
  refine forall_congr' fun i ↦ ?_
  rw [deriv_quarticWell_eq_zero_iff, deriv_deriv_quarticWell]
  refine ⟨And.left, fun hi ↦ ⟨hi, ?_⟩⟩
  rcases hi with h | h | h <;> rw [h] <;> norm_num

/-- The Morse index of a critical point of the Euclidean quartic is the number of its zero
coordinates. -/
theorem morseIndex_quarticWellSum {y : ι → ℝ} (hy : ∀ i, y i = -1 ∨ y i = 0 ∨ y i = 1) :
    morseIndex quarticWellSum y = {i | y i = 0}.ncard := by
  rw [quarticWellSum_eq, morseIndex_sum_comp_eval fun _ ↦ contDiff_quarticWell.contDiffAt]
  congr 1
  ext i
  rw [mem_ofPred_eq, mem_ofPred_eq, deriv_deriv_quarticWell]
  rcases hy i with h | h | h <;> rw [h] <;> norm_num

theorem isIntegralCurve_quarticWellSumFlow {y : ι → ℝ} (hy : y ∈ Icc (-1) 1) :
    IsIntegralCurve (fun t ↦ quarticWellSumFlow t y) (fun _ z i ↦ -deriv quarticWell (z i)) :=
  hasDerivAt_quarticWellSumFlow hy

/-- **Uniqueness of captured trajectories** on the cube: a negative gradient trajectory of the
Euclidean quartic which stays in `[-1, 1]^ι` is the flow line through its initial point. -/
theorem eq_quarticWellSumFlow_of_isIntegralCurve {γ : ℝ → ι → ℝ}
    (hγ : IsIntegralCurve γ (fun _ z i ↦ -deriv quarticWell (z i)))
    (hmem : ∀ t, γ t ∈ Icc (-1) 1) : γ = fun t ↦ quarticWellSumFlow t (γ 0) := by
  funext t i
  have hi : IsIntegralCurve (fun t ↦ γ t i) (fun _ y ↦ -∇ quarticWell y) := fun t ↦ by
    simpa [gradient_eq_deriv'] using hasDerivAt_pi.1 (hγ t) i
  exact congrFun (eq_quarticFlow_of_isIntegralCurve hi
    fun t ↦ mem_Icc_neg_one_one_iff.1 (hmem t) i) t

end Sum

end TauCeti
