/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Fredholm
public import TauCeti.Analysis.Calculus.Morse.OneDimensional
public import Mathlib.Analysis.SpecialFunctions.Sigmoid
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The interval base of a continuation: its flow and the regularity of its scalar operators

A continuation between two Morse functions `f₀` and `f₁` on `X` can be realized as a Morse
function on the product `X × ℝ`, of the form `F(x, t) = C h(t) + f_t(x)` with the double-well
`h(t) = (t² - 1)² / 4` and a large constant `C > 0`. This file studies its base factor, the
function `C h` of the parameter `t` alone (`TauCeti.intervalBasePotential`).

Its negative gradient is the field `a(t) = C t (1 - t²)`. The critical point `0` is a local
maximum, of Morse index `1`, and `1` is a local minimum, of Morse index `0`; the Hessians there
are `-C` and `2 C`. So `0 → 1` is the source-to-sink flow of the parameter, and the endpoint index
shifts of a continuation are `1` at `t = 0` and `0` at `t = 1`. One trajectory from `0` to `1` is

`q(s) = 1 / √(1 + e^{-2 C s})` (`TauCeti.intervalBaseOrbit`),

and along every solution in `(0, 1)` the coordinate `U(t) = log t - (1 / 2) log (1 - t²)`
(`TauCeti.intervalBaseTimeCoordinate`) advances at the constant rate `C`; along `q` it is `C s`.
The time coordinate identifies `(0, 1)` with `ℝ`, with inverse `q` at unit rate.

The flow of the field on the invariant interval `[-1, 1]` is explicit:

`Φ_s(t) = t / √(t² + (1 - t²) e^{-2 C s})` (`TauCeti.intervalBaseFlow`).

It fixes the critical points, preserves `[-1, 1]`, `[0, 1]` and `(0, 1)` and the order of points,
and moves the time coordinate by `C s`. For `C > 0` every flow line in `(0, 1)` runs from `0` to
`1`. The flow of the base acts coordinatewise on the ordered-triangle base
`TauCeti.Analysis.Calculus.Morse.TriangleBase` of a composition of two continuations.

The main results verify that this base is regular, in the sense needed to glue continuation
moduli spaces over it. Along every trajectory `γ` from `0` to `1`, the linearized operator
`ξ ↦ ξ' - a'(γ) ξ` from `W^{1,2}(ℝ, ℝ)` to `L²(ℝ, ℝ)` is Fredholm of index `1`; its kernel is the
line spanned by the velocity `γ'`; it is surjective; and its formal adjoint `-d/ds - a'(γ)` is
injective. At the constant trajectories the linearized operators `d/ds - C` and `d/ds + 2 C` are
bijective.

## Main declarations

* `TauCeti.intervalBasePotential`: the function `C (t² - 1)² / 4`.
* `TauCeti.isNondegenerateCriticalPoint_intervalBasePotential_zero`,
  `TauCeti.morseIndex_intervalBasePotential_zero` and their analogues at `1`: the two critical
  points and their Morse indices.
* `TauCeti.isNondegenerateCriticalPoint_intervalBasePotential_iff` and
  `TauCeti.morseIndex_intervalBasePotential_neg_one`: the critical points are `-1`, `0` and `1`.
* `TauCeti.intervalBaseOrbit` and `TauCeti.isIntegralCurve_intervalBaseOrbit`: a trajectory from
  `0` to `1`, the flow line through `1 / √2` (`TauCeti.intervalBaseOrbit_eq_intervalBaseFlow`).
* `TauCeti.intervalBaseTimeCoordinate` and
  `TauCeti.intervalBaseTimeCoordinate_intervalBaseOrbit`: the coordinate `U` with `U(q(s)) = C s`.
* `TauCeti.bijOn_intervalBaseTimeCoordinate` and
  `TauCeti.intervalBaseOrbit_one_intervalBaseTimeCoordinate`: `U` identifies `(0, 1)` with `ℝ`.
* `TauCeti.tendsto_intervalBaseTimeCoordinate_nhdsGT_zero` and
  `TauCeti.tendsto_intervalBaseTimeCoordinate_nhdsLT_one`: `U` tends to `-∞` at `0` and to `+∞`
  at `1`.
* `TauCeti.intervalBaseFlow`, `TauCeti.isIntegralCurve_intervalBaseFlow` and
  `TauCeti.intervalBaseFlow_add`: the flow.
* `TauCeti.intervalBaseTimeCoordinate_intervalBaseFlow`, `TauCeti.strictMonoOn_intervalBaseFlow`,
  `TauCeti.tendsto_intervalBaseFlow_atTop` and `TauCeti.tendsto_intervalBaseFlow_atBot`: its
  action on the time coordinate, its monotonicity and its limits.
* `TauCeti.intervalBaseFlow_mem_Ioo`, `TauCeti.tendsto_intervalBaseFlow_atTop_sign` and
  `TauCeti.tendsto_intervalBaseFlow_atBot_ite`: invariance of `(-1, 1)` and the limits of the flow
  from every point of `[-1, 1]`.
* `TauCeti.eq_intervalBaseFlow_of_isIntegralCurve`: the negative gradient trajectories staying in
  `[-1, 1]` are the flow lines, since the field is Lipschitz there.
* `TauCeti.intervalBaseOrbit_sq_eq_sigmoid`, `TauCeti.one_sub_intervalBaseOrbit_sq` and
  `TauCeti.intervalBaseFlow_eq_intervalBaseOrbit`: the trajectory `q` through the sigmoid, and
  every flow line through `(0, 1)` as a reparametrization of `q`.
* `TauCeti.index_trajectoryOperator_intervalBasePotential`,
  `TauCeti.exists_ker_trajectoryOperator_intervalBasePotential_eq_span`,
  `TauCeti.surjective_trajectoryOperator_intervalBasePotential` and
  `TauCeti.ker_trajectoryOperator_neg_intervalBasePotential_eq_bot`: the operator along a
  trajectory from `0` to `1`.
* `TauCeti.bijective_trajectoryOperator_intervalBasePotential_zero` and
  `TauCeti.bijective_trajectoryOperator_intervalBasePotential_one`: the operators at the constant
  trajectories.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §4 (continuation maps).
* M. Schwarz, *Morse Homology*, Progress in Mathematics **111**, Birkhäuser, 1993, Chapter 2
  (the linearized trajectory operator).
-/

public section

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal Gradient Topology

namespace TauCeti

variable {C : ℝ}

/-! ### The potential -/

/-- The base potential `C h(t)` of a continuation, with `h(t) = (t² - 1)² / 4`. Its negative
gradient is `C t (1 - t²)`. -/
noncomputable def intervalBasePotential (C : ℝ) (t : ℝ) : ℝ :=
  C * ((t ^ 2 - 1) ^ 2 / 4)

theorem intervalBasePotential_apply (C t : ℝ) :
    intervalBasePotential C t = C * ((t ^ 2 - 1) ^ 2 / 4) := (rfl)

/-- The base potential is a polynomial, hence smooth. -/
theorem contDiff_intervalBasePotential (C : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (intervalBasePotential C) := by
  unfold intervalBasePotential
  fun_prop

/-- The derivative of the base potential is `C t (t² - 1)`. -/
theorem hasDerivAt_intervalBasePotential (C t : ℝ) :
    HasDerivAt (intervalBasePotential C) (C * t * (t ^ 2 - 1)) t := by
  refine (((((hasDerivAt_pow 2 t).sub_const 1).pow 2).div_const 4).const_mul C).congr_deriv ?_
  norm_num
  ring

@[simp]
theorem deriv_intervalBasePotential (C : ℝ) :
    deriv (intervalBasePotential C) = fun t ↦ C * t * (t ^ 2 - 1) :=
  funext fun t ↦ (hasDerivAt_intervalBasePotential C t).deriv

/-- The gradient of the base potential is `C t (t² - 1)`, so its negative gradient is the field
`C t (1 - t²)`. -/
@[simp]
theorem gradient_intervalBasePotential (C t : ℝ) :
    ∇ (intervalBasePotential C) t = C * t * (t ^ 2 - 1) := by
  rw [gradient_eq_deriv', deriv_intervalBasePotential]

/-- The second derivative of the base potential is `C (3 t² - 1)`: it is `-C` at `0` and `2 C` at
`1`. -/
@[simp]
theorem iteratedDeriv_two_intervalBasePotential (C t : ℝ) :
    iteratedDeriv 2 (intervalBasePotential C) t = C * (3 * t ^ 2 - 1) := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, deriv_intervalBasePotential]
  refine (((hasDerivAt_id t).const_mul C).mul ((hasDerivAt_pow 2 t).sub_const 1)).congr_deriv
    ?_ |>.deriv
  simp only [id, Nat.cast_ofNat]
  ring

/-- The Hessian operator of the base potential at `t` is multiplication by `C (3 t² - 1)`. -/
@[simp]
theorem hessianOperator_intervalBasePotential (C t : ℝ) :
    hessianOperator (intervalBasePotential C) t =
      (C * (3 * t ^ 2 - 1)) • ContinuousLinearMap.id ℝ ℝ := by
  rw [hessianOperator_real, iteratedDeriv_two_intervalBasePotential]

/-! ### The critical points -/

/-- For `C ≠ 0`, `0` is a nondegenerate critical point of the base potential, with Hessian `-C`. -/
theorem isNondegenerateCriticalPoint_intervalBasePotential_zero (hC : C ≠ 0) :
    IsNondegenerateCriticalPoint (intervalBasePotential C) 0 := by
  rw [isNondegenerateCriticalPoint_real_iff (contDiff_intervalBasePotential C).contDiffAt,
    iteratedDeriv_two_intervalBasePotential, deriv_intervalBasePotential]
  simpa using hC

/-- For `C ≠ 0`, `1` is a nondegenerate critical point of the base potential, with Hessian `2 C`.
-/
theorem isNondegenerateCriticalPoint_intervalBasePotential_one (hC : C ≠ 0) :
    IsNondegenerateCriticalPoint (intervalBasePotential C) 1 := by
  rw [isNondegenerateCriticalPoint_real_iff (contDiff_intervalBasePotential C).contDiffAt,
    iteratedDeriv_two_intervalBasePotential, deriv_intervalBasePotential]
  norm_num [hC]

/-- For `C > 0` the critical point `0` of the base potential is a local maximum: its Morse index
is `1`. -/
@[simp]
theorem morseIndex_intervalBasePotential_zero (hC : 0 < C) :
    morseIndex (intervalBasePotential C) 0 = 1 :=
  morseIndex_real_of_neg
    (by rw [iteratedDeriv_two_intervalBasePotential]; linarith)

/-- For `C > 0` the critical point `1` of the base potential is a local minimum: its Morse index
is `0`. -/
@[simp]
theorem morseIndex_intervalBasePotential_one (hC : 0 < C) :
    morseIndex (intervalBasePotential C) 1 = 0 :=
  morseIndex_real_of_pos
    (by rw [iteratedDeriv_two_intervalBasePotential]; linarith)

/-- **The base potential is a Morse function**: for `C ≠ 0` its critical points are `-1`, `0` and
`1`, all nondegenerate. -/
@[simp]
theorem isNondegenerateCriticalPoint_intervalBasePotential_iff (hC : C ≠ 0) {t : ℝ} :
    IsNondegenerateCriticalPoint (intervalBasePotential C) t ↔ t = -1 ∨ t = 0 ∨ t = 1 := by
  rw [isNondegenerateCriticalPoint_real_iff (contDiff_intervalBasePotential C).contDiffAt,
    iteratedDeriv_two_intervalBasePotential, deriv_intervalBasePotential]
  beta_reduce
  have hfac : C * t * (t ^ 2 - 1) = C * (t * (t + 1) * (t - 1)) := by ring
  rw [hfac]
  simp only [mul_eq_zero, hC, false_or, add_eq_zero_iff_eq_neg, sub_eq_zero]
  refine ⟨fun h ↦ by tauto, fun h ↦ ⟨by tauto, ?_⟩⟩
  rcases h with rfl | rfl | rfl <;> norm_num [hC]

/-- For `C > 0` the critical point `-1` of the base potential is a local minimum: its Morse index
is `0`. -/
@[simp]
theorem morseIndex_intervalBasePotential_neg_one (hC : 0 < C) :
    morseIndex (intervalBasePotential C) (-1) = 0 :=
  morseIndex_real_of_pos (by rw [iteratedDeriv_two_intervalBasePotential]; norm_num; linarith)

/-! ### The flow of the base -/

/-- The flow `Φ_s(t) = t / √(t² + (1 - t²) e^{-2 C s})` of the negative gradient field
`C t (1 - t²)` of the base potential, on the invariant interval `[-1, 1]`
(`TauCeti.isIntegralCurve_intervalBaseFlow`). Only its values on `[-1, 1]` are meaningful: outside
that interval the solutions of the field are not defined for all times. -/
noncomputable def intervalBaseFlow (C s t : ℝ) : ℝ :=
  t / √(t ^ 2 + (1 - t ^ 2) * Real.exp (-(2 * C * s)))

theorem intervalBaseFlow_apply (C s t : ℝ) :
    intervalBaseFlow C s t = t / √(t ^ 2 + (1 - t ^ 2) * Real.exp (-(2 * C * s))) := (rfl)

/-- At time `0` the flow is the identity. -/
@[simp]
theorem intervalBaseFlow_zero (C t : ℝ) : intervalBaseFlow C 0 t = t := by
  simp [intervalBaseFlow]

/-- The critical point `0` is fixed by the flow. -/
@[simp]
theorem intervalBaseFlow_apply_zero (C s : ℝ) : intervalBaseFlow C s 0 = 0 := by
  simp [intervalBaseFlow]

/-- The critical point `1` is fixed by the flow. -/
@[simp]
theorem intervalBaseFlow_apply_one (C s : ℝ) : intervalBaseFlow C s 1 = 1 := by
  simp [intervalBaseFlow]

private theorem intervalBaseFlow_denom_pos (C s : ℝ) {t : ℝ} (ht : t ∈ Icc (-1) 1) :
    0 < t ^ 2 + (1 - t ^ 2) * Real.exp (-(2 * C * s)) := by
  have he := Real.exp_pos (-(2 * C * s))
  have h1 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
  rcases (sq_nonneg t).eq_or_lt with h | h
  · rw [← h]
    simpa using he
  · nlinarith [mul_nonneg (sub_nonneg.2 h1) he.le]

/-- The square of the flow is `t² / (t² + (1 - t²) e^{-2 C s})`. -/
theorem intervalBaseFlow_sq (C s : ℝ) {t : ℝ} (ht : t ∈ Icc (-1) 1) :
    intervalBaseFlow C s t ^ 2 = t ^ 2 / (t ^ 2 + (1 - t ^ 2) * Real.exp (-(2 * C * s))) := by
  rw [intervalBaseFlow, div_pow, Real.sq_sqrt (intervalBaseFlow_denom_pos C s ht).le]

/-- The flow preserves `[-1, 1]`. -/
theorem intervalBaseFlow_mem_Icc (C s : ℝ) {t : ℝ} (ht : t ∈ Icc (-1) 1) :
    intervalBaseFlow C s t ∈ Icc (-1) 1 := by
  have hD := intervalBaseFlow_denom_pos C s ht
  have h1 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
  have hsq : intervalBaseFlow C s t ^ 2 ≤ 1 := by
    rw [intervalBaseFlow_sq C s ht, div_le_one hD]
    nlinarith [mul_nonneg (sub_nonneg.2 h1) (Real.exp_pos (-(2 * C * s))).le]
  exact abs_le.1 (sq_le_one_iff_abs_le_one _ |>.1 hsq)

/-- The flow preserves `[0, 1]`. -/
theorem intervalBaseFlow_mem_Icc_zero_one (C s : ℝ) {t : ℝ} (ht : t ∈ Icc 0 1) :
    intervalBaseFlow C s t ∈ Icc 0 1 :=
  ⟨div_nonneg ht.1 (Real.sqrt_nonneg _),
    (intervalBaseFlow_mem_Icc C s ⟨by linarith [ht.1], ht.2⟩).2⟩

/-- The flow preserves `(0, 1)`. -/
theorem intervalBaseFlow_mem_Ioo_zero_one (C s : ℝ) {t : ℝ} (ht : t ∈ Ioo 0 1) :
    intervalBaseFlow C s t ∈ Ioo 0 1 := by
  have ht' : t ∈ Icc (-1) 1 := ⟨by linarith [ht.1], ht.2.le⟩
  have hD := intervalBaseFlow_denom_pos C s ht'
  have hpos : 0 < intervalBaseFlow C s t := div_pos ht.1 (Real.sqrt_pos.2 hD)
  have hsq : intervalBaseFlow C s t ^ 2 < 1 := by
    rw [intervalBaseFlow_sq C s ht', div_lt_one hD]
    nlinarith [mul_pos (by nlinarith [ht.1, ht.2] : 0 < 1 - t ^ 2) (Real.exp_pos (-(2 * C * s)))]
  exact ⟨hpos, by nlinarith⟩

/-- **The flow property.** -/
theorem intervalBaseFlow_add (C s r : ℝ) {t : ℝ} (ht : t ∈ Icc (-1) 1) :
    intervalBaseFlow C (s + r) t = intervalBaseFlow C s (intervalBaseFlow C r t) := by
  have hr := intervalBaseFlow_denom_pos C r ht
  have key : intervalBaseFlow C r t ^ 2 + (1 - intervalBaseFlow C r t ^ 2) *
      Real.exp (-(2 * C * s)) = (t ^ 2 + (1 - t ^ 2) * Real.exp (-(2 * C * (s + r)))) /
        (t ^ 2 + (1 - t ^ 2) * Real.exp (-(2 * C * r))) := by
    rw [intervalBaseFlow_sq C r ht, show -(2 * C * (s + r)) = -(2 * C * s) + -(2 * C * r) by ring,
      Real.exp_add]
    field_simp
    ring
  have hr' : √(t ^ 2 + (1 - t ^ 2) * Real.exp (-(2 * C * r))) ≠ 0 := (Real.sqrt_pos.2 hr).ne'
  rw [intervalBaseFlow_apply C s, key, Real.sqrt_div' _ hr.le, intervalBaseFlow_apply C r,
    intervalBaseFlow_apply]
  field_simp

/-- The flow solves `Φ' = C Φ (1 - Φ²)`. -/
theorem hasDerivAt_intervalBaseFlow (C s : ℝ) {t : ℝ} (ht : t ∈ Icc (-1) 1) :
    HasDerivAt (fun s ↦ intervalBaseFlow C s t)
      (C * intervalBaseFlow C s t * (1 - intervalBaseFlow C s t ^ 2)) s := by
  have hD := intervalBaseFlow_denom_pos C s ht
  have hsq : 0 < √(t ^ 2 + (1 - t ^ 2) * Real.exp (-(2 * C * s))) := Real.sqrt_pos.2 hD
  have hexp : HasDerivAt (fun s ↦ t ^ 2 + (1 - t ^ 2) * Real.exp (-(2 * C * s)))
      ((1 - t ^ 2) * (Real.exp (-(2 * C * s)) * -(2 * C))) s := by
    have := (((hasDerivAt_id s).const_mul (2 * C)).neg.exp.const_mul (1 - t ^ 2)).const_add (t ^ 2)
    simpa using this
  refine ((hasDerivAt_const s t).div (hexp.sqrt hD.ne') hsq.ne').congr_deriv ?_
  rw [intervalBaseFlow_sq C s ht, intervalBaseFlow]
  field_simp
  rw [Real.sq_sqrt hD.le]
  ring

/-- The flow lines are negative gradient trajectories of the base potential. -/
theorem isIntegralCurve_intervalBaseFlow (C : ℝ) {t : ℝ} (ht : t ∈ Icc (-1) 1) :
    IsIntegralCurve (fun s ↦ intervalBaseFlow C s t)
      (fun _ t ↦ -∇ (intervalBasePotential C) t) := by
  intro s
  refine (hasDerivAt_intervalBaseFlow C s ht).congr_deriv ?_
  dsimp only
  rw [gradient_intervalBasePotential]
  ring

/-- The flow is odd. -/
theorem intervalBaseFlow_neg (C s t : ℝ) : intervalBaseFlow C s (-t) = -intervalBaseFlow C s t := by
  rw [intervalBaseFlow, intervalBaseFlow, neg_sq, neg_div]

/-- The critical point `-1` is fixed by the flow. -/
@[simp]
theorem intervalBaseFlow_apply_neg_one (C s : ℝ) : intervalBaseFlow C s (-1) = -1 := by
  rw [intervalBaseFlow_neg, intervalBaseFlow_apply_one]

/-- The negative gradient field of the base potential is `2 |C|`-Lipschitz on `[-1, 1]`: the
difference quotient of `C t (1 - t²)` is `C (1 - (a² + a b + b²))`. -/
theorem lipschitzOnWith_neg_gradient_intervalBasePotential (C : ℝ) :
    LipschitzOnWith (2 * ‖C‖₊) (fun t ↦ -∇ (intervalBasePotential C) t) (Icc (-1) 1) := by
  refine LipschitzOnWith.of_dist_le_mul fun a ha b hb ↦ ?_
  rw [mem_Icc] at ha hb
  have h : |1 - (a ^ 2 + a * b + b ^ 2)| ≤ 2 := by
    rw [abs_le]
    constructor <;> nlinarith
  simp only [gradient_intervalBasePotential, dist_eq_norm, Real.norm_eq_abs, NNReal.coe_mul,
    NNReal.coe_ofNat, coe_nnnorm]
  have hdiff : -(C * a * (a ^ 2 - 1)) - -(C * b * (b ^ 2 - 1)) =
      C * (a - b) * (1 - (a ^ 2 + a * b + b ^ 2)) := by ring
  rw [hdiff, abs_mul, abs_mul]
  nlinarith [mul_nonneg (abs_nonneg C) (abs_nonneg (a - b))]

/-- **Uniqueness of captured trajectories**: a negative gradient trajectory of the base potential
which stays in `[-1, 1]` is the flow line through its initial point. -/
theorem eq_intervalBaseFlow_of_isIntegralCurve {γ : ℝ → ℝ}
    (hγ : IsIntegralCurve γ (fun _ t ↦ -∇ (intervalBasePotential C) t))
    (hmem : ∀ s, γ s ∈ Icc (-1) 1) : γ = fun s ↦ intervalBaseFlow C s (γ 0) :=
  ODE_solution_unique_univ (v := fun _ t ↦ -∇ (intervalBasePotential C) t)
    (s := fun _ ↦ Icc (-1) 1) (fun _ ↦ lipschitzOnWith_neg_gradient_intervalBasePotential C)
    (fun s ↦ ⟨hγ s, hmem s⟩)
    (fun s ↦ ⟨isIntegralCurve_intervalBaseFlow C (hmem 0) s, intervalBaseFlow_mem_Icc C s (hmem 0)⟩)
    (t₀ := 0) (by simp)

/-- For `C > 0`, the flow line through a point of `(0, 1]` tends to the minimum `1` at `+∞`. -/
theorem tendsto_intervalBaseFlow_atTop (hC : 0 < C) {t : ℝ} (ht : t ∈ Ioc 0 1) :
    Tendsto (fun s ↦ intervalBaseFlow C s t) atTop (𝓝 1) := by
  have hexp : Tendsto (fun s ↦ Real.exp (-(2 * C * s))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop (by positivity)))
  have hD : Tendsto (fun s ↦ √(t ^ 2 + (1 - t ^ 2) * Real.exp (-(2 * C * s)))) atTop
      (𝓝 √(t ^ 2 + (1 - t ^ 2) * 0)) :=
    (tendsto_const_nhds.add (tendsto_const_nhds.mul hexp)).sqrt
  rw [mul_zero, add_zero, Real.sqrt_sq ht.1.le] at hD
  have h := (tendsto_const_nhds (x := t)).div hD ht.1.ne'
  rw [div_self ht.1.ne'] at h
  exact h.congr fun s ↦ by simp [intervalBaseFlow_apply]

/-- For `C > 0`, the flow line through a point of `(-1, 1)` tends to the maximum `0` at `-∞`. -/
theorem tendsto_intervalBaseFlow_atBot (hC : 0 < C) {t : ℝ} (ht : t ∈ Ioo (-1) 1) :
    Tendsto (fun s ↦ intervalBaseFlow C s t) atBot (𝓝 0) := by
  have h1 : 0 < 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
  have hexp : Tendsto (fun s ↦ Real.exp (-(2 * C * s))) atBot atTop :=
    Real.tendsto_exp_atTop.comp
      (tendsto_neg_atBot_atTop.comp (tendsto_id.const_mul_atBot (by positivity)))
  have hD : Tendsto (fun s ↦ t ^ 2 + (1 - t ^ 2) * Real.exp (-(2 * C * s))) atBot atTop :=
    tendsto_atTop_add_const_left _ _ (hexp.const_mul_atTop h1)
  simp only [intervalBaseFlow_apply]
  exact tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp hD)

/-- **Forward limit**: for `C > 0`, as `s → ∞` the flow from `t` tends to the sign of `t`, the
minimum `±1` on its side of `0`, or `0` if `t = 0`. The closed formula has this limit for every
`t`, although it is a trajectory only for `t ∈ [-1, 1]`. -/
theorem tendsto_intervalBaseFlow_atTop_sign (hC : 0 < C) (t : ℝ) :
    Tendsto (fun s ↦ intervalBaseFlow C s t) atTop (𝓝 (SignType.sign t)) := by
  rcases eq_or_ne t 0 with rfl | ht0
  · simp
  simp only [intervalBaseFlow_apply]
  have hexp : Tendsto (fun s ↦ Real.exp (-(2 * C * s))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop (by positivity)))
  have hD := ((tendsto_const_nhds (x := t ^ 2)).add (hexp.const_mul (1 - t ^ 2))).sqrt
  rw [mul_zero, add_zero, Real.sqrt_sq_eq_abs] at hD
  have h := (tendsto_const_nhds (x := t)).div hD (abs_pos.2 ht0).ne'
  have hsign : (SignType.sign t : ℝ) = t / |t| := by
    rw [eq_div_iff (abs_pos.2 ht0).ne', sign_mul_abs]
  rwa [hsign]

/-- **Backward limit**: for `C > 0`, the backward limit of the flow from `t ∈ [-1, 1]` is `0` if
`t ∈ (-1, 1)`, and `t` itself if `t = ±1`, where the flow is stationary. -/
theorem tendsto_intervalBaseFlow_atBot_ite (hC : 0 < C) {t : ℝ} (ht : t ∈ Icc (-1) 1) :
    Tendsto (fun s ↦ intervalBaseFlow C s t) atBot (𝓝 (if t ∈ Ioo (-1) 1 then 0 else t)) := by
  split_ifs with ht'
  · exact tendsto_intervalBaseFlow_atBot hC ht'
  · have h : t ∈ Icc (-1) 1 \ Ioo (-1) 1 := ⟨ht, ht'⟩
    rw [Icc_sdiff_Ioo_same (by norm_num)] at h
    rcases h with rfl | rfl <;> simp

/-! ### A trajectory from `0` to `1` and the time coordinate -/

/-- The trajectory `q(s) = 1 / √(1 + e^{-2 C s})` of the negative gradient field `C t (1 - t²)` of
the base potential. For `C > 0` it runs from `0` at `-∞` to `1` at `+∞`. -/
noncomputable def intervalBaseOrbit (C s : ℝ) : ℝ :=
  (√(1 + Real.exp (-(2 * C * s))))⁻¹

theorem intervalBaseOrbit_apply (C s : ℝ) :
    intervalBaseOrbit C s = (√(1 + Real.exp (-(2 * C * s))))⁻¹ := (rfl)

/-- The square of the trajectory `q` is `1 / (1 + e^{-2 C s})`. -/
theorem intervalBaseOrbit_sq (C s : ℝ) :
    intervalBaseOrbit C s ^ 2 = (1 + Real.exp (-(2 * C * s)))⁻¹ := by
  rw [intervalBaseOrbit, inv_pow, Real.sq_sqrt (by positivity)]

/-- The square of the trajectory `q` is the sigmoid `σ (2 C s)`: at `C = 1` it leaves `0` at
rate `1`, and the time coordinate is half the logit of `q²`. -/
theorem intervalBaseOrbit_sq_eq_sigmoid (C s : ℝ) :
    intervalBaseOrbit C s ^ 2 = Real.sigmoid (2 * C * s) := by
  rw [intervalBaseOrbit_sq, Real.sigmoid_def]

/-- One minus the square of the trajectory `q` is the sigmoid `σ (-2 C s)`: at `C = 1` it
approaches `1` at rate `2`. -/
theorem one_sub_intervalBaseOrbit_sq (C s : ℝ) :
    1 - intervalBaseOrbit C s ^ 2 = Real.sigmoid (-(2 * C * s)) := by
  rw [intervalBaseOrbit_sq_eq_sigmoid, Real.sigmoid_neg]

private theorem inv_sqrt_two_mem_Ioo : (√2)⁻¹ ∈ Ioo (0 : ℝ) 1 :=
  ⟨by positivity, inv_lt_one_of_one_lt₀ Real.one_lt_sqrt_two⟩

private theorem inv_sqrt_two_mem_Icc : (√2)⁻¹ ∈ Icc (-1 : ℝ) 1 :=
  ⟨by linarith [inv_sqrt_two_mem_Ioo.1], inv_sqrt_two_mem_Ioo.2.le⟩

/-- The trajectory `q` is the flow line through `q(0) = 1 / √2`. -/
theorem intervalBaseOrbit_eq_intervalBaseFlow (C s : ℝ) :
    intervalBaseOrbit C s = intervalBaseFlow C s (√2)⁻¹ := by
  have h2 : (√2)⁻¹ ^ 2 = (1 / 2 : ℝ) := by rw [inv_pow, Real.sq_sqrt zero_le_two, one_div]
  rw [intervalBaseOrbit_apply, intervalBaseFlow_apply, h2,
    show 1 / 2 + (1 - 1 / 2) * Real.exp (-(2 * C * s)) = (1 + Real.exp (-(2 * C * s))) / 2 by ring,
    Real.sqrt_div' _ zero_le_two]
  field_simp

/-- The flow moves the trajectory `q` along itself: `Φ_s(q(r)) = q(s + r)`. -/
@[simp]
theorem intervalBaseFlow_intervalBaseOrbit (C s r : ℝ) :
    intervalBaseFlow C s (intervalBaseOrbit C r) = intervalBaseOrbit C (s + r) := by
  rw [intervalBaseOrbit_eq_intervalBaseFlow, intervalBaseOrbit_eq_intervalBaseFlow,
    intervalBaseFlow_add C s r inv_sqrt_two_mem_Icc]

/-- The trajectory `q` takes values in `(0, 1)`. -/
theorem intervalBaseOrbit_mem_Ioo (C s : ℝ) : intervalBaseOrbit C s ∈ Ioo 0 1 := by
  rw [intervalBaseOrbit_eq_intervalBaseFlow]
  exact intervalBaseFlow_mem_Ioo_zero_one C s inv_sqrt_two_mem_Ioo

/-- The trajectory `q` solves `q' = C q (1 - q²)`. -/
theorem hasDerivAt_intervalBaseOrbit (C s : ℝ) :
    HasDerivAt (intervalBaseOrbit C)
      (C * intervalBaseOrbit C s * (1 - intervalBaseOrbit C s ^ 2)) s := by
  rw [funext (intervalBaseOrbit_eq_intervalBaseFlow C)]
  exact hasDerivAt_intervalBaseFlow C s inv_sqrt_two_mem_Icc

theorem tendsto_intervalBaseOrbit_atBot (hC : 0 < C) :
    Tendsto (intervalBaseOrbit C) atBot (𝓝 0) := by
  rw [funext (intervalBaseOrbit_eq_intervalBaseFlow C)]
  exact tendsto_intervalBaseFlow_atBot hC (Ioo_subset_Ioo_left (by norm_num) inv_sqrt_two_mem_Ioo)

theorem tendsto_intervalBaseOrbit_atTop (hC : 0 < C) :
    Tendsto (intervalBaseOrbit C) atTop (𝓝 1) := by
  rw [funext (intervalBaseOrbit_eq_intervalBaseFlow C)]
  exact tendsto_intervalBaseFlow_atTop hC (Ioo_subset_Ioc_self inv_sqrt_two_mem_Ioo)

/-- The trajectory `q` is a negative gradient trajectory of the base potential. -/
theorem isIntegralCurve_intervalBaseOrbit (C : ℝ) :
    IsIntegralCurve (intervalBaseOrbit C) (fun _ t ↦ -∇ (intervalBasePotential C) t) := by
  rw [funext (intervalBaseOrbit_eq_intervalBaseFlow C)]
  exact isIntegralCurve_intervalBaseFlow C inv_sqrt_two_mem_Icc

/-- The time coordinate `U(t) = log t - (1 / 2) log (1 - t²)` of the base flow on `(0, 1)`. Along
every solution of `t' = C t (1 - t²)` in `(0, 1)` it advances at rate `C`
(`HasDerivAt.intervalBaseTimeCoordinate_comp`). -/
noncomputable def intervalBaseTimeCoordinate (t : ℝ) : ℝ :=
  Real.log t - Real.log (1 - t ^ 2) / 2

theorem intervalBaseTimeCoordinate_apply (t : ℝ) :
    intervalBaseTimeCoordinate t = Real.log t - Real.log (1 - t ^ 2) / 2 := (rfl)

/-- On `(0, 1)` the derivative of the time coordinate is `1 / (t (1 - t²))`. -/
theorem hasDerivAt_intervalBaseTimeCoordinate {t : ℝ} (ht : t ∈ Ioo 0 1) :
    HasDerivAt intervalBaseTimeCoordinate (t * (1 - t ^ 2))⁻¹ t := by
  have h1 : 0 < 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
  refine ((Real.hasDerivAt_log ht.1.ne').sub
    ((((hasDerivAt_pow 2 t).const_sub 1).log h1.ne').div_const 2)).congr_deriv ?_
  field_simp [ht.1.ne', h1.ne']
  ring

/-- **The time coordinate advances at rate `C`.** Along a solution of `x' = C x (1 - x²)` taking
values in `(0, 1)`, the derivative of `U ∘ x` is `C`. -/
theorem _root_.HasDerivAt.intervalBaseTimeCoordinate_comp {x : ℝ → ℝ} {s : ℝ}
    (hx : HasDerivAt x (C * x s * (1 - x s ^ 2)) s) (hxs : x s ∈ Ioo 0 1) :
    HasDerivAt (fun s ↦ intervalBaseTimeCoordinate (x s)) C s := by
  have h1 : 0 < 1 - x s ^ 2 := by nlinarith [hxs.1, hxs.2]
  refine ((hasDerivAt_intervalBaseTimeCoordinate hxs).comp s hx).congr_deriv ?_
  field_simp [hxs.1.ne', h1.ne']

/-- **The time coordinate advances at rate `C` along the flow.** -/
@[simp]
theorem intervalBaseTimeCoordinate_intervalBaseFlow (C s : ℝ) {t : ℝ} (ht : t ∈ Ioo 0 1) :
    intervalBaseTimeCoordinate (intervalBaseFlow C s t) = intervalBaseTimeCoordinate t + C * s := by
  have ht' : t ∈ Icc (-1) 1 := ⟨by linarith [ht.1], ht.2.le⟩
  have hD := intervalBaseFlow_denom_pos C s ht'
  have h1 : 0 < 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
  have hsub : 1 - intervalBaseFlow C s t ^ 2 =
      (1 - t ^ 2) * Real.exp (-(2 * C * s)) / (t ^ 2 + (1 - t ^ 2) * Real.exp (-(2 * C * s))) := by
    rw [intervalBaseFlow_sq C s ht']
    field_simp
    ring
  rw [intervalBaseTimeCoordinate, hsub, intervalBaseFlow, intervalBaseTimeCoordinate,
    Real.log_div ht.1.ne' (Real.sqrt_pos.2 hD).ne', Real.log_sqrt hD.le,
    Real.log_div (mul_pos h1 (Real.exp_pos _)).ne' hD.ne', Real.log_mul h1.ne' (Real.exp_pos _).ne',
    Real.log_exp]
  ring

private theorem intervalBaseTimeCoordinate_inv_sqrt_two :
    intervalBaseTimeCoordinate (√2)⁻¹ = 0 := by
  rw [intervalBaseTimeCoordinate, inv_pow, Real.sq_sqrt zero_le_two,
    show (1 : ℝ) - 2⁻¹ = 2⁻¹ by norm_num, Real.log_inv, Real.log_inv, Real.log_sqrt zero_le_two]
  ring

/-- Along the trajectory `q` the time coordinate is exactly `C s`. -/
@[simp]
theorem intervalBaseTimeCoordinate_intervalBaseOrbit (C s : ℝ) :
    intervalBaseTimeCoordinate (intervalBaseOrbit C s) = C * s := by
  rw [intervalBaseOrbit_eq_intervalBaseFlow,
    intervalBaseTimeCoordinate_intervalBaseFlow C s inv_sqrt_two_mem_Ioo,
    intervalBaseTimeCoordinate_inv_sqrt_two, zero_add]

/-- The time coordinate is strictly increasing on `(0, 1)`. -/
theorem strictMonoOn_intervalBaseTimeCoordinate :
    StrictMonoOn intervalBaseTimeCoordinate (Ioo 0 1) := by
  intro x hx y hy hxy
  have h1 : 0 < 1 - y ^ 2 := by nlinarith [hy.1, hy.2]
  have hlog := Real.log_lt_log hx.1 hxy
  have hlog' := Real.log_lt_log h1 (by nlinarith [hx.1] : 1 - y ^ 2 < 1 - x ^ 2)
  rw [intervalBaseTimeCoordinate, intervalBaseTimeCoordinate]
  linarith

/-- The trajectory `q` at unit rate inverts the time coordinate on `(0, 1)`. -/
@[simp]
theorem intervalBaseOrbit_one_intervalBaseTimeCoordinate {t : ℝ} (ht : t ∈ Ioo 0 1) :
    intervalBaseOrbit 1 (intervalBaseTimeCoordinate t) = t :=
  strictMonoOn_intervalBaseTimeCoordinate.injOn (intervalBaseOrbit_mem_Ioo _ _) ht
    (by rw [intervalBaseTimeCoordinate_intervalBaseOrbit, one_mul])

/-- **The time coordinate identifies `(0, 1)` with `ℝ`.** -/
theorem bijOn_intervalBaseTimeCoordinate : BijOn intervalBaseTimeCoordinate (Ioo 0 1) univ :=
  ⟨mapsTo_univ _ _, strictMonoOn_intervalBaseTimeCoordinate.injOn, fun y _ ↦
    ⟨intervalBaseOrbit 1 y, intervalBaseOrbit_mem_Ioo 1 y, by
      rw [intervalBaseTimeCoordinate_intervalBaseOrbit, one_mul]⟩⟩

/-- Points of `(0, 1)` whose time coordinate tends to `-∞` tend to `0`. -/
theorem tendsto_nhds_zero_of_tendsto_intervalBaseTimeCoordinate_atBot {α : Type*} {l : Filter α}
    {x : α → ℝ} (hx : ∀ᶠ i in l, x i ∈ Ioo 0 1)
    (h : Tendsto (fun i ↦ intervalBaseTimeCoordinate (x i)) l atBot) : Tendsto x l (𝓝 0) :=
  ((tendsto_intervalBaseOrbit_atBot one_pos).comp h).congr' <| hx.mono fun _ hi ↦
    intervalBaseOrbit_one_intervalBaseTimeCoordinate hi

/-- Points of `(0, 1)` whose time coordinate tends to `+∞` tend to `1`. -/
theorem tendsto_nhds_one_of_tendsto_intervalBaseTimeCoordinate_atTop {α : Type*} {l : Filter α}
    {x : α → ℝ} (hx : ∀ᶠ i in l, x i ∈ Ioo 0 1)
    (h : Tendsto (fun i ↦ intervalBaseTimeCoordinate (x i)) l atTop) : Tendsto x l (𝓝 1) :=
  ((tendsto_intervalBaseOrbit_atTop one_pos).comp h).congr' <| hx.mono fun _ hi ↦
    intervalBaseOrbit_one_intervalBaseTimeCoordinate hi

/-- The time coordinate tends to `-∞` as `t → 0` from above. -/
theorem tendsto_intervalBaseTimeCoordinate_nhdsGT_zero :
    Tendsto intervalBaseTimeCoordinate (𝓝[>] 0) atBot := by
  have hc : ContinuousAt (fun t : ℝ ↦ Real.log (1 - t ^ 2) / 2) 0 :=
    ((Real.continuousAt_log (by norm_num)).comp (by fun_prop)).div_const 2
  have h : Tendsto (fun t : ℝ ↦ -(Real.log (1 - t ^ 2) / 2)) (𝓝[>] 0)
      (𝓝 (-(Real.log (1 - 0 ^ 2) / 2))) :=
    (hc.tendsto.mono_left nhdsWithin_le_nhds).neg
  exact (Real.tendsto_log_nhdsGT_zero.atBot_add h).congr fun t ↦ by
    simp [intervalBaseTimeCoordinate, sub_eq_add_neg]

/-- The time coordinate tends to `+∞` as `t → 1` from below. -/
theorem tendsto_intervalBaseTimeCoordinate_nhdsLT_one :
    Tendsto intervalBaseTimeCoordinate (𝓝[<] 1) atTop := by
  have hq : Tendsto (fun t : ℝ ↦ 1 - t ^ 2) (𝓝[<] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun t : ℝ ↦ 1 - t ^ 2) (𝓝 1) (𝓝 (1 - 1 ^ 2)) :=
        (continuous_const.sub (continuous_pow 2)).tendsto 1
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with t ht
      exact mem_Ioi.2 (by nlinarith [ht.1, ht.2])
  have h₁ : Tendsto (fun t : ℝ ↦ -(Real.log (1 - t ^ 2) / 2)) (𝓝[<] 1) atTop :=
    tendsto_neg_atBot_atTop.comp ((Real.tendsto_log_nhdsGT_zero.comp hq).atBot_div_const two_pos)
  have h₀ : Tendsto Real.log (𝓝[<] 1) (𝓝 (Real.log 1)) :=
    ((Real.continuousAt_log one_ne_zero).tendsto).mono_left nhdsWithin_le_nhds
  exact (h₀.add_atTop h₁).congr fun t ↦ by simp [intervalBaseTimeCoordinate, sub_eq_add_neg]

/-! ### The flow and the time coordinate -/

private theorem strictMonoOn_intervalBaseFlow_Icc_zero_one (C s : ℝ) :
    StrictMonoOn (intervalBaseFlow C s) (Icc 0 1) := by
  intro x hx y hy hxy
  rcases hx.1.eq_or_lt with rfl | hx0
  · rw [intervalBaseFlow_apply_zero]
    have hy' : y ∈ Icc (-1) 1 := ⟨by linarith [hy.1], hy.2⟩
    exact div_pos hxy (Real.sqrt_pos.2 (intervalBaseFlow_denom_pos C s hy'))
  rcases hy.2.eq_or_lt with rfl | hy1
  · rw [intervalBaseFlow_apply_one]
    exact (intervalBaseFlow_mem_Ioo_zero_one C s ⟨hx0, hxy⟩).2
  have hx' : x ∈ Ioo 0 1 := ⟨hx0, hxy.trans hy1⟩
  have hy' : y ∈ Ioo 0 1 := ⟨hx0.trans hxy, hy1⟩
  refine (strictMonoOn_intervalBaseTimeCoordinate.lt_iff_lt
    (intervalBaseFlow_mem_Ioo_zero_one C s hx') (intervalBaseFlow_mem_Ioo_zero_one C s hy')).1 ?_
  rw [intervalBaseTimeCoordinate_intervalBaseFlow C s hx',
    intervalBaseTimeCoordinate_intervalBaseFlow C s hy', add_lt_add_iff_right]
  exact strictMonoOn_intervalBaseTimeCoordinate hx' hy' hxy

/-- The flow is strictly increasing on `[-1, 1]`: it preserves the order of points. -/
theorem strictMonoOn_intervalBaseFlow (C s : ℝ) :
    StrictMonoOn (intervalBaseFlow C s) (Icc (-1) 1) := by
  have h₀ := strictMonoOn_intervalBaseFlow_Icc_zero_one C s
  intro x hx y hy hxy
  rcases le_or_gt 0 x with hx0 | hx0
  · exact h₀ ⟨hx0, hx.2⟩ ⟨hx0.trans hxy.le, hy.2⟩ hxy
  rcases le_or_gt 0 y with hy0 | hy0
  -- Opposite signs: the flow keeps the sign of a point.
  · have hx' : intervalBaseFlow C s x < 0 :=
      div_neg_of_neg_of_pos hx0 (Real.sqrt_pos.2 (intervalBaseFlow_denom_pos C s hx))
    have hy' : 0 ≤ intervalBaseFlow C s y := div_nonneg hy0 (Real.sqrt_nonneg _)
    linarith
  -- Both negative: reflect to `[0, 1]`, where the flow is odd.
  · have h := h₀ ⟨neg_nonneg.2 hy0.le, by linarith [hy.1]⟩ ⟨neg_nonneg.2 hx0.le, by linarith [hx.1]⟩
      (neg_lt_neg hxy)
    rw [intervalBaseFlow_neg, intervalBaseFlow_neg] at h
    linarith

/-- On `[-1, 1]` the flow vanishes only at the critical point `0`. -/
@[simp]
theorem intervalBaseFlow_eq_zero_iff (C s : ℝ) {t : ℝ} (ht : t ∈ Icc (-1) 1) :
    intervalBaseFlow C s t = 0 ↔ t = 0 := by
  rw [intervalBaseFlow, div_eq_zero_iff,
    or_iff_left (Real.sqrt_pos.2 (intervalBaseFlow_denom_pos C s ht)).ne']

/-- On `[-1, 1]` the flow takes the value `1` only at the critical point `1`. -/
@[simp]
theorem intervalBaseFlow_eq_one_iff (C s : ℝ) {t : ℝ} (ht : t ∈ Icc (-1) 1) :
    intervalBaseFlow C s t = 1 ↔ t = 1 := by
  conv_lhs => rw [← intervalBaseFlow_apply_one C s]
  exact (strictMonoOn_intervalBaseFlow C s).injOn.eq_iff ht ⟨by norm_num, le_rfl⟩

/-- The flow preserves `(-1, 1)`. -/
theorem intervalBaseFlow_mem_Ioo (C s : ℝ) {t : ℝ} (ht : t ∈ Ioo (-1) 1) :
    intervalBaseFlow C s t ∈ Ioo (-1) 1 := by
  have h := strictMonoOn_intervalBaseFlow C s
  have ht' : t ∈ Icc (-1) 1 := Ioo_subset_Icc_self ht
  constructor
  · simpa using h ⟨le_rfl, by norm_num⟩ ht' ht.1
  · simpa using h ht' ⟨by norm_num, le_rfl⟩ ht.2

/-- **The flow lines through `(0, 1)` lie on one orbit**: the flow line through `t ∈ (0, 1)` is the
unit-rate reference trajectory `intervalBaseOrbit 1` evaluated at time
`intervalBaseTimeCoordinate t + C * s`. So for `C > 0` it runs forward from `0` to `1`, for
`C < 0` it runs backward from `1` to `0`, and for `C = 0` it is stationary. -/
theorem intervalBaseFlow_eq_intervalBaseOrbit (C s : ℝ) {t : ℝ} (ht : t ∈ Ioo 0 1) :
    intervalBaseFlow C s t = intervalBaseOrbit 1 (intervalBaseTimeCoordinate t + C * s) := by
  rw [← intervalBaseTimeCoordinate_intervalBaseFlow C s ht,
    intervalBaseOrbit_one_intervalBaseTimeCoordinate (intervalBaseFlow_mem_Ioo_zero_one C s ht)]

/-! ### Regularity of the linearized operators -/

section Operator

open TauCeti.WeakDerivStep

variable {γ : ℝ → ℝ}
  {AL : Lp (ℝ →L[ℝ] ℝ) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}

/-- Along a trajectory of the base flow from `0` to `1`, the linearized operator
`ξ ↦ ξ' - a'(γ) ξ`, with `a(t) = C t (1 - t²)`, is Fredholm. -/
theorem isFredholm_trajectoryOperator_intervalBasePotential (hC : C ≠ 0)
    (hγ : IsIntegralCurve γ (fun _ t ↦ -∇ (intervalBasePotential C) t))
    (hbot : Tendsto γ atBot (𝓝 0)) (htop : Tendsto γ atTop (𝓝 1))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ hessianOperator (intervalBasePotential C) (γ s)) :
    (trajectoryOperator (p := 2) AL).IsFredholm :=
  hγ.isFredholm_trajectoryOperator_hessianOperator (contDiff_intervalBasePotential C)
    (isNondegenerateCriticalPoint_intervalBasePotential_zero hC)
    (isNondegenerateCriticalPoint_intervalBasePotential_one hC) hbot htop hAL

/-- **The base operator has index one.** For `C > 0`, along a trajectory of the base flow from
`0` to `1`, the linearized operator `ξ ↦ ξ' - a'(γ) ξ` has index `1`, the drop of the Morse index
from the maximum `0` to the minimum `1`. -/
theorem index_trajectoryOperator_intervalBasePotential (hC : 0 < C)
    (hγ : IsIntegralCurve γ (fun _ t ↦ -∇ (intervalBasePotential C) t))
    (hbot : Tendsto γ atBot (𝓝 0)) (htop : Tendsto γ atTop (𝓝 1))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ hessianOperator (intervalBasePotential C) (γ s)) :
    (trajectoryOperator (p := 2) AL).index = 1 := by
  rw [hγ.index_trajectoryOperator_hessianOperator (contDiff_intervalBasePotential C)
    (isNondegenerateCriticalPoint_intervalBasePotential_zero hC.ne')
    (isNondegenerateCriticalPoint_intervalBasePotential_one hC.ne') hbot htop hAL,
    morseIndex_intervalBasePotential_zero hC, morseIndex_intervalBasePotential_one hC]
  simp

/-- **The kernel of the base operator is spanned by the velocity.** Along a trajectory `γ` of
the base flow from `0` to `1`, the kernel of `ξ ↦ ξ' - a'(γ) ξ` on `W^{1,2}(ℝ, ℝ)` is the line
through the element whose value is `γ'`. -/
theorem exists_ker_trajectoryOperator_intervalBasePotential_eq_span
    (hγ : IsIntegralCurve γ (fun _ t ↦ -∇ (intervalBasePotential C) t))
    (hbot : Tendsto γ atBot (𝓝 0)) (htop : Tendsto γ atTop (𝓝 1))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ hessianOperator (intervalBasePotential C) (γ s)) :
    ∃ u : WeakDerivStep volume ⊤ 2
        (ContinuousLinearMap.id ℝ (Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))),
      ⇑(prev (ContinuousLinearMap.id ℝ (Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) u)
          =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] deriv γ ∧
        (trajectoryOperator (p := 2) AL).ker = ℝ ∙ u :=
  hγ.exists_ker_trajectoryOperator_hessianOperator_eq_span (Module.finrank_self ℝ)
    (contDiff_intervalBasePotential C) hbot htop zero_ne_one hAL

/-- **The base operator is onto.** For `C > 0`, along a trajectory of the base flow from `0` to
`1`, the linearized operator `ξ ↦ ξ' - a'(γ) ξ` from `W^{1,2}(ℝ, ℝ)` to `L²(ℝ, ℝ)` is
surjective. -/
theorem surjective_trajectoryOperator_intervalBasePotential (hC : 0 < C)
    (hγ : IsIntegralCurve γ (fun _ t ↦ -∇ (intervalBasePotential C) t))
    (hbot : Tendsto γ atBot (𝓝 0)) (htop : Tendsto γ atTop (𝓝 1))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ hessianOperator (intervalBasePotential C) (γ s)) :
    Function.Surjective (trajectoryOperator (p := 2) AL) :=
  (hγ.surjective_trajectoryOperator_hessianOperator_iff (Module.finrank_self ℝ)
    (contDiff_intervalBasePotential C)
    (isNondegenerateCriticalPoint_intervalBasePotential_zero hC.ne')
    (isNondegenerateCriticalPoint_intervalBasePotential_one hC.ne') hbot htop zero_ne_one hAL).2
    (by rw [morseIndex_intervalBasePotential_zero hC, morseIndex_intervalBasePotential_one hC])

/-- **The adjoint of the base operator is injective.** For `C > 0`, along a trajectory of the
base flow from `0` to `1`, the formal adjoint `-d/ds - a'(γ)` of the linearized operator has
trivial kernel on `W^{1,2}(ℝ, ℝ)`: the kernel of `ξ ↦ ξ' + a'(γ) ξ` vanishes. -/
theorem ker_trajectoryOperator_neg_intervalBasePotential_eq_bot (hC : 0 < C)
    (hγ : IsIntegralCurve γ (fun _ t ↦ -∇ (intervalBasePotential C) t))
    (hbot : Tendsto γ atBot (𝓝 0)) (htop : Tendsto γ atTop (𝓝 1))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ hessianOperator (intervalBasePotential C) (γ s)) :
    (trajectoryOperator (p := 2) (-AL)).ker = ⊥ := by
  have hadj : ∀ᵐ s ∂volume.restrict ((⊤ : Opens ℝ) : Set ℝ),
      AL s = ContinuousLinearMap.adjoint (AL s) := by
    filter_upwards [hAL] with s hs
    rw [hs]
    exact (contDiff_intervalBasePotential C).contDiffAt.isSelfAdjoint_hessianOperator.isSymmetric
      |>.clm_adjoint_eq.symm
  exact (surjective_trajectoryOperator_iff_ker_neg_eq_bot hadj
    (isFredholm_trajectoryOperator_intervalBasePotential hC.ne' hγ hbot htop hAL).isClosed_range).1
    (surjective_trajectoryOperator_intervalBasePotential hC hγ hbot htop hAL)

/-- **The base operator at `0` is invertible.** For `C ≠ 0`, the linearized operator at
the constant trajectory at `0`, which is `ξ ↦ ξ' - C ξ`, is a bijection from `W^{1,2}(ℝ, ℝ)` onto
`L²(ℝ, ℝ)`. -/
theorem bijective_trajectoryOperator_intervalBasePotential_zero (hC : C ≠ 0)
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun _ ↦ hessianOperator (intervalBasePotential C) 0) :
    Function.Bijective (trajectoryOperator (p := 2) AL) :=
  IsNondegenerateCriticalPoint.bijective_trajectoryOperator_hessianOperator
    (isNondegenerateCriticalPoint_intervalBasePotential_zero hC) hAL

/-- **The base operator at `1` is invertible.** For `C ≠ 0`, the linearized operator at
the constant trajectory at `1`, which is `ξ ↦ ξ' + 2 C ξ`, is a bijection from `W^{1,2}(ℝ, ℝ)`
onto `L²(ℝ, ℝ)`. -/
theorem bijective_trajectoryOperator_intervalBasePotential_one (hC : C ≠ 0)
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun _ ↦ hessianOperator (intervalBasePotential C) 1) :
    Function.Bijective (trajectoryOperator (p := 2) AL) :=
  IsNondegenerateCriticalPoint.bijective_trajectoryOperator_hessianOperator
    (isNondegenerateCriticalPoint_intervalBasePotential_one hC) hAL

end Operator

end TauCeti

end
