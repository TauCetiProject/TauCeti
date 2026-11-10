/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sigmoid
public import TauCeti.Analysis.Calculus.Morse.IntervalBase
public import TauCeti.Analysis.Calculus.Morse.Pi
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.ODE.ExistUnique

/-!
# The negative gradient flow of the Euclidean quartic

The quartic `(x² - 1)² / 4` on `ℝ` is the base potential `TauCeti.intervalBasePotential 1`. It
has a local maximum at `0` and minima at `±1`, and its negative gradient field is `x (1 - x²)`,
whose linearization is `1` at `0` and `-2` at `±1`, so trajectories leave `0` at rate `1` and
approach `±1` at rate `2`. Its flow `TauCeti.intervalBaseFlow 1`, trajectory
`TauCeti.intervalBaseOrbit 1` from `0` to `1` and time coordinate
`TauCeti.intervalBaseTimeCoordinate` on `(0, 1)` are developed in
`TauCeti.Analysis.Calculus.Morse.IntervalBase`, for the base of a continuation, on the half
`[0, 1]` of the interval. This file completes the picture on the whole interval `[-1, 1]` and for
every `C`: the critical point `-1`
(`TauCeti.isNondegenerateCriticalPoint_intervalBasePotential_iff`), the invariance of `(-1, 1)`,
the forward limit at the sign of the initial point (`TauCeti.tendsto_intervalBaseFlow_atTop_sign`),
the backward limits, and the fact that the flow
lines are the only negative gradient trajectories staying in `[-1, 1]`
(`TauCeti.eq_intervalBaseFlow_of_isIntegralCurve`), since the field is Lipschitz there. Outside
`[-1, 1]` the backward flow escapes in finite time; it is not used here. In the time coordinate
`s`, the identities `q² = σ (2s)` and `1 - q² = σ (-2s)` for the sigmoid `σ` display the two
asymptotic rates exactly, and the flow line through any point of `(0, 1)` is a translate of `q`
(`TauCeti.intervalBaseFlow_eq_intervalBaseOrbit`).

The separated sum `quarticWellSum y = ∑ i, (yᵢ² - 1)² / 4` on `ι → ℝ` is the standard model
for compactified spaces of broken trajectories and for the comparison of Morse chains with
cellular chains of the cube. Its critical points are the points of `{-1, 0, 1}^ι`, all
nondegenerate, and the Morse index of such a point is the number of its zero coordinates
(`TauCeti.morseIndex_quarticWellSum`). Its partial derivatives are those of the summands
(`TauCeti.fderiv_quarticWellSum_apply`), so its negative gradient field for the Euclidean inner
product acts coordinatewise, and its flow `quarticWellSumFlow` is the coordinatewise flow
`TauCeti.intervalBaseFlow 1`. It keeps the cube `[-1, 1]^ι` invariant, and every point of the cube
has a forward limit, the coordinatewise sign, and a backward limit, which keeps the coordinates
equal to `±1` and replaces the others by `0`. So the points of the cube flowing backward to a
critical point `p` form the open face of the cube centred at `p`. A point `y` of the cube lies on a
trajectory from `p` to `q` exactly when, coordinatewise, either `p i = 0`, `y i ∈ (-1, 1)` and
`q i` is the sign of `y i`, or `y i = p i = q i = ±1`
(`TauCeti.tendsto_quarticWellSumFlow_atBot_atTop_iff`). The coordinates that move are those with
`p i = 0 ≠ q i`, and their number is the index difference.

## Main definitions

* `TauCeti.quarticWellSum`, `TauCeti.quarticWellSumFlow`: the separated sum on `ι → ℝ` and its
  coordinatewise flow.

## Main results

* `TauCeti.isNondegenerateCriticalPoint_intervalBasePotential_iff`,
  `TauCeti.morseIndex_intervalBasePotential_neg_one`: the critical points of the base potential.
* `TauCeti.intervalBaseFlow_mem_Ioo`, `TauCeti.tendsto_intervalBaseFlow_atTop_sign`,
  `TauCeti.tendsto_intervalBaseFlow_atBot_ite`: invariance of `(-1, 1)` and the limits of the flow.
* `TauCeti.eq_intervalBaseFlow_of_isIntegralCurve`: the trajectories in `[-1, 1]` are the flow
  lines.
* `TauCeti.intervalBaseOrbit_sq_eq_sigmoid`, `TauCeti.one_sub_intervalBaseOrbit_sq`,
  `TauCeti.intervalBaseFlow_eq_intervalBaseOrbit`: the time coordinate.
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

variable {C : ℝ}

/-! ### The base potential on the whole interval `[-1, 1]` -/

/-- **The base potential is a Morse function**: for `C ≠ 0` its critical points are `-1`, `0` and
`1`, all nondegenerate. -/
theorem isNondegenerateCriticalPoint_intervalBasePotential_iff (hC : C ≠ 0) {t : ℝ} :
    IsNondegenerateCriticalPoint (intervalBasePotential C) t ↔ t = -1 ∨ t = 0 ∨ t = 1 := by
  rw [isNondegenerateCriticalPoint_real_iff (contDiff_intervalBasePotential C).contDiffAt,
    iteratedDeriv_two_intervalBasePotential, deriv_intervalBasePotential]
  beta_reduce
  rw [show C * t * (t ^ 2 - 1) = C * (t * (t + 1) * (t - 1)) by ring]
  simp only [mul_eq_zero, hC, false_or, add_eq_zero_iff_eq_neg, sub_eq_zero]
  refine ⟨fun h ↦ by tauto, fun h ↦ ⟨by tauto, ?_⟩⟩
  rcases h with rfl | rfl | rfl <;> norm_num [hC]

/-- For `C > 0` the critical point `-1` of the base potential is a local minimum: its Morse index
is `0`. -/
@[simp]
theorem morseIndex_intervalBasePotential_neg_one (hC : 0 < C) :
    morseIndex (intervalBasePotential C) (-1) = 0 :=
  morseIndex_real_of_pos (by rw [iteratedDeriv_two_intervalBasePotential]; norm_num; linarith)

/-- The critical point `-1` is fixed by the flow. -/
@[simp]
theorem intervalBaseFlow_apply_neg_one (C s : ℝ) : intervalBaseFlow C s (-1) = -1 := by
  rw [intervalBaseFlow_neg, intervalBaseFlow_apply_one]

/-- The flow preserves `(-1, 1)`. -/
theorem intervalBaseFlow_mem_Ioo (C s : ℝ) {t : ℝ} (ht : t ∈ Ioo (-1) 1) :
    intervalBaseFlow C s t ∈ Ioo (-1) 1 := by
  have h := strictMonoOn_intervalBaseFlow C s
  have ht' : t ∈ Icc (-1) 1 := Ioo_subset_Icc_self ht
  constructor
  · simpa using h ⟨le_rfl, by norm_num⟩ ht' ht.1
  · simpa using h ht' ⟨by norm_num, le_rfl⟩ ht.2

/-- **Forward limit**: for `C > 0`, as `s → ∞` the flow from `t` tends to the sign of `t`, the
minimum `±1` on its side of `0`, or `0` if `t = 0`. The closed formula has this limit for every
`t`, although it is a trajectory only for `t ∈ [-1, 1]`. -/
theorem tendsto_intervalBaseFlow_atTop_sign (hC : 0 < C) (t : ℝ) :
    Tendsto (fun s ↦ intervalBaseFlow C s t) atTop (𝓝 (SignType.sign t)) := by
  rcases eq_or_ne t 0 with rfl | ht0
  · simp
  simp only [intervalBaseFlow_apply]
  have hexp : Tendsto (fun s ↦ exp (-(2 * C * s))) atTop (𝓝 0) :=
    tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop (by positivity)))
  have hD := ((tendsto_const_nhds (x := t ^ 2)).add (hexp.const_mul (1 - t ^ 2))).sqrt
  rw [mul_zero, add_zero, sqrt_sq_eq_abs] at hD
  have h := (tendsto_const_nhds (x := t)).div hD (abs_pos.2 ht0).ne'
  rwa [show (SignType.sign t : ℝ) = t / |t| by
    rw [eq_div_iff (abs_pos.2 ht0).ne', sign_mul_abs]]

/-- **Backward limit**: for `C > 0`, the backward limit of the flow from `t ∈ [-1, 1]` is `0` if
`t ∈ (-1, 1)`, and `t` itself if `t = ±1`, where the flow is stationary. -/
theorem tendsto_intervalBaseFlow_atBot_ite (hC : 0 < C) {t : ℝ} (ht : t ∈ Icc (-1) 1) :
    Tendsto (fun s ↦ intervalBaseFlow C s t) atBot (𝓝 (if t ∈ Ioo (-1) 1 then 0 else t)) := by
  split_ifs with ht'
  · exact tendsto_intervalBaseFlow_atBot hC ht'
  · have h : t ∈ Icc (-1) 1 \ Ioo (-1) 1 := ⟨ht, ht'⟩
    rw [Icc_sdiff_Ioo_same (by norm_num)] at h
    rcases h with rfl | rfl <;> simp

/-- The negative gradient field of the base potential is `2 |C|`-Lipschitz on `[-1, 1]`: the
difference quotient of `C t (1 - t²)` is `C (1 - (a² + a b + b²))`. -/
theorem lipschitzOnWith_neg_gradient_intervalBasePotential (C : ℝ) :
    LipschitzOnWith (2 * ‖C‖₊) (fun t ↦ -∇ (intervalBasePotential C) t) (Icc (-1) 1) := by
  refine LipschitzOnWith.of_dist_le_mul fun a ha b hb ↦ ?_
  rw [mem_Icc] at ha hb
  have h : |1 - (a ^ 2 + a * b + b ^ 2)| ≤ 2 := by
    rw [abs_le]
    constructor <;> nlinarith
  simp only [gradient_intervalBasePotential, dist_eq_norm, norm_eq_abs, NNReal.coe_mul,
    NNReal.coe_ofNat, coe_nnnorm]
  rw [show -(C * a * (a ^ 2 - 1)) - -(C * b * (b ^ 2 - 1)) =
      C * (a - b) * (1 - (a ^ 2 + a * b + b ^ 2)) by ring, abs_mul, abs_mul]
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

/-! ### The time coordinate -/

/-- The square of the trajectory `q` is the sigmoid `σ (2 C s)`: at `C = 1` it leaves `0` at
rate `1`, and the time coordinate is half the logit of `q²`. -/
theorem intervalBaseOrbit_sq_eq_sigmoid (C s : ℝ) :
    intervalBaseOrbit C s ^ 2 = sigmoid (2 * C * s) := by
  rw [intervalBaseOrbit_sq, sigmoid_def]

/-- One minus the square of the trajectory `q` is the sigmoid `σ (-2 C s)`: at `C = 1` it
approaches `1` at rate `2`. -/
theorem one_sub_intervalBaseOrbit_sq (C s : ℝ) :
    1 - intervalBaseOrbit C s ^ 2 = sigmoid (-(2 * C * s)) := by
  rw [intervalBaseOrbit_sq_eq_sigmoid, sigmoid_neg]

/-- **The trajectories from `0` to `1` form one orbit**: the flow line through `t ∈ (0, 1)` is the
trajectory `q` at unit rate, started at the time coordinate of `t`. -/
theorem intervalBaseFlow_eq_intervalBaseOrbit (C s : ℝ) {t : ℝ} (ht : t ∈ Ioo 0 1) :
    intervalBaseFlow C s t = intervalBaseOrbit 1 (intervalBaseTimeCoordinate t + C * s) := by
  rw [← intervalBaseTimeCoordinate_intervalBaseFlow C s ht,
    intervalBaseOrbit_one_intervalBaseTimeCoordinate (intervalBaseFlow_mem_Ioo_zero_one C s ht)]

/-! ### The quartic on the cube -/

section Sum

variable {ι : Type*}

/-- The **negative gradient flow of the Euclidean quartic** on the cube `[-1, 1]^ι`: the flow
`TauCeti.intervalBaseFlow 1` in each coordinate. -/
def quarticWellSumFlow (s : ℝ) (y : ι → ℝ) : ι → ℝ := fun i ↦ intervalBaseFlow 1 s (y i)

@[simp]
theorem quarticWellSumFlow_apply (s : ℝ) (y : ι → ℝ) (i : ι) :
    quarticWellSumFlow s y i = intervalBaseFlow 1 s (y i) := (rfl)

@[simp]
theorem quarticWellSumFlow_zero_left (y : ι → ℝ) : quarticWellSumFlow 0 y = y :=
  funext fun i ↦ intervalBaseFlow_zero 1 (y i)

/-- The flow property of the coordinatewise flow on the cube. -/
theorem quarticWellSumFlow_add {y : ι → ℝ} (hy : y ∈ Icc (-1) 1) (s r : ℝ) :
    quarticWellSumFlow (s + r) y = quarticWellSumFlow s (quarticWellSumFlow r y) :=
  funext fun i ↦ intervalBaseFlow_add 1 s r ⟨hy.1 i, hy.2 i⟩

/-- The flow keeps the cube `[-1, 1]^ι` invariant. -/
theorem quarticWellSumFlow_mem_Icc {y : ι → ℝ} (hy : y ∈ Icc (-1) 1) (s : ℝ) :
    quarticWellSumFlow s y ∈ Icc (-1) 1 :=
  ⟨fun i ↦ (intervalBaseFlow_mem_Icc 1 s ⟨hy.1 i, hy.2 i⟩).1,
    fun i ↦ (intervalBaseFlow_mem_Icc 1 s ⟨hy.1 i, hy.2 i⟩).2⟩

/-- The coordinatewise flow solves the negative gradient equation `yᵢ' = yᵢ (1 - yᵢ²)` of the
Euclidean quartic. -/
theorem hasDerivAt_quarticWellSumFlow {y : ι → ℝ} (hy : y ∈ Icc (-1) 1) (s : ℝ) :
    HasDerivAt (fun s ↦ quarticWellSumFlow s y)
      (fun i ↦ -∇ (intervalBasePotential 1) (quarticWellSumFlow s y i)) s :=
  hasDerivAt_pi.2 fun i ↦ isIntegralCurve_intervalBaseFlow 1 ⟨hy.1 i, hy.2 i⟩ s

/-- **Forward limits**: every point flows to the critical point given by the signs of its
coordinates. On the cube `[-1, 1]^ι` this is the forward limit of the negative gradient
trajectory through the point. -/
theorem tendsto_quarticWellSumFlow_atTop (y : ι → ℝ) :
    Tendsto (fun s ↦ quarticWellSumFlow s y) atTop (𝓝 fun i ↦ (SignType.sign (y i) : ℝ)) :=
  tendsto_pi_nhds.2 fun i ↦ tendsto_intervalBaseFlow_atTop_sign one_pos (y i)

/-- **Backward limits on the cube**: as `s → -∞` a point of `[-1, 1]^ι` tends to the critical
point keeping its coordinates equal to `±1` and replacing the others by `0`. -/
theorem tendsto_quarticWellSumFlow_atBot {y : ι → ℝ} (hy : y ∈ Icc (-1) 1) :
    Tendsto (fun s ↦ quarticWellSumFlow s y) atBot
      (𝓝 fun i ↦ if y i ∈ Ioo (-1) 1 then 0 else y i) :=
  tendsto_pi_nhds.2 fun i ↦ tendsto_intervalBaseFlow_atBot_ite one_pos ⟨hy.1 i, hy.2 i⟩

/-- **Connecting trajectories in the cube.** A point `y` of `[-1, 1]^ι` lies on a trajectory from
`p` to `q` exactly when each coordinate either moves, with `p i = 0`, `y i ∈ (-1, 1)` and `q i`
the sign of `y i`, or stays at `y i = p i = q i = ±1`. -/
theorem tendsto_quarticWellSumFlow_atBot_atTop_iff {y p q : ι → ℝ} (hy : y ∈ Icc (-1) 1) :
    Tendsto (fun s ↦ quarticWellSumFlow s y) atBot (𝓝 p) ∧
        Tendsto (fun s ↦ quarticWellSumFlow s y) atTop (𝓝 q) ↔
      ∀ i, (y i ∈ Ioo (-1) 1 ∧ p i = 0 ∧ q i = SignType.sign (y i)) ∨
        ((y i = -1 ∨ y i = 1) ∧ p i = y i ∧ q i = y i) := by
  have hbot := tendsto_quarticWellSumFlow_atBot hy
  have htop := tendsto_quarticWellSumFlow_atTop y
  have key : ∀ i, (p i = (if y i ∈ Ioo (-1) 1 then 0 else y i) ∧
      q i = SignType.sign (y i)) ↔ ((y i ∈ Ioo (-1) 1 ∧ p i = 0 ∧ q i = SignType.sign (y i)) ∨
        ((y i = -1 ∨ y i = 1) ∧ p i = y i ∧ q i = y i)) := fun i ↦ by
    by_cases hi : y i ∈ Ioo (-1) 1
    · have : ¬(y i = -1 ∨ y i = 1) := by rintro (h | h) <;> simp [h] at hi
      simp [hi, this]
    · have h : y i ∈ Icc (-1) 1 \ Ioo (-1) 1 := ⟨⟨hy.1 i, hy.2 i⟩, hi⟩
      rw [Icc_sdiff_Ioo_same (by norm_num), mem_insert_iff, mem_singleton_iff] at h
      have hs : (SignType.sign (y i) : ℝ) = y i := by rcases h with h | h <;> simp [h]
      simp [hi, h, hs]
  refine ⟨fun ⟨hp, hq⟩ i ↦ (key i).1 ⟨congrFun (tendsto_nhds_unique hp hbot) i,
    congrFun (tendsto_nhds_unique hq htop) i⟩, fun h ↦ ?_⟩
  have hp : p = fun i ↦ if y i ∈ Ioo (-1) 1 then 0 else y i := funext fun i ↦ ((key i).2 (h i)).1
  have hq : q = fun i ↦ (SignType.sign (y i) : ℝ) := funext fun i ↦ ((key i).2 (h i)).2
  exact ⟨hp ▸ hbot, hq ▸ htop⟩

variable [Fintype ι]

/-- The **Euclidean quartic** `∑ i, (yᵢ² - 1)² / 4` on `ι → ℝ`, the separated sum of copies of
the base potential `TauCeti.intervalBasePotential 1`. -/
def quarticWellSum (y : ι → ℝ) : ℝ := ∑ i, intervalBasePotential 1 (y i)

theorem quarticWellSum_def (y : ι → ℝ) :
    quarticWellSum y = ∑ i, intervalBasePotential 1 (y i) := (rfl)

private theorem quarticWellSum_eq :
    (quarticWellSum : (ι → ℝ) → ℝ) = fun z ↦ ∑ i, intervalBasePotential 1 (z i) :=
  funext quarticWellSum_def

/-- The partial derivatives of the Euclidean quartic are those of its summands, so its gradient
for the Euclidean inner product is `(yᵢ (yᵢ² - 1))ᵢ`, and `TauCeti.quarticWellSumFlow` integrates
its negative. -/
theorem fderiv_quarticWellSum_apply (y v : ι → ℝ) :
    fderiv ℝ quarticWellSum y v = ∑ i, ∇ (intervalBasePotential 1) (y i) * v i := by
  rw [quarticWellSum_eq,
    fderiv_sum_comp_eval fun _ ↦ (hasDerivAt_intervalBasePotential 1 _).differentiableAt]
  simp

private theorem deriv_deriv_intervalBasePotential_one (t : ℝ) :
    deriv (deriv (intervalBasePotential 1)) t = 3 * t ^ 2 - 1 := by
  have h := iteratedDeriv_two_intervalBasePotential 1 t
  rwa [iteratedDeriv_succ, iteratedDeriv_one, one_mul] at h

/-- **The Euclidean quartic is a Morse function**: its critical points are the points of
`{-1, 0, 1}^ι`, all nondegenerate. -/
theorem isNondegenerateCriticalPoint_quarticWellSum_iff {y : ι → ℝ} :
    IsNondegenerateCriticalPoint quarticWellSum y ↔ ∀ i, y i = -1 ∨ y i = 0 ∨ y i = 1 := by
  rw [quarticWellSum_eq, isNondegenerateCriticalPoint_sum_comp_eval_iff
    fun _ ↦ (contDiff_intervalBasePotential 1).contDiffAt]
  refine forall_congr' fun i ↦ ?_
  rw [← isNondegenerateCriticalPoint_intervalBasePotential_iff one_ne_zero,
    isNondegenerateCriticalPoint_real_iff (contDiff_intervalBasePotential 1).contDiffAt,
    iteratedDeriv_succ, iteratedDeriv_one]

/-- The Morse index of a critical point of the Euclidean quartic is the number of its zero
coordinates. -/
theorem morseIndex_quarticWellSum {y : ι → ℝ} (hy : ∀ i, y i = -1 ∨ y i = 0 ∨ y i = 1) :
    morseIndex quarticWellSum y = {i | y i = 0}.ncard := by
  rw [quarticWellSum_eq,
    morseIndex_sum_comp_eval fun _ ↦ (contDiff_intervalBasePotential 1).contDiffAt]
  congr 1
  ext i
  rw [mem_ofPred_eq, mem_ofPred_eq, deriv_deriv_intervalBasePotential_one]
  rcases hy i with h | h | h <;> rw [h] <;> norm_num

theorem isIntegralCurve_quarticWellSumFlow {y : ι → ℝ} (hy : y ∈ Icc (-1) 1) :
    IsIntegralCurve (fun s ↦ quarticWellSumFlow s y)
      (fun _ z i ↦ -∇ (intervalBasePotential 1) (z i)) :=
  hasDerivAt_quarticWellSumFlow hy

/-- **Uniqueness of captured trajectories** on the cube: a negative gradient trajectory of the
Euclidean quartic which stays in `[-1, 1]^ι` is the flow line through its initial point. -/
theorem eq_quarticWellSumFlow_of_isIntegralCurve {γ : ℝ → ι → ℝ}
    (hγ : IsIntegralCurve γ (fun _ z i ↦ -∇ (intervalBasePotential 1) (z i)))
    (hmem : ∀ s, γ s ∈ Icc (-1) 1) : γ = fun s ↦ quarticWellSumFlow s (γ 0) := by
  funext s i
  exact congrFun (eq_intervalBaseFlow_of_isIntegralCurve (fun s ↦ hasDerivAt_pi.1 (hγ s) i)
    fun s ↦ ⟨(hmem s).1 i, (hmem s).2 i⟩) s

end Sum

end TauCeti
