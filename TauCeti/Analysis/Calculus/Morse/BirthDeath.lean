/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.GradientFlow
public import TauCeti.Analysis.Calculus.Morse.OneDimensional
public import TauCeti.Analysis.Calculus.Morse.Prod
public import TauCeti.Analysis.SpecialFunctions.Hyperbolic
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import TauCeti.Geometry.Manifold.IntegralCurve.Basic

/-!
# The birth–death model of a one-parameter family of functions

In a generic one-parameter family of functions `f_t`, the critical points are nondegenerate except
at isolated parameters, where a single critical point is degenerate in the mildest possible way: its
Hessian has a one-dimensional kernel, the third derivative along the kernel is nonzero, and the
critical point moves with nonzero speed in the parameter. Cerf's normal form says that near such a
point, after a change of coordinates, the family is

`x₁³ / 3 - s x₁ - x₂² / 2 - ⋯ - x_i² / 2 + x_{i+1}² / 2 + ⋯`,

with `s = ±(t - t₀)`. As `s` passes through `0`, a pair of nondegenerate critical points of adjacent
indices is created (*birth*) or annihilated (*death*), and while they exist the two are joined by a
single negative gradient trajectory. This file computes this local model.

**The cubic.** The potential `x ↦ x³ / 3 - s x` (`TauCeti.birthDeathPotential s`) on the line has
derivative `x² - s`, second derivative `2 x` and third derivative `2`, and the parameter derivative
of its derivative is `-1`. So:

* for `s < 0` it has no critical point;
* for `s = 0` it has exactly one, the origin, which is degenerate
  (`TauCeti.not_isNondegenerateCriticalPoint_birthDeathPotential_zero`), although the third
  derivative there and the parameter derivative of the derivative are nonzero: these are the
  conditions defining a birth–death point;
* for `s > 0` it has exactly two, both nondegenerate: a local maximum at `-√s`, of Morse index `1`,
  and a local minimum at `√s`, of Morse index `0`. The difference of the critical values is
  `4 s √s / 3`.

So the critical points form the two branches `s ↦ ±√s` over `s ≥ 0`, which meet at the
degenerate critical point at `s = 0`. A continuous choice of critical points follows a single
branch (`TauCeti.eqOn_sqrt_or_eqOn_neg_sqrt_of_forall_fderiv_birthDeathPotential_eq_zero`), and
every choice tends to the origin as the parameter tends to `0`
(`TauCeti.tendsto_zero_of_eventually_fderiv_birthDeathPotential_eq_zero`): the branches of
nondegenerate critical points cannot be continued through the birth–death parameter.

The negative gradient field is `s - x²`. For `s > 0`, the curve
`t ↦ √s tanh (√s t)` (`TauCeti.birthDeathOrbit s`) is a negative gradient trajectory from the
maximum to the minimum, and every negative gradient trajectory from `-√s` to `√s` is one of its
time translates (`TauCeti.exists_eq_birthDeathOrbit_comp_add`): the two critical points are joined
by exactly one unparametrized trajectory.

**The model in higher dimensions.** Adding a function `g` with a nondegenerate critical point `y`
of Morse index `k` in transverse directions gives the separated sum
`(x, y) ↦ x³ / 3 - s x + g y`. For `s > 0` the points `(-√s, y)` and `(√s, y)` are nondegenerate
critical points of Morse indices `k + 1` and `k`, and every negative gradient trajectory from the
first to the second is `t ↦ (√s tanh (√s (t + τ)), y)` for some `τ`
(`TauCeti.exists_eq_birthDeathOrbit_separatedSum`): its transverse component stays at `y`, because a
negative gradient trajectory with the same limit at both ends is constant. When `g` is the
quadratic form `-x₂² / 2 - ⋯ + ⋯`, this is Cerf's normal form. It is the local picture behind the
change of the Morse complex at a birth or a death: two generators of adjacent degrees appear or
disappear, and they are joined by a single trajectory.

## Main declarations

* `TauCeti.birthDeathPotential`: the cubic `x³ / 3 - s x`.
* `TauCeti.fderiv_birthDeathPotential_eq_zero_iff`: its critical points are the solutions of
  `x² = s`.
* `TauCeti.isNondegenerateCriticalPoint_birthDeathPotential_iff`: they are nondegenerate exactly
  when `s ≠ 0`, that is, away from the birth–death parameter.
* `TauCeti.morseIndex_birthDeathPotential_neg_sqrt`, `TauCeti.morseIndex_birthDeathPotential_sqrt`:
  for `s > 0`, the two critical points have Morse indices `1` and `0`.
* `TauCeti.tendsto_zero_of_eventually_fderiv_birthDeathPotential_eq_zero`: as the parameter tends
  to `0`, every choice of critical points tends to the degenerate critical point `0`.
* `TauCeti.eqOn_sqrt_or_eqOn_neg_sqrt_of_forall_fderiv_birthDeathPotential_eq_zero`: over a
  preconnected set of nonzero parameters, a continuous choice of critical points is one of the two
  branches `√s` and `-√s`.
* `TauCeti.birthDeathOrbit`, `TauCeti.isIntegralCurve_birthDeathOrbit`: the connecting trajectory
  `t ↦ √s tanh (√s t)`.
* `TauCeti.exists_eq_birthDeathOrbit_comp_add`: it is the only trajectory from `-√s` to `√s`, up to
  translation of time.
* `TauCeti.morseIndex_separatedSum_birthDeathPotential_neg_sqrt`,
  `TauCeti.morseIndex_separatedSum_birthDeathPotential_sqrt`,
  `TauCeti.exists_eq_birthDeathOrbit_separatedSum`: the same statements in the model with
  transverse directions.

## References

* J. Cerf, *La stratification naturelle des espaces de fonctions différentiables réelles et le
  théorème de la pseudo-isotopie*, Publ. Math. IHÉS 39 (1970), 5–173 (generic one-parameter
  families and the birth–death normal form).
* J. Milnor, *Lectures on the h-cobordism theorem*, Princeton University Press, 1965, §5
  (cancellation of two critical points joined by a single trajectory).
-/

public section

open Filter Set
open scoped Gradient Manifold Topology

namespace TauCeti

variable {s : ℝ}

/-! ### The potential -/

/-- The **birth–death potential** `x ↦ x³ / 3 - s x`. As the parameter `s` increases through `0`,
a pair of nondegenerate critical points `±√s` of Morse indices `1` and `0` is born. -/
noncomputable def birthDeathPotential (s x : ℝ) : ℝ :=
  x ^ 3 / 3 - s * x

theorem birthDeathPotential_apply (s x : ℝ) :
    birthDeathPotential s x = x ^ 3 / 3 - s * x := (rfl)

/-- The birth–death potential is a polynomial in the variable, hence smooth. -/
theorem contDiff_birthDeathPotential (s : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (birthDeathPotential s) := by
  unfold birthDeathPotential
  fun_prop

/-- The birth–death potential is jointly smooth in the parameter and the variable: it is a smooth
one-parameter family of functions. -/
theorem contDiff_birthDeathPotential_uncurry {n : WithTop ℕ∞} :
    ContDiff ℝ n fun p : ℝ × ℝ ↦ birthDeathPotential p.1 p.2 := by
  unfold birthDeathPotential
  fun_prop

/-- The derivative of the birth–death potential is `x² - s`. -/
theorem hasDerivAt_birthDeathPotential (s x : ℝ) :
    HasDerivAt (birthDeathPotential s) (x ^ 2 - s) x := by
  refine (((hasDerivAt_pow 3 x).div_const 3).sub ((hasDerivAt_id' x).const_mul s)).congr_deriv ?_
  norm_num

theorem differentiable_birthDeathPotential (s : ℝ) : Differentiable ℝ (birthDeathPotential s) :=
  fun x ↦ (hasDerivAt_birthDeathPotential s x).differentiableAt

@[simp]
theorem deriv_birthDeathPotential (s : ℝ) :
    deriv (birthDeathPotential s) = fun x ↦ x ^ 2 - s :=
  funext fun x ↦ (hasDerivAt_birthDeathPotential s x).deriv

/-- The differential of the birth–death potential at `x` is multiplication by `x² - s`. -/
@[simp]
theorem fderiv_birthDeathPotential (s x : ℝ) :
    fderiv ℝ (birthDeathPotential s) x = (x ^ 2 - s) • ContinuousLinearMap.id ℝ ℝ := by
  ext
  simp [← toSpanSingleton_deriv]

/-- The gradient of the birth–death potential is `x² - s`, so its negative gradient field is
`s - x²`. -/
@[simp]
theorem gradient_birthDeathPotential (s x : ℝ) :
    ∇ (birthDeathPotential s) x = x ^ 2 - s := by
  rw [gradient_eq_deriv', deriv_birthDeathPotential]

/-- The second derivative of the birth–death potential is `2 x`. -/
@[simp]
theorem iteratedDeriv_two_birthDeathPotential (s x : ℝ) :
    iteratedDeriv 2 (birthDeathPotential s) x = 2 * x := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, deriv_birthDeathPotential]
  refine ((hasDerivAt_pow 2 x).sub_const s).deriv.trans ?_
  norm_num

/-- The third derivative of the birth–death potential is the constant `2`: along the kernel of the
Hessian at the degenerate critical point, the potential is a nondegenerate cubic. -/
@[simp]
theorem iteratedDeriv_three_birthDeathPotential (s x : ℝ) :
    iteratedDeriv 3 (birthDeathPotential s) x = 2 := by
  rw [iteratedDeriv_succ, funext (iteratedDeriv_two_birthDeathPotential s)]
  exact ((hasDerivAt_id' x).const_mul 2).deriv.trans (mul_one 2)

/-- The parameter derivative of the derivative of the birth–death potential is `-1`: the critical
points move with nonzero speed in the parameter. -/
theorem hasDerivAt_deriv_birthDeathPotential_param (s x : ℝ) :
    HasDerivAt (fun s ↦ deriv (birthDeathPotential s) x) (-1) s := by
  simpa using (hasDerivAt_id' s).const_sub (x ^ 2)

/-! ### Critical points -/

/-- **The critical points of the birth–death potential** are the solutions of `x² = s`. -/
theorem fderiv_birthDeathPotential_eq_zero_iff {x : ℝ} :
    fderiv ℝ (birthDeathPotential s) x = 0 ↔ x ^ 2 = s := by
  rw [fderiv_birthDeathPotential]
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  simpa [sub_eq_zero] using congrArg (· 1) h

/-- Before the birth, for `s < 0`, the birth–death potential has no critical point. -/
theorem fderiv_birthDeathPotential_ne_zero (hs : s < 0) (x : ℝ) :
    fderiv ℝ (birthDeathPotential s) x ≠ 0 := fun h ↦ by
  have := fderiv_birthDeathPotential_eq_zero_iff.1 h
  nlinarith [sq_nonneg x]

/-- **Nondegenerate critical points of the birth–death potential.** A point is a nondegenerate
critical point exactly when it is a nonzero solution of `x² = s`. -/
theorem isNondegenerateCriticalPoint_birthDeathPotential_iff {x : ℝ} :
    IsNondegenerateCriticalPoint (birthDeathPotential s) x ↔ x ^ 2 = s ∧ x ≠ 0 := by
  rw [isNondegenerateCriticalPoint_real_iff (contDiff_birthDeathPotential s).contDiffAt,
    deriv_birthDeathPotential, iteratedDeriv_two_birthDeathPotential, sub_eq_zero]
  simp

/-- **The birth–death point.** At `s = 0` the origin, the only critical point of the birth–death
potential (`TauCeti.fderiv_birthDeathPotential_eq_zero_iff`), is degenerate. -/
theorem not_isNondegenerateCriticalPoint_birthDeathPotential_zero :
    ¬IsNondegenerateCriticalPoint (birthDeathPotential 0) 0 := by
  simp [isNondegenerateCriticalPoint_birthDeathPotential_iff]

/-- For `s ≥ 0`, the critical points of the birth–death potential are `-√s` and `√s`, which
coincide at the birth–death parameter `s = 0`. -/
theorem fderiv_birthDeathPotential_eq_zero_iff_of_nonneg (hs : 0 ≤ s) {x : ℝ} :
    fderiv ℝ (birthDeathPotential s) x = 0 ↔ x = -√s ∨ x = √s := by
  conv_lhs => rw [fderiv_birthDeathPotential_eq_zero_iff, ← Real.sq_sqrt hs]
  rw [sq_eq_sq_iff_eq_or_eq_neg, or_comm]

/-- After the birth, for `s > 0`, the nondegenerate critical points of the birth–death potential are
`-√s` and `√s`. -/
theorem isNondegenerateCriticalPoint_birthDeathPotential_iff_of_pos (hs : 0 < s) {x : ℝ} :
    IsNondegenerateCriticalPoint (birthDeathPotential s) x ↔ x = -√s ∨ x = √s := by
  have hsq := Real.sqrt_pos.2 hs
  rw [isNondegenerateCriticalPoint_birthDeathPotential_iff,
    ← fderiv_birthDeathPotential_eq_zero_iff,
    fderiv_birthDeathPotential_eq_zero_iff_of_nonneg hs.le, and_iff_left_iff_imp]
  rintro (rfl | rfl) <;> linarith

/-- For `s > 0`, `-√s` is a nondegenerate critical point of the birth–death potential. -/
theorem isNondegenerateCriticalPoint_birthDeathPotential_neg_sqrt (hs : 0 < s) :
    IsNondegenerateCriticalPoint (birthDeathPotential s) (-√s) :=
  (isNondegenerateCriticalPoint_birthDeathPotential_iff_of_pos hs).2 (.inl rfl)

/-- For `s > 0`, `√s` is a nondegenerate critical point of the birth–death potential. -/
theorem isNondegenerateCriticalPoint_birthDeathPotential_sqrt (hs : 0 < s) :
    IsNondegenerateCriticalPoint (birthDeathPotential s) √s :=
  (isNondegenerateCriticalPoint_birthDeathPotential_iff_of_pos hs).2 (.inr rfl)

/-- For `s > 0` the critical point `-√s` is a local maximum: its Morse index is `1`. -/
@[simp]
theorem morseIndex_birthDeathPotential_neg_sqrt (hs : 0 < s) :
    morseIndex (birthDeathPotential s) (-√s) = 1 :=
  morseIndex_real_of_neg (by
    rw [iteratedDeriv_two_birthDeathPotential]
    linarith [Real.sqrt_pos.2 hs])

/-- For `s > 0` the critical point `√s` is a local minimum: its Morse index is `0`. -/
@[simp]
theorem morseIndex_birthDeathPotential_sqrt (hs : 0 < s) :
    morseIndex (birthDeathPotential s) √s = 0 :=
  morseIndex_real_of_pos (by
    rw [iteratedDeriv_two_birthDeathPotential]
    linarith [Real.sqrt_pos.2 hs])

/-- The critical value at the local maximum `-√s` is `2 s √s / 3`. -/
theorem birthDeathPotential_neg_sqrt (s : ℝ) :
    birthDeathPotential s (-√s) = 2 * s * √s / 3 := by
  rcases le_or_gt 0 s with hs | hs
  · have h := Real.sq_sqrt hs
    rw [birthDeathPotential_apply]
    linear_combination (-√s / 3) * h
  · simp [birthDeathPotential_apply, Real.sqrt_eq_zero'.2 hs.le]

/-- The critical value at the local minimum `√s` is `-(2 s √s / 3)`. -/
theorem birthDeathPotential_sqrt (s : ℝ) :
    birthDeathPotential s √s = -(2 * s * √s / 3) := by
  rcases le_or_gt 0 s with hs | hs
  · have h := Real.sq_sqrt hs
    rw [birthDeathPotential_apply]
    linear_combination (√s / 3) * h
  · simp [birthDeathPotential_apply, Real.sqrt_eq_zero'.2 hs.le]

/-! ### Branches of critical points -/

/-- A critical point of the birth–death potential lies at distance `√s` from the origin. -/
theorem abs_eq_sqrt_of_fderiv_birthDeathPotential_eq_zero {x : ℝ}
    (h : fderiv ℝ (birthDeathPotential s) x = 0) : |x| = √s := by
  rw [← fderiv_birthDeathPotential_eq_zero_iff.1 h, Real.sqrt_sq_eq_abs]

/-- **Branches of critical points end at the birth–death point.** Let the parameters `σ a` tend to
the birth–death parameter `0` along a filter `l`, and let `ψ a` be a critical point of the
birth–death potential with parameter `σ a`, eventually along `l`. Then `ψ a` tends to the origin,
the degenerate critical point at the parameter `0`
(`TauCeti.not_isNondegenerateCriticalPoint_birthDeathPotential_zero`). So a branch of critical
points, continuous or not, cannot be continued through the parameter `0` as a branch of
nondegenerate critical points. -/
theorem tendsto_zero_of_eventually_fderiv_birthDeathPotential_eq_zero {α : Type*} {l : Filter α}
    {σ ψ : α → ℝ} (hσ : Tendsto σ l (𝓝 0))
    (h : ∀ᶠ a in l, fderiv ℝ (birthDeathPotential (σ a)) (ψ a) = 0) : Tendsto ψ l (𝓝 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  refine Tendsto.congr' (h.mono fun a ha ↦ ?_)
    (Real.sqrt_zero ▸ (Real.continuous_sqrt.tendsto 0).comp hσ)
  exact (abs_eq_sqrt_of_fderiv_birthDeathPotential_eq_zero ha).symm

/-- **Continuous branches of critical points.** Let `T` be a preconnected set of indices, `σ` a
family of nonzero parameters on `T`, and `ψ a` a critical point of the birth–death potential with
parameter `σ a`, continuous on `T`. Then `ψ` follows a single one of the two
branches of critical points on all of `T`: either `ψ = √σ`, the branch of local minima, or
`ψ = -√σ`, the branch of local maxima. Without `σ ≠ 0` this fails: for `σ a = a²` on `ℝ`, the
critical points `ψ a = a` switch branches at `a = 0`. -/
theorem eqOn_sqrt_or_eqOn_neg_sqrt_of_forall_fderiv_birthDeathPotential_eq_zero {α : Type*}
    [TopologicalSpace α] {T : Set α} {σ ψ : α → ℝ} (hT : IsPreconnected T)
    (hψ : ContinuousOn ψ T) (hσ₀ : ∀ a ∈ T, σ a ≠ 0)
    (h : ∀ a ∈ T, fderiv ℝ (birthDeathPotential (σ a)) (ψ a) = 0) :
    EqOn ψ (fun a ↦ √(σ a)) T ∨ EqOn ψ (fun a ↦ -√(σ a)) T := by
  have hsq (a : α) (ha : a ∈ T) : ψ a ^ 2 = σ a := fderiv_birthDeathPotential_eq_zero_iff.1 (h a ha)
  have hpos (a : α) (ha : a ∈ T) : 0 < σ a :=
    lt_of_le_of_ne (hsq a ha ▸ sq_nonneg _) (hσ₀ a ha).symm
  have hσ : ContinuousOn σ T := (hψ.pow 2).congr fun a ha ↦ (hsq a ha).symm
  refine (hT.eq_or_eq_neg_of_sq_eq hψ (Real.continuous_sqrt.comp_continuousOn hσ)
    (fun a ha ↦ ?_) fun {a} ha ↦ (Real.sqrt_pos.2 (hpos a ha)).ne').imp_right
    fun h' a ha ↦ h' ha
  simp [hsq a ha, Real.sq_sqrt (hpos a ha).le]

/-! ### The connecting trajectory -/

/-- The negative gradient trajectory `t ↦ √s tanh (√s t)` of the birth–death potential. For
`s > 0` it runs from the local maximum `-√s` to the local minimum `√s`, and every trajectory
between them is one of its time translates (`TauCeti.exists_eq_birthDeathOrbit_comp_add`). -/
noncomputable def birthDeathOrbit (s t : ℝ) : ℝ :=
  √s * Real.tanh (√s * t)

theorem birthDeathOrbit_apply (s t : ℝ) :
    birthDeathOrbit s t = √s * Real.tanh (√s * t) := (rfl)

@[simp]
theorem birthDeathOrbit_zero (s : ℝ) : birthDeathOrbit s 0 = 0 := by
  simp [birthDeathOrbit_apply]

/-- For `s ≥ 0`, the trajectory solves `x' = s - x²`. -/
theorem hasDerivAt_birthDeathOrbit (hs : 0 ≤ s) (t : ℝ) :
    HasDerivAt (birthDeathOrbit s) (s - birthDeathOrbit s t ^ 2) t := by
  have h := ((Real.hasDerivAt_tanh (√s * t)).comp t ((hasDerivAt_id' t).const_mul √s)).const_mul √s
  refine h.congr_deriv ?_
  have hsq : √s * √s = s := Real.mul_self_sqrt hs
  rw [birthDeathOrbit_apply]
  linear_combination (1 / Real.cosh (√s * t) ^ 2 + Real.tanh (√s * t) ^ 2) * hsq -
    s * Real.one_sub_tanh_sq (√s * t)

/-- For `s ≥ 0`, the trajectory is a negative gradient trajectory of the birth–death potential. -/
theorem isIntegralCurve_birthDeathOrbit (hs : 0 ≤ s) :
    IsIntegralCurve (birthDeathOrbit s) (fun _ x ↦ -∇ (birthDeathPotential s) x) := fun t ↦
  (hasDerivAt_birthDeathOrbit hs t).congr_deriv (by simp)

/-- For `s > 0`, the trajectory stays strictly between the two critical points. -/
theorem birthDeathOrbit_mem_Ioo (hs : 0 < s) (t : ℝ) : birthDeathOrbit s t ∈ Ioo (-√s) √s := by
  have hsq := Real.sqrt_pos.2 hs
  rw [birthDeathOrbit_apply]
  constructor
  · nlinarith [Real.neg_one_lt_tanh (√s * t)]
  · nlinarith [Real.tanh_lt_one (√s * t)]

/-- The trajectory tends to `-√s` at `-∞`. -/
theorem tendsto_birthDeathOrbit_atBot (s : ℝ) :
    Tendsto (birthDeathOrbit s) atBot (𝓝 (-√s)) := by
  rcases (Real.sqrt_nonneg s).eq_or_lt with h | h
  · simp only [funext (birthDeathOrbit_apply s), ← h, zero_mul, neg_zero]
    exact tendsto_const_nhds
  · rw [funext (birthDeathOrbit_apply s)]
    simpa [Function.comp_def] using
      (Real.tendsto_tanh_atBot.comp (tendsto_id.const_mul_atBot h)).const_mul √s

/-- The trajectory tends to `√s` at `+∞`. -/
theorem tendsto_birthDeathOrbit_atTop (s : ℝ) :
    Tendsto (birthDeathOrbit s) atTop (𝓝 √s) := by
  rcases (Real.sqrt_nonneg s).eq_or_lt with h | h
  · simp only [funext (birthDeathOrbit_apply s), ← h, zero_mul]
    exact tendsto_const_nhds
  · rw [funext (birthDeathOrbit_apply s)]
    simpa [Function.comp_def] using
      (Real.tendsto_tanh_atTop.comp (tendsto_id.const_mul_atTop h)).const_mul √s

/-- **Uniqueness of the connecting trajectory.** For `s > 0`, every negative gradient trajectory
of the birth–death potential from the local maximum `-√s` to the local minimum `√s` is a time
translate of `TauCeti.birthDeathOrbit s`. So the two critical points born at `s = 0` are joined by
exactly one unparametrized trajectory. -/
theorem exists_eq_birthDeathOrbit_comp_add (hs : 0 < s) {γ : ℝ → ℝ}
    (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ (birthDeathPotential s) x))
    (hbot : Tendsto γ atBot (𝓝 (-√s))) (htop : Tendsto γ atTop (𝓝 √s)) :
    ∃ τ, γ = fun t ↦ birthDeathOrbit s (t + τ) := by
  have hsq := Real.sqrt_pos.2 hs
  -- The trajectory crosses `0`, by the intermediate value theorem.
  obtain ⟨a, ha⟩ := (hbot.eventually (gt_mem_nhds (neg_lt_zero.2 hsq))).exists
  obtain ⟨b, hb⟩ := (htop.eventually (lt_mem_nhds hsq)).exists
  obtain ⟨t₀, ht₀⟩ := intermediate_value_univ a b
    (continuous_iff_continuousAt.2 fun t ↦ (hγ t).continuousAt) ⟨ha.le, hb.le⟩
  refine ⟨-t₀, ?_⟩
  -- The orbit translated to cross `0` at time `t₀` solves the same equation.
  have hδ : IsIntegralCurve (fun t ↦ birthDeathOrbit s (t + -t₀))
      (fun _ x ↦ -∇ (birthDeathPotential s) x) := fun t ↦
    (isIntegralCurve_birthDeathOrbit hs.le (t + -t₀)).comp_add_const t (-t₀)
  -- Integral curves of the smooth field `s - x²` agreeing at one time agree everywhere: read the
  -- line as a manifold modelled on itself and use the uniqueness of its integral curves.
  let V : (x : ℝ) → TangentSpace 𝓘(ℝ, ℝ) x := fun x ↦ -∇ (birthDeathPotential s) x
  have hV : ContDiff ℝ 1 V := by
    simp only [V, gradient_birthDeathPotential]
    fun_prop
  have hM : ∀ c : ℝ → ℝ, IsIntegralCurve c (fun _ x ↦ -∇ (birthDeathPotential s) x) →
      IsMIntegralCurve c V := fun c hc ↦ isMIntegralCurve_iff_isMIntegralCurveOn.2
    (isMIntegralCurveOn_iff_isIntegralCurveOn.2 (hc.isIntegralCurveOn _))
  exact isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (t₀ := t₀)
    (contMDiff_vectorSpace_iff_contDiff.2 hV) (hM γ hγ) (hM _ hδ) (by simp [ht₀])

/-! ### The model with transverse directions -/

section SeparatedSum

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] {g : F → ℝ} {y : F}

/-- In the birth–death model with transverse directions, the critical point `(-√s, y)` above a
nondegenerate critical point `y` of the transverse function `g` has Morse index one more than
`y`. -/
theorem morseIndex_separatedSum_birthDeathPotential_neg_sqrt [FiniteDimensional ℝ F] (hs : 0 < s)
    (hy : IsNondegenerateCriticalPoint g y) :
    morseIndex (separatedSum (birthDeathPotential s) g) (WithLp.toLp 2 (-√s, y)) =
      morseIndex g y + 1 := by
  rw [morseIndex_separatedSum (contDiff_birthDeathPotential s).contDiffAt hy.contDiffAt,
    WithLp.toLp_fst, WithLp.toLp_snd, morseIndex_birthDeathPotential_neg_sqrt hs, add_comm]

/-- In the birth–death model with transverse directions, the critical point `(√s, y)` above a
nondegenerate critical point `y` of the transverse function `g` has the Morse index of `y`. -/
theorem morseIndex_separatedSum_birthDeathPotential_sqrt [FiniteDimensional ℝ F] (hs : 0 < s)
    (hy : IsNondegenerateCriticalPoint g y) :
    morseIndex (separatedSum (birthDeathPotential s) g) (WithLp.toLp 2 (√s, y)) =
      morseIndex g y := by
  rw [morseIndex_separatedSum (contDiff_birthDeathPotential s).contDiffAt hy.contDiffAt,
    WithLp.toLp_fst, WithLp.toLp_snd, morseIndex_birthDeathPotential_sqrt hs, zero_add]

/-- **The connecting trajectory of the birth–death model.** Let `g` be differentiable. For `s > 0`,
every negative gradient trajectory of
`(x, y) ↦ x³ / 3 - s x + g y` from `(-√s, y)` to `(√s, y)` is
`t ↦ (√s tanh (√s (t + τ)), y)` for some `τ`: its transverse component is constant, and its first
component is a translate of `TauCeti.birthDeathOrbit s`. -/
theorem exists_eq_birthDeathOrbit_separatedSum [CompleteSpace F] (hs : 0 < s)
    (hg : Differentiable ℝ g) {z : ℝ → WithLp 2 (ℝ × F)}
    (hz : IsIntegralCurve z (fun _ w ↦ -∇ (separatedSum (birthDeathPotential s) g) w))
    (hbot : Tendsto z atBot (𝓝 (WithLp.toLp 2 (-√s, y))))
    (htop : Tendsto z atTop (𝓝 (WithLp.toLp 2 (√s, y)))) :
    ∃ τ, z = fun t ↦ WithLp.toLp 2 (birthDeathOrbit s (t + τ), y) :=
  hz.exists_eq_toLp_comp_add_of_separatedSum hg (fun _ ↦ differentiable_birthDeathPotential s _)
    (fun _ hδ hδbot hδtop ↦ exists_eq_birthDeathOrbit_comp_add hs hδ hδbot hδtop) hbot htop

/-- Conversely, above a critical point `y` of a transverse function `g` differentiable at `y`, the
curve `t ↦ (√s tanh (√s t), y)` is a negative gradient trajectory of the birth–death model. -/
theorem isIntegralCurve_birthDeathOrbit_separatedSum [CompleteSpace F] (hs : 0 ≤ s)
    (hg : DifferentiableAt ℝ g y) (hy : ∇ g y = 0) :
    IsIntegralCurve (fun t ↦ WithLp.toLp 2 (birthDeathOrbit s t, y))
      (fun _ w ↦ -∇ (separatedSum (birthDeathPotential s) g) w) :=
  (isIntegralCurve_birthDeathOrbit hs).separatedSum (isIntegralCurve_const_neg_gradient_iff.2 hy)
    (fun _ ↦ differentiable_birthDeathPotential s _) fun _ ↦ hg

end SeparatedSum

end TauCeti
