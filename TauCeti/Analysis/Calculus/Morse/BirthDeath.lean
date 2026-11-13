/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.GradientFlow
public import TauCeti.Analysis.Calculus.Morse.OneDimensional
public import TauCeti.Analysis.Calculus.Morse.Prod
public import TauCeti.Analysis.SpecialFunctions.Artanh
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
of its derivative is `-1`. Varying `s` across `0` gives the complete critical-point and global
negative-gradient trajectory trichotomy for `x' = s - x²`:

* **Before the birth (`s < 0`):** `birthDeathPotential s` has no critical point, and every global
  negative gradient trajectory diverges to `-∞` at `+∞` and to `+∞` at `-∞`, so no global
  trajectory converges at either end
  (`TauCeti.tendsto_atTop_atBot_of_isIntegralCurve_birthDeathPotential_of_neg`,
  `TauCeti.tendsto_atBot_atTop_of_isIntegralCurve_birthDeathPotential_of_neg`).
* **At the birth–death instant (`s = 0`):** the origin is the unique critical point and is
  degenerate (`TauCeti.not_isNondegenerateCriticalPoint_birthDeathPotential_zero`), although the
  third derivative there and the parameter derivative of the derivative are nonzero, and the
  constant zero curve is the unique global negative gradient trajectory with finite limits at both
  ends (`TauCeti.eq_zero_of_isIntegralCurve_birthDeathPotential_zero`).
* **After the birth (`s > 0`):** there are two critical points, both nondegenerate: a local maximum
  at `-√s` of Morse index `1`, and a local minimum at `√s` of Morse index `0`, whose critical values
  differ by `4 s √s / 3`. Thus `birthDeathPotential s` has nondegenerate critical points on `ℝ` if
  and only if `s ≠ 0` (`TauCeti.hasNondegenerateCriticalPointsOn_birthDeathPotential_iff`).

For `s > 0`, the open interval `(-√s, √s)` is parametrized by the inverse-hyperbolic time coordinate
`x ↦ (√s)⁻¹ * artanh (x / √s)` (`TauCeti.birthDeathTimeCoordinate s`), inverse to the connecting
orbit `t ↦ √s tanh (√s t)` (`TauCeti.birthDeathOrbit s`). Every negative gradient trajectory from
`-√s` to `√s` stays inside `(-√s, √s)` and is a unique time translate
`t ↦ birthDeathOrbit s (t + τ)` with `τ = birthDeathTimeCoordinate s (γ 0)`
(`TauCeti.existsUnique_eq_birthDeathOrbit_comp_add`), while no negative gradient trajectory runs
from `√s` to `-√s` (`TauCeti.not_isIntegralCurve_birthDeathPotential_sqrt_to_neg_sqrt`).

**The model in higher dimensions.** Adding a function `g` with a nondegenerate critical point `y`
of Morse index `k` in transverse directions gives the separated sum
`(x, y) ↦ x³ / 3 - s x + g y`. For `s < 0` no trajectory converges at either end; for `s > 0` the
points `(-√s, y)` and `(√s, y)` are nondegenerate critical points of Morse indices `k + 1` and `k`,
every negative gradient trajectory from `(-√s, y)` to `(√s, y)` is a unique time translate
`t ↦ (√s tanh (√s (t + τ)), y)` (`TauCeti.existsUnique_eq_birthDeathOrbit_separatedSum`), and no
trajectory runs from `(√s, y)` to `(-√s, y)`. The explicit multi-dimensional Cerf normal form
obtained by taking `g = splitQuadratic` lives in
`TauCeti.Analysis.Calculus.Morse.BirthDeath.NormalForm`, and the `W^{1,2} → L²` Fredholm regularity
of the linearized trajectory operators lives in
`TauCeti.Analysis.Calculus.Morse.BirthDeath.Fredholm`.

## Main declarations

* `TauCeti.birthDeathPotential`: the cubic `x³ / 3 - s x`.
* `TauCeti.fderiv_birthDeathPotential_eq_zero_iff`,
  `TauCeti.isNondegenerateCriticalPoint_birthDeathPotential_iff`,
  `TauCeti.hasNondegenerateCriticalPointsOn_birthDeathPotential_iff`: critical-point and Morse
  characterization across `s`.
* `TauCeti.morseIndex_birthDeathPotential_neg_sqrt`, `TauCeti.morseIndex_birthDeathPotential_sqrt`:
  for `s > 0`, the two critical points have Morse indices `1` and `0`.
* `TauCeti.eq_of_isIntegralCurve_birthDeathPotential`,
  `TauCeti.tendsto_atTop_atBot_of_isIntegralCurve_birthDeathPotential_of_neg`,
  `TauCeti.eq_zero_of_isIntegralCurve_birthDeathPotential_zero`: global ODE uniqueness and the
  pre-birth (`s < 0`) and birth–death (`s = 0`) trajectory regimes.
* `TauCeti.birthDeathOrbit`, `TauCeti.birthDeathTimeCoordinate`,
  `TauCeti.isIntegralCurve_birthDeathOrbit`: the connecting trajectory `t ↦ √s tanh (√s t)` and its
  inverse `artanh` time coordinate on `(-√s, √s)`.
* `TauCeti.existsUnique_eq_birthDeathOrbit_comp_add`,
  `TauCeti.exists_eq_birthDeathOrbit_comp_add`,
  `TauCeti.not_isIntegralCurve_birthDeathPotential_sqrt_to_neg_sqrt`: unique time-shift
  classification of forward connecting orbits and nonexistence of reverse orbits.
* `TauCeti.morseIndex_separatedSum_birthDeathPotential_neg_sqrt`,
  `TauCeti.morseIndex_separatedSum_birthDeathPotential_sqrt`,
  `TauCeti.existsUnique_eq_birthDeathOrbit_separatedSum`,
  `TauCeti.exists_eq_birthDeathOrbit_separatedSum`: the corresponding statements in the model with
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

@[simp]
theorem birthDeathPotential_zero_right (s : ℝ) : birthDeathPotential s 0 = 0 := by
  simp [birthDeathPotential_apply]

/-- The birth–death potential is odd in the spatial variable: `f_s(-x) = -f_s(x)`. -/
theorem birthDeathPotential_neg (s x : ℝ) :
    birthDeathPotential s (-x) = -birthDeathPotential s x := by
  simp only [birthDeathPotential_apply]
  ring

/-- The birth–death potential is a polynomial in the variable, hence smooth. -/
@[fun_prop]
theorem contDiff_birthDeathPotential (s : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (birthDeathPotential s) := by
  unfold birthDeathPotential
  fun_prop

/-- The birth–death potential is jointly smooth in the parameter and the variable: it is a smooth
one-parameter family of functions. -/
@[fun_prop]
theorem contDiff_birthDeathPotential_uncurry {n : WithTop ℕ∞} :
    ContDiff ℝ n fun p : ℝ × ℝ ↦ birthDeathPotential p.1 p.2 := by
  unfold birthDeathPotential
  fun_prop

@[fun_prop]
theorem continuous_birthDeathPotential (s : ℝ) : Continuous (birthDeathPotential s) :=
  (contDiff_birthDeathPotential (n := 0) s).continuous

/-- The derivative of the birth–death potential is `x² - s`. -/
theorem hasDerivAt_birthDeathPotential (s x : ℝ) :
    HasDerivAt (birthDeathPotential s) (x ^ 2 - s) x := by
  refine (((hasDerivAt_pow 3 x).div_const 3).sub ((hasDerivAt_id' x).const_mul s)).congr_deriv ?_
  norm_num

@[fun_prop]
theorem differentiable_birthDeathPotential (s : ℝ) : Differentiable ℝ (birthDeathPotential s) :=
  fun x ↦ (hasDerivAt_birthDeathPotential s x).differentiableAt

@[simp]
theorem deriv_birthDeathPotential (s : ℝ) :
    deriv (birthDeathPotential s) = fun x ↦ x ^ 2 - s :=
  funext fun x ↦ (hasDerivAt_birthDeathPotential s x).deriv

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

/-- The Hessian operator of `birthDeathPotential s` at `x` is multiplication by `2 x`. -/
@[simp]
theorem hessianOperator_birthDeathPotential (s x : ℝ) :
    hessianOperator (birthDeathPotential s) x = (2 * x) • ContinuousLinearMap.id ℝ ℝ := by
  rw [hessianOperator_real, iteratedDeriv_two_birthDeathPotential]

/-- The Hessian quadratic form of `birthDeathPotential s` at `x` sends `v` to `2 x v²`. -/
theorem hessianQuadraticForm_birthDeathPotential_apply (s x v : ℝ) :
    hessianQuadraticForm (birthDeathPotential s) x v = 2 * x * v ^ 2 := by
  rw [hessianQuadraticForm_real_apply, iteratedDeriv_two_birthDeathPotential]

/-! ### Critical points -/

/-- **The critical points of the birth–death potential** are the solutions of `x² = s`. -/
theorem fderiv_birthDeathPotential_eq_zero_iff {x : ℝ} :
    fderiv ℝ (birthDeathPotential s) x = 0 ↔ x ^ 2 = s := by
  rw [← toSpanSingleton_deriv, deriv_birthDeathPotential]
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

/-- **Morse characterization of the birth–death family.** `birthDeathPotential s` has nondegenerate
critical points on all of `ℝ` if and only if `s ≠ 0`. -/
@[simp]
theorem hasNondegenerateCriticalPointsOn_birthDeathPotential_iff :
    HasNondegenerateCriticalPointsOn (birthDeathPotential s) univ ↔ s ≠ 0 := by
  refine ⟨fun h hs ↦ ?_, fun hs ↦ hasNondegenerateCriticalPointsOn_iff.2 fun x _ hx ↦ ?_⟩
  · subst hs
    exact not_isNondegenerateCriticalPoint_birthDeathPotential_zero
      (hasNondegenerateCriticalPointsOn_iff.1 h (mem_univ 0)
        (fderiv_birthDeathPotential_eq_zero_iff.2 (by norm_num)))
  · have hxsq : x ^ 2 = s := fderiv_birthDeathPotential_eq_zero_iff.1 hx
    refine isNondegenerateCriticalPoint_birthDeathPotential_iff.2 ⟨hxsq, ?_⟩
    rintro rfl
    exact hs (by simpa using hxsq.symm)

/-- After the birth, for `s > 0`, the nondegenerate critical points of the birth–death potential are
`-√s` and `√s`. -/
theorem isNondegenerateCriticalPoint_birthDeathPotential_iff_of_pos (hs : 0 < s) {x : ℝ} :
    IsNondegenerateCriticalPoint (birthDeathPotential s) x ↔ x = -√s ∨ x = √s := by
  have hsq := Real.sqrt_pos.2 hs
  rw [isNondegenerateCriticalPoint_birthDeathPotential_iff]
  constructor
  · rintro ⟨h, -⟩
    exact (sq_eq_sq_iff_eq_or_eq_neg.1 (h.trans (Real.sq_sqrt hs.le).symm)).symm
  · rintro (rfl | rfl) <;> refine ⟨by simp [Real.sq_sqrt hs.le], by linarith⟩

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

/-! ### Global ODE uniqueness and the regimes `s < 0` and `s = 0` -/

/-- **Global uniqueness for negative gradient trajectories of `birthDeathPotential s`.** Two global
solutions of `x' = s - x²` that agree at one time `t₀` coincide everywhere on `ℝ`. -/
theorem eq_of_isIntegralCurve_birthDeathPotential {γ₁ γ₂ : ℝ → ℝ}
    (h₁ : IsIntegralCurve γ₁ (fun _ x ↦ -∇ (birthDeathPotential s) x))
    (h₂ : IsIntegralCurve γ₂ (fun _ x ↦ -∇ (birthDeathPotential s) x))
    {t₀ : ℝ} (heq : γ₁ t₀ = γ₂ t₀) : γ₁ = γ₂ := by
  let V : (x : ℝ) → TangentSpace 𝓘(ℝ, ℝ) x := fun x ↦ -∇ (birthDeathPotential s) x
  have hV : ContDiff ℝ 1 V := by
    simp only [V, gradient_birthDeathPotential]
    fun_prop
  have hM : ∀ c : ℝ → ℝ, IsIntegralCurve c (fun _ x ↦ -∇ (birthDeathPotential s) x) →
      IsMIntegralCurve c V := fun c hc ↦ isMIntegralCurve_iff_isMIntegralCurveOn.2
    (isMIntegralCurveOn_iff_isIntegralCurveOn.2 (hc.isIntegralCurveOn _))
  exact isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (t₀ := t₀)
    (contMDiff_vectorSpace_iff_contDiff.2 hV) (hM γ₁ h₁) (hM γ₂ h₂) heq

/-- **Time-reversal symmetry of the birth–death ODE.** Since `birthDeathPotential s` is odd,
`t ↦ -γ (-t)` is a negative gradient trajectory whenever `γ` is. -/
theorem isIntegralCurve_neg_comp_neg_birthDeathPotential {γ : ℝ → ℝ}
    (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ (birthDeathPotential s) x)) :
    IsIntegralCurve (fun t ↦ -γ (-t)) (fun _ x ↦ -∇ (birthDeathPotential s) x) := fun t ↦ by
  refine (((hγ (-t)).comp t (hasDerivAt_id' t).neg).neg).congr_deriv ?_
  simp only [gradient_birthDeathPotential]
  ring

private theorem tendsto_const_sub_mul_atTop_atBot (A : ℝ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun t ↦ A - c * t) atTop atBot :=
  tendsto_atBot.2 fun B ↦ eventually_atTop.2
    ⟨(A - B) / c, fun _ ht ↦ by linarith [(div_le_iff₀ hc).1 ht]⟩

/-- **Before the birth (`s < 0`), every global trajectory diverges to `-∞` at `+∞`.** -/
theorem tendsto_atTop_atBot_of_isIntegralCurve_birthDeathPotential_of_neg (hs : s < 0)
    {γ : ℝ → ℝ} (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ (birthDeathPotential s) x)) :
    Tendsto γ atTop atBot := by
  have hd : ∀ t, HasDerivAt (fun u ↦ γ u - s * u) (-(γ t ^ 2)) t := fun t ↦ by
    have h₁ : HasDerivAt γ (-∇ (birthDeathPotential s) (γ t)) t := hγ t
    rw [gradient_birthDeathPotential] at h₁
    exact (h₁.sub ((hasDerivAt_id' t).const_mul s)).congr_deriv (by ring)
  have hant : Antitone (fun t ↦ γ t - s * t) :=
    antitone_of_hasDerivAt_nonpos hd fun _ ↦ neg_nonpos.2 (sq_nonneg _)
  refine tendsto_atBot_mono' atTop ?_ (tendsto_const_sub_mul_atTop_atBot (γ 0) (neg_pos.2 hs))
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  have h := hant ht
  dsimp only at h
  linarith

/-- **Before the birth (`s < 0`), every global trajectory diverges to `+∞` at `-∞`.** -/
theorem tendsto_atBot_atTop_of_isIntegralCurve_birthDeathPotential_of_neg (hs : s < 0)
    {γ : ℝ → ℝ} (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ (birthDeathPotential s) x)) :
    Tendsto γ atBot atTop := by
  have h := tendsto_neg_atBot_atTop.comp
    ((tendsto_atTop_atBot_of_isIntegralCurve_birthDeathPotential_of_neg hs
      (isIntegralCurve_neg_comp_neg_birthDeathPotential hγ)).comp tendsto_neg_atBot_atTop)
  simpa [Function.comp_def] using h

/-- For `s < 0`, no global negative gradient trajectory of `birthDeathPotential s` converges at
`+∞`. -/
theorem not_tendsto_atTop_nhds_of_isIntegralCurve_birthDeathPotential_of_neg (hs : s < 0)
    {γ : ℝ → ℝ} (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ (birthDeathPotential s) x)) (q : ℝ) :
    ¬Tendsto γ atTop (𝓝 q) := by
  intro hq
  have hbot := tendsto_atTop_atBot_of_isIntegralCurve_birthDeathPotential_of_neg hs hγ
  obtain ⟨t, ht1, ht2⟩ := ((hq.eventually (Ioi_mem_nhds (sub_one_lt q))).and
    (hbot.eventually (eventually_le_atBot (q - 2)))).exists
  linarith

/-- For `s < 0`, no global negative gradient trajectory of `birthDeathPotential s` converges at
`-∞`. -/
theorem not_tendsto_atBot_nhds_of_isIntegralCurve_birthDeathPotential_of_neg (hs : s < 0)
    {γ : ℝ → ℝ} (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ (birthDeathPotential s) x)) (p : ℝ) :
    ¬Tendsto γ atBot (𝓝 p) := by
  intro hp
  refine not_tendsto_atTop_nhds_of_isIntegralCurve_birthDeathPotential_of_neg hs
    (isIntegralCurve_neg_comp_neg_birthDeathPotential hγ) (-p) ?_
  simpa [Function.comp_def] using (hp.comp tendsto_neg_atTop_atBot).neg

private theorem eq_zero_of_tendsto_atTop_birthDeathPotential_zero {γ : ℝ → ℝ}
    (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ (birthDeathPotential 0) x)) {q : ℝ}
    (htop : Tendsto γ atTop (𝓝 q)) : q = 0 := by
  by_contra hq
  have hqpos : 0 < |q| / 2 := half_pos (abs_pos.2 hq)
  set c := (|q| / 2) ^ 2
  have hc : 0 < c := sq_pos_of_pos hqpos
  obtain ⟨S, hS⟩ := eventually_atTop.1
    (htop.abs.eventually (Ioi_mem_nhds (half_lt_self (abs_pos.2 hq))))
  have hd : ∀ t ∈ Ici S, HasDerivAt (fun u ↦ γ u + c * u) (-(γ t ^ 2) + c) t := fun t _ ↦ by
    have h₁ : HasDerivAt γ (-∇ (birthDeathPotential 0) (γ t)) t := hγ t
    rw [gradient_birthDeathPotential, sub_zero] at h₁
    exact (h₁.add ((hasDerivAt_id' t).const_mul c)).congr_deriv (by ring)
  have hant : AntitoneOn (fun u ↦ γ u + c * u) (Ici S) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici S)
      (fun t ht ↦ (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht ↦ (hd t (interior_subset ht)).hasDerivWithinAt) fun t ht ↦ ?_
    have hlt : |q| / 2 < |γ t| := hS t (interior_subset ht)
    have hsq : c ≤ γ t ^ 2 := by
      rw [← sq_abs (γ t)]
      exact pow_le_pow_left₀ hqpos.le hlt.le 2
    linarith
  have hbot : Tendsto γ atTop atBot := by
    refine tendsto_atBot_mono' atTop ?_ (tendsto_const_sub_mul_atTop_atBot (γ S + c * S) hc)
    filter_upwards [eventually_ge_atTop S] with t ht
    have h := hant self_mem_Ici ht ht
    dsimp only at h
    linarith
  obtain ⟨t, ht1, ht2⟩ := ((htop.eventually (Ioi_mem_nhds (sub_one_lt q))).and
    (hbot.eventually (eventually_le_atBot (q - 2)))).exists
  linarith

/-- **At the birth–death instant `s = 0`, the constant zero trajectory is the unique global
connecting trajectory.** Any global negative gradient trajectory of `birthDeathPotential 0` with
finite limits `p` and `q` at `-∞` and `+∞` satisfies `p = 0`, `q = 0`, and `γ = 0`. -/
theorem eq_zero_of_isIntegralCurve_birthDeathPotential_zero {γ : ℝ → ℝ}
    (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ (birthDeathPotential 0) x)) {p q : ℝ}
    (hbot : Tendsto γ atBot (𝓝 p)) (htop : Tendsto γ atTop (𝓝 q)) :
    p = 0 ∧ q = 0 ∧ γ = 0 := by
  have hp : p = 0 := neg_eq_zero.1 <| eq_zero_of_tendsto_atTop_birthDeathPotential_zero
    (isIntegralCurve_neg_comp_neg_birthDeathPotential hγ)
    (by simpa [Function.comp_def] using (hbot.comp tendsto_neg_atTop_atBot).neg)
  have hq : q = 0 := eq_zero_of_tendsto_atTop_birthDeathPotential_zero hγ htop
  subst hp hq
  exact ⟨rfl, rfl, hγ.eq_const_of_tendsto (fun _ ↦ differentiable_birthDeathPotential 0 _)
    (continuous_birthDeathPotential 0).continuousAt hbot htop⟩

/-! ### The connecting trajectory and its inverse time coordinate -/

/-- The negative gradient trajectory `t ↦ √s tanh (√s t)` of the birth–death potential. For
`s > 0` it runs from the local maximum `-√s` to the local minimum `√s`, and every trajectory
between them is a unique time translate (`TauCeti.existsUnique_eq_birthDeathOrbit_comp_add`). -/
noncomputable def birthDeathOrbit (s t : ℝ) : ℝ :=
  √s * Real.tanh (√s * t)

theorem birthDeathOrbit_apply (s t : ℝ) :
    birthDeathOrbit s t = √s * Real.tanh (√s * t) := (rfl)

@[simp]
theorem birthDeathOrbit_zero (s : ℝ) : birthDeathOrbit s 0 = 0 := by
  simp [birthDeathOrbit_apply]

@[simp]
theorem birthDeathOrbit_neg (s t : ℝ) : birthDeathOrbit s (-t) = -birthDeathOrbit s t := by
  simp [birthDeathOrbit_apply, Real.tanh_neg]

@[fun_prop]
theorem contDiff_birthDeathOrbit (s : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (birthDeathOrbit s) := by
  unfold birthDeathOrbit
  exact contDiff_const.mul (Real.contDiff_tanh.comp (contDiff_const.mul contDiff_id))

/-- For `s > 0`, `birthDeathOrbit s` is strictly increasing. -/
theorem strictMono_birthDeathOrbit (hs : 0 < s) : StrictMono (birthDeathOrbit s) := by
  have hsq := Real.sqrt_pos.2 hs
  exact fun _ _ htu ↦
    mul_lt_mul_of_pos_left (Real.tanh_strictMono (mul_lt_mul_of_pos_left htu hsq)) hsq

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

/-- The inverse-hyperbolic time coordinate `x ↦ (√s)⁻¹ * artanh (x / √s)` on `(-√s, √s)`, inverse
to `TauCeti.birthDeathOrbit s` for `s > 0`. -/
noncomputable def birthDeathTimeCoordinate (s x : ℝ) : ℝ :=
  (√s)⁻¹ * Real.artanh (x / √s)

theorem birthDeathTimeCoordinate_apply (s x : ℝ) :
    birthDeathTimeCoordinate s x = (√s)⁻¹ * Real.artanh (x / √s) := (rfl)

@[simp]
theorem birthDeathTimeCoordinate_zero_right (s : ℝ) : birthDeathTimeCoordinate s 0 = 0 := by
  simp [birthDeathTimeCoordinate_apply]

@[simp]
theorem birthDeathTimeCoordinate_neg_right (s x : ℝ) :
    birthDeathTimeCoordinate s (-x) = -birthDeathTimeCoordinate s x := by
  simp [birthDeathTimeCoordinate_apply, neg_div, Real.artanh_neg_eq_neg_artanh]

@[simp]
theorem birthDeathTimeCoordinate_birthDeathOrbit (hs : 0 < s) (t : ℝ) :
    birthDeathTimeCoordinate s (birthDeathOrbit s t) = t := by
  have ha : √s ≠ 0 := (Real.sqrt_pos.2 hs).ne'
  rw [birthDeathTimeCoordinate_apply, birthDeathOrbit_apply, mul_div_cancel_left₀ _ ha,
    Real.artanh_tanh, inv_mul_cancel_left₀ ha]

@[simp]
theorem birthDeathOrbit_birthDeathTimeCoordinate (hs : 0 < s) {x : ℝ}
    (hx : x ∈ Ioo (-√s) √s) :
    birthDeathOrbit s (birthDeathTimeCoordinate s x) = x := by
  have ha : 0 < √s := Real.sqrt_pos.2 hs
  have hx' : x / √s ∈ Ioo (-1 : ℝ) 1 :=
    ⟨(lt_div_iff₀ ha).2 (by linarith [hx.1]), (div_lt_iff₀ ha).2 (by linarith [hx.2])⟩
  rw [birthDeathOrbit_apply, birthDeathTimeCoordinate_apply, mul_inv_cancel_left₀ ha.ne',
    Real.tanh_artanh hx', mul_div_cancel₀ _ ha.ne']

/-- For `s > 0`, `birthDeathTimeCoordinate s` is an order-preserving bijection from `(-√s, √s)` onto
`ℝ`. -/
theorem bijOn_birthDeathTimeCoordinate (hs : 0 < s) :
    BijOn (birthDeathTimeCoordinate s) (Ioo (-√s) √s) univ := by
  refine ⟨mapsTo_univ _ _, fun x hx y hy hxy ↦ ?_,
    fun t _ ↦ ⟨birthDeathOrbit s t, birthDeathOrbit_mem_Ioo hs t,
      birthDeathTimeCoordinate_birthDeathOrbit hs t⟩⟩
  rw [← birthDeathOrbit_birthDeathTimeCoordinate hs hx,
    ← birthDeathOrbit_birthDeathTimeCoordinate hs hy, hxy]

theorem strictMonoOn_birthDeathTimeCoordinate (hs : 0 < s) :
    StrictMonoOn (birthDeathTimeCoordinate s) (Ioo (-√s) √s) := by
  have ha : 0 < √s := Real.sqrt_pos.2 hs
  intro x hx y hy hxy
  have hx' : x / √s ∈ Ioo (-1 : ℝ) 1 :=
    ⟨(lt_div_iff₀ ha).2 (by linarith [hx.1]), (div_lt_iff₀ ha).2 (by linarith [hx.2])⟩
  have hy' : y / √s ∈ Ioo (-1 : ℝ) 1 :=
    ⟨(lt_div_iff₀ ha).2 (by linarith [hy.1]), (div_lt_iff₀ ha).2 (by linarith [hy.2])⟩
  exact mul_lt_mul_of_pos_left
    (Real.strictMonoOn_artanh hx' hy' ((div_lt_div_iff_of_pos_right ha).2 hxy)) (inv_pos.2 ha)

/-- On `(-√s, √s)` (`s > 0`), `birthDeathTimeCoordinate s` has derivative `(s - x²)⁻¹`, reciprocal
to the negative-gradient speed `s - x²`. -/
theorem hasDerivAt_birthDeathTimeCoordinate (hs : 0 < s) {x : ℝ} (hx : x ∈ Ioo (-√s) √s) :
    HasDerivAt (birthDeathTimeCoordinate s) ((s - x ^ 2)⁻¹) x := by
  set a := √s
  have ha : 0 < a := Real.sqrt_pos.2 hs
  have hasq : a ^ 2 = s := Real.sq_sqrt hs.le
  have hx' : x / a ∈ Ioo (-1 : ℝ) 1 :=
    ⟨(lt_div_iff₀ ha).2 (by linarith [hx.1]), (div_lt_iff₀ ha).2 (by linarith [hx.2])⟩
  have hd := (((hasDerivAt_id' x).div_const a).artanh hx').const_mul a⁻¹
  refine hd.congr_deriv ?_
  have ha0 : a ≠ 0 := ha.ne'
  have hsub : a ^ 2 - x ^ 2 ≠ 0 := sub_ne_zero.2 (by nlinarith [hx.1, hx.2])
  have h1 : 1 - (x / a) ^ 2 = (a ^ 2 - x ^ 2) / a ^ 2 := by field_simp
  rw [h1, ← hasq]
  field_simp

/-- **Unique time-shift classification of the connecting trajectory.** For `s > 0`, every negative
gradient trajectory of `birthDeathPotential s` from `-√s` to `√s` is `t ↦ birthDeathOrbit s (t + τ)`
for a *unique* time shift `τ = birthDeathTimeCoordinate s (γ 0)`. -/
theorem existsUnique_eq_birthDeathOrbit_comp_add (hs : 0 < s) {γ : ℝ → ℝ}
    (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ (birthDeathPotential s) x))
    (hbot : Tendsto γ atBot (𝓝 (-√s))) (htop : Tendsto γ atTop (𝓝 √s)) :
    ∃! τ, γ = fun t ↦ birthDeathOrbit s (t + τ) := by
  have hsq := Real.sqrt_pos.2 hs
  -- The trajectory crosses `0`, by the intermediate value theorem.
  obtain ⟨a, ha⟩ := (hbot.eventually (gt_mem_nhds (neg_lt_zero.2 hsq))).exists
  obtain ⟨b, hb⟩ := (htop.eventually (lt_mem_nhds hsq)).exists
  obtain ⟨t₀, ht₀⟩ := intermediate_value_univ a b
    (continuous_iff_continuousAt.2 fun t ↦ (hγ t).continuousAt) ⟨ha.le, hb.le⟩
  have hδ : IsIntegralCurve (fun t ↦ birthDeathOrbit s (t + -t₀))
      (fun _ x ↦ -∇ (birthDeathPotential s) x) := fun t ↦
    (isIntegralCurve_birthDeathOrbit hs.le (t + -t₀)).comp_add_const t (-t₀)
  refine ⟨-t₀, eq_of_isIntegralCurve_birthDeathPotential hγ hδ (t₀ := t₀) (by simp [ht₀]),
    fun τ hτ ↦ ?_⟩
  have hval := congrArg (birthDeathTimeCoordinate s) (congrFun hτ (-t₀))
  have hval0 : γ (-t₀) = birthDeathOrbit s (-t₀ + -t₀) :=
    congrFun (eq_of_isIntegralCurve_birthDeathPotential hγ hδ (t₀ := t₀) (by simp [ht₀])) (-t₀)
  rw [hval0, birthDeathTimeCoordinate_birthDeathOrbit hs,
    birthDeathTimeCoordinate_birthDeathOrbit hs] at hval
  linarith

/-- **Uniqueness of the connecting trajectory.** For `s > 0`, every negative gradient trajectory
of the birth–death potential from the local maximum `-√s` to the local minimum `√s` is a time
translate of `TauCeti.birthDeathOrbit s`. So the two critical points born at `s = 0` are joined by
exactly one unparametrized trajectory. -/
theorem exists_eq_birthDeathOrbit_comp_add (hs : 0 < s) {γ : ℝ → ℝ}
    (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ (birthDeathPotential s) x))
    (hbot : Tendsto γ atBot (𝓝 (-√s))) (htop : Tendsto γ atTop (𝓝 √s)) :
    ∃ τ, γ = fun t ↦ birthDeathOrbit s (t + τ) :=
  (existsUnique_eq_birthDeathOrbit_comp_add hs hγ hbot htop).exists

/-- For `s > 0`, every negative gradient trajectory of `birthDeathPotential s` from `-√s` to `√s`
stays strictly inside `(-√s, √s)`. -/
theorem mem_Ioo_of_isIntegralCurve_birthDeathPotential (hs : 0 < s) {γ : ℝ → ℝ}
    (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ (birthDeathPotential s) x))
    (hbot : Tendsto γ atBot (𝓝 (-√s))) (htop : Tendsto γ atTop (𝓝 √s)) (t : ℝ) :
    γ t ∈ Ioo (-√s) √s := by
  obtain ⟨τ, rfl⟩ := exists_eq_birthDeathOrbit_comp_add hs hγ hbot htop
  exact birthDeathOrbit_mem_Ioo hs (t + τ)

/-- **No reverse connecting trajectory exists.** For `s > 0`, no negative gradient trajectory of
`birthDeathPotential s` runs from `√s` at `-∞` to `-√s` at `+∞`. -/
theorem not_isIntegralCurve_birthDeathPotential_sqrt_to_neg_sqrt (hs : 0 < s) {γ : ℝ → ℝ}
    (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ (birthDeathPotential s) x))
    (hbot : Tendsto γ atBot (𝓝 √s)) (htop : Tendsto γ atTop (𝓝 (-√s))) : False := by
  have hant : Antitone (birthDeathPotential s ∘ γ) :=
    hγ.antitone_comp_neg_gradient fun t ↦ differentiable_birthDeathPotential s (γ t)
  have hfbot : Tendsto (birthDeathPotential s ∘ γ) atBot (𝓝 (birthDeathPotential s √s)) :=
    ((continuous_birthDeathPotential s).tendsto √s).comp hbot
  have hftop : Tendsto (birthDeathPotential s ∘ γ) atTop (𝓝 (birthDeathPotential s (-√s))) :=
    ((continuous_birthDeathPotential s).tendsto (-√s)).comp htop
  have hle0 : birthDeathPotential s (γ 0) ≤ birthDeathPotential s √s :=
    hant.ge_of_tendsto hfbot 0
  have hge0 : birthDeathPotential s (-√s) ≤ birthDeathPotential s (γ 0) :=
    hant.le_of_tendsto hftop 0
  have hineq : birthDeathPotential s (-√s) ≤ birthDeathPotential s √s := hge0.trans hle0
  rw [birthDeathPotential_neg_sqrt, birthDeathPotential_sqrt] at hineq
  have hmul : 0 < s * √s := mul_pos hs (Real.sqrt_pos.2 hs)
  linarith

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

/-- Before the birth (`s < 0`), no global negative gradient trajectory of
`separatedSum (birthDeathPotential s) g` converges at `+∞`. -/
theorem not_tendsto_atTop_nhds_of_isIntegralCurve_separatedSum_birthDeathPotential_of_neg
    [CompleteSpace F] (hs : s < 0) (hg : Differentiable ℝ g) {z : ℝ → WithLp 2 (ℝ × F)}
    (hz : IsIntegralCurve z (fun _ w ↦ -∇ (separatedSum (birthDeathPotential s) g) w))
    (q : WithLp 2 (ℝ × F)) : ¬Tendsto z atTop (𝓝 q) := fun hq ↦
  not_tendsto_atTop_nhds_of_isIntegralCurve_birthDeathPotential_of_neg hs
    ((isIntegralCurve_separatedSum_iff
      (fun _ ↦ differentiable_birthDeathPotential s _) fun _ ↦ hg _).1 hz).1 q.fst
    (((WithLp.fstL 2 ℝ ℝ F).continuous.tendsto q).comp hq)

/-- Before the birth (`s < 0`), no global negative gradient trajectory of
`separatedSum (birthDeathPotential s) g` converges at `-∞`. -/
theorem not_tendsto_atBot_nhds_of_isIntegralCurve_separatedSum_birthDeathPotential_of_neg
    [CompleteSpace F] (hs : s < 0) (hg : Differentiable ℝ g) {z : ℝ → WithLp 2 (ℝ × F)}
    (hz : IsIntegralCurve z (fun _ w ↦ -∇ (separatedSum (birthDeathPotential s) g) w))
    (p : WithLp 2 (ℝ × F)) : ¬Tendsto z atBot (𝓝 p) := fun hp ↦
  not_tendsto_atBot_nhds_of_isIntegralCurve_birthDeathPotential_of_neg hs
    ((isIntegralCurve_separatedSum_iff
      (fun _ ↦ differentiable_birthDeathPotential s _) fun _ ↦ hg _).1 hz).1 p.fst
    (((WithLp.fstL 2 ℝ ℝ F).continuous.tendsto p).comp hp)

/-- **Unique time-shift classification in the model with transverse directions.** Let `g` be
differentiable. For `s > 0`, every negative gradient trajectory of
`(x, y) ↦ x³ / 3 - s x + g y` from `(-√s, y)` to `(√s, y)` is
`t ↦ (√s tanh (√s (t + τ)), y)` for a *unique* time shift `τ`. -/
theorem existsUnique_eq_birthDeathOrbit_separatedSum [CompleteSpace F] (hs : 0 < s)
    (hg : Differentiable ℝ g) {z : ℝ → WithLp 2 (ℝ × F)}
    (hz : IsIntegralCurve z (fun _ w ↦ -∇ (separatedSum (birthDeathPotential s) g) w))
    (hbot : Tendsto z atBot (𝓝 (WithLp.toLp 2 (-√s, y))))
    (htop : Tendsto z atTop (𝓝 (WithLp.toLp 2 (√s, y)))) :
    ∃! τ, z = fun t ↦ WithLp.toLp 2 (birthDeathOrbit s (t + τ), y) := by
  obtain ⟨h₁, h₂⟩ := (isIntegralCurve_separatedSum_iff
    (fun _ ↦ differentiable_birthDeathPotential s _) fun _ ↦ hg _).1 hz
  have hfst := (WithLp.fstL 2 ℝ ℝ F).continuous.tendsto
  have hsnd := (WithLp.sndL 2 ℝ ℝ F).continuous.tendsto
  have hy := h₂.eq_const_of_tendsto (fun _ ↦ hg _) (hg y).continuousAt
    (by simpa [Function.comp_def] using (hsnd _).comp hbot)
    (by simpa [Function.comp_def] using (hsnd _).comp htop)
  obtain ⟨τ, hτ, huniq⟩ := existsUnique_eq_birthDeathOrbit_comp_add hs h₁
    (by simpa [Function.comp_def] using (hfst _).comp hbot)
    (by simpa [Function.comp_def] using (hfst _).comp htop)
  refine ⟨τ, funext fun t ↦ WithLp.ofLp_injective 2 (Prod.ext ?_ ?_), fun τ' hτ' ↦ huniq τ' ?_⟩
  · simpa using congrFun hτ t
  · simpa using congrFun hy t
  · funext t
    simpa using congrArg WithLp.fst (congrFun hτ' t)

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
  (existsUnique_eq_birthDeathOrbit_separatedSum hs hg hz hbot htop).exists

/-- Conversely, above a critical point `y` of a transverse function `g` differentiable at `y`, the
curve `t ↦ (√s tanh (√s t), y)` is a negative gradient trajectory of the birth–death model. -/
theorem isIntegralCurve_birthDeathOrbit_separatedSum [CompleteSpace F] (hs : 0 ≤ s)
    (hg : DifferentiableAt ℝ g y) (hy : ∇ g y = 0) :
    IsIntegralCurve (fun t ↦ WithLp.toLp 2 (birthDeathOrbit s t, y))
      (fun _ w ↦ -∇ (separatedSum (birthDeathPotential s) g) w) :=
  (isIntegralCurve_birthDeathOrbit hs).separatedSum (isIntegralCurve_const_neg_gradient_iff.2 hy)
    (fun _ ↦ differentiable_birthDeathPotential s _) fun _ ↦ hg

/-- For `s > 0` and differentiable `g`, no negative gradient trajectory of
`separatedSum (birthDeathPotential s) g` runs from `(√s, y)` to `(-√s, y)`. -/
theorem not_isIntegralCurve_separatedSum_birthDeathPotential_sqrt_to_neg_sqrt [CompleteSpace F]
    (hs : 0 < s) (hg : Differentiable ℝ g) {z : ℝ → WithLp 2 (ℝ × F)}
    (hz : IsIntegralCurve z (fun _ w ↦ -∇ (separatedSum (birthDeathPotential s) g) w))
    (hbot : Tendsto z atBot (𝓝 (WithLp.toLp 2 (√s, y))))
    (htop : Tendsto z atTop (𝓝 (WithLp.toLp 2 (-√s, y)))) : False := by
  have hfst := (WithLp.fstL 2 ℝ ℝ F).continuous.tendsto
  exact not_isIntegralCurve_birthDeathPotential_sqrt_to_neg_sqrt hs
    ((isIntegralCurve_separatedSum_iff
      (fun _ ↦ differentiable_birthDeathPotential s _) fun _ ↦ hg _).1 hz).1
    (by simpa [Function.comp_def] using (hfst _).comp hbot)
    (by simpa [Function.comp_def] using (hfst _).comp htop)

end SeparatedSum

end TauCeti

end
