/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Topology.Maps.Proper.CompactlyGenerated
public import TauCeti.Analysis.Calculus.Morse.FlowExistence
public import TauCeti.Analysis.Calculus.Morse.OneDimensional
public import TauCeti.Geometry.Manifold.Flow.Damping

/-!
# Properness, lower bounds and completeness on the real line

Morse theory on a noncompact manifold needs global hypotheses on the function and on its
negative gradient flow, and three natural ones are logically independent. This file separates them
with three functions on `ℝ`, none of which is covered by the compact theory.

* `f(x) = x` is a proper map that is not bounded below. It has no critical point, while
  `H₀(ℝ; ℤ) = ℤ`, and none of its sublevel sets is compact.
* `f(x) = arctan x + π / 2` is bounded below, with values in `(0, π)`
  (`TauCeti.NoncompactLineExample.arctan_add_pi_div_two_mem_Ioo`), but it is not a proper map
  (`TauCeti.NoncompactLineExample.not_isProperMap_arctan_add_pi_div_two`). It has no critical point
  either. Its sublevel sets are empty at levels `a ≤ 0`, the half-lines `(-∞, tan (a - π / 2)]` for
  `0 < a < π` and the whole line for `a ≥ π`, so none of the nonempty ones is compact
  (`TauCeti.NoncompactLineExample.not_isCompact_setOf_arctan_add_pi_div_two_le`).
* `f(x) = x² + x⁴` is bounded below, has compact sublevel sets
  (`TauCeti.NoncompactLineExample.isCompact_setOf_sq_add_pow_four_le`), so it is a proper map
  (`TauCeti.NoncompactLineExample.isProperMap_sq_add_pow_four`), and has a single critical point,
  the nondegenerate minimum `0` (`TauCeti.NoncompactLineExample.deriv_sq_add_pow_four_eq_zero_iff`,
  `TauCeti.NoncompactLineExample.isNondegenerateCriticalPoint_sq_add_pow_four`). Yet its negative
  gradient flow `x' = -(2 x + 4 x³)` is not complete: the trajectory through `1` escapes to
  infinity in finite backward time. Along a trajectory `γ` avoiding `0`, the function `y = γ⁻²`
  solves the linear equation `y' = 4 y + 8`, so `(y + 2) e^{-4t}` is constant. Starting from
  `y(0) = 1`, this forces `y(t) = 3 e^{4t} - 2`, which reaches `0` at `t = log (2 / 3) / 4`, and
  the trajectory through `1` is the curve `t ↦ (3 e^{4t} - 2)^{-1/2}`
  (`TauCeti.NoncompactLineExample.escapeCurve`). A trajectory through `1` exists on `[T, 0]`
  exactly when `log (2 / 3) / 4 < T`
  (`TauCeti.NoncompactLineExample.exists_isIntegralCurveOn_Icc_iff`). Consequently `x² + x⁴` has no
  negative gradient flow at all
  (`TauCeti.NoncompactLineExample.not_isNegativeGradient_sq_add_pow_four`), and its gradient is not
  globally Lipschitz (`TauCeti.NoncompactLineExample.not_lipschitzWith_gradient_sq_add_pow_four`):
  compact sublevels and a lower bound do not replace the global Lipschitz hypothesis of
  `TauCeti.negativeGradientFlow`.

Any comparison of Morse homology with the homology of a noncompact manifold therefore has to state
its properness, lower-bound and completeness hypotheses separately, or construct a complete
pseudo-gradient instead of the gradient. Properness is enough for the latter: damping the
negative gradient by the factor `TauCeti.rateDamping` of `df(-f') = -f'²`, which leaves it
unchanged where `f'² ≤ 1`, gives a complete field with the same trajectories
(`TauCeti.NoncompactLineExample.isCompleteVectorField_rateDampedField_sq_add_pow_four`).

## Main results

* `TauCeti.NoncompactLineExample.not_isProperMap_arctan_add_pi_div_two`: `arctan x + π / 2` is not
  proper.
* `TauCeti.NoncompactLineExample.not_isCompact_setOf_arctan_add_pi_div_two_le`: none of its
  nonempty sublevel sets is compact.
* `TauCeti.NoncompactLineExample.isCompact_setOf_sq_add_pow_four_le`,
  `TauCeti.NoncompactLineExample.isProperMap_sq_add_pow_four`: the sublevel sets of `x² + x⁴` are
  compact, and it is a proper map.
* `TauCeti.NoncompactLineExample.isNondegenerateCriticalPoint_sq_add_pow_four`: its only critical
  point `0` is nondegenerate.
* `TauCeti.NoncompactLineExample.log_div_four_lt_of_isIntegralCurveOn`: a negative gradient
  trajectory of `x² + x⁴` through `1` defined on `[T, 0]` has `log (2 / 3) / 4 < T`.
* `TauCeti.NoncompactLineExample.tendsto_escapeCurve`: the trajectory through `1` tends to `∞` as
  `t` decreases to `log (2 / 3) / 4`.
* `TauCeti.NoncompactLineExample.exists_isIntegralCurveOn_Icc_iff`: a trajectory through `1`
  exists on `[T, 0]` exactly when `log (2 / 3) / 4 < T`.
* `TauCeti.NoncompactLineExample.not_isNegativeGradient_sq_add_pow_four`: `x² + x⁴` has no negative
  gradient flow.
* `TauCeti.NoncompactLineExample.isCompleteVectorField_rateDampedField_sq_add_pow_four`: its damped
  negative gradient is complete.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 2 (pseudo-gradient fields and the completeness of their flows).
-/

public section

noncomputable section

open Filter Real Set Topology
open scoped Gradient NNReal

namespace TauCeti.NoncompactLineExample

/-! ### `f(x) = x`: proper, but not bounded below -/

/-- `f(x) = x` is a proper map. -/
example : IsProperMap fun x : ℝ ↦ x := isProperMap_id

/-- `f(x) = x` is not bounded below. -/
example : ¬BddBelow (range fun x : ℝ ↦ x) := by
  simp

/-- `f(x) = x` has no critical point. -/
example (x : ℝ) : deriv (fun x : ℝ ↦ x) x ≠ 0 := by
  simp

/-- No sublevel set of `f(x) = x` is compact. -/
example (a : ℝ) : ¬IsCompact {x : ℝ | x ≤ a} :=
  fun h ↦ not_bddBelow_Iic a h.bddBelow

/-! ### `f(x) = arctan x + π / 2`: bounded below, but not proper -/

/-- `arctan x + π / 2` takes its values in `(0, π)`; in particular it is bounded below. -/
theorem arctan_add_pi_div_two_mem_Ioo (x : ℝ) : arctan x + π / 2 ∈ Ioo 0 π := by
  constructor <;> linarith [neg_pi_div_two_lt_arctan x, arctan_lt_pi_div_two x]

/-- `arctan x + π / 2` has no critical point: its derivative is `1 / (1 + x²)`. -/
theorem deriv_arctan_add_pi_div_two_ne_zero (x : ℝ) :
    deriv (fun x ↦ arctan x + π / 2) x ≠ 0 := by
  rw [((hasDerivAt_arctan x).add_const _).deriv]
  positivity

/-- **`arctan x + π / 2` is not a proper map**: the preimage of the compact interval `[0, π]` is the
whole line. -/
theorem not_isProperMap_arctan_add_pi_div_two : ¬IsProperMap fun x : ℝ ↦ arctan x + π / 2 := by
  intro h
  have hpre : (fun x : ℝ ↦ arctan x + π / 2) ⁻¹' Icc 0 π = univ :=
    eq_univ_of_forall fun x ↦ Ioo_subset_Icc_self (arctan_add_pi_div_two_mem_Ioo x)
  exact noncompact_univ ℝ (hpre ▸ h.isCompact_preimage isCompact_Icc)

/-- At a level `a ≤ 0` the sublevel set of `arctan x + π / 2` is empty. -/
theorem setOf_arctan_add_pi_div_two_le_of_nonpos {a : ℝ} (ha : a ≤ 0) :
    {x : ℝ | arctan x + π / 2 ≤ a} = ∅ :=
  eq_empty_of_forall_notMem fun x hx ↦ (arctan_add_pi_div_two_mem_Ioo x).1.not_ge (hx.trans ha)

/-- At a level `0 < a < π` the sublevel set of `arctan x + π / 2` is the half-line
`(-∞, tan (a - π / 2)]`. -/
theorem setOf_arctan_add_pi_div_two_le {a : ℝ} (ha₀ : 0 < a) (haπ : a < π) :
    {x : ℝ | arctan x + π / 2 ≤ a} = Iic (tan (a - π / 2)) := by
  have key : ∀ x, x ≤ tan (a - π / 2) ↔ arctan x ≤ a - π / 2 := fun x ↦ by
    rw [← arctan_strictMono.le_iff_le, arctan_tan (by linarith) (by linarith)]
  ext x
  rw [mem_ofPred_eq, mem_Iic, key]
  constructor <;> intro h <;> linarith

/-- At a level `a ≥ π` the sublevel set of `arctan x + π / 2` is the whole line. -/
theorem setOf_arctan_add_pi_div_two_le_of_pi_le {a : ℝ} (ha : π ≤ a) :
    {x : ℝ | arctan x + π / 2 ≤ a} = univ :=
  eq_univ_of_forall fun x ↦ (arctan_add_pi_div_two_mem_Ioo x).2.le.trans ha

/-- **No nonempty sublevel set of `arctan x + π / 2` is compact**: at every level `a > 0` the
sublevel set is unbounded below. -/
theorem not_isCompact_setOf_arctan_add_pi_div_two_le {a : ℝ} (ha : 0 < a) :
    ¬IsCompact {x : ℝ | arctan x + π / 2 ≤ a} := by
  intro h
  rcases lt_or_ge a π with haπ | haπ
  · rw [setOf_arctan_add_pi_div_two_le ha haπ] at h
    exact not_bddBelow_Iic _ h.bddBelow
  · rw [setOf_arctan_add_pi_div_two_le_of_pi_le haπ] at h
    exact not_bddBelow_univ h.bddBelow

/-! ### `f(x) = x² + x⁴`: proper and bounded below, but with an incomplete gradient flow -/

/-- The derivative of `x² + x⁴` is `2 x + 4 x³`. -/
theorem hasDerivAt_sq_add_pow_four (x : ℝ) :
    HasDerivAt (fun x : ℝ ↦ x ^ 2 + x ^ 4) (2 * x + 4 * x ^ 3) x := by
  convert (hasDerivAt_pow 2 x).add (hasDerivAt_pow 4 x) using 1
  ring

/-- The gradient of `x² + x⁴` is `2 x + 4 x³`. -/
theorem gradient_sq_add_pow_four (x : ℝ) : ∇ (fun x : ℝ ↦ x ^ 2 + x ^ 4) x = 2 * x + 4 * x ^ 3 := by
  rw [gradient_eq_deriv', (hasDerivAt_sq_add_pow_four x).deriv]

/-- `x² + x⁴` is bounded below by `0`. -/
example (x : ℝ) : 0 ≤ x ^ 2 + x ^ 4 := by
  positivity

/-- **The sublevel sets of `x² + x⁴` are compact.** -/
theorem isCompact_setOf_sq_add_pow_four_le (a : ℝ) : IsCompact {x : ℝ | x ^ 2 + x ^ 4 ≤ a} := by
  refine (isCompact_Icc (a := -(a + 1)) (b := a + 1)).of_isClosed_subset
    (isClosed_le (by fun_prop) continuous_const) fun x (hx : x ^ 2 + x ^ 4 ≤ a) ↦ ?_
  constructor <;> nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (x + 1 / 2), sq_nonneg (x ^ 2)]

/-- **`x² + x⁴` is a proper map**: the preimage of a compact set lies in a compact sublevel set. -/
theorem isProperMap_sq_add_pow_four : IsProperMap fun x : ℝ ↦ x ^ 2 + x ^ 4 := by
  refine isProperMap_iff_isCompact_preimage.2 ⟨by fun_prop, fun K hK ↦ ?_⟩
  obtain ⟨a, ha⟩ := hK.bddAbove
  exact (isCompact_setOf_sq_add_pow_four_le a).of_isClosed_subset
    (hK.isClosed.preimage (by fun_prop)) fun x hx ↦ ha hx

/-- **The only critical point of `x² + x⁴` is `0`.** -/
theorem deriv_sq_add_pow_four_eq_zero_iff {x : ℝ} :
    deriv (fun x : ℝ ↦ x ^ 2 + x ^ 4) x = 0 ↔ x = 0 := by
  rw [(hasDerivAt_sq_add_pow_four x).deriv]
  constructor
  · intro h
    have : x * (2 + 4 * x ^ 2) = 0 := by linear_combination h
    exact (mul_eq_zero.1 this).resolve_right (by positivity)
  · rintro rfl
    simp

/-- The second derivative of `x² + x⁴` at `0` is `2`. -/
theorem iteratedDeriv_two_sq_add_pow_four_zero :
    iteratedDeriv 2 (fun x : ℝ ↦ x ^ 2 + x ^ 4) 0 = 2 := by
  have hd : HasDerivAt (fun x : ℝ ↦ 2 * x + 4 * x ^ 3) 2 0 := by
    convert ((hasDerivAt_id' (0 : ℝ)).const_mul 2).add ((hasDerivAt_pow 3 (0 : ℝ)).const_mul 4)
      using 1
    norm_num
  rw [iteratedDeriv_succ, iteratedDeriv_one,
    funext fun x ↦ (hasDerivAt_sq_add_pow_four x).deriv, hd.deriv]

/-- `0` is a nondegenerate critical point of `x² + x⁴`; by `deriv_sq_add_pow_four_eq_zero_iff`
it is the only critical point. -/
theorem isNondegenerateCriticalPoint_sq_add_pow_four :
    IsNondegenerateCriticalPoint (fun x : ℝ ↦ x ^ 2 + x ^ 4) 0 :=
  (isNondegenerateCriticalPoint_real_iff (by fun_prop)).2
    ⟨deriv_sq_add_pow_four_eq_zero_iff.2 rfl, by
      rw [iteratedDeriv_two_sq_add_pow_four_zero]; norm_num⟩

/-- The critical point `0` of `x² + x⁴` is a minimum, of Morse index `0`. -/
theorem morseIndex_sq_add_pow_four_zero : morseIndex (fun x : ℝ ↦ x ^ 2 + x ^ 4) 0 = 0 :=
  morseIndex_real_of_pos (by rw [iteratedDeriv_two_sq_add_pow_four_zero]; norm_num)

section Escape

variable {γ : ℝ → ℝ} {T : ℝ}

/-- The escape time `log (2 / 3) / 4` is negative. -/
private theorem log_div_four_neg : log (2 / 3) / 4 < 0 :=
  div_neg_of_neg_of_pos (log_neg (by norm_num) (by norm_num)) (by norm_num)

/-- The quantity `3 e^{4t} - 2` under the square root is positive exactly when
`t > log (2 / 3) / 4`. -/
private theorem sub_pos_iff_log_div_four_lt {t : ℝ} :
    0 < 3 * exp (4 * t) - 2 ↔ log (2 / 3) / 4 < t := by
  rw [sub_pos, div_lt_iff₀ (by norm_num : (0 : ℝ) < 4), log_lt_iff_lt_exp (by norm_num),
    mul_comm t 4]
  constructor <;> intro h <;> linarith

/-- Along a negative gradient trajectory of `x² + x⁴` avoiding `0`, the function `γ⁻²` solves the
linear equation `y' = 4 y + 8`. -/
private theorem hasDerivWithinAt_inv_sq {s : Set ℝ} {t : ℝ}
    (hγ : IsIntegralCurveOn γ (fun _ x ↦ -∇ (fun x : ℝ ↦ x ^ 2 + x ^ 4) x) s) (ht : t ∈ s)
    (hγt : γ t ≠ 0) :
    HasDerivWithinAt (fun t ↦ (γ t ^ 2)⁻¹) (4 * (γ t ^ 2)⁻¹ + 8) s t := by
  have h := ((hγ t ht).pow 2).inv (pow_ne_zero 2 hγt)
  simp only [gradient_sq_add_pow_four, Pi.pow_apply] at h
  refine h.congr_deriv ?_
  field_simp
  ring

/-- **Escape in finite backward time.** A negative gradient trajectory of `x² + x⁴` through `1`
defined on the interval `[T, 0]` has `log (2 / 3) / 4 < T`. -/
theorem log_div_four_lt_of_isIntegralCurveOn
    (hγ : IsIntegralCurveOn γ (fun _ x ↦ -∇ (fun x : ℝ ↦ x ^ 2 + x ^ 4) x) (Icc T 0))
    (h0 : γ 0 = 1) : log (2 / 3) / 4 < T := by
  -- For `T > 0` there is nothing to prove, since `log (2 / 3) < 0`.
  rcases lt_or_ge 0 T with hT | hT
  · exact log_div_four_neg.trans hT
  -- The function decreases along the trajectory, so `γ² + γ⁴ ≥ 2` and `γ² ≥ 1` on `[T, 0]`.
  have hanti := hγ.antitoneOn_comp_neg_gradient (convex_Icc T 0) fun t _ ↦
    (hasDerivAt_sq_add_pow_four (γ t)).differentiableAt
  have hne : ∀ t ∈ Icc T 0, γ t ≠ 0 := fun t ht hzero ↦ by
    have := hanti ht (right_mem_Icc.2 hT) ht.2
    simp only [Function.comp_apply, h0, hzero] at this
    norm_num at this
  -- `F = (γ⁻² + 2) e^{-4t}` has zero derivative, hence is constant on `[T, 0]`.
  set F : ℝ → ℝ := fun t ↦ ((γ t ^ 2)⁻¹ + 2) * exp (-4 * t) with hF
  have hderiv : ∀ t ∈ Icc T 0, HasDerivWithinAt F 0 (Icc T 0) t := fun t ht ↦ by
    have hexp : HasDerivAt (fun t : ℝ ↦ exp (-4 * t)) (exp (-4 * t) * -4) t :=
      ((hasDerivAt_id' t).const_mul (-4)).exp.congr_deriv (by ring)
    convert ((hasDerivWithinAt_inv_sq hγ ht (hne t ht)).add_const 2).mul hexp.hasDerivWithinAt
      using 1
    ring
  have hconst := constant_of_has_deriv_right_zero
    (fun t ht ↦ (hderiv t ht).continuousWithinAt)
    (fun t ht ↦ (hderiv t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ⟨ht.1, ht.2⟩))
    0 (right_mem_Icc.2 hT)
  simp only [hF, h0, one_pow, inv_one, mul_zero, exp_zero, mul_one] at hconst
  -- Hence `γ(T)⁻² = 3 e^{4T} - 2`, which must be positive.
  have hpos : 0 < (γ T ^ 2)⁻¹ := by
    have := hne T (left_mem_Icc.2 hT)
    positivity
  have heq : (γ T ^ 2)⁻¹ + 2 = 3 * exp (4 * T) := by
    have hx : exp (-4 * T) * exp (4 * T) = 1 := by
      rw [← exp_add, show -4 * T + 4 * T = 0 by ring, exp_zero]
    linear_combination -exp (4 * T) * hconst - ((γ T ^ 2)⁻¹ + 2) * hx
  have hlog : log (2 / 3) < 4 * T := (log_lt_iff_lt_exp (by norm_num)).2 (by linarith)
  linarith

/-- The negative gradient trajectory of `x² + x⁴` through `1`, `t ↦ (3 e^{4t} - 2)^{-1/2}`. It
solves `x' = -(2 x + 4 x³)` on `t > log (2 / 3) / 4`
(`TauCeti.NoncompactLineExample.isIntegralCurveOn_escapeCurve`) and escapes to infinity as `t`
decreases to `log (2 / 3) / 4` (`TauCeti.NoncompactLineExample.tendsto_escapeCurve`); for
`t ≤ log (2 / 3) / 4` the formula takes the junk value `0`. -/
def escapeCurve (t : ℝ) : ℝ :=
  (√(3 * exp (4 * t) - 2))⁻¹

theorem escapeCurve_def (t : ℝ) : escapeCurve t = (√(3 * exp (4 * t) - 2))⁻¹ :=
  (rfl)

/-- The trajectory `escapeCurve` passes through `1` at time `0`. -/
@[simp]
theorem escapeCurve_zero : escapeCurve 0 = 1 := by
  norm_num [escapeCurve_def]

/-- **The trajectory through `1`.** `escapeCurve` solves `x' = -(2 x + 4 x³)` for
`t > log (2 / 3) / 4`. -/
theorem isIntegralCurveOn_escapeCurve :
    IsIntegralCurveOn escapeCurve (fun _ x ↦ -∇ (fun x : ℝ ↦ x ^ 2 + x ^ 4) x)
      (Ioi (log (2 / 3) / 4)) := by
  intro t ht
  have hu : 0 < 3 * exp (4 * t) - 2 := sub_pos_iff_log_div_four_lt.2 ht
  have hsq : 0 < √(3 * exp (4 * t) - 2) := sqrt_pos.2 hu
  have hu' : HasDerivAt (fun t : ℝ ↦ 3 * exp (4 * t) - 2) (3 * (exp (4 * t) * 4)) t := by
    convert ((((hasDerivAt_id' t).const_mul 4).exp).const_mul 3).sub_const 2 using 1
    ring
  have h := (hu'.sqrt hu.ne').inv hsq.ne'
  refine (h.congr_deriv ?_).hasDerivWithinAt
  simp only [gradient_sq_add_pow_four, escapeCurve_def]
  have hsq2 : √(3 * exp (4 * t) - 2) ^ 2 = 3 * exp (4 * t) - 2 := sq_sqrt hu.le
  field_simp
  nlinarith [hsq2]

/-- **Escape to infinity.** The trajectory `escapeCurve` tends to `∞` as `t` decreases to
`log (2 / 3) / 4`. -/
theorem tendsto_escapeCurve : Tendsto escapeCurve (𝓝[>] (log (2 / 3) / 4)) atTop := by
  have hc : ContinuousAt (fun t : ℝ ↦ 3 * exp (4 * t) - 2) (log (2 / 3) / 4) := by fun_prop
  have h0 : 3 * exp (4 * (log (2 / 3) / 4)) - 2 = 0 := by
    rw [mul_div_cancel₀ _ (by norm_num : (4 : ℝ) ≠ 0), exp_log (by norm_num)]
    norm_num
  have hu : Tendsto (fun t : ℝ ↦ 3 * exp (4 * t) - 2) (𝓝[>] (log (2 / 3) / 4)) (𝓝[>] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (h0 ▸ hc.tendsto.mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun t ht ↦ sub_pos_iff_log_div_four_lt.2 ht)
  have hsqrt : Tendsto (fun t : ℝ ↦ √(3 * exp (4 * t) - 2)) (𝓝[>] (log (2 / 3) / 4)) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h := (continuous_sqrt.tendsto 0).comp (hu.mono_right nhdsWithin_le_nhds)
      rwa [sqrt_zero] at h
    · exact hu.eventually (eventually_nhdsWithin_of_forall fun u hu ↦ sqrt_pos.2 hu)
  exact tendsto_inv_nhdsGT_zero.comp hsqrt

/-- **The maximal backward existence time.** A negative gradient trajectory of `x² + x⁴` through
`1` exists on `[T, 0]` exactly when `log (2 / 3) / 4 < T`. -/
theorem exists_isIntegralCurveOn_Icc_iff :
    (∃ γ : ℝ → ℝ, IsIntegralCurveOn γ (fun _ x ↦ -∇ (fun x : ℝ ↦ x ^ 2 + x ^ 4) x) (Icc T 0) ∧
      γ 0 = 1) ↔ log (2 / 3) / 4 < T :=
  ⟨fun ⟨_, hγ, h0⟩ ↦ log_div_four_lt_of_isIntegralCurveOn hγ h0,
    fun h ↦ ⟨escapeCurve, isIntegralCurveOn_escapeCurve.mono fun _ ht ↦ h.trans_le ht.1,
      escapeCurve_zero⟩⟩

/-- **`x² + x⁴` has no negative gradient flow**, although it is bounded below and has compact
sublevel sets: the orbit of `1` would be a trajectory through `1` defined for all time. -/
theorem not_isNegativeGradient_sq_add_pow_four (φ : Flow ℝ ℝ) :
    ¬φ.IsNegativeGradient fun x : ℝ ↦ x ^ 2 + x ^ 4 := by
  intro hφ
  exact lt_irrefl _ (log_div_four_lt_of_isIntegralCurveOn
    ((hφ.isIntegralCurve 1).isIntegralCurveOn _) (φ.map_zero_apply 1))

/-- **The gradient of `x² + x⁴` is not globally Lipschitz**: otherwise
`TauCeti.negativeGradientFlow` would be a negative gradient flow of `x² + x⁴`. -/
theorem not_lipschitzWith_gradient_sq_add_pow_four (K : ℝ≥0) :
    ¬LipschitzWith K (∇ fun x : ℝ ↦ x ^ 2 + x ^ 4) := fun hK ↦
  not_isNegativeGradient_sq_add_pow_four _ (isNegativeGradient_negativeGradientFlow _ hK)

/-- **The damped negative gradient of `x² + x⁴` is complete.** The negative gradient field
`x ↦ -(2 x + 4 x³)` of `x² + x⁴`, which has the escaping trajectory `escapeCurve`, becomes complete
after multiplication by the damping factor `TauCeti.rateDamping` of the rate `-(2 x + 4 x³)²`,
because `x² + x⁴` is proper. -/
theorem isCompleteVectorField_rateDampedField_sq_add_pow_four :
    IsCompleteVectorField (rateDampedField (modelWithCornersSelf ℝ ℝ)
      (fun x : ℝ ↦ x ^ 2 + x ^ 4) fun x : ℝ ↦ -(2 * x + 4 * x ^ 3)) :=
  isCompleteVectorField_rateDampedField isProperMap_sq_add_pow_four
    (by fun_prop : ContDiff ℝ 2 fun x : ℝ ↦ x ^ 2 + x ^ 4).contMDiff
    (contMDiff_vectorSpace_iff_contDiff.2
      ((contDiff_const.mul contDiff_id).add (contDiff_const.mul (contDiff_id.pow 3))).neg)

end Escape

end TauCeti.NoncompactLineExample
