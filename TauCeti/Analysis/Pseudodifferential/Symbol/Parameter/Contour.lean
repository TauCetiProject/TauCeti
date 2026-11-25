/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import TauCeti.Analysis.Pseudodifferential.Symbol.Parameter.Evaluation
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import TauCeti.Analysis.Calculus.IteratedFDeriv.Prod
import TauCeti.MeasureTheory.Integral.Bochner.Basic

/-!
# Contour integrals of parameter-dependent symbols

Seeley's construction of the complex powers `A^s` of an elliptic operator `A` of order `2`
integrates a parametrix `b(x, ξ, λ)` of the resolvent `(A - λ)⁻¹`, a strongly
parameter-dependent symbol of order `-2` (`TauCeti.ParameterSymbol`), against `λ^s` along a
contour `Γ` around the spectrum:

`(x, ξ) ↦ (i / 2π) ∫_Γ λ^s b(x, ξ, λ) dλ`.

This file proves that such contour integrals are ordinary symbols, of the order predicted by the
homogeneity of the class, in which a spectral parameter counts as two frequency orders.

Let `a` be a parameter-dependent symbol of order `m` on an open set `Λ` of spectral parameters, let
`γ : ℝ → ℂ` be a continuous path in `Λ` going to infinity at least linearly,
`1 + |t| ≤ c (1 + ‖γ t‖)`, and let `g : ℝ → ℂ` be a measurable weight with
`‖g t‖ ≤ C (|t| ^ σ + (1 + |t|) ^ σ)`. If `-1 < σ` and `m + 2 σ + 2 < 0`, then

`(x, ξ) ↦ ∫ g(t) a(x, ξ, γ(t)) dt`

is a symbol of order `m + 2 σ + 2` (`TauCeti.ParameterSymbol.contourIntegral`). For `σ ≥ 0` the
bound on `g` is the growth bound `‖g t‖ ≤ C' (1 + |t|) ^ σ`; for `-1 < σ < 0` it also allows the
integrable singularity `|t| ^ σ` at `t = 0`. For a contour
integral `∫_γ f(λ) a(x, ξ, λ) dλ` the weight is `g(t) = f(γ t) γ'(t)`; for `f(λ) = λ^s` along a
path with bounded speed and `‖γ t‖` bounded below by a positive constant and comparable to
`1 + |t|`, and a branch of `λ^s` with bounded argument, the exponent is `σ = Re s`. For the
resolvent parametrix (`m = -2`) the conditions are `-1 < Re s < 0`, and the integral has order
`2 Re s`: this is the strip of negative powers in which Seeley's integral converges. Along the
negative real axis, `γ(t) = -|t|` and `g(t) = t ^ (-ρ)` for `t > 0` (and `0` otherwise), with
`0 < ρ < 1`, give Balakrishnan's real-axis form of this integral
(`TauCeti.ParameterSymbol.balakrishnanIntegral`). There the exponent is `σ = -ρ ∈ (-1, 0)`, and
the singularity of the weight at `t = 0` is needed.

The estimates come from the symbol estimates of `a` uniformly in the spectral parameter
(`TauCeti.ParameterSymbol.exists_norm_mixedDeriv_coefficient_le`): the weight
`1 + ‖ξ‖ + ‖γ t‖ ^ (1 / 2)` is at least a multiple of `⟨ξ⟩ + (1 + |t|) ^ (1 / 2)`, and

`∫ (|t| ^ σ + (1 + |t|) ^ σ) (⟨ξ⟩ + (1 + |t|) ^ (1 / 2)) ^ μ dt ≤ K ⟨ξ⟩ ^ (μ + 2 σ + 2)`

for `-1 < σ`, `μ ≤ 0` and `μ + 2 σ + 2 < 0`, by the substitution `t = ⟨ξ⟩² v`. The derivatives of
the integral are the integrals of the derivatives
(`TauCeti.ParameterSymbol.mixedDeriv_contourIntegral`), by differentiation under the integral sign
at every order (`hasFTaylorSeriesUpToOn_integral_of_le_bound`).

## Main declarations

* `TauCeti.ParameterSymbol.contourIntegral`: the symbol `(x, ξ) ↦ ∫ g(t) a(x, ξ, γ(t)) dt` of order
  `m + 2 σ + 2`.
* `TauCeti.ParameterSymbol.coefficient_contourIntegral`: its coefficient.
* `TauCeti.ParameterSymbol.mixedDeriv_contourIntegral`: its mixed derivatives are the integrals of
  the mixed derivatives of the symbols `a(·, ·, γ(t))`.
* `TauCeti.ParameterSymbol.contourIntegral_add`, `TauCeti.ParameterSymbol.contourIntegral_smul`,
  `TauCeti.ParameterSymbol.contourIntegral_neg`, `TauCeti.ParameterSymbol.contourIntegral_sub`:
  it is linear in `a`, so a parametrix may be integrated term by term.
* `TauCeti.ParameterSymbol.contourIntegralₗ`: the contour integral as a `ℂ`-linear map, with
  `TauCeti.ParameterSymbol.contourIntegral_sum` for finite sums.

## References

* R. T. Seeley, *Complex powers of an elliptic operator*, Proc. Sympos. Pure Math. 10 (1967),
  288–307.
* M. A. Shubin, *Pseudodifferential Operators and Spectral Theory*, Chapter II, §10 (definition
  and properties of the complex powers).
-/

public section

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace TauCeti

namespace ParameterSymbol

/-! ### A weighted integral on the line -/

section Weight

/-- The weight `(|t| ^ σ + (1 + |t|) ^ σ) (√B + √(1 + |t|)) ^ μ` whose integral governs the order of
a contour integral; `B = ⟨ξ⟩²`. -/
private def lineWeight (σ μ B t : ℝ) : ℝ :=
  (|t| ^ σ + (1 + |t|) ^ σ) * (Real.sqrt B + Real.sqrt (1 + |t|)) ^ μ

private theorem lineWeight_nonneg (σ μ B t : ℝ) : 0 ≤ lineWeight σ μ B t := by
  unfold lineWeight
  positivity

/-- The rescaled weight `(v ^ σ + (1 + v) ^ σ) (1 + √v) ^ μ` on `(0, ∞)`, which dominates the weight
after the substitution `t = B v`. -/
private def scaledWeight (σ μ v : ℝ) : ℝ :=
  (v ^ σ + (1 + v) ^ σ) * (1 + Real.sqrt v) ^ μ

private theorem integrableOn_scaledWeight {σ μ : ℝ} (hσ : -1 < σ) (hμ : μ ≤ 0)
    (hσμ : σ + μ / 2 < -1) : IntegrableOn (scaledWeight σ μ) (Ioi 0) := by
  -- `(1 + √v) ^ μ` is at most `1`, at most `v ^ (μ / 2)` and at most `(1 + v) ^ (μ / 2)`.
  have hsq (v : ℝ) (hv : 0 < v) : (1 + Real.sqrt v) ^ μ ≤ v ^ (μ / 2) := by
    calc (1 + Real.sqrt v) ^ μ ≤ Real.sqrt v ^ μ :=
          Real.rpow_le_rpow_of_nonpos (Real.sqrt_pos.2 hv) (by linarith) hμ
      _ = v ^ (μ / 2) := (Real.rpow_div_two_eq_sqrt μ hv.le).symm
  have hsq' (v : ℝ) (hv : 0 ≤ v) : (1 + Real.sqrt v) ^ μ ≤ (1 + v) ^ (μ / 2) := by
    have h1 : 0 < 1 + v := by linarith
    calc (1 + Real.sqrt v) ^ μ ≤ Real.sqrt (1 + v) ^ μ := by
          refine Real.rpow_le_rpow_of_nonpos (Real.sqrt_pos.2 h1) ?_ hμ
          rw [Real.sqrt_le_left (by positivity)]
          nlinarith [Real.sq_sqrt hv, Real.sqrt_nonneg v]
      _ = (1 + v) ^ (μ / 2) := (Real.rpow_div_two_eq_sqrt μ h1.le).symm
  have hone (v : ℝ) : (1 + Real.sqrt v) ^ μ ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.sqrt_nonneg v]) hμ
  -- The term `(1 + v) ^ σ (1 + √v) ^ μ` is dominated by `(1 + v) ^ (σ + μ / 2)`.
  have h₂ : IntegrableOn (fun v ↦ (1 + v) ^ σ * (1 + Real.sqrt v) ^ μ) (Ioi 0) := by
    have hi : Integrable fun v : ℝ ↦ (1 + ‖v‖) ^ (-(-(σ + μ / 2))) :=
      integrable_one_add_norm (by simp; linarith)
    refine hi.integrableOn.mono' (Measurable.aestronglyMeasurable (by fun_prop))
      ((ae_restrict_iff' measurableSet_Ioi).2 (.of_forall fun v (hv : 0 < v) ↦ ?_))
    rw [neg_neg, Real.norm_of_nonneg (show 0 ≤ (1 + v) ^ σ * (1 + Real.sqrt v) ^ μ by positivity),
      Real.norm_eq_abs v, abs_of_pos hv, Real.rpow_add (by linarith)]
    exact mul_le_mul_of_nonneg_left (hsq' v hv.le) (by positivity)
  -- The term `v ^ σ (1 + √v) ^ μ` is dominated by `v ^ σ` near `0` and by `v ^ (σ + μ / 2)` at
  -- infinity.
  have h₁ : IntegrableOn (fun v ↦ v ^ σ * (1 + Real.sqrt v) ^ μ) (Ioi 0) := by
    rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
    refine IntegrableOn.union ?_ ?_
    · have hi : IntegrableOn (fun v : ℝ ↦ v ^ σ) (Ioc 0 1) :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
          (intervalIntegral.intervalIntegrable_rpow' hσ)
      refine hi.mono' (Measurable.aestronglyMeasurable (by fun_prop))
        ((ae_restrict_iff' measurableSet_Ioc).2 (.of_forall fun v hv ↦ ?_))
      have hv0 : 0 ≤ v ^ σ := Real.rpow_nonneg hv.1.le σ
      rw [Real.norm_of_nonneg (by positivity)]
      exact mul_le_of_le_one_right hv0 (hone v)
    · refine (integrableOn_Ioi_rpow_of_lt hσμ one_pos).mono'
        (Measurable.aestronglyMeasurable (by fun_prop))
        ((ae_restrict_iff' measurableSet_Ioi).2 (.of_forall fun v (hv : 1 < v) ↦ ?_))
      have hv0 : 0 < v := one_pos.trans hv
      rw [Real.norm_of_nonneg (by positivity), Real.rpow_add hv0]
      exact mul_le_mul_of_nonneg_left (hsq v hv0) (by positivity)
  refine (h₁.add h₂).congr_fun (fun v _ ↦ ?_) measurableSet_Ioi
  simp only [scaledWeight, Pi.add_apply]
  ring

/-- **The substitution `t = B v`.** For `t = B v > 0` and `B ≥ 1` the weight is at most
`2 B ^ (σ + μ / 2)` times the rescaled weight at `v`. -/
private theorem lineWeight_le_scaledWeight {σ μ B : ℝ} (hμ : μ ≤ 0) (hB : 1 ≤ B) {v : ℝ}
    (hv : 0 < v) : lineWeight σ μ B (B * v) ≤ 2 * B ^ (σ + μ / 2) * scaledWeight σ μ v := by
  have hB0 : 0 < B := one_pos.trans_le hB
  have hBv : 0 < B * v := mul_pos hB0 hv
  -- The factor `|B v| ^ σ` is `B ^ σ v ^ σ`.
  have h₀ : |B * v| ^ σ ≤ B ^ σ * (v ^ σ + (1 + v) ^ σ) := by
    rw [abs_of_pos hBv, Real.mul_rpow hB0.le hv.le]
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) (by positivity)
  -- The factor `(1 + B v) ^ σ` is at most `B ^ σ (v ^ σ + (1 + v) ^ σ)`, whatever the sign of `σ`.
  have h₁ : (1 + |B * v|) ^ σ ≤ B ^ σ * (v ^ σ + (1 + v) ^ σ) := by
    rw [abs_of_pos hBv]
    rcases le_or_gt 0 σ with hσ | hσ
    · calc (1 + B * v) ^ σ ≤ (B * (1 + v)) ^ σ :=
            Real.rpow_le_rpow (by positivity) (by nlinarith) hσ
        _ = B ^ σ * (1 + v) ^ σ := Real.mul_rpow hB0.le (by positivity)
        _ ≤ B ^ σ * (v ^ σ + (1 + v) ^ σ) :=
            mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity)) (by positivity)
    · calc (1 + B * v) ^ σ ≤ (B * v) ^ σ :=
            Real.rpow_le_rpow_of_nonpos hBv (by linarith) hσ.le
        _ = B ^ σ * v ^ σ := Real.mul_rpow hB0.le hv.le
        _ ≤ B ^ σ * (v ^ σ + (1 + v) ^ σ) :=
            mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) (by positivity)
  -- The factor `(√B + √(1 + B v)) ^ μ` is at most `(√B (1 + √v)) ^ μ = B ^ (μ / 2) (1 + √v) ^ μ`.
  have h₂ : (Real.sqrt B + Real.sqrt (1 + |B * v|)) ^ μ ≤ B ^ (μ / 2) * (1 + Real.sqrt v) ^ μ := by
    have hpos : 0 < Real.sqrt B * (1 + Real.sqrt v) :=
      mul_pos (Real.sqrt_pos.2 hB0) (by positivity)
    calc (Real.sqrt B + Real.sqrt (1 + |B * v|)) ^ μ ≤ (Real.sqrt B * (1 + Real.sqrt v)) ^ μ := by
          refine Real.rpow_le_rpow_of_nonpos hpos ?_ hμ
          rw [mul_add, mul_one, ← Real.sqrt_mul hB0.le, abs_of_pos hBv]
          gcongr
          linarith
      _ = B ^ (μ / 2) * (1 + Real.sqrt v) ^ μ := by
          rw [Real.mul_rpow (Real.sqrt_nonneg B) (by positivity),
            ← Real.rpow_div_two_eq_sqrt μ hB0.le]
  calc lineWeight σ μ B (B * v) ≤ (2 * (B ^ σ * (v ^ σ + (1 + v) ^ σ))) *
        (B ^ (μ / 2) * (1 + Real.sqrt v) ^ μ) :=
        mul_le_mul (by linarith) h₂ (by positivity) (by positivity)
    _ = 2 * B ^ (σ + μ / 2) * scaledWeight σ μ v := by
        rw [Real.rpow_add hB0, scaledWeight]
        ring

/-- The weight `lineWeight σ μ B` is the even extension of this function on `(0, ∞)`. -/
private def halfLineWeight (σ μ B t : ℝ) : ℝ :=
  (t ^ σ + (1 + t) ^ σ) * (Real.sqrt B + Real.sqrt (1 + t)) ^ μ

private theorem lineWeight_eq_halfLineWeight (σ μ B t : ℝ) :
    lineWeight σ μ B t = halfLineWeight σ μ B |t| :=
  rfl

/-- On `(0, ∞)` the weight is dominated by `2 B ^ (σ + μ / 2)` times the rescaled weight at
`B⁻¹ t`, and is integrable. -/
private theorem halfLineWeight_le_and_integrableOn {σ μ B : ℝ} (hσ : -1 < σ) (hμ : μ ≤ 0)
    (hσμ : σ + μ / 2 < -1) (hB : 1 ≤ B) :
    (∀ t, 0 < t → halfLineWeight σ μ B t ≤ 2 * B ^ (σ + μ / 2) * scaledWeight σ μ (B⁻¹ * t)) ∧
      IntegrableOn (fun t ↦ 2 * B ^ (σ + μ / 2) * scaledWeight σ μ (B⁻¹ * t)) (Ioi 0) ∧
      IntegrableOn (halfLineWeight σ μ B) (Ioi 0) := by
  have hB0 : 0 < B := one_pos.trans_le hB
  have hle (t : ℝ) (ht : 0 < t) :
      halfLineWeight σ μ B t ≤ 2 * B ^ (σ + μ / 2) * scaledWeight σ μ (B⁻¹ * t) := by
    have h := lineWeight_le_scaledWeight (σ := σ) hμ hB (mul_pos (inv_pos.2 hB0) ht)
    rwa [mul_inv_cancel_left₀ hB0.ne', lineWeight_eq_halfLineWeight, abs_of_pos ht] at h
  have hscaled : IntegrableOn (fun t ↦ 2 * B ^ (σ + μ / 2) * scaledWeight σ μ (B⁻¹ * t))
      (Ioi 0) := by
    refine Integrable.const_mul ?_ _
    have := (integrableOn_Ioi_comp_mul_left_iff (scaledWeight σ μ) 0 (inv_pos.2 hB0)).2
    rw [mul_zero] at this
    exact this (integrableOn_scaledWeight hσ hμ hσμ)
  refine ⟨hle, hscaled, hscaled.mono' (Measurable.aestronglyMeasurable ?_)
    ((ae_restrict_iff' measurableSet_Ioi).2 (.of_forall fun t (ht : 0 < t) ↦ ?_))⟩
  · unfold halfLineWeight
    fun_prop
  · rw [Real.norm_of_nonneg (by unfold halfLineWeight; positivity)]
    exact hle t ht

private theorem integrable_lineWeight {σ μ B : ℝ} (hσ : -1 < σ) (hμ : μ ≤ 0)
    (hσμ : σ + μ / 2 < -1) (hB : 1 ≤ B) : Integrable (lineWeight σ μ B) :=
  TauCeti.MeasureTheory.integrable_comp_abs (halfLineWeight_le_and_integrableOn hσ hμ hσμ hB).2.2

/-- **The weighted integral on the line.** For `-1 < σ`, `μ ≤ 0` and `σ + μ / 2 < -1` there is
`K` with `∫ (|t| ^ σ + (1 + |t|) ^ σ) (√B + √(1 + |t|)) ^ μ dt ≤ K B ^ (σ + μ / 2 + 1)` for every
`B ≥ 1`. -/
private theorem exists_integral_lineWeight_le {σ μ : ℝ} (hσ : -1 < σ) (hμ : μ ≤ 0)
    (hσμ : σ + μ / 2 < -1) :
    ∃ K, ∀ B, 1 ≤ B → ∫ t, lineWeight σ μ B t ≤ K * B ^ (σ + μ / 2 + 1) := by
  refine ⟨4 * ∫ v in Ioi 0, scaledWeight σ μ v, fun B hB ↦ ?_⟩
  have hB0 : 0 < B := one_pos.trans_le hB
  obtain ⟨hle, hscaled, hint⟩ := halfLineWeight_le_and_integrableOn hσ hμ hσμ hB
  -- By symmetry the integral is twice the integral over `(0, ∞)`.
  have habs : ∫ t, lineWeight σ μ B t = 2 * ∫ t in Ioi 0, halfLineWeight σ μ B t :=
    integral_comp_abs (f := halfLineWeight σ μ B)
  have hmono : ∫ t in Ioi 0, halfLineWeight σ μ B t ≤
      ∫ t in Ioi 0, 2 * B ^ (σ + μ / 2) * scaledWeight σ μ (B⁻¹ * t) :=
    setIntegral_mono_on hint hscaled measurableSet_Ioi hle
  -- Undo the substitution in the dominating integral.
  have hsub : ∫ t in Ioi 0, 2 * B ^ (σ + μ / 2) * scaledWeight σ μ (B⁻¹ * t) =
      2 * B ^ (σ + μ / 2) * (B * ∫ v in Ioi 0, scaledWeight σ μ v) := by
    rw [integral_const_mul, integral_comp_mul_left_Ioi _ _ (inv_pos.2 hB0), mul_zero, inv_inv,
      smul_eq_mul]
  rw [habs]
  calc 2 * ∫ t in Ioi 0, halfLineWeight σ μ B t
      ≤ 2 * (2 * B ^ (σ + μ / 2) * (B * ∫ v in Ioi 0, scaledWeight σ μ v)) :=
        mul_le_mul_of_nonneg_left (hmono.trans_eq hsub) zero_le_two
    _ = 4 * (∫ v in Ioi 0, scaledWeight σ μ v) * B ^ (σ + μ / 2 + 1) := by
        rw [Real.rpow_add_one hB0.ne']
        ring

end Weight

/-! ### The contour integral -/

section Contour

variable {n : ℕ} {Λ : TopologicalSpace.Opens ℂ} {V W : Type*} [NormedAddCommGroup V]
  [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] {m σ : ℝ}
  (a : ParameterSymbol n Λ V W m) {γ g : ℝ → ℂ}

/-- Along a path with `1 + |t| ≤ c (1 + ‖γ t‖)`, the parameter weight at `γ t` is at least a
multiple of `⟨ξ⟩ + (1 + |t|) ^ (1 / 2)`; so its nonpositive powers are at most a multiple of those
of `⟨ξ⟩ + (1 + |t|) ^ (1 / 2)`. -/
private theorem parameterWeight_rpow_le {c : ℝ} (hc : ∀ t, 1 + |t| ≤ c * (1 + ‖γ t‖)) {μ : ℝ}
    (hμ : μ ≤ 0) (ξ : CoordinateSpace n) (t : ℝ) :
    parameterWeight ξ (γ t) ^ μ ≤ (1 + Real.sqrt c) ^ (-μ) *
      (Real.sqrt (1 + ‖ξ‖ ^ 2) + Real.sqrt (1 + |t|)) ^ μ := by
  have hc0 : 0 ≤ c := by
    by_contra h
    nlinarith [hc 0, norm_nonneg (γ 0), abs_nonneg (0 : ℝ)]
  set S := Real.sqrt (1 + ‖ξ‖ ^ 2) + Real.sqrt (1 + |t|)
  have hS : 0 < S := by positivity
  have hw := parameterWeight_def ξ (γ t)
  -- `⟨ξ⟩ ≤ 1 + ‖ξ‖` and `(1 + |t|) ^ (1 / 2) ≤ √c (1 + ‖γ t‖ ^ (1 / 2))`.
  have h₁ : Real.sqrt (1 + ‖ξ‖ ^ 2) ≤ 1 + ‖ξ‖ := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [norm_nonneg ξ]
  have h₂ : Real.sqrt (1 + |t|) ≤ Real.sqrt c * (1 + Real.sqrt ‖γ t‖) := by
    calc Real.sqrt (1 + |t|) ≤ Real.sqrt (c * (1 + ‖γ t‖)) := Real.sqrt_le_sqrt (hc t)
      _ = Real.sqrt c * Real.sqrt (1 + ‖γ t‖) := Real.sqrt_mul hc0 _
      _ ≤ Real.sqrt c * (1 + Real.sqrt ‖γ t‖) := by
          gcongr
          rw [Real.sqrt_le_left (by positivity)]
          nlinarith [Real.sq_sqrt (norm_nonneg (γ t)), Real.sqrt_nonneg ‖γ t‖]
  have hSw : S / (1 + Real.sqrt c) ≤ parameterWeight ξ (γ t) := by
    rw [div_le_iff₀ (by positivity)]
    have := Real.sqrt_nonneg c
    have := Real.sqrt_nonneg ‖γ t‖
    nlinarith [norm_nonneg ξ]
  calc parameterWeight ξ (γ t) ^ μ ≤ (S / (1 + Real.sqrt c)) ^ μ :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hSw hμ
    _ = (1 + Real.sqrt c) ^ (-μ) * S ^ μ := by
        rw [Real.div_rpow hS.le (by positivity), Real.rpow_neg (by positivity), div_eq_mul_inv,
          mul_comm]

/-- At each point of the path the integrand is smooth in the position and the frequency. -/
private theorem contDiff_smul_coefficient (t : ℝ) :
    ContDiff ℝ ∞ fun q ↦ g t • a.coefficient (q, γ t) :=
  (a.contDiff_coefficient_slice (γ t)).const_smul (g t)

/-- The derivatives of the integrand are those of the symbol at the point of the path, times the
weight. -/
private theorem iteratedFDeriv_smul_coefficient (k : ℕ) (t : ℝ)
    (q : CoordinateSpace n × CoordinateSpace n) :
    iteratedFDeriv ℝ k (fun q ↦ g t • a.coefficient (q, γ t)) q =
      g t • iteratedFDeriv ℝ k (fun q ↦ a.coefficient (q, γ t)) q :=
  iteratedFDeriv_const_smul_apply'
    (((a.contDiff_coefficient_slice (γ t)).of_le (by exact_mod_cast le_top)).contDiffAt)

variable (hγ : Continuous γ) (hγΛ : ∀ t, γ t ∈ Λ)
include hγ hγΛ

/-- Along a continuous path in `Λ`, the derivatives of the symbols at the points of the path
depend continuously on the time. -/
private theorem continuous_iteratedFDeriv_coefficient (k : ℕ)
    (q : CoordinateSpace n × CoordinateSpace n) :
    Continuous fun t ↦ iteratedFDeriv ℝ k (fun q ↦ a.coefficient (q, γ t)) q := by
  have h (t : ℝ) := (a.contDiffAt_coefficient (p := (q, γ t)) (hγΛ t)).iteratedFDeriv_prod_left
    k (by exact_mod_cast le_top)
  simp_rw [h]
  refine (ContinuousMultilinearMap.compContinuousLinearMapL _).continuous.comp ?_
  refine continuous_iff_continuousAt.2 fun t ↦ ?_
  exact ((a.contDiffAt_coefficient (p := (q, γ t)) (hγΛ t)).continuousAt_iteratedFDeriv
    (by exact_mod_cast le_top)).comp (f := fun t ↦ (q, γ t))
    (continuous_const.prodMk hγ).continuousAt

variable (hg : AEStronglyMeasurable g)
include hg

/-- The derivatives of the integrand are measurable in the time. -/
private theorem aestronglyMeasurable_iteratedFDeriv_smul_coefficient (k : ℕ)
    (q : CoordinateSpace n × CoordinateSpace n) :
    AEStronglyMeasurable (fun t ↦ iteratedFDeriv ℝ k (fun q ↦ g t • a.coefficient (q, γ t)) q) := by
  simp_rw [iteratedFDeriv_smul_coefficient]
  exact hg.smul (a.continuous_iteratedFDeriv_coefficient hγ hγΛ k q).aestronglyMeasurable

variable (hγc : ∃ c, ∀ t, 1 + |t| ≤ c * (1 + ‖γ t‖))
  (hgσ : ∃ C, ∀ t, ‖g t‖ ≤ C * (|t| ^ σ + (1 + |t|) ^ σ)) (hσ : -1 < σ) (hm : m + 2 * σ + 2 < 0)
include hγc hgσ hσ hm

omit hγ hg in
/-- On the unit ball around each point, the derivatives of order `k` of the integrand are dominated
by one integrable function of the time. -/
private theorem exists_bound_iteratedFDeriv_smul_coefficient
    (p₀ : CoordinateSpace n × CoordinateSpace n) (k : ℕ) :
    ∃ G : ℝ → ℝ, Integrable G ∧ ∀ t, ∀ p ∈ Metric.ball p₀ 1,
      ‖iteratedFDeriv ℝ k (fun q ↦ g t • a.coefficient (q, γ t)) p‖ ≤ G t := by
  obtain ⟨c, hc⟩ := hγc
  obtain ⟨C, hC⟩ := hgσ
  have hm0 : m ≤ 0 := by linarith
  -- One constant for the mixed derivatives along all words of length `k`, on a compact ball.
  have hK := isCompact_closedBall p₀.1 1
  choose D hD0 hD using fun w : Fin k → Fin n ⊕ Fin n ↦ a.exists_norm_mixedDeriv_coefficient_le
    hK ((List.ofFn w).filterMap Sum.getLeft?) ((List.ofFn w).filterMap Sum.getRight?)
  set M := ∑ w, D w
  have hM : 0 ≤ M := Finset.sum_nonneg fun w _ ↦ hD0 w
  refine ⟨fun t ↦ C * M * (1 + Real.sqrt c) ^ (-m) * lineWeight σ m 1 t,
    (integrable_lineWeight hσ hm0 (by linarith) le_rfl).const_mul _, fun t p hp ↦ ?_⟩
  have hpK : p.1 ∈ Metric.closedBall p₀.1 1 := by
    rw [Metric.mem_closedBall]
    exact (le_max_left _ _).trans (Metric.mem_ball.1 hp).le
  have hw := one_le_parameterWeight p.2 (γ t)
  -- Every mixed derivative of order `k` is at most `D w * w ^ m`.
  have hsum : ‖iteratedFDeriv ℝ k (fun q ↦ a.coefficient (q, γ t)) p‖ ≤
      M * parameterWeight p.2 (γ t) ^ m := by
    refine (norm_iteratedFDeriv_le_sum_mixedDeriv ((a.contDiff_coefficient_slice (γ t)).of_le
      (by exact_mod_cast le_top)) p).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun w _ ↦ (hD w p.1 hpK p.2 (γ t) (hγΛ t)).trans ?_
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hw (by simp)) (hD0 w)
  -- The parameter weight is controlled along the path, uniformly in the frequency.
  have hweight : parameterWeight p.2 (γ t) ^ m ≤ (1 + Real.sqrt c) ^ (-m) *
      (Real.sqrt 1 + Real.sqrt (1 + |t|)) ^ m := by
    refine (parameterWeight_rpow_le hc hm0 p.2 t).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos (by positivity) ?_ hm0) (by positivity))
    gcongr
    simp
  have hgt : ‖g t‖ ≤ C * (|t| ^ σ + (1 + |t|) ^ σ) := hC t
  rw [iteratedFDeriv_smul_coefficient, norm_smul]
  calc ‖g t‖ * ‖iteratedFDeriv ℝ k (fun q ↦ a.coefficient (q, γ t)) p‖
      ≤ (C * (|t| ^ σ + (1 + |t|) ^ σ)) * (M * ((1 + Real.sqrt c) ^ (-m) *
          (Real.sqrt 1 + Real.sqrt (1 + |t|)) ^ m)) :=
        mul_le_mul hgt (hsum.trans (mul_le_mul_of_nonneg_left hweight hM)) (norm_nonneg _)
          ((norm_nonneg _).trans hgt)
    _ = C * M * (1 + Real.sqrt c) ^ (-m) * lineWeight σ m 1 t := by
        rw [lineWeight]
        ring

/-- On the unit ball around each point, the integrals of the derivatives of the integrand form a
Taylor series of `(x, ξ) ↦ ∫ g(t) a(x, ξ, γ(t)) dt`: differentiation under the integral sign. -/
private theorem hasFTaylorSeriesUpToOn_integral_smul_coefficient
    (p₀ : CoordinateSpace n × CoordinateSpace n) :
    HasFTaylorSeriesUpToOn ∞ (fun p ↦ ∫ t, g t • a.coefficient (p, γ t))
      (fun p k ↦ ∫ t, iteratedFDeriv ℝ k (fun q ↦ g t • a.coefficient (q, γ t)) p)
      (Metric.ball p₀ 1) := by
  choose G hG hGb using a.exists_bound_iteratedFDeriv_smul_coefficient hγΛ hγc hgσ hσ hm p₀
  exact hasFTaylorSeriesUpToOn_integral_of_le_bound Metric.isOpen_ball
    (fun p _ k _ ↦ a.aestronglyMeasurable_iteratedFDeriv_smul_coefficient hγ hγΛ hg k p)
    (.of_forall fun t p hp k _ ↦ hGb k t p hp) (fun k _ ↦ hG k)
    (.of_forall fun t ↦ (a.contDiff_smul_coefficient t).ftaylorSeries.hasFTaylorSeriesUpToOn _)

/-- The coefficient `(x, ξ) ↦ ∫ g(t) a(x, ξ, γ(t)) dt` is smooth. -/
private theorem contDiff_integral_smul_coefficient :
    ContDiff ℝ ∞ fun p ↦ ∫ t, g t • a.coefficient (p, γ t) :=
  contDiff_iff_contDiffAt.2 fun p₀ ↦
    ((a.hasFTaylorSeriesUpToOn_integral_smul_coefficient hγ hγΛ hg hγc hgσ hσ hm p₀).contDiffOn
      ).contDiffAt (Metric.ball_mem_nhds p₀ one_pos)

/-- The derivatives of `(x, ξ) ↦ ∫ g(t) a(x, ξ, γ(t)) dt` are the integrals of the derivatives. -/
private theorem iteratedFDeriv_integral_smul_coefficient (k : ℕ)
    (p₀ : CoordinateSpace n × CoordinateSpace n) :
    iteratedFDeriv ℝ k (fun p ↦ ∫ t, g t • a.coefficient (p, γ t)) p₀ =
      ∫ t, iteratedFDeriv ℝ k (fun q ↦ g t • a.coefficient (q, γ t)) p₀ := by
  have hp₀ := Metric.mem_ball_self (x := p₀) one_pos
  have h := (a.hasFTaylorSeriesUpToOn_integral_smul_coefficient hγ hγΛ hg hγc hgσ hσ hm
    p₀).eq_iteratedFDerivWithin_of_uniqueDiffOn (m := k) (by exact_mod_cast le_top)
    Metric.isOpen_ball.uniqueDiffOn hp₀
  rw [iteratedFDerivWithin_of_isOpen k Metric.isOpen_ball hp₀] at h
  exact h.symm

/-- The derivatives of the integrand are integrable in the time. -/
private theorem integrable_iteratedFDeriv_smul_coefficient (k : ℕ)
    (p : CoordinateSpace n × CoordinateSpace n) :
    Integrable fun t ↦ iteratedFDeriv ℝ k (fun q ↦ g t • a.coefficient (q, γ t)) p := by
  obtain ⟨G, hG, hGb⟩ := a.exists_bound_iteratedFDeriv_smul_coefficient hγΛ hγc hgσ hσ hm p k
  exact hG.mono' (a.aestronglyMeasurable_iteratedFDeriv_smul_coefficient hγ hγΛ hg k p)
    (.of_forall fun t ↦ hGb t p (Metric.mem_ball_self one_pos))

/-- The integrand is integrable at every position and frequency. -/
private theorem integrable_smul_coefficient (p : CoordinateSpace n × CoordinateSpace n) :
    Integrable fun t ↦ g t • a.coefficient (p, γ t) := by
  have hc : Continuous fun t ↦ a.coefficient (p, γ t) := continuous_iff_continuousAt.2 fun t ↦
    (a.contDiffAt_coefficient (p := (p, γ t)) (hγΛ t)).continuousAt.comp
      (f := fun t ↦ (p, γ t)) (continuous_const.prodMk hγ).continuousAt
  exact (a.integrable_iteratedFDeriv_smul_coefficient hγ hγΛ hg hγc hgσ hσ hm 0 p).norm.mono'
    (hg.smul hc.aestronglyMeasurable)
    (.of_forall fun t ↦ (norm_iteratedFDeriv_zero (f := fun q ↦ g t • a.coefficient (q, γ t))).ge)

/-- The mixed derivatives of `(x, ξ) ↦ ∫ g(t) a(x, ξ, γ(t)) dt` are the integrals of the mixed
derivatives. -/
private theorem mixedDeriv_integral_smul_coefficient (α β : List (Fin n))
    (x ξ : CoordinateSpace n) :
    mixedDeriv α β (fun p ↦ ∫ t, g t • a.coefficient (p, γ t)) x ξ =
      ∫ t, g t • mixedDeriv α β (fun q ↦ a.coefficient (q, γ t)) x ξ := by
  rw [mixedDeriv_eq_iteratedFDeriv α β ((a.contDiff_integral_smul_coefficient hγ hγΛ hg hγc hgσ
      hσ hm).of_le (by exact_mod_cast le_top)),
    a.iteratedFDeriv_integral_smul_coefficient hγ hγΛ hg hγc hgσ hσ hm,
    ContinuousMultilinearMap.integral_apply
      (a.integrable_iteratedFDeriv_smul_coefficient hγ hγΛ hg hγc hgσ hσ hm _ _)]
  refine integral_congr_ae (.of_forall fun t ↦ ?_)
  simp only [iteratedFDeriv_smul_coefficient, smul_apply]
  rw [mixedDeriv_eq_iteratedFDeriv α β ((a.contDiff_coefficient_slice (γ t)).of_le
    (by exact_mod_cast le_top))]

/-- The symbol estimates of order `m + 2 σ + 2` for `(x, ξ) ↦ ∫ g(t) a(x, ξ, γ(t)) dt`. -/
private theorem exists_norm_mixedDeriv_integral_smul_coefficient_le {K : Set (CoordinateSpace n)}
    (hK : IsCompact K) (α β : List (Fin n)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ K, ∀ ξ,
      ‖mixedDeriv α β (fun p ↦ ∫ t, g t • a.coefficient (p, γ t)) x ξ‖ ≤
        B * (1 + ‖ξ‖ ^ 2) ^ ((m + 2 * σ + 2 - β.length) / 2) := by
  obtain ⟨c, hc⟩ := hγc
  obtain ⟨C, hC⟩ := hgσ
  set μ := m - β.length
  have hμ : μ ≤ 0 := by linarith [Nat.cast_nonneg (α := ℝ) β.length]
  have hσμ : σ + μ / 2 < -1 := by linarith [Nat.cast_nonneg (α := ℝ) β.length]
  obtain ⟨D, hD0, hD⟩ := a.exists_norm_mixedDeriv_coefficient_le hK α β
  obtain ⟨L, hL⟩ := exists_integral_lineWeight_le hσ hμ hσμ
  have hC0 : 0 ≤ C := by
    have h := (norm_nonneg _).trans (hC 0)
    rw [abs_zero, add_zero, Real.one_rpow] at h
    exact nonneg_of_mul_nonneg_left h (by positivity)
  set E := C * D * (1 + Real.sqrt c) ^ (-μ)
  have hE : 0 ≤ E := by positivity
  have hL0 : 0 ≤ L := by
    have h := (integral_nonneg (lineWeight_nonneg σ μ 1)).trans (hL 1 le_rfl)
    rwa [Real.one_rpow, mul_one] at h
  refine ⟨E * L, mul_nonneg hE hL0, fun x hx ξ ↦ ?_⟩
  set B := 1 + ‖ξ‖ ^ 2
  have hB : 1 ≤ B := le_add_of_nonneg_right (by positivity)
  rw [a.mixedDeriv_integral_smul_coefficient hγ hγΛ hg ⟨c, hc⟩ ⟨C, hC⟩ hσ hm]
  have hbound : ∀ t, ‖g t • mixedDeriv α β (fun q ↦ a.coefficient (q, γ t)) x ξ‖ ≤
      E * lineWeight σ μ B t := fun t ↦ by
    rw [norm_smul]
    calc ‖g t‖ * ‖mixedDeriv α β (fun q ↦ a.coefficient (q, γ t)) x ξ‖
        ≤ (C * (|t| ^ σ + (1 + |t|) ^ σ)) * (D * ((1 + Real.sqrt c) ^ (-μ) *
            (Real.sqrt B + Real.sqrt (1 + |t|)) ^ μ)) :=
          mul_le_mul (hC t) ((hD x hx ξ (γ t) (hγΛ t)).trans (mul_le_mul_of_nonneg_left
            (parameterWeight_rpow_le hc hμ ξ t) hD0)) (norm_nonneg _)
            ((norm_nonneg _).trans (hC t))
      _ = E * lineWeight σ μ B t := by
          rw [lineWeight]
          ring
  calc ‖∫ t, g t • mixedDeriv α β (fun q ↦ a.coefficient (q, γ t)) x ξ‖
      ≤ ∫ t, E * lineWeight σ μ B t :=
        norm_integral_le_of_norm_le ((integrable_lineWeight hσ hμ hσμ hB).const_mul E)
          (.of_forall hbound)
    _ = E * ∫ t, lineWeight σ μ B t := integral_const_mul E _
    _ ≤ E * (L * B ^ (σ + μ / 2 + 1)) := mul_le_mul_of_nonneg_left (hL B hB) hE
    _ = E * L * B ^ ((m + 2 * σ + 2 - β.length) / 2) := by
        rw [show σ + μ / 2 + 1 = (m + 2 * σ + 2 - β.length) / 2 by simp only [μ]; ring]
        ring

/-- **Contour integrals of parameter-dependent symbols.** Let `a` be a parameter-dependent symbol
of order `m`, `γ` a continuous path in `Λ` with `1 + |t| ≤ c (1 + ‖γ t‖)`, and `g` a measurable
weight with `‖g t‖ ≤ C (|t| ^ σ + (1 + |t|) ^ σ)`, where `-1 < σ` and `m + 2 σ + 2 < 0`. Then
`(x, ξ) ↦ ∫ g(t) a(x, ξ, γ(t)) dt` is a symbol of order `m + 2 σ + 2`. For `g(t) = f(γ t) γ'(t)` it
is the contour integral `∫_γ f(λ) a(x, ξ, λ) dλ`. -/
def contourIntegral : Symbol n V W (m + 2 * σ + 2) where
  coefficient p := ∫ t, g t • a.coefficient (p, γ t)
  contDiff_coefficient := a.contDiff_integral_smul_coefficient hγ hγΛ hg hγc hgσ hσ hm
  exists_bound _ hK α β :=
    a.exists_norm_mixedDeriv_integral_smul_coefficient_le hγ hγΛ hg hγc hgσ hσ hm hK α β

/-- The coefficient of the contour integral is the pointwise integral along the path. -/
@[simp]
theorem coefficient_contourIntegral (p : CoordinateSpace n × CoordinateSpace n) :
    (a.contourIntegral hγ hγΛ hg hγc hgσ hσ hm).coefficient p =
      ∫ t, g t • a.coefficient (p, γ t) :=
  (rfl)

/-- The mixed derivatives of a contour integral of a parameter-dependent symbol are the contour
integrals of the mixed derivatives of the symbols `a(·, ·, λ)` at the points `λ` of the path. -/
theorem mixedDeriv_contourIntegral (α β : List (Fin n)) (x ξ : CoordinateSpace n) :
    mixedDeriv α β (a.contourIntegral hγ hγΛ hg hγc hgσ hσ hm).coefficient x ξ =
      ∫ t, g t • mixedDeriv α β (a.toSymbol (γ t)).coefficient x ξ := by
  have hI : (a.contourIntegral hγ hγΛ hg hγc hgσ hσ hm).coefficient =
      fun p ↦ ∫ t, g t • a.coefficient (p, γ t) :=
    funext (a.coefficient_contourIntegral hγ hγΛ hg hγc hgσ hσ hm)
  have hz (z : ℂ) : (a.toSymbol z).coefficient = fun q ↦ a.coefficient (q, z) :=
    funext (a.coefficient_toSymbol z)
  simp only [hI, hz]
  exact a.mixedDeriv_integral_smul_coefficient hγ hγΛ hg hγc hgσ hσ hm α β x ξ

/-- The contour integral of the zero symbol is the zero symbol. -/
@[simp]
theorem contourIntegral_zero :
    (0 : ParameterSymbol n Λ V W m).contourIntegral hγ hγΛ hg hγc hgσ hσ hm = 0 :=
  Symbol.ext <| funext fun p ↦ by simp [coefficient_zero]

/-- The contour integral is additive in the parameter-dependent symbol. -/
@[simp]
theorem contourIntegral_add (b : ParameterSymbol n Λ V W m) :
    (a + b).contourIntegral hγ hγΛ hg hγc hgσ hσ hm =
      a.contourIntegral hγ hγΛ hg hγc hgσ hσ hm + b.contourIntegral hγ hγΛ hg hγc hgσ hσ hm :=
  Symbol.ext <| funext fun p ↦ by
    simp only [coefficient_contourIntegral, coefficient_add, Pi.add_apply, smul_add]
    exact integral_add (a.integrable_smul_coefficient hγ hγΛ hg hγc hgσ hσ hm p)
      (b.integrable_smul_coefficient hγ hγΛ hg hγc hgσ hσ hm p)

/-- The contour integral commutes with multiplication by a complex scalar. -/
@[simp]
theorem contourIntegral_smul (c : ℂ) :
    (c • a).contourIntegral hγ hγΛ hg hγc hgσ hσ hm =
      c • a.contourIntegral hγ hγΛ hg hγc hgσ hσ hm :=
  Symbol.ext <| funext fun p ↦ by
    simp only [coefficient_contourIntegral, coefficient_smul, Pi.smul_apply, smul_comm (g _) c]
    exact integral_smul c _

/-- The contour integral commutes with negation. -/
@[simp]
theorem contourIntegral_neg :
    (-a).contourIntegral hγ hγΛ hg hγc hgσ hσ hm = -a.contourIntegral hγ hγΛ hg hγc hgσ hσ hm :=
  Symbol.ext <| funext fun p ↦ by
    simp only [coefficient_contourIntegral, coefficient_neg, Pi.neg_apply, smul_neg]
    exact integral_neg _

/-- The contour integral commutes with subtraction. -/
@[simp]
theorem contourIntegral_sub (b : ParameterSymbol n Λ V W m) :
    (a - b).contourIntegral hγ hγΛ hg hγc hgσ hσ hm =
      a.contourIntegral hγ hγΛ hg hγc hgσ hσ hm - b.contourIntegral hγ hγΛ hg hγc hgσ hσ hm := by
  rw [sub_eq_add_neg, contourIntegral_add, contourIntegral_neg, ← sub_eq_add_neg]

/-- The contour integral as a `ℂ`-linear map from parameter-dependent symbols of order `m` to
symbols of order `m + 2 σ + 2`. -/
def contourIntegralₗ : ParameterSymbol n Λ V W m →ₗ[ℂ] Symbol n V W (m + 2 * σ + 2) where
  toFun b := b.contourIntegral hγ hγΛ hg hγc hgσ hσ hm
  map_add' b b' := b.contourIntegral_add hγ hγΛ hg hγc hgσ hσ hm b'
  map_smul' c b := b.contourIntegral_smul hγ hγΛ hg hγc hgσ hσ hm c

@[simp]
theorem contourIntegralₗ_apply :
    contourIntegralₗ hγ hγΛ hg hγc hgσ hσ hm a = a.contourIntegral hγ hγΛ hg hγc hgσ hσ hm :=
  (rfl)

/-- The contour integral of a finite sum is the sum of the contour integrals, so a finite
parametrix expansion may be integrated term by term. -/
@[simp]
theorem contourIntegral_sum {ι : Type*} (s : Finset ι) (b : ι → ParameterSymbol n Λ V W m) :
    (∑ i ∈ s, b i).contourIntegral hγ hγΛ hg hγc hgσ hσ hm =
      ∑ i ∈ s, (b i).contourIntegral hγ hγΛ hg hγc hgσ hσ hm :=
  map_sum (contourIntegralₗ hγ hγΛ hg hγc hgσ hσ hm) b s

end Contour

end ParameterSymbol

end TauCeti
