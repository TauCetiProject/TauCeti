/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Index
public import TauCeti.Analysis.Calculus.Morse.Linearization
public import Mathlib.Analysis.ODE.Basic
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Analysis.ODE.Heteroclinic

/-!
# Nondegenerate critical points of functions of one real variable

A function `f : ℝ → ℝ` is a function on the one-dimensional real inner product space `ℝ`, so the
general Morse-theoretic notions apply to it. This file reads them off the first and second
derivatives of `f`. The Hessian operator of `f` at `t` is multiplication by `f''(t)`
(`TauCeti.hessianOperator_real`); `t` is a nondegenerate critical point exactly when `f'(t) = 0`
and `f''(t) ≠ 0` (`TauCeti.isNondegenerateCriticalPoint_real_iff`); and the Morse index there is
`1` when `f''(t) < 0` and `0` when `0 < f''(t)`.

These are the facts needed to apply the theory of linearized trajectory operators, which is stated
on finite-dimensional inner product spaces, to the negative-gradient flow of an explicit function
of one variable.

## Main declarations

* `TauCeti.hessianOperator_real`: the Hessian operator is multiplication by `f''(t)`.
* `TauCeti.isNondegenerateCriticalPoint_real_iff`: nondegenerate critical points of a function of
  one variable, with the example `TauCeti.isNondegenerateCriticalPoint_sq` of `y ↦ y²` at `0`.
* `TauCeti.morseIndex_real_of_neg` and `TauCeti.morseIndex_real_of_pos`: the Morse index is `1`
  where the second derivative is negative (a local maximum at a critical point) and `0` where it is
  positive (a local minimum at a critical point).
* `TauCeti.isNondegenerateCriticalPoint_pow_iff`: the only nondegenerate critical point of a power
  `y ↦ yⁿ` is `0`, for `n = 2`.
* `TauCeti.exists_isIntegralCurve_neg_gradient_of_deriv_neg`: two consecutive critical points
  `p < q` of a `C²` function `f` which decreases between them are joined by a negative gradient
  trajectory from `p` to `q`, and every negative gradient trajectory from `p` to `q` is one of its
  time translates. So they are joined by exactly one unparametrized trajectory, as in the Morse
  complex of a function of one variable, where `p` is a local maximum and `q` a local minimum.
-/

public section

open Filter Set
open scoped Topology Gradient

namespace TauCeti

variable {f : ℝ → ℝ} {t : ℝ}

/-- The Hessian operator of a function of one real variable is multiplication by its second
derivative. -/
theorem hessianOperator_real (f : ℝ → ℝ) (t : ℝ) :
    hessianOperator f t = iteratedDeriv 2 f t • ContinuousLinearMap.id ℝ ℝ := by
  refine ContinuousLinearMap.ext_ring ?_
  have h := inner_hessianOperator_left f t 1 1
  rw [fderiv_fderiv_apply_eq_smul_iteratedDeriv] at h
  simpa using h

/-- The Hessian quadratic form of a function of one real variable is `v ↦ f''(t) v²`. -/
theorem hessianQuadraticForm_real_apply (f : ℝ → ℝ) (t v : ℝ) :
    hessianQuadraticForm f t v = iteratedDeriv 2 f t * v ^ 2 := by
  rw [hessianQuadraticForm_apply, fderiv_fderiv_apply_eq_smul_iteratedDeriv, smul_eq_mul]
  ring

/-- **Nondegenerate critical points of a function of one variable.** A point at which `f` is
twice continuously differentiable is a nondegenerate critical point exactly when the first
derivative vanishes there and the second does not. -/
theorem isNondegenerateCriticalPoint_real_iff (hf : ContDiffAt ℝ 2 f t) :
    IsNondegenerateCriticalPoint f t ↔ deriv f t = 0 ∧ iteratedDeriv 2 f t ≠ 0 := by
  have h0 : ContinuousLinearMap.toSpanSingleton ℝ (deriv f t) = 0 ↔ deriv f t = 0 :=
    ⟨fun h ↦ by simpa using congrArg (· 1) h, fun h ↦ by simp [h]⟩
  rw [isNondegenerateCriticalPoint_iff_separatingLeft, ← toSpanSingleton_deriv, h0]
  simp only [hf, true_and]
  refine and_congr_right fun _ ↦ ⟨fun h h0 ↦ one_ne_zero (h 1 fun w ↦ ?_), fun h v hv ↦ ?_⟩
  · rw [ContinuousLinearMap.toBilinForm_apply, fderiv_fderiv_apply_eq_smul_iteratedDeriv, h0,
      smul_zero]
  · have := hv 1
    simp only [ContinuousLinearMap.toBilinForm_apply, fderiv_fderiv_apply_eq_smul_iteratedDeriv,
      smul_eq_mul, mul_one] at this
    exact (mul_eq_zero.1 this).resolve_right h

/-- The function `y ↦ y²` has a nondegenerate critical point at `0`. -/
theorem isNondegenerateCriticalPoint_sq :
    IsNondegenerateCriticalPoint (fun y : ℝ ↦ y ^ 2) 0 := by
  rw [isNondegenerateCriticalPoint_real_iff (by fun_prop)]
  constructor <;> simp [← iteratedDeriv_one]

/-- Where the second derivative is negative, the Morse index of a function of one variable is `1`;
at a critical point this is a local maximum. -/
theorem morseIndex_real_of_neg (hneg : iteratedDeriv 2 f t < 0) : morseIndex f t = 1 := by
  have := (neg_hessianQuadraticForm_posDef_iff_morseIndex_eq_finrank (f := f) (x := t)).1
    fun v hv ↦ by
    rw [neg_apply, hessianQuadraticForm_real_apply]
    nlinarith [pow_pos (abs_pos.2 hv) 2, sq_abs v]
  simpa using this

/-- Where the second derivative is positive, the Morse index of a function of one variable is `0`;
at a critical point this is a local minimum. -/
theorem morseIndex_real_of_pos (hpos : 0 < iteratedDeriv 2 f t) : morseIndex f t = 0 :=
  morseIndex_eq_zero_of_posDef fun v hv ↦ by
    rw [hessianQuadraticForm_real_apply]
    nlinarith [pow_pos (abs_pos.2 hv) 2, sq_abs v]

/-- **Nondegenerate critical points of a power.** The function `y ↦ yⁿ` has a nondegenerate
critical point at `t` exactly when `n = 2` and `t = 0`. For `n = 0` the Hessian vanishes
everywhere, for `n = 1` there is no critical point, and for `3 ≤ n` the only critical point `0` has
vanishing second derivative. -/
@[simp]
theorem isNondegenerateCriticalPoint_pow_iff {n : ℕ} :
    IsNondegenerateCriticalPoint (fun y : ℝ ↦ y ^ n) t ↔ n = 2 ∧ t = 0 := by
  rw [isNondegenerateCriticalPoint_real_iff (by fun_prop)]
  rcases n with _ | _ | _ | n
  · simp [iteratedDeriv_const]
  · simp
  · simp [eq_comm]
  · have h₂ : (n : ℝ) + 1 + 1 ≠ 0 := by positivity
    have h₃ : (n : ℝ) + 1 + 1 + 1 ≠ 0 := by positivity
    simp [h₂, h₃]

/-- **Consecutive critical points of a function of one variable are joined by exactly one
trajectory.** Let `f` be `C²` near `[p, q]`, with `p < q` critical points of `f` and `f' < 0` on
`(p, q)`. Then there is a negative gradient trajectory `γ` of `f` with values in `(p, q)`, strictly
increasing, tending to `p` at `-∞` and to `q` at `+∞`, and every negative gradient trajectory of `f`
tending to `p` at `-∞` and to `q` at `+∞` is a time translate of `γ`. -/
theorem exists_isIntegralCurve_neg_gradient_of_deriv_neg {p q : ℝ} (hpq : p < q)
    (hf : ∀ y ∈ Icc p q, ContDiffAt ℝ 2 f y) (hp : deriv f p = 0) (hq : deriv f q = 0)
    (hneg : ∀ y ∈ Ioo p q, deriv f y < 0) :
    ∃ γ : ℝ → ℝ, IsIntegralCurve γ (fun _ y ↦ -∇ f y) ∧ StrictMono γ ∧ (∀ σ, γ σ ∈ Ioo p q) ∧
      Tendsto γ atBot (𝓝 p) ∧ Tendsto γ atTop (𝓝 q) ∧
      ∀ δ : ℝ → ℝ, IsIntegralCurve δ (fun _ y ↦ -∇ f y) → Tendsto δ atBot (𝓝 p) →
        Tendsto δ atTop (𝓝 q) → ∃ τ, δ = fun σ ↦ γ (σ + τ) := by
  -- On the line, the negative gradient field is `-f'`, which is `C¹`, so Lipschitz, on `[p, q]`.
  have hV : (fun y ↦ -∇ f y) = fun y ↦ -deriv f y := funext fun _ ↦ by rw [gradient_eq_deriv']
  obtain ⟨K, hK⟩ : ∃ K, LipschitzOnWith K (fun y ↦ -deriv f y) (Icc p q) :=
    ContDiffOn.exists_lipschitzOnWith (n := 1)
      (fun y hy ↦ ((hf y hy).derivWithin (by norm_num)).neg.contDiffWithinAt) one_ne_zero
      (convex_Icc p q) isCompact_Icc
  rw [hV]
  obtain ⟨γ, hγ, hmono, hmem, hbot, htop⟩ := exists_isIntegralCurve_tendsto_of_pos hpq hK
    (by simp [hp]) (by simp [hq]) fun y hy ↦ neg_pos.2 (hneg y hy)
  exact ⟨γ, hγ, hmono, hmem, hbot, htop, fun δ hδ hδp hδq ↦
    exists_eq_comp_add_of_isIntegralCurve_of_tendsto
      (fun _ _ ↦ ⟨K, Ioo p q, self_mem_nhdsWithin, hK.mono Ioo_subset_Icc_self⟩) hγ hmem hδ hδp
      hδq⟩

end TauCeti

end
