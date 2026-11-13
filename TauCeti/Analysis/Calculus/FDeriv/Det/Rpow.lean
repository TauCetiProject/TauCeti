/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Analysis.Calculus.FDeriv.Det.Basic
public import TauCeti.Analysis.Calculus.Deriv.Matrix
public import TauCeti.LinearAlgebra.Matrix.Trace.Riccati
public import Mathlib.Analysis.Calculus.Deriv.Abs
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Real powers of the absolute determinant

At a nonsingular real matrix, the logarithmic derivative of `|det J| ^ r` is
`r * trace (J' * J⁻¹)`. Differentiating this identity once more gives the scalar differential
inequality for a determinant density root under a symmetric matrix Riccati equation.

These statements concern actual matrix curves and their derivatives. A geometric application
must separately identify the Jacobi matrix, its symmetry and its curvature trace bound.

Formalization references:
[lean-eval-submissions](https://github.com/frenzymath/lean-eval-submissions)
and [PoincareConjecture](https://github.com/frenzymath/PoincareConjecture).
-/

public section

open Filter
open scoped Topology Matrix.Norms.Operator

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The logarithmic derivative of a real power of an absolute determinant. The exponent is
arbitrary, and the matrix index may be empty. -/
theorem hasDerivAt_abs_det_rpow {J : ℝ → Matrix ι ι ℝ} {V : Matrix ι ι ℝ} {r t : ℝ}
    (hJ : HasDerivAt J V t) (hne : (J t).det ≠ 0) :
    HasDerivAt (fun s ↦ |(J s).det| ^ r)
      (r * (V * (J t)⁻¹).trace * |(J t).det| ^ r) t := by
  have hd : HasDerivAt (fun s ↦ (J s).det)
      ((J t).det * ((J t)⁻¹ * V).trace) t := by
    have hd := (differentiable_det (J t)).hasFDerivAt.comp_hasDerivAt t hJ
    convert! hd using 1
    exact (fderiv_det_apply hne.isUnit V).symm
  rw [trace_mul_comm] at hd
  have ha : HasDerivAt (fun s ↦ |(J s).det|)
      (|(J t).det| * (V * (J t)⁻¹).trace) t := by
    convert! (hasDerivAt_abs hne).comp t hd using 1
    obtain hn | hp := hne.lt_or_gt
    · simp [hn, abs_of_neg hn]
    · simp [hp, abs_of_pos hp]
  have hp : 0 < |(J t).det| := abs_pos.mpr hne
  have heq : (|(J t).det| * (V * (J t)⁻¹).trace) * r * |(J t).det| ^ (r - 1) =
      r * (V * (J t)⁻¹).trace * |(J t).det| ^ r := by
    rw [Real.rpow_sub hp, Real.rpow_one]
    field_simp
  exact heq ▸ ha.rpow_const (Or.inl hp.ne')

/-- The second derivative of a real power of an absolute determinant, using a germ of matrix
velocities and the derivative of the logarithmic trace. -/
theorem hasDerivAt_deriv_abs_det_rpow {J V : ℝ → Matrix ι ι ℝ} {r t h' : ℝ}
    (hJ : ∀ᶠ s in 𝓝 t, HasDerivAt J (V s) s) (hne : (J t).det ≠ 0)
    (hh : HasDerivAt (fun s ↦ (V s * (J s)⁻¹).trace) h' t) :
    HasDerivAt (deriv (fun s ↦ |(J s).det| ^ r))
      ((r * h' + (r * (V t * (J t)⁻¹).trace) ^ 2) * |(J t).det| ^ r) t := by
  have hd := hasDerivAt_abs_det_rpow (r := r) hJ.self_of_nhds hne
  have hc := (differentiable_det (J t)).continuousAt.comp hJ.self_of_nhds.continuousAt
  have hp : ∀ᶠ s in 𝓝 t, (J s).det ≠ 0 := hc.eventually_ne hne
  have heq : deriv (fun s ↦ |(J s).det| ^ r) =ᶠ[𝓝 t]
      (fun s ↦ r * (V s * (J s)⁻¹).trace * |(J s).det| ^ r) := by
    filter_upwards [hJ, hp] with s hs hsp
    exact (hasDerivAt_abs_det_rpow hs hsp).deriv
  convert! (((hh.const_mul r).mul hd).congr_of_eventuallyEq heq) using 1; ring

/-- A symmetric Riccati equation and a lower curvature-trace bound give the scalar
second-derivative bound for the absolute determinant root in positive dimension. -/
theorem deriv2_abs_det_rpow_le_of_riccati {J V : ℝ → Matrix ι ι ℝ} {K : Matrix ι ι ℝ}
    {κ t : ℝ} (hm : 0 < Fintype.card ι)
    (hJ : ∀ᶠ s in 𝓝 t, HasDerivAt J (V s) s) (hne : (J t).det ≠ 0)
    (hS : (V t * (J t)⁻¹).IsSymm)
    (hS' : HasDerivAt (fun s ↦ V s * (J s)⁻¹)
      (-((V t * (J t)⁻¹) * (V t * (J t)⁻¹)) - K) t)
    (hRic : -(Fintype.card ι : ℝ) * κ ≤ K.trace) :
    deriv (deriv (fun s ↦ |(J s).det| ^ (1 / (Fintype.card ι : ℝ)))) t ≤
      κ * |(J t).det| ^ (1 / (Fintype.card ι : ℝ)) := by
  have hh := hS'.matrix_trace
  rw [(hasDerivAt_deriv_abs_det_rpow hJ hne hh).deriv]
  have hm' : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr hm
  have htrace := trace_add_sq_trace_div_card_le_card_mul hS rfl hRic
  have hcoef : (1 / (Fintype.card ι : ℝ)) *
        (-((V t * (J t)⁻¹) * (V t * (J t)⁻¹)) - K).trace +
      (1 / (Fintype.card ι : ℝ) * (V t * (J t)⁻¹).trace) ^ 2 ≤ κ := by
    have heq (a b m : ℝ) (hm : m ≠ 0) :
        1 / m * a + (1 / m * b) ^ 2 = (a + b ^ 2 / m) / m := by field_simp
    rw [heq _ _ _ hm'.ne']
    exact (div_le_iff₀ hm').mpr (by simpa only [mul_comm] using htrace)
  exact mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg (abs_nonneg _) _)

end Matrix
