/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import TauCeti.Analysis.Calculus.ContDiff.PiecewiseC1On
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.LSeries.Nonvanishing
import TauCeti.Analysis.Contour.Argument.Variation
import TauCeti.NumberTheory.LSeries.RiemannZeta

/-!
# The argument of the Riemann zeta function on the critical line: `S(T)`

For a real `T ≠ 0` that is not the ordinate of a zero of `ζ`, Titchmarsh's `S(T)` is `π⁻¹` times
the change of a continuous argument of `ζ` along the path `2 → 2 + iT → 1/2 + iT`, made of a
vertical and a horizontal segment. It is the error term in the Riemann–von Mangoldt formula
`N(T) = θ(T)/π + 1 + S(T)`, where it carries the irregular part of the zero count.

The path is `TauCeti.LFunctions.riemannZetaSPath T` on `[0, 2]`. The quantity
`TauCeti.LFunctions.riemannZetaS T` is defined as `π⁻¹` times the imaginary part of the integral
of `ζ'/ζ` along it, which needs no choice of argument. For admissible `T` it is `π⁻¹ (θ 2 - θ 0)`
for every continuous argument `θ` of `ζ` along the path
(`TauCeti.LFunctions.riemannZetaS_eq_sub_div_pi`), and such an argument may be chosen to start
from the argument `0` of the positive real number `ζ(2)`, so that `S(T) = θ 2 / π`
(`TauCeti.LFunctions.exists_riemannZetaS_eq_div_pi`). Only zeros in `1/2 ≤ Re s < 1` need to be
excluded at height `T`: `ζ` has no zeros on `Re s ≥ 1`.

## References

* E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function*, 2nd ed., §9.3.
* H. Davenport, *Multiplicative Number Theory*, Chapter 15.
-/

public section

open Complex Set
open scoped Real

namespace TauCeti.LFunctions

/-- The path from `2` up to `2 + iT` on `[0, 1]`, then left to `1/2 + iT` on `[1, 2]`, along which
the argument of `ζ` defines `S(T)`. -/
noncomputable def riemannZetaSPath (T t : ℝ) : ℂ :=
  if t ≤ 1 then 2 + t * T * I else 2 - 3 / 2 * (t - 1) + T * I

variable {T t : ℝ}

/-- On `[0, 1]` the path runs up the vertical segment from `2` to `2 + iT`. -/
theorem riemannZetaSPath_of_le_one (ht : t ≤ 1) : riemannZetaSPath T t = 2 + t * T * I := by
  simp [riemannZetaSPath, ht]

/-- From time `1` the path runs left along the horizontal segment from `2 + iT` to `1/2 + iT`. -/
theorem riemannZetaSPath_of_one_le (ht : 1 ≤ t) :
    riemannZetaSPath T t = 2 - 3 / 2 * (t - 1) + T * I := by
  rcases ht.eq_or_lt with rfl | ht
  · simp [riemannZetaSPath]
  · simp [riemannZetaSPath, not_le.mpr ht]

/-- The path starts at `2`. -/
@[simp]
theorem riemannZetaSPath_zero : riemannZetaSPath T 0 = 2 := by
  simp [riemannZetaSPath_of_le_one zero_le_one]

/-- The path ends at `1/2 + iT`. -/
@[simp]
theorem riemannZetaSPath_two : riemannZetaSPath T 2 = 1 / 2 + T * I := by
  rw [riemannZetaSPath_of_one_le one_le_two]
  norm_num

/-- The path is piecewise `C¹` on `[0, 2]`. -/
theorem isPiecewiseC1On_riemannZetaSPath (T : ℝ) : IsPiecewiseC1On (riemannZetaSPath T) 0 2 := by
  have hof : ContDiff ℝ 1 ((↑) : ℝ → ℂ) := ofRealCLM.contDiff
  have h₁ : IsPiecewiseC1On (fun t : ℝ ↦ 2 + t * T * I) 0 1 :=
    .of_contDiffOn (by fun_prop)
  have h₂ : IsPiecewiseC1On (fun t : ℝ ↦ 2 - 3 / 2 * (t - 1) + T * I) 1 2 :=
    .of_contDiffOn (by fun_prop)
  exact h₁.if_le h₂ zero_le_one one_le_two (by push_cast; ring)

/-- Away from height `0` the path avoids the pole of `ζ` at `1`. -/
theorem riemannZetaSPath_ne_one (hT : T ≠ 0) (t : ℝ) : riemannZetaSPath T t ≠ 1 := by
  intro h
  rcases le_total t 1 with h1 | h1
  · rw [riemannZetaSPath_of_le_one h1] at h
    have := congrArg re h
    simp at this
  · rw [riemannZetaSPath_of_one_le h1] at h
    have := congrArg im h
    simp [hT] at this

/-- If `ζ` has no zero on `[1/2, 1) + iT`, it has no zero along the path on `[0, 2]`. -/
theorem riemannZeta_riemannZetaSPath_ne_zero
    (hT : ∀ σ ∈ Ico (1 / 2 : ℝ) 1, riemannZeta (σ + T * I) ≠ 0) (ht : t ∈ Icc (0 : ℝ) 2) :
    riemannZeta (riemannZetaSPath T t) ≠ 0 := by
  rcases le_total t 1 with h1 | h1
  · rw [riemannZetaSPath_of_le_one h1]
    exact riemannZeta_ne_zero_of_one_le_re (by simp)
  · rw [riemannZetaSPath_of_one_le h1]
    by_cases hσ : 1 ≤ 2 - 3 / 2 * (t - 1)
    · exact riemannZeta_ne_zero_of_one_le_re (by simpa using hσ)
    · have h := hT (2 - 3 / 2 * (t - 1)) ⟨by linarith [ht.2], not_le.mp hσ⟩
      push_cast at h
      exact h

/-- If a real number `x` is `‖x‖ · exp (i θ)`, then `x = |x| cos θ`. -/
private theorem eq_abs_mul_cos_of_ofReal_eq {x θ : ℝ} (h : (x : ℂ) = ‖(x : ℂ)‖ * exp (I * θ)) :
    x = |x| * Real.cos θ := by
  have h' := congrArg re h
  rwa [ofReal_re, norm_real, Real.norm_eq_abs, mul_comm I, re_ofReal_mul,
    exp_ofReal_mul_I_re] at h'

/-- At height `0` the path runs along the real axis through the pole of `ζ` at `1`, across which
`ζ` changes sign, so `ζ` has no continuous argument along it. -/
private theorem not_exists_continuousOn_arg_riemannZetaSPath_zero :
    ¬ ∃ θ : ℝ → ℝ, ContinuousOn θ (Icc 0 2) ∧ ∀ t ∈ Icc (0 : ℝ) 2,
      riemannZeta (riemannZetaSPath 0 t) =
        ‖riemannZeta (riemannZetaSPath 0 t)‖ * exp (I * θ t) := by
  rintro ⟨θ, hθ, hlift⟩
  -- On the horizontal segment at height `0`, `ζ` is a real number `x` with `x = |x| cos θ`.
  have hcos (t : ℝ) (ht : t ∈ Icc (4 / 3 : ℝ) 2) :
      (riemannZeta (2 - 3 / 2 * (t - 1) : ℝ)).im = 0 →
        (riemannZeta (2 - 3 / 2 * (t - 1) : ℝ)).re =
          |(riemannZeta (2 - 3 / 2 * (t - 1) : ℝ)).re| * Real.cos (θ t) := fun him ↦ by
    have h := hlift t ⟨by linarith [ht.1], by linarith [ht.2]⟩
    rw [riemannZetaSPath_of_one_le (by linarith [ht.1]),
      show (2 - 3 / 2 * (t - 1) + (0 : ℝ) * I : ℂ) = ((2 - 3 / 2 * (t - 1) : ℝ) : ℂ) by
        push_cast; ring,
      ← re_add_im (riemannZeta _), him, ofReal_zero, zero_mul, add_zero] at h
    exact eq_abs_mul_cos_of_ofReal_eq h
  have hc : ContinuousOn (fun t ↦ Real.cos (θ t)) (Icc (4 / 3) 2) :=
    Real.continuous_cos.comp_continuousOn (hθ.mono (Icc_subset_Icc (by norm_num) (by norm_num)))
  -- Just before time `5/3` the path is at a real point `σ > 1`, where `ζ σ > 0`, so `cos θ = 1`.
  have hpos : EqOn (fun t ↦ Real.cos (θ t)) (fun _ ↦ 1) (Ioo (4 / 3) (5 / 3)) := by
    intro t ht
    have hσ : 1 < 2 - 3 / 2 * (t - 1) := by linarith [ht.2]
    have hx := hcos t (Ioo_subset_Icc_self ⟨ht.1, by linarith [ht.2]⟩)
      (riemannZeta_im_eq_zero_of_one_lt hσ)
    have hre := riemannZeta_re_pos_of_one_lt hσ
    rw [abs_of_pos hre] at hx
    simpa using (mul_eq_left₀ hre.ne').mp hx.symm
  -- Just after time `5/3` the path is at a real point `1/2 < σ < 1`, where `ζ σ < 0`, so
  -- `cos θ = -1`.
  have hneg : EqOn (fun t ↦ Real.cos (θ t)) (fun _ ↦ -1) (Ioo (5 / 3) 2) := by
    intro t ht
    have hlt := Complex.lt_def.mp
      (riemannZeta_lt_zero (σ := 2 - 3 / 2 * (t - 1)) (by linarith [ht.2]) (by linarith [ht.1]))
    have hx := hcos t (Ioo_subset_Icc_self ⟨by linarith [ht.1], ht.2⟩) hlt.2
    rw [abs_of_neg hlt.1] at hx
    have h' : (riemannZeta (2 - 3 / 2 * (t - 1) : ℝ)).re * (Real.cos (θ t) + 1) = 0 := by
      linear_combination hx
    simp only
    linarith [(mul_eq_zero.mp h').resolve_left hlt.1.ne]
  -- By continuity `cos (θ (5/3))` is both `1` and `-1`.
  have h1 := hpos.of_subset_closure (hc.mono (Icc_subset_Icc le_rfl (by norm_num)))
    continuousOn_const Ioo_subset_Icc_self (by rw [closure_Ioo (by norm_num)])
    (right_mem_Icc.mpr (by norm_num))
  have h2 := hneg.of_subset_closure (hc.mono (Icc_subset_Icc (by norm_num) le_rfl))
    continuousOn_const Ioo_subset_Icc_self (by rw [closure_Ioo (by norm_num)])
    (left_mem_Icc.mpr (by norm_num))
  linarith

/-- **Titchmarsh's `S(T)`**: `π⁻¹` times the imaginary part of the integral of `ζ'/ζ` along the
path `2 → 2 + iT → 1/2 + iT`. When `T ≠ 0` and `ζ` has no zero at height `T` with
`1/2 ≤ Re s < 1`, a continuous argument of `ζ` along the path exists, and this is `π⁻¹` times its
change (`TauCeti.LFunctions.riemannZetaS_eq_sub_div_pi`,
`TauCeti.LFunctions.exists_riemannZetaS_eq_div_pi`). At other heights the value carries no
meaning. -/
noncomputable def riemannZetaS (T : ℝ) : ℝ :=
  π⁻¹ * (∫ t in (0 : ℝ)..2,
    deriv (riemannZetaSPath T) t • logDeriv riemannZeta (riemannZetaSPath T t)).im

/-- `S(T)` is `π⁻¹` times the imaginary part of the integral of `ζ'/ζ` along the path. -/
theorem riemannZetaS_def (T : ℝ) : riemannZetaS T = π⁻¹ * (∫ t in (0 : ℝ)..2,
    deriv (riemannZetaSPath T) t • logDeriv riemannZeta (riemannZetaSPath T t)).im := (rfl)

/-- **`S(T)` is the variation of a continuous argument of `ζ`.** If `ζ` has no zero at height `T`
with `1/2 ≤ Re s < 1`, then for every continuous argument `θ` of `ζ` along the path
`2 → 2 + iT → 1/2 + iT` on `[0, 2]`, `S(T) = (θ 2 - θ 0) / π`. At height `0` there is no such
argument, since the path crosses the pole of `ζ` at `1`. -/
theorem riemannZetaS_eq_sub_div_pi
    (hT : ∀ σ ∈ Ico (1 / 2 : ℝ) 1, riemannZeta (σ + T * I) ≠ 0) {θ : ℝ → ℝ}
    (hθ : ContinuousOn θ (Icc 0 2))
    (hlift : ∀ t ∈ Icc (0 : ℝ) 2,
      riemannZeta (riemannZetaSPath T t) = ‖riemannZeta (riemannZetaSPath T t)‖ * exp (I * θ t)) :
    riemannZetaS T = (θ 2 - θ 0) / π := by
  rcases eq_or_ne T 0 with rfl | hT0
  · exact absurd ⟨θ, hθ, hlift⟩ not_exists_continuousOn_arg_riemannZetaSPath_zero
  rw [riemannZetaS_def, TauCeti.Contour.integral_deriv_smul_logDeriv_eq_log_norm_add_I_mul_sub
    zero_le_two (isPiecewiseC1On_riemannZetaSPath T)
    (fun t _ ↦ analyticOn_riemannZeta _ (riemannZetaSPath_ne_one hT0 t))
    (fun t ht ↦ riemannZeta_riemannZetaSPath_ne_zero hT ht) hθ hlift]
  simp [div_eq_inv_mul]

/-- **`S(T)` from the argument of `ζ` started at `ζ(2)`.** If `T ≠ 0` and `ζ` has no zero at height
`T` with `1/2 ≤ Re s < 1`, there is a continuous argument `θ` of `ζ` along the path
`2 → 2 + iT → 1/2 + iT` on `[0, 2]` with `θ 0 = 0`, the argument of the positive real number
`ζ(2)`, and then `S(T) = θ 2 / π`. -/
theorem exists_riemannZetaS_eq_div_pi (hT0 : T ≠ 0)
    (hT : ∀ σ ∈ Ico (1 / 2 : ℝ) 1, riemannZeta (σ + T * I) ≠ 0) :
    ∃ θ : ℝ → ℝ, ContinuousOn θ (Icc 0 2) ∧ (∀ t ∈ Icc (0 : ℝ) 2,
      riemannZeta (riemannZetaSPath T t) = ‖riemannZeta (riemannZetaSPath T t)‖ * exp (I * θ t)) ∧
      θ 0 = 0 ∧ riemannZetaS T = θ 2 / π := by
  have hc : ContinuousOn (fun t ↦ riemannZeta (riemannZetaSPath T t)) (Icc 0 2) := fun t ht ↦
    (analyticOn_riemannZeta _ (riemannZetaSPath_ne_one hT0 t)).continuousAt.comp_continuousWithinAt
      (((isPiecewiseC1On_riemannZetaSPath T).continuousOn.mono (by simp)) t ht)
  obtain ⟨θ, hθ, hlift⟩ := TauCeti.Contour.exists_continuousOn_eq_norm_mul_exp hc
    fun t ht ↦ riemannZeta_riemannZetaSPath_ne_zero hT ht
  -- `ζ(2)` is a positive real, so `exp (i θ 0) = 1`.
  have h0 : exp (I * θ 0) = 1 := by
    have h := hlift 0 (by simp)
    rw [riemannZetaSPath_zero, riemannZeta_two] at h
    have hpos : (0 : ℝ) < π ^ 2 / 6 := by positivity
    have hn : ‖(π : ℂ) ^ 2 / 6‖ = π ^ 2 / 6 := by
      rw [← ofReal_pow, ← ofReal_ofNat, ← ofReal_div, norm_real, Real.norm_of_nonneg hpos.le]
    rw [hn] at h
    have hne : ((π ^ 2 / 6 : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hpos.ne'
    push_cast at h hne
    exact (mul_eq_left₀ hne).mp h.symm
  have hlift' : ∀ t ∈ Icc (0 : ℝ) 2, riemannZeta (riemannZetaSPath T t) =
      ‖riemannZeta (riemannZetaSPath T t)‖ * exp (I * (θ t - θ 0 : ℝ)) := fun t ht ↦ by
    rw [ofReal_sub, mul_sub, exp_sub, h0, div_one, ← hlift t ht]
  refine ⟨fun t ↦ θ t - θ 0, hθ.sub continuousOn_const, hlift', sub_self _, ?_⟩
  rw [riemannZetaS_eq_sub_div_pi hT (hθ.sub continuousOn_const) hlift']
  simp

end TauCeti.LFunctions
