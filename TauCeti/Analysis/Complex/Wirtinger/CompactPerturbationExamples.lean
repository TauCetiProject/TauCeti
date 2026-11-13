/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import TauCeti.Analysis.Complex.Wirtinger.Holomorphic

/-!
# The compact perturbation `\bar∂ + 1` and its kernel

As background, not established here: realized as a Fredholm operator between Sobolev spaces of
functions over the unit disc with real boundary values, the Cauchy–Riemann operator `\bar∂` has
index `1` and its kernel consists of the real constants, and the compact zeroth-order perturbation
`\bar∂ + 1` has the same index. This file records the pointwise kernel computation behind that
example, which is a check on the compact-perturbation statement for real Cauchy–Riemann
operators: the perturbation changes the kernel.

The integrating factor `e^{conj z}` turns `\bar∂ + 1` into `\bar∂`: for `ξ` real differentiable,
`\bar∂(e^{conj z} ξ) = e^{conj z} (\bar∂ξ + ξ)`, since `\bar∂ e^{conj z} = e^{conj z}`. Hence the
solutions of `\bar∂ξ + ξ = 0` on an open set are exactly the maps `e^{-conj z} h` with `h`
holomorphic. A nonzero constant `c` is not a solution, because `(\bar∂ + 1) c = c`. On the other
hand `e^{-2 s} = e^{-conj z} e^{-z}` (with `z = s + i t`) is a nonzero solution which is real on
the whole plane, in particular on the unit circle. So the kernel with real boundary values
contains `e^{-2 s}` and no nonzero constant.

The companion check for the deformation statement, that the zeroth-order term `t / (1 - t)` has
`L^p` norm tending to infinity as `t → 1⁻`, is
`MeasureTheory.Measure.tendsto_norm_lpConst_div_one_sub` in
`TauCeti/MeasureTheory/Function/Lp/Const.lean`.

Here `\bar∂ξ` is `conjWirtingerDeriv ξ z 1 = (∂ₛξ + i ∂ₜξ) / 2`.

## Main results

* `Complex.conjWirtingerDeriv_cexp_conj_apply_one`: `\bar∂ e^{conj z} = e^{conj z}`.
* `TauCeti.conjWirtingerDeriv_cexp_conj_smul_apply_one`: the integrating factor identity
  `\bar∂(e^{conj z} ξ) = e^{conj z} (\bar∂ξ + ξ)`.
* `TauCeti.differentiableAt_cexp_conj_smul_iff`: `e^{conj z} ξ` is complex differentiable at `z`
  exactly when `\bar∂ξ + ξ = 0` there.
* `TauCeti.conjWirtingerDeriv_add_eq_zero_iff_exists_eq_cexp_neg_conj_smul`: on an open set, the
  solutions of `\bar∂ξ + ξ = 0` are the maps `e^{-conj z} h` with `h` holomorphic.
* `Complex.conjWirtingerDeriv_ofReal_exp_neg_two_mul_re_apply_one_add`: `e^{-2 s}` solves
  `\bar∂ξ + ξ = 0`.
* `TauCeti.compactPerturbation_disc_kernel_check`: on the unit disc with real values on the unit
  circle, the constants solving `\bar∂ξ = 0` are the real ones, the only constant solving
  `\bar∂ξ + ξ = 0` is `0`, and `e^{-2 s}` solves `\bar∂ξ + ξ = 0`.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Appendix C.1.
-/

public section

open Complex Filter Metric Set
open scoped ComplexConjugate

namespace Complex

open TauCeti

/-- The real derivative of `w ↦ e^{conj w}`. -/
theorem hasFDerivAt_cexp_conj (z : ℂ) :
    HasFDerivAt (fun w : ℂ ↦ cexp (conj w))
      (cexp (conj z) • (conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap) z :=
  (conjCLE : ℂ ≃L[ℝ] ℂ).hasFDerivAt.cexp

/-- In the coordinate `z = s + i t`, `e^{-2 s} = e^{-conj z} e^{-z}`. -/
theorem ofReal_exp_neg_two_mul_re (z : ℂ) :
    ((Real.exp (-2 * z.re) : ℝ) : ℂ) = cexp (-conj z) * cexp (-z) := by
  rw [ofReal_exp, ← exp_add]
  congr 1
  apply Complex.ext <;> simp; ring

/-! ### The integrating factor `e^{conj z}` -/

/-- The antiholomorphic exponential is its own conjugate Wirtinger derivative:
`\bar∂ e^{conj z} = e^{conj z}`. -/
theorem conjWirtingerDeriv_cexp_conj_apply_one (z : ℂ) :
    conjWirtingerDeriv (fun w : ℂ ↦ cexp (conj w)) z 1 = cexp (conj z) := by
  rw [conjWirtingerDeriv_apply, (hasFDerivAt_cexp_conj z).fderiv]
  simp only [smul_apply, ContinuousLinearEquiv.coe_coe, conjCLE_apply, map_one, smul_eq_mul,
    mul_one, conj_I]
  linear_combination -cexp (conj z) / 2 * I_sq

end Complex

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **The integrating factor** for `\bar∂ + 1`: `\bar∂(e^{conj z} ξ) = e^{conj z} (\bar∂ξ + ξ)`. -/
theorem conjWirtingerDeriv_cexp_conj_smul_apply_one {ξ : ℂ → E} {z : ℂ}
    (hξ : DifferentiableAt ℝ ξ z) :
    conjWirtingerDeriv (fun w ↦ cexp (conj w) • ξ w) z 1 =
      cexp (conj z) • (conjWirtingerDeriv ξ z 1 + ξ z) := by
  rw [conjWirtingerDeriv_smul_apply (hasFDerivAt_cexp_conj z).differentiableAt hξ,
    conjWirtingerDeriv_cexp_conj_apply_one, smul_add]

/-- A real-differentiable `ξ` solves `\bar∂ξ + ξ = 0` at `z` exactly when `e^{conj z} ξ` is complex
differentiable at `z`. -/
theorem differentiableAt_cexp_conj_smul_iff {ξ : ℂ → E} {z : ℂ}
    (hξ : DifferentiableAt ℝ ξ z) :
    DifferentiableAt ℂ (fun w ↦ cexp (conj w) • ξ w) z ↔
      conjWirtingerDeriv ξ z 1 + ξ z = 0 := by
  have hd : DifferentiableAt ℝ (fun w ↦ cexp (conj w) • ξ w) z :=
    (hasFDerivAt_cexp_conj z).differentiableAt.smul hξ
  rw [differentiableAt_iff_conjWirtingerDeriv_apply_one_eq_zero hd,
    conjWirtingerDeriv_cexp_conj_smul_apply_one hξ, smul_eq_zero_iff_right (exp_ne_zero _)]

/-- **The kernel of `\bar∂ + 1`.** On an open set `Ω`, a map `ξ` is real differentiable with
`\bar∂ξ + ξ = 0` exactly when `ξ = e^{-conj z} h` on `Ω` for a map `h` holomorphic on `Ω`. -/
theorem conjWirtingerDeriv_add_eq_zero_iff_exists_eq_cexp_neg_conj_smul {ξ : ℂ → E}
    {Ω : Set ℂ} (hΩ : IsOpen Ω) :
    (DifferentiableOn ℝ ξ Ω ∧ ∀ z ∈ Ω, conjWirtingerDeriv ξ z 1 + ξ z = 0) ↔
      ∃ h : ℂ → E, DifferentiableOn ℂ h Ω ∧ EqOn ξ (fun z ↦ cexp (-conj z) • h z) Ω := by
  constructor
  · rintro ⟨hξ, h0⟩
    refine ⟨fun w ↦ cexp (conj w) • ξ w, fun z hz ↦ ?_, fun z _ ↦ ?_⟩
    · exact ((differentiableAt_cexp_conj_smul_iff ((hξ z hz).differentiableAt
        (hΩ.mem_nhds hz))).2 (h0 z hz)).differentiableWithinAt
    · simp only [smul_smul, ← exp_add, neg_add_cancel, exp_zero, one_smul]
  · rintro ⟨h, hh, hξ⟩
    have hd : ∀ z ∈ Ω, DifferentiableAt ℝ ξ z := fun z hz ↦
      ((((conjCLE : ℂ ≃L[ℝ] ℂ).differentiableAt.neg).cexp.smul
        ((hh.differentiableAt (hΩ.mem_nhds hz)).restrictScalars ℝ))).congr_of_eventuallyEq
        (eventuallyEq_of_mem (hΩ.mem_nhds hz) hξ)
    refine ⟨fun z hz ↦ (hd z hz).differentiableWithinAt, fun z hz ↦ ?_⟩
    rw [← differentiableAt_cexp_conj_smul_iff (hd z hz)]
    refine (hh.differentiableAt (hΩ.mem_nhds hz)).congr_of_eventuallyEq ?_
    filter_upwards [hΩ.mem_nhds hz] with w hw
    rw [hξ hw, smul_smul, ← exp_add, add_neg_cancel, exp_zero, one_smul]

end TauCeti

namespace Complex

open TauCeti

/-! ### Constants and the solution `e^{-2 s}` -/

/-- The real function `e^{-2 s}` solves `\bar∂ξ + ξ = 0` on the whole plane. -/
theorem conjWirtingerDeriv_ofReal_exp_neg_two_mul_re_apply_one_add (z : ℂ) :
    conjWirtingerDeriv (fun w : ℂ ↦ ((Real.exp (-2 * w.re) : ℝ) : ℂ)) z 1 +
      ((Real.exp (-2 * z.re) : ℝ) : ℂ) = 0 :=
  ((conjWirtingerDeriv_add_eq_zero_iff_exists_eq_cexp_neg_conj_smul isOpen_univ).2
    ⟨fun w : ℂ ↦ cexp (-w), (differentiable_id.neg.cexp).differentiableOn,
      fun (w : ℂ) _ ↦ by simp only [smul_eq_mul, ofReal_exp_neg_two_mul_re]⟩).2 z (mem_univ z)

end Complex

namespace TauCeti

/-- **Check: compact perturbation changes the kernel.** On the unit disc with real values on the
unit circle:
* a constant is in the kernel of `\bar∂` exactly when it is real;
* the only constant in the kernel of `\bar∂ + 1` is `0`;
* the function `e^{-2 s}`, which is nonzero and real everywhere, is in the kernel of `\bar∂ + 1`.

So the kernel changes under the compact perturbation `\bar∂ ↦ \bar∂ + 1`. -/
theorem compactPerturbation_disc_kernel_check :
    (∀ c : ℂ, ((∀ z ∈ ball (0 : ℂ) 1, conjWirtingerDeriv (fun _ : ℂ ↦ c) z 1 = 0) ∧
        ∀ z ∈ sphere (0 : ℂ) 1, c.im = 0) ↔ c.im = 0) ∧
    (∀ c : ℂ, ((∀ z ∈ ball (0 : ℂ) 1, conjWirtingerDeriv (fun _ : ℂ ↦ c) z 1 + c = 0) ∧
        ∀ z ∈ sphere (0 : ℂ) 1, c.im = 0) ↔ c = 0) ∧
    (DifferentiableOn ℝ (fun w : ℂ ↦ ((Real.exp (-2 * w.re) : ℝ) : ℂ)) (ball 0 1) ∧
      (∀ z ∈ ball (0 : ℂ) 1, conjWirtingerDeriv (fun w : ℂ ↦ ((Real.exp (-2 * w.re) : ℝ) : ℂ))
        z 1 + ((Real.exp (-2 * z.re) : ℝ) : ℂ) = 0) ∧
      (∀ z ∈ sphere (0 : ℂ) 1, (((Real.exp (-2 * z.re) : ℝ) : ℂ)).im = 0) ∧
      ∀ z : ℂ, ((Real.exp (-2 * z.re) : ℝ) : ℂ) ≠ 0) := by
  have h1 : (1 : ℂ) ∈ sphere (0 : ℂ) 1 := by simp
  refine ⟨fun c ↦ ⟨fun h ↦ h.2 1 h1, fun h ↦ ⟨fun z _ ↦ ?_, fun _ _ ↦ h⟩⟩,
    fun c ↦ ⟨fun h ↦ ?_, fun h ↦ ⟨fun z _ ↦ ?_, fun _ _ ↦ by simp [h]⟩⟩, ?_, fun z _ ↦
      conjWirtingerDeriv_ofReal_exp_neg_two_mul_re_apply_one_add z, fun z _ ↦ ofReal_im _,
      fun z ↦ ofReal_ne_zero.2 (Real.exp_pos _).ne'⟩
  · simp
  · simpa using h.1 0 (by simp)
  · simp [h]
  · exact fun z _ ↦ (Complex.ofRealCLM.differentiableAt.comp z
      ((Real.differentiableAt_exp).comp z
        ((reCLM.differentiableAt).const_mul (-2)))).differentiableWithinAt

end TauCeti
