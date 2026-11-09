/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import TauCeti.Analysis.Complex.Wirtinger.Basic

/-!
# Monomials times radial profiles

For a real profile `C : ℝ → ℝ` with derivative `c` at `‖z‖²`, this file computes the real
derivative and the conjugate Wirtinger derivative of the radial function `z ↦ C(‖z‖²)` and of the
product `z ↦ zⁿ C(‖z‖²)`, together with the corresponding operator-norm bounds:

* `TauCeti.hasFDerivAt_ofReal_comp_norm_sq`: the derivative of `z ↦ C(‖z‖²)` is
  `v ↦ 2 C'(‖z‖²) Re (v conj z)` (`TauCeti.fderiv_ofReal_comp_norm_sq_apply`), of norm at most
  `2 |C'(‖z‖²)| ‖z‖` (`TauCeti.norm_fderiv_ofReal_comp_norm_sq_le`);
* `TauCeti.conjWirtingerDeriv_ofReal_comp_norm_sq_apply_one`: `\bar∂ C(‖z‖²) = C'(‖z‖²) z`;
* `TauCeti.contDiffAt_pow_mul_ofReal_comp_norm_sq`: `z ↦ zⁿ C(‖z‖²)` is as regular as `C`;
* `TauCeti.norm_fderiv_pow_mul_ofReal_comp_norm_sq_le`: the product rule bound for its
  derivative;
* `TauCeti.conjWirtingerDeriv_pow_mul_ofReal_comp_norm_sq_apply_one`:
  `\bar∂ (zⁿ C(‖z‖²)) = zⁿ C'(‖z‖²) z`, since `zⁿ` is holomorphic.
-/

public section

open Complex ComplexConjugate

namespace TauCeti

variable {C : ℝ → ℝ} {c : ℝ} {z : ℂ}

/-- The derivative of a radial function `z ↦ C(‖z‖²)`. -/
theorem hasFDerivAt_ofReal_comp_norm_sq (h : HasDerivAt C c (‖z‖ ^ 2)) :
    HasFDerivAt (fun w : ℂ ↦ (C (‖w‖ ^ 2) : ℂ))
      (ofRealCLM ∘L (c • (2 • innerSL ℝ z))) z :=
  ofRealCLM.hasFDerivAt.comp z (h.comp_hasFDerivAt z (hasStrictFDerivAt_norm_sq z).hasFDerivAt)

/-- The derivative of `z ↦ C(‖z‖²)` in direction `v` is `2 C'(‖z‖²) Re (v conj z)`. -/
theorem fderiv_ofReal_comp_norm_sq_apply (h : HasDerivAt C c (‖z‖ ^ 2)) (v : ℂ) :
    fderiv ℝ (fun w : ℂ ↦ (C (‖w‖ ^ 2) : ℂ)) z v = (2 * c * (v * conj z).re : ℝ) := by
  rw [(hasFDerivAt_ofReal_comp_norm_sq h).fderiv]
  simp [Complex.inner]
  ring

/-- The derivative of `z ↦ C(‖z‖²)` has norm at most `2 |C'(‖z‖²)| ‖z‖`. -/
theorem norm_fderiv_ofReal_comp_norm_sq_le (h : HasDerivAt C c (‖z‖ ^ 2)) :
    ‖fderiv ℝ (fun w : ℂ ↦ (C (‖w‖ ^ 2) : ℂ)) z‖ ≤ 2 * |c| * ‖z‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v ↦ ?_
  rw [fderiv_ofReal_comp_norm_sq_apply h, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul]
  calc |2| * |c| * |(v * conj z).re| ≤ 2 * |c| * ‖v * conj z‖ := by
        rw [abs_two]; gcongr; exact abs_re_le_norm _
    _ = 2 * |c| * ‖z‖ * ‖v‖ := by rw [norm_mul, Complex.norm_conj]; ring

/-- `\bar∂ C(‖z‖²) = C'(‖z‖²) z`. -/
theorem conjWirtingerDeriv_ofReal_comp_norm_sq_apply_one (h : HasDerivAt C c (‖z‖ ^ 2)) :
    conjWirtingerDeriv (fun w : ℂ ↦ (C (‖w‖ ^ 2) : ℂ)) z 1 = c * z := by
  rw [conjWirtingerDeriv_apply, fderiv_ofReal_comp_norm_sq_apply h,
    fderiv_ofReal_comp_norm_sq_apply h]
  apply Complex.ext <;> simp <;> ring

/-- The real derivative of `w ↦ wⁿ` has norm at most `n ‖z‖ⁿ⁻¹`. -/
theorem norm_fderiv_pow_le (n : ℕ) (z : ℂ) :
    ‖fderiv ℝ (fun w : ℂ ↦ w ^ n) z‖ ≤ n * ‖z‖ ^ (n - 1) := by
  rw [((hasDerivAt_pow n z).hasFDerivAt.restrictScalars ℝ).fderiv]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v ↦ ?_
  simp [mul_comm]

variable (n : ℕ)

/-- `z ↦ zⁿ C(‖z‖²)` is as regular as `C` at `‖z‖²`. -/
theorem contDiffAt_pow_mul_ofReal_comp_norm_sq {m : WithTop ℕ∞}
    (hC : ContDiffAt ℝ m C (‖z‖ ^ 2)) :
    ContDiffAt ℝ m (fun w : ℂ ↦ w ^ n * (C (‖w‖ ^ 2) : ℂ)) z :=
  (contDiffAt_id.pow n).mul
    (ofRealCLM.contDiff.contDiffAt.comp z (hC.comp z (contDiffAt_id.norm_sq ℝ)))

/-- The product rule bound for the derivative of `z ↦ zⁿ C(‖z‖²)`. -/
theorem norm_fderiv_pow_mul_ofReal_comp_norm_sq_le (h : HasDerivAt C c (‖z‖ ^ 2)) :
    ‖fderiv ℝ (fun w : ℂ ↦ w ^ n * (C (‖w‖ ^ 2) : ℂ)) z‖ ≤
      ‖z‖ ^ n * (2 * |c| * ‖z‖) + |C (‖z‖ ^ 2)| * (n * ‖z‖ ^ (n - 1)) := by
  have hp : DifferentiableAt ℝ (fun w : ℂ ↦ w ^ n) z := by fun_prop
  rw [fderiv_fun_mul hp (hasFDerivAt_ofReal_comp_norm_sq h).differentiableAt]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  gcongr
  · exact norm_fderiv_ofReal_comp_norm_sq_le h
  · exact norm_fderiv_pow_le n z

/-- `\bar∂ (zⁿ C(‖z‖²)) = zⁿ C'(‖z‖²) z`, since `zⁿ` is holomorphic. -/
theorem conjWirtingerDeriv_pow_mul_ofReal_comp_norm_sq_apply_one
    (h : HasDerivAt C c (‖z‖ ^ 2)) :
    conjWirtingerDeriv (fun w : ℂ ↦ w ^ n * (C (‖w‖ ^ 2) : ℂ)) z 1 = z ^ n * (c * z) := by
  have hp : DifferentiableAt ℂ (fun w : ℂ ↦ w ^ n) z := by fun_prop
  rw [conjWirtingerDeriv_fun_mul (hp.restrictScalars ℝ)
    (hasFDerivAt_ofReal_comp_norm_sq h).differentiableAt]
  simp [conjWirtingerDeriv_ofReal_comp_norm_sq_apply_one h]

end TauCeti
