/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.MvPolynomial.Hyperbolic.Concave
public import TauCeti.Analysis.PDE.FullyNonlinear.HessianCone
import TauCeti.RingTheory.MvPolynomial.Symmetric.PDeriv

/-!
# Concavity of `σ_k^{1/k}` on the Hessian cone `Γ_k`

The function `σ_k^{1/k}` is concave on the Hessian cone `Γ_k ⊆ ℝⁿ`
(`TauCeti.concaveOn_esymm_rpow`), and for `k ≥ 1` superadditive there
(`TauCeti.eval_esymm_rpow_add_le`). Both are Gårding's theorem
(`MvPolynomial.IsHyperbolic.concaveOn_rpow`) for the elementary symmetric polynomial `σ_k`,
hyperbolic of degree `k` in the direction `e = (1, …, 1)` with Gårding cone `Γ_k` for `k ≤ n`;
for `k > n` the cone is empty (`TauCeti.hessianCone_eq_empty`).

Gårding's inequality (`MvPolynomial.IsHyperbolic.mul_rpow_mul_rpow_le_eval_sum_smul_pderiv`) for
`σ_{k+1}` is the tangent inequality
(`TauCeti.mul_esymm_rpow_mul_esymm_rpow_le_sum_mul_eval_update_zero_esymm`): for `μ ∈ Γ_{k+1}` and
`ν` in the closure of `Γ_{k+1}`,

`(k + 1) σ_{k+1}(ν)^{1/(k+1)} σ_{k+1}(μ)^{k/(k+1)} ≤ ∑ᵢ νᵢ σ_{k;i}(μ)`,

where `σ_{k;i}(μ) = ∂σ_{k+1}/∂μᵢ (μ)` is `σ_k` of `μ` with its `i`-th entry set to zero
(`TauCeti.eval_pderiv_esymm_succ`).

## References

* J. Spruck, *Geometric aspects of the theory of fully nonlinear elliptic equations*, in
  *Global theory of minimal surfaces*, Clay Math. Proc. 2 (2005), §2.
-/

public section

open MvPolynomial

namespace TauCeti

variable {n k : ℕ}

/-- **`σ_k^{1/k}` is superadditive on `Γ_k`**, for `k ≥ 1`. -/
theorem eval_esymm_rpow_add_le (hk : 1 ≤ k) {μ ν : Fin n → ℝ} (hμ : μ ∈ hessianCone n k)
    (hν : ν ∈ hessianCone n k) :
    eval μ (esymm (Fin n) ℝ k) ^ (k : ℝ)⁻¹ + eval ν (esymm (Fin n) ℝ k) ^ (k : ℝ)⁻¹ ≤
      eval (μ + ν) (esymm (Fin n) ℝ k) ^ (k : ℝ)⁻¹ := by
  rcases le_or_gt k n with hkn | hkn
  · rw [← gardingCone_esymm_eq_hessianCone] at hμ hν
    exact (isHyperbolic_esymm (σ := Fin n) (by simpa using hkn)).eval_rpow_add_le hk hμ hν
  · simp [hessianCone_eq_empty hkn] at hμ

/-- **`σ_k^{1/k}` is concave on `Γ_k`.** For `k = 0` it is the constant `1` (the exponent is the
junk value `0`), and for `k > n` the cone is empty. -/
theorem concaveOn_esymm_rpow (n k : ℕ) :
    ConcaveOn ℝ (hessianCone n k) fun μ ↦ eval μ (esymm (Fin n) ℝ k) ^ (k : ℝ)⁻¹ := by
  rcases le_or_gt k n with hkn | hkn
  · rw [← gardingCone_esymm_eq_hessianCone]
    exact (isHyperbolic_esymm (σ := Fin n) (by simpa using hkn)).concaveOn_rpow
  · rw [hessianCone_eq_empty hkn]
    exact ⟨convex_empty, fun _ hx ↦ hx.elim⟩

/-- **The tangent inequality for `σ_{k+1}^{1/(k+1)}`.** For `μ` in the Hessian cone `Γ_{k+1}` and
`ν` in its closure, `(k + 1) σ_{k+1}(ν)^{1/(k+1)} σ_{k+1}(μ)^{1 - 1/(k+1)} ≤ ∑ᵢ νᵢ σ_{k;i}(μ)`,
where `σ_{k;i}(μ)` is `σ_k` of `μ` with its `i`-th entry set to zero. -/
theorem mul_esymm_rpow_mul_esymm_rpow_le_sum_mul_eval_update_zero_esymm (k : ℕ)
    {μ ν : Fin n → ℝ} (hμ : μ ∈ hessianCone n (k + 1)) (hν : ν ∈ closure (hessianCone n (k + 1))) :
    ((k + 1 : ℕ) : ℝ) * eval ν (esymm (Fin n) ℝ (k + 1)) ^ ((k + 1 : ℕ) : ℝ)⁻¹ *
        eval μ (esymm (Fin n) ℝ (k + 1)) ^ (1 - ((k + 1 : ℕ) : ℝ)⁻¹) ≤
      ∑ i, ν i * eval (Function.update μ i 0) (esymm (Fin n) ℝ k) := by
  rcases le_or_gt (k + 1) n with hkn | hkn
  · rw [← gardingCone_esymm_eq_hessianCone] at hμ hν
    have h := (isHyperbolic_esymm (σ := Fin n) (by simpa using hkn))
      |>.mul_rpow_mul_rpow_le_eval_sum_smul_pderiv hμ hν
    simpa only [map_sum, smul_eval, eval_pderiv_esymm_succ] using h
  · simp [hessianCone_eq_empty hkn] at hμ

end TauCeti
