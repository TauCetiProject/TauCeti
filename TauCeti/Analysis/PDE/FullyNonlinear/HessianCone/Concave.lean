/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.MvPolynomial.Hyperbolic.Concave
public import TauCeti.Analysis.PDE.FullyNonlinear.HessianCone

/-!
# Concavity of `σ_k^{1/k}` on the Hessian cone `Γ_k`

The function `σ_k^{1/k}` is concave on the Hessian cone `Γ_k ⊆ ℝⁿ`
(`TauCeti.concaveOn_esymm_rpow`), and for `k ≥ 1` superadditive there
(`TauCeti.eval_esymm_rpow_add_le`). Both are Gårding's theorem
(`MvPolynomial.IsHyperbolic.concaveOn_rpow`) for the elementary symmetric polynomial `σ_k`,
hyperbolic of degree `k` in the direction `e = (1, …, 1)` with Gårding cone `Γ_k` for `k ≤ n`;
for `k > n` the cone is empty (`TauCeti.hessianCone_eq_empty`).

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

end TauCeti
