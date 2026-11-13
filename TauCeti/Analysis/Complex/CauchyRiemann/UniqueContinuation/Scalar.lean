/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.UniqueContinuation
public import TauCeti.Analysis.Complex.Wirtinger.Similarity.Basic
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# The scalar similarity principle as a similarity factorization

The scalar similarity principle (`TauCeti.Analysis.Complex.Wirtinger.Similarity.Basic`) makes a
real-differentiable solution `f : ℂ → ℂ` of `bar∂ f = a f`, with `a` of class `Cᵏ` for some `k ≥ 1`,
holomorphic near each point `z` after multiplication by `exp (-g)` for a `Cᵏ` integrating factor
`g`. This file compares it with the vector similarity principle in the case `n = 1`: the identity
`f = exp g • (exp (-g) * f)` is a local similarity factorization in the sense of
`TauCeti.HasSimilarityFactorizationAt`, with `Φ = exp g • id` continuous and invertible and
`σ = exp (-g) * f` holomorphic. No zero of `f` at `z` is needed.

The consequences of a factorization from `TauCeti.Analysis.Complex.CauchyRiemann.UniqueContinuation`
then apply to scalar solutions:

* on an open preconnected domain, a solution vanishing to infinite order at one point vanishes on
  the domain (`TauCeti.eqOn_zero_of_conjWirtingerDeriv_apply_one_eq_mul_of_forall_isBigO`);
* at each zero `z₀` of a solution not vanishing near `z₀`, the exponent `m` of the scalar power
  factorization `f w = (w - z₀) ^ m * v w`
  (`TauCeti.exists_contDiffAt_pow_mul_of_conjWirtingerDeriv_apply_one_eq_mul`) is positive
  (`TauCeti.pos_of_eventually_eq_pow_mul`), `‖f w‖` is comparable to `‖w - z₀‖ ^ m`
  (`TauCeti.isTheta_pow_of_eventually_eq_pow_mul`), and `m` is the analytic order of the
  holomorphic factor `σ` of every similarity factorization `f = Φ σ` at `z₀`
  (`TauCeti.analyticOrderAt_eq_of_eventually_eq_pow_mul`).

The comparison of exponents needs no hypothesis on the equation, so it lives with the other
consequences of a factorization in `TauCeti.Analysis.Complex.CauchyRiemann.UniqueContinuation`: a
power factorization `f w = (w - z₀) ^ m * v w` at a zero `z₀`, with `v` continuous and nonzero at
`z₀`, is itself a similarity factorization with `Φ = v • id` and `σ = (· - z₀) ^ m`, and the
analytic order of the holomorphic factor does not depend on the factorization
(`TauCeti.analyticOrderAt_eq_of_eventually_eq_clm_apply`).

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 2.3.
* I. N. Vekua, *Generalized Analytic Functions*, Chapter I.
-/

public noncomputable section

open Asymptotics Complex Filter Set Topology

namespace TauCeti

variable {k : ℕ∞} {U : Set ℂ} {a f : ℂ → ℂ} {z₀ : ℂ}

/-- **The scalar similarity principle as a similarity factorization.** A real-differentiable
solution of `bar∂ f = a f` on an open `U`, with `a` of class `Cᵏ` on `U` for some `k ≥ 1`, factors
at every point `z ∈ U` as `f = Φ σ`, with `Φ = exp g • id` for the integrating factor `g` of
`TauCeti.exists_contDiff_analyticAt_exp_neg_mul_of_conjWirtingerDeriv_apply_one_eq_mul` and
`σ = exp (-g) * f` holomorphic at `z`. -/
theorem hasSimilarityFactorizationAt_of_conjWirtingerDeriv_apply_one_eq_mul (hk : 1 ≤ k)
    (hU : IsOpen U) (ha : ContDiffOn ℝ k a U) (hf : DifferentiableOn ℝ f U)
    (heq : ∀ w ∈ U, conjWirtingerDeriv f w 1 = a w * f w) {z : ℂ} (hz : z ∈ U) :
    HasSimilarityFactorizationAt f z := by
  obtain ⟨g, hg, hσ⟩ :=
    exists_contDiff_analyticAt_exp_neg_mul_of_conjWirtingerDeriv_apply_one_eq_mul hk hU ha hf
      heq hz
  refine hasSimilarityFactorizationAt_iff.2 ⟨fun w ↦ exp (g w) • ContinuousLinearMap.id ℝ ℂ, _,
    ((hg.continuous.cexp).smul continuous_const).continuousAt,
    ContinuousLinearMap.isUnit_smul_id_of_ne_zero (exp_ne_zero _), hσ,
    Eventually.of_forall fun w ↦ ?_⟩
  simp [← mul_assoc, ← exp_add]

/-- **Unique continuation from a zero of infinite order** for the scalar equation. On an open
preconnected `U`, a real-differentiable solution of `bar∂ f = a f`, with `a` of class `Cᵏ` on `U`
for some `k ≥ 1`, satisfying `f = O(‖w - z₀‖ⁿ)` near one point `z₀ ∈ U` for every `n` vanishes
on `U`. -/
theorem eqOn_zero_of_conjWirtingerDeriv_apply_one_eq_mul_of_forall_isBigO (hk : 1 ≤ k)
    (hU : IsOpen U) (hUc : IsPreconnected U) (ha : ContDiffOn ℝ k a U)
    (hf : DifferentiableOn ℝ f U) (heq : ∀ w ∈ U, conjWirtingerDeriv f w 1 = a w * f w)
    (hz₀ : z₀ ∈ U) (h₀ : ∀ n : ℕ, f =O[𝓝 z₀] fun w ↦ (w - z₀) ^ n) : EqOn f 0 U :=
  eqOn_zero_of_hasSimilarityFactorizationAt_of_forall_isBigO hU hUc hf.continuousOn
    (fun _ hz _ ↦ hasSimilarityFactorizationAt_of_conjWirtingerDeriv_apply_one_eq_mul hk hU ha
      hf heq hz) hz₀ h₀

end TauCeti
