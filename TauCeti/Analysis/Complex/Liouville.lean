/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, OpenAI Codex
-/
module

public import Mathlib.Analysis.Complex.Liouville

/-!
# Liouville's theorem and affine rigidity

An entire function `f` with `f(s) = -g(1 / s) / s²` for `s ≠ 0`, where `g` is continuous at `0`,
vanishes identically (`Differentiable.eq_zero_of_eq_neg_inv_sq_smul`): it tends to `0` at
infinity, so it is zero by Liouville's theorem. This is the transformation law of the coefficient
of a one-form `f(t) dt = g(s) ds` under the change of coordinate `s = 1 / t`, and it shows that a
holomorphic one-form on the Riemann sphere vanishes.

An entire function that is little-o of `z ^ (n + 1)` is a polynomial of degree at most `n`
(`Differentiable.exists_eq_polynomial_eval_of_isLittleO_pow`). In particular, an entire function
that is little-o of `z²` is affine, with its value and derivative at zero as coefficients
(`Differentiable.eq_affine_of_isLittleO_sq`). This strict-growth form of Liouville's theorem
identifies the exponent in an order-one Hadamard factorization.

## References

* Daniel Huybrechts, *Complex Geometry: An Introduction*, Universitext, Springer, 2005,
  Section 2.6.
-/

public section

open Set Filter Topology

namespace Differentiable

/-- **Liouville's theorem for the transformation law of a one-form under `t ↦ 1 / t`.** If an entire
function `f` satisfies `f(s) = -g(1 / s) / s²` for `s ≠ 0`, with `g` continuous at `0`, then `f`
tends to `0` at infinity, so it vanishes. -/
theorem eq_zero_of_eq_neg_inv_sq_smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f g : ℂ → F} (hf : Differentiable ℂ f) (hg : ContinuousAt g 0)
    (h : ∀ s ≠ 0, f s = -(s ^ 2)⁻¹ • g s⁻¹) (t : ℂ) : f t = 0 := by
  have hinv : Tendsto (fun s : ℂ ↦ s⁻¹) (cocompact ℂ) (𝓝 0) := by
    rw [← Metric.cobounded_eq_cocompact]
    exact tendsto_inv₀_cobounded
  have hlim : Tendsto (fun s : ℂ ↦ -(s⁻¹ ^ 2) • g s⁻¹) (cocompact ℂ) (𝓝 0) := by
    simpa using (hinv.pow 2).neg.smul (hg.tendsto.comp hinv)
  refine hf.apply_eq_of_tendsto_cocompact t (hlim.congr' ?_)
  filter_upwards [(isCompact_singleton (x := (0 : ℂ))).compl_mem_cocompact] with s hs
  rw [h s (mem_compl_singleton_iff.1 hs), inv_pow]

end Differentiable

open Complex Bornology Asymptotics

/-- An entire function that is little-o of `z ^ (n + 1)` is a polynomial of degree at most `n`. -/
theorem Differentiable.exists_eq_polynomial_eval_of_isLittleO_pow {n : ℕ} {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h : f =o[cobounded ℂ] (· ^ (n + 1))) :
    ∃ p : Polynomial ℂ, p.natDegree ≤ n ∧ f = p.eval := by
  obtain ⟨p, hp, rfl⟩ := hf.exists_eq_polynomial_eval_of_isBigO_pow h.isBigO
  refine ⟨p, Nat.le_of_lt_succ (hp.lt_of_ne fun hpn ↦ ?_), rfl⟩
  -- A polynomial of exact degree `n + 1` is not little-o of `z ^ (n + 1)`.
  have hc : p.leadingCoeff ≠ 0 := by
    rw [Ne, Polynomial.leadingCoeff_eq_zero]
    rintro rfl
    simp at hpn
  have hlead : (· ^ (n + 1)) =O[cobounded ℂ] p.eval := by
    rw [← hpn]
    exact (isBigO_self_const_mul hc _ _).trans
      Polynomial.isEquivalent_cobounded_leading_monomial.symm.isBigO
  refine isLittleO_irrefl ?_ (hlead.trans_isLittleO h)
  exact (eventually_ne_cobounded (0 : ℂ)).frequently.mono fun z hz ↦ pow_ne_zero _ hz

/-- An entire function that is little-o of the square is affine, with its value and derivative
at zero as coefficients. -/
theorem Differentiable.eq_affine_of_isLittleO_sq {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h : f =o[cobounded ℂ] (fun z ↦ z ^ 2)) :
    ∀ z, f z = f 0 + _root_.deriv f 0 * z := by
  obtain ⟨p, hp, rfl⟩ := hf.exists_eq_polynomial_eval_of_isLittleO_pow (n := 1) h
  have hlin : p.eval = fun z ↦ p.coeff 0 + p.coeff 1 * z := by
    rw [Polynomial.eq_X_add_C_of_natDegree_le_one hp]
    funext z
    simp [add_comm]
  rw [hlin]
  intro z
  simp
