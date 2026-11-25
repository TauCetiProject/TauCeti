/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.LineDeriv
public import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The factorial-normalized Dirac derivative series diverges

The formal series `∑ δ⁽ⁿ⁾/n!` does not converge as a series of distributions, even on an
arbitrarily small open neighbourhood of zero. A compact smooth test equal near zero to
`1 / (1 + 2*x)` evaluates its nth term to `2^n`. Its support can be kept inside
`(-1/4, 1/4)`. Thus even pointwise convergence of the partial sums fails; in particular
they do not converge in the native compact-convergence distribution topology.

This distinguishes formal infinite sums of point-supported derivatives from actual
distributions. Only finite sums are automatically distributions.

## References

* L. Schwartz, *Théorie des distributions*, Chapter III, §3 (convergence of distributions).
-/

public noncomputable section

open Filter LineDeriv Set TopologicalSpace
open scoped ContDiff Distributions Topology

namespace TauCeti

/-- There is a compact smooth test, supported in `(-1/4, 1/4)`, whose germ at zero is
`1 / (1 + 2*x)`. It can be chosen on any open neighbourhood of zero. -/
private theorem exists_testFunction_eventuallyEq_inv_one_add_two_mul {Ω : Opens ℝ} (hΩ : 0 ∈ Ω) :
    ∃ φ : 𝓓(Ω, ℝ), tsupport φ ⊆ Ioo (-(1 / 4)) (1 / 4) ∧
      (φ : ℝ → ℝ) =ᶠ[𝓝 0] fun x => (1 + 2 * x)⁻¹ := by
  let U : Opens ℝ := Ω ⊓ ⟨Ioo (-(1 / 4)) (1 / 4), isOpen_Ioo⟩
  have hUΩ : U ≤ Ω := inf_le_left
  have hU : (0 : ℝ) ∈ U := ⟨hΩ, by norm_num⟩
  obtain ⟨χ, hχ, -⟩ := TestFunction.exists_eventually_eq_one
    (n := ⊤) (isCompact_singleton (x := (0 : ℝ))) (singleton_subset_iff.mpr hU)
  have hg : ContDiffOn ℝ ∞ (fun x : ℝ => (1 + 2 * x)⁻¹) U := by
    apply (contDiffOn_const.add (contDiffOn_const.mul contDiffOn_id)).inv
    intro x hx
    have hx' : -(1 / 4 : ℝ) < x := hx.2.1
    simp only [id_eq]
    linarith
  obtain ⟨ψ, hψ⟩ := TestFunction.exists_coe_eq_smul_of_contDiffOn hg χ
  let φ : 𝓓(Ω, ℝ) := TestFunction.monoCLM ℝ ψ
  have hφ : (φ : ℝ → ℝ) = ψ := by
    simp [φ, TestFunction.monoCLM_apply, hUΩ]
  refine ⟨φ, ?_, ?_⟩
  · rw [hφ]
    exact ψ.tsupport_subset.trans (fun _ hx => hx.2)
  · have hχ0 : ∀ᶠ x in 𝓝 (0 : ℝ), χ x = 1 := by simpa using hχ
    filter_upwards [hχ0] with x hx
    simp [hφ, hψ, hx]

/-- A single small-support test evaluates every factorial-normalized Dirac derivative to
`2^n`. This is an obstruction to convergence that does not depend on the size of the domain. -/
theorem exists_testFunction_normalized_delta_derivative_eq_two_pow {Ω : Opens ℝ}
    (hΩ : 0 ∈ Ω) :
    ∃ φ : 𝓓(Ω, ℝ), tsupport φ ⊆ Ioo (-(1 / 4)) (1 / 4) ∧ ∀ n : ℕ,
      ((n.factorial : ℝ)⁻¹ •
        (lineDerivOp (1 : ℝ))^[n] (Distribution.delta 0 : 𝓓'(Ω, ℝ))) φ = 2 ^ n := by
  obtain ⟨φ, hsupp, hφ⟩ := exists_testFunction_eventuallyEq_inv_one_add_two_mul hΩ
  refine ⟨φ, hsupp, fun n => ?_⟩
  have hd : (deriv^[n] (φ : ℝ → ℝ)) 0 = (-1 : ℝ) ^ n * n.factorial * 2 ^ n := by
    rw [← iteratedDeriv_eq_iterate]
    rw [hφ.iteratedDeriv_eq]
    have heq : (fun x : ℝ => (1 + 2 * x)⁻¹) = fun x => (2 * x + 1)⁻¹ := by
      ext x
      rw [add_comm]
    rw [heq, iteratedDeriv_eq_iterate, iter_deriv_inv_linear]
    simp
  rw [smul_apply, Distribution.iterate_lineDerivOp_apply_apply,
    Distribution.delta_apply, TestFunction.coe_iterate_lineDerivOp_one, hd]
  have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  simp only [smul_eq_mul]
  have hsign : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by
    rw [← mul_pow]
    simp
  calc
    _ = (n.factorial : ℝ)⁻¹ * (n.factorial * 2 ^ n) := by
      linear_combination (n.factorial : ℝ)⁻¹ * n.factorial * 2 ^ n * hsign
    _ = 2 ^ n := by field_simp

/-- The partial sums of `∑ δ⁽ⁿ⁾/n!` do not converge to any distribution on any open
neighbourhood of zero, with the native compact-convergence topology. -/
theorem not_tendsto_sum_normalized_delta_derivative {Ω : Opens ℝ} (hΩ : 0 ∈ Ω)
    (T : 𝓓'(Ω, ℝ)) :
    ¬ Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N,
      (n.factorial : ℝ)⁻¹ •
        (lineDerivOp (1 : ℝ))^[n] (Distribution.delta 0 : 𝓓'(Ω, ℝ))) atTop (𝓝 T) := by
  obtain ⟨φ, -, hφ⟩ := exists_testFunction_normalized_delta_derivative_eq_two_pow hΩ
  intro h
  have htest := (continuous_eval_const φ).tendsto T |>.comp h
  have heval (N : ℕ) :
      (∑ n ∈ Finset.range N, (n.factorial : ℝ)⁻¹ •
        (lineDerivOp (1 : ℝ))^[n] (Distribution.delta 0 : 𝓓'(Ω, ℝ))) φ =
        (2 : ℝ) ^ N - 1 := by
    simp only [sum_apply, hφ]
    convert geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1) N using 1; norm_num
  have hscalar : Tendsto (fun N : ℕ => (2 : ℝ) ^ N - 1) atTop (𝓝 (T φ)) :=
    htest.congr' (Eventually.of_forall heval)
  have hpow : Tendsto (fun N : ℕ => (2 : ℝ) ^ N) atTop (𝓝 (T φ + 1)) := by
    simpa using hscalar.add_const 1
  exact not_tendsto_nhds_of_tendsto_atTop
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)) _ hpow

end TauCeti
