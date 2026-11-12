/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Group.Rounding
public import TauCeti.NumberTheory.Padics.Complex.Basic

/-!
# Rounding the norm on `ℂ_p` does not preserve the scalar inequality

Rounding a module norm to powers of a fixed constant preserves a contractive scalar action
when the scalar norms already lie in that discrete set. The nondiscrete value group of `ℂ_p`
prevents dropping this hypothesis. A square root `z` of `p` has norm strictly between `p⁻¹`
and `1`, so its rounded norm is `1`. Multiplying the module vector `1` by `z` therefore
violates the scalar inequality for the rounded norm and the original scalar norm.

The rounded additive norm still gives the same complete ultrametric topology; the failure
concerns only contractivity for the unchanged scalar norm.
-/

public section

namespace PadicComplex

open TauCeti

variable {p : ℕ} [hp : Fact p.Prime]

/-- For every prime there is a scalar whose rounded norm is strictly larger than its norm:
a square root of the prime itself is such a scalar. -/
theorem exists_sq_eq_prime_norm_lt_zpowCeil :
    ∃ z : ℂ_[p], z ^ 2 = p ∧ ‖z‖ < zpowCeil (p : ℝ)⁻¹ ‖z‖ := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (p : ℂ_[p]) (n := 2) (by omega)
  have hp₀ : 0 < (p : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hp.out.pos)
  have hp₁ : (p : ℝ)⁻¹ < 1 := by simpa only [norm_p] using norm_p_lt_one p
  have hz₂ : ‖z‖ ^ 2 = (p : ℝ)⁻¹ := by rw [← norm_pow, hz, norm_p]
  have hz₀ : 0 < ‖z‖ := by nlinarith [norm_nonneg z]
  have hz₁ : ‖z‖ < 1 := by nlinarith [norm_nonneg z]
  have hzlo : (p : ℝ)⁻¹ < ‖z‖ := by nlinarith
  have hround : zpowCeil (p : ℝ)⁻¹ ‖z‖ = 1 := by
    simpa using (zpowCeil_eq_zpow_iff hp₀ hp₁ 0).2 ⟨by simpa using hzlo, hz₁.le⟩
  exact ⟨z, hz, by rwa [hround]⟩

/-- The rounded additive norm on `ℂ_p` fails the module norm inequality for its original
scalar norm. This holds for every prime, including two. -/
theorem not_forall_zpowCeil_norm_mul_le :
    ¬ ∀ a x : ℂ_[p], zpowCeil (p : ℝ)⁻¹ ‖a * x‖ ≤
      ‖a‖ * zpowCeil (p : ℝ)⁻¹ ‖x‖ := by
  intro h
  have hp₀ : 0 < (p : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hp.out.pos)
  have hp₁ : (p : ℝ)⁻¹ < 1 := by simpa only [norm_p] using norm_p_lt_one p
  have hfixed := (zpowCeil_norm_mul_le_iff hp₀ hp₁).1 h
  obtain ⟨z, -, hz⟩ := exists_sq_eq_prime_norm_lt_zpowCeil (p := p)
  exact hz.ne (hfixed z).symm

end PadicComplex
