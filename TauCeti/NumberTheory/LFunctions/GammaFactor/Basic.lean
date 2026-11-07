/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
module

public import TauCeti.NumberTheory.LFunctions.Data.Basic
public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Analytic reciprocals of archimedean factors

The total reciprocals of Mathlib's `Gammaℝ` and `Gammaℂ` are entire, with zero
values at their poles. A finite product of shifted factors therefore has a
canonical entire reciprocal. This module supplies that reciprocal for every
analytic L-function record, without assuming a functional equation or any
properties of its completed function.

The construction uses `Complex.differentiable_Gammaℝ_inv` and
`Complex.differentiable_Gammaℂ_inv` from Mathlib's gamma-factor theory.
The order comparison is Mathlib's `meromorphicOrderAt_inv`.

## References

* H. Iwaniec and E. Kowalski, *Analytic Number Theory* (2004), §5.1.
-/

public section

open Complex

namespace TauCeti.LFunctions.AnalyticLFunctionData

variable (d : AnalyticLFunctionData)

/-- The entire reciprocal of the archimedean gamma factor, including its pole values. -/
noncomputable def invGammaFactor (s : ℂ) : ℂ := (d.gammaFactor s)⁻¹

theorem invGammaFactor_def (s : ℂ) : d.invGammaFactor s = (d.gammaFactor s)⁻¹ := (rfl)

/-- The reciprocal is the product of the shifted reciprocal gamma factors. -/
theorem invGammaFactor_eq_prod (s : ℂ) :
    d.invGammaFactor s = (d.gammaR.map fun μ ↦ (Gammaℝ (s + μ))⁻¹).prod *
      (d.gammaC.map fun ν ↦ (Gammaℂ (s + ν))⁻¹).prod := by
  simp only [invGammaFactor_def, gammaFactor_def, mul_inv, Multiset.prod_map_inv]

/-- A degree-zero record has no gamma factors, so its analytic reciprocal is one. -/
theorem invGammaFactor_of_degree_eq_zero (hd : d.degree = 0) (s : ℂ) :
    d.invGammaFactor s = 1 := by
  have hR : d.gammaR = 0 := by
    apply Multiset.card_eq_zero.mp
    rw [degree_def] at hd
    omega
  have hC : d.gammaC = 0 := by
    apply Multiset.card_eq_zero.mp
    rw [degree_def] at hd
    omega
  simp [invGammaFactor_eq_prod, hR, hC]

private theorem differentiable_multiset_prod {ι : Type*} (m : Multiset ι)
    (f : ι → ℂ → ℂ) (hf : ∀ i ∈ m, Differentiable ℂ (f i)) :
    Differentiable ℂ (fun s ↦ (m.map fun i ↦ f i s).prod) := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons i m ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    apply Differentiable.mul
    · exact hf i (by simp)
    · exact ih (fun j hj ↦ hf j (by simp [hj]))

/-- The analytic reciprocal is entire, including at all shifted gamma poles. -/
@[fun_prop]
theorem differentiable_invGammaFactor : Differentiable ℂ d.invGammaFactor := by
  rw [funext (d.invGammaFactor_eq_prod)]
  apply Differentiable.mul
  · apply differentiable_multiset_prod
    intro μ _
    exact differentiable_Gammaℝ_inv.comp (differentiable_id.add_const μ)
  · apply differentiable_multiset_prod
    intro ν _
    exact differentiable_Gammaℂ_inv.comp (differentiable_id.add_const ν)

/-- The reciprocal is analytic at every point. -/
@[fun_prop]
theorem analyticAt_invGammaFactor (s : ℂ) : AnalyticAt ℂ d.invGammaFactor s :=
  d.differentiable_invGammaFactor.analyticAt s

@[simp]
theorem inv_invGammaFactor (s : ℂ) : (d.invGammaFactor s)⁻¹ = d.gammaFactor s := by
  rw [invGammaFactor_def, inv_inv]

/-- The archimedean factor is globally meromorphic. -/
@[fun_prop]
theorem meromorphic_gammaFactor : Meromorphic d.gammaFactor := by
  intro s
  have h := (d.analyticAt_invGammaFactor s).meromorphicAt.inv
  rw [show (d.invGammaFactor)⁻¹ = d.gammaFactor from funext (d.inv_invGammaFactor)] at h
  exact h

/-- The gamma factor is analytic wherever its total value is nonzero. -/
theorem analyticAt_gammaFactor {s : ℂ} (hs : d.gammaFactor s ≠ 0) :
    AnalyticAt ℂ d.gammaFactor s := by
  have h := (d.analyticAt_invGammaFactor s).inv (by simpa [invGammaFactor_def] using hs)
  rw [show (d.invGammaFactor)⁻¹ = d.gammaFactor from funext (d.inv_invGammaFactor)] at h
  exact h

@[simp]
theorem invGammaFactor_eq_zero_iff (s : ℂ) :
    d.invGammaFactor s = 0 ↔ d.gammaFactor s = 0 := by
  rw [invGammaFactor_def, inv_eq_zero]

/-- The total zero values of the gamma factor occur precisely on the shifted gamma
pole lattices. They are not zeros of its meromorphic germ. -/
theorem gammaFactor_eq_zero_iff (s : ℂ) :
    d.gammaFactor s = 0 ↔
      (∃ μ ∈ d.gammaR, ∃ n : ℕ, s + μ = -(2 * (n : ℂ))) ∨
      (∃ ν ∈ d.gammaC, ∃ n : ℕ, s + ν = -(n : ℂ)) := by
  have hC : ∀ z : ℂ, Gammaℂ z = 0 ↔ ∃ n : ℕ, z = -(n : ℂ) := by
    intro z
    simp [Gammaℂ_def, Real.pi_ne_zero, Gamma_eq_zero_iff]
  simp only [gammaFactor_def, mul_eq_zero, Multiset.prod_eq_zero_iff, Multiset.mem_map,
    Gammaℝ_eq_zero_iff, hC]

/-- The analytic reciprocal vanishes precisely on the shifted gamma pole lattices. -/
theorem invGammaFactor_eq_zero_iff_shift (s : ℂ) :
    d.invGammaFactor s = 0 ↔
      (∃ μ ∈ d.gammaR, ∃ n : ℕ, s + μ = -(2 * (n : ℂ))) ∨
      (∃ ν ∈ d.gammaC, ∃ n : ℕ, s + ν = -(n : ℂ)) := by
  rw [invGammaFactor_eq_zero_iff, gammaFactor_eq_zero_iff]

/-- Off the poles, the analytic reciprocal cancels the gamma factor pointwise. -/
theorem invGammaFactor_mul_gammaFactor {s : ℂ} (hs : d.gammaFactor s ≠ 0) :
    d.invGammaFactor s * d.gammaFactor s = 1 := by
  rw [invGammaFactor_def, inv_mul_cancel₀ hs]

/-- Taking the analytic reciprocal negates the meromorphic order. -/
theorem meromorphicOrderAt_invGammaFactor (s : ℂ) :
    meromorphicOrderAt d.invGammaFactor s = -meromorphicOrderAt d.gammaFactor s := by
  rw [show d.invGammaFactor = (d.gammaFactor)⁻¹ from funext (d.invGammaFactor_def)]
  exact meromorphicOrderAt_inv

/-- Duality commutes with the analytic reciprocal. -/
theorem invGammaFactor_dual (s : ℂ) :
    d.dual.invGammaFactor s = star (d.invGammaFactor (star s)) := by
  simp only [invGammaFactor_def, gammaFactor_dual, Complex.star_def, map_inv₀]

end TauCeti.LFunctions.AnalyticLFunctionData
