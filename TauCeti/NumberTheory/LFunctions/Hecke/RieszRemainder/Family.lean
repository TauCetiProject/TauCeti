/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Hecke.RieszRemainder.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# First Riesz remainders of weighted ray class families

The weighted sum of the real parts of the individual Riesz remainders is real even if the
support is not closed under inversion. For Mellin transforms it can also be written as a
complex sum over inverse pairs. Bounds on the individual summands transfer to the family.

The real-part normalization is that of Levent Alpöge's `Deduction.Gm`
(<https://github.com/leanprover-community/riemann-hypothesis>).
-/

public section

open Complex MeasureTheory Set TauCeti.LFunctions
open scoped ComplexConjugate

namespace Finsupp

variable {K : Type*} [Field K] [NumberField K]

/-- The real first Riesz remainder of finitely supported weights on primitive ray class
characters, obtained by weighting the real parts of the individual remainders. -/
noncomputable def familyRieszRemainder (w : PrimitiveRayClassCharacter K →₀ ℝ) : ℝ → ℝ :=
  linearCombination ℝ (fun ψ y ↦ (ψ.rieszRemainder y).re) w

/-- The family remainder as a sum over the support of its weights. -/
theorem familyRieszRemainder_apply (w : PrimitiveRayClassCharacter K →₀ ℝ) (y : ℝ) :
    w.familyRieszRemainder y = w.sum (fun ψ c ↦ c * (ψ.rieszRemainder y).re) := by
  simp [familyRieszRemainder, linearCombination_apply, Finsupp.sum, Finset.sum_apply]

/-- An empty family has zero remainder. -/
@[simp] theorem familyRieszRemainder_zero :
    (0 : PrimitiveRayClassCharacter K →₀ ℝ).familyRieszRemainder = 0 := by
  simp [familyRieszRemainder]

/-- A singleton's remainder is the real part of its member's remainder times the weight. -/
@[simp] theorem familyRieszRemainder_single (ψ : PrimitiveRayClassCharacter K) (c y : ℝ) :
    (single ψ c).familyRieszRemainder y = c * (ψ.rieszRemainder y).re := by
  simp [familyRieszRemainder_apply, sum_single_index]

/-- Adding weights adds the Riesz remainders. -/
@[simp] theorem familyRieszRemainder_add (w v : PrimitiveRayClassCharacter K →₀ ℝ) :
    (w + v).familyRieszRemainder = w.familyRieszRemainder + v.familyRieszRemainder := by
  simp [familyRieszRemainder]

/-- Scaling weights scales the Riesz remainder. -/
@[simp] theorem familyRieszRemainder_smul (w : PrimitiveRayClassCharacter K →₀ ℝ) (c : ℝ) :
    (c • w).familyRieszRemainder = c • w.familyRieszRemainder := by
  simp [familyRieszRemainder]

/-- Relabeling the weights by character inversion leaves the real remainder unchanged. -/
@[simp] theorem familyRieszRemainder_mapDomain_inv (w : PrimitiveRayClassCharacter K →₀ ℝ) :
    (w.mapDomain Inv.inv).familyRieszRemainder = w.familyRieszRemainder := by
  funext y
  simp only [familyRieszRemainder_apply]
  rw [sum_mapDomain_index_inj inv_injective]
  simp only [PrimitiveRayClassCharacter.rieszRemainder_inv, conj_re]

/-- The real remainder, regarded as complex-valued, is the weighted sum of the averages of
inverse pairs. This formula does not require inverse characters to belong to the support. -/
theorem ofReal_familyRieszRemainder (w : PrimitiveRayClassCharacter K →₀ ℝ) (y : ℝ) :
    (w.familyRieszRemainder y : ℂ) =
      w.sum (fun ψ c ↦ (c : ℂ) * ((ψ.rieszRemainder y + ψ⁻¹.rieszRemainder y) / 2)) := by
  simp only [familyRieszRemainder_apply, Finsupp.sum, ofReal_sum, ofReal_mul,
    PrimitiveRayClassCharacter.rieszRemainder_inv, re_eq_add_conj]

/-- For inversion-invariant weights the complex sum is already real. -/
theorem ofReal_familyRieszRemainder_of_mapDomain_inv_eq (w : PrimitiveRayClassCharacter K →₀ ℝ)
    (hw : w.mapDomain Inv.inv = w) (y : ℝ) :
    (w.familyRieszRemainder y : ℂ) = w.sum (fun ψ c ↦ (c : ℂ) * ψ.rieszRemainder y) := by
  have hinv : w.sum (fun ψ c ↦ (c : ℂ) * ψ⁻¹.rieszRemainder y) =
      w.sum (fun ψ c ↦ (c : ℂ) * ψ.rieszRemainder y) := by
    conv_rhs => rw [← hw, sum_mapDomain_index_inj inv_injective]
  rw [ofReal_familyRieszRemainder]
  simp only [Finsupp.sum] at hinv ⊢
  simp_rw [← mul_div_assoc, mul_add, ← Finset.sum_div, Finset.sum_add_distrib]
  rw [hinv, ← two_mul, mul_div_cancel_left₀ _ two_ne_zero]

/-- The weighted real remainder is continuous. -/
@[fun_prop] theorem continuous_familyRieszRemainder (w : PrimitiveRayClassCharacter K →₀ ℝ) :
    Continuous w.familyRieszRemainder := by
  simp only [funext (familyRieszRemainder_apply w), Finsupp.sum]
  fun_prop

/-- Termwise power bounds for the members give a power bound for the weighted family. The
weights may have either sign, and no bound is needed outside their support. -/
theorem exists_norm_familyRieszRemainder_le_rpow_of_forall_mem_support
    (w : PrimitiveRayClassCharacter K →₀ ℝ) {a σ : ℝ}
    (h : ∀ ψ ∈ w.support, ∃ C : ℝ, ∀ y ≥ a, ‖ψ.rieszRemainder y‖ ≤ C * y ^ σ) :
    ∃ C : ℝ, ∀ y ≥ a, ‖w.familyRieszRemainder y‖ ≤ C * y ^ σ := by
  classical
  choose C hC using h
  let D (ψ : PrimitiveRayClassCharacter K) := if hψ : ψ ∈ w.support then C ψ hψ else 0
  refine ⟨∑ ψ ∈ w.support, ‖w ψ‖ * D ψ, fun y hy ↦ ?_⟩
  rw [familyRieszRemainder_apply, Finsupp.sum, Finset.sum_mul]
  refine norm_sum_le_of_le _ fun ψ hψ ↦ ?_
  rw [norm_mul, mul_assoc]
  have hD : D ψ = C ψ hψ := dite_eq_left hψ
  exact mul_le_mul_of_nonneg_left ((abs_re_le_norm _).trans (hD ▸ hC ψ hψ y hy)) (norm_nonneg _)

/-- On `y ≥ 1`, the family remainder is bounded by a constant times `y ^ σ` for any `σ > 1`. -/
theorem exists_norm_familyRieszRemainder_le_rpow (w : PrimitiveRayClassCharacter K →₀ ℝ)
    {σ : ℝ} (hσ : 1 < σ) : ∃ C : ℝ, ∀ y ≥ 1, ‖w.familyRieszRemainder y‖ ≤ C * y ^ σ :=
  w.exists_norm_familyRieszRemainder_le_rpow_of_forall_mem_support
    fun ψ _ ↦ ψ.exists_norm_rieszRemainder_le_rpow hσ

/-- On `Re s > 1`, the family remainder has an absolutely convergent upper-ray Mellin integral. -/
theorem integrableOn_familyRieszRemainder_mul_cpow (w : PrimitiveRayClassCharacter K →₀ ℝ)
    {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun y : ℝ ↦ (w.familyRieszRemainder y : ℂ) * (y : ℂ) ^ (-s - 1)) (Ioi 1) := by
  simp only [IntegrableOn] at ⊢
  have hintegrable (ψ : PrimitiveRayClassCharacter K) :
      IntegrableOn (fun y : ℝ ↦ (w ψ : ℂ) *
        ((ψ.rieszRemainder y + ψ⁻¹.rieszRemainder y) / 2 * (y : ℂ) ^ (-s - 1))) (Ioi 1) := by
    have h := (ψ.integrableOn_rieszRemainder_mul_cpow hs).add
      (ψ⁻¹.integrableOn_rieszRemainder_mul_cpow hs)
    simpa only [IntegrableOn, Pi.add_apply, ← add_mul, div_eq_mul_inv,
      mul_right_comm _ (2 : ℂ)⁻¹] using
      (h.mul_const (2 : ℂ)⁻¹).const_mul (w ψ : ℂ)
  simpa only [ofReal_familyRieszRemainder, Finsupp.sum, Finset.sum_mul, mul_assoc] using
    integrable_finsetSum w.support fun ψ _ ↦ hintegrable ψ

end Finsupp
