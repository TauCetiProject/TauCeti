/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Hecke.RieszRemainder
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# First Riesz remainders of weighted families

Take the real parts of the first Riesz remainders of primitive ray class characters and form
finitely supported real linear combinations. Inversion leaves the family remainder unchanged;
for symmetric weights one can instead sum the complex remainders without taking real parts.
The growth and integrability estimates allow Mellin transforms of these weighted remainders.

The real-part normalization over `ℚ` is that of Levent Alpöge's `Deduction.Gm`
(<https://github.com/leanprover-community/riemann-hypothesis>).
-/

public section

open Complex MeasureTheory Set
open scoped NumberField

namespace TauCeti.LFunctions

/-- The first Riesz remainder of a family is the weighted sum of the real parts of its members'
first Riesz remainders. The weights may be signed. -/
noncomputable def familyRieszRemainder (K : Type*) [Field K] [NumberField K] :
    (PrimitiveRayClassCharacter K →₀ ℝ) →ₗ[ℝ] (ℝ → ℝ) :=
  Finsupp.linearCombination ℝ fun ψ y ↦ (ψ.rieszRemainder y).re

variable (K : Type*) [Field K] [NumberField K]

/-- The pointwise weighted-sum formula for a family remainder. -/
theorem familyRieszRemainder_apply (w : PrimitiveRayClassCharacter K →₀ ℝ) (y : ℝ) :
    familyRieszRemainder K w y = w.sum fun ψ c ↦ c * (ψ.rieszRemainder y).re := by
  simp only [familyRieszRemainder, Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]

/-- A family supported on one character contributes just its weighted real remainder. -/
@[simp] theorem familyRieszRemainder_single (ψ : PrimitiveRayClassCharacter K) (c y : ℝ) :
    familyRieszRemainder K (Finsupp.single ψ c) y = c * (ψ.rieszRemainder y).re := by
  simp [familyRieszRemainder, Finsupp.linearCombination_single]

/-- Replacing all characters by their inverses leaves the family remainder unchanged. -/
@[simp] theorem familyRieszRemainder_mapDomain_inv (w : PrimitiveRayClassCharacter K →₀ ℝ) :
    familyRieszRemainder K (w.mapDomain Inv.inv) = familyRieszRemainder K w := by
  ext y
  simp [familyRieszRemainder_apply, Finsupp.sum_mapDomain_index, add_mul]

/-- In complex coordinates, the family remainder is the weighted sum of the averages of the
remainders at each character and its inverse. -/
theorem ofReal_familyRieszRemainder (w : PrimitiveRayClassCharacter K →₀ ℝ) (y : ℝ) :
    (familyRieszRemainder K w y : ℂ) =
      w.sum fun ψ c ↦ (c : ℂ) * ((ψ.rieszRemainder y + ψ⁻¹.rieszRemainder y) / 2) := by
  simp only [familyRieszRemainder_apply, Finsupp.sum, ofReal_sum, ofReal_mul,
    PrimitiveRayClassCharacter.rieszRemainder_inv]
  exact Finset.sum_congr rfl fun ψ _ ↦ congrArg ((w ψ : ℂ) * ·) (re_eq_add_conj _)

/-- For inverse-symmetric weights the weighted sum of the complex remainders is already real. -/
theorem ofReal_familyRieszRemainder_of_mapDomain_inv_eq (w : PrimitiveRayClassCharacter K →₀ ℝ)
    (hw : w.mapDomain Inv.inv = w) (y : ℝ) :
    (familyRieszRemainder K w y : ℂ) = w.sum fun ψ c ↦ (c : ℂ) * ψ.rieszRemainder y := by
  have hreindex : (w.sum fun ψ c ↦ (c : ℂ) * ψ⁻¹.rieszRemainder y) =
      w.sum fun ψ c ↦ (c : ℂ) * ψ.rieszRemainder y := by
    conv_rhs => rw [← hw]
    rw [Finsupp.sum_mapDomain_index] <;> simp [add_mul]
  rw [ofReal_familyRieszRemainder K]
  simp only [Finsupp.sum] at hreindex ⊢
  simp only [← mul_div_assoc, ← Finset.sum_div, mul_add, Finset.sum_add_distrib, hreindex]
  ring

/-- The family remainder is continuous in the cutoff. -/
@[fun_prop] theorem continuous_familyRieszRemainder (w : PrimitiveRayClassCharacter K →₀ ℝ) :
    Continuous (familyRieszRemainder K w) := by
  simp only [funext (familyRieszRemainder_apply K w), Finsupp.sum]
  exact continuous_finsetSum _ fun ψ _ ↦
    (continuous_re.comp ψ.continuous_rieszRemainder).const_mul _

/-- A power bound on each member of the support implies a power bound on the whole family,
with the same exponent and cutoff. -/
theorem exists_abs_familyRieszRemainder_le_rpow_of_forall (w : PrimitiveRayClassCharacter K →₀ ℝ)
    {a σ : ℝ} (h : ∀ ψ ∈ w.support, ∃ C : ℝ, ∀ y ≥ a, ‖ψ.rieszRemainder y‖ ≤ C * y ^ σ) :
    ∃ C : ℝ, ∀ y ≥ a, |familyRieszRemainder K w y| ≤ C * y ^ σ := by
  classical
  choose C hC using (fun ψ : w.support ↦ h ψ ψ.property)
  refine ⟨∑ ψ ∈ w.support.attach, |w ψ| * C ψ, fun y hy ↦ ?_⟩
  rw [familyRieszRemainder_apply, Finsupp.sum, ← Finset.sum_attach w.support]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  gcongr with ψ _
  rw [abs_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left ((abs_re_le_norm _).trans (hC ψ y hy)) (abs_nonneg _)

/-- On `y ≥ 1` the family remainder grows at most quadratically. -/
theorem exists_abs_familyRieszRemainder_le_sq (w : PrimitiveRayClassCharacter K →₀ ℝ) :
    ∃ C : ℝ, ∀ y ≥ 1, |familyRieszRemainder K w y| ≤ C * y ^ 2 := by
  obtain ⟨C, hC⟩ := exists_abs_familyRieszRemainder_le_rpow_of_forall K (a := 1) (σ := 2) w
    (fun ψ _ ↦ ψ.exists_norm_rieszRemainder_le_rpow (by norm_num))
  exact ⟨C, fun y hy ↦ by simpa only [Real.rpow_two] using hC y hy⟩

/-- The family remainder has an absolutely integrable Mellin integrand above `1` on
`Re s > 1`. -/
theorem integrableOn_familyRieszRemainder_mul_cpow (w : PrimitiveRayClassCharacter K →₀ ℝ)
    {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun y : ℝ ↦ (familyRieszRemainder K w y : ℂ) * (y : ℂ) ^ (-s - 1))
      (Ioi 1) := by
  simp only [ofReal_familyRieszRemainder, Finsupp.sum, Finset.sum_mul]
  refine integrable_finsetSum _ fun ψ _ ↦ ?_
  have h := ((ψ.integrableOn_rieszRemainder_mul_cpow hs).add
    (ψ⁻¹.integrableOn_rieszRemainder_mul_cpow hs)).const_mul ((w ψ : ℂ) / 2)
  convert h using 1
  ext y
  simp only [Pi.add_apply]
  ring

end TauCeti.LFunctions
