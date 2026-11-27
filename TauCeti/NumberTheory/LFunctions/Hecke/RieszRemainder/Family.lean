/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Hecke.RieszRemainder
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# First Riesz remainders of finitely supported character families

The family remainder is the real-weighted sum of the real parts of the individual remainders.
It is linear in the weights and invariant under relabeling by inverse characters. Taking real
parts is equivalent to averaging each remainder with the remainder of its inverse character;
this is the pairing that enters the Mellin transform. The family remainder is continuous and
its upper-tail Mellin integral is absolutely convergent on `Re s > 1`.

The rational normalization is Levent Alpöge's `Deduction.Gm` in
`Development/AutomorphicArithmetic/DedekindLFunctions/CharFamily.lean`
(<https://github.com/leanprover-community/riemann-hypothesis>).
-/

public section

open Complex MeasureTheory Set
open scoped NumberField

namespace TauCeti.LFunctions

variable {K : Type*} [Field K] [NumberField K]

/-- The first Riesz remainder of a family of primitive ray class characters, as a linear map
from finitely supported real weights to real functions. The weights may have either sign. -/
noncomputable def finsuppRieszRemainder : (PrimitiveRayClassCharacter K →₀ ℝ) →ₗ[ℝ] (ℝ → ℝ) :=
  Finsupp.linearCombination ℝ fun ψ y ↦ (ψ.rieszRemainder y).re

/-- The family remainder is the finite weighted sum of the real parts of the individual
remainders. -/
theorem finsuppRieszRemainder_apply (w : PrimitiveRayClassCharacter K →₀ ℝ) (y : ℝ) :
    finsuppRieszRemainder w y = w.sum (fun ψ c ↦ c * (ψ.rieszRemainder y).re) := by
  simp only [finsuppRieszRemainder, Finsupp.linearCombination_apply, Finsupp.sum,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- A family supported at a single character gives that character's real remainder, scaled
by its weight. -/
@[simp] theorem finsuppRieszRemainder_single (ψ : PrimitiveRayClassCharacter K) (c y : ℝ) :
    finsuppRieszRemainder (Finsupp.single ψ c) y = c * (ψ.rieszRemainder y).re := by
  simp [finsuppRieszRemainder_apply]

/-- Relabeling the weights by inversion leaves the real family remainder unchanged. -/
@[simp] theorem finsuppRieszRemainder_mapDomain_inv (w : PrimitiveRayClassCharacter K →₀ ℝ) :
    finsuppRieszRemainder (w.mapDomain Inv.inv) = finsuppRieszRemainder w := by
  simp [finsuppRieszRemainder, Function.comp_def]

/-- The complex value of the family remainder is obtained by averaging the two remainders
of each inverse pair. No symmetry of the weights is required. -/
theorem ofReal_finsuppRieszRemainder (w : PrimitiveRayClassCharacter K →₀ ℝ) (y : ℝ) :
    (finsuppRieszRemainder w y : ℂ) =
      w.sum (fun ψ c ↦ (c : ℂ) * ((ψ.rieszRemainder y + ψ⁻¹.rieszRemainder y) / 2)) := by
  simp only [finsuppRieszRemainder_apply, Finsupp.sum, ofReal_sum, ofReal_mul,
    PrimitiveRayClassCharacter.rieszRemainder_inv, re_eq_add_conj]

/-- For inverse-invariant weights, the complex weighted sum already has real values. -/
theorem ofReal_finsuppRieszRemainder_of_mapDomain_inv_eq (w : PrimitiveRayClassCharacter K →₀ ℝ)
    (hw : w.mapDomain Inv.inv = w) (y : ℝ) :
    (finsuppRieszRemainder w y : ℂ) = w.sum (fun ψ c ↦ (c : ℂ) * ψ.rieszRemainder y) := by
  let v (ψ : PrimitiveRayClassCharacter K) := ψ.rieszRemainder y
  have h : Finsupp.linearCombination ℝ v (w.mapDomain Inv.inv) =
      Finsupp.linearCombination ℝ v w := congrArg (Finsupp.linearCombination ℝ v) hw
  rw [Finsupp.linearCombination_mapDomain] at h
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, Function.comp_apply, real_smul, v] at h
  rw [ofReal_finsuppRieszRemainder]
  simp only [Finsupp.sum, ← mul_div_assoc, ← Finset.sum_div, mul_add, Finset.sum_add_distrib, h]
  ring

/-- The family remainder is continuous, including at the cutoffs in its prime sums. -/
@[fun_prop] theorem continuous_finsuppRieszRemainder (w : PrimitiveRayClassCharacter K →₀ ℝ) :
    Continuous (finsuppRieszRemainder w) := by
  simp only [funext (finsuppRieszRemainder_apply w), Finsupp.sum]
  exact continuous_finsetSum _ fun ψ _ ↦
    (continuous_re.comp ψ.continuous_rieszRemainder).const_mul _

/-- The family remainder has growth at most `y ^ σ` for each `σ > 1` on `[1, ∞)`. -/
theorem exists_norm_finsuppRieszRemainder_le_rpow (w : PrimitiveRayClassCharacter K →₀ ℝ)
    {σ : ℝ} (hσ : 1 < σ) : ∃ C : ℝ, ∀ y ≥ 1, ‖finsuppRieszRemainder w y‖ ≤ C * y ^ σ := by
  choose C hC using fun ψ : PrimitiveRayClassCharacter K ↦ ψ.exists_norm_rieszRemainder_le_rpow hσ
  refine ⟨∑ ψ ∈ w.support, ‖w ψ‖ * C ψ, fun y hy ↦ ?_⟩
  rw [finsuppRieszRemainder_apply, Finsupp.sum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ψ _ ↦ ?_)
  rw [norm_mul, mul_assoc, Real.norm_eq_abs (ψ.rieszRemainder y).re]
  exact mul_le_mul_of_nonneg_left ((abs_re_le_norm _).trans (hC ψ y hy)) (norm_nonneg _)

/-- The upper-tail Mellin integrand for the family remainder is absolutely integrable for
`Re s > 1`. -/
theorem integrableOn_finsuppRieszRemainder_mul_cpow (w : PrimitiveRayClassCharacter K →₀ ℝ)
    {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun y : ℝ ↦ (finsuppRieszRemainder w y : ℂ) * (y : ℂ) ^ (-s - 1)) (Ioi 1) := by
  simp only [ofReal_finsuppRieszRemainder, Finsupp.sum, Finset.sum_mul]
  refine integrable_finsetSum _ fun ψ _ ↦ ?_
  have h := ((ψ.integrableOn_rieszRemainder_mul_cpow hs).add
    (ψ⁻¹.integrableOn_rieszRemainder_mul_cpow hs)).const_mul ((w ψ : ℂ) / 2)
  convert h using 1
  funext y
  simp only [Pi.add_apply]
  ring

end TauCeti.LFunctions
