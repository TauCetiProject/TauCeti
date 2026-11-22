/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Density.Basic
public import TauCeti.MeasureTheory.Integral.Bochner.OfBasis

/-!
# Basis independence of density integrals

Under a basis change from `b` to `b'`, `b.addHaar` scales by `|b.det b'|⁻¹` while `μ x b` scales by
`|b.det b'|`, cancelling without any orientation sign (including in dimension zero).
-/

public section

noncomputable section

open MeasureTheory

namespace Module.Basis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  {m : ℕ}

/-- Set integrability of `x ↦ μ x b` against `b.addHaar` is independent of `b` (any `s`). -/
theorem integrableOn_density_apply_iff (b b' : Basis (Fin m) ℝ E)
    (μ : E → TauCeti.Density E m) (s : Set E) :
    IntegrableOn (fun x ↦ μ x b') s b'.addHaar ↔ IntegrableOn (fun x ↦ μ x b) s b.addHaar :=
  b.integrableOn_addHaar_iff_of_eq_smul b' (abs_ne_zero.mpr (b.isUnit_det b').ne_zero)
    (fun x ↦ (μ x).apply_eq_abs_det_mul b b') s

/-- Integrability of `x ↦ μ x b` against `b.addHaar` is independent of `b` (all dims). -/
theorem integrable_density_apply_iff (b b' : Basis (Fin m) ℝ E) (μ : E → TauCeti.Density E m) :
    Integrable (fun x ↦ μ x b') b'.addHaar ↔ Integrable (fun x ↦ μ x b) b.addHaar := by
  simpa only [← integrableOn_univ] using integrableOn_density_apply_iff b b' μ Set.univ

/-- The normalized Haar set integral `∫ x in s, μ x b ∂b.addHaar` is independent of `b`. -/
theorem setIntegral_density_apply_eq (b b' : Basis (Fin m) ℝ E)
    (μ : E → TauCeti.Density E m) (s : Set E) :
    (∫ x in s, μ x b ∂b.addHaar) = ∫ x in s, μ x b' ∂b'.addHaar := by
  have h := b.setIntegral_addHaar_eq_of_eq_smul b' |b.det b'|
    (fun x ↦ (μ x).apply_eq_abs_det_mul b b') s
  rw [div_self (abs_ne_zero.mpr (b.isUnit_det b').ne_zero), one_smul] at h
  exact h.symm

/-- The normalized Haar integral `∫ x, μ x b ∂b.addHaar` is independent of `b` (all dims). -/
theorem integral_density_apply_eq (b b' : Basis (Fin m) ℝ E) (μ : E → TauCeti.Density E m) :
    (∫ x, μ x b ∂b.addHaar) = ∫ x, μ x b' ∂b'.addHaar := by
  simpa only [Measure.restrict_univ] using setIntegral_density_apply_eq b b' μ Set.univ

end Module.Basis
