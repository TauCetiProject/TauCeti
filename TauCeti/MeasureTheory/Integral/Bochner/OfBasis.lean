/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Basis-change rules for Haar Bochner integrals

Under a basis change `b ↦ b'`, `b.addHaar` rescales by `|b.det b'|⁻¹`. When a function rescales
by a nonzero constant `c` (`∀ x, g x = c • f x`), set integrability is preserved and the set
integral against `b'.addHaar` scales by `c / |b.det b'|`.
-/

public section

noncomputable section

open MeasureTheory

namespace Module.Basis

variable {E G ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Set integrability against a basis Haar measure is preserved when changing basis and rescaling
by a nonzero scalar. -/
theorem integrableOn_addHaar_iff_of_eq_smul (b b' : Basis ι ℝ E) {c : ℝ} (hc : c ≠ 0)
    {f g : E → G} (hfg : ∀ x, g x = c • f x) (s : Set E) :
    IntegrableOn g s b'.addHaar ↔ IntegrableOn f s b.addHaar := by
  classical
  have hd : b.det b' ≠ 0 := (b.isUnit_det b').ne_zero
  simp only [IntegrableOn, addHaar_eq_smul_of_basis b b', Measure.restrict_smul]
  rw [integrable_smul_measure
    (ENNReal.ofReal_ne_zero_iff.mpr (abs_pos.mpr (inv_ne_zero hd))) ENNReal.ofReal_ne_top]
  simp_rw [show g = fun x ↦ c • f x from funext hfg]
  exact integrable_smul_iff (f := f) hc

/-- Changing basis from `b` to `b'` while rescaling the integrand by `c` scales the Haar set
integral by `c / |b.det b'|`. -/
theorem setIntegral_addHaar_eq_of_eq_smul (b b' : Basis ι ℝ E) (c : ℝ)
    {f g : E → G} (hfg : ∀ x, g x = c • f x) (s : Set E) :
    (∫ x in s, g x ∂b'.addHaar) = (c / |b.det b'|) • ∫ x in s, f x ∂b.addHaar := by
  rw [addHaar_eq_smul_of_basis b b', Measure.restrict_smul, integral_smul_measure]
  simp_rw [show g = fun x ↦ c • f x from funext hfg, integral_smul]
  rw [ENNReal.toReal_ofReal (abs_nonneg _), abs_inv, smul_smul, div_eq_mul_inv, mul_comm c]

end Module.Basis
