/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.GeneralizedGamma.Basic
public import TauCeti.Probability.Density
public import Mathlib.MeasureTheory.Measure.Support
import TauCeti.Analysis.SpecialFunctions.Gamma
import TauCeti.MeasureTheory.Measure.WithDensity

/-!
# Densities and support of generalized gamma laws

On the positive half-line the generalized gamma density is
`|c| / (s * Gamma a) * (x / s) ^ (a * c - 1) * exp (-(x / s) ^ c)`.
The absolute value of the power parameter is essential when that parameter is negative.
The density is zero at invalid parameters and at nonpositive arguments. This file identifies
the power pushforward with its Lebesgue density and supplies its probability-density and
Radon–Nikodym interfaces and exact topological support.

The change of variables uses `TauCeti.MeasureTheory.map_withDensity_abs_deriv_mul` on the
positive half-line, following the density-transport pattern of the log-normal law.

## References

* E. W. Stacy, *A Generalization of the Gamma Distribution*, Annals of Mathematical
  Statistics 33 (1962), 1187–1192. We also allow negative power parameters.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

namespace TauCeti.Probability

variable {a c s x : ℝ}

/-- The real generalized gamma density, zero outside its valid parameter range and support. -/
def generalizedGammaPDFReal (a c s x : ℝ) : ℝ :=
  if 0 < a ∧ c ≠ 0 ∧ 0 < s ∧ 0 < x then
    |c| / (s * Real.Gamma a) * (x / s) ^ (a * c - 1) * exp (-(x / s) ^ c)
  else 0

/-- The extended nonnegative generalized gamma density. -/
def generalizedGammaPDF (a c s x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (generalizedGammaPDFReal a c s x)

/-- The extended density is the nonnegative coercion of the real density. -/
theorem generalizedGammaPDF_eq_ofReal (a c s x : ℝ) :
    generalizedGammaPDF a c s x = ENNReal.ofReal (generalizedGammaPDFReal a c s x) := (rfl)

/-- The density formula at valid parameters and a positive argument. -/
@[simp]
theorem generalizedGammaPDFReal_of_pos
    (ha : 0 < a) (hc : c ≠ 0) (hs : 0 < s) (hx : 0 < x) :
    generalizedGammaPDFReal a c s x =
      |c| / (s * Real.Gamma a) * (x / s) ^ (a * c - 1) * exp (-(x / s) ^ c) := by
  simp [generalizedGammaPDFReal, ha, hc, hs, hx]

/-- The density vanishes at invalid parameters. -/
@[simp]
theorem generalizedGammaPDFReal_of_not_valid (h : ¬ (0 < a ∧ c ≠ 0 ∧ 0 < s)) (x : ℝ) :
    generalizedGammaPDFReal a c s x = 0 := by
  simp only [generalizedGammaPDFReal]
  split_ifs with hx
  · exact (h ⟨hx.1, hx.2.1, hx.2.2.1⟩).elim
  · rfl

/-- The density vanishes at nonpositive arguments. -/
@[simp]
theorem generalizedGammaPDFReal_of_nonpos (hx : x ≤ 0) :
    generalizedGammaPDFReal a c s x = 0 := by
  simp [generalizedGammaPDFReal, not_lt.mpr hx]

/-- The extended density formula at valid parameters and a positive argument. -/
@[simp]
theorem generalizedGammaPDF_of_pos
    (ha : 0 < a) (hc : c ≠ 0) (hs : 0 < s) (hx : 0 < x) :
    generalizedGammaPDF a c s x = ENNReal.ofReal
      (|c| / (s * Real.Gamma a) * (x / s) ^ (a * c - 1) * exp (-(x / s) ^ c)) := by
  rw [generalizedGammaPDF_eq_ofReal, generalizedGammaPDFReal_of_pos ha hc hs hx]

/-- The extended density vanishes at invalid parameters. -/
@[simp]
theorem generalizedGammaPDF_of_not_valid (h : ¬ (0 < a ∧ c ≠ 0 ∧ 0 < s)) (x : ℝ) :
    generalizedGammaPDF a c s x = 0 := by
  simp [generalizedGammaPDF_eq_ofReal, generalizedGammaPDFReal_of_not_valid h]

/-- The extended density vanishes at nonpositive arguments. -/
@[simp]
theorem generalizedGammaPDF_of_nonpos (hx : x ≤ 0) : generalizedGammaPDF a c s x = 0 := by
  simp [generalizedGammaPDF_eq_ofReal, generalizedGammaPDFReal_of_nonpos hx]

/-- The real density is nonnegative for all parameters and arguments. -/
theorem generalizedGammaPDFReal_nonneg (a c s x : ℝ) :
    0 ≤ generalizedGammaPDFReal a c s x := by
  unfold generalizedGammaPDFReal
  split_ifs with h
  · exact mul_nonneg (mul_nonneg (div_nonneg (abs_nonneg c)
      (mul_pos h.2.2.1 (Gamma_pos_of_pos h.1)).le)
      (rpow_nonneg (div_pos h.2.2.2 h.2.2.1).le _)) (exp_nonneg _)
  · rfl

/-- The extended density has the named real density as its real value. -/
@[simp]
theorem toReal_generalizedGammaPDF (a c s x : ℝ) :
    (generalizedGammaPDF a c s x).toReal = generalizedGammaPDFReal a c s x := by
  rw [generalizedGammaPDF_eq_ofReal, ENNReal.toReal_ofReal (generalizedGammaPDFReal_nonneg a c s x)]

/-- Joint measurability of the density in parameters and sample point. -/
@[fun_prop]
theorem measurable_uncurry_generalizedGammaPDFReal :
    Measurable fun p : (ℝ × ℝ × ℝ) × ℝ ↦
      generalizedGammaPDFReal p.1.1 p.1.2.1 p.1.2.2 p.2 := by
  unfold generalizedGammaPDFReal
  have hnorm : Measurable fun p : (ℝ × ℝ × ℝ) × ℝ ↦ ‖p.1.2.1‖ := by fun_prop
  have habs : Measurable fun p : (ℝ × ℝ × ℝ) × ℝ ↦ |p.1.2.1| := by
    simpa only [Real.norm_eq_abs] using hnorm
  exact Measurable.ite (by measurability) (by fun_prop) measurable_const

/-- Measurability of the real density in its sample point. -/
@[fun_prop]
theorem measurable_generalizedGammaPDFReal (a c s : ℝ) :
    Measurable (generalizedGammaPDFReal a c s) :=
  measurable_uncurry_generalizedGammaPDFReal.comp
    ((measurable_const (a := (a, c, s))).prodMk measurable_id)

/-- Joint measurability of the extended density. -/
@[fun_prop]
theorem measurable_uncurry_generalizedGammaPDF :
    Measurable fun p : (ℝ × ℝ × ℝ) × ℝ ↦ generalizedGammaPDF p.1.1 p.1.2.1 p.1.2.2 p.2 :=
  measurable_uncurry_generalizedGammaPDFReal.ennreal_ofReal

/-- Measurability of the extended density in its sample point. -/
@[fun_prop]
theorem measurable_generalizedGammaPDF (a c s : ℝ) : Measurable (generalizedGammaPDF a c s) :=
  measurable_uncurry_generalizedGammaPDF.comp
    ((measurable_const (a := (a, c, s))).prodMk measurable_id)

/-- At valid parameters the density is positive exactly on the positive half-line. -/
@[simp]
theorem support_generalizedGammaPDF (ha : 0 < a) (hc : c ≠ 0) (hs : 0 < s) :
    Function.support (generalizedGammaPDF a c s) = Ioi 0 := by
  ext x
  simp only [Function.mem_support, generalizedGammaPDF_eq_ofReal, ENNReal.ofReal_ne_zero_iff,
    mem_Ioi]
  by_cases hx : 0 < x
  · simp only [generalizedGammaPDFReal_of_pos ha hc hs hx, hx, iff_true]
    exact mul_pos (mul_pos (div_pos (abs_pos.mpr hc) (mul_pos hs (Gamma_pos_of_pos ha)))
      (rpow_pos_of_pos (div_pos hx hs) _)) (exp_pos _)
  · simp [generalizedGammaPDFReal_of_nonpos (le_of_not_gt hx), hx]

private theorem generalizedGamma_density_jacobian
    (ha : 0 < a) (hc : c ≠ 0) (hs : 0 < s) (hx : 0 < x) :
    ENNReal.ofReal |s * (c⁻¹ * x ^ (c⁻¹ - 1))| *
        generalizedGammaPDF a c s (s * x ^ c⁻¹) = gammaPDF a 1 x := by
  rw [generalizedGammaPDF_eq_ofReal, ← ENNReal.ofReal_mul (abs_nonneg _),
    generalizedGammaPDFReal_of_pos ha hc hs (mul_pos hs (rpow_pos_of_pos hx _)),
    gammaPDF_of_nonneg hx.le]
  congr 1
  rw [mul_div_cancel_left₀ _ hs.ne', rpow_inv_rpow hx.le hc, ← rpow_mul hx.le,
    abs_mul, abs_of_pos hs, abs_mul, abs_inv,
    abs_of_pos (rpow_pos_of_pos hx _)]
  have hexp : c⁻¹ - 1 + c⁻¹ * (a * c - 1) = a - 1 := by
    field_simp
    ring
  calc
    _ = (s * |c|⁻¹ * (|c| / (s * Gamma a))) *
        (x ^ (c⁻¹ - 1) * x ^ (c⁻¹ * (a * c - 1))) * exp (-x) := by ring
    _ = _ := by
      rw [← rpow_add hx, hexp]
      simp only [one_rpow, one_mul]
      field_simp

/-- The generalized gamma power pushforward has its named Lebesgue density at all parameters. -/
theorem generalizedGammaMeasure_eq_withDensity (a c s : ℝ) :
    generalizedGammaMeasure a c s = volume.withDensity (generalizedGammaPDF a c s) := by
  by_cases h : 0 < a ∧ c ≠ 0 ∧ 0 < s
  swap
  · have hz : generalizedGammaPDF a c s = 0 := by
      ext x
      simp [generalizedGammaPDF_eq_ofReal, generalizedGammaPDFReal_of_not_valid h]
    simp [h, hz]
  obtain ⟨ha, hc, hs⟩ := h
  have himage : (fun x : ℝ ↦ s * x ^ c⁻¹) '' Ioi 0 = Ioi 0 := by
    ext y
    refine ⟨fun ⟨x, hx, hxy⟩ ↦ hxy ▸ mul_pos hs (rpow_pos_of_pos hx _), fun hy ↦ ?_⟩
    refine ⟨(y / s) ^ c, rpow_pos_of_pos (div_pos hy hs) _, ?_⟩
    dsimp only
    rw [rpow_rpow_inv (div_pos hy hs).le hc, mul_div_cancel₀ _ hs.ne']
  have hinj : InjOn (fun x : ℝ ↦ s * x ^ c⁻¹) (Ioi 0) := by
    intro x hx y hy hxy
    exact (rpow_left_inj hx.le hy.le (inv_ne_zero hc)).1 (mul_left_cancel₀ hs.ne' hxy)
  have hmap := TauCeti.MeasureTheory.map_withDensity_abs_deriv_mul
    (f := generalizedGammaPDF a c s) measurableSet_Ioi (by fun_prop)
    (fun x hx ↦ ((Real.hasDerivAt_rpow_const (Or.inl hx.ne')).const_mul s).hasDerivWithinAt) hinj
  have hweight := withDensity_congr_ae (μ := volume.restrict (Ioi (0 : ℝ)))
    ((ae_restrict_mem measurableSet_Ioi).mono fun x hx ↦
      generalizedGamma_density_jacobian ha hc hs hx)
  rw [hweight, himage] at hmap
  rw [generalizedGammaMeasure_of_valid ha hc hs,
    gammaMeasure_eq_withDensity_restrict_Ioi, hmap, ← withDensity_indicator measurableSet_Ioi,
    indicator_eq_self.mpr (support_generalizedGammaPDF ha hc hs).le]

/-- Joint Giry measurability of the entire totalized generalized gamma family. -/
@[fun_prop]
theorem measurable_generalizedGammaMeasure :
    Measurable fun p : ℝ × ℝ × ℝ ↦ generalizedGammaMeasure p.1 p.2.1 p.2.2 := by
  simp_rw [generalizedGammaMeasure_eq_withDensity]
  exact measurable_withDensity measurable_uncurry_generalizedGammaPDF

/-- Generalized gamma laws have no atoms, including at invalid parameters. -/
instance (a c s : ℝ) : NullSingletonClass (generalizedGammaMeasure a c s) := by
  rw [generalizedGammaMeasure_eq_withDensity]
  infer_instance

/-- Valid generalized gamma laws have exact topological support `[0, ∞)`. -/
@[simp]
theorem support_generalizedGammaMeasure (ha : 0 < a) (hc : c ≠ 0) (hs : 0 < s) :
    (generalizedGammaMeasure a c s).support = Ici 0 := by
  rw [generalizedGammaMeasure_eq_withDensity,
    Measure.support_withDensity_eq_closure (measurable_generalizedGammaPDF a c s) isOpen_Ioi
      (support_generalizedGammaPDF ha hc hs), closure_Ioi]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}

/-- A random variable with a generalized gamma law has a Lebesgue density. -/
theorem hasPDF_of_hasLaw_generalizedGammaMeasure
    (hX : HasLaw X (generalizedGammaMeasure a c s) P) : HasPDF X P := by
  rw [generalizedGammaMeasure_eq_withDensity] at hX
  exact hasPDF_of_hasLaw_withDensity (measurable_generalizedGammaPDF a c s).aemeasurable hX

/-- The random-variable density agrees almost everywhere with the named density. -/
theorem pdf_eq_generalizedGammaPDF_of_hasLaw_generalizedGammaMeasure
    (hX : HasLaw X (generalizedGammaMeasure a c s) P) :
    pdf X P =ᵐ[volume] generalizedGammaPDF a c s := by
  rw [generalizedGammaMeasure_eq_withDensity] at hX
  exact pdf_eq_of_hasLaw_withDensity (measurable_generalizedGammaPDF a c s).aemeasurable hX

/-- The generalized gamma Radon–Nikodym derivative is its named density. -/
theorem rnDeriv_generalizedGammaMeasure (a c s : ℝ) :
    (generalizedGammaMeasure a c s).rnDeriv volume =ᵐ[volume] generalizedGammaPDF a c s := by
  rw [generalizedGammaMeasure_eq_withDensity]
  exact Measure.rnDeriv_withDensity _ (measurable_generalizedGammaPDF a c s)

end TauCeti.Probability
