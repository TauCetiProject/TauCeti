/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# Convexity of relative entropy in its first measure

For a fixed finite reference measure `ρ`, relative entropy is convex in the measure being
compared to `ρ`. On its finite-value domain it is strictly convex: mixing two distinct
finite measures with positive weights gives strictly less than their weighted entropies.
This is the uniqueness mechanism for entropy minimization over convex sets of measures,
in particular sets with prescribed marginals.

The statements use Mathlib's finite-measure I-divergence `InformationTheory.klDiv`, including
its mass correction. Neither normalization nor a topology on the measurable carrier is needed.
Infinite values are retained in the convexity inequality; strictness requires both endpoint
values to be finite. Equality for an interior mixture holds exactly when the measures agree.

For absolutely continuous measures, relative entropy is the integral of
`InformationTheory.klFun` of the Radon–Nikodym density. Strict convexity of this integrand
on `[0, ∞)` forces those densities to agree almost everywhere in the equality case.

## References

* Mathlib, `InformationTheory.klDiv_eq_lintegral_klFun_of_ac` and
  `InformationTheory.strictConvexOn_klFun`.
* I. Csiszár, *I-divergence geometry of probability distributions and minimization problems*,
  Ann. Probability 3 (1975), 146–158.
-/

public section

open MeasureTheory InformationTheory Set
open scoped ENNReal NNReal

namespace TauCeti

variable {α : Type*} [MeasurableSpace α] {μ ν ρ : Measure α} {a b : ℝ≥0}

section Densities

variable [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite ρ]

/-- The entropy integrand of a mixture is the entropy integrand of the mixture of densities. -/
private theorem klFun_rnDeriv_smul_add_smul :
    (fun x ↦ klFun ((a • μ + b • ν).rnDeriv ρ x).toReal) =ᵐ[ρ]
      fun x ↦ klFun (a * (μ.rnDeriv ρ x).toReal + b * (ν.rnDeriv ρ x).toReal) := by
  filter_upwards [Measure.rnDeriv_add' (a • μ) (b • ν) ρ,
    Measure.rnDeriv_smul_left' μ ρ a, Measure.rnDeriv_smul_left' ν ρ b,
    Measure.rnDeriv_lt_top μ ρ, Measure.rnDeriv_lt_top ν ρ] with x hadd hμ hν hμfin hνfin
  simp only [Pi.add_apply, Pi.smul_apply, ENNReal.smul_def, smul_eq_mul] at hadd hμ hν
  simp only [Measure.coe_nnreal_smul] at hadd hμ hν
  rw [hadd, hμ, hν, ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.coe_ne_top hμfin.ne)
    (ENNReal.mul_ne_top ENNReal.coe_ne_top hνfin.ne)]
  simp

/-- The pointwise convexity inequality for the entropy density of a mixture. -/
private theorem klFun_rnDeriv_smul_add_smul_le (hab : a + b = 1) :
    (fun x ↦ klFun ((a • μ + b • ν).rnDeriv ρ x).toReal) ≤ᵐ[ρ]
      fun x ↦ a * klFun (μ.rnDeriv ρ x).toReal + b * klFun (ν.rnDeriv ρ x).toReal := by
  filter_upwards [klFun_rnDeriv_smul_add_smul (μ := μ) (ν := ν) (ρ := ρ) (a := a) (b := b)]
    with x hx
  rw [hx]
  exact convexOn_klFun.2 ENNReal.toReal_nonneg ENNReal.toReal_nonneg a.coe_nonneg b.coe_nonneg
    (by exact_mod_cast hab)

end Densities

variable [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ρ]

/-- Integrating the weighted entropy densities gives the weighted endpoint entropies. -/
private theorem lintegral_weighted_klFun_rnDeriv (hμac : μ ≪ ρ) (hνac : ν ≪ ρ) :
    (∫⁻ x, ENNReal.ofReal
      (a * klFun (μ.rnDeriv ρ x).toReal + b * klFun (ν.rnDeriv ρ x).toReal) ∂ρ) =
        a * klDiv μ ρ + b * klDiv ν ρ := by
  rw [klDiv_eq_lintegral_klFun_of_ac hμac, klDiv_eq_lintegral_klFun_of_ac hνac]
  simp_rw [ENNReal.ofReal_add
    (mul_nonneg a.coe_nonneg (klFun_nonneg ENNReal.toReal_nonneg))
    (mul_nonneg b.coe_nonneg (klFun_nonneg ENNReal.toReal_nonneg)),
    ENNReal.ofReal_mul a.coe_nonneg, ENNReal.ofReal_mul b.coe_nonneg,
    ENNReal.ofReal_coe_nnreal]
  rw [lintegral_add_left (by fun_prop), lintegral_const_mul _ (by fun_prop),
    lintegral_const_mul _ (by fun_prop)]

/-- **Convexity of relative entropy.** For finite measures and nonnegative weights summing to
one, the entropy of their mixture against a fixed finite reference is at most the weighted
sum of their entropies. This includes infinite endpoint values and zero weights. -/
theorem klDiv_smul_add_smul_le (hab : a + b = 1) :
    klDiv (a • μ + b • ν) ρ ≤ a * klDiv μ ρ + b * klDiv ν ρ := by
  rcases eq_or_ne a 0 with rfl | ha
  · have hb : b = 1 := by simpa using hab
    simp [hb]
  rcases eq_or_ne b 0 with rfl | hb
  · have ha : a = 1 := by simpa using hab
    simp [ha]
  by_cases hμ : klDiv μ ρ = ∞
  · simp [hμ, ha]
  by_cases hν : klDiv ν ρ = ∞
  · simp [hν, hb]
  have hμac := (klDiv_ne_top_iff.1 hμ).1
  have hνac := (klDiv_ne_top_iff.1 hν).1
  rw [klDiv_eq_lintegral_klFun_of_ac ((hμac.smul_left a).add_left (hνac.smul_left b)),
    ← lintegral_weighted_klFun_rnDeriv hμac hνac]
  exact lintegral_mono_ae ((klFun_rnDeriv_smul_add_smul_le hab).mono fun _ hx ↦
    ENNReal.ofReal_le_ofReal hx)

/-- **Strict convexity of relative entropy on its finite-value domain.** Two distinct finite
measures with finite entropy against a finite reference have a strict convexity inequality
for every mixture with positive weights. The measures need not have equal mass. -/
theorem klDiv_smul_add_smul_lt (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    (hμ : klDiv μ ρ ≠ ∞) (hν : klDiv ν ρ ≠ ∞) (hne : μ ≠ ν) :
    klDiv (a • μ + b • ν) ρ < a * klDiv μ ρ + b * klDiv ν ρ := by
  have hμac := (klDiv_ne_top_iff.1 hμ).1
  have hνac := (klDiv_ne_top_iff.1 hν).1
  have hac := (hμac.smul_left a).add_left (hνac.smul_left b)
  have hle := klDiv_smul_add_smul_le (μ := μ) (ν := ν) (ρ := ρ) hab
  have hfin : (∫⁻ x, ENNReal.ofReal (klFun ((a • μ + b • ν).rnDeriv ρ x).toReal) ∂ρ) ≠ ∞ := by
    rw [← klDiv_eq_lintegral_klFun_of_ac hac]
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨by finiteness, by finiteness⟩) hle
  refine lt_of_le_of_ne hle fun heq ↦ hne ?_
  rw [klDiv_eq_lintegral_klFun_of_ac hac, ← lintegral_weighted_klFun_rnDeriv hμac hνac] at heq
  have heqae := (lintegral_eq_iff_ae_eq_of_ae_le hfin (by fun_prop)
    ((klFun_rnDeriv_smul_add_smul_le hab).mono fun _ hx ↦ ENNReal.ofReal_le_ofReal hx)).1 heq
  have hdens : μ.rnDeriv ρ =ᵐ[ρ] ν.rnDeriv ρ := by
    filter_upwards [heqae, klFun_rnDeriv_smul_add_smul (μ := μ) (ν := ν) (ρ := ρ)
      (a := a) (b := b), Measure.rnDeriv_lt_top μ ρ, Measure.rnDeriv_lt_top ν ρ]
      with x hx hmixeq hμfin hνfin
    have hreal : (μ.rnDeriv ρ x).toReal = (ν.rnDeriv ρ x).toReal := by
      by_contra hdiff
      have hs := strictConvexOn_klFun.2 ENNReal.toReal_nonneg ENNReal.toReal_nonneg hdiff
        (NNReal.coe_pos.2 ha) (NNReal.coe_pos.2 hb) (by exact_mod_cast hab)
      simp only [smul_eq_mul] at hs
      rw [hmixeq] at hx
      exact ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg
        (klFun_nonneg (add_nonneg (mul_nonneg a.coe_nonneg ENNReal.toReal_nonneg)
          (mul_nonneg b.coe_nonneg ENNReal.toReal_nonneg)))).2 hs).ne hx
    exact (ENNReal.toReal_eq_toReal_iff' hμfin.ne hνfin.ne).1 hreal
  rw [← Measure.withDensity_rnDeriv_eq μ ρ hμac, ← Measure.withDensity_rnDeriv_eq ν ρ hνac,
    withDensity_congr_ae hdens]

/-- For positive mixture weights and finite endpoint entropies, equality in the entropy
convexity inequality holds exactly when the measures are equal. -/
@[simp] theorem klDiv_smul_add_smul_eq_iff (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    (hμ : klDiv μ ρ ≠ ∞) (hν : klDiv ν ρ ≠ ∞) :
    klDiv (a • μ + b • ν) ρ = a * klDiv μ ρ + b * klDiv ν ρ ↔ μ = ν := by
  refine ⟨fun h ↦ by
    by_contra hne
    exact (klDiv_smul_add_smul_lt ha hb hab hμ hν hne).ne h, fun h ↦ ?_⟩
  subst ν
  rw [← add_smul, hab, one_smul, ← add_mul]
  simp [← ENNReal.coe_add, hab]

/-- The finite-entropy domain consists of a convex set of finite measures. -/
theorem convex_setOf_isFiniteMeasure_klDiv_ne_top :
    Convex ℝ≥0 {μ : Measure α | IsFiniteMeasure μ ∧ klDiv μ ρ ≠ ∞} := by
  rintro μ ⟨hμfin, hμ⟩ ν ⟨hνfin, hν⟩ a b _ _ hab
  let := hμfin
  let := hνfin
  exact ⟨inferInstance, ne_top_of_le_ne_top
    (ENNReal.add_ne_top.2 ⟨by finiteness, by finiteness⟩) (klDiv_smul_add_smul_le hab)⟩

/-- Relative entropy, read as a real-valued function on its finite-value domain, is strictly
convex. This allows the usual `StrictConvexOn.eq_of_isMinOn` uniqueness theorem to be used. -/
theorem strictConvexOn_toReal_klDiv :
    StrictConvexOn ℝ≥0 {μ : Measure α | IsFiniteMeasure μ ∧ klDiv μ ρ ≠ ∞}
      (fun μ ↦ (klDiv μ ρ).toReal) := by
  refine ⟨convex_setOf_isFiniteMeasure_klDiv_ne_top, ?_⟩
  rintro μ ⟨hμfin, hμ⟩ ν ⟨hνfin, hν⟩ hne a b ha hb hab
  let := hμfin
  let := hνfin
  have h := ENNReal.toReal_strict_mono
    (ENNReal.add_ne_top.2 ⟨by finiteness, by finiteness⟩)
    (klDiv_smul_add_smul_lt ha hb hab hμ hν hne)
  rw [ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_mul,
    ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.coe_toReal] at h
  simpa only [NNReal.smul_def, smul_eq_mul] using h

end TauCeti
