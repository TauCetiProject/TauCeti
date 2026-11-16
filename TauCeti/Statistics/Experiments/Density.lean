/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.Measure.WithDensity

import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import TauCeti.MeasureTheory.Measure.WithDensity
import TauCeti.Probability.Density

/-!
# Real-valued densities of measures

This file defines `TauCeti.HasDensity P μ f`, stating that `f : X → ℝ` is a measurable,
`μ`-almost-everywhere nonnegative real-valued density of `P` with respect to `μ`:
`P = μ.withDensity (fun x ↦ ENNReal.ofReal (f x))`.

It develops the characteristic API for `HasDensity`:
* measure evaluation, Lebesgue integral transfer, and null-set characterization via the positivity
  set `{x | 0 < f x}`;
* Bochner integral and integrability transfer (without integrability assumptions on the integrand,
  reusing `TauCeti.Probability.integral_withDensity_ofReal` and
  `TauCeti.Probability.integrable_withDensity_ofReal_iff`), together with integrability and unit
  integral of densities of finite and probability measures;
* almost-everywhere congruence, uniqueness for σ-finite measures, identification with
  the Radon–Nikodym derivative, chaining of densities, and pushforward along a map through which
  the density factors (reusing `MeasureTheory.Measure.map_withDensity_comp`).

## References

* M. J. Schervish, *Theory of Statistics*, Springer (1995), Theorems A.54 (p. 591) and A.74 with
  (A.76) (pp. 597–598).
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

variable {X Y F : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {P Q μ : Measure X} {f g : X → ℝ}

/-- `f : X → ℝ` is a real-valued density of `P` with respect to `μ`: `f` is measurable,
`μ`-almost-everywhere nonnegative, and `P = μ.withDensity (fun x ↦ ENNReal.ofReal (f x))`. -/
def HasDensity (P μ : Measure X) (f : X → ℝ) : Prop :=
  Measurable f ∧ (∀ᵐ x ∂μ, 0 ≤ f x) ∧ P = μ.withDensity (fun x ↦ ENNReal.ofReal (f x))

/-- Unfolding lemma for `HasDensity`. -/
theorem hasDensity_def :
    HasDensity P μ f ↔
      Measurable f ∧ (∀ᵐ x ∂μ, 0 ≤ f x) ∧ P = μ.withDensity (fun x ↦ ENNReal.ofReal (f x)) :=
  (Iff.rfl)

/-- A real density is measurable. -/
@[fun_prop]
theorem HasDensity.measurable (h : HasDensity P μ f) : Measurable f :=
  h.1

/-- A real density is almost everywhere nonnegative with respect to the reference measure. -/
theorem HasDensity.ae_nonneg (h : HasDensity P μ f) : ∀ᵐ x ∂μ, 0 ≤ f x :=
  h.2.1

/-- A measure with a real density `f` equals `μ.withDensity (ENNReal.ofReal ∘ f)`. -/
theorem HasDensity.eq_withDensity (h : HasDensity P μ f) :
    P = μ.withDensity (fun x ↦ ENNReal.ofReal (f x)) :=
  h.2.2

/-- A measurable, `μ`-almost-everywhere nonnegative function `f` is a real density of
`μ.withDensity (fun x ↦ ENNReal.ofReal (f x))`. -/
theorem hasDensity_withDensity_ofReal (hf : Measurable f) (hnn : ∀ᵐ x ∂μ, 0 ≤ f x) :
    HasDensity (μ.withDensity (fun x ↦ ENNReal.ofReal (f x))) μ f :=
  ⟨hf, hnn, rfl⟩

/-- Every measure has the constant function `1` as a real density with respect to itself. -/
@[simp]
theorem hasDensity_self (μ : Measure X) : HasDensity μ μ (fun _ ↦ 1) :=
  ⟨measurable_const, ae_of_all _ fun _ ↦ zero_le_one, by simp⟩

/-- A measure with a real density with respect to `μ` is absolutely continuous with respect to
`μ`. -/
theorem HasDensity.absolutelyContinuous (h : HasDensity P μ f) : P ≪ μ := by
  rw [h.eq_withDensity]
  exact withDensity_absolutelyContinuous _ _

/-- A measure with a real density with respect to a σ-finite measure is σ-finite. -/
theorem HasDensity.sigmaFinite [SigmaFinite μ] (h : HasDensity P μ f) : SigmaFinite P := by
  rw [h.eq_withDensity]
  infer_instance

/-- A measure with a real density with respect to an s-finite measure is s-finite. -/
theorem HasDensity.sFinite [SFinite μ] (h : HasDensity P μ f) : SFinite P := by
  rw [h.eq_withDensity]
  infer_instance

/-- Measure of a measurable set under a real density. -/
theorem HasDensity.apply (h : HasDensity P μ f) {s : Set X} (hs : MeasurableSet s) :
    P s = ∫⁻ x in s, ENNReal.ofReal (f x) ∂μ := by
  rw [h.eq_withDensity, withDensity_apply _ hs]

/-- Real measure of a measurable set under a real density, as a set Bochner integral. -/
theorem HasDensity.measureReal_eq_setIntegral (h : HasDensity P μ f) {s : Set X}
    (hs : MeasurableSet s) :
    P.real s = ∫ x in s, f x ∂μ := by
  rw [h.eq_withDensity]
  exact Probability.measureReal_withDensity_ofReal (ae_restrict_of_ae h.ae_nonneg) hs
    h.measurable.aemeasurable.restrict

/-- Lebesgue integral transfer under a real density, with no measurability hypothesis on `g`. -/
theorem HasDensity.lintegral_eq (h : HasDensity P μ f) (g : X → ℝ≥0∞) :
    ∫⁻ x, g x ∂P = ∫⁻ x, ENNReal.ofReal (f x) * g x ∂μ := by
  rw [h.eq_withDensity,
    lintegral_withDensity_eq_lintegral_mul_non_measurable _ h.measurable.ennreal_ofReal
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top) g]
  rfl

/-- A measurable set is `P`-null if and only if its intersection with `{x | 0 < f x}` is
`μ`-null. -/
theorem HasDensity.measure_eq_zero_iff (h : HasDensity P μ f) {s : Set X} (hs : MeasurableSet s) :
    P s = 0 ↔ μ (s ∩ {x | 0 < f x}) = 0 := by
  rw [h.apply hs, lintegral_eq_zero_iff h.measurable.ennreal_ofReal]
  simp only [Filter.EventuallyEq, Pi.zero_apply, ENNReal.ofReal_eq_zero, ae_iff, not_le]
  rw [Measure.restrict_apply' hs, inter_comm]

section Bochner

variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Under a real density `f`, a function is `P`-integrable if and only if its `f`-weighted
version is `μ`-integrable. -/
theorem HasDensity.integrable_iff (h : HasDensity P μ f) (g : X → F) :
    Integrable g P ↔ Integrable (fun x ↦ f x • g x) μ := by
  rw [h.eq_withDensity]
  exact Probability.integrable_withDensity_ofReal_iff h.measurable.aemeasurable h.ae_nonneg

/-- Bochner integral transfer under a real density `f`, with no integrability hypothesis on `g`:
when `g` is not `P`-integrable, both sides vanish. -/
theorem HasDensity.integral_eq (h : HasDensity P μ f) (g : X → F) :
    ∫ x, g x ∂P = ∫ x, f x • g x ∂μ := by
  rw [h.eq_withDensity]
  exact Probability.integral_withDensity_ofReal h.measurable.aemeasurable h.ae_nonneg g

/-- Bochner integral transfer for the pushforward of a measure with a real density. -/
theorem HasDensity.integral_map (h : HasDensity P μ f) {φ : X → Y} (hφ : AEMeasurable φ P)
    {g : Y → F} (hg : AEStronglyMeasurable g (P.map φ)) :
    ∫ y, g y ∂P.map φ = ∫ x, f x • g (φ x) ∂μ := by
  rw [MeasureTheory.integral_map hφ hg, h.integral_eq]

end Bochner

/-- A real density of a finite measure is integrable with respect to the reference measure. -/
theorem HasDensity.integrable [IsFiniteMeasure P] (h : HasDensity P μ f) : Integrable f μ :=
  Probability.integrable_of_eq_withDensity h.eq_withDensity h.measurable.aemeasurable h.ae_nonneg

/-- The Bochner integral of a real density equals the real total mass of the measure. -/
theorem HasDensity.integral_eq_measureReal_univ (h : HasDensity P μ f) :
    ∫ x, f x ∂μ = P.real univ := by
  rw [h.measureReal_eq_setIntegral MeasurableSet.univ, Measure.restrict_univ]

/-- The Bochner integral of a real density of a probability measure equals `1`. -/
theorem HasDensity.integral_eq_one [IsProbabilityMeasure P] (h : HasDensity P μ f) :
    ∫ x, f x ∂μ = 1 := by
  rw [h.integral_eq_measureReal_univ, probReal_univ]

/-- Replacing a real density by a `μ`-almost-everywhere equal measurable function preserves
`HasDensity`. -/
theorem HasDensity.congr_ae (h : HasDensity P μ f) (hg : Measurable g) (hfg : f =ᵐ[μ] g) :
    HasDensity P μ g := by
  refine ⟨hg, ?_, ?_⟩
  · filter_upwards [h.ae_nonneg, hfg] with x hx hxeq
    exact hxeq ▸ hx
  · rw [h.eq_withDensity]
    refine withDensity_congr_ae ?_
    filter_upwards [hfg] with x hxeq
    rw [hxeq]

/-- Two real densities of the same σ-finite measure agree almost everywhere with respect to the
reference measure. (In particular, this holds whenever `P` is finite, or whenever `μ` is σ-finite
via `HasDensity.sigmaFinite`.) -/
theorem HasDensity.ae_eq [SigmaFinite P] (h₁ : HasDensity P μ f) (h₂ : HasDensity P μ g) :
    f =ᵐ[μ] g := by
  have hae_n : ∀ n, (fun x ↦ ENNReal.ofReal (f x)) =ᵐ[μ.restrict (spanningSets P n)]
      fun x ↦ ENNReal.ofReal (g x) := fun n ↦ by
    have hs : MeasurableSet (spanningSets P n) := measurableSet_spanningSets P n
    have heq : (μ.restrict (spanningSets P n)).withDensity (fun x ↦ ENNReal.ofReal (f x)) =
        (μ.restrict (spanningSets P n)).withDensity (fun x ↦ ENNReal.ofReal (g x)) := by
      rw [← restrict_withDensity hs, ← restrict_withDensity hs, ← h₁.eq_withDensity,
        ← h₂.eq_withDensity]
    have hfin : ∫⁻ x, ENNReal.ofReal (f x) ∂μ.restrict (spanningSets P n) ≠ ∞ := by
      rw [← h₁.apply hs]
      exact (measure_spanningSets_lt_top P n).ne
    exact (withDensity_eq_iff h₁.measurable.ennreal_ofReal.aemeasurable
      h₂.measurable.ennreal_ofReal.aemeasurable hfin).mp heq
  have hae : (fun x ↦ ENNReal.ofReal (f x)) =ᵐ[μ] fun x ↦ ENNReal.ofReal (g x) := by
    rw [Filter.EventuallyEq, ae_iff]
    have hcov : {x | ¬ENNReal.ofReal (f x) = ENNReal.ofReal (g x)} =
        ⋃ n, {x | ¬ENNReal.ofReal (f x) = ENNReal.ofReal (g x)} ∩ spanningSets P n := by
      rw [← inter_iUnion, iUnion_spanningSets, inter_univ]
    rw [hcov]
    refine measure_iUnion_null fun n ↦ ?_
    have h0 := ae_iff.mp (hae_n n)
    rwa [Measure.restrict_apply' (measurableSet_spanningSets P n)] at h0
  filter_upwards [hae, h₁.ae_nonneg, h₂.ae_nonneg] with x hxeq hfx hgx
  have := congrArg ENNReal.toReal hxeq
  simpa [ENNReal.toReal_ofReal hfx, ENNReal.toReal_ofReal hgx] using this

/-- The Radon–Nikodym derivative of a measure with real density `f` with respect to a σ-finite
reference measure agrees almost everywhere with `ENNReal.ofReal ∘ f`. -/
theorem HasDensity.rnDeriv_ae_eq [SigmaFinite μ] (h : HasDensity P μ f) :
    P.rnDeriv μ =ᵐ[μ] fun x ↦ ENNReal.ofReal (f x) := by
  rw [h.eq_withDensity]
  exact Measure.rnDeriv_withDensity μ h.measurable.ennreal_ofReal

/-- The real part of the Radon–Nikodym derivative of a measure with real density `f` with respect
to a σ-finite reference measure agrees almost everywhere with `f`. -/
theorem HasDensity.toReal_rnDeriv_ae_eq [SigmaFinite μ] (h : HasDensity P μ f) :
    (fun x ↦ (P.rnDeriv μ x).toReal) =ᵐ[μ] f := by
  filter_upwards [h.rnDeriv_ae_eq, h.ae_nonneg] with x hxeq hfx
  rw [hxeq, ENNReal.toReal_ofReal hfx]

/-- If `P` is σ-finite and absolutely continuous with respect to `μ` (with a Lebesgue
decomposition), then `(P.rnDeriv μ ·).toReal` is a real density of `P` with respect to `μ`. -/
theorem hasDensity_rnDeriv [SigmaFinite P] [P.HaveLebesgueDecomposition μ] (hac : P ≪ μ) :
    HasDensity P μ (fun x ↦ (P.rnDeriv μ x).toReal) := by
  refine ⟨(Measure.measurable_rnDeriv P μ).ennreal_toReal,
    ae_of_all _ fun _ ↦ ENNReal.toReal_nonneg, ?_⟩
  conv_lhs => rw [← Measure.withDensity_rnDeriv_eq P μ hac]
  refine withDensity_congr_ae ?_
  filter_upwards [Measure.rnDeriv_lt_top P μ] with x hx
  rw [ENNReal.ofReal_toReal hx.ne]

/-- Chaining real densities: if `P` has density `g` with respect to `Q` and `Q` has density `h`
with respect to `μ`, then `P` has density `g * h` with respect to `μ`. -/
theorem HasDensity.trans (hPQ : HasDensity P Q g) (hQμ : HasDensity Q μ h) :
    HasDensity P μ (fun x ↦ g x * h x) := by
  have hgnn : ∀ᵐ x ∂μ, 0 ≤ h x → h x = 0 ∨ 0 ≤ g x := by
    have hQ : ∀ᵐ x ∂(μ.withDensity (fun x ↦ ENNReal.ofReal (h x))), 0 ≤ g x :=
      hQμ.eq_withDensity ▸ hPQ.ae_nonneg
    rw [ae_withDensity_iff hQμ.measurable.ennreal_ofReal] at hQ
    filter_upwards [hQ] with x hx hhx
    by_cases h0 : h x = 0
    · exact Or.inl h0
    · refine Or.inr (hx ?_)
      simp [ENNReal.ofReal_eq_zero, not_le.mpr (lt_of_le_of_ne hhx (Ne.symm h0))]
  refine ⟨hPQ.measurable.mul hQμ.measurable, ?_, ?_⟩
  · filter_upwards [hQμ.ae_nonneg, hgnn] with x hhx hcases
    rcases hcases hhx with h0 | hgx
    · simp [h0]
    · exact mul_nonneg hgx hhx
  · rw [hPQ.eq_withDensity, hQμ.eq_withDensity,
      ← withDensity_mul _ hQμ.measurable.ennreal_ofReal hPQ.measurable.ennreal_ofReal]
    refine withDensity_congr_ae ?_
    filter_upwards [hQμ.ae_nonneg, hgnn] with x hhx hcases
    rcases hcases hhx with h0 | hgx
    · simp [h0]
    · rw [Pi.mul_apply, mul_comm, ENNReal.ofReal_mul hgx]

/-- Pushforward of a real density that factors through a measurable map `φ`: if `P` has real
density `g ∘ φ` with respect to `μ`, then `P.map φ` has real density `g` with respect to
`μ.map φ`. -/
theorem HasDensity.map_comp {φ : X → Y} {g : Y → ℝ} (hφ : Measurable φ) (hg : Measurable g)
    (h : HasDensity P μ (g ∘ φ)) :
    HasDensity (P.map φ) (μ.map φ) g := by
  refine ⟨hg, ?_, ?_⟩
  · rw [ae_map_iff hφ.aemeasurable (measurableSet_le measurable_const hg)]
    exact h.ae_nonneg
  · rw [h.eq_withDensity]
    exact Measure.map_withDensity_comp hφ hg.ennreal_ofReal

end TauCeti
