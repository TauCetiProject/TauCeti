/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.MeasureTheory.Measure.WithDensity
import TauCeti.MeasureTheory.Integral.Bochner.WithDensity

/-!
# Real densities of statistical models

A statistical model is usually specified by real densities with respect to a fixed reference
measure. `TauCeti.HasDensity P μ f` says that the real function `f` is a density of `P` with
respect to `μ`: `f` is measurable, `μ`-a.e. nonnegative, and `P = μ.withDensity (ofReal ∘ f)`.
A density may be changed on a `μ`-null set, and when `μ` is σ-finite it is unique up to such a
change.
Measures with densities in `ℝ≥0∞` are handled by Mathlib's `withDensity` and `rnDeriv` directly.

The integral transfer `∫ g dP = ∫ f • g dμ` holds for every integrand `g`, with no integrability
hypothesis, since both sides take the junk value `0` together; integrability transfers in the
same way. A finite measure has an integrable density, and a probability measure a density of
integral `1`. A density that factors as `k ∘ φ` through a measurable map `φ` pushes forward to the
density `k` of `P.map φ` with respect to `μ.map φ`.

## Main definitions

* `TauCeti.HasDensity P μ f`: `f` is a real density of `P` with respect to `μ`.

## Main results

* `TauCeti.HasDensity.congr_ae`, `TauCeti.HasDensity.ae_eq`: a density may be changed on a
  `μ`-null set, and for σ-finite `μ` it is unique up to such a change.
* `TauCeti.HasDensity.integral_eq`: `∫ g dP = ∫ f • g dμ`, for every `g`.
* `TauCeti.HasDensity.integrable_iff`: `g` is `P`-integrable iff `f • g` is `μ`-integrable.
* `TauCeti.HasDensity.integrable`, `TauCeti.HasDensity.integral_eq_one`: the density of a finite
  measure is integrable, and that of a probability measure has integral `1`.
* `TauCeti.HasDensity.integral_map`: the integral transfer for the pushforward `P.map φ`.
* `TauCeti.HasDensity.map`: a density `k ∘ φ` of `P` gives the density `k` of `P.map φ` with
  respect to `μ.map φ`.

## References

* M. J. Schervish, *Theory of Statistics*, Springer (1995), Theorem A.54 and Theorem A.74 with
  (A.76).
-/

public section

open MeasureTheory

open scoped ENNReal

namespace TauCeti

variable {X Y E : Type*} [MeasurableSpace X] [MeasurableSpace Y] [NormedAddCommGroup E]
  [NormedSpace ℝ E] {P μ : Measure X} {f : X → ℝ}

/-- `f` is a **real density** of the measure `P` with respect to the reference measure `μ`: it is
measurable, nonnegative `μ`-almost everywhere, and `P = μ.withDensity (ENNReal.ofReal ∘ f)`. -/
structure HasDensity (P μ : Measure X) (f : X → ℝ) : Prop where
  /-- A density is measurable. -/
  measurable : Measurable f
  /-- A density is nonnegative almost everywhere. -/
  ae_nonneg : 0 ≤ᵐ[μ] f
  /-- The measure is the reference measure weighted by the density. -/
  eq_withDensity : P = μ.withDensity fun x ↦ ENNReal.ofReal (f x)

/-- A measurable, almost everywhere nonnegative `f` is a density of `μ.withDensity (ofReal ∘ f)`. -/
theorem hasDensity_withDensity_ofReal (hf : Measurable f) (hf₀ : 0 ≤ᵐ[μ] f) :
    HasDensity (μ.withDensity fun x ↦ ENNReal.ofReal (f x)) μ f :=
  ⟨hf, hf₀, rfl⟩

namespace HasDensity

/-- A measure with a density is absolutely continuous with respect to the reference measure. -/
theorem absolutelyContinuous (h : HasDensity P μ f) : P ≪ μ :=
  h.eq_withDensity ▸ withDensity_absolutelyContinuous μ _

/-- A density may be changed on a `μ`-null set, keeping it measurable. -/
theorem congr_ae (h : HasDensity P μ f) {g : X → ℝ} (hg : Measurable g) (hfg : f =ᵐ[μ] g) :
    HasDensity P μ g where
  measurable := hg
  ae_nonneg := by
    filter_upwards [h.ae_nonneg, hfg] with x hx hfx
    rwa [← hfx]
  eq_withDensity := h.eq_withDensity.trans <| withDensity_congr_ae <| by
    filter_upwards [hfg] with x hx
    rw [hx]

/-- **Uniqueness of densities.** Two densities of the same measure with respect to a σ-finite
measure agree almost everywhere. -/
theorem ae_eq [SigmaFinite μ] (hf : HasDensity P μ f) {g : X → ℝ} (hg : HasDensity P μ g) :
    f =ᵐ[μ] g := by
  have h := (withDensity_eq_iff_of_sigmaFinite hf.measurable.ennreal_ofReal.aemeasurable
    hg.measurable.ennreal_ofReal.aemeasurable).mp (hf.eq_withDensity.symm.trans hg.eq_withDensity)
  filter_upwards [h, hf.ae_nonneg, hg.ae_nonneg] with x hx hfx hgx
  exact (ENNReal.ofReal_eq_ofReal_iff hfx hgx).mp hx

/-- The mass of a measurable set is the integral of the density over it. -/
theorem measure_apply (h : HasDensity P μ f) {s : Set X} (hs : MeasurableSet s) :
    P s = ∫⁻ x in s, ENNReal.ofReal (f x) ∂μ := by
  rw [h.eq_withDensity, withDensity_apply _ hs]

/-- **The integral transfer.** Integration against `P` is integration of the `f`-weighted
integrand against `μ`. No integrability hypothesis is needed: when `g` is not `P`-integrable,
`f • g` is not `μ`-integrable either, and both sides are `0`. -/
theorem integral_eq (h : HasDensity P μ f) (g : X → E) :
    ∫ x, g x ∂P = ∫ x, f x • g x ∂μ := by
  rw [h.eq_withDensity]
  exact MeasureTheory.integral_withDensity_ofReal h.measurable.aemeasurable h.ae_nonneg g

/-- A function is `P`-integrable iff its product with the density is `μ`-integrable. -/
theorem integrable_iff (h : HasDensity P μ f) {g : X → E} :
    Integrable g P ↔ Integrable (fun x ↦ f x • g x) μ := by
  rw [h.eq_withDensity]
  exact MeasureTheory.integrable_withDensity_ofReal_iff h.measurable.aemeasurable h.ae_nonneg

/-- The density of a finite measure is integrable. -/
theorem integrable [IsFiniteMeasure P] (h : HasDensity P μ f) : Integrable f μ :=
  MeasureTheory.integrable_of_eq_withDensity h.eq_withDensity h.measurable.aemeasurable h.ae_nonneg

/-- The density of a probability measure has integral `1`. -/
theorem integral_eq_one [IsProbabilityMeasure P] (h : HasDensity P μ f) : ∫ x, f x ∂μ = 1 := by
  simpa using (h.integral_eq fun _ ↦ (1 : ℝ)).symm

/-- **The integral transfer for pushforwards.** Integration against the image of `P` under `φ` is
integration of the `f`-weighted integrand `g ∘ φ` against `μ`. -/
theorem integral_map (h : HasDensity P μ f) {φ : X → Y} (hφ : AEMeasurable φ P) {g : Y → E}
    (hg : AEStronglyMeasurable g (P.map φ)) :
    ∫ y, g y ∂P.map φ = ∫ x, f x • g (φ x) ∂μ := by
  rw [MeasureTheory.integral_map hφ hg, h.integral_eq]

/-- **Pushing a density forward.** If the density of `P` factors as `k ∘ φ` through a measurable
map `φ`, with `k` measurable, then `k` is a density of `P.map φ` with respect to `μ.map φ`. -/
theorem map {k : Y → ℝ} {φ : X → Y} (h : HasDensity P μ (k ∘ φ)) (hφ : Measurable φ)
    (hk : Measurable k) : HasDensity (P.map φ) (μ.map φ) k where
  measurable := hk
  ae_nonneg := (ae_map_iff hφ.aemeasurable (measurableSet_le measurable_const hk)).mpr h.ae_nonneg
  eq_withDensity := by
    rw [h.eq_withDensity]
    exact Measure.map_withDensity_comp hφ hk.ennreal_ofReal

end HasDensity

end TauCeti
