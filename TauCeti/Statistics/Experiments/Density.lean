/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import TauCeti.MeasureTheory.Integral.Bochner.WithDensity
import TauCeti.MeasureTheory.Measure.Decomposition.RNDeriv
import TauCeti.MeasureTheory.Measure.PiWithDensity

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
density `k` of `P.map φ` with respect to `μ.map φ`. Densities of the factors of a finite product
multiply to a density of the product measure.

## Main definitions

* `TauCeti.HasDensity P μ f`: `f` is a real density of `P` with respect to `μ`.

## Main results

* `TauCeti.hasDensity_def`, `TauCeti.hasDensity_of_measure_apply_eq_setLIntegral`,
  `TauCeti.hasDensity_toReal_rnDeriv`: unfolding and introduction lemmas for `HasDensity`.
* `TauCeti.HasDensity.congr_ae`, `TauCeti.HasDensity.ae_eq`,
  `TauCeti.HasDensity.ae_eq_of_sigmaFinite`, `TauCeti.HasDensity.ae_eq_toReal_rnDeriv`: a
  density may be changed on a `μ`-null set, is unique up to a `μ`-null set for σ-finite `μ` or
  σ-finite `P`, and agrees `μ`-a.e. with `(P.rnDeriv μ ·).toReal`.
* `TauCeti.HasDensity.ae_pos`: a density is positive almost everywhere for the measure it
  defines.
* `TauCeti.HasDensity.measure_apply_eq_zero_iff`: a set is `P`-null iff its intersection with
  `{x | 0 < f x}` is `μ`-null.
* `TauCeti.HasDensity.measure_apply`, `TauCeti.HasDensity.measureReal_apply`,
  `TauCeti.HasDensity.restrict`: extended and real set masses as integrals of the density, and
  restriction of a density to a measurable set.
* `TauCeti.HasDensity.lintegral_eq`, `TauCeti.HasDensity.integral_eq`: Lebesgue and Bochner
  integral transfers for `P`.
* `TauCeti.HasDensity.integrable_iff`: `g` is `P`-integrable iff `f • g` is `μ`-integrable.
* `TauCeti.HasDensity.integrable`, `TauCeti.HasDensity.integral_eq_one`: the density of a finite
  measure is integrable, and that of a probability measure has integral `1`.
* `TauCeti.HasDensity.integral_map`: the integral transfer for the pushforward `P.map φ`.
* `TauCeti.HasDensity.map`: a density `k ∘ φ` of `P` gives the density `k` of `P.map φ` with
  respect to `μ.map φ`.
* `TauCeti.HasDensity.trans`: chaining real densities `P ≪ Q ≪ μ`.
* `TauCeti.HasDensity.pi`: densities `f i` of `P i` give the product density `∏ i, f i (x i)` of
  `Measure.pi P` with respect to `Measure.pi μ`.

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

/-- Unfolding lemma for `HasDensity`. -/
theorem hasDensity_def :
    HasDensity P μ f ↔
      Measurable f ∧ 0 ≤ᵐ[μ] f ∧ P = μ.withDensity fun x ↦ ENNReal.ofReal (f x) :=
  ⟨fun h ↦ ⟨h.measurable, h.ae_nonneg, h.eq_withDensity⟩, fun ⟨h1, h2, h3⟩ ↦ ⟨h1, h2, h3⟩⟩

/-- A measurable, almost everywhere nonnegative function `f` whose set Lebesgue integrals
`∫⁻ x in s, ENNReal.ofReal (f x) ∂μ` equal `P s` for all measurable sets `s` is a density of `P`
with respect to `μ`. -/
theorem hasDensity_of_measure_apply_eq_setLIntegral (hf : Measurable f) (hf₀ : 0 ≤ᵐ[μ] f)
    (happly : ∀ {s : Set X}, MeasurableSet s → P s = ∫⁻ x in s, ENNReal.ofReal (f x) ∂μ) :
    HasDensity P μ f := by
  refine ⟨hf, hf₀, ?_⟩
  ext s hs
  rw [happly hs, withDensity_apply _ hs]

/-- A measurable, almost everywhere nonnegative `f` is a density of `μ.withDensity (ofReal ∘ f)`. -/
theorem hasDensity_withDensity_ofReal (hf : Measurable f) (hf₀ : 0 ≤ᵐ[μ] f) :
    HasDensity (μ.withDensity fun x ↦ ENNReal.ofReal (f x)) μ f :=
  ⟨hf, hf₀, rfl⟩

/-- The real-valued Radon–Nikodym derivative `(P.rnDeriv μ ·).toReal` is a real density of a
σ-finite measure `P` with respect to `μ`, provided `P ≪ μ` and `P` has a Lebesgue decomposition
with respect to `μ`. -/
theorem hasDensity_toReal_rnDeriv [SigmaFinite P] [P.HaveLebesgueDecomposition μ]
    (hPμ : P ≪ μ) :
    HasDensity P μ fun x ↦ (P.rnDeriv μ x).toReal := by
  refine ⟨(Measure.measurable_rnDeriv P μ).ennreal_toReal,
    ae_of_all _ fun _ ↦ ENNReal.toReal_nonneg, ?_⟩
  calc P = μ.withDensity (P.rnDeriv μ) := (Measure.withDensity_rnDeriv_eq P μ hPμ).symm
    _ = μ.withDensity fun x ↦ ENNReal.ofReal (P.rnDeriv μ x).toReal :=
        withDensity_congr_ae (Measure.ofReal_toReal_rnDeriv P μ).symm

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

/-- **Uniqueness of densities under σ-finite `P`.** Two densities of the same σ-finite measure
agree almost everywhere with respect to the reference measure `μ`, even if `μ` is only s-finite. -/
theorem ae_eq_of_sigmaFinite [SigmaFinite P] (hf : HasDensity P μ f) {g : X → ℝ}
    (hg : HasDensity P μ g) : f =ᵐ[μ] g := by
  have : SigmaFinite (μ.withDensity fun x ↦ ENNReal.ofReal (f x)) :=
    hf.eq_withDensity ▸ inferInstance
  have h := (withDensity_eq_iff_of_sigmaFinite_withDensity hf.measurable.ennreal_ofReal.aemeasurable
    hg.measurable.ennreal_ofReal.aemeasurable).mp (hf.eq_withDensity.symm.trans hg.eq_withDensity)
  filter_upwards [h, hf.ae_nonneg, hg.ae_nonneg] with x hx hfx hgx
  exact (ENNReal.ofReal_eq_ofReal_iff hfx hgx).mp hx

/-- **Uniqueness of densities.** Two densities of the same measure with respect to a σ-finite
measure agree almost everywhere. -/
theorem ae_eq [SigmaFinite μ] (hf : HasDensity P μ f) {g : X → ℝ} (hg : HasDensity P μ g) :
    f =ᵐ[μ] g :=
  have : SigmaFinite P := hf.eq_withDensity ▸ inferInstance
  hf.ae_eq_of_sigmaFinite hg

/-- Any real density of a σ-finite measure `P` with respect to `μ` agrees `μ`-almost everywhere
with the real-valued Radon–Nikodym derivative `(P.rnDeriv μ ·).toReal`. -/
theorem ae_eq_toReal_rnDeriv [SigmaFinite P] (hf : HasDensity P μ f) :
    f =ᵐ[μ] fun x ↦ (P.rnDeriv μ x).toReal :=
  have : P.HaveLebesgueDecomposition μ :=
    hf.eq_withDensity ▸ Measure.haveLebesgueDecomposition_withDensity μ hf.measurable.ennreal_ofReal
  hf.ae_eq_of_sigmaFinite (hasDensity_toReal_rnDeriv hf.absolutelyContinuous)

/-- A density is positive almost everywhere with respect to the measure it defines. -/
theorem ae_pos (h : HasDensity P μ f) : ∀ᵐ x ∂P, 0 < f x := by
  rw [h.eq_withDensity, ae_withDensity_iff h.measurable.ennreal_ofReal]
  exact ae_of_all _ fun x hx ↦ ENNReal.ofReal_pos.1 (pos_iff_ne_zero.2 hx)

/-- A set is `P`-null iff its intersection with `{x | 0 < f x}` is `μ`-null. -/
theorem measure_apply_eq_zero_iff (h : HasDensity P μ f) {s : Set X} :
    P s = 0 ↔ μ ({x | 0 < f x} ∩ s) = 0 := by
  rw [h.eq_withDensity, withDensity_apply_eq_zero h.measurable.ennreal_ofReal]
  simp

/-- The mass of a measurable set is the integral of the density over it. -/
theorem measure_apply (h : HasDensity P μ f) {s : Set X} (hs : MeasurableSet s) :
    P s = ∫⁻ x in s, ENNReal.ofReal (f x) ∂μ := by
  rw [h.eq_withDensity, withDensity_apply _ hs]

/-- The real mass of a `μ`-null-measurable set is the integral of the density over it. -/
theorem measureReal_apply (h : HasDensity P μ f) {s : Set X} (hs : NullMeasurableSet s μ) :
    P.real s = ∫ x in s, f x ∂μ := by
  rw [h.eq_withDensity]
  exact MeasureTheory.measureReal_withDensity_ofReal (ae_restrict_of_ae h.ae_nonneg) hs
    h.measurable.aemeasurable.restrict

/-- Restricting both a measure and its reference measure to a measurable set preserves the
density. -/
theorem restrict (h : HasDensity P μ f) {s : Set X} (hs : MeasurableSet s) :
    HasDensity (P.restrict s) (μ.restrict s) f where
  measurable := h.measurable
  ae_nonneg := ae_restrict_of_ae h.ae_nonneg
  eq_withDensity := by rw [h.eq_withDensity, restrict_withDensity hs]

/-- **The Lebesgue integral transfer.** Integration of a nonnegative function against `P` is
integration against `μ` weighted by `ENNReal.ofReal ∘ f`, with no measurability hypothesis on
`g`. -/
theorem lintegral_eq (h : HasDensity P μ f) (g : X → ℝ≥0∞) :
    ∫⁻ x, g x ∂P = ∫⁻ x, ENNReal.ofReal (f x) * g x ∂μ := by
  rw [h.eq_withDensity]
  exact lintegral_withDensity_eq_lintegral_mul_non_measurable μ h.measurable.ennreal_ofReal
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top) g

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
    exact Measure.map_withDensity_comp hφ.aemeasurable hk.ennreal_ofReal.aemeasurable

/-- **Chaining real densities.** If `P` has density `g` with respect to `Q` and `Q` has density
`h` with respect to `μ`, then `P` has density `g * h` with respect to `μ`. -/
theorem trans {Q : Measure X} {g h : X → ℝ} (hPQ : HasDensity P Q g) (hQμ : HasDensity Q μ h) :
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
  have hae : ∀ᵐ x ∂μ, 0 ≤ g x * h x ∧
      ENNReal.ofReal (h x) * ENNReal.ofReal (g x) = ENNReal.ofReal (g x * h x) := by
    filter_upwards [hQμ.ae_nonneg, hgnn] with x hhx hcases
    rcases hcases hhx with h0 | hgx
    · simp [h0]
    · exact ⟨mul_nonneg hgx hhx, by rw [mul_comm, ENNReal.ofReal_mul hgx]⟩
  refine ⟨hPQ.measurable.mul hQμ.measurable, hae.mono fun _ h ↦ h.1, ?_⟩
  rw [hPQ.eq_withDensity, hQμ.eq_withDensity,
    ← withDensity_mul _ hQμ.measurable.ennreal_ofReal hPQ.measurable.ennreal_ofReal]
  exact withDensity_congr_ae (hae.mono fun _ h ↦ h.2)

/-- **Densities of a finite product.** If `f i` is a density of `P i` with respect to the
σ-finite measure `μ i` for each `i` in a finite type, then `x ↦ ∏ i, f i (x i)` is a density of
the product measure `Measure.pi P` with respect to `Measure.pi μ`. -/
theorem pi {ι : Type*} [Fintype ι] {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    {P μ : ∀ i, Measure (X i)} [∀ i, SigmaFinite (μ i)] {f : ∀ i, X i → ℝ}
    (h : ∀ i, HasDensity (P i) (μ i) (f i)) :
    HasDensity (Measure.pi P) (Measure.pi μ) fun x ↦ ∏ i, f i (x i) := by
  have hall : ∀ᵐ x ∂Measure.pi μ, ∀ i, 0 ≤ f i (x i) :=
    ae_all_iff.2 fun i ↦ Measure.tendsto_eval_ae_ae.eventually (h i).ae_nonneg
  refine ⟨Finset.measurable_prod _ fun i _ ↦ (h i).measurable.comp (measurable_pi_apply i),
    hall.mono fun x hx ↦ Finset.prod_nonneg fun i _ ↦ hx i, ?_⟩
  obtain rfl : P = fun i ↦ (μ i).withDensity fun x ↦ ENNReal.ofReal (f i x) :=
    funext fun i ↦ (h i).eq_withDensity
  rw [pi_withDensity μ fun i ↦ (h i).measurable.ennreal_ofReal]
  refine withDensity_congr_ae ?_
  filter_upwards [hall] with x hx
  exact (ENNReal.ofReal_prod_of_nonneg fun i _ ↦ hx i).symm

end HasDensity

end TauCeti
