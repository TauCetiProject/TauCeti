/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import TauCeti.MeasureTheory.Measure.WithDensity
import TauCeti.Probability.Density

/-!
# Real-valued densities of measures

In mathematical statistics, parametric families of probability measures are commonly presented by
real-valued densities `f : X → ℝ` with respect to a reference measure `μ`. This file defines the
predicate `TauCeti.HasDensity P μ f`, meaning that `f` is measurable, `μ`-almost everywhere
nonnegative, and satisfies `P = μ.withDensity (fun x ↦ ENNReal.ofReal (f x))`.

We provide the characteristic API for `HasDensity`: projections, almost-everywhere congruence,
absolute continuity, uniqueness up to `μ`-almost everywhere equality for σ-finite `μ`,
identification with the Radon–Nikodym derivative, transfer of integrability and Bochner integrals
(including non-integrable integrands, where both sides vanish), evaluation of set masses, scaling,
addition, chaining of densities, and pushforward along a map through which the density factors or
along a measurable equivalence.

The integration and pushforward identities delegate directly to `TauCeti.Probability.Density` and
`TauCeti.MeasureTheory.Measure.WithDensity`.

## Main definitions

* `TauCeti.HasDensity P μ f`: `f : X → ℝ` is a real-valued density of `P` with respect to `μ`.

## Main results

* `TauCeti.HasDensity.integrable_iff`: a function `g` is `P`-integrable iff `x ↦ f x • g x` is
  `μ`-integrable.
* `TauCeti.HasDensity.integral_eq`: `∫ x, g x ∂P = ∫ x, f x • g x ∂μ`, with no integrability
  assumption.
* `TauCeti.HasDensity.integrable`: a density of a finite measure is `μ`-integrable.
* `TauCeti.HasDensity.integral_eq_one`: a density of a probability measure integrates to `1`.
* `TauCeti.HasDensity.ae_eq_of_hasDensity`: two real densities of the same measure against a
  σ-finite reference measure agree almost everywhere.
* `TauCeti.HasDensity.trans`: chain rule for real densities.
* `TauCeti.HasDensity.map_comp`: pushforward of a density factoring through a measurable map.

## References

* M. J. Schervish, *Theory of Statistics*, Springer, 1995, Appendix A (Theorems A.54 and A.74).
-/

public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal

namespace TauCeti

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {P Q μ ν : Measure X} {f g : X → ℝ}

/-- `HasDensity P μ f` says that `f` is a real-valued density of `P` with respect to `μ`: `f` is
measurable, `μ`-almost everywhere nonnegative, and `P` is `μ` weighted by `ENNReal.ofReal ∘ f`. -/
def HasDensity (P μ : Measure X) (f : X → ℝ) : Prop :=
  Measurable f ∧ (∀ᵐ x ∂μ, 0 ≤ f x) ∧ P = μ.withDensity (fun x ↦ ENNReal.ofReal (f x))

/-- Unfolding characterization of `HasDensity`. -/
theorem hasDensity_iff :
    HasDensity P μ f ↔
      Measurable f ∧ (∀ᵐ x ∂μ, 0 ≤ f x) ∧ P = μ.withDensity (fun x ↦ ENNReal.ofReal (f x)) :=
  (Iff.rfl)

namespace HasDensity

/-- A real density is measurable. -/
theorem measurable (h : HasDensity P μ f) : Measurable f :=
  h.1

/-- A real density is nonnegative almost everywhere with respect to the reference measure. -/
theorem ae_nonneg (h : HasDensity P μ f) : ∀ᵐ x ∂μ, 0 ≤ f x :=
  h.2.1

/-- A measure with real density `f` equals `μ.withDensity (ENNReal.ofReal ∘ f)`. -/
theorem eq_withDensity (h : HasDensity P μ f) :
    P = μ.withDensity (fun x ↦ ENNReal.ofReal (f x)) :=
  h.2.2

/-- A measure with a density is absolutely continuous with respect to the reference measure. -/
theorem absolutelyContinuous (h : HasDensity P μ f) : P ≪ μ := by
  rw [h.eq_withDensity]
  exact withDensity_absolutelyContinuous _ _

/-- A real density is strictly positive almost everywhere with respect to the measure it defines. -/
theorem ae_pos (h : HasDensity P μ f) : ∀ᵐ x ∂P, 0 < f x := by
  rw [h.eq_withDensity, ae_withDensity_iff h.measurable.ennreal_ofReal]
  exact ae_of_all _ fun _ hx ↦ ENNReal.ofReal_pos.mp (pos_iff_ne_zero.mpr hx)

/-- Modifying a real density on a `μ`-null set while preserving measurability preserves
`HasDensity`. -/
theorem congr_ae (h : HasDensity P μ f) (hg : Measurable g) (hfg : f =ᵐ[μ] g) :
    HasDensity P μ g := by
  refine ⟨hg, ?_, ?_⟩
  · filter_upwards [h.ae_nonneg, hfg] with x hx hxeq
    exact hxeq ▸ hx
  · rw [h.eq_withDensity]
    refine withDensity_congr_ae ?_
    filter_upwards [hfg] with x hxeq
    rw [hxeq]

/-- Two real densities of the same measure against a σ-finite reference measure agree almost
everywhere. -/
theorem ae_eq_of_hasDensity [SigmaFinite μ] (hf : HasDensity P μ f) (hg : HasDensity P μ g) :
    f =ᵐ[μ] g := by
  have heq : (fun x ↦ ENNReal.ofReal (f x)) =ᵐ[μ] fun x ↦ ENNReal.ofReal (g x) :=
    (withDensity_eq_iff_of_sigmaFinite hf.measurable.ennreal_ofReal.aemeasurable
      hg.measurable.ennreal_ofReal.aemeasurable).mp (hf.eq_withDensity.symm.trans hg.eq_withDensity)
  filter_upwards [heq, hf.ae_nonneg, hg.ae_nonneg] with x hfx hfn hgn
  exact (ENNReal.ofReal_eq_ofReal_iff hfn hgn).mp hfx

/-- The Radon–Nikodym derivative of a measure with real density `f` against a σ-finite reference
measure agrees almost everywhere with `ENNReal.ofReal ∘ f`. -/
theorem rnDeriv_ae_eq [SigmaFinite μ] (h : HasDensity P μ f) :
    P.rnDeriv μ =ᵐ[μ] fun x ↦ ENNReal.ofReal (f x) := by
  rw [h.eq_withDensity]
  exact Measure.rnDeriv_withDensity μ h.measurable.ennreal_ofReal

/-- The measure of a measurable set under a real density is the set Lebesgue integral of its
`ENNReal.ofReal` lift. -/
theorem apply_eq_lintegral (h : HasDensity P μ f) {s : Set X} (hs : MeasurableSet s) :
    P s = ∫⁻ x in s, ENNReal.ofReal (f x) ∂μ := by
  rw [h.eq_withDensity, withDensity_apply _ hs]

/-- Lebesgue integration against a measure with real density `f`. -/
theorem lintegral_eq (h : HasDensity P μ f) {φ : X → ℝ≥0∞} (hφ : AEMeasurable φ P) :
    ∫⁻ x, φ x ∂P = ∫⁻ x, ENNReal.ofReal (f x) * φ x ∂μ := by
  have hφ' : AEMeasurable φ (μ.withDensity fun x ↦ ENNReal.ofReal (f x)) :=
    h.eq_withDensity ▸ hφ
  rw [h.eq_withDensity,
    lintegral_withDensity_eq_lintegral_mul₀' h.measurable.ennreal_ofReal.aemeasurable hφ']
  rfl

/-- Under a measure with real density `f`, a function is integrable iff its `f`-weighted product is
integrable against the reference measure. -/
theorem integrable_iff (h : HasDensity P μ f) {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {φ : X → F} :
    Integrable φ P ↔ Integrable (fun x ↦ f x • φ x) μ := by
  rw [h.eq_withDensity]
  exact TauCeti.Probability.integrable_withDensity_ofReal_iff h.measurable.aemeasurable h.ae_nonneg

/-- Bochner integration against a measure with real density `f` reduces to `f`-weighted integration
against the reference measure. No integrability assumption is needed: both sides vanish when the
integrand is not integrable. -/
theorem integral_eq (h : HasDensity P μ f) {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (φ : X → F) :
    ∫ x, φ x ∂P = ∫ x, f x • φ x ∂μ := by
  rw [h.eq_withDensity]
  exact TauCeti.Probability.integral_withDensity_ofReal h.measurable.aemeasurable h.ae_nonneg φ

/-- A real density of a finite measure is integrable against the reference measure. -/
theorem integrable [IsFiniteMeasure P] (h : HasDensity P μ f) : Integrable f μ :=
  TauCeti.Probability.integrable_of_eq_withDensity h.eq_withDensity
    h.measurable.aemeasurable h.ae_nonneg

/-- The real mass of a measurable set under a real density is the set integral of the density. -/
theorem measureReal_eq (h : HasDensity P μ f) {s : Set X} (hs : MeasurableSet s) :
    P.real s = ∫ x in s, f x ∂μ := by
  rw [h.eq_withDensity]
  exact TauCeti.Probability.measureReal_withDensity_ofReal (ae_restrict_of_ae h.ae_nonneg) hs
    h.measurable.aemeasurable.restrict

/-- The integral of a real density equals the total real mass of the measure. -/
theorem integral_eq_measureReal_univ (h : HasDensity P μ f) :
    ∫ x, f x ∂μ = P.real Set.univ := by
  rw [h.measureReal_eq MeasurableSet.univ, Measure.restrict_univ]

/-- The integral of a real density of a probability measure equals `1`. -/
theorem integral_eq_one [IsProbabilityMeasure P] (h : HasDensity P μ f) :
    ∫ x, f x ∂μ = 1 := by
  rw [h.integral_eq_measureReal_univ, probReal_univ]

/-- Scaling a measure by a nonnegative constant scales its real density by the same constant. -/
theorem smul (h : HasDensity P μ f) {c : ℝ} (hc : 0 ≤ c) :
    HasDensity (ENNReal.ofReal c • P) μ (fun x ↦ c * f x) := by
  refine ⟨measurable_const.mul h.measurable, ?_, ?_⟩
  · filter_upwards [h.ae_nonneg] with x hx
    exact mul_nonneg hc hx
  · rw [h.eq_withDensity, ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
    exact congrArg μ.withDensity (funext fun x ↦ by simp [ENNReal.ofReal_mul hc])

/-- The sum of two measures with real densities against the same reference measure has the sum of
their densities. -/
theorem add (hP : HasDensity P μ f) (hQ : HasDensity Q μ g) :
    HasDensity (P + Q) μ (fun x ↦ f x + g x) := by
  refine ⟨hP.measurable.add hQ.measurable, ?_, ?_⟩
  · filter_upwards [hP.ae_nonneg, hQ.ae_nonneg] with x hfx hgx
    exact add_nonneg hfx hgx
  · rw [hP.eq_withDensity, hQ.eq_withDensity,
      ← withDensity_add_left hP.measurable.ennreal_ofReal]
    refine withDensity_congr_ae ?_
    filter_upwards [hP.ae_nonneg, hQ.ae_nonneg] with x hfx hgx
    exact (ENNReal.ofReal_add hfx hgx).symm

/-- Chain rule for real densities: if `P` has density `f` with respect to `ν` and `ν` has density
`g` with respect to `μ`, then `P` has density `x ↦ f x * g x` with respect to `μ`. -/
theorem trans (hPν : HasDensity P ν f) (hνμ : HasDensity ν μ g) :
    HasDensity P μ (fun x ↦ f x * g x) := by
  have hfg_nn : ∀ᵐ x ∂μ, 0 ≤ f x * g x := by
    have hfν : ∀ᵐ x ∂μ, ENNReal.ofReal (g x) ≠ 0 → 0 ≤ f x := by
      have h := hPν.ae_nonneg
      rw [hνμ.eq_withDensity, ae_withDensity_iff hνμ.measurable.ennreal_ofReal] at h
      exact h
    filter_upwards [hνμ.ae_nonneg, hfν] with x hgx hfx
    by_cases hg0 : g x = 0
    · simp [hg0]
    · exact mul_nonneg (hfx (ENNReal.ofReal_pos.mpr (lt_of_le_of_ne hgx (Ne.symm hg0))).ne') hgx
  refine ⟨hPν.measurable.mul hνμ.measurable, hfg_nn, ?_⟩
  rw [hPν.eq_withDensity, hνμ.eq_withDensity,
    ← withDensity_mul μ hνμ.measurable.ennreal_ofReal hPν.measurable.ennreal_ofReal]
  refine withDensity_congr_ae ?_
  filter_upwards [hνμ.ae_nonneg] with x hgx
  rw [Pi.mul_apply, mul_comm (ENNReal.ofReal (g x)), ← ENNReal.ofReal_mul' hgx]

/-- Pushforward of a density factoring through a measurable map: if `P` has density `k ∘ φ` with
respect to `μ`, then `P.map φ` has density `k` with respect to `μ.map φ`. -/
theorem map_comp {φ : X → Y} {k : Y → ℝ} (hφ : Measurable φ) (hk : Measurable k)
    (h : HasDensity P μ (k ∘ φ)) :
    HasDensity (P.map φ) (μ.map φ) k := by
  refine ⟨hk, ?_, ?_⟩
  · rw [ae_map_iff hφ.aemeasurable (measurableSet_le measurable_const hk)]
    exact h.ae_nonneg
  · rw [h.eq_withDensity]
    exact Measure.map_withDensity_comp hφ hk.ennreal_ofReal

/-- Pushforward of a real density along a measurable equivalence. -/
theorem map_equiv (h : HasDensity P μ f) (e : X ≃ᵐ Y) :
    HasDensity (P.map e) (μ.map e) (f ∘ e.symm) := by
  refine ⟨h.measurable.comp e.symm.measurable, ?_, ?_⟩
  · rw [ae_map_iff e.measurable.aemeasurable
      (measurableSet_le measurable_const (h.measurable.comp e.symm.measurable))]
    filter_upwards [h.ae_nonneg] with x hx
    simpa using hx
  · rw [h.eq_withDensity, MeasurableEquiv.map_withDensity]
    rfl

end HasDensity

/-- A nonnegative measurable function `f` defines a measure `μ.withDensity (ENNReal.ofReal ∘ f)`
having real density `f` with respect to `μ`. -/
theorem hasDensity_withDensity_ofReal (hf : Measurable f) (hf₀ : ∀ᵐ x ∂μ, 0 ≤ f x) :
    HasDensity (μ.withDensity fun x ↦ ENNReal.ofReal (f x)) μ f :=
  ⟨hf, hf₀, rfl⟩

/-- Every measure has constant density `1` with respect to itself. -/
@[simp]
theorem hasDensity_self (μ : Measure X) : HasDensity μ μ (fun _ ↦ 1) :=
  ⟨measurable_const, ae_of_all _ fun _ ↦ zero_le_one, by simp⟩

/-- The zero measure has constant density `0` with respect to any reference measure. -/
@[simp]
theorem hasDensity_zero (μ : Measure X) : HasDensity 0 μ (fun _ ↦ 0) :=
  ⟨measurable_const, ae_of_all _ fun _ ↦ le_rfl, by simp⟩

/-- Restricting `μ` to a measurable set `s` has density `s.indicator 1` with respect to `μ`. -/
theorem hasDensity_restrict_indicator (μ : Measure X) {s : Set X} (hs : MeasurableSet s) :
    HasDensity (μ.restrict s) μ (s.indicator 1) := by
  refine ⟨measurable_const.indicator hs, ae_of_all _ fun x ↦ ?_, ?_⟩
  · by_cases hx : x ∈ s <;> simp [hx]
  · rw [← withDensity_indicator_one hs]
    congr 1
    ext x
    by_cases hx : x ∈ s <;> simp [hx]

/-- If `P ≪ μ` with `P` σ-finite and admitting a Lebesgue decomposition against `μ`, then
`x ↦ (P.rnDeriv μ x).toReal` is a real density of `P` with respect to `μ`. -/
theorem hasDensity_toReal_rnDeriv [SigmaFinite P] [P.HaveLebesgueDecomposition μ]
    (hP : P ≪ μ) :
    HasDensity P μ (fun x ↦ (P.rnDeriv μ x).toReal) := by
  refine ⟨(Measure.measurable_rnDeriv P μ).ennreal_toReal,
    ae_of_all _ fun _ ↦ ENNReal.toReal_nonneg, ?_⟩
  refine (Measure.withDensity_rnDeriv_eq P μ hP).symm.trans (withDensity_congr_ae ?_)
  filter_upwards [Measure.rnDeriv_lt_top P μ] with x hx
  exact (ENNReal.ofReal_toReal hx.ne).symm

end TauCeti
