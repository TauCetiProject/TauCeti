/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Probability.ConditionalProbability
public import TauCeti.MeasureTheory.Integral.PiSystem

/-!
# Product-measure helpers

Small pieces of product-measure theory with no `L²` or inner-product content.

* `TauCeti.ae_of_ae_fst` / `TauCeti.ae_of_ae_snd` transfer an a.e. statement about one factor to the
  product measure, along `Measure.quasiMeasurePreserving_fst` / `_snd`.
* `TauCeti.measurable_setLIntegral_of_measurableSet` proves measurability of a set integral whose
  truncating relation is jointly measurable.
* `TauCeti.lintegral_mul_setLIntegral_eq` exchanges a weighted integral of set integrals over an
  arbitrary parameter measure with the corresponding integral over the sections of the truncating
  relation.
* `TauCeti.lintegral_cond_prod_le` bounds a lower Lebesgue integral over a product of two
  conditional laws by any bound the integrand satisfies on the rectangle conditioned on. Use it to
  estimate an integral against two independently conditioned coordinates when the integrand is
  controlled only on the pair of sets being conditioned on.
* `TauCeti.setIntegral_eq_zero_of_forall_prod` is the binary-product specialization of the Dynkin
  (π-λ) step for Bochner integrals: a function whose integral vanishes on every measurable rectangle
  has vanishing integral on every measurable set. Rectangles are a π-system generating the product
  σ-algebra (`MeasureTheory.isPiSystem_prod`, `MeasureTheory.generateFrom_prod`), so this is the
  general `TauCeti.setIntegral_eq_zero_of_isPiSystem` instantiated at that π-system; the only work
  left here is extracting the whole-space hypothesis from the rectangle `univ ×ˢ univ`.
-/

public section

namespace TauCeti

open MeasureTheory Set
open scoped ENNReal ProbabilityTheory

variable {α β γ E : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} {μ : Measure α} {ν : Measure β} {κ : Measure γ}
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The truncated integral `t ↦ ∫⁻ x in {x | R t x}, g x ∂μ` is measurable when the truncating
relation is jointly measurable. -/
theorem measurable_setLIntegral_of_measurableSet [SFinite μ] {g : α → ℝ≥0∞}
    {R : γ → α → Prop} (hR : MeasurableSet {z : γ × α | R z.1 z.2}) (hg : Measurable g) :
    Measurable fun t => ∫⁻ x in {x | R t x}, g x ∂μ := by
  have hRx : ∀ t : γ, MeasurableSet {x | R t x} := fun t => measurable_prodMk_left hR
  have hind : ∀ t : γ, ∫⁻ x in {x | R t x}, g x ∂μ =
      ∫⁻ x, {z : γ × α | R z.1 z.2}.indicator (fun z => g z.2) (t, x) ∂μ := by
    intro t
    rw [← lintegral_indicator (hRx t)]
    rfl
  simp_rw [hind]
  exact ((hg.comp measurable_snd).indicator hR).lintegral_prod_right'

/-- **Tonelli for a weighted integral of truncated integrals.** For a jointly measurable
truncating relation `R` and measurable weight `w`, integrating first in `x` and then against the
parameter measure gives the same value as integrating the weight over each parameter section and
then in `x`. -/
theorem lintegral_mul_setLIntegral_eq [SFinite μ] [SFinite κ] {g : α → ℝ≥0∞} {w : γ → ℝ≥0∞}
    {R : γ → α → Prop} (hR : MeasurableSet {z : γ × α | R z.1 z.2}) (hg : Measurable g)
    (hw : Measurable w) :
    ∫⁻ t, w t * ∫⁻ x in {x | R t x}, g x ∂μ ∂κ =
      ∫⁻ x, (∫⁻ t, {t : γ | R t x}.indicator w t ∂κ) * g x ∂μ := by
  have hRx : ∀ t : γ, MeasurableSet {x | R t x} := fun t => measurable_prodMk_left hR
  have hRt : ∀ x : α, MeasurableSet {t : γ | R t x} := fun x => measurable_prodMk_right hR
  set G : γ × α → ℝ≥0∞ :=
    {z : γ × α | R z.1 z.2}.indicator (fun z => w z.1 * g z.2) with hG
  have hGmeas : Measurable G :=
    ((hw.comp measurable_fst).mul (hg.comp measurable_snd)).indicator hR
  -- The same cut-off reads as a condition on `x` for a fixed `t`, or as one on `t` for a fixed `x`;
  -- each `show` names the set whose indicator is being unfolded, which a bare `hx` leaves open.
  have hGx : ∀ (t : γ) (x : α), G (t, x) = w t * {x | R t x}.indicator g x := by
    intro t x
    by_cases hx : R t x
    · rw [hG, Set.indicator_of_mem (show (t, x) ∈ {z : γ × α | R z.1 z.2} from hx),
        Set.indicator_of_mem (show x ∈ {x | R t x} from hx)]
    · rw [hG, Set.indicator_of_notMem (show (t, x) ∉ {z : γ × α | R z.1 z.2} from hx),
        Set.indicator_of_notMem (show x ∉ {x | R t x} from hx), mul_zero]
  have hGt : ∀ (t : γ) (x : α), G (t, x) = {t : γ | R t x}.indicator w t * g x := by
    intro t x
    by_cases hx : R t x
    · rw [hG, Set.indicator_of_mem (show (t, x) ∈ {z : γ × α | R z.1 z.2} from hx),
        Set.indicator_of_mem (show t ∈ {t : γ | R t x} from hx)]
    · rw [hG, Set.indicator_of_notMem (show (t, x) ∉ {z : γ × α | R z.1 z.2} from hx),
        Set.indicator_of_notMem (show t ∉ {t : γ | R t x} from hx), zero_mul]
  have hslice : ∀ t : γ, ∫⁻ x, G (t, x) ∂μ = w t * ∫⁻ x in {x | R t x}, g x ∂μ := by
    intro t
    rw [← lintegral_indicator (hRx t), ← lintegral_const_mul _ (hg.indicator (hRx t))]
    exact lintegral_congr fun x => hGx t x
  have hinner : ∀ x : α, (∫⁻ t, G (t, x) ∂κ) =
      (∫⁻ t, {t : γ | R t x}.indicator w t ∂κ) * g x := by
    intro x
    rw [← lintegral_mul_const _ (hw.indicator (hRt x))]
    exact lintegral_congr fun t => hGt t x
  refine (lintegral_congr fun t => (hslice t).symm).trans ?_
  rw [lintegral_lintegral_swap (μ := κ) (ν := μ) (f := fun t x => G (t, x))
    hGmeas.aemeasurable]
  exact lintegral_congr hinner

/-- An a.e. statement on the first factor transfers to the product measure. -/
theorem ae_of_ae_fst [SFinite ν] {p : α → Prop} (hp : ∀ᵐ x ∂μ, p x) :
    ∀ᵐ q : α × β ∂(μ.prod ν), p q.1 :=
  Measure.quasiMeasurePreserving_fst.tendsto_ae.eventually hp

/-- An a.e. statement on the second factor transfers to the product measure. -/
theorem ae_of_ae_snd [SFinite ν] {p : β → Prop} (hp : ∀ᵐ y ∂ν, p y) :
    ∀ᵐ q : α × β ∂(μ.prod ν), p q.2 :=
  Measure.quasiMeasurePreserving_snd.tendsto_ae.eventually hp

/-- **A rectangle bound for an integral against a product of conditional laws.** If `f` is bounded
by `b` on `s ×ˢ t`, then its lower Lebesgue integral against the product of the laws of `μ` and `ν`
conditioned on `s` and on `t` is at most `b`: conditioning confines each coordinate to its own set
almost surely, so the bound holds almost everywhere on the product. -/
theorem lintegral_cond_prod_le {s : Set α} {t : Set β} (hs : MeasurableSet s)
    (ht : MeasurableSet t) (hμ : μ s ≠ 0) (hμtop : μ s ≠ ∞) (hν : ν t ≠ 0) (hνtop : ν t ≠ ∞)
    {f : α × β → ℝ≥0∞} {b : ℝ≥0∞} (hf : ∀ x ∈ s, ∀ y ∈ t, f (x, y) ≤ b) :
    ∫⁻ z, f z ∂((μ[|s]).prod (ν[|t])) ≤ b := by
  have := ProbabilityTheory.cond_isProbabilityMeasure_of_finite hμ hμtop
  have := ProbabilityTheory.cond_isProbabilityMeasure_of_finite hν hνtop
  refine lintegral_le_const ?_
  filter_upwards [ae_of_ae_fst (ν := ν[|t]) (ProbabilityTheory.ae_cond_mem (μ := μ) hs),
    ae_of_ae_snd (μ := μ[|s]) (ProbabilityTheory.ae_cond_mem (μ := ν) ht)] with ⟨x, y⟩ hx hy
  exact hf x hx y hy

/-- **The Dynkin (π-λ) step for Bochner integrals on a product space.** A function whose integral
vanishes on every measurable rectangle has vanishing integral on every measurable set.

This is `TauCeti.setIntegral_eq_zero_of_isPiSystem` at the π-system of measurable rectangles. -/
theorem setIntegral_eq_zero_of_forall_prod {ρ : Measure (α × β)} {f : α × β → E}
    (hf : Integrable f ρ)
    (hrect : ∀ s, MeasurableSet s → ∀ t, MeasurableSet t → ∫ p in s ×ˢ t, f p ∂ρ = 0) :
    ∀ u, MeasurableSet u → ∫ p in u, f p ∂ρ = 0 := by
  have huniv : ∫ p, f p ∂ρ = 0 := by
    have h := hrect Set.univ MeasurableSet.univ Set.univ MeasurableSet.univ
    rwa [Set.univ_prod_univ, setIntegral_univ] at h
  refine setIntegral_eq_zero_of_isPiSystem generateFrom_prod.symm isPiSystem_prod hf huniv ?_
  rintro _ ⟨s, hs, t, ht, rfl⟩
  exact hrect s hs t ht

end TauCeti
