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
* `TauCeti.lintegral_mul_setLIntegral_eq` exchanges a weighted integral of set integrals with the
  corresponding integral over the sections of the truncating relation.
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

variable {α β E : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ : Measure α} {ν : Measure β}
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The truncated integral `t ↦ ∫⁻ x in {x | R t x}, g x ∂μ` is measurable when the truncating
relation is jointly measurable. -/
theorem measurable_setLIntegral_of_measurableSet [SFinite μ] {g : α → ℝ≥0∞}
    {R : ℝ → α → Prop} (hR : MeasurableSet {z : ℝ × α | R z.1 z.2}) (hg : Measurable g) :
    Measurable fun t => ∫⁻ x in {x | R t x}, g x ∂μ := by
  have hRx : ∀ t : ℝ, MeasurableSet {x | R t x} := fun t => measurable_prodMk_left hR
  have hind : ∀ t : ℝ, ∫⁻ x in {x | R t x}, g x ∂μ =
      ∫⁻ x, {z : ℝ × α | R z.1 z.2}.indicator (fun z => g z.2) (t, x) ∂μ := by
    intro t
    rw [← lintegral_indicator (hRx t)]
    rfl
  simp_rw [hind]
  exact ((hg.comp measurable_snd).indicator hR).lintegral_prod_right'

/-- **Tonelli for a weighted integral of truncated integrals.** For a jointly measurable
truncating relation `R`, the weight `t ^ s` pairs with the truncated integrals of `g` in either
order: integrating first in `x` and then in `t` gives the same value as integrating the weight
over the `t`-section of `R` and then in `x`. -/
theorem lintegral_mul_setLIntegral_eq [SFinite μ] {g : α → ℝ≥0∞} {R : ℝ → α → Prop}
    (hR : MeasurableSet {z : ℝ × α | R z.1 z.2}) (hg : Measurable g) (s : ℝ) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ s) * ∫⁻ x in {x | R t x}, g x ∂μ =
      ∫⁻ x, (∫⁻ t in Ioi (0 : ℝ),
        {t : ℝ | R t x}.indicator (fun t => ENNReal.ofReal (t ^ s)) t) * g x ∂μ := by
  have hRx : ∀ t : ℝ, MeasurableSet {x | R t x} := fun t => measurable_prodMk_left hR
  have hRt : ∀ x : α, MeasurableSet {t : ℝ | R t x} := fun x => measurable_prodMk_right hR
  have hw : Measurable fun t : ℝ => ENNReal.ofReal (t ^ s) :=
    (measurable_id.pow measurable_const).ennreal_ofReal
  set G : ℝ × α → ℝ≥0∞ :=
    {z : ℝ × α | R z.1 z.2}.indicator (fun z => ENNReal.ofReal (z.1 ^ s) * g z.2) with hG
  have hGmeas : Measurable G :=
    (((measurable_fst.pow measurable_const).ennreal_ofReal).mul
      (hg.comp measurable_snd)).indicator hR
  -- The same cut-off reads as a condition on `x` for a fixed `t`, or as one on `t` for a fixed `x`;
  -- each `show` names the set whose indicator is being unfolded, which a bare `hx` leaves open.
  have hGx : ∀ (t : ℝ) (x : α), G (t, x) =
      ENNReal.ofReal (t ^ s) * {x | R t x}.indicator g x := by
    intro t x
    by_cases hx : R t x
    · rw [hG, Set.indicator_of_mem (show (t, x) ∈ {z : ℝ × α | R z.1 z.2} from hx),
        Set.indicator_of_mem (show x ∈ {x | R t x} from hx)]
    · rw [hG, Set.indicator_of_notMem (show (t, x) ∉ {z : ℝ × α | R z.1 z.2} from hx),
        Set.indicator_of_notMem (show x ∉ {x | R t x} from hx), mul_zero]
  have hGt : ∀ (t : ℝ) (x : α), G (t, x) =
      {t : ℝ | R t x}.indicator (fun t => ENNReal.ofReal (t ^ s)) t * g x := by
    intro t x
    by_cases hx : R t x
    · rw [hG, Set.indicator_of_mem (show (t, x) ∈ {z : ℝ × α | R z.1 z.2} from hx),
        Set.indicator_of_mem (show t ∈ {t : ℝ | R t x} from hx)]
    · rw [hG, Set.indicator_of_notMem (show (t, x) ∉ {z : ℝ × α | R z.1 z.2} from hx),
        Set.indicator_of_notMem (show t ∉ {t : ℝ | R t x} from hx), zero_mul]
  have hslice : ∀ t : ℝ, ∫⁻ x, G (t, x) ∂μ =
      ENNReal.ofReal (t ^ s) * ∫⁻ x in {x | R t x}, g x ∂μ := by
    intro t
    rw [← lintegral_indicator (hRx t), ← lintegral_const_mul _ (hg.indicator (hRx t))]
    exact lintegral_congr fun x => hGx t x
  have hinner : ∀ x : α, (∫⁻ t in Ioi (0 : ℝ), G (t, x)) =
      (∫⁻ t in Ioi (0 : ℝ),
        {t : ℝ | R t x}.indicator (fun t => ENNReal.ofReal (t ^ s)) t) * g x := by
    intro x
    rw [← lintegral_mul_const _ (hw.indicator (hRt x))]
    exact lintegral_congr fun t => hGt t x
  refine (lintegral_congr fun t => (hslice t).symm).trans ?_
  rw [lintegral_lintegral_swap (f := fun t x => G (t, x)) hGmeas.aemeasurable]
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
