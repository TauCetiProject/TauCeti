/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Probability.ConditionalProbability
public import TauCeti.MeasureTheory.Integral.PiSystem
import TauCeti.MeasureTheory.Measure.Typeclasses.SFinite

/-!
# Product-measure helpers

Small pieces of product-measure theory with no `L²` or inner-product content.

* `TauCeti.ae_of_ae_fst` / `TauCeti.ae_of_ae_snd` transfer an a.e. statement about one factor to the
  product measure, along `Measure.quasiMeasurePreserving_fst` / `_snd`.
* `TauCeti.integrable_left_of_mul_prod_of_ae_ne_zero`: integrability of a separated product whose
  right factor is nonzero almost everywhere implies integrability of its left factor.
* `TauCeti.exists_ae_eq_const_of_ae_prod_eq`: if `f x = g y` for almost every `(x, y)` in a product
  of nonzero measures, then `f` and `g` are almost everywhere the same constant. This is the
  uniqueness of a function of the form `f(x) + g(y)` up to one additive constant.
* `TauCeti.measurable_setLIntegral_of_measurableSet` proves measurability of a set integral whose
  truncating relation is jointly measurable, and
  `TauCeti.aestronglyMeasurable_setIntegral_of_measurableSet` is its Bochner form for a jointly
  measurable integrand, such as the retarded Duhamel integral `t ↦ ∫_{s < t} K t s ds`.
* `TauCeti.lintegral_mul_setLIntegral_eq` exchanges a weighted integral of set integrals over an
  arbitrary parameter measure with the corresponding integral over the sections of the truncating
  relation.
* `TauCeti.lintegral_cond_prod_le` bounds a lower Lebesgue integral over a product of two
  conditional laws by any bound the integrand satisfies on the rectangle conditioned on. Use it to
  estimate an integral against two independently conditioned coordinates when the integrand is
  controlled only on the pair of sets being conditioned on.
* `TauCeti.abs_integral_prod_sub_integral_prod_le_of_ae`: if the integrals over the second factor
  differ by at most `C` for almost every point of a probability first factor, the integrals over
  the product measures differ by at most `C`.
* `TauCeti.integrable_prod_restrict_of_continuous`: a continuous function on `α × β` vanishing on
  `(α \ K) × D` for compact `K` and `D` is integrable for `μ × ν|_D`, the integrability needed to
  apply Fubini's theorem to a compactly supported integrand over a compact parameter set.
* `TauCeti.setIntegral_eq_zero_of_forall_prod` is the binary-product specialization of the Dynkin
  (π-λ) step for Bochner integrals: a function whose integral vanishes on every measurable rectangle
  has vanishing integral on every measurable set. Rectangles are a π-system generating the product
  σ-algebra (`MeasureTheory.isPiSystem_prod`, `MeasureTheory.generateFrom_prod`), so this is the
  general `TauCeti.setIntegral_eq_zero_of_isPiSystem` instantiated at that π-system; the only work
  left here is extracting the whole-space hypothesis from the rectangle `univ ×ˢ univ`.
* `TauCeti.enorm_integral_setIntegral_le_lintegral_lintegral` bounds an iterated integral
  truncated to a region `s ∈ S t` (such as `s < t`) by the iterated integral of the norm, as used
  to pass from bilinear to retarded estimates.
* `TauCeti.integral_setIntegral_Iio_eq_setIntegral` writes the iterated integral
  `∫ ∫_{s < t} f(s, t) ds dt` as the integral of `f` over the region `{(s, t) | s < t}`.
* `TauCeti.continuous_integral_of_hasCompactSupport_uncurry` and
  `TauCeti.hasCompactSupport_integral_of_hasCompactSupport_uncurry`: integrating a continuous
  compactly supported function of `(x, y)` in `y` gives a continuous compactly supported function
  of `x`.
* `TauCeti.integrable_and_integral_prod_le` deduces product-measure integrability and an integral
  bound for an a.e.-nonnegative kernel from a.e. slice integrability and an integrable slice
  majorant.
* `TauCeti.mul_integral_le_integral_prod_of_forall` integrates a slicewise lower bound
  `c F x ≤ ∫ g (x, y) dy` over the first factor: `c ∫ F ≤ ∫ g` over the product measure.
* `MeasureTheory.StronglyMeasurable.fubini_of_countable_rectangles` gives Fubini for arbitrary
  measures when the integrand is supported on countably many finite-measure rectangles.
  The supporting sets need not be measurable. The extended norm integral condition ensures
  that divergent sections cannot be hidden by the default value of the Bochner integral.
* `TauCeti.ae_eq_zero_prod_of_forall_integral_mul_eq_zero`: completeness passes from a countable
  complete system in the first variable of a product to the whole product, slice by slice.

## Fubini on sigma-finite supports

The support-localized results apply Mathlib's `lintegral_prod` and `integral_integral_swap`
to the restricted measures. They do not use the ambient native product measure, which is
defined to be zero when the second measure is not s-finite.

### References

* T. Hytönen, J. van Neerven, M. Veraar and L. Weis, *Analysis in Banach Spaces*,
  Volume I, §1.2, Remark 1.2.8.

-/

public section

namespace MeasureTheory

/-- Integrating a function of the first coordinate against a difference between the two
coordinates subtracts the product of their separate means. -/
theorem integral_mul_sub_comp_prod_eq_sub {α : Type*} [MeasurableSpace α]
    {μ ν : Measure α} [SFinite μ] [IsProbabilityMeasure ν] {f u : α → ℝ}
    (hf : Integrable f μ) (hu : Integrable u ν) (hfu : Integrable (fun x ↦ f x * u x) μ) :
    ∫ p : α × α, f p.1 * (u p.1 - u p.2) ∂μ.prod ν =
      (∫ x, f x * u x ∂μ) - (∫ x, f x ∂μ) * ∫ x, u x ∂ν := by
  have hfst : ∫ p : α × α, f p.1 * u p.1 ∂μ.prod ν = ∫ x, f x * u x ∂μ := by
    simpa only [mul_one, integral_const, probReal_univ, smul_eq_mul, one_mul] using
      (integral_prod_mul (μ := μ) (ν := ν) (fun x ↦ f x * u x) (fun _ ↦ (1 : ℝ)))
  simp_rw [mul_sub]
  rw [integral_sub (hfu.comp_fst ν) (hf.mul_prod hu), hfst, integral_prod_mul]

end MeasureTheory

namespace TauCeti

open MeasureTheory Set
open scoped ENNReal ProbabilityTheory

variable {α β γ E : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} {μ : Measure α} {ν : Measure β} {κ : Measure γ}
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The truncated integral `t ↦ ∫⁻ x in {x | R t x}, g x ∂μ` of an a.e.-measurable integrand is
measurable when the truncating relation is jointly measurable. -/
theorem measurable_setLIntegral_of_measurableSet [SFinite μ] {g : α → ℝ≥0∞}
    {R : γ → α → Prop} (hR : MeasurableSet {z : γ × α | R z.1 z.2})
    (hg : AEMeasurable g μ) :
    Measurable fun t => ∫⁻ x in {x | R t x}, g x ∂μ := by
  let g' := hg.mk g
  have hRx : ∀ t : γ, MeasurableSet {x | R t x} := fun t => measurable_prodMk_left hR
  have heq : (fun t => ∫⁻ x in {x | R t x}, g x ∂μ) =
      fun t => ∫⁻ x in {x | R t x}, g' x ∂μ := by
    funext t
    exact lintegral_congr_ae (ae_restrict_of_ae hg.ae_eq_mk)
  rw [heq]
  have hind : ∀ t : γ, ∫⁻ x in {x | R t x}, g' x ∂μ =
      ∫⁻ x, {z : γ × α | R z.1 z.2}.indicator (fun z => g' z.2) (t, x) ∂μ := by
    intro t
    rw [← lintegral_indicator (hRx t)]
    rfl
  simp_rw [hind]
  exact ((hg.measurable_mk.comp measurable_snd).indicator hR).lintegral_prod_right'

/-- The truncated integral `t ↦ ∫ x in {x | R t x}, K t x ∂μ` of an integrand that is almost
everywhere strongly measurable for `κ.prod μ` is almost everywhere strongly measurable when the
truncating relation is jointly measurable. With `R t s := s < t` this is the retarded integral
`t ↦ ∫_{s < t} K t s ds`. Where the integral does not exist it takes the value `0`. -/
theorem aestronglyMeasurable_setIntegral_of_measurableSet [SFinite μ] {K : γ → α → E}
    (hK : AEStronglyMeasurable (Function.uncurry K) (κ.prod μ))
    {R : γ → α → Prop} (hR : MeasurableSet {z : γ × α | R z.1 z.2}) :
    AEStronglyMeasurable (fun t ↦ ∫ x in {x | R t x}, K t x ∂μ) κ := by
  refine (hK.indicator hR).integral_prod_right'.congr (ae_of_all _ fun t ↦ ?_)
  dsimp only
  have hRt : MeasurableSet {x | R t x} := measurable_prodMk_left hR
  rw [← integral_indicator hRt]
  refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  by_cases h : R t x <;> simp [Set.indicator, h]

/-- **Tonelli for a weighted integral of truncated integrals.** For a jointly measurable
truncating relation `R` and a.e.-measurable integrand and weight, integrating first in `x` and then
against the parameter measure gives the same value as integrating the weight over each parameter
section and then in `x`. -/
theorem lintegral_mul_setLIntegral_eq [SFinite μ] [SFinite κ] {g : α → ℝ≥0∞} {w : γ → ℝ≥0∞}
    {R : γ → α → Prop} (hR : MeasurableSet {z : γ × α | R z.1 z.2})
    (hg : AEMeasurable g μ) (hw : AEMeasurable w κ) :
    ∫⁻ t, w t * ∫⁻ x in {x | R t x}, g x ∂μ ∂κ =
      ∫⁻ x, (∫⁻ t, {t : γ | R t x}.indicator w t ∂κ) * g x ∂μ := by
  let g' := hg.mk g
  let w' := hw.mk w
  have hRx : ∀ t : γ, MeasurableSet {x | R t x} := fun t => measurable_prodMk_left hR
  have hRt : ∀ x : α, MeasurableSet {t : γ | R t x} := fun x => measurable_prodMk_right hR
  set G : γ × α → ℝ≥0∞ :=
    {z : γ × α | R z.1 z.2}.indicator (fun z => w' z.1 * g' z.2) with hG
  have hGmeas : Measurable G :=
    ((hw.measurable_mk.comp measurable_fst).mul
      (hg.measurable_mk.comp measurable_snd)).indicator hR
  -- The same cut-off reads as a condition on `x` for a fixed `t`, or as one on `t` for a fixed `x`;
  -- each `show` names the set whose indicator is being unfolded, which a bare `hx` leaves open.
  have hGx : ∀ (t : γ) (x : α), G (t, x) = w' t * {x | R t x}.indicator g' x := by
    intro t x
    by_cases hx : R t x
    · rw [hG, Set.indicator_of_mem (show (t, x) ∈ {z : γ × α | R z.1 z.2} from hx),
        Set.indicator_of_mem (show x ∈ {x | R t x} from hx)]
    · rw [hG, Set.indicator_of_notMem (show (t, x) ∉ {z : γ × α | R z.1 z.2} from hx),
        Set.indicator_of_notMem (show x ∉ {x | R t x} from hx), mul_zero]
  have hGt : ∀ (t : γ) (x : α), G (t, x) = {t : γ | R t x}.indicator w' t * g' x := by
    intro t x
    by_cases hx : R t x
    · rw [hG, Set.indicator_of_mem (show (t, x) ∈ {z : γ × α | R z.1 z.2} from hx),
        Set.indicator_of_mem (show t ∈ {t : γ | R t x} from hx)]
    · rw [hG, Set.indicator_of_notMem (show (t, x) ∉ {z : γ × α | R z.1 z.2} from hx),
        Set.indicator_of_notMem (show t ∉ {t : γ | R t x} from hx), zero_mul]
  have hslice : ∀ t : γ, ∫⁻ x, G (t, x) ∂μ = w' t * ∫⁻ x in {x | R t x}, g' x ∂μ := by
    intro t
    rw [← lintegral_indicator (hRx t),
      ← lintegral_const_mul _ (hg.measurable_mk.indicator (hRx t))]
    exact lintegral_congr fun x => hGx t x
  have hinner : ∀ x : α, (∫⁻ t, G (t, x) ∂κ) =
      (∫⁻ t, {t : γ | R t x}.indicator w' t ∂κ) * g' x := by
    intro x
    rw [← lintegral_mul_const _ (hw.measurable_mk.indicator (hRt x))]
    exact lintegral_congr fun t => hGt t x
  calc
    ∫⁻ t, w t * ∫⁻ x in {x | R t x}, g x ∂μ ∂κ =
        ∫⁻ t, w' t * ∫⁻ x in {x | R t x}, g' x ∂μ ∂κ := by
      refine lintegral_congr_ae ?_
      filter_upwards [hw.ae_eq_mk] with t ht
      exact congrArg₂ (fun a b : ℝ≥0∞ => a * b) ht
        (lintegral_congr_ae (ae_restrict_of_ae hg.ae_eq_mk))
    _ = ∫⁻ t, ∫⁻ x, G (t, x) ∂μ ∂κ := lintegral_congr fun t => (hslice t).symm
    _ = ∫⁻ x, ∫⁻ t, G (t, x) ∂κ ∂μ :=
      lintegral_lintegral_swap (μ := κ) (ν := μ) (f := fun t x => G (t, x))
        hGmeas.aemeasurable
    _ = ∫⁻ x, (∫⁻ t, {t : γ | R t x}.indicator w' t ∂κ) * g' x ∂μ :=
      lintegral_congr hinner
    _ = ∫⁻ x, (∫⁻ t, {t : γ | R t x}.indicator w t ∂κ) * g x ∂μ := by
      refine lintegral_congr_ae ?_
      filter_upwards [hg.ae_eq_mk] with x hx
      exact congrArg₂ (fun a b : ℝ≥0∞ => a * b)
        (lintegral_congr_ae (hw.ae_eq_mk.mono fun t ht => by
          by_cases htx : R t x <;> simp [htx, ht, w'])).symm hx.symm

/-- An a.e. statement on the first factor transfers to the product measure. -/
theorem ae_of_ae_fst {p : α → Prop} (hp : ∀ᵐ x ∂μ, p x) :
    ∀ᵐ q : α × β ∂(μ.prod ν), p q.1 :=
  Measure.quasiMeasurePreserving_fst.tendsto_ae.eventually hp

/-- An a.e. statement on the second factor transfers to the product measure. -/
theorem ae_of_ae_snd {p : β → Prop} (hp : ∀ᵐ y ∂ν, p y) :
    ∀ᵐ q : α × β ∂(μ.prod ν), p q.2 :=
  Measure.quasiMeasurePreserving_snd.tendsto_ae.eventually hp

/-- If a separated product `f x * g y` is integrable and `g` is nonzero almost everywhere
under a nonzero s-finite measure, then `f` is integrable. -/
theorem integrable_left_of_mul_prod_of_ae_ne_zero [SFinite μ] [SFinite ν] [NeZero ν]
    {L : Type*} [NormedDivisionRing L] {f : α → L} {g : β → L}
    (hfg : Integrable (fun z ↦ f z.1 * g z.2) (μ.prod ν))
    (hg : ∀ᵐ y ∂ν, g y ≠ 0) : Integrable f μ := by
  obtain ⟨y, hgy, hy⟩ := (hg.and hfg.prod_left_ae).exists
  exact (integrable_mul_const_iff (isUnit_iff_ne_zero.2 hgy) f).1 hy

/-- If `f x = g y` for `μ.prod ν`-almost every `(x, y)`, with both measures nonzero, then `f` and
`g` are almost everywhere equal to one and the same constant. -/
theorem exists_ae_eq_const_of_ae_prod_eq [SFinite ν] {δ : Type*} {f : α → δ} {g : β → δ}
    (hμ : μ ≠ 0) (hν : ν ≠ 0) (h : ∀ᵐ z ∂μ.prod ν, f z.1 = g z.2) :
    ∃ c, f =ᵐ[μ] (fun _ ↦ c) ∧ g =ᵐ[ν] (fun _ ↦ c) := by
  have h' := Measure.ae_ae_of_ae_prod h
  have : (ae μ).NeBot := ae_neBot.2 hμ
  have : (ae ν).NeBot := ae_neBot.2 hν
  obtain ⟨x₀, hx₀⟩ := h'.exists
  refine ⟨f x₀, ?_, hx₀.mono fun _ hy ↦ hy.symm⟩
  filter_upwards [h'] with x hx
  obtain ⟨y, hxy, hx₀y⟩ := (hx.and hx₀).exists
  rw [hxy, hx₀y]

/-- **A rectangle bound for an integral against a product of conditional laws.** If `f` is bounded
by `b` on `s ×ˢ t`, then its lower Lebesgue integral against the product of the laws of `μ` and `ν`
conditioned on `s` and on `t` is at most `b`. The sets need not be measurable, and their measures
may be zero or infinite: either case makes the corresponding conditional measure zero. Arbitrary
conditioning sets need not carry full conditional measure in the almost-everywhere sense, so the
bound is on the lower integral and not an almost-everywhere bound for `f` itself. -/
theorem lintegral_cond_prod_le {s : Set α} {t : Set β} {f : α × β → ℝ≥0∞} {b : ℝ≥0∞}
    (hf : ∀ x ∈ s, ∀ y ∈ t, f (x, y) ≤ b) :
    ∫⁻ z, f z ∂((μ[|s]).prod (ν[|t])) ≤ b := by
  rcases eq_zero_or_isProbabilityMeasure (μ := μ[|s]) with hμ | hμ
  · simp [hμ]
  rcases eq_zero_or_isProbabilityMeasure (μ := ν[|t]) with hν | hν
  · simp [hν]
  -- Pass to a measurable minorant `g ≤ f` with the same integral: the set `{b < g}` is measurable,
  -- and each of its sections at a point of `s` misses `t`, hence is null for the conditional law
  -- of `ν`, so the set is null for the product.
  obtain ⟨g, hgm, hgf, hg⟩ := exists_measurable_le_lintegral_eq (μ := (μ[|s]).prod (ν[|t])) f
  rw [hg]
  refine lintegral_le_const ?_
  have hA : MeasurableSet {z : α × β | b < g z} := measurableSet_lt measurable_const hgm
  have hsec : ∀ x ∈ s, ν[|t] (Prod.mk x ⁻¹' {z : α × β | b < g z}) = 0 := fun x hx => by
    have hm : MeasurableSet (Prod.mk x ⁻¹' {z : α × β | b < g z}) := measurable_prodMk_left hA
    rw [ProbabilityTheory.cond, smul_apply, Measure.restrict_apply hm]
    have : Prod.mk x ⁻¹' {z : α × β | b < g z} ∩ t = ∅ := Set.eq_empty_of_forall_notMem fun y hy =>
      absurd (hy.1.trans_le ((hgf _).trans (hf x hx y hy.2))) (lt_irrefl _)
    rw [this]
    simp
  have hφ : Measurable fun x => ν[|t] (Prod.mk x ⁻¹' {z : α × β | b < g z}) :=
    measurable_measure_prodMk_left hA
  have hB : MeasurableSet {x | ν[|t] (Prod.mk x ⁻¹' {z : α × β | b < g z}) ≠ 0} :=
    hφ (measurableSet_singleton (0 : ℝ≥0∞)).compl
  have hnull : (μ[|s]) {x | ν[|t] (Prod.mk x ⁻¹' {z : α × β | b < g z}) ≠ 0} = 0 := by
    rw [ProbabilityTheory.cond, smul_apply, Measure.restrict_apply hB]
    have : {x | ν[|t] (Prod.mk x ⁻¹' {z : α × β | b < g z}) ≠ 0} ∩ s = ∅ :=
      Set.eq_empty_of_forall_notMem fun x hx => hx.1 (hsec x hx.2)
    rw [this]
    simp
  have hprod : ((μ[|s]).prod (ν[|t])) {z : α × β | b < g z} = 0 :=
    (Measure.measure_prod_null hA).2 hnull
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hprod] with z hz using not_lt.1 hz

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
  exact setIntegral_eq_zero_of_isPiSystem le_rfl generateFrom_prod.symm isPiSystem_prod hf huniv
    fun _ ⟨s, hs, t, ht, h⟩ => h ▸ hrect s hs t ht

/-- If two integrals over the second factor of a product measure with a probability first factor
differ by at most `C` for almost every point of the first factor, then the two integrals over the
product measures differ by at most `C`. -/
theorem abs_integral_prod_sub_integral_prod_le_of_ae {ρ : Measure α} [IsProbabilityMeasure ρ]
    {κ₁ κ₂ : Measure β} [SFinite κ₁] [SFinite κ₂] {F : α × β → ℝ} {C : ℝ}
    (h₁ : Integrable F (ρ.prod κ₁)) (h₂ : Integrable F (ρ.prod κ₂))
    (h : ∀ᵐ t ∂ρ, |∫ w, F (t, w) ∂κ₁ - ∫ w, F (t, w) ∂κ₂| ≤ C) :
    |∫ p, F p ∂(ρ.prod κ₁) - ∫ p, F p ∂(ρ.prod κ₂)| ≤ C := by
  rw [integral_prod _ h₁, integral_prod _ h₂,
    ← integral_sub h₁.integral_prod_left h₂.integral_prod_left, ← Real.norm_eq_abs]
  exact le_trans (norm_integral_le_of_norm_le_const (C := C)
    (by simpa only [Real.norm_eq_abs] using h)) (by simp)

omit [NormedSpace ℝ E] in
/-- A continuous function on `α × β` that vanishes on `(α \ K) × D`, for compact sets `K` and
`D`, is integrable for `μ × ν|_D`. -/
theorem integrable_prod_restrict_of_continuous [TopologicalSpace α] [TopologicalSpace β]
    [T2Space α] [T2Space β] [OpensMeasurableSpace β] [OpensMeasurableSpace (α × β)]
    [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν] [SFinite μ] [SFinite ν]
    {G : α × β → E} (hG : Continuous G) {K : Set α} {D : Set β} (hK : IsCompact K)
    (hD : IsCompact D)
    (hGK : ∀ x y, y ∈ D → x ∉ K → G (x, y) = 0) : Integrable G (μ.prod (ν.restrict D)) := by
  rw [← Measure.restrict_univ (μ := μ), Measure.prod_restrict]
  refine IntegrableOn.of_forall_sdiff_eq_zero (hG.continuousOn.integrableOn_compact (hK.prod hD))
    (MeasurableSet.univ.prod hD.measurableSet) fun q hq ↦ ?_
  exact hGK q.1 q.2 hq.1.2 fun h ↦ hq.2 ⟨h, hq.1.2⟩

/-- If an almost everywhere nonnegative measurable function `G : α × β → ℝ` has integrable
`ν`-slices bounded above by an integrable majorant `H : α → ℝ` for `μ`-almost every `x`, then `G`
is integrable on `μ.prod ν` and its product integral is at most `∫ x, H x ∂μ`. -/
theorem integrable_and_integral_prod_le [SFinite μ] [SFinite ν] {G : α × β → ℝ}
    (hG_meas : AEStronglyMeasurable G (μ.prod ν)) (hG_nn : 0 ≤ᵐ[μ.prod ν] G)
    {H : α → ℝ} (hH_int : Integrable H μ)
    (hslice : ∀ᵐ x ∂μ, Integrable (fun y ↦ G (x, y)) ν ∧ ∫ y, G (x, y) ∂ν ≤ H x) :
    Integrable G (μ.prod ν) ∧ ∫ p, G p ∂(μ.prod ν) ≤ ∫ x, H x ∂μ := by
  have hG_int : Integrable G (μ.prod ν) := by
    rw [integrable_prod_iff hG_meas]
    refine ⟨hslice.mono fun _ h ↦ h.1, hH_int.mono' hG_meas.norm.integral_prod_right' ?_⟩
    filter_upwards [Measure.ae_ae_of_ae_prod hG_nn, hslice] with x hx h
    rw [Real.norm_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _),
      integral_congr_ae (hx.mono fun _ hy ↦ Real.norm_of_nonneg hy)]
    exact h.2
  exact ⟨hG_int, (integral_prod G hG_int).trans_le
    (integral_mono_ae hG_int.integral_prod_left hH_int (hslice.mono fun _ h ↦ h.2))⟩

/-- Integrating a slicewise lower bound `c F x ≤ ∫ g (x, y) dy` over the first factor gives
`c ∫ F ≤ ∫ g` over the product measure. -/
theorem mul_integral_le_integral_prod_of_forall [SFinite μ] [SFinite ν] {F : α → ℝ}
    {g : α × β → ℝ} {c : ℝ} (hF : Integrable F μ) (hg : Integrable g (μ.prod ν))
    (h : ∀ x, c * F x ≤ ∫ y, g (x, y) ∂ν) :
    c * ∫ x, F x ∂μ ≤ ∫ p, g p ∂μ.prod ν := by
  rw [integral_prod _ hg, ← integral_const_mul]
  exact integral_mono (hF.const_mul c) hg.integral_prod_left h

/-- The integral of `f s t` over a region `{(s, t) | s ∈ S t}` is bounded by the iterated
integral of `‖f s t‖`: `|∫ ∫_{s ∈ S t} f s t ds dt| ≤ ∫∫ |f s t| ds dt`.

With `f s t` a Duhamel pairing and `S = Iio`, this passes from a bilinear estimate to retarded
estimates. -/
theorem enorm_integral_setIntegral_le_lintegral_lintegral {S : α → Set β} {ρ : Measure β}
    (f : β → α → E) :
    ‖∫ t, ∫ s in S t, f s t ∂ρ ∂μ‖ₑ ≤ ∫⁻ t, ∫⁻ s, ‖f s t‖ₑ ∂ρ ∂μ :=
  calc _ ≤ ∫⁻ t, ‖∫ s in S t, f s t ∂ρ‖ₑ ∂μ := eNorm_integral_le_lintegral_eNorm _
    _ ≤ ∫⁻ t, ∫⁻ s in S t, ‖f s t‖ₑ ∂ρ ∂μ :=
        lintegral_mono fun _ ↦ eNorm_integral_le_lintegral_eNorm _
    _ ≤ _ := lintegral_mono fun _ ↦ setLIntegral_le_lintegral _ _

/-- The iterated integral `∫ ∫_{s < t} f(s, t) ds dt` of a function integrable on the region
`{(s, t) | s < t}` is its integral over that region. -/
theorem integral_setIntegral_Iio_eq_setIntegral {μ ν : Measure ℝ} [SFinite μ] [SFinite ν]
    {f : ℝ × ℝ → E} (hf : IntegrableOn f {z : ℝ × ℝ | z.1 < z.2} (μ.prod ν)) :
    ∫ t, ∫ s in Iio t, f (s, t) ∂μ ∂ν = ∫ z in {z : ℝ × ℝ | z.1 < z.2}, f z ∂(μ.prod ν) := by
  have hmeas : MeasurableSet {z : ℝ × ℝ | z.1 < z.2} :=
    measurableSet_lt measurable_fst measurable_snd
  rw [← integral_indicator hmeas, integral_prod_symm _ ((integrable_indicator_iff hmeas).2 hf)]
  refine integral_congr_ae (.of_forall fun t ↦ ?_)
  dsimp only
  rw [← integral_indicator measurableSet_Iio]
  exact integral_congr_ae (.of_forall fun s ↦ by simp [Set.indicator_apply])

/-- **Completeness in the first variable of a product.** Let `e k`, `k ∈ ι` countable, be a
complete system for `μ`: an integrable function orthogonal to every `e k` vanishes almost
everywhere. If `G` is integrable on `μ × ν` and for every `k` the coefficient
`y ↦ ∫ G (t, y) e k t dμ(t)` vanishes for almost every `y`, then `G` vanishes almost everywhere.
For almost every `y` the slice `G (·, y)` is integrable and orthogonal to every `e k`, so it
vanishes, and Tonelli concludes. This is how completeness passes from a system on an interval to
the separated systems on a product of intervals. -/
theorem ae_eq_zero_prod_of_forall_integral_mul_eq_zero {ι : Type*} [Countable ι] [SFinite μ]
    [SFinite ν] {e : ι → α → ℝ}
    (he : ∀ g : α → ℝ, Integrable g μ → (∀ k, ∫ t, g t * e k t ∂μ = 0) → g =ᵐ[μ] 0)
    {G : α × β → ℝ} (hG : Integrable G (μ.prod ν))
    (h : ∀ k, (fun y => ∫ t, G (t, y) * e k t ∂μ) =ᵐ[ν] 0) :
    G =ᵐ[μ.prod ν] 0 := by
  have hslice : ∀ᵐ y ∂ν, (fun t => G (t, y)) =ᵐ[μ] 0 := by
    filter_upwards [ae_all_iff.2 h, hG.prod_left_ae] with y hy hyi
    exact he _ hyi hy
  have hlin : ∫⁻ z, ‖G z‖ₑ ∂μ.prod ν = 0 := by
    rw [lintegral_prod_symm _ hG.aestronglyMeasurable.eNorm]
    refine lintegral_eq_zero_of_ae_eq_zero ?_
    filter_upwards [hslice] with y hy
    exact lintegral_eq_zero_of_ae_eq_zero (by filter_upwards [hy] with t ht; simp [ht])
  filter_upwards [(lintegral_eq_zero_iff' hG.aestronglyMeasurable.eNorm).1 hlin] with z hz
  simpa using hz

section CompactSupport

variable [TopologicalSpace α] [TopologicalSpace β] {f : β → α → E}

/-- Integrating a compactly supported function of `(x, y)` in `y` gives a compactly supported
function of `x`. -/
theorem hasCompactSupport_integral_of_hasCompactSupport_uncurry [R1Space β]
    (hf : HasCompactSupport (Function.uncurry f)) : HasCompactSupport fun x ↦ ∫ y, f x y ∂μ := by
  refine HasCompactSupport.intro (hf.image continuous_fst) fun x hx ↦ ?_
  have h (y : α) : f x y = 0 :=
    image_eq_zero_of_notMem_tsupport (f := Function.uncurry f) fun h ↦ hx ⟨(x, y), h, rfl⟩
  simp [h]

/-- **Parametric integrals of compactly supported functions are continuous.** Integrating a
continuous compactly supported function of `(x, y)` in `y`, against a locally finite measure,
gives a continuous function of `x`. -/
theorem continuous_integral_of_hasCompactSupport_uncurry [OpensMeasurableSpace α]
    [FirstCountableTopology β] [LocallyCompactSpace β] [SecondCountableTopologyEither α E]
    [IsLocallyFiniteMeasure μ] (hf : Continuous (Function.uncurry f))
    (hfc : HasCompactSupport (Function.uncurry f)) : Continuous fun x ↦ ∫ y, f x y ∂μ := by
  -- Each slice vanishes off the compact projection of the support to the second factor.
  have hset (x : β) : ∫ y in Prod.snd '' tsupport (Function.uncurry f), f x y ∂μ = ∫ y, f x y ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦
      image_eq_zero_of_notMem_tsupport (f := Function.uncurry f) fun h ↦ hy ⟨(x, y), h, rfl⟩
  simp_rw [← hset]
  exact continuous_parametric_integral_of_continuous hf (hfc.image continuous_snd)

end CompactSupport

end TauCeti

section LocalizedFubini

open MeasureTheory Set Function Filter
open scoped ENNReal

namespace MeasureTheory.Integrable

variable {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup E] {μ : Measure α} {ν : Measure β}
    {s : Set α} {t : Set β} {f : α × β → E}

/-- Integrability on a supporting rectangle gives integrability of almost every ambient
section, even when the ambient measures are not s-finite. -/
theorem prod_right_ae_of_support_subset [SFinite (ν.restrict t)]
    (hf : Integrable f ((μ.restrict s).prod (ν.restrict t)))
    (hfs : support f ⊆ s ×ˢ t) :
    ∀ᵐ x ∂μ, Integrable (fun y ↦ f (x, y)) ν := by
  have hzero : ∀ z, z ∉ s ×ˢ t → f z = 0 := support_subset_iff'.1 hfs
  filter_upwards [ae_imp_of_ae_restrict
    ((integrable_prod_iff hf.aestronglyMeasurable).mp hf).1] with x hx
  by_cases hxs : x ∈ s
  · exact IntegrableOn.integrable_of_forall_notMem_eq_zero (hx hxs) fun y hy ↦
      hzero (x, y) (fun h ↦ hy h.2)
  · simp [fun y ↦ hzero (x, y) (fun h ↦ hxs h.1)]

/-- The integral of the ambient sections is integrable when the integrand is integrable
on a supporting rectangle with s-finite restricted measures. -/
theorem integral_prod_left_of_support_subset [NormedSpace ℝ E]
    [SFinite (ν.restrict t)]
    (hf : Integrable f ((μ.restrict s).prod (ν.restrict t)))
    (hfs : support f ⊆ s ×ˢ t) : Integrable (fun x ↦ ∫ y, f (x, y) ∂ν) μ := by
  have hzero : ∀ z, z ∉ s ×ˢ t → f z = 0 := support_subset_iff'.1 hfs
  have hinner (x : α) : ∫ y in t, f (x, y) ∂ν = ∫ y, f (x, y) ∂ν :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦
      hzero (x, y) (fun h ↦ hy h.2)
  have h := hf.integral_prod_left
  simp_rw [hinner] at h
  exact IntegrableOn.integrable_of_forall_notMem_eq_zero h fun x hx ↦ by
    simp [fun y ↦ hzero (x, y) (fun h ↦ hx h.1)]

end MeasureTheory.Integrable

namespace TauCeti

variable {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {s : Set α} {t : Set β}

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Fubini's formula on a supporting rectangle, expressed using ambient iterated integrals.
Only the restrictions to the supporting sets need be s-finite. -/
theorem integral_integral_swap_of_support_subset {f : α × β → E}
    (hfs : support f ⊆ s ×ˢ t) [SFinite (μ.restrict s)] [SFinite (ν.restrict t)]
    (hf : Integrable f ((μ.restrict s).prod (ν.restrict t))) :
    ∫ x, ∫ y, f (x, y) ∂ν ∂μ = ∫ y, ∫ x, f (x, y) ∂μ ∂ν := by
  have hzero : ∀ z, z ∉ s ×ˢ t → f z = 0 := support_subset_iff'.1 hfs
  have hright (x : α) : ∫ y in t, f (x, y) ∂ν = ∫ y, f (x, y) ∂ν :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦
      hzero (x, y) (fun h ↦ hy h.2)
  have hleft (y : β) : ∫ x in s, f (x, y) ∂μ = ∫ x, f (x, y) ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦
      hzero (x, y) (fun h ↦ hx h.1)
  have houter_right : ∀ x, x ∉ s → (∫ y, f (x, y) ∂ν) = 0 := by
    intro x hx
    simp [fun y ↦ hzero (x, y) (fun h ↦ hx h.1)]
  have houter_left : ∀ y, y ∉ t → (∫ x, f (x, y) ∂μ) = 0 := by
    intro y hy
    simp [fun x ↦ hzero (x, y) (fun h ↦ hy h.2)]
  have h := integral_integral_swap (f := fun x y ↦ f (x, y)) hf
  simp_rw [hright, hleft] at h
  simpa only [setIntegral_eq_integral_of_forall_compl_eq_zero houter_right,
    setIntegral_eq_integral_of_forall_compl_eq_zero houter_left] using h

/-- Localized Fubini for arbitrary measures with countable finite-measure rectangle support.
The supporting sets need not be measurable. Finiteness of either iterated extended norm
integral gives integrable sections almost everywhere, integrable section integrals in both
orders, and equality of the iterated Bochner integrals. -/
theorem _root_.MeasureTheory.StronglyMeasurable.fubini_of_countable_rectangles
    {f : α × β → E} (hf : StronglyMeasurable f)
    (s : ℕ → Set α) (t : ℕ → Set β)
    (hμ : ∀ n, μ (s n) < ∞) (hν : ∀ n, ν (t n) < ∞)
    (hfs : support f ⊆ ⋃ n, s n ×ˢ t n)
    (hfin : (∫⁻ x, ∫⁻ y, ‖f (x, y)‖ₑ ∂ν ∂μ < ∞) ∨
      (∫⁻ y, ∫⁻ x, ‖f (x, y)‖ₑ ∂μ ∂ν < ∞)) :
    (∀ᵐ x ∂μ, Integrable (fun y ↦ f (x, y)) ν) ∧
      (∀ᵐ y ∂ν, Integrable (fun x ↦ f (x, y)) μ) ∧
      Integrable (fun x ↦ ∫ y, f (x, y) ∂ν) μ ∧
      Integrable (fun y ↦ ∫ x, f (x, y) ∂μ) ν ∧
      (∫ x, ∫ y, f (x, y) ∂ν ∂μ) = ∫ y, ∫ x, f (x, y) ∂μ ∂ν := by
  let S := fun n ↦ toMeasurable μ (s n)
  let T := fun n ↦ toMeasurable ν (t n)
  let := μ.sigmaFinite_restrict_iUnion S fun n ↦ (measure_toMeasurable (s n)).trans_lt (hμ n)
  let := ν.sigmaFinite_restrict_iUnion T fun n ↦ (measure_toMeasurable (t n)).trans_lt (hν n)
  have hsupport : support f ⊆ (⋃ n, S n) ×ˢ (⋃ n, T n) := by
    intro z hz
    obtain ⟨n, hn⟩ := mem_iUnion.1 (hfs hz)
    exact ⟨mem_iUnion.2 ⟨n, subset_toMeasurable μ (s n) hn.1⟩,
      mem_iUnion.2 ⟨n, subset_toMeasurable ν (t n) hn.2⟩⟩
  have hI : Integrable f ((μ.restrict (⋃ n, S n)).prod (ν.restrict (⋃ n, T n))) := by
    refine ⟨hf.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_eNorm]
    rcases hfin with hfin | hfin
    · rw [lintegral_prod _ hf.eNorm.aemeasurable]
      exact lt_of_le_of_lt ((setLIntegral_le_lintegral _ _).trans
        (lintegral_mono fun x ↦ setLIntegral_le_lintegral _ _)) hfin
    · rw [lintegral_prod_symm _ hf.eNorm.aemeasurable]
      exact lt_of_le_of_lt ((setLIntegral_le_lintegral _ _).trans
        (lintegral_mono fun y ↦ setLIntegral_le_lintegral _ _)) hfin
  have hswap : support (f ∘ Prod.swap) ⊆ (⋃ n, T n) ×ˢ (⋃ n, S n) := by
    intro z hz
    exact ⟨(hsupport hz).2, (hsupport hz).1⟩
  exact ⟨hI.prod_right_ae_of_support_subset hsupport,
    hI.swap.prod_right_ae_of_support_subset hswap,
    hI.integral_prod_left_of_support_subset hsupport,
    hI.swap.integral_prod_left_of_support_subset hswap,
    integral_integral_swap_of_support_subset hsupport hI⟩

end TauCeti

end LocalizedFubini
