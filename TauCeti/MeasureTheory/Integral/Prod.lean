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
* `TauCeti.integrable_left_of_mul_prod_of_ae_ne_zero`: integrability of a separated product whose
  right factor is nonzero almost everywhere implies integrability of its left factor.
* `TauCeti.exists_ae_eq_const_of_ae_prod_eq`: if `f x = g y` for almost every `(x, y)` in a product
  of nonzero measures, then `f` and `g` are almost everywhere the same constant. This is the
  uniqueness of a function of the form `f(x) + g(y)` up to one additive constant.
* `TauCeti.measurable_setLIntegral_of_measurableSet` proves measurability of a set integral whose
  truncating relation is jointly measurable.
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
* `TauCeti.integrable_and_integral_prod_le` deduces product-measure integrability and an integral
  bound for an a.e.-nonnegative kernel from a.e. slice integrability and an integrable slice
  majorant.
-/

public section

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

end TauCeti
