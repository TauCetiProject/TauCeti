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
* `TauCeti.setIntegral_eq_zero_of_forall_prod` is the binary-product specialization of the Dynkin
  (π-λ) step for Bochner integrals: a function whose integral vanishes on every measurable rectangle
  has vanishing integral on every measurable set. Rectangles are a π-system generating the product
  σ-algebra (`MeasureTheory.isPiSystem_prod`, `MeasureTheory.generateFrom_prod`), so this is the
  general `TauCeti.setIntegral_eq_zero_of_isPiSystem` instantiated at that π-system; the only work
  left here is extracting the whole-space hypothesis from the rectangle `univ ×ˢ univ`.
* `TauCeti.ae_eq_zero_of_marginal_eq_zero` transfers zeros of a nonnegative function's marginal
  to the function itself, almost everywhere on the product.
* `TauCeti.integrable_mul_marginal_weight` derives integrability of a weighted product function
  from integrability of its weighted marginal.
-/

public section

namespace TauCeti

open MeasureTheory MeasureTheory.Measure Set
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
conditioned on `s` and on `t` is at most `b`: conditioning confines each coordinate to its own set
almost surely, so the bound holds almost everywhere on the product. The sets need only be
null-measurable, and their measures may be zero or infinite: either case makes the corresponding
conditional measure zero. -/
theorem lintegral_cond_prod_le {s : Set α} {t : Set β} (hs : NullMeasurableSet s μ)
    (ht : NullMeasurableSet t ν) {f : α × β → ℝ≥0∞} {b : ℝ≥0∞}
    (hf : ∀ x ∈ s, ∀ y ∈ t, f (x, y) ≤ b) :
    ∫⁻ z, f z ∂((μ[|s]).prod (ν[|t])) ≤ b := by
  rcases eq_zero_or_isProbabilityMeasure (μ := μ[|s]) with hμ | hμ
  · simp [hμ]
  rcases eq_zero_or_isProbabilityMeasure (μ := ν[|t]) with hν | hν
  · simp [hν]
  refine lintegral_le_const ?_
  filter_upwards [ae_of_ae_fst (ν := ν[|t]) (ProbabilityTheory.ae_cond_mem₀ hs),
    ae_of_ae_snd (μ := μ[|s]) (ProbabilityTheory.ae_cond_mem₀ ht)] with ⟨x, y⟩ hx hy
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
  exact setIntegral_eq_zero_of_isPiSystem le_rfl generateFrom_prod.symm isPiSystem_prod hf huniv
    fun _ ⟨s, hs, t, ht, h⟩ => h ▸ hrect s hs t ht

/-- A nonnegative integrable function vanishes almost everywhere where its second marginal
vanishes. -/
theorem ae_eq_zero_of_marginal_eq_zero (μ : Measure α) (ν : Measure β)
    [SFinite μ] [SFinite ν] {g : α × β → ℝ}
    (hnonneg : 0 ≤ᵐ[μ.prod ν] g) (hg : Integrable g (μ.prod ν)) :
    ∀ᵐ p ∂μ.prod ν, (∫ x, g (x, p.2) ∂μ) = 0 → g p = 0 := by
  let b : β → ℝ := fun y ↦ ∫ x, g (x, y) ∂μ
  let gm := hg.aestronglyMeasurable.mk g
  let bm := hg.integral_prod_right.aestronglyMeasurable.mk b
  have hg_eq : g =ᵐ[μ.prod ν] gm := hg.aestronglyMeasurable.ae_eq_mk
  have hb_eq : b =ᵐ[ν] bm := hg.integral_prod_right.aestronglyMeasurable.ae_eq_mk
  have hswap : ∀ᵐ p ∂ν.prod μ, 0 ≤ g (p.2, p.1) :=
    measurePreserving_swap.quasiMeasurePreserving.ae hnonneg
  have hswap_eq : ∀ᵐ p ∂ν.prod μ, g (p.2, p.1) = gm (p.2, p.1) :=
    measurePreserving_swap.quasiMeasurePreserving.ae hg_eq
  have hreverse : ∀ᵐ y ∂ν, ∀ᵐ x ∂μ, bm y = 0 → gm (x, y) = 0 := by
    filter_upwards [ae_ae_of_ae_prod hswap, hg.prod_left_ae, hb_eq,
      ae_ae_of_ae_prod hswap_eq] with y hy hyi hby hgy
    by_cases hz : b y = 0
    · have hzero := (integral_eq_zero_iff_of_nonneg_ae hy hyi).mp hz
      filter_upwards [hzero, hgy] with x hx hx'
      intro _
      simpa only [Pi.zero_apply] using hx'.symm.trans hx
    · filter_upwards with x
      intro hbz
      exact False.elim (hz (hby.trans hbz))
  have hmeas : MeasurableSet {p : α × β | bm p.2 = 0 → gm p = 0} := by
    have hbm : Measurable bm :=
      hg.integral_prod_right.aestronglyMeasurable.stronglyMeasurable_mk.measurable
    have hgm : Measurable gm := hg.aestronglyMeasurable.stronglyMeasurable_mk.measurable
    exact (measurableSet_eq_fun (hbm.comp measurable_snd) measurable_const).imp
      (measurableSet_eq_fun hgm measurable_const)
  have hreverse_prod : ∀ᵐ p ∂ν.prod μ, bm p.1 = 0 → gm (p.2, p.1) = 0 :=
    (ae_prod_iff_ae_ae (measurable_swap hmeas)).2 hreverse
  have hforward : ∀ᵐ p ∂μ.prod ν, bm p.2 = 0 → gm p = 0 :=
    measurePreserving_swap.quasiMeasurePreserving.ae hreverse_prod
  have hb_prod : ∀ᵐ p ∂μ.prod ν, b p.2 = bm p.2 :=
    quasiMeasurePreserving_snd.ae hb_eq
  filter_upwards [hforward, hg_eq, hb_prod] with p hp hgp hbp
  intro hz
  exact hgp.trans (hp (hbp.symm.trans hz))

/-- A nonnegative integrable product function remains integrable when multiplied by a measurable
weight on the second factor, provided the weighted second marginal is integrable. -/
theorem integrable_mul_marginal_weight (μ : Measure α) (ν : Measure β)
    [SFinite μ] [SFinite ν] {g : α × β → ℝ} {w : β → ℝ}
    (hnonneg : 0 ≤ᵐ[μ.prod ν] g) (hg : Integrable g (μ.prod ν))
    (hw : AEMeasurable w ν)
    (hmarg : Integrable (fun y ↦ (∫ x, g (x, y) ∂μ) * w y) ν) :
    Integrable (fun p ↦ g p * w p.2) (μ.prod ν) := by
  let b : β → ℝ := fun y ↦ ∫ x, g (x, y) ∂μ
  have hmeas : AEStronglyMeasurable (fun p ↦ g p * w p.2) (μ.prod ν) :=
    hg.aestronglyMeasurable.mul
      (hw.aestronglyMeasurable.comp_quasiMeasurePreserving quasiMeasurePreserving_snd)
  apply (integrable_prod_iff' hmeas).2
  constructor
  · filter_upwards [hg.prod_left_ae] with y hy
    exact hy.mul_const _
  · have hswap : ∀ᵐ p ∂ν.prod μ, 0 ≤ g (p.2, p.1) :=
      measurePreserving_swap.quasiMeasurePreserving.ae hnonneg
    apply hmarg.norm.congr
    filter_upwards [ae_ae_of_ae_prod hswap] with y hy
    have hb : 0 ≤ b y := integral_nonneg_of_ae hy
    calc
      ‖b y * w y‖ = b y * ‖w y‖ := by
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hb]
      _ = ∫ x, g (x, y) * ‖w y‖ ∂μ := (integral_mul_const _ _).symm
      _ = ∫ x, ‖g (x, y) * w y‖ ∂μ := by
        apply integral_congr_ae
        filter_upwards [hy] with x hx
        simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg hx]

end TauCeti
