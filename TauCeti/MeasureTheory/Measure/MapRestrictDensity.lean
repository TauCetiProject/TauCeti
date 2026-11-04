/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import TauCeti.MeasureTheory.Measure.AEMeasurable

/-!
# The density of a set upstairs, seen on the base of a measure-preserving map

Let `f : Ω' → Ω` push a measure `ν` forward to a measure below a σ-finite measure `μ` (for
instance, `f` is measure-preserving from `ν` to `μ`), and let `s ⊆ Ω'` be a set upstairs.
The part of `ν` carried by `s` pushes forward to a measure `≤ μ`
(`MeasureTheory.Measure.map_restrict_le_map`), so it has a Radon–Nikodym density with respect
to `μ` taking values in `[0, 1]`. That density is `mapRestrictDensity f ν μ s`, and it is
characterised by

`∫ a, mapRestrictDensity f ν μ s a * g a ∂μ = ∫ x in s, g (f x) ∂ν`

for every `μ`-a.e. strongly measurable `g : Ω → ℝ` (`integral_mapRestrictDensity_mul`). This
Radon–Nikodym identity holds for arbitrary `s`. When `f` is measure-preserving and `s` is
measurable, the density has the additional probabilistic reading of the conditional probability
of `s` given `f`: composing it with `f` gives a version of `ν[s.indicator 1 | comap f]`. Nothing
here needs that reading, so the conditional-expectation machinery is not used; the elementary
Radon–Nikodym route is enough.

**Truncation is deliberate.** The definition applies `min 1` to the Radon–Nikodym derivative so
that the `[0, 1]` bounds hold *everywhere*, not merely almost everywhere. Consumers pair this
function against a kernel and need a strict pointwise bound to feed an extremal argument; the
truncation is invisible to every integral statement below, because it changes the derivative only
on a `μ`-null set (`mapRestrictDensity_ae_eq_rnDeriv`).
The private product-carrier regression below confirms that the density can be a genuinely
fractional multiple of an indicator, rather than always an indicator itself.

## Main definitions

* `TauCeti.MeasureTheory.mapRestrictDensity` — the `[0, 1]`-valued density on the base of the part
  of `ν` carried by a set upstairs.

## Main results

* `TauCeti.MeasureTheory.integral_mapRestrictDensity_mul` — the characterising identity: integrating
  against the density downstairs computes the integral over the set upstairs. No measurability of
  the set is needed.
* `TauCeti.MeasureTheory.mapRestrictDensity_ae_eq_rnDeriv` — the truncation is a.e. invisible.
* `TauCeti.MeasureTheory.mapRestrictDensity_mem_Icc` — the density lies in `[0, 1]` everywhere.
* `TauCeti.MeasureTheory.integral_mapRestrictDensity` — the density integrates to the measure of
  the set, the case `g = 1`.
* `TauCeti.MeasureTheory.mapRestrictDensity_congr_set` — the density depends on the set upstairs
  only through its `ν`-a.e. class; this equality is exact, not almost everywhere.
* `TauCeti.MeasureTheory.mapRestrictDensity_preimage` and
  `TauCeti.MeasureTheory.mapRestrictDensity_univ` — for a measure-preserving `f`, on a preimage the
  density collapses `μ`-almost everywhere to an indicator, so the construction extends the trivial
  case.

## References

* Mathlib's `MeasureTheory.toReal_rnDeriv_map` identifies the Radon–Nikodym derivative of a
  pushforward with a conditional expectation; it is the abstract form of the reading above and is
  not needed for any statement here.
-/

public section

noncomputable section

open MeasureTheory Set

open scoped ENNReal

namespace TauCeti

namespace MeasureTheory

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
variable {μ : Measure Ω} {ν : Measure Ω'} {f : Ω' → Ω}

/-- The **density on the base of the part of `ν` carried by `s`**: the Radon–Nikodym derivative of
`(ν.restrict s).map f` with respect to `μ`, truncated to `[0, 1]`.

When `f` pushes `ν` forward to a measure below `μ` the truncation is a.e. invisible
(`mapRestrictDensity_ae_eq_rnDeriv`) and the function is characterised by
`integral_mapRestrictDensity_mul`. The measures are explicit arguments because neither is
determined by the others: `μ` is not forced to be `ν.map f` by the type. -/
def mapRestrictDensity (f : Ω' → Ω) (ν : Measure Ω') (μ : Measure Ω) (s : Set Ω') (a : Ω) : ℝ :=
  min 1 (((ν.restrict s).map f).rnDeriv μ a).toReal

/-- The defining formula of `mapRestrictDensity`. -/
theorem mapRestrictDensity_def (f : Ω' → Ω) (ν : Measure Ω') (μ : Measure Ω)
    (s : Set Ω') (a : Ω) :
    mapRestrictDensity f ν μ s a = min 1 (((ν.restrict s).map f).rnDeriv μ a).toReal := (rfl)

/-- The density is measurable, being a truncated Radon–Nikodym derivative. -/
@[fun_prop]
theorem measurable_mapRestrictDensity (f : Ω' → Ω) (ν : Measure Ω') (μ : Measure Ω)
    (s : Set Ω') : Measurable (mapRestrictDensity f ν μ s) :=
  measurable_const.min (Measure.measurable_rnDeriv _ _).ennreal_toReal

/-- **The density is `[0, 1]`-valued everywhere.**  The upper bound is what the truncation in the
definition buys; both bounds are packaged together, in the form the extremal arguments of the
cut-norm theory consume, and the two halves are `.1` and `.2`. -/
theorem mapRestrictDensity_mem_Icc (f : Ω' → Ω) (ν : Measure Ω') (μ : Measure Ω)
    (s : Set Ω') (a : Ω) : mapRestrictDensity f ν μ s a ∈ Icc (0 : ℝ) 1 :=
  ⟨le_min zero_le_one ENNReal.toReal_nonneg, min_le_left _ _⟩

/-- **The density depends on the set upstairs only through its `ν`-a.e. class.**  Replacing `s` by
an a.e. equal set does not change the function at all, since it does not change `ν.restrict s`. -/
theorem mapRestrictDensity_congr_set (f : Ω' → Ω) (μ : Measure Ω) {s t : Set Ω'}
    (h : s =ᵐ[ν] t) : mapRestrictDensity f ν μ s = mapRestrictDensity f ν μ t := by
  funext a
  rw [mapRestrictDensity_def, mapRestrictDensity_def, Measure.restrict_congr_set h]

/-- **The truncation in `mapRestrictDensity` is a.e. invisible.**  The underlying Radon–Nikodym
derivative is already at most `1` almost everywhere, because the measure it differentiates is
below `μ`.  This holds as soon as `f` pushes `ν` forward to a measure below `μ`, in particular
when `f` is measure-preserving. -/
theorem mapRestrictDensity_ae_eq_rnDeriv [SigmaFinite μ] (hf : AEMeasurable f ν)
    (hμ : ν.map f ≤ μ) (s : Set Ω') :
    mapRestrictDensity f ν μ s =ᵐ[μ] fun a => (((ν.restrict s).map f).rnDeriv μ a).toReal := by
  filter_upwards [Measure.rnDeriv_le_one_of_le ((Measure.map_restrict_le_map hf s).trans hμ)]
    with a ha
  exact min_eq_right <| by simpa using ENNReal.toReal_mono ENNReal.one_ne_top ha

/-- **The characterising identity of `mapRestrictDensity`.**  Integrating a function on the base
against the density computes its integral, composed with `f`, over the set upstairs.

The set is arbitrary: `Measure.restrict` and every step of the computation are insensitive to its
measurability.  It suffices that `f` pushes `ν` forward to a measure below `μ`, in particular that
`f` is measure-preserving. -/
theorem integral_mapRestrictDensity_mul [SigmaFinite μ] (hf : AEMeasurable f ν)
    (hμ : ν.map f ≤ μ) (s : Set Ω') {g : Ω → ℝ} (hg : AEStronglyMeasurable g μ) :
    ∫ a, mapRestrictDensity f ν μ s a * g a ∂μ = ∫ x in s, g (f x) ∂ν := by
  have hle := (Measure.map_restrict_le_map hf s).trans hμ
  have : SigmaFinite ((ν.restrict s).map f) := Measure.sigmaFinite_of_le μ hle
  rw [← integral_map hf.restrict (hg.mono_measure hle),
    ← integral_toReal_rnDeriv_mul (Measure.absolutelyContinuous_of_le hle)]
  exact integral_congr_ae (mapRestrictDensity_ae_eq_rnDeriv hf hμ s).mul_right

/-- The density integrates to the measure of the set it came from: the case `g = 1` of
`integral_mapRestrictDensity_mul`. -/
theorem integral_mapRestrictDensity [SigmaFinite μ] (hf : AEMeasurable f ν) (hμ : ν.map f ≤ μ)
    (s : Set Ω') : ∫ a, mapRestrictDensity f ν μ s a ∂μ = ν.real s := by
  simpa using integral_mapRestrictDensity_mul hf hμ s (g := fun _ => (1 : ℝ))
    aestronglyMeasurable_const

/-- **On a preimage the density is `μ`-almost everywhere an indicator.**  Nothing is lost when the
set upstairs is already cut out by a set on the base, so `mapRestrictDensity` extends the trivial
case rather than replacing it.

The conclusion is only `μ`-a.e., as it must be: the Radon–Nikodym derivative is itself defined only
up to a `μ`-null set. -/
theorem mapRestrictDensity_preimage [SigmaFinite μ] (hf : MeasurePreserving f ν μ) {t : Set Ω}
    (ht : NullMeasurableSet t μ) :
    mapRestrictDensity f ν μ (f ⁻¹' t) =ᵐ[μ] t.indicator 1 := by
  have hu : toMeasurable μ t =ᵐ[μ] t := ht.toMeasurable_ae_eq
  have hmap : (ν.restrict (f ⁻¹' toMeasurable μ t)).map f = μ.restrict (toMeasurable μ t) := by
    rw [← Measure.restrict_map hf.measurable (measurableSet_toMeasurable μ t), hf.map_eq]
  rw [← mapRestrictDensity_congr_set f μ (hf.quasiMeasurePreserving.preimage_ae_eq hu)]
  filter_upwards [mapRestrictDensity_ae_eq_rnDeriv hf.aemeasurable hf.map_eq.le
      (f ⁻¹' toMeasurable μ t),
    hmap ▸ Measure.rnDeriv_restrict_self μ (measurableSet_toMeasurable μ t),
    indicator_ae_eq_of_ae_eq_set (f := (1 : Ω → ℝ)) hu] with a ha hb hc
  rw [ha, hb, ← hc]
  by_cases hat : a ∈ toMeasurable μ t <;> simp [hat]

/-- The whole carrier upstairs has density `1` `μ`-almost everywhere. -/
theorem mapRestrictDensity_univ [SigmaFinite μ] (hf : MeasurePreserving f ν μ) :
    mapRestrictDensity f ν μ univ =ᵐ[μ] 1 := by
  simpa using mapRestrictDensity_preimage hf (t := univ) nullMeasurableSet_univ

/-- **The density genuinely takes fractional values.**  On a product carrier projected to its first
factor, a rectangle `s ×ˢ t` has density `ν.real t · 1_s` `μ`-almost everywhere: the second factor
contributes its mass, not an indicator.  Together with `mapRestrictDensity_preimage` this pins the
construction down — an indicator of a set on the base would be wrong whenever
`0 < ν.real t < 1`. -/
private theorem mapRestrictDensity_fst_prod [SigmaFinite μ] [IsProbabilityMeasure ν] {s : Set Ω}
    (hs : MeasurableSet s) (t : Set Ω') :
    mapRestrictDensity Prod.fst (μ.prod ν) μ (s ×ˢ t) =ᵐ[μ]
      fun a => ν.real t * s.indicator 1 a := by
  have hf : MeasurePreserving (Prod.fst : Ω × Ω' → Ω) (μ.prod ν) μ := measurePreserving_fst
  have hmap : ((μ.prod ν).restrict (s ×ˢ t)).map Prod.fst = ν t • μ.restrict s := by
    rw [← Measure.prod_restrict, Measure.map_fst_prod, Measure.restrict_apply_univ]
  filter_upwards [mapRestrictDensity_ae_eq_rnDeriv hf.aemeasurable hf.map_eq.le (s ×ˢ t),
    hmap ▸ Measure.rnDeriv_smul_left_of_ne_top' (μ.restrict s) μ (measure_ne_top ν t),
    Measure.rnDeriv_restrict_self μ hs] with a ha hb hc
  rw [ha, hb, Pi.smul_apply, hc]
  by_cases has : a ∈ s <;> simp [has, measureReal_def]

end MeasureTheory

end TauCeti
