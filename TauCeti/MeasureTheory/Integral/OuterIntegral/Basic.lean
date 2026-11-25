/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import TauCeti.MeasureTheory.Integral.OuterIntegral.LIntegral

import Mathlib.Basic.Real.Pointwise
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import TauCeti.Basic.ENNReal.Real
import TauCeti.MeasureTheory.Measure.AEMeasurable
import TauCeti.Order.Filter.Group

/-!
# Real-valued outer and inner integrals

Given a measure `μ` on a measurable space `α` and an arbitrary (not necessarily measurable)
real-valued function `f : α → ℝ`, the outer integral `TauCeti.outerIntegral μ f` is the infimum of
`∫ ω, g ω ∂μ` over measurable integrable majorants `g ≥ f`, and the inner integral
`TauCeti.innerIntegral μ f` is `-outerIntegral μ (-f)`.

## Main definitions

* `TauCeti.outerIntegral`: real-valued outer integral.
* `TauCeti.innerIntegral`: real-valued inner integral.

## Main results

* `TauCeti.exists_measurable_ge_outerIntegral_eq` and
  `TauCeti.exists_measurable_le_innerIntegral_eq`: existence of minimal measurable integrable
  majorants and maximal measurable integrable minorants (van der Vaart–Wellner, Lemma 1.2.1).
* `TauCeti.outerLIntegral_ofReal_eq`: agreement of `outerLIntegral` and `outerIntegral` for
  almost-everywhere nonnegative functions admitting an integrable measurable majorant.
* `TauCeti.outerIntegral_eq_integral`, `TauCeti.innerIntegral_eq_integral`, and their
  finite-measure variants `TauCeti.outerIntegral_eq_integral_of_aemeasurable` and
  `TauCeti.innerIntegral_eq_integral_of_aemeasurable`: agreement with the Bochner integral.
* `TauCeti.outerIntegral_indicator_const`, `TauCeti.outerIntegral_indicator_one`, and
  `TauCeti.innerIntegral_indicator_one`: outer and inner integrals of indicators recover outer and
  inner measure.
* `TauCeti.outerIntegral_add_le`, `TauCeti.outerIntegral_const_mul`,
  `TauCeti.innerIntegral_le_outerIntegral`, and `TauCeti.abs_outerIntegral_sub_le`: subadditivity,
  positive homogeneity, inner-outer comparison, and the triangle inequality.

## References

* A. W. van der Vaart and J. A. Wellner, *Weak Convergence and Empirical Processes*, 2nd edition,
  Springer, 2023, §1.2, Lemma 1.2.1, p. 6.
-/

public section

open Filter MeasureTheory Set Topology
open scoped ENNReal

namespace TauCeti

variable {α : Type*} [MeasurableSpace α]

/-! ### Definitions -/

/-- The outer integral of a real-valued function `f` with respect to `μ`, defined as the infimum of
`∫ ω, g ω ∂μ` over measurable integrable majorants `g ≥ f`.

When `f` has no integrable measurable majorant or the majorant integrals are not bounded below,
this takes the `sInf` default value `0`; for nonnegative possibly unbounded functions, use
`outerLIntegral`. -/
noncomputable def outerIntegral (μ : Measure α) (f : α → ℝ) : ℝ :=
  ⨅ g : {g : α → ℝ // Measurable g ∧ Integrable g μ ∧ f ≤ g}, ∫ ω, (g : α → ℝ) ω ∂μ

/-- The inner integral of a real-valued function `f` with respect to `μ`, defined as
`-outerIntegral μ (-f)`. -/
noncomputable def innerIntegral (μ : Measure α) (f : α → ℝ) : ℝ :=
  -outerIntegral μ (-f)

/-- Unfolding lemma for `outerIntegral`. -/
theorem outerIntegral_def (μ : Measure α) (f : α → ℝ) :
    outerIntegral μ f =
      ⨅ g : {g : α → ℝ // Measurable g ∧ Integrable g μ ∧ f ≤ g}, ∫ ω, (g : α → ℝ) ω ∂μ :=
  (rfl)

/-- Unfolding lemma for `innerIntegral`. -/
theorem innerIntegral_def (μ : Measure α) (f : α → ℝ) :
    innerIntegral μ f = -outerIntegral μ (-f) :=
  (rfl)

/-- Characterization of `innerIntegral` as the supremum of integrals over measurable integrable
minorants (including degenerate cases where both sides are `0`). -/
theorem innerIntegral_eq_iSup (μ : Measure α) (f : α → ℝ) :
    innerIntegral μ f =
      ⨆ g : {g : α → ℝ // Measurable g ∧ Integrable g μ ∧ g ≤ f}, ∫ ω, (g : α → ℝ) ω ∂μ := by
  rw [innerIntegral_def, outerIntegral_def, iInf, iSup, ← neg_inj, neg_neg, ← Real.sInf_neg]
  congr 1
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨⟨-g.val, g.property.1.neg, g.property.2.1.neg, neg_le.mp g.property.2.2⟩,
      by simp [integral_neg]⟩
  · rintro ⟨g, hg⟩
    exact ⟨⟨-g.val, g.property.1.neg, g.property.2.1.neg, neg_le_neg g.property.2.2⟩,
      by simp [integral_neg, hg]⟩

/-- If `f` admits no measurable integrable majorant, then `outerIntegral μ f = 0`. -/
theorem outerIntegral_eq_zero_of_not_exists {μ : Measure α} {f : α → ℝ}
    (hu : ¬ ∃ u, Measurable u ∧ Integrable u μ ∧ f ≤ u) :
    outerIntegral μ f = 0 := by
  have : IsEmpty {g : α → ℝ // Measurable g ∧ Integrable g μ ∧ f ≤ g} :=
    (isEmpty_subtype _).2 fun g ⟨hg_meas, hg_int, hfg⟩ ↦ hu ⟨g, hg_meas, hg_int, hfg⟩
  rw [outerIntegral_def, Real.iInf_of_isEmpty]

/-- If the integrals of measurable integrable majorants of `f` are not bounded below, then
`outerIntegral μ f = 0`. -/
theorem outerIntegral_eq_zero_of_not_bddBelow {μ : Measure α} {f : α → ℝ}
    (h : ¬ BddBelow (Set.range fun g :
      {g : α → ℝ // Measurable g ∧ Integrable g μ ∧ f ≤ g} ↦ ∫ ω, g.val ω ∂μ)) :
    outerIntegral μ f = 0 := by
  rw [outerIntegral_def, Real.iInf_of_not_bddBelow h]

private theorem exists_measurable_integrable_ge_neg_iff {μ : Measure α} {f : α → ℝ} :
    (∃ u, Measurable u ∧ Integrable u μ ∧ -f ≤ u) ↔
      ∃ l, Measurable l ∧ Integrable l μ ∧ l ≤ f :=
  ⟨fun ⟨u, hu_meas, hu_int, hfu⟩ ↦ ⟨-u, hu_meas.neg, hu_int.neg, neg_le.mp hfu⟩,
   fun ⟨l, hl_meas, hl_int, hlf⟩ ↦ ⟨-l, hl_meas.neg, hl_int.neg, neg_le_neg hlf⟩⟩

/-- If `f` admits no measurable integrable minorant, then `innerIntegral μ f = 0`. -/
theorem innerIntegral_eq_zero_of_not_exists {μ : Measure α} {f : α → ℝ}
    (hl : ¬ ∃ l, Measurable l ∧ Integrable l μ ∧ l ≤ f) :
    innerIntegral μ f = 0 := by
  rw [innerIntegral_def,
    outerIntegral_eq_zero_of_not_exists (exists_measurable_integrable_ge_neg_iff.not.mpr hl),
    neg_zero]

/-- If the integrals of measurable integrable minorants of `f` are not bounded above, then
`innerIntegral μ f = 0`. -/
theorem innerIntegral_eq_zero_of_not_bddAbove {μ : Measure α} {f : α → ℝ}
    (h : ¬ BddAbove (Set.range fun g :
      {g : α → ℝ // Measurable g ∧ Integrable g μ ∧ g ≤ f} ↦ ∫ ω, g.val ω ∂μ)) :
    innerIntegral μ f = 0 := by
  rw [innerIntegral_eq_iSup, Real.iSup_of_not_bddAbove h]

/-! ### Real-valued outer integral -/

section OuterIntegral

private theorem bddBelow_range_integral_majorants {μ : Measure α} {f : α → ℝ}
    (hl : ∃ l, Integrable l μ ∧ l ≤ᵐ[μ] f) :
    BddBelow (Set.range fun h : {g : α → ℝ // Measurable g ∧ Integrable g μ ∧ f ≤ g} ↦
      ∫ ω, h.val ω ∂μ) := by
  obtain ⟨l, hl_int, hlf⟩ := hl
  refine ⟨∫ ω, l ω ∂μ, ?_⟩
  rintro _ ⟨h, rfl⟩
  exact integral_mono_ae hl_int h.property.2.1 (hlf.trans (ae_of_all _ h.property.2.2))

private theorem outerIntegral_le_integral_of_ae_of_bddBelow {μ : Measure α} {f g : α → ℝ}
    (hg : Integrable g μ) (hfg : f ≤ᵐ[μ] g) (hu : ∃ u, Measurable u ∧ f ≤ u)
    (hbdd : BddBelow (Set.range fun h : {g : α → ℝ // Measurable g ∧ Integrable g μ ∧ f ≤ g} ↦
      ∫ ω, h.val ω ∂μ)) :
    outerIntegral μ f ≤ ∫ ω, g ω ∂μ := by
  obtain ⟨u, hu_meas, hfu⟩ := hu
  obtain ⟨g', hg'_meas, hfg', hg'_ae⟩ :=
    hg.aemeasurable.exists_measurable_ge_ae_eq_of_ae_le hfg hu_meas hfu
  calc outerIntegral μ f ≤ ∫ ω, g' ω ∂μ :=
        ciInf_le hbdd ⟨g', hg'_meas, hg.congr hg'_ae, hfg'⟩
    _ = ∫ ω, g ω ∂μ := integral_congr_ae hg'_ae.symm

/-- `outerIntegral μ f` is bounded above by `∫ g ∂μ` for any measurable integrable majorant
`g ≥ f`, provided `f` admits an integrable minorant so that the infimum is bounded below. -/
theorem outerIntegral_le_integral {μ : Measure α} {f g : α → ℝ}
    (hg_meas : Measurable g) (hg_int : Integrable g μ) (hfg : f ≤ g)
    (hl : ∃ l, Integrable l μ ∧ l ≤ᵐ[μ] f) :
    outerIntegral μ f ≤ ∫ ω, g ω ∂μ :=
  ciInf_le (bddBelow_range_integral_majorants hl) ⟨g, hg_meas, hg_int, hfg⟩

/-- `outerIntegral μ f` is bounded above by `∫ g ∂μ` for any integrable `g` with `f ≤ᵐ[μ] g`,
provided `f` admits a measurable majorant and an integrable minorant. -/
theorem outerIntegral_le_integral_of_ae {μ : Measure α} {f g : α → ℝ}
    (hg : Integrable g μ) (hfg : f ≤ᵐ[μ] g)
    (hu : ∃ u, Measurable u ∧ f ≤ u) (hl : ∃ l, Integrable l μ ∧ l ≤ᵐ[μ] f) :
    outerIntegral μ f ≤ ∫ ω, g ω ∂μ :=
  outerIntegral_le_integral_of_ae_of_bddBelow hg hfg hu (bddBelow_range_integral_majorants hl)

/-- Universal lower bound for `outerIntegral`: if `f` has a measurable integrable majorant and
`c ≤ ∫ g ∂μ` for every measurable integrable `g ≥ f`, then `c ≤ outerIntegral μ f`. -/
theorem le_outerIntegral {μ : Measure α} {f : α → ℝ} {c : ℝ}
    (hu : ∃ u, Measurable u ∧ Integrable u μ ∧ f ≤ u)
    (h : ∀ g, Measurable g → Integrable g μ → f ≤ g → c ≤ ∫ ω, g ω ∂μ) :
    c ≤ outerIntegral μ f := by
  obtain ⟨u, hu_meas, hu_int, hfu⟩ := hu
  have : Nonempty {g : α → ℝ // Measurable g ∧ Integrable g μ ∧ f ≤ g} :=
    ⟨⟨u, hu_meas, hu_int, hfu⟩⟩
  exact le_ciInf fun ⟨g, hg_meas, hg_int, hfg⟩ ↦ h g hg_meas hg_int hfg

/-- Universal lower-bound characterization for `outerIntegral` when `f` admits a measurable
integrable majorant and an integrable minorant. -/
theorem le_outerIntegral_iff {μ : Measure α} {f : α → ℝ} {c : ℝ}
    (hu : ∃ u, Measurable u ∧ Integrable u μ ∧ f ≤ u)
    (hl : ∃ l, Integrable l μ ∧ l ≤ᵐ[μ] f) :
    c ≤ outerIntegral μ f ↔ ∀ g, Measurable g → Integrable g μ → f ≤ g → c ≤ ∫ ω, g ω ∂μ :=
  ⟨fun h _ hg_meas hg_int hfg ↦ h.trans (outerIntegral_le_integral hg_meas hg_int hfg hl),
    le_outerIntegral hu⟩

/-- The integral of any integrable minorant `l ≤ᵐ[μ] f` is bounded above by `outerIntegral μ f`,
provided `f` admits a measurable integrable majorant. -/
theorem integral_le_outerIntegral {μ : Measure α} {f l : α → ℝ}
    (hl : Integrable l μ) (hlf : l ≤ᵐ[μ] f)
    (hu : ∃ u, Measurable u ∧ Integrable u μ ∧ f ≤ u) :
    ∫ ω, l ω ∂μ ≤ outerIntegral μ f :=
  le_outerIntegral hu fun _ _ hg_int hfg ↦
    integral_mono_ae hl hg_int (hlf.trans (ae_of_all _ hfg))

/-- Any integrable a.e. majorant `g` attaining `outerIntegral μ f` is minimal almost everywhere
among all a.e.-measurable a.e. majorants `h` of `f`. -/
theorem ae_le_of_integral_eq_outerIntegral {μ : Measure α} {f g h : α → ℝ}
    (hg : Integrable g μ) (hfg : f ≤ᵐ[μ] g)
    (hu : ∃ u, Measurable u ∧ f ≤ u) (hl : ∃ l, Integrable l μ ∧ l ≤ᵐ[μ] f)
    (hg_eq : ∫ ω, g ω ∂μ = outerIntegral μ f)
    (hh : AEMeasurable h μ) (hfh : f ≤ᵐ[μ] h) :
    g ≤ᵐ[μ] h := by
  obtain ⟨l₀, hl₀_int, hl₀f⟩ := hl
  let m : α → ℝ := fun ω ↦ min (g ω) (h ω)
  have hm_aem : AEMeasurable m μ := hg.aemeasurable.min hh
  have hfm : f ≤ᵐ[μ] m := (hfg.and hfh).mono fun _ ⟨h1, h2⟩ ↦ le_min h1 h2
  have hm_int : Integrable m μ := integrable_of_le_of_le hm_aem.aestronglyMeasurable
    (hl₀f.trans hfm) (ae_of_all _ fun _ ↦ min_le_left _ _) hl₀_int hg
  have hle : ∫ ω, g ω ∂μ ≤ ∫ ω, m ω ∂μ := by
    rw [hg_eq]
    exact outerIntegral_le_integral_of_ae hm_int hfm hu ⟨l₀, hl₀_int, hl₀f⟩
  have hm_eq : ∫ ω, m ω ∂μ = ∫ ω, g ω ∂μ :=
    le_antisymm (integral_mono hm_int hg fun _ ↦ min_le_left _ _) hle
  have heq : m =ᵐ[μ] g :=
    (integral_eq_iff_of_ae_le hm_int hg (ae_of_all _ fun _ ↦ min_le_left _ _)).mp hm_eq
  exact heq.mono fun ω hω ↦ hω ▸ min_le_right (g ω) (h ω)

/-- **Measurable cover for `outerIntegral` (van der Vaart–Wellner, Lemma 1.2.1).** If `f` admits a
measurable integrable majorant and an integrable minorant, there exists a measurable integrable
majorant `g ≥ f` whose integral equals `outerIntegral μ f` and which is minimal almost everywhere
among all a.e.-measurable functions `h` with `f ≤ᵐ[μ] h`. -/
theorem exists_measurable_ge_outerIntegral_eq {μ : Measure α} {f : α → ℝ}
    (hu : ∃ u, Measurable u ∧ Integrable u μ ∧ f ≤ u)
    (hl : ∃ l, Integrable l μ ∧ l ≤ᵐ[μ] f) :
    ∃ g : α → ℝ, Measurable g ∧ Integrable g μ ∧ f ≤ g ∧ ∫ ω, g ω ∂μ = outerIntegral μ f ∧
      ∀ h : α → ℝ, AEMeasurable h μ → f ≤ᵐ[μ] h → g ≤ᵐ[μ] h := by
  obtain ⟨u, hu_meas, hu_int, hfu⟩ := hu
  obtain ⟨l₀, hl₀_int, hl₀f⟩ := hl
  let w : α → ℝ≥0∞ := fun ω ↦ ENNReal.ofReal (u ω - f ω)
  obtain ⟨h, hh_meas, hhw, hh_eq⟩ := exists_measurable_le_lintegral_eq μ w
  have hh_lt_top : ∀ ω, h ω < ⊤ := fun ω ↦ (hhw ω).trans_lt ENNReal.ofReal_lt_top
  have hh_fin : ∫⁻ ω, h ω ∂μ ≠ ⊤ := by
    refine ne_top_of_le_ne_top (hu_int.sub hl₀_int).hasFiniteIntegral.ne ?_
    rw [← hh_eq]
    refine lintegral_mono_ae (hl₀f.mono fun ω hω ↦ ?_)
    have hle : u ω - f ω ≤ |u ω - l₀ ω| := (sub_le_sub_left hω (u ω)).trans (le_abs_self _)
    exact (ENNReal.ofReal_le_ofReal hle).trans_eq (Real.eNorm_eq_ofReal_abs _).symm
  have hh_int : Integrable (fun ω ↦ (h ω).toReal) μ :=
    integrable_toReal_of_lintegral_ne_top hh_meas.aemeasurable hh_fin
  let g : α → ℝ := fun ω ↦ u ω - (h ω).toReal
  have hg_meas : Measurable g := hu_meas.sub hh_meas.ennreal_toReal
  have hg_int : Integrable g μ := hu_int.sub hh_int
  have hfg : f ≤ g := fun ω ↦ by
    have hle : (h ω).toReal ≤ (w ω).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hhw ω)
    rw [ENNReal.toReal_ofReal (sub_nonneg.mpr (hfu ω))] at hle
    linarith
  have hg_eq : ∫ ω, g ω ∂μ = outerIntegral μ f := by
    refine le_antisymm ?_ (outerIntegral_le_integral hg_meas hg_int hfg ⟨l₀, hl₀_int, hl₀f⟩)
    refine le_outerIntegral ⟨u, hu_meas, hu_int, hfu⟩ fun v _ hv_int hfv ↦ ?_
    let v' : α → ℝ := fun ω ↦ min (v ω) (u ω)
    have hv'_int : Integrable v' μ := hv_int.inf hu_int
    have hle_lint : ∫⁻ ω, ENNReal.ofReal (u ω - v' ω) ∂μ ≤ ∫⁻ ω, h ω ∂μ := by
      rw [← hh_eq]
      exact lintegral_mono fun ω ↦
        ENNReal.ofReal_le_ofReal (sub_le_sub_left (le_min (hfv ω) (hfu ω)) _)
    have h1 : ENNReal.ofReal (∫ ω, (u ω - v' ω) ∂μ) = ∫⁻ ω, ENNReal.ofReal (u ω - v' ω) ∂μ :=
      ofReal_integral_eq_lintegral_ofReal (hu_int.sub hv'_int)
        (ae_of_all _ fun _ ↦ sub_nonneg.mpr (min_le_right _ _))
    rw [← h1] at hle_lint
    have hle_real : ∫ ω, (u ω - v' ω) ∂μ ≤ ∫ ω, (h ω).toReal ∂μ := by
      rw [integral_toReal hh_meas.aemeasurable (ae_of_all _ hh_lt_top)]
      exact (ENNReal.ofReal_le_iff_le_toReal hh_fin).mp hle_lint
    rw [integral_sub hu_int hv'_int] at hle_real
    have hv'v : ∫ ω, v' ω ∂μ ≤ ∫ ω, v ω ∂μ := integral_mono hv'_int hv_int fun _ ↦ min_le_left _ _
    rw [integral_sub hu_int hh_int]
    linarith
  exact ⟨g, hg_meas, hg_int, hfg, hg_eq, fun k hk hfk ↦
    ae_le_of_integral_eq_outerIntegral hg_int (ae_of_all _ hfg) ⟨g, hg_meas, hfg⟩
      ⟨l₀, hl₀_int, hl₀f⟩ hg_eq hk hfk⟩

/-- For an integrable function admitting a measurable majorant, `outerIntegral` agrees with the
Bochner integral. -/
theorem outerIntegral_eq_integral {μ : Measure α} {f : α → ℝ}
    (hf : Integrable f μ) (hu : ∃ u, Measurable u ∧ f ≤ u) :
    outerIntegral μ f = ∫ ω, f ω ∂μ := by
  obtain ⟨u, hu_meas, hfu⟩ := hu
  obtain ⟨g, hg_meas, hfg, hg_ae⟩ :=
    hf.aemeasurable.exists_measurable_ge_ae_eq_of_ae_le EventuallyEq.rfl.le hu_meas hfu
  refine le_antisymm ?_
    (integral_le_outerIntegral hf EventuallyEq.rfl.le ⟨g, hg_meas, hf.congr hg_ae, hfg⟩)
  calc outerIntegral μ f ≤ ∫ ω, g ω ∂μ :=
        outerIntegral_le_integral hg_meas (hf.congr hg_ae) hfg ⟨f, hf, EventuallyEq.rfl.le⟩
    _ = ∫ ω, f ω ∂μ := integral_congr_ae hg_ae.symm

/-- For a measurable integrable function, `outerIntegral` agrees with the Bochner integral. -/
theorem outerIntegral_eq_integral_of_measurable {μ : Measure α} {f : α → ℝ}
    (hm : Measurable f) (hf : Integrable f μ) :
    outerIntegral μ f = ∫ ω, f ω ∂μ :=
  outerIntegral_eq_integral hf ⟨f, hm, le_rfl⟩

private theorem lintegral_min_negPart_le_of_bddBelow {μ : Measure α} [IsFiniteMeasure μ]
    {f u : α → ℝ} (hf : AEMeasurable f μ) (hu_meas : Measurable u) (hu_int : Integrable u μ)
    (hfu : f ≤ u) (hp_int : Integrable (fun ω ↦ max (hf.mk f ω) 0) μ) {M : ℝ}
    (hM : ∀ g : {g : α → ℝ // Measurable g ∧ Integrable g μ ∧ f ≤ g}, M ≤ ∫ ω, g.val ω ∂μ)
    (n : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (min (max (-(hf.mk f ω)) 0) n) ∂μ ≤
      ENNReal.ofReal (∫ ω, max (hf.mk f ω) 0 ∂μ - M) := by
  let f₀ : α → ℝ := hf.mk f
  have hf₀_meas : Measurable f₀ := hf.measurable_mk
  let h : α → ℝ := fun ω ↦ max (f₀ ω) (-(n : ℝ))
  have hh_meas : Measurable h := hf₀_meas.max measurable_const
  have hh_int : Integrable h μ := integrable_of_le_of_le hh_meas.aestronglyMeasurable
    (ae_of_all _ fun _ ↦ le_max_right _ _)
    ((hf.ae_eq_mk.symm.le.trans (ae_of_all _ hfu)).mono fun _ hω ↦ max_le_max_right _ hω)
    (integrable_const _) (hu_int.sup (integrable_const _))
  obtain ⟨g, hg_meas, hfg, hg_ae⟩ :=
    hh_meas.aemeasurable.exists_measurable_ge_ae_eq_of_ae_le
      (hf.ae_eq_mk.le.trans (ae_of_all _ fun _ ↦ le_max_left _ _)) hu_meas hfu
  have hM_le : M ≤ ∫ ω, h ω ∂μ := by
    rw [integral_congr_ae hg_ae]
    exact hM ⟨g, hg_meas, hh_int.congr hg_ae, hfg⟩
  let q : α → ℝ := fun ω ↦ min (max (-f₀ ω) 0) n
  have hq_nn : ∀ ω, 0 ≤ q ω := fun _ ↦ le_min (le_max_right _ _) (Nat.cast_nonneg _)
  have hq_int : Integrable q μ := integrable_of_le_of_le
    ((hf₀_meas.neg.max measurable_const).min measurable_const).aestronglyMeasurable
    (ae_of_all _ hq_nn) (ae_of_all _ fun _ ↦ min_le_right _ _)
    (integrable_zero α ℝ μ) (integrable_const (n : ℝ))
  have hdecomp : h = (fun ω ↦ max (f₀ ω) 0) - q := funext fun ω ↦ by
    simp only [h, q, Pi.sub_apply, max_def, min_def]
    split_ifs <;> linarith [Nat.cast_nonneg (α := ℝ) n]
  rw [hdecomp, Pi.sub_def, integral_sub hp_int hq_int] at hM_le
  rw [← ofReal_integral_eq_lintegral_ofReal hq_int (ae_of_all _ hq_nn)]
  exact ENNReal.ofReal_le_ofReal (by linarith)

private theorem integrable_of_aemeasurable_of_bddBelow {μ : Measure α} [IsFiniteMeasure μ]
    {f u : α → ℝ} (hf : AEMeasurable f μ) (hu_meas : Measurable u) (hu_int : Integrable u μ)
    (hfu : f ≤ u)
    (hbdd : BddBelow (Set.range fun g :
      {g : α → ℝ // Measurable g ∧ Integrable g μ ∧ f ≤ g} ↦ ∫ ω, g.val ω ∂μ)) :
    Integrable f μ := by
  obtain ⟨M, hM⟩ := hbdd
  let f₀ : α → ℝ := hf.mk f
  have hf₀_meas : Measurable f₀ := hf.measurable_mk
  have hp_int : Integrable (fun ω ↦ max (f₀ ω) 0) μ := integrable_of_le_of_le
    (hf₀_meas.max measurable_const).aestronglyMeasurable
    (ae_of_all _ fun _ ↦ le_max_right _ _)
    ((hf.ae_eq_mk.symm.le.trans (ae_of_all _ hfu)).mono fun _ hω ↦ max_le_max_right _ hω)
    (integrable_zero α ℝ μ) (hu_int.sup (integrable_zero α ℝ μ))
  have hneg_fin : ∫⁻ ω, ENNReal.ofReal (max (-f₀ ω) 0) ∂μ < ⊤ := by
    simp_rw [← ENNReal.iSup_ofReal_min_natCast (max (-f₀ _) 0)]
    have hq_meas : ∀ n : ℕ, Measurable fun ω ↦ ENNReal.ofReal (min (max (-f₀ ω) 0) n) :=
      fun n ↦ ((hf₀_meas.neg.max measurable_const).min measurable_const).ennreal_ofReal
    rw [lintegral_iSup hq_meas
      (fun _ _ hmn ω ↦ ENNReal.ofReal_le_ofReal (min_le_min_left _ (Nat.cast_le.mpr hmn)))]
    exact lt_of_le_of_lt
      (iSup_le fun n ↦ lintegral_min_negPart_le_of_bddBelow hf hu_meas hu_int hfu hp_int
        (fun g ↦ hM ⟨g, rfl⟩) n)
      ENNReal.ofReal_lt_top
  have hneg_int : Integrable (fun ω ↦ max (-f₀ ω) 0) μ :=
    ⟨(hf₀_meas.neg.max measurable_const).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ ↦ le_max_right _ _)).mpr hneg_fin⟩
  have heq : f₀ = (fun ω ↦ max (f₀ ω) 0) - fun ω ↦ max (-f₀ ω) 0 :=
    funext fun ω ↦ (max_zero_sub_eq_self (f₀ ω)).symm
  exact (hp_int.sub hneg_int).congr ((EventuallyEq.of_eq heq.symm).trans hf.ae_eq_mk.symm)

/-- Under a finite measure, `outerIntegral` agrees with the Bochner integral for any
a.e.-measurable function admitting a measurable majorant (without assuming integrability). -/
theorem outerIntegral_eq_integral_of_aemeasurable {μ : Measure α} [IsFiniteMeasure μ]
    {f : α → ℝ} (hf : AEMeasurable f μ) (hu : ∃ u, Measurable u ∧ f ≤ u) :
    outerIntegral μ f = ∫ ω, f ω ∂μ := by
  by_cases hf_int : Integrable f μ
  · exact outerIntegral_eq_integral hf_int hu
  rw [integral_undef hf_int]
  by_cases hu' : ∃ u, Measurable u ∧ Integrable u μ ∧ f ≤ u
  · obtain ⟨u, hu_meas, hu_int, hfu⟩ := hu'
    exact outerIntegral_eq_zero_of_not_bddBelow fun hbdd ↦
      hf_int (integrable_of_aemeasurable_of_bddBelow hf hu_meas hu_int hfu hbdd)
  · exact outerIntegral_eq_zero_of_not_exists hu'

/-- If `0 ≤ᵐ[μ] f`, then `0 ≤ outerIntegral μ f` (including when the majorant set is empty). -/
theorem outerIntegral_nonneg {μ : Measure α} {f : α → ℝ} (hf : 0 ≤ᵐ[μ] f) :
    0 ≤ outerIntegral μ f := by
  by_cases hu : ∃ u, Measurable u ∧ Integrable u μ ∧ f ≤ u
  · simpa using integral_le_outerIntegral (integrable_zero α ℝ μ) hf hu
  · exact (outerIntegral_eq_zero_of_not_exists hu).ge

/-- Agreement of `outerLIntegral` and `outerIntegral`: for an a.e.-nonnegative function admitting
an integrable measurable majorant, `outerLIntegral μ (ofReal ∘ f) = ofReal (outerIntegral μ f)`. -/
theorem outerLIntegral_ofReal_eq {μ : Measure α} {f : α → ℝ}
    (hf : 0 ≤ᵐ[μ] f) (hu : ∃ u, Measurable u ∧ Integrable u μ ∧ f ≤ u) :
    outerLIntegral μ (fun ω ↦ ENNReal.ofReal (f ω)) = ENNReal.ofReal (outerIntegral μ f) := by
  apply le_antisymm
  · obtain ⟨g, hg_meas, hg_int, hfg, hg_eq, _⟩ :=
      exists_measurable_ge_outerIntegral_eq hu ⟨0, integrable_zero α ℝ μ, hf⟩
    have hg_nn : 0 ≤ᵐ[μ] g := hf.mono fun ω hω ↦ hω.trans (hfg ω)
    calc outerLIntegral μ (fun ω ↦ ENNReal.ofReal (f ω))
        ≤ ∫⁻ ω, ENNReal.ofReal (g ω) ∂μ :=
          outerLIntegral_le_lintegral (ENNReal.measurable_ofReal.comp hg_meas)
            fun ω ↦ ENNReal.ofReal_le_ofReal (hfg ω)
      _ = ENNReal.ofReal (∫ ω, g ω ∂μ) := (ofReal_integral_eq_lintegral_ofReal hg_int hg_nn).symm
      _ = ENNReal.ofReal (outerIntegral μ f) := by rw [hg_eq]
  · obtain ⟨u, hu_meas, hu_int, hfu⟩ := hu
    refine le_outerLIntegral fun h hh_meas hfh ↦ ?_
    let h' : α → ℝ≥0∞ := fun ω ↦ min (h ω) (ENNReal.ofReal (u ω))
    have hh'_meas : Measurable h' := hh_meas.min (ENNReal.measurable_ofReal.comp hu_meas)
    have hh'_lt_top : ∀ ω, h' ω < ⊤ := fun ω ↦
      lt_of_le_of_lt (min_le_right _ _) ENNReal.ofReal_lt_top
    let g : α → ℝ := fun ω ↦ (h' ω).toReal
    have hg_meas : Measurable g := hh'_meas.ennreal_toReal
    have hfg : f ≤ g := fun ω ↦ by
      by_cases h0 : f ω ≤ 0
      · exact h0.trans ENNReal.toReal_nonneg
      · have hle : ENNReal.ofReal (f ω) ≤ h' ω :=
          le_min (hfh ω) (ENNReal.ofReal_le_ofReal (hfu ω))
        simpa [g, ENNReal.toReal_ofReal (le_of_not_ge h0)] using
          ENNReal.toReal_mono (hh'_lt_top ω).ne hle
    have hg_int : Integrable g μ := integrable_of_le_of_le hg_meas.aestronglyMeasurable
      (ae_of_all _ fun _ ↦ ENNReal.toReal_nonneg)
      (ae_of_all _ fun ω ↦
        (ENNReal.toReal_mono ENNReal.ofReal_ne_top (min_le_right _ _)).trans_eq
          ENNReal.toReal_ofReal')
      (integrable_zero α ℝ μ) (hu_int.sup (integrable_zero α ℝ μ))
    calc ENNReal.ofReal (outerIntegral μ f)
        ≤ ENNReal.ofReal (∫ ω, g ω ∂μ) :=
          ENNReal.ofReal_le_ofReal
            (outerIntegral_le_integral hg_meas hg_int hfg ⟨0, integrable_zero α ℝ μ, hf⟩)
      _ = ∫⁻ ω, ENNReal.ofReal (g ω) ∂μ :=
          ofReal_integral_eq_lintegral_ofReal hg_int (ae_of_all _ fun _ ↦ ENNReal.toReal_nonneg)
      _ = ∫⁻ ω, h' ω ∂μ := lintegral_congr fun ω ↦ ENNReal.ofReal_toReal (hh'_lt_top ω).ne
      _ ≤ ∫⁻ ω, h ω ∂μ := lintegral_mono fun _ ↦ min_le_left _ _

/-- `outerIntegral` of the constant zero function is `0`. -/
@[simp]
theorem outerIntegral_zero (μ : Measure α) : outerIntegral μ (fun _ ↦ 0) = 0 := by
  have h := outerIntegral_eq_integral_of_measurable (f := fun _ : α ↦ (0 : ℝ))
    measurable_const (integrable_zero α ℝ μ)
  simpa using h

/-- `outerIntegral` of the zero function is `0`. -/
@[simp]
theorem outerIntegral_zero_fun (μ : Measure α) : outerIntegral μ 0 = 0 := by
  rw [Pi.zero_def, outerIntegral_zero]

/-- `outerIntegral` with respect to the zero measure is `0`. -/
@[simp]
theorem outerIntegral_zero_measure (f : α → ℝ) : outerIntegral (0 : Measure α) f = 0 := by
  simp only [outerIntegral_def, integral_zero_measure, Real.iInf_const_zero]

/-- `outerIntegral` of a constant function under a finite measure is `c * μ.real Set.univ`. -/
@[simp]
theorem outerIntegral_const (μ : Measure α) [IsFiniteMeasure μ] (c : ℝ) :
    outerIntegral μ (fun _ ↦ c) = c * μ.real Set.univ := by
  rw [outerIntegral_eq_integral_of_measurable measurable_const (integrable_const c),
    integral_const, smul_eq_mul, mul_comm]

/-- For `0 ≤ c` and any (not necessarily measurable) set `s`, the outer integral of
`s.indicator (fun _ ↦ c)` equals `c * μ.real s`. -/
@[simp]
theorem outerIntegral_indicator_const (μ : Measure α) (s : Set α) {c : ℝ} (hc : 0 ≤ c) :
    outerIntegral μ (s.indicator fun _ ↦ c) = c * μ.real s := by
  rcases eq_or_lt_of_le hc with rfl | hcpos
  · simp
  by_cases hs : μ s = ⊤
  · rw [outerIntegral_eq_zero_of_not_exists, Measure.real, hs, ENNReal.toReal_top, mul_zero]
    rintro ⟨g, hg_meas, hg_int, hsg⟩
    have hsub : s ⊆ {ω | ENNReal.ofReal c ≤ ‖g ω‖ₑ} := fun ω hω ↦ by
      have hcg : c ≤ g ω := by simpa [hω] using hsg ω
      simpa [Real.eNorm_eq_ofReal_abs] using ENNReal.ofReal_le_ofReal (hcg.trans (le_abs_self _))
    have hle : ENNReal.ofReal c * μ s ≤ ∫⁻ ω, ‖g ω‖ₑ ∂μ :=
      (mul_le_mul_right (measure_mono hsub) _).trans
        (mul_meas_ge_le_lintegral hg_meas.eNorm _)
    rw [hs, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hcpos).ne'] at hle
    exact hg_int.hasFiniteIntegral.ne (top_unique hle)
  · have hu : ∃ u, Measurable u ∧ Integrable u μ ∧ s.indicator (fun _ ↦ c) ≤ u := by
      refine ⟨(toMeasurable μ s).indicator fun _ ↦ c,
        measurable_const.indicator (measurableSet_toMeasurable μ s),
        (integrable_indicator_iff (measurableSet_toMeasurable μ s)).mpr
          (integrableOn_const (by rw [measure_toMeasurable]; exact hs)),
        Set.indicator_le_indicator_of_subset (subset_toMeasurable μ s) (fun _ ↦ hc)⟩
    have hnn : 0 ≤ᵐ[μ] s.indicator (fun _ ↦ c) :=
      ae_of_all _ fun ω ↦ Set.indicator_nonneg (fun _ _ ↦ hc) ω
    have heq := outerLIntegral_ofReal_eq hnn hu
    have hind : (fun ω ↦ ENNReal.ofReal (s.indicator (fun _ ↦ c) ω)) =
        s.indicator fun _ ↦ ENNReal.ofReal c := by
      ext ω; by_cases hω : ω ∈ s <;> simp [hω]
    rw [hind, outerLIntegral_indicator_const, ← ENNReal.ofReal_toReal hs,
      ← ENNReal.ofReal_mul hc] at heq
    exact ((ENNReal.ofReal_eq_ofReal_iff (mul_nonneg hc ENNReal.toReal_nonneg)
      (outerIntegral_nonneg hnn)).mp heq).symm

/-- For any (not necessarily measurable) set `s`, `outerIntegral μ (s.indicator 1) = μ.real s`. -/
@[simp]
theorem outerIntegral_indicator_one (μ : Measure α) (s : Set α) :
    outerIntegral μ (s.indicator 1) = μ.real s := by
  simp [Pi.one_def]

/-- Monotonicity of `outerIntegral` with respect to almost-everywhere inequality. -/
theorem outerIntegral_mono_ae {μ : Measure α} {f₁ f₂ : α → ℝ} (h : f₁ ≤ᵐ[μ] f₂)
    (hu₁ : ∃ u, Measurable u ∧ f₁ ≤ u)
    (hu₂ : ∃ u, Measurable u ∧ Integrable u μ ∧ f₂ ≤ u)
    (hl₁ : ∃ l, Integrable l μ ∧ l ≤ᵐ[μ] f₁) :
    outerIntegral μ f₁ ≤ outerIntegral μ f₂ :=
  le_outerIntegral hu₂ fun _ _ hg_int h₂g ↦
    outerIntegral_le_integral_of_ae hg_int (h.trans (ae_of_all _ h₂g)) hu₁ hl₁

/-- Monotonicity of `outerIntegral`. -/
theorem outerIntegral_mono {μ : Measure α} {f₁ f₂ : α → ℝ} (h : f₁ ≤ f₂)
    (hu₂ : ∃ u, Measurable u ∧ Integrable u μ ∧ f₂ ≤ u)
    (hl₁ : ∃ l, Integrable l μ ∧ l ≤ᵐ[μ] f₁) :
    outerIntegral μ f₁ ≤ outerIntegral μ f₂ :=
  le_outerIntegral hu₂ fun _ hg_meas hg_int h₂g ↦
    outerIntegral_le_integral hg_meas hg_int (h.trans h₂g) hl₁

private theorem range_integral_majorants_subset_of_ae_le {μ : Measure α} {f₁ f₂ : α → ℝ}
    (h : f₂ ≤ᵐ[μ] f₁) (hu₂ : ∃ u, Measurable u ∧ f₂ ≤ u) :
    Set.range (fun g : {g : α → ℝ // Measurable g ∧ Integrable g μ ∧ f₁ ≤ g} ↦ ∫ ω, g.val ω ∂μ) ⊆
      Set.range (fun g : {g : α → ℝ // Measurable g ∧ Integrable g μ ∧ f₂ ≤ g} ↦
        ∫ ω, g.val ω ∂μ) := by
  obtain ⟨u₂, hu₂_meas, hf₂u₂⟩ := hu₂
  rintro x ⟨⟨g, hg_meas, hg_int, hfg⟩, rfl⟩
  obtain ⟨g', hg'_meas, hf₂g', hg'_ae⟩ :=
    hg_meas.aemeasurable.exists_measurable_ge_ae_eq_of_ae_le
      (h.trans (ae_of_all _ hfg)) hu₂_meas hf₂u₂
  exact ⟨⟨g', hg'_meas, hg_int.congr hg'_ae, hf₂g'⟩, integral_congr_ae hg'_ae.symm⟩

/-- Functions equal almost everywhere that each admit a measurable majorant have equal
`outerIntegral`. -/
theorem outerIntegral_congr_ae {μ : Measure α} {f₁ f₂ : α → ℝ} (h : f₁ =ᵐ[μ] f₂)
    (hu₁ : ∃ u, Measurable u ∧ f₁ ≤ u) (hu₂ : ∃ u, Measurable u ∧ f₂ ≤ u) :
    outerIntegral μ f₁ = outerIntegral μ f₂ := by
  rw [outerIntegral_def, outerIntegral_def, iInf, iInf]
  exact congrArg sInf (Set.Subset.antisymm
    (range_integral_majorants_subset_of_ae_le h.symm.le hu₂)
    (range_integral_majorants_subset_of_ae_le h.le hu₁))

/-- Subadditivity of `outerIntegral`. -/
theorem outerIntegral_add_le {μ : Measure α} {f g : α → ℝ}
    (hfu : ∃ u, Measurable u ∧ Integrable u μ ∧ f ≤ u)
    (hgu : ∃ u, Measurable u ∧ Integrable u μ ∧ g ≤ u)
    (hfl : ∃ l, Integrable l μ ∧ l ≤ᵐ[μ] f)
    (hgl : ∃ l, Integrable l μ ∧ l ≤ᵐ[μ] g) :
    outerIntegral μ (f + g) ≤ outerIntegral μ f + outerIntegral μ g := by
  obtain ⟨f', hf'_meas, hf'_int, hff', hf'_eq, _⟩ := exists_measurable_ge_outerIntegral_eq hfu hfl
  obtain ⟨g', hg'_meas, hg'_int, hgg', hg'_eq, _⟩ := exists_measurable_ge_outerIntegral_eq hgu hgl
  obtain ⟨lf, hlf_int, hlf⟩ := hfl
  obtain ⟨lg, hlg_int, hlg⟩ := hgl
  calc outerIntegral μ (f + g) ≤ ∫ ω, (f' + g') ω ∂μ :=
        outerIntegral_le_integral (hf'_meas.add hg'_meas) (hf'_int.add hg'_int)
          (add_le_add hff' hgg')
          ⟨lf + lg, hlf_int.add hlg_int, (hlf.and hlg).mono fun _ ⟨h1, h2⟩ ↦ add_le_add h1 h2⟩
    _ = ∫ ω, f' ω ∂μ + ∫ ω, g' ω ∂μ := integral_add hf'_int hg'_int
    _ = outerIntegral μ f + outerIntegral μ g := by rw [hf'_eq, hg'_eq]

/-- Adding a measurable integrable function shifts `outerIntegral` by its integral. -/
theorem outerIntegral_add_of_measurable {μ : Measure α} {f g : α → ℝ}
    (hg_meas : Measurable g) (hg_int : Integrable g μ)
    (hfu : ∃ u, Measurable u ∧ Integrable u μ ∧ f ≤ u)
    (hfl : ∃ l, Integrable l μ ∧ l ≤ᵐ[μ] f) :
    outerIntegral μ (f + g) = outerIntegral μ f + ∫ ω, g ω ∂μ := by
  obtain ⟨u, hu_meas, hu_int, hfu'⟩ := hfu
  obtain ⟨l, hl_int, hlf⟩ := hfl
  apply le_antisymm
  · calc outerIntegral μ (f + g) ≤ outerIntegral μ f + outerIntegral μ g :=
          outerIntegral_add_le ⟨u, hu_meas, hu_int, hfu'⟩ ⟨g, hg_meas, hg_int, le_rfl⟩
            ⟨l, hl_int, hlf⟩ ⟨g, hg_int, EventuallyEq.rfl.le⟩
      _ = outerIntegral μ f + ∫ ω, g ω ∂μ := by
          rw [outerIntegral_eq_integral_of_measurable hg_meas hg_int]
  · have h1 := outerIntegral_add_le
      ⟨u + g, hu_meas.add hg_meas, hu_int.add hg_int, add_le_add hfu' le_rfl⟩
      ⟨-g, hg_meas.neg, hg_int.neg, le_rfl⟩
      ⟨l + g, hl_int.add hg_int, hlf.mono fun _ hω ↦ add_le_add hω le_rfl⟩
      ⟨-g, hg_int.neg, EventuallyEq.rfl.le⟩
    rw [add_neg_cancel_right, outerIntegral_eq_integral_of_measurable hg_meas.neg hg_int.neg] at h1
    simp only [Pi.neg_apply, integral_neg] at h1
    linarith

/-- Adding a constant shifts `outerIntegral` under a finite measure by `c * μ.real Set.univ`. -/
theorem outerIntegral_add_const {μ : Measure α} [IsFiniteMeasure μ] {f : α → ℝ} (c : ℝ)
    (hfu : ∃ u, Measurable u ∧ Integrable u μ ∧ f ≤ u)
    (hfl : ∃ l, Integrable l μ ∧ l ≤ᵐ[μ] f) :
    outerIntegral μ (fun ω ↦ f ω + c) = outerIntegral μ f + c * μ.real Set.univ := by
  have h := outerIntegral_add_of_measurable (g := fun _ ↦ c) measurable_const (integrable_const c)
    hfu hfl
  simpa [Pi.add_def, integral_const, mul_comm] using h

/-- Positive homogeneity of `outerIntegral` for all `0 ≤ c` (no majorant or finiteness hypotheses
required). -/
theorem outerIntegral_const_mul (μ : Measure α) {c : ℝ} (hc : 0 ≤ c) (f : α → ℝ) :
    outerIntegral μ (fun ω ↦ c * f ω) = c * outerIntegral μ f := by
  rcases eq_or_lt_of_le hc with rfl | hcpos
  · simp
  let e : {g : α → ℝ // Measurable g ∧ Integrable g μ ∧ f ≤ g} ≃
      {h : α → ℝ // Measurable h ∧ Integrable h μ ∧ (fun ω ↦ c * f ω) ≤ h} :=
    { toFun := fun g ↦ ⟨fun ω ↦ c * g.val ω, g.property.1.const_mul c, g.property.2.1.const_mul c,
        fun ω ↦ mul_le_mul_of_nonneg_left (g.property.2.2 ω) hc⟩
      invFun := fun h ↦ ⟨fun ω ↦ c⁻¹ * h.val ω, h.property.1.const_mul c⁻¹,
        h.property.2.1.const_mul c⁻¹, fun ω ↦ by
          calc f ω = c⁻¹ * (c * f ω) := by rw [inv_mul_cancel_left₀ hcpos.ne']
            _ ≤ c⁻¹ * h.val ω := mul_le_mul_of_nonneg_left (h.property.2.2 ω) (inv_nonneg.mpr hc)⟩
      left_inv := fun g ↦ Subtype.ext <| funext fun ω ↦ inv_mul_cancel_left₀ hcpos.ne' (g.val ω)
      right_inv := fun h ↦ Subtype.ext <| funext fun ω ↦ mul_inv_cancel_left₀ hcpos.ne' (h.val ω) }
  rw [outerIntegral_def, outerIntegral_def, ← smul_eq_mul, Real.smul_iInf_of_nonneg hc]
  symm
  refine e.iInf_congr fun g ↦ ?_
  simp [e, integral_const_mul]

/-- The absolute value of `outerIntegral μ f` is bounded by `outerIntegral μ (fun ω ↦ |f ω|)`
whenever `f` admits a measurable integrable minorant. -/
theorem abs_outerIntegral_le_outerIntegral_abs {μ : Measure α} {f : α → ℝ}
    (hl : ∃ l, Measurable l ∧ Integrable l μ ∧ l ≤ f) :
    |outerIntegral μ f| ≤ outerIntegral μ (fun ω ↦ |f ω|) := by
  by_cases hu : ∃ u, Measurable u ∧ Integrable u μ ∧ f ≤ u
  · obtain ⟨u, hu_meas, hu_int, hfu⟩ := hu
    obtain ⟨l, hl_meas, hl_int, hlf⟩ := hl
    have habs_u : ∃ w, Measurable w ∧ Integrable w μ ∧ (fun ω ↦ |f ω|) ≤ w :=
      ⟨fun ω ↦ max (u ω) (-l ω), hu_meas.max hl_meas.neg, hu_int.sup hl_int.neg,
        fun ω ↦ abs_le.mpr ⟨by linarith [hlf ω, le_max_right (u ω) (-l ω)],
          (hfu ω).trans (le_max_left _ _)⟩⟩
    rw [abs_le]
    refine ⟨?_, outerIntegral_mono (fun ω ↦ le_abs_self (f ω)) habs_u ⟨l, hl_int, ae_of_all _ hlf⟩⟩
    have hsum := outerIntegral_add_le habs_u ⟨u, hu_meas, hu_int, hfu⟩
      ⟨0, integrable_zero α ℝ μ, ae_of_all _ fun _ ↦ abs_nonneg _⟩
      ⟨l, hl_int, ae_of_all _ hlf⟩
    have h0 : 0 ≤ outerIntegral μ ((fun ω ↦ |f ω|) + f) :=
      outerIntegral_nonneg (ae_of_all _ fun ω ↦ by
        simp only [Pi.zero_apply, Pi.add_apply]
        linarith [neg_abs_le (f ω)])
    linarith
  · rw [outerIntegral_eq_zero_of_not_exists hu, abs_zero]
    exact outerIntegral_nonneg (ae_of_all _ fun _ ↦ abs_nonneg _)

/-- One-sided triangle inequality for `outerIntegral`: `outerIntegral μ f` is bounded by
`outerIntegral μ g + outerIntegral μ (fun ω ↦ |f ω - g ω|)`. -/
theorem outerIntegral_le_add_outerIntegral_abs_sub {μ : Measure α} {f g : α → ℝ}
    (hgu : ∃ u, Measurable u ∧ Integrable u μ ∧ g ≤ u)
    (hgl : ∃ l, Integrable l μ ∧ l ≤ᵐ[μ] g)
    (hdu : ∃ w, Measurable w ∧ Integrable w μ ∧ (fun ω ↦ |f ω - g ω|) ≤ w) :
    outerIntegral μ f ≤ outerIntegral μ g + outerIntegral μ (fun ω ↦ |f ω - g ω|) := by
  obtain ⟨ug, hug_meas, hug_int, hug⟩ := hgu
  obtain ⟨lg, hlg_int, hlg⟩ := hgl
  obtain ⟨w, hw_meas, hw_int, hdw⟩ := hdu
  have hfl : ∃ l, Integrable l μ ∧ l ≤ᵐ[μ] f :=
    ⟨lg - w, hlg_int.sub hw_int, hlg.mono fun ω hω ↦ by
      simp only [Pi.sub_apply]
      linarith [hdw ω, neg_abs_le (f ω - g ω)]⟩
  calc outerIntegral μ f ≤ outerIntegral μ (g + fun ω ↦ |f ω - g ω|) :=
        outerIntegral_mono
          (fun ω ↦ by simp only [Pi.add_apply]; linarith [le_abs_self (f ω - g ω)])
          ⟨ug + w, hug_meas.add hw_meas, hug_int.add hw_int, add_le_add hug hdw⟩ hfl
    _ ≤ outerIntegral μ g + outerIntegral μ (fun ω ↦ |f ω - g ω|) :=
        outerIntegral_add_le ⟨ug, hug_meas, hug_int, hug⟩ ⟨w, hw_meas, hw_int, hdw⟩
          ⟨lg, hlg_int, hlg⟩ ⟨0, integrable_zero α ℝ μ, ae_of_all _ fun _ ↦ abs_nonneg _⟩

/-- Triangle inequality for `outerIntegral`: `|outerIntegral μ f - outerIntegral μ g|` is bounded
by `outerIntegral μ (fun ω ↦ |f ω - g ω|)`. -/
theorem abs_outerIntegral_sub_le {μ : Measure α} {f g : α → ℝ}
    (hfu : ∃ u, Measurable u ∧ Integrable u μ ∧ f ≤ u)
    (hfl : ∃ l, Measurable l ∧ Integrable l μ ∧ l ≤ f)
    (hgu : ∃ u, Measurable u ∧ Integrable u μ ∧ g ≤ u)
    (hgl : ∃ l, Measurable l ∧ Integrable l μ ∧ l ≤ g) :
    |outerIntegral μ f - outerIntegral μ g| ≤ outerIntegral μ (fun ω ↦ |f ω - g ω|) := by
  obtain ⟨uf, huf_meas, huf_int, huf⟩ := hfu
  obtain ⟨lf, hlf_meas, hlf_int, hlf⟩ := hfl
  obtain ⟨ug, hug_meas, hug_int, hug⟩ := hgu
  obtain ⟨lg, hlg_meas, hlg_int, hlg⟩ := hgl
  have hdu : ∃ w, Measurable w ∧ Integrable w μ ∧ (fun ω ↦ |f ω - g ω|) ≤ w :=
    ⟨fun ω ↦ max (uf ω - lg ω) (ug ω - lf ω),
      (huf_meas.sub hlg_meas).max (hug_meas.sub hlf_meas),
      (huf_int.sub hlg_int).sup (hug_int.sub hlf_int),
      fun ω ↦ abs_le.mpr ⟨by linarith [hlf ω, hug ω, le_max_right (uf ω - lg ω) (ug ω - lf ω)],
        by linarith [huf ω, hlg ω, le_max_left (uf ω - lg ω) (ug ω - lf ω)]⟩⟩
  have hdu' : ∃ w, Measurable w ∧ Integrable w μ ∧ (fun ω ↦ |g ω - f ω|) ≤ w := by
    simpa only [abs_sub_comm] using hdu
  have hfg := outerIntegral_le_add_outerIntegral_abs_sub
    ⟨ug, hug_meas, hug_int, hug⟩ ⟨lg, hlg_int, ae_of_all _ hlg⟩ hdu
  have hgf := outerIntegral_le_add_outerIntegral_abs_sub
    ⟨uf, huf_meas, huf_int, huf⟩ ⟨lf, hlf_int, ae_of_all _ hlf⟩ hdu'
  simp_rw [abs_sub_comm (g _)] at hgf
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

end OuterIntegral

/-! ### Real-valued inner integral -/

section InnerIntegral

private theorem exists_measurable_ge_neg {f : α → ℝ}
    (hl : ∃ l, Measurable l ∧ l ≤ f) :
    ∃ u, Measurable u ∧ -f ≤ u :=
  let ⟨l, hl_meas, hlf⟩ := hl
  ⟨-l, hl_meas.neg, neg_le_neg hlf⟩

private theorem exists_integrable_le_ae_neg {μ : Measure α} {f : α → ℝ}
    (hu : ∃ u, Integrable u μ ∧ f ≤ᵐ[μ] u) :
    ∃ l, Integrable l μ ∧ l ≤ᵐ[μ] -f :=
  let ⟨u, hu_int, hfu⟩ := hu
  ⟨-u, hu_int.neg, hfu.neg⟩

/-- `innerIntegral μ (-f) = -outerIntegral μ f`. -/
@[simp]
theorem innerIntegral_neg (μ : Measure α) (f : α → ℝ) :
    innerIntegral μ (-f) = -outerIntegral μ f := by
  rw [innerIntegral_def, neg_neg]

/-- `outerIntegral μ (-f) = -innerIntegral μ f`. -/
@[simp]
theorem outerIntegral_neg (μ : Measure α) (f : α → ℝ) :
    outerIntegral μ (-f) = -innerIntegral μ f := by
  rw [innerIntegral_def, neg_neg]

/-- `innerIntegral` of the constant zero function is `0`. -/
@[simp]
theorem innerIntegral_zero (μ : Measure α) : innerIntegral μ (fun _ ↦ 0) = 0 := by
  rw [innerIntegral_def]
  have h : -(fun _ : α ↦ (0 : ℝ)) = fun _ ↦ 0 := by ext; simp
  rw [h, outerIntegral_zero, neg_zero]

/-- `innerIntegral` of the zero function is `0`. -/
@[simp]
theorem innerIntegral_zero_fun (μ : Measure α) : innerIntegral μ 0 = 0 := by
  rw [Pi.zero_def, innerIntegral_zero]

/-- `innerIntegral` with respect to the zero measure is `0`. -/
@[simp]
theorem innerIntegral_zero_measure (f : α → ℝ) : innerIntegral (0 : Measure α) f = 0 := by
  rw [innerIntegral_def, outerIntegral_zero_measure, neg_zero]

/-- `innerIntegral` of a constant function under a finite measure is `c * μ.real Set.univ`. -/
@[simp]
theorem innerIntegral_const (μ : Measure α) [IsFiniteMeasure μ] (c : ℝ) :
    innerIntegral μ (fun _ ↦ c) = c * μ.real Set.univ := by
  rw [innerIntegral_def]
  have h : -(fun _ : α ↦ c) = fun _ ↦ -c := by ext; simp
  rw [h, outerIntegral_const, neg_mul, neg_neg]

/-- Positive homogeneity of `innerIntegral` for all `0 ≤ c`. -/
theorem innerIntegral_const_mul (μ : Measure α) {c : ℝ} (hc : 0 ≤ c) (f : α → ℝ) :
    innerIntegral μ (fun ω ↦ c * f ω) = c * innerIntegral μ f := by
  rw [innerIntegral_def, innerIntegral_def]
  have h : -(fun ω ↦ c * f ω) = fun ω ↦ c * (-f) ω := by ext ω; simp [mul_neg]
  rw [h, outerIntegral_const_mul μ hc (-f), mul_neg]

/-- Universal upper bound for `innerIntegral`: if `f` has a measurable integrable minorant and
`∫ g ∂μ ≤ c` for every measurable integrable `g ≤ f`, then `innerIntegral μ f ≤ c`. -/
theorem innerIntegral_le {μ : Measure α} {f : α → ℝ} {c : ℝ}
    (hl : ∃ l, Measurable l ∧ Integrable l μ ∧ l ≤ f)
    (h : ∀ g, Measurable g → Integrable g μ → g ≤ f → ∫ ω, g ω ∂μ ≤ c) :
    innerIntegral μ f ≤ c := by
  rw [innerIntegral_def, neg_le]
  refine le_outerIntegral (exists_measurable_integrable_ge_neg_iff.mpr hl)
    fun g hg_meas hg_int hfg ↦ ?_
  have hneg := h (-g) hg_meas.neg hg_int.neg (neg_le.mp hfg)
  simp only [Pi.neg_apply, integral_neg] at hneg
  linarith

/-- The integral of any measurable integrable minorant `g ≤ f` is bounded above by
`innerIntegral μ f`, provided `f` admits an integrable majorant. -/
theorem integral_le_innerIntegral {μ : Measure α} {f g : α → ℝ}
    (hg_meas : Measurable g) (hg_int : Integrable g μ) (hgf : g ≤ f)
    (hu : ∃ u, Integrable u μ ∧ f ≤ᵐ[μ] u) :
    ∫ ω, g ω ∂μ ≤ innerIntegral μ f := by
  rw [innerIntegral_def, le_neg, ← integral_neg]
  exact outerIntegral_le_integral hg_meas.neg hg_int.neg (neg_le_neg hgf)
    (exists_integrable_le_ae_neg hu)

/-- Universal upper-bound characterization for `innerIntegral` when `f` admits a measurable
integrable minorant and an integrable majorant. -/
theorem innerIntegral_le_iff {μ : Measure α} {f : α → ℝ} {c : ℝ}
    (hl : ∃ l, Measurable l ∧ Integrable l μ ∧ l ≤ f)
    (hu : ∃ u, Integrable u μ ∧ f ≤ᵐ[μ] u) :
    innerIntegral μ f ≤ c ↔ ∀ g, Measurable g → Integrable g μ → g ≤ f → ∫ ω, g ω ∂μ ≤ c :=
  ⟨fun h _ hg_meas hg_int hgf ↦ (integral_le_innerIntegral hg_meas hg_int hgf hu).trans h,
    innerIntegral_le hl⟩

/-- The integral of any integrable minorant `g ≤ᵐ[μ] f` is bounded above by `innerIntegral μ f`,
provided `f` admits a measurable minorant and an integrable majorant. -/
theorem integral_le_innerIntegral_of_ae {μ : Measure α} {f g : α → ℝ}
    (hg : Integrable g μ) (hgf : g ≤ᵐ[μ] f)
    (hl : ∃ l, Measurable l ∧ l ≤ f) (hu : ∃ u, Integrable u μ ∧ f ≤ᵐ[μ] u) :
    ∫ ω, g ω ∂μ ≤ innerIntegral μ f := by
  rw [innerIntegral_def, le_neg, ← integral_neg]
  exact outerIntegral_le_integral_of_ae hg.neg hgf.neg
    (exists_measurable_ge_neg hl) (exists_integrable_le_ae_neg hu)

/-- `innerIntegral μ f` is bounded above by the integral of any integrable majorant `u ≥ᵐ[μ] f`,
provided `f` admits a measurable integrable minorant. -/
theorem innerIntegral_le_integral {μ : Measure α} {f u : α → ℝ}
    (hu : Integrable u μ) (hfu : f ≤ᵐ[μ] u)
    (hl : ∃ l, Measurable l ∧ Integrable l μ ∧ l ≤ f) :
    innerIntegral μ f ≤ ∫ ω, u ω ∂μ := by
  rw [innerIntegral_def, neg_le, ← integral_neg]
  exact integral_le_outerIntegral hu.neg hfu.neg
    (exists_measurable_integrable_ge_neg_iff.mpr hl)

/-- `innerIntegral μ f ≤ outerIntegral μ f` whenever `f` admits both a measurable integrable
majorant and a measurable integrable minorant. -/
theorem innerIntegral_le_outerIntegral {μ : Measure α} {f : α → ℝ}
    (hu : ∃ u, Measurable u ∧ Integrable u μ ∧ f ≤ u)
    (hl : ∃ l, Measurable l ∧ Integrable l μ ∧ l ≤ f) :
    innerIntegral μ f ≤ outerIntegral μ f := by
  have ⟨u, _, hu_int, hfu⟩ := hu
  have ⟨l, _, hl_int, hlf⟩ := hl
  rw [innerIntegral_def, neg_le]
  have h0 : 0 ≤ outerIntegral μ f + outerIntegral μ (-f) := by
    have hsum := outerIntegral_add_le hu (exists_measurable_integrable_ge_neg_iff.mpr hl)
      ⟨l, hl_int, ae_of_all _ hlf⟩ (exists_integrable_le_ae_neg ⟨u, hu_int, ae_of_all _ hfu⟩)
    rwa [add_neg_cancel, outerIntegral_zero_fun] at hsum
  linarith

/-- Monotonicity of `innerIntegral` with respect to almost-everywhere inequality. -/
theorem innerIntegral_mono_ae {μ : Measure α} {f₁ f₂ : α → ℝ} (h : f₁ ≤ᵐ[μ] f₂)
    (hl₁ : ∃ l, Measurable l ∧ Integrable l μ ∧ l ≤ f₁)
    (hl₂ : ∃ l, Measurable l ∧ l ≤ f₂)
    (hu₂ : ∃ u, Integrable u μ ∧ f₂ ≤ᵐ[μ] u) :
    innerIntegral μ f₁ ≤ innerIntegral μ f₂ := by
  rw [innerIntegral_def, innerIntegral_def, neg_le_neg_iff]
  exact outerIntegral_mono_ae h.neg
    (exists_measurable_ge_neg hl₂) (exists_measurable_integrable_ge_neg_iff.mpr hl₁)
    (exists_integrable_le_ae_neg hu₂)

/-- Monotonicity of `innerIntegral`. -/
theorem innerIntegral_mono {μ : Measure α} {f₁ f₂ : α → ℝ} (h : f₁ ≤ f₂)
    (hl₁ : ∃ l, Measurable l ∧ Integrable l μ ∧ l ≤ f₁)
    (hu₂ : ∃ u, Integrable u μ ∧ f₂ ≤ᵐ[μ] u) :
    innerIntegral μ f₁ ≤ innerIntegral μ f₂ := by
  rw [innerIntegral_def, innerIntegral_def, neg_le_neg_iff]
  exact outerIntegral_mono (neg_le_neg h) (exists_measurable_integrable_ge_neg_iff.mpr hl₁)
    (exists_integrable_le_ae_neg hu₂)

/-- Functions equal almost everywhere that each admit a measurable minorant have equal
`innerIntegral`. -/
theorem innerIntegral_congr_ae {μ : Measure α} {f₁ f₂ : α → ℝ} (h : f₁ =ᵐ[μ] f₂)
    (hl₁ : ∃ l, Measurable l ∧ l ≤ f₁) (hl₂ : ∃ l, Measurable l ∧ l ≤ f₂) :
    innerIntegral μ f₁ = innerIntegral μ f₂ := by
  have hneg : (-f₁) =ᵐ[μ] (-f₂) := h.mono fun _ hω ↦ congrArg Neg.neg hω
  rw [innerIntegral_def, innerIntegral_def,
    outerIntegral_congr_ae hneg (exists_measurable_ge_neg hl₁) (exists_measurable_ge_neg hl₂)]

/-- Superadditivity of `innerIntegral`. -/
theorem le_innerIntegral_add {μ : Measure α} {f g : α → ℝ}
    (hfl : ∃ l, Measurable l ∧ Integrable l μ ∧ l ≤ f)
    (hgl : ∃ l, Measurable l ∧ Integrable l μ ∧ l ≤ g)
    (hfu : ∃ u, Integrable u μ ∧ f ≤ᵐ[μ] u)
    (hgu : ∃ u, Integrable u μ ∧ g ≤ᵐ[μ] u) :
    innerIntegral μ f + innerIntegral μ g ≤ innerIntegral μ (f + g) := by
  rw [innerIntegral_def, innerIntegral_def, innerIntegral_def, neg_add, ← neg_add_rev,
    add_comm (outerIntegral μ (-g)), neg_le_neg_iff]
  simpa [neg_add] using outerIntegral_add_le
    (exists_measurable_integrable_ge_neg_iff.mpr hfl)
    (exists_measurable_integrable_ge_neg_iff.mpr hgl)
    (exists_integrable_le_ae_neg hfu) (exists_integrable_le_ae_neg hgu)

/-- Adding a measurable integrable function shifts `innerIntegral` by its integral. -/
theorem innerIntegral_add_of_measurable {μ : Measure α} {f g : α → ℝ}
    (hg_meas : Measurable g) (hg_int : Integrable g μ)
    (hfl : ∃ l, Measurable l ∧ Integrable l μ ∧ l ≤ f)
    (hfu : ∃ u, Integrable u μ ∧ f ≤ᵐ[μ] u) :
    innerIntegral μ (f + g) = innerIntegral μ f + ∫ ω, g ω ∂μ := by
  rw [innerIntegral_def, innerIntegral_def, neg_add,
    outerIntegral_add_of_measurable hg_meas.neg hg_int.neg
      (exists_measurable_integrable_ge_neg_iff.mpr hfl) (exists_integrable_le_ae_neg hfu)]
  simp only [Pi.neg_apply, integral_neg]
  ring

/-- Adding a constant shifts `innerIntegral` under a finite measure by `c * μ.real Set.univ`. -/
theorem innerIntegral_add_const {μ : Measure α} [IsFiniteMeasure μ] {f : α → ℝ} (c : ℝ)
    (hfl : ∃ l, Measurable l ∧ Integrable l μ ∧ l ≤ f)
    (hfu : ∃ u, Integrable u μ ∧ f ≤ᵐ[μ] u) :
    innerIntegral μ (fun ω ↦ f ω + c) = innerIntegral μ f + c * μ.real Set.univ := by
  have h := innerIntegral_add_of_measurable (g := fun _ ↦ c) measurable_const (integrable_const c)
    hfl hfu
  simpa [Pi.add_def, integral_const, mul_comm] using h

/-- For an integrable function admitting a measurable minorant, `innerIntegral` agrees with the
Bochner integral. -/
theorem innerIntegral_eq_integral {μ : Measure α} {f : α → ℝ}
    (hf : Integrable f μ) (hl : ∃ l, Measurable l ∧ l ≤ f) :
    innerIntegral μ f = ∫ ω, f ω ∂μ := by
  rw [innerIntegral_def, outerIntegral_eq_integral hf.neg (exists_measurable_ge_neg hl)]
  simp [Pi.neg_apply, integral_neg]

/-- For a measurable integrable function, `innerIntegral` agrees with the Bochner integral. -/
theorem innerIntegral_eq_integral_of_measurable {μ : Measure α} {f : α → ℝ}
    (hm : Measurable f) (hf : Integrable f μ) :
    innerIntegral μ f = ∫ ω, f ω ∂μ :=
  innerIntegral_eq_integral hf ⟨f, hm, le_rfl⟩

/-- Under a finite measure, `innerIntegral` agrees with the Bochner integral for any
a.e.-measurable function admitting a measurable minorant (without assuming integrability). -/
theorem innerIntegral_eq_integral_of_aemeasurable {μ : Measure α} [IsFiniteMeasure μ]
    {f : α → ℝ} (hf : AEMeasurable f μ) (hl : ∃ l, Measurable l ∧ l ≤ f) :
    innerIntegral μ f = ∫ ω, f ω ∂μ := by
  rw [innerIntegral_def,
    outerIntegral_eq_integral_of_aemeasurable hf.neg (exists_measurable_ge_neg hl)]
  simp [Pi.neg_apply, integral_neg]

/-- If `0 ≤ᵐ[μ] f`, then `0 ≤ innerIntegral μ f` (with no majorant or finiteness hypotheses). -/
theorem innerIntegral_nonneg {μ : Measure α} {f : α → ℝ} (hf : 0 ≤ᵐ[μ] f) :
    0 ≤ innerIntegral μ f := by
  rw [innerIntegral_def, neg_nonneg]
  by_cases hu : ∃ u, Measurable u ∧ Integrable u μ ∧ -f ≤ u
  · by_cases hbdd : BddBelow (Set.range fun g :
        {g : α → ℝ // Measurable g ∧ Integrable g μ ∧ -f ≤ g} ↦ ∫ ω, g.val ω ∂μ)
    · obtain ⟨u, hu_meas, _, hfu⟩ := hu
      calc outerIntegral μ (-f) ≤ ∫ _ : α, (0 : ℝ) ∂μ :=
            outerIntegral_le_integral_of_ae_of_bddBelow (integrable_zero α ℝ μ)
              (hf.mono fun _ hω ↦ neg_nonpos.mpr hω) ⟨u, hu_meas, hfu⟩ hbdd
        _ = 0 := integral_zero α ℝ
    · rw [outerIntegral_eq_zero_of_not_bddBelow hbdd]
  · rw [outerIntegral_eq_zero_of_not_exists hu]

/-- Under a finite measure, `innerIntegral μ (s.indicator 1)` is the inner measure
`μ.real Set.univ - μ.real sᶜ`. -/
@[simp]
theorem innerIntegral_indicator_one (μ : Measure α) [IsFiniteMeasure μ] (s : Set α) :
    innerIntegral μ (s.indicator 1) = μ.real Set.univ - μ.real sᶜ := by
  have heq : -(s.indicator (1 : α → ℝ)) = fun ω ↦ sᶜ.indicator (1 : α → ℝ) ω + (-1) := by
    ext ω; by_cases hω : ω ∈ s <;> simp [hω]
  have h1 := outerIntegral_add_const (f := sᶜ.indicator (1 : α → ℝ)) (-1)
    ⟨fun _ ↦ 1, measurable_const, integrable_const 1,
      fun ω ↦ by by_cases hω : ω ∈ sᶜ <;> simp [hω]⟩
    ⟨0, integrable_zero α ℝ μ, ae_of_all _ fun ω ↦ Set.indicator_nonneg (fun _ _ ↦ zero_le_one) ω⟩
  rw [innerIntegral_def, heq, h1, outerIntegral_indicator_one]
  ring

/-- **Measurable minorant for `innerIntegral`.** If `f` admits a measurable integrable minorant
and an integrable majorant, there exists a measurable integrable minorant `g ≤ f` whose integral
equals `innerIntegral μ f` and which is maximal almost everywhere among all a.e.-measurable
functions `h` with `h ≤ᵐ[μ] f`. -/
theorem exists_measurable_le_innerIntegral_eq {μ : Measure α} {f : α → ℝ}
    (hl : ∃ l, Measurable l ∧ Integrable l μ ∧ l ≤ f)
    (hu : ∃ u, Integrable u μ ∧ f ≤ᵐ[μ] u) :
    ∃ g : α → ℝ, Measurable g ∧ Integrable g μ ∧ g ≤ f ∧ ∫ ω, g ω ∂μ = innerIntegral μ f ∧
      ∀ h : α → ℝ, AEMeasurable h μ → h ≤ᵐ[μ] f → h ≤ᵐ[μ] g := by
  obtain ⟨g', hg'_meas, hg'_int, hfg', hg'_eq, hg'_min⟩ :=
    exists_measurable_ge_outerIntegral_eq
      (exists_measurable_integrable_ge_neg_iff.mpr hl) (exists_integrable_le_ae_neg hu)
  refine ⟨-g', hg'_meas.neg, hg'_int.neg, neg_le.mp hfg', ?_, fun h hh hhf ↦ ?_⟩
  · rw [innerIntegral_def, ← hg'_eq]
    simp [Pi.neg_apply, integral_neg]
  · exact (hg'_min (-h) hh.neg hhf.neg).mono fun ω hω ↦ le_neg.mp hω

end InnerIntegral

end TauCeti
