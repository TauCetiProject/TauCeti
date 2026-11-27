/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import TauCeti.Analysis.BoundedVariation.Perimeter
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.MeasureTheory.Covering.DensityTheorem
import TauCeti.MeasureTheory.Measure.Lebesgue.Basic
import TauCeti.Analysis.BoundedVariation.Hyperplane
import TauCeti.Analysis.BoundedVariation.OneDimensional.LebesguePoints

/-!
# Perimeter on the real line

Using the Lebesgue-point variation bounds from
`TauCeti.Analysis.BoundedVariation.OneDimensional.LebesguePoints` (for Lebesgue points whose
joining closed interval lies in `Ω`), almost every point of a measurable set `s` is a Lebesgue
point of its indicator with value `0` or `1`. Counting alternations between points of `s` and of
its complement gives the sharp one-dimensional isoperimetric inequality and its rigidity:

* a null-measurable `s ⊆ ℝ` of positive finite measure has perimeter at least `2`
  (`TauCeti.Real.two_le_perimeter`);
* if `s` is null-measurable of finite measure and does not agree almost everywhere with any
  interval, then it has perimeter at least `4` (`TauCeti.Real.four_le_perimeter`);
* a nonempty bounded open interval has perimeter `2` (`TauCeti.Real.perimeter_Ioo`), and a
  null-measurable set of finite measure has perimeter `2` exactly when it agrees almost everywhere
  with such an interval (`TauCeti.Real.perimeter_eq_two_iff`).

These are the statements about almost every line section that slicing arguments for sets of
finite perimeter in higher dimensions apply: for a null-measurable set of finite volume, almost
every section of perimeter less than `4` is an interval of finite length up to a null set.

By `TauCeti.perimeter_setOf_inner_lt`, a half-line with endpoint `x` has perimeter `1` in an open
set containing `x` and `0` in any other open set (`TauCeti.Real.perimeter_Iio`,
`TauCeti.Real.perimeter_Ioi`).

More locally, on any open interval `Ω ⊆ ℝ` (including open rays and the whole line), a set `s`
null-measurable for Lebesgue measure restricted to `Ω` whose perimeter with respect to Lebesgue
measure in `Ω` is strictly less than `1` is either null or conull in `Ω`
(`TauCeti.Real.measure_inter_eq_zero_or_sdiff_eq_zero_of_perimeter_lt_one`).

## Main results

* `TauCeti.Real.two_le_perimeter`, `TauCeti.Real.four_le_perimeter`,
  `TauCeti.Real.perimeter_Ioo` and `TauCeti.Real.perimeter_eq_two_iff`.
* `TauCeti.Real.perimeter_Iio` and `TauCeti.Real.perimeter_Ioi`: the perimeter of a half-line.
* `TauCeti.Real.measure_inter_eq_zero_or_sdiff_eq_zero_of_perimeter_lt_one` and
  `TauCeti.Real.one_le_perimeter_of_ordConnected`: a null-measurable set on an open interval
  `Ω ⊆ ℝ` of perimeter strictly less than `1` in `Ω` is either null or conull there (equivalently,
  charging both itself and its complement in `Ω` forces perimeter at least `1`).

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §5.10 (functions of bounded variation of one variable).
* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, §3.2 (pointwise and essential variation in one variable).
-/

public section

open Filter Set MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal RealInnerProductSpace

namespace TauCeti.Real

/-- Monotone Lebesgue points of the indicator of a measurable set `s` bound its perimeter from
below by the number of alternations between `s` and its complement. -/
private theorem ofReal_sum_le_perimeter {s : Set ℝ} (hs : MeasurableSet s) {m : ℕ}
    {x : Fin (m + 1) → ℝ} (hx : Monotone x)
    (hxs : ∀ i, Tendsto (fun r => ⨍ y in closedBall (x i) r,
      ‖s.indicator 1 y - s.indicator (1 : ℝ → ℝ) (x i)‖) (𝓝[>] 0) (𝓝 0)) :
    ENNReal.ofReal (∑ i : Fin m,
      |s.indicator 1 (x i.succ) - s.indicator (1 : ℝ → ℝ) (x i.castSucc)|)
      ≤ perimeter volume ⊤ s := by
  have hu : LocallyIntegrableOn (s.indicator (1 : ℝ → ℝ)) ((⊤ : Opens ℝ) : Set ℝ) := by
    rw [Pi.one_def]
    exact ((locallyIntegrable_const 1).indicator hs).locallyIntegrableOn _
  rw [perimeter_def]
  exact ofReal_sum_abs_sub_le_totalVariationOn (v := fun i => s.indicator 1 (x i)) hu hx
    (by simp) hxs

/-- A null-measurable set agrees almost everywhere with a measurable set of the same perimeter
and measure. -/
private theorem exists_measurableSet_ae_eq {s : Set ℝ} (hs : NullMeasurableSet s) :
    ∃ t, MeasurableSet t ∧ s =ᵐ[volume] t ∧ perimeter volume ⊤ s = perimeter volume ⊤ t ∧
      volume s = volume t :=
  ⟨toMeasurable volume s, measurableSet_toMeasurable _ _, hs.toMeasurable_ae_eq.symm,
    perimeter_congr_ae (ae_restrict_of_ae hs.toMeasurable_ae_eq.symm),
    (measure_toMeasurable s).symm⟩

/-- A set `s ⊆ ℝ` of finite measure has a complement of infinite measure in each ray, so a property
holding almost everywhere holds at some point outside `s` to the left of `b` and at some point
outside `s` to the right of `b'`. -/
private theorem exists_notMem_lt_and_gt {s : Set ℝ} (hfin : volume s ≠ ∞) {P : ℝ → Prop}
    (hP : ∀ᵐ x, P x) (b b' : ℝ) : (∃ a < b, a ∉ s ∧ P a) ∧ ∃ c > b', c ∉ s ∧ P c := by
  obtain ⟨a, ⟨hab, has⟩, ha⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae (s := Iio b \ s)
    (by rw [measure_sdiff_eq_top Real.volume_Iio hfin]; exact ENNReal.top_ne_zero)
    (ae_restrict_of_ae hP)
  obtain ⟨c, ⟨hb'c, hcs⟩, hc⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae (s := Ioi b' \ s)
    (by rw [measure_sdiff_eq_top Real.volume_Ioi hfin]; exact ENNReal.top_ne_zero)
    (ae_restrict_of_ae hP)
  exact ⟨⟨a, hab, has, ha⟩, c, hb'c, hcs, hc⟩

private theorem two_le_perimeter_of_measurableSet {s : Set ℝ} (hs : MeasurableSet s)
    (h0 : volume s ≠ 0) (hfin : volume s ≠ ∞) : 2 ≤ perimeter volume ⊤ s := by
  have hae := IsUnifLocDoublingMeasure.ae_tendsto_average_closedBall_norm_sub volume
    (f := s.indicator (1 : ℝ → ℝ)) ((locallyIntegrable_const 1).indicator hs)
  -- A Lebesgue point of `s`, with Lebesgue points of the complement on either side.
  obtain ⟨b, hbs, hb⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae h0 (ae_restrict_of_ae hae)
  obtain ⟨⟨a, hab, has, ha⟩, c, hbc, hcs, hc⟩ := exists_notMem_lt_and_gt hfin hae b b
  have h := ofReal_sum_le_perimeter hs (x := ![a, b, c])
    (Fin.monotone_iff_le_succ.2 fun i => by fin_cases i <;> simp [hab.le, hbc.le])
    (fun i => by fin_cases i <;> assumption)
  simpa [Fin.sum_univ_succ, has, hbs, hcs, one_add_one_eq_two] using h

private theorem four_le_perimeter_of_measurableSet {s : Set ℝ} (hs : MeasurableSet s)
    (hfin : volume s ≠ ∞) (h : ∀ I : Set ℝ, I.OrdConnected → ¬s =ᵐ[volume] I) :
    4 ≤ perimeter volume ⊤ s := by
  set P : ℝ → Prop := fun x => Tendsto (fun r => ⨍ y in closedBall x r,
    ‖s.indicator 1 y - s.indicator (1 : ℝ → ℝ) x‖) (𝓝[>] 0) (𝓝 0)
  have hae := IsUnifLocDoublingMeasure.ae_tendsto_average_closedBall_norm_sub volume
    (f := s.indicator (1 : ℝ → ℝ)) ((locallyIntegrable_const 1).indicator hs)
  have hnull : volume {x | ¬P x} = 0 := ae_iff.1 hae
  -- Two Lebesgue points of `s` separated by a Lebesgue point of its complement.
  obtain ⟨b, z, b', hbz, hzb', hbs, hb, hzs, hz, hb's, hb'⟩ :
      ∃ b z b', b < z ∧ z < b' ∧ b ∈ s ∧ P b ∧ z ∉ s ∧ P z ∧ b' ∈ s ∧ P b' := by
    by_contra! hcon
    -- Otherwise `s` agrees a.e. with the interval spanned by its Lebesgue points.
    set I : Set ℝ := {y | ∃ b ∈ s, P b ∧ ∃ b' ∈ s, P b' ∧ b ≤ y ∧ y ≤ b'}
    have hI : I.OrdConnected := ⟨fun y₁ ⟨b, hbs, hb, _, _, _, hby, _⟩ y₂
      ⟨_, _, _, b', hb's, hb', _, hyb'⟩ y hy =>
        ⟨b, hbs, hb, b', hb's, hb', hby.trans hy.1, hy.2.trans hyb'⟩⟩
    have h₁ : s \ I ⊆ {x | ¬P x} := fun y ⟨hys, hyI⟩ hy =>
      hyI ⟨y, hys, hy, y, hys, hy, le_rfl, le_rfl⟩
    have h₂ : I \ s ⊆ {x | ¬P x} := fun y ⟨⟨b, hbs, hb, b', hb's, hb', hby, hyb'⟩, hys⟩ hy =>
      hcon b y b' (lt_of_le_of_ne hby (ne_of_mem_of_not_mem hbs hys))
        (lt_of_le_of_ne hyb' (ne_of_mem_of_not_mem hb's hys).symm) hbs hb hys hy hb's hb'
    exact h I hI (ae_eq_set.2 ⟨measure_mono_null h₁ hnull, measure_mono_null h₂ hnull⟩)
  -- Lebesgue points of the complement on either side.
  obtain ⟨⟨a, hab, has, ha⟩, c, hb'c, hcs, hc⟩ := exists_notMem_lt_and_gt hfin hae b b'
  have h := ofReal_sum_le_perimeter hs (x := ![a, b, z, b', c])
    (Fin.monotone_iff_le_succ.2 fun i => by
      fin_cases i <;> simp [hab.le, hbz.le, hzb'.le, hb'c.le])
    (fun i => by fin_cases i <;> assumption)
  have h4 : (1 + (1 + (1 + 1)) : ℝ) = 4 := by norm_num
  simpa [Fin.sum_univ_succ, has, hbs, hzs, hb's, hcs, h4] using h

/-- **The isoperimetric inequality on the line.** A null-measurable set of positive finite measure
in `ℝ` has perimeter at least two. -/
theorem two_le_perimeter {s : Set ℝ} (hs : NullMeasurableSet s) (h0 : volume s ≠ 0)
    (hfin : volume s ≠ ∞) : 2 ≤ perimeter volume ⊤ s := by
  obtain ⟨t, ht, -, hst, hvol⟩ := exists_measurableSet_ae_eq hs
  rw [hvol] at h0 hfin
  exact hst ▸ two_le_perimeter_of_measurableSet ht h0 hfin

/-- A null-measurable set of finite measure in `ℝ` that does not agree almost everywhere with any
interval has perimeter at least four. -/
theorem four_le_perimeter {s : Set ℝ} (hs : NullMeasurableSet s) (hfin : volume s ≠ ∞)
    (h : ∀ I : Set ℝ, I.OrdConnected → ¬s =ᵐ[volume] I) : 4 ≤ perimeter volume ⊤ s := by
  obtain ⟨t, ht, hst, hP, hvol⟩ := exists_measurableSet_ae_eq hs
  rw [hvol] at hfin
  exact hP ▸ four_le_perimeter_of_measurableSet ht hfin fun I hI hI' => h I hI (hst.trans hI')

/-- A bounded open interval of `ℝ` has perimeter two. -/
theorem perimeter_Ioo {a b : ℝ} (hab : a < b) : perimeter volume ⊤ (Ioo a b) = 2 := by
  refine le_antisymm ?_ (two_le_perimeter measurableSet_Ioo.nullMeasurableSet (by simp [hab])
    (by simp))
  rw [perimeter_def, totalVariationOn_le_iff]
  intro φ hφ
  have hdiff : Differentiable ℝ φ := φ.contDiff.differentiable (by simp)
  have hint : ∫ x, TestFunction.divergenceCLM φ x * (Ioo a b).indicator 1 x = φ b - φ a := by
    simp_rw [TestFunction.divergenceCLM_apply_eq_deriv, ← indicator_mul_right, Pi.one_apply,
      mul_one]
    rw [integral_indicator measurableSet_Ioo, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hab.le, intervalIntegral.integral_deriv_eq_sub
        (fun x _ => hdiff x) ((φ.contDiff.continuous_deriv (by simp)).intervalIntegrable _ _)]
  rw [hint, ← ENNReal.ofReal_ofNat 2]
  refine ENNReal.ofReal_le_ofReal ?_
  have ha := hφ a
  have hb := hφ b
  rw [Real.norm_eq_abs, abs_le] at ha hb
  linarith

/-- **The perimeter of a half-line ending at a point**: by `TauCeti.perimeter_setOf_inner_lt`, the
perimeter of `(-∞, x)` in an open set `Ω` is `1` if `x ∈ Ω` and `0` otherwise. -/
@[simp]
theorem perimeter_Iio (x : ℝ) (Ω : Opens ℝ) :
    perimeter volume Ω (Iio x) = (Ω : Set ℝ).indicator 1 x := by
  have h := perimeter_setOf_inner_lt (F := ℝ) (ν := 1) (by simp) x Ω
  have hlt : {y : ℝ | ⟪y, (1 : ℝ)⟫ < x} = Iio x := by ext y; simp
  have heq : {y : ℝ | ⟪y, (1 : ℝ)⟫ = x} = {x} := by ext y; simp
  rw [hlt, heq] at h
  by_cases hx : x ∈ (Ω : Set ℝ) <;> simpa [hx] using h

/-- **The perimeter of a half-line starting at a point**: the perimeter of `(x, ∞)` in an open
set `Ω` is `1` if `x ∈ Ω` and `0` otherwise. -/
@[simp]
theorem perimeter_Ioi (x : ℝ) (Ω : Opens ℝ) :
    perimeter volume Ω (Ioi x) = (Ω : Set ℝ).indicator 1 x := by
  rw [← compl_Iic, perimeter_compl, perimeter_congr_ae (ae_restrict_of_ae Iio_ae_eq_Iic.symm)]
  exact perimeter_Iio x Ω

/-- **Equality in the isoperimetric inequality on the line.** A null-measurable set of finite
measure in `ℝ` has perimeter two exactly when it agrees almost everywhere with a nonempty bounded
open interval. -/
theorem perimeter_eq_two_iff {s : Set ℝ} (hs : NullMeasurableSet s) (hfin : volume s ≠ ∞) :
    perimeter volume ⊤ s = 2 ↔ ∃ a b, a < b ∧ s =ᵐ[volume] Ioo a b := by
  refine ⟨fun h2 => ?_, fun ⟨a, b, hab, hsab⟩ => ?_⟩
  · -- A null set has perimeter zero, and otherwise a perimeter below four forces an interval.
    have h0 : volume s ≠ 0 := fun h0 => by
      rw [perimeter_congr_ae (ae_restrict_of_ae (ae_eq_empty.2 h0)), perimeter_empty] at h2
      norm_num at h2
    by_contra! hne
    refine absurd (four_le_perimeter hs hfin fun I hI hsI => ?_) (by rw [h2]; norm_num)
    obtain ⟨a, b, hab, hIab⟩ := hI.exists_ae_eq_Ioo ((measure_congr hsI).symm ▸ h0)
      ((measure_congr hsI).symm ▸ hfin)
    exact hne a b hab (hsI.trans hIab)
  · rw [perimeter_congr_ae (ae_restrict_of_ae hsab), perimeter_Ioo hab]

/-- A null-measurable set of finite length has perimeter at most two exactly when it agrees
almost everywhere with an interval, possibly empty. -/
theorem perimeter_le_two_iff {s : Set ℝ} (hs : NullMeasurableSet s) (hfin : volume s ≠ ∞) :
    perimeter volume ⊤ s ≤ 2 ↔ ∃ I : Set ℝ, I.OrdConnected ∧ s =ᵐ[volume] I := by
  refine ⟨fun hP ↦ ?_, fun ⟨I, hI, hsI⟩ ↦ ?_⟩
  · by_contra! hbad
    have hfour := four_le_perimeter hs hfin hbad
    have : (4 : ℝ≥0∞) ≤ 2 := hfour.trans hP
    norm_num at this
  · by_cases hzero : volume s = 0
    · rw [perimeter_congr_ae (ae_restrict_of_ae (ae_eq_empty.mpr hzero)), perimeter_empty]
      exact zero_le
    · obtain ⟨a, b, hab, hIab⟩ := hI.exists_ae_eq_Ioo
        ((measure_congr hsI).symm ▸ hzero) ((measure_congr hsI).symm ▸ hfin)
      exact (perimeter_eq_two_iff hs hfin).mpr ⟨a, b, hab, hsI.trans hIab⟩ |>.le

/-- **Local constancy below unit perimeter.** If a set `s ⊆ ℝ` is null-measurable on an open
interval `Ω ⊆ ℝ` and has perimeter strictly less than `1` in `Ω`, then either `s ∩ Ω` or
`Ω \ s` has measure zero. -/
theorem measure_inter_eq_zero_or_sdiff_eq_zero_of_perimeter_lt_one {Ω : Opens ℝ}
    (hΩ : (Ω : Set ℝ).OrdConnected) {s : Set ℝ} (hs : NullMeasurableSet s (volume.restrict Ω))
    (hP : perimeter volume Ω s < 1) :
    volume (s ∩ Ω) = 0 ∨ volume ((Ω : Set ℝ) \ s) = 0 := by
  have hsI : NullMeasurableSet (s ∩ Ω) volume :=
    (nullMeasurableSet_restrict Ω.isOpen.measurableSet.nullMeasurableSet).1 hs
  set t := toMeasurable volume (s ∩ Ω)
  have ht : MeasurableSet t := measurableSet_toMeasurable _ _
  have hst : (s ∩ Ω : Set ℝ) =ᵐ[volume] t := hsI.toMeasurable_ae_eq.symm
  have hstI : s =ᵐ[volume.restrict Ω] t :=
    eventuallyEqSet_iff.2 ((ae_restrict_iff' Ω.isOpen.measurableSet).2
      ((eventuallyEqSet_iff.1 hst).mono fun _ hy hyI => by simpa [hyI] using hy))
  have h1eq : volume (s ∩ Ω) = volume (t ∩ Ω) := by
    simpa [inter_assoc] using measure_congr (hst.inter (.refl _ (Ω : Set ℝ)))
  have h0eq : volume ((Ω : Set ℝ) \ s) = volume ((Ω : Set ℝ) \ t) := by
    have hdiff : (Ω : Set ℝ) \ (s ∩ Ω) = (Ω : Set ℝ) \ s := by ext y; simp
    rw [← hdiff]
    exact measure_congr ((Filter.EventuallyEqSet.refl _ (Ω : Set ℝ)).diff hst)
  -- Otherwise Lebesgue points of `t` and of its complement in `Ω` contribute at least `1`
  -- to the total variation on `Ω`.
  by_contra! hne
  have hae := IsUnifLocDoublingMeasure.ae_tendsto_average_closedBall_norm_sub volume
    (f := t.indicator (1 : ℝ → ℝ)) ((locallyIntegrable_const 1).indicator ht)
  obtain ⟨y₁, ⟨hy₁t, hy₁I⟩, hy₁⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae (s := t ∩ Ω)
    (h1eq ▸ hne.1) (ae_restrict_of_ae hae)
  obtain ⟨y₀, ⟨hy₀I, hy₀t⟩, hy₀⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (s := (Ω : Set ℝ) \ t) (h0eq ▸ hne.2) (ae_restrict_of_ae hae)
  simp only [indicator_of_mem hy₁t, Pi.one_apply] at hy₁
  simp only [indicator_of_notMem hy₀t] at hy₀
  have hu : LocallyIntegrableOn (t.indicator (1 : ℝ → ℝ)) Ω volume := by
    rw [Pi.one_def]
    exact ((locallyIntegrable_const 1).indicator ht).locallyIntegrableOn _
  have hle1 : (1 : ℝ≥0∞) ≤ perimeter volume Ω s := by
    rw [perimeter_congr_ae hstI, perimeter_def]
    simpa using ofReal_abs_sub_le_totalVariationOn hu (hΩ.uIcc_subset hy₀I hy₁I) hy₀ hy₁
  exact (not_le_of_gt hP) hle1

/-- **A local lower bound for the perimeter on the line.** A set `s ⊆ ℝ`, null-measurable in an
open interval `V`, that charges both itself and its complement in `V` has perimeter at least one
in `V`. -/
theorem one_le_perimeter_of_ordConnected {s : Set ℝ} {V : Opens ℝ}
    (hs : NullMeasurableSet s (volume.restrict V)) (hV : (V : Set ℝ).OrdConnected)
    (h1 : volume (s ∩ V) ≠ 0) (h0 : volume (sᶜ ∩ V) ≠ 0) : 1 ≤ perimeter volume V s := by
  by_contra! hlt
  rcases measure_inter_eq_zero_or_sdiff_eq_zero_of_perimeter_lt_one hV hs hlt with h | h
  · exact h1 h
  · exact h0 (by simpa only [sdiff_eq_compl_inter, inter_comm] using h)

end TauCeti.Real
