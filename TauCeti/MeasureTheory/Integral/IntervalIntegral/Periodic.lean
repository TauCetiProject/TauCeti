/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import TauCeti.Topology.Instances.AddCircle.Lift

import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import TauCeti.MeasureTheory.Function.Jacobian
import TauCeti.MeasureTheory.Integral.OddSymmetric

/-!
# Pushforwards of Haar measure along circle diffeomorphisms

Let `φ : AddCircle T → AddCircle T` be the map of the circle with lift `F : ℝ → ℝ`, so that
`F (x + T) = F x + T` and `φ x = F x` for every real `x`
(`TauCeti/Topology/Instances/AddCircle/Lift.lean`). When `F` is differentiable with
`c ≤ F' ≤ M` for constants `0 < c ≤ M`, the map `φ` distorts measure only by bounded factors:
`φ` pushes Haar measure forward to at most `c⁻¹` times Haar measure, and the inverse of `φ`
pushes Haar measure forward to at most `M` times Haar measure. These are the bounds which make
precomposition with an orientation-preserving diffeomorphism of the circle a bounded isomorphism
of `L²` of the circle (`MeasureTheory.eLpNorm_comp_le_of_map_le_smul`).

The proof reads the measure of the circle on the fundamental interval `(0, T]`, which `F` maps
onto the fundamental interval `(F 0, F 0 + T]`, and applies the change of variables formula
`map_withDensity_abs_det_fderiv_eq_addHaar` there.

The same reading on a fundamental domain shows that maps of `AddCircle T × Y` lifted from
measure-preserving maps `f` of `ℝ × Y` commuting with `(s, y) ↦ (s + T, y)` preserve
`volume.prod ν`: both `(0, T] × Y` and its preimage under `f` are fundamental domains of these
translations, and an invariant set has the same measure in both.

The file also collects facts about interval integrals of periodic functions on `ℝ`, among them
the integrals of an even `T`-periodic function `f` over whole periods. Such a function is
determined by its values on `[0, T/2]`: the reflection `x ↦ T - x` carries `[0, T/2]` to
`[T/2, T]` and preserves `f`, so integrability on `[0, T/2]` gives integrability over a period;
and the integral over `[-T/2, T/2]`, which is the integral over a period, is twice the integral
over `[0, T/2]` (`intervalIntegral.integral_eq_two_smul_of_even`). If `T ≠ 0` and `f` is not
integrable on `[0, T/2]`, then `f` is not integrable from `t` to `t + n T` for any integer
`n ≠ 0`, and both sides of these identities are `0`.

## Main declarations

* `AddCircle.map_volume_le_of_lift` and `AddCircle.map_haarAddCircle_le_of_lift`: if `c ≤ F'`
  with `c > 0`, then `φ` pushes the measure of the circle forward to at most `c⁻¹` times itself.
* `AddCircle.volume_le_smul_map_volume_of_lift`: if `0 < F' ≤ M`, then the measure of the
  circle is at most `M` times its pushforward along `φ`.
* `AddCircle.map_volume_le_of_lift_of_leftInverse` and
  `AddCircle.map_haarAddCircle_le_of_lift_of_leftInverse`: if `0 < F' ≤ M`, then a left
  inverse of `φ` pushes the measure of the circle forward to at most `M` times itself.
* `AddCircle.integral_deriv_smul_comp_of_lift` and
  `AddCircle.integral_haarAddCircle_deriv_smul_comp_of_lift`: the change of variables formula
  `∫ F' x • g (φ x) dx = ∫ g x dx` over the circle, for a lift with nonnegative derivative.
* `AddCircle.measurable_of_lift`: a map of `AddCircle T × Y` lifted from a measurable map of
  `ℝ × Y` is measurable.
* `AddCircle.measurePreserving_of_lift`: a measure-preserving map of `ℝ × Y` commuting with the
  translation by `T` of the first coordinate descends to a measure-preserving map of
  `AddCircle T × Y`.
* `Function.Periodic.eqOn_zero_of_intervalIntegral_eq_zero`: a continuous periodic function which
  is nonnegative over a period and has integral zero over a period vanishes inside that period.
* `Function.Periodic.intervalIntegral_neg_div_two_eq`: the integral of a `T`-periodic function
  over `[-T/2, T/2]` is its integral over `[0, T]`.
* `Function.Periodic.intervalIntegrable_of_even`: an even `T`-periodic function (`T ≠ 0`) which is
  interval integrable on `[0, T/2]` is interval integrable on every interval.
* `Function.Periodic.intervalIntegral_add_zsmul_eq'`: Mathlib's
  `Function.Periodic.intervalIntegral_add_zsmul_eq` without its integrability hypothesis.
* `Function.Periodic.intervalIntegral_eq_two_smul_of_even` and
  `Function.Periodic.intervalIntegral_add_int_mul_eq_of_even`: an even `T`-periodic function
  integrates from `0` to `T` to twice, and from `t` to `t + n T` to `2 n` times, its integral from
  `0` to `T / 2`, with no integrability hypothesis.
* `Function.Periodic.intervalIntegral_add_int_mul_eq_add_of_even`: quasi-periodicity of the
  integral of an even `T`-periodic function which is interval integrable on `[0, T/2]`.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace AddCircle

variable {T : ℝ} [hT : Fact (0 < T)] {φ : AddCircle T → AddCircle T} {F F' : ℝ → ℝ}

/-- Haar measure on the circle is the measure of the circle divided by its length `T`. -/
theorem haarAddCircle_eq_smul_volume :
    (haarAddCircle : Measure (AddCircle T)) = (ENNReal.ofReal T)⁻¹ • volume := by
  rw [volume_eq_smul_haarAddCircle, smul_smul, ENNReal.inv_mul_cancel
    (ENNReal.ofReal_pos.2 hT.out).ne' ENNReal.ofReal_ne_top, one_smul]

section Pushforward

variable (hF : ∀ x, HasDerivAt F (F' x) x) (hper : ∀ x, F (x + T) = F x + T)
  (hφ : ∀ x : ℝ, φ x = F x)
include hF hper hφ

omit hper in
/-- Pushing the measure of the circle forward along `φ` is pushing Lebesgue measure on `(0, T]`
forward along the lift `F`, and then to the circle. -/
private theorem map_volume_eq_of_lift :
    (volume : Measure (AddCircle T)).map φ =
      ((volume.restrict (Ioc 0 T)).map F).map ((↑) : ℝ → AddCircle T) := by
  have hFc : Continuous F := continuous_iff_continuousAt.2 fun x ↦ (hF x).continuousAt
  rw [← (AddCircle.measurePreserving_mk T 0).map_eq, zero_add,
    Measure.map_map (continuous_of_lift hFc hφ).measurable AddCircle.measurable_mk',
    Measure.map_map AddCircle.measurable_mk' hFc.measurable]
  congr 1
  funext x
  simp [hφ]

/-- **Pushforward bound for a circle map with derivative bounded below.** If the lift `F` of `φ`
satisfies `c ≤ F'` with `c > 0`, then `φ` pushes the measure of the circle forward to at most `c⁻¹`
times itself. -/
theorem map_volume_le_of_lift {c : ℝ} (hc : 0 < c) (hcF : ∀ x, c ≤ F' x) :
    (volume : Measure (AddCircle T)).map φ ≤ (ENNReal.ofReal c)⁻¹ • volume := by
  have hmono : StrictMono F := strictMono_of_hasDerivAt_pos hF fun x ↦ hc.trans_le (hcF x)
  rw [map_volume_eq_of_lift hF hφ, ← (AddCircle.measurePreserving_mk T (F 0)).map_eq,
    ← Measure.map_smul _ AddCircle.measurable_mk'.aemeasurable]
  refine Measure.map_mono ?_ AddCircle.measurable_mk'
  refine (map_restrict_le_smul_restrict_image volume measurableSet_Ioc.nullMeasurableSet
    (fun x _ ↦ (hF x).hasFDerivAt.hasFDerivWithinAt) hmono.injective.injOn hc
    (fun x _ ↦ by simpa using (hcF x).trans (le_abs_self _))).trans ?_
  gcongr
  exact image_Ioc_subset_of_lift hmono hper

/-- **Reverse pushforward bound for a circle map with derivative bounded above.** If the lift `F`
of `φ` satisfies `0 < F' ≤ M`, then the measure of the circle is at most `M` times its pushforward
along `φ`. -/
theorem volume_le_smul_map_volume_of_lift (hpos : ∀ x, 0 < F' x) {M : ℝ} (hMF : ∀ x, F' x ≤ M) :
    (volume : Measure (AddCircle T)) ≤
      ENNReal.ofReal M • (volume : Measure (AddCircle T)).map φ := by
  have hmono : StrictMono F := strictMono_of_hasDerivAt_pos hF hpos
  have hFc : Continuous F := continuous_iff_continuousAt.2 fun x ↦ (hF x).continuousAt
  rw [map_volume_eq_of_lift hF hφ, ← Measure.map_smul _ AddCircle.measurable_mk'.aemeasurable,
    ← (AddCircle.measurePreserving_mk T (F 0)).map_eq, ← image_Ioc_of_lift hmono hFc hper,
    ← map_withDensity_abs_det_fderiv_eq_addHaar volume measurableSet_Ioc.nullMeasurableSet
      (fun x _ ↦ (hF x).hasFDerivAt.hasFDerivWithinAt) hmono.injective.injOn,
    ← Measure.map_smul _ hFc.measurable.aemeasurable, ← withDensity_const]
  refine Measure.map_mono (Measure.map_mono (withDensity_mono (Filter.Eventually.of_forall
    fun x ↦ ?_)) hFc.measurable) AddCircle.measurable_mk'
  simpa [abs_of_pos (hpos x)] using ENNReal.ofReal_le_ofReal (hMF x)

/-- If the lift `F` of `φ` has positive derivative, every left inverse `ψ` of `φ` is measurable:
it is the inverse of the homeomorphism of the circle presented by `F`. -/
private theorem measurable_of_lift_of_leftInverse (hpos : ∀ x, 0 < F' x)
    {ψ : AddCircle T → AddCircle T} (hψφ : Function.LeftInverse ψ φ) : Measurable ψ := by
  have hmono : StrictMono F := strictMono_of_hasDerivAt_pos hF hpos
  have hFc : Continuous F := continuous_iff_continuousAt.2 fun x ↦ (hF x).continuousAt
  rw [eq_homeomorphOfLift_symm_of_leftInverse hmono hFc hper hφ hψφ]
  exact (homeomorphOfLift φ hmono hFc hper hφ).symm.continuous.measurable

/-- If the lift `F` of `φ` satisfies `0 < F' ≤ M` and `ψ` is a left inverse of `φ`, then `ψ` pushes
the measure of the circle forward to at most `M` times itself. -/
theorem map_volume_le_of_lift_of_leftInverse (hpos : ∀ x, 0 < F' x) {M : ℝ}
    (hMF : ∀ x, F' x ≤ M) {ψ : AddCircle T → AddCircle T}
    (hψφ : Function.LeftInverse ψ φ) :
    (volume : Measure (AddCircle T)).map ψ ≤ ENNReal.ofReal M • volume := by
  have hFc : Continuous F := continuous_iff_continuousAt.2 fun x ↦ (hF x).continuousAt
  have hψ := measurable_of_lift_of_leftInverse hF hper hφ hpos hψφ
  calc (volume : Measure (AddCircle T)).map ψ
      ≤ (ENNReal.ofReal M • (volume : Measure (AddCircle T)).map φ).map ψ :=
        Measure.map_mono (volume_le_smul_map_volume_of_lift hF hper hφ hpos hMF) hψ
    _ = ENNReal.ofReal M • volume := by
        rw [Measure.map_smul _ hψ.aemeasurable,
          Measure.map_map hψ (continuous_of_lift hFc hφ).measurable, hψφ.comp_eq_id,
          Measure.map_id]

/-- The `haarAddCircle` form of `AddCircle.map_volume_le_of_lift`. -/
theorem map_haarAddCircle_le_of_lift {c : ℝ} (hc : 0 < c) (hcF : ∀ x, c ≤ F' x) :
    (haarAddCircle : Measure (AddCircle T)).map φ ≤ (ENNReal.ofReal c)⁻¹ • haarAddCircle := by
  have hFc : Continuous F := continuous_iff_continuousAt.2 fun x ↦ (hF x).continuousAt
  rw [haarAddCircle_eq_smul_volume, Measure.map_smul _
    (continuous_of_lift hFc hφ).measurable.aemeasurable, smul_comm]
  gcongr
  exact map_volume_le_of_lift hF hper hφ hc hcF

/-- The `haarAddCircle` form of `AddCircle.map_volume_le_of_lift_of_leftInverse`. -/
theorem map_haarAddCircle_le_of_lift_of_leftInverse (hpos : ∀ x, 0 < F' x) {M : ℝ}
    (hMF : ∀ x, F' x ≤ M) {ψ : AddCircle T → AddCircle T}
    (hψφ : Function.LeftInverse ψ φ) :
    (haarAddCircle : Measure (AddCircle T)).map ψ ≤ ENNReal.ofReal M • haarAddCircle := by
  have hψ := measurable_of_lift_of_leftInverse hF hper hφ hpos hψφ
  rw [haarAddCircle_eq_smul_volume,
    Measure.map_smul _ hψ.aemeasurable,
    smul_comm]
  gcongr
  exact map_volume_le_of_lift_of_leftInverse hF hper hφ hpos hMF hψφ

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Change of variables along a circle map.** If the lift `F` of `φ` has nonnegative derivative
`F'`, read on the circle as `f'`, then `∫ f' x • g (φ x) dx = ∫ g x dx` over the circle, for every
function `g`. -/
theorem integral_deriv_smul_comp_of_lift (hpos : ∀ x, 0 ≤ F' x) {f' : AddCircle T → ℝ}
    (hf' : ∀ x : ℝ, f' x = F' x) (g : AddCircle T → E) :
    ∫ x, f' x • g (φ x) = ∫ x, g x := by
  have hFc : Continuous F := continuous_iff_continuousAt.2 fun x ↦ (hF x).continuousAt
  rw [← AddCircle.intervalIntegral_preimage T 0, ← AddCircle.intervalIntegral_preimage T (F 0),
    ← hper, zero_add]
  simp only [hf', hφ]
  exact intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg (g := fun y : ℝ ↦ g y)
    hFc.continuousOn (fun x _ ↦ hF x) fun x _ ↦ hpos x

/-- The `haarAddCircle` form of `AddCircle.integral_deriv_smul_comp_of_lift`. -/
theorem integral_haarAddCircle_deriv_smul_comp_of_lift (hpos : ∀ x, 0 ≤ F' x)
    {f' : AddCircle T → ℝ} (hf' : ∀ x : ℝ, f' x = F' x) (g : AddCircle T → E) :
    ∫ x, f' x • g (φ x) ∂haarAddCircle = ∫ x, g x ∂haarAddCircle := by
  rw [haarAddCircle_eq_smul_volume, integral_smul_measure, integral_smul_measure,
    integral_deriv_smul_comp_of_lift hF hper hφ hpos hf' g]

end Pushforward

section Descent

variable {Y : Type*} [MeasurableSpace Y] {ν : Measure Y}

/-- The action of `ℤ` on `ℝ × Y` by translating the first coordinate by multiples of `T`. -/
private abbrev translateAction (T : ℝ) (Y : Type*) : AddAction ℤ (ℝ × Y) where
  vadd n x := (x.1 + n • T, x.2)
  zero_vadd x := by simp [HVAdd.hVAdd]
  add_vadd m n x := by
    simp only [HVAdd.hVAdd, Prod.mk.injEq, and_true]
    rw [add_zsmul]
    ring

omit hT [MeasurableSpace Y] in
/-- A map commuting with the translation by `T` of the first coordinate commutes with the
translations by all integer multiples of `T`. -/
private theorem apply_add_zsmul {f : ℝ × Y → ℝ × Y}
    (hf : ∀ x : ℝ × Y, f (x.1 + T, x.2) = ((f x).1 + T, (f x).2)) (n : ℤ) (x : ℝ × Y) :
    f (x.1 + n • T, x.2) = ((f x).1 + n • T, (f x).2) := by
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih =>
    have h := hf (x.1 + (n : ℤ) • T, x.2)
    rw [ih] at h
    rw [add_one_zsmul, ← add_assoc, h, add_assoc]
  | pred n ih =>
    have h := hf (x.1 + (-(n : ℤ) - 1) • T, x.2)
    rw [add_assoc, ← add_one_zsmul, sub_add_cancel, ih, Prod.ext_iff] at h
    refine Prod.ext ?_ h.2.symm
    have hs : (-(n : ℤ) - 1) • T = -(n : ℤ) • T - T := by rw [sub_zsmul, one_zsmul]; abel
    linarith [h.1]

/-- A map of `AddCircle T × Y` lifted from a measurable map of `ℝ × Y` is measurable. -/
theorem measurable_of_lift {f : ℝ × Y → ℝ × Y} (hf : Measurable f)
    {g : AddCircle T × Y → AddCircle T × Y}
    (hg : ∀ x : ℝ × Y, g ((x.1 : AddCircle T), x.2) = (((f x).1 : AddCircle T), (f x).2)) :
    Measurable g := by
  -- `g = π ∘ f ∘ σ` for the measurable section `σ` of the projection `π` with values in
  -- `(0, T] × Y`.
  have hσ : Measurable fun z : AddCircle T × Y ↦ ((equivIoc T 0 z.1 : ℝ), z.2) :=
    ((measurable_subtypeVal.comp (measurableEquivIoc T 0).measurable).comp
      measurable_fst).prodMk measurable_snd
  convert (AddCircle.measurable_mk'.prodMap measurable_id).comp (hf.comp hσ) using 1
  funext ⟨θ, y⟩
  simpa [Prod.map] using hg ((equivIoc T 0 θ : ℝ), y)

/-- **Descent of measure-preserving maps to `AddCircle T × Y`.** Let `f` be a map of `ℝ × Y`
preserving `volume.prod ν` and commuting with the translation `(s, y) ↦ (s + T, y)`. Then the map
`g` it induces on `AddCircle T × Y`, characterized by `g ([s], y) = [f (s, y)]`, preserves
`volume.prod ν`. -/
theorem measurePreserving_of_lift [SFinite ν] {f : ℝ × Y → ℝ × Y}
    (hf : MeasurePreserving f (volume.prod ν) (volume.prod ν))
    (hfT : ∀ x : ℝ × Y, f (x.1 + T, x.2) = ((f x).1 + T, (f x).2))
    {g : AddCircle T × Y → AddCircle T × Y}
    (hg : ∀ x : ℝ × Y, g ((x.1 : AddCircle T), x.2) = (((f x).1 : AddCircle T), (f x).2)) :
    MeasurePreserving g (volume.prod ν) (volume.prod ν) := by
  -- Read the measure of a set of `AddCircle T × Y` on the fundamental domain `F = (0, T] × Y` of
  -- the translations, and compare `F` with the second fundamental domain `f ⁻¹' F`.
  set π : ℝ × Y → AddCircle T × Y := Prod.map (↑) id
  have hπm : Measurable π := AddCircle.measurable_mk'.prodMap measurable_id
  have hgπ (x : ℝ × Y) : g (π x) = π (f x) := hg x
  set F : Set (ℝ × Y) := Ioc 0 T ×ˢ univ
  have hFm : MeasurableSet F := measurableSet_Ioc.prod MeasurableSet.univ
  have hπ : MeasurePreserving π ((volume.prod ν).restrict F) (volume.prod ν) := by
    have := (AddCircle.measurePreserving_mk T 0).prod (MeasurePreserving.id ν)
    rwa [zero_add, Measure.restrict_prod_eq_prod_univ] at this
  have hgm := measurable_of_lift hf.measurable hg
  refine ⟨hgm, Measure.ext fun E hE ↦ ?_⟩
  let := translateAction T Y
  have hvadd (n : ℤ) (x : ℝ × Y) : n +ᵥ x = (x.1 + n • T, x.2) := rfl
  have : MeasurableConstVAdd ℤ (ℝ × Y) :=
    ⟨fun n ↦ (measurable_fst.add_const _).prodMk measurable_snd⟩
  have : VAddInvariantMeasure ℤ (ℝ × Y) (volume.prod ν) := ⟨fun n s hs ↦
    ((measurePreserving_add_right volume (n • T)).prod (MeasurePreserving.id ν)).measure_preimage
      hs.nullMeasurableSet⟩
  have hFdom : IsAddFundamentalDomain ℤ F (volume.prod ν) := by
    refine .mk' hFm.nullMeasurableSet fun x ↦ ?_
    simpa [hvadd, F, zero_add] using existsUnique_add_zsmul_mem_Ioc hT.out x.1 0
  have hfF : IsAddFundamentalDomain ℤ (f ⁻¹' F) (volume.prod ν) := by
    refine .mk' (hf.measurable hFm).nullMeasurableSet fun x ↦ ?_
    simp only [mem_preimage, hvadd, apply_add_zsmul hfT]
    simpa [F] using existsUnique_add_zsmul_mem_Ioc hT.out (f x).1 0
  have hπv (n : ℤ) (x : ℝ × Y) : π (n +ᵥ x) = π x := by
    obtain ⟨s, y⟩ := x
    simp [hvadd, π]
  have hinv (S : Set (AddCircle T × Y)) (n : ℤ) :
      (fun x ↦ n +ᵥ x) ⁻¹' (π ⁻¹' S) = π ⁻¹' S := by
    ext x
    simp only [mem_preimage, hπv]
  have hEm : MeasurableSet (π ⁻¹' E) := hπm hE
  rw [Measure.map_apply hgm hE, ← hπ.measure_preimage (hgm hE).nullMeasurableSet,
    ← hπ.measure_preimage hE.nullMeasurableSet, Measure.restrict_apply (hπm (hgm hE)),
    Measure.restrict_apply hEm, hFdom.measure_set_eq hfF (hπm (hgm hE)) (hinv _)]
  have : π ⁻¹' (g ⁻¹' E) ∩ f ⁻¹' F = f ⁻¹' (π ⁻¹' E ∩ F) := by
    ext x
    simp [hgπ]
  rw [this, hf.measure_preimage (hEm.inter hFm).nullMeasurableSet]

end Descent

end AddCircle

/-- A continuous `T`-periodic function which is nonnegative on `[a, a + T]` and whose integral over
a period vanishes, vanishes on `(a, a + T)`. -/
theorem Function.Periodic.eqOn_zero_of_intervalIntegral_eq_zero {f : ℝ → ℝ} {T : ℝ}
    (hper : Function.Periodic f T) (hf : Continuous f) {a : ℝ}
    (hnn : ∀ t ∈ Icc a (a + T), 0 ≤ f t) (hint : ∫ t in 0..T, f t = 0) :
    EqOn f 0 (Ioo a (a + T)) := by
  intro t ht
  have hab : a ≤ a + T := (ht.1.trans ht.2).le
  have hint' : ∫ t in a..a + T, f t = 0 := by
    rw [hper.intervalIntegral_add_eq a 0, zero_add]
    exact hint
  have hzero := (intervalIntegral.integral_eq_zero_iff_of_nonneg_ae
    (ae_restrict_of_forall_mem (measurableSet_Ioc.union measurableSet_Ioc) fun t ht ↦ by
      rcases ht with ht | ht
      · exact hnn t (Ioc_subset_Icc_self ht)
      · exact absurd (ht.1.trans_le ht.2) (not_lt.mpr hab))
    (hf.intervalIntegrable _ _)).mp hint'
  exact Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae_restrict_of_subset
    (fun t ht ↦ Or.inl (Ioo_subset_Ioc_self ht)) hzero) isOpen_Ioo hf.continuousOn
    continuousOn_const ht

/-- By periodicity, the integral of a `T`-periodic function over `[-T/2, T/2]` is its integral
over the period `[0, T]`. -/
theorem Function.Periodic.intervalIntegral_neg_div_two_eq {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ → E} {T : ℝ} (hf : Function.Periodic f T) :
    ∫ t in -T / 2..T / 2, f t = ∫ t in 0..T, f t := by
  have h := hf.intervalIntegral_add_eq (-T / 2) 0
  rwa [zero_add, show -T / 2 + T = T / 2 by ring] at h

namespace Function.Periodic

variable {E : Type*} [NormedAddCommGroup E] {f : ℝ → E} {T : ℝ}

/-- An even `T`-periodic function (`T ≠ 0`) that is interval integrable from `0` to `T / 2` is
interval integrable over every interval. -/
theorem intervalIntegrable_of_even (hper : Periodic f T) (heven : Function.Even f) (hT : T ≠ 0)
    (hf : IntervalIntegrable f volume 0 (T / 2)) (a b : ℝ) : IntervalIntegrable f volume a b := by
  have hfun : (fun x ↦ f (T - x)) = f := funext fun x ↦ by
    rw [sub_eq_neg_add, hper (-x), heven x]
  have h2 : IntervalIntegrable f volume (T / 2) T := by
    have h := hf.comp_sub_left T
    rw [hfun, sub_half, sub_zero] at h
    exact h.symm
  exact hper.intervalIntegrable₀ hT (hf.trans h2) a b

variable [NormedSpace ℝ E]

/-- Version of `Function.Periodic.intervalIntegral_add_zsmul_eq` without the integrability
hypothesis: if `f` is not interval integrable over one period, it is not interval integrable over
`n` periods for `n ≠ 0`, and both sides are `0`. -/
theorem intervalIntegral_add_zsmul_eq' (hper : Periodic f T) (n : ℤ) (t : ℝ) :
    ∫ x in t..t + n • T, f x = n • ∫ x in t..t + T, f x := by
  rcases eq_or_ne T 0 with rfl | hT
  · simp
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  by_cases h : IntervalIntegrable f volume t (t + T)
  · exact hper.intervalIntegral_add_zsmul_eq n t (hper.intervalIntegrable hT h)
  · rw [intervalIntegral.integral_undef h, smul_zero]
    exact intervalIntegral.integral_undef fun hI ↦
      h ((hper.zsmul n).intervalIntegrable (smul_ne_zero hn hT) hI _ _)

/-- An even `T`-periodic function integrates from `0` to `T` to twice its integral from `0` to
`T / 2`; no integrability hypothesis is needed. -/
theorem intervalIntegral_eq_two_smul_of_even (hper : Periodic f T) (heven : Function.Even f) :
    ∫ x in (0 : ℝ)..T, f x = (2 : ℝ) • ∫ x in (0 : ℝ)..T / 2, f x := by
  rw [← hper.intervalIntegral_neg_div_two_eq, neg_div,
    intervalIntegral.integral_eq_two_smul_of_even heven]

/-- An even `T`-periodic function integrates over `n` periods, from `t` to `t + n T`, to `2 n` times
its integral from `0` to `T / 2`; no integrability hypothesis is needed. -/
theorem intervalIntegral_add_int_mul_eq_of_even (hper : Periodic f T) (heven : Function.Even f)
    (t : ℝ) (n : ℤ) :
    ∫ x in t..t + n * T, f x = (2 * (n : ℝ)) • ∫ x in (0 : ℝ)..T / 2, f x := by
  rw [← zsmul_eq_mul, hper.intervalIntegral_add_zsmul_eq' n t, hper.intervalIntegral_add_eq t 0,
    zero_add, hper.intervalIntegral_eq_two_smul_of_even heven, ← Int.cast_smul_eq_zsmul ℝ n,
    smul_smul, mul_comm (n : ℝ) 2]

/-- **Quasi-periodicity** of the integral of an even `T`-periodic function that is interval
integrable from `0` to `T / 2`: adding `n` periods to the upper limit adds `2 n` times the integral
over `[0, T / 2]`. -/
theorem intervalIntegral_add_int_mul_eq_add_of_even (hper : Periodic f T)
    (heven : Function.Even f) (hf : IntervalIntegrable f volume 0 (T / 2)) (a x : ℝ) (n : ℤ) :
    ∫ θ in a..x + n * T, f θ =
      (∫ θ in a..x, f θ) + (2 * (n : ℝ)) • ∫ θ in (0 : ℝ)..T / 2, f θ := by
  rcases eq_or_ne T 0 with rfl | hT
  · simp
  have hint := hper.intervalIntegrable_of_even heven hT hf
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint a x) (hint x _),
    hper.intervalIntegral_add_int_mul_eq_of_even heven x n]

end Function.Periodic
