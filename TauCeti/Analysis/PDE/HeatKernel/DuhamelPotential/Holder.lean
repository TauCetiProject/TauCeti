/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.HeatKernel.DuhamelPotential.Basic
public import TauCeti.Analysis.PDE.HeatKernel.CauchyPotential
import TauCeti.Analysis.PDE.Parabolic.SpaceTime.Holder

/-!
# Parabolic Hölder continuity of the Duhamel potential

For jointly measurable forcing with uniformly bounded, spatially Hölder slices, the Duhamel
heat potential is Hölder on each closed parabolic slab, including the initial slice. No time
regularity of the forcing is required. This supplies the value-field estimate for constructing
the bounded classical solution operator of the inhomogeneous heat equation.

The estimate separates the common integration interval, where the Cauchy potential's parabolic
Hölder estimate `TauCeti.holderWith_heatCauchyPotential` applies, from the remaining interval,
whose length bounds its contribution. For `0 < α < 1`, the spatial Hessian also satisfies a
joint parabolic Hölder estimate, obtained from its separate spatial and temporal estimates.

## References

* A. Friedman, *Partial Differential Equations of Parabolic Type*, Chapter 1, Section 3.
* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004, Chapter 4.
-/

public section
noncomputable section

namespace TauCeti

open MeasureTheory Set Real ParabolicSpaceTime
open scoped NNReal Convolution Interval

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {f : ℝ → E → F} {T M : ℝ} {H α : ℝ≥0}

/-- The Cauchy-potential integrand of the Duhamel potential is integrable on `[0, s]`
for every `s ∈ [0, T]`, even when its elapsed-time argument is nonpositive. -/
theorem intervalIntegrable_heatDuhamelPotential_integrand
    (hf : StronglyMeasurable (Function.uncurry f))
    (hM : ∀ r ∈ Icc 0 T, ∀ y, ‖f r y‖ ≤ M)
    {s : ℝ} (hs : s ∈ Icc 0 T) (t : ℝ) (x : E) :
    IntervalIntegrable (fun r => heatCauchyPotential (f r) (t - r) x) volume 0 s := by
  have hmeas : StronglyMeasurable (fun p : ℝ × E =>
      heatKernel 1 p.2 • f p.1 (x - √(t - p.1) • p.2)) := by
    exact (contDiff_heatKernel 1 (k := 0)).continuous.stronglyMeasurable.comp_measurable
      measurable_snd |>.smul (hf.comp_measurable
        (g := fun p : ℝ × E => (p.1, x - √(t - p.1) • p.2)) (by fun_prop))
  simp_rw [heatCauchyPotential_def]
  refine (intervalIntegrable_const (c := M)).mono_fun'
    (hmeas.integral_prod_right' (ν := volume)).aestronglyMeasurable ?_
  rw [uIoc_of_le hs.1]
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  simpa only [← heatCauchyPotential_def] using
    norm_heatCauchyPotential_le (hM r ⟨hr.1.le, hr.2.trans hs.2⟩) (t - r) x

/-- On nonnegative time slices the Duhamel potential can be integrated using the Cauchy
potential, whose extension to nonpositive elapsed times does not affect the integral. -/
theorem heatDuhamelPotential_eq_integral_heatCauchyPotential {t : ℝ} (ht : 0 ≤ t)
    (x : E) : heatDuhamelPotential f t x =
      ∫ r in 0..t, heatCauchyPotential (f r) (t - r) x := by
  rw [heatDuhamelPotential_def]
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le ht, ← restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  exact (heatCauchyPotential_eq_convolution _ (sub_pos.2 hr.2) x).symm

/-- The contribution of the common integration interval to a difference of Duhamel potentials
is controlled by the parabolic Hölder estimate for the Cauchy potential. -/
private theorem norm_heatDuhamelPotential_sub_le_of_le
    (hf : StronglyMeasurable (Function.uncurry f))
    (hM : ∀ r ∈ Icc 0 T, ∀ y, ‖f r y‖ ≤ M)
    (hH : ∀ r ∈ Icc 0 T, HolderWith H α (f r)) (hα : 0 < α)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ T) (x y : E) :
    ‖heatDuhamelPotential f t x - heatDuhamelPotential f s y‖ ≤
      s * (H * (1 + heatKernelMoment E α)) *
        (dist x y + √|t - s|) ^ (α : ℝ) + M * (t - s) := by
  have hsT : s ∈ Icc 0 T := ⟨hs, hst.trans ht⟩
  have htT : t ∈ Icc 0 T := ⟨hs.trans hst, ht⟩
  have hit := intervalIntegrable_heatDuhamelPotential_integrand hf hM htT t x
  have his := intervalIntegrable_heatDuhamelPotential_integrand hf hM hsT t x
  have hjs := intervalIntegrable_heatDuhamelPotential_integrand hf hM hsT s y
  have hist := his.symm.trans hit
  rw [heatDuhamelPotential_eq_integral_heatCauchyPotential htT.1,
    heatDuhamelPotential_eq_integral_heatCauchyPotential hs,
    ← intervalIntegral.integral_add_adjacent_intervals his hist]
  have heq : (∫ r in 0..s, heatCauchyPotential (f r) (t - r) x) +
      (∫ r in s..t, heatCauchyPotential (f r) (t - r) x) -
      (∫ r in 0..s, heatCauchyPotential (f r) (s - r) y) =
      (∫ r in 0..s, heatCauchyPotential (f r) (t - r) x -
        heatCauchyPotential (f r) (s - r) y) +
      (∫ r in s..t, heatCauchyPotential (f r) (t - r) x) := by
    rw [intervalIntegral.integral_sub his hjs]
    abel
  rw [heq]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (intervalIntegral.norm_integral_le_of_norm_le hs (g := fun _ =>
        (H * (1 + heatKernelMoment E α)) * (dist x y + √|t - s|) ^ (α : ℝ)) ?_
        intervalIntegrable_const).trans_eq (by
          rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
          ring)
    filter_upwards [] with r hr
    have hrT : r ∈ Icc 0 T := ⟨hr.1.le, hr.2.trans hsT.2⟩
    have h := (holderWith_heatCauchyPotential (hH r hrT) ((hH r hrT).continuous hα)).dist_le
      (ofCoords x (t - r)) (ofCoords y (s - r))
    simpa [ParabolicSpaceTime.dist_eq, sub_sub_sub_cancel_right, dist_eq_norm] using h
  · refine (intervalIntegral.norm_integral_le_of_norm_le hst (g := fun _ => M) ?_
        intervalIntegrable_const).trans_eq (by
          rw [intervalIntegral.integral_const, smul_eq_mul]
          ring)
    filter_upwards [] with r hr
    exact norm_heatCauchyPotential_le (hM r ⟨hs.trans hr.1.le, hr.2.trans ht⟩) _ _

/-- A bounded time increment controlled by the squared parabolic distance is also controlled
by its `α` power, for `0 ≤ α ≤ 2`. -/
private theorem time_increment_le_max_mul_rpow {d δ T : ℝ} {α : ℝ≥0}
    (hd : 0 ≤ d) (hsq : δ ≤ d ^ 2) (hT : δ ≤ T) (hα₂ : α ≤ 2) :
    δ ≤ max 1 T * d ^ (α : ℝ) := by
  by_cases hd₁ : d ≤ 1
  · have hα₂' : (α : ℝ) ≤ 2 := by exact_mod_cast hα₂
    have hp : d ^ 2 ≤ d ^ (α : ℝ) := by
      simpa using Real.rpow_le_rpow_of_exponent_ge' hd hd₁ α.coe_nonneg hα₂'
    exact (hsq.trans hp).trans (le_mul_of_one_le_left (by positivity) (le_max_left _ _))
  · have hp : 1 ≤ d ^ (α : ℝ) := Real.one_le_rpow (le_of_not_ge hd₁) α.coe_nonneg
    exact (hT.trans (le_max_right _ _)).trans
      (le_mul_of_one_le_right (le_trans zero_le_one (le_max_left _ _)) hp)

/-- **The value-field parabolic Hölder estimate for the Duhamel potential.** If the forcing
is jointly measurable and its spatial slices on `[0,T]` are bounded by `M` and `α`-Hölder with
constant `H`, where `0 < α ≤ 2`, then its Duhamel potential is parabolically `α`-Hölder on the
closed slab, with constant `T H (1 + M_α) + M max(1,T)`. Here `M_α` is the heat-kernel moment.
No temporal continuity of the forcing is assumed. -/
theorem holderWith_heatDuhamelPotential (hf : StronglyMeasurable (Function.uncurry f))
    {T M : ℝ≥0} (hM : ∀ r ∈ Icc (0 : ℝ) T, ∀ y, ‖f r y‖ ≤ M)
    (hH : ∀ r ∈ Icc (0 : ℝ) T, HolderWith H α (f r)) (hα : 0 < α) (hα₂ : α ≤ 2) :
    HolderWith (T * H * (1 + heatKernelMoment E α) + M * max 1 T) α
      (fun p : slab (E := E) 0 T =>
        heatDuhamelPotential f (p : ParabolicSpaceTime E).time
          (p : ParabolicSpaceTime E).space) := by
  have hordered (s t : Icc (0 : ℝ) T) (hst : (s : ℝ) ≤ t) (x y : E) :
      ‖heatDuhamelPotential f t x - heatDuhamelPotential f s y‖ ≤
        (T * H * (1 + heatKernelMoment E α) + M * max 1 T : ℝ≥0) *
          (dist x y + √|(t : ℝ) - s|) ^ (α : ℝ) := by
    -- The tail interval has length at most both `T` and the square of the parabolic distance.
    set d := dist x y + √|(t : ℝ) - s|
    have hd : 0 ≤ d := by positivity
    have hdiff : 0 ≤ (t : ℝ) - s := sub_nonneg.2 hst
    have hsq : (t : ℝ) - s ≤ d ^ 2 := by
      have hsqrt := Real.sq_sqrt hdiff
      dsimp only [d]
      rw [abs_of_nonneg hdiff]
      nlinarith [dist_nonneg (x := x) (y := y), sqrt_nonneg ((t : ℝ) - s)]
    have htime := time_increment_le_max_mul_rpow hd hsq
      ((sub_le_self _ s.2.1).trans t.2.2) hα₂
    -- Bound the common integration interval by its maximal length `T`.
    refine (norm_heatDuhamelPotential_sub_le_of_le hf hM hH hα s.2.1 hst t.2.2 x y).trans ?_
    push_cast at htime ⊢
    dsimp only [d] at *
    have hnonneg : (0 : ℝ) ≤ H * (1 + heatKernelMoment E α) *
        (dist x y + √|(t : ℝ) - s|) ^ (α : ℝ) := by positivity
    nlinarith [mul_le_mul_of_nonneg_right s.2.2 hnonneg,
      mul_le_mul_of_nonneg_left htime M.coe_nonneg]
  rw [← holderOnWith_univ]
  refine HolderOnWith.of_dist_le fun p _ q _ => ?_
  obtain ⟨x, t, rfl⟩ : ∃ x t, slabMk x t = p := ⟨_, _, slabMk_space_slabTime p⟩
  obtain ⟨y, s, rfl⟩ : ∃ y s, slabMk y s = q := ⟨_, _, slabMk_space_slabTime q⟩
  rw [dist_eq_norm, Subtype.dist_eq, ParabolicSpaceTime.dist_eq]
  simp only [space_slabMk, time_slabMk]
  rcases le_total (s : ℝ) t with hst | hts
  · exact hordered s t hst x y
  · simpa [norm_sub_rev, dist_comm, abs_sub_comm] using hordered t s hts y x

/-- The Hessian of the Duhamel potential is jointly parabolically `α`-Hölder on the closed
slab, for `0 < α < 1`. The constant is independent of the horizon and the bound on the forcing;
only its uniform spatial Hölder constant enters. No temporal regularity is required. -/
theorem exists_holderWith_iteratedFDeriv_two_heatDuhamelPotential_slab [CompleteSpace F]
    (hα : 0 < α) (hα₁ : α < 1) :
    ∃ C : ℝ≥0, ∀ {f : ℝ → E → F} {M T : ℝ} {H : ℝ≥0},
      StronglyMeasurable (Function.uncurry f) →
      (∀ᵐ s ∂volume.restrict (Ioo 0 T), ∀ᵐ y, ‖f s y‖ ≤ M) →
      (∀ᵐ s ∂volume.restrict (Ioo 0 T), HolderWith H α (f s)) →
      HolderWith (C * H) α (fun p : slab (E := E) 0 T =>
        iteratedFDeriv ℝ 2 (heatDuhamelPotential f (p : ParabolicSpaceTime E).time)
          (p : ParabolicSpaceTime E).space) := by
  obtain ⟨Cs, hs⟩ :=
    exists_holderWith_iteratedFDeriv_two_heatDuhamelPotential (E := E) (F := F) hα hα₁
  obtain ⟨Ct, ht⟩ := exists_holderOnWith_iteratedFDeriv_two_heatDuhamelPotential
    (E := E) (F := F) hα (hα₁.trans (by norm_num))
  refine ⟨Cs + Ct, fun {f M T H} hf hM hH => ?_⟩
  apply eHolderNorm_le_iff.1
  refine (eHolderNorm_le_spaceEHolderNorm_add_timeEHolderNorm α _).trans ?_
  rw [add_mul, ENNReal.coe_add, ENNReal.coe_mul, ENNReal.coe_mul]
  apply add_le_add
  · apply spaceEHolderNorm_le_iff.2
    intro t x y
    rcases t.2.1.eq_or_lt with hzero | hpos
    · simp [← hzero, heatDuhamelPotential_zero]
    · simpa only [space_slabMk, time_slabMk, ENNReal.coe_mul] using (hs hf
        (ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo_right t.2.2) hM)
        (ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo_right t.2.2) hH) hpos) x y
  · apply timeEHolderNorm_le_iff.2
    intro x t s
    simpa only [space_slabMk, time_slabMk, ENNReal.coe_mul, Set.domRestrict_apply] using
      (ht hf hM hH x).holderWith t s

end TauCeti
