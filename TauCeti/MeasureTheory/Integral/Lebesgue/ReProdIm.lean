/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Lebesgue integrals over horizontal bands in `ℂ`

On a punctured Riemann surface with cylindrical ends, a map on an end is read in the coordinate
`z = s + i t` with `s` along the end and `t` the circle coordinate, so it is a function on `ℂ`
that is periodic in the direction `I`. This file collects the facts about lower Lebesgue
integrals over the sets `s ×ℂ t = {z | z.re ∈ s ∧ z.im ∈ t}` that are needed to work with such
periodic functions on half-strips.

* For a function periodic under `z ↦ z + I`, translating the band `t` vertically by an integer
  does not change the integral (`TauCeti.setLIntegral_reProdIm_preimage_add_intCast`), so its
  integral over a band of `k` periods is `k` times its integral over one period
  (`TauCeti.setLIntegral_reProdIm_Ico_intCast_add_natCast`). A disc of radius at most `1/2` lies
  in two periods, so the integral over it is at most twice the integral over one period of the
  half-strip to its right (`TauCeti.setLIntegral_ball_le_two_mul_setLIntegral_reProdIm_Ioi`).
* If the integral over the half-strip `(a, ∞) ×ℂ t` is finite, then the integrals over the
  half-strips `(R, ∞) ×ℂ t` tend to zero as `R → ∞`
  (`TauCeti.tendsto_setLIntegral_reProdIm_Ioi_atTop`). For the energy density of a map on a
  cylindrical end, this says that a finite-energy end carries less and less energy far out.
-/

public section

namespace TauCeti

open Complex Filter Function Metric MeasureTheory Set Topology
open scoped ENNReal

variable {f : ℂ → ℝ≥0∞}

/-- For a function periodic under `z ↦ z + I`, translating the band `t` by an integer does not
change its integral over `s ×ℂ t`. -/
theorem setLIntegral_reProdIm_preimage_add_intCast (hf : Periodic f I) (s t : Set ℝ) (n : ℤ) :
    ∫⁻ z in s ×ℂ ((· + (n : ℝ)) ⁻¹' t), f z = ∫⁻ z in s ×ℂ t, f z := by
  have hpre : (· + (n : ℂ) * I) ⁻¹' (s ×ℂ t) = s ×ℂ ((· + (n : ℝ)) ⁻¹' t) := by
    ext z
    simp [mem_reProdIm]
  rw [← hpre, ← (measurePreserving_add_right volume ((n : ℂ) * I)).setLIntegral_comp_preimage_emb
    (measurableEmbedding_addRight _) f (s ×ℂ t)]
  simp_rw [hf.int_mul n _]

/-- For a function periodic under `z ↦ z + I`, its integral over `k` consecutive periods
`s ×ℂ [n, n + k)` is `k` times its integral over the period `s ×ℂ [0, 1)`. -/
theorem setLIntegral_reProdIm_Ico_intCast_add_natCast (hf : Periodic f I) {s : Set ℝ}
    (hs : MeasurableSet s) (n : ℤ) (k : ℕ) :
    ∫⁻ z in s ×ℂ Ico (n : ℝ) (n + k), f z = k * ∫⁻ z in s ×ℂ Ico 0 1, f z := by
  induction k with
  | zero => simp [reProdIm]
  | succ k ih =>
    have hunion : s ×ℂ Ico (n : ℝ) (n + (k + 1 : ℕ)) =
        s ×ℂ Ico (n : ℝ) (n + k) ∪ s ×ℂ Ico ((n : ℝ) + k) (n + k + 1) := by
      ext z
      simp only [mem_union, mem_reProdIm, mem_Ico]
      push_cast
      constructor
      · rintro ⟨hs, h₁, h₂⟩
        rcases lt_or_ge z.im (n + k) with h | h
        · exact Or.inl ⟨hs, h₁, h⟩
        · exact Or.inr ⟨hs, h, by linarith⟩
      · rintro (⟨hs, h₁, h₂⟩ | ⟨hs, h₁, h₂⟩)
        · exact ⟨hs, h₁, by linarith⟩
        · exact ⟨hs, by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)], by linarith⟩
    have hdisj : Disjoint (s ×ℂ Ico (n : ℝ) (n + k)) (s ×ℂ Ico ((n : ℝ) + k) (n + k + 1)) :=
      Set.disjoint_left.2 fun z hz hz' ↦ by
        simp only [mem_reProdIm, mem_Ico] at hz hz'
        linarith [hz.2.2, hz'.2.1]
    have hshift : ∫⁻ z in s ×ℂ Ico ((n : ℝ) + k) (n + k + 1), f z =
        ∫⁻ z in s ×ℂ Ico 0 1, f z := by
      rw [← setLIntegral_reProdIm_preimage_add_intCast hf s (Ico 0 1) (-(n + k)),
        preimage_add_const_Ico]
      push_cast
      ring_nf
    have hmeas : MeasurableSet (s ×ℂ Ico ((n : ℝ) + k) (n + k + 1)) :=
      (continuous_re.measurable hs).inter (continuous_im.measurable measurableSet_Ico)
    rw [hunion, lintegral_union hmeas hdisj, ih, hshift]
    push_cast
    ring

/-- For a function periodic under `z ↦ z + I`, its integral over a disc of radius `r ≤ 1/2` about
`z₀` is at most twice its integral over one period `(z₀.re - r, ∞) ×ℂ [0, 1]` of the half-strip
to the right of the disc. -/
theorem setLIntegral_ball_le_two_mul_setLIntegral_reProdIm_Ioi (hf : Periodic f I) (z₀ : ℂ)
    {r : ℝ} (hr : r ≤ 1 / 2) :
    ∫⁻ y in ball z₀ r, f y ≤ 2 * ∫⁻ y in Ioi (z₀.re - r) ×ℂ Icc 0 1, f y := by
  -- The disc lies in the two periods `n ≤ im < n + 2` for `n = ⌊z₀.im - 1/2⌋`.
  set n : ℤ := ⌊z₀.im - 1 / 2⌋
  have hsub : ball z₀ r ⊆ Ioi (z₀.re - r) ×ℂ Ico (n : ℝ) (n + (2 : ℕ)) := by
    intro y hy
    rw [mem_ball, dist_eq_norm] at hy
    have hre := abs_re_le_norm (y - z₀)
    have him := abs_im_le_norm (y - z₀)
    simp only [sub_re, sub_im] at hre him
    rw [abs_le] at hre him
    have h₁ := Int.floor_le (z₀.im - 1 / 2)
    have h₂ := Int.lt_floor_add_one (z₀.im - 1 / 2)
    simp only [mem_reProdIm, mem_Ioi, mem_Ico, Nat.cast_ofNat]
    refine ⟨by linarith, by linarith, by linarith⟩
  calc ∫⁻ y in ball z₀ r, f y
      ≤ ∫⁻ y in Ioi (z₀.re - r) ×ℂ Ico (n : ℝ) (n + (2 : ℕ)), f y := lintegral_mono_set hsub
    _ = 2 * ∫⁻ y in Ioi (z₀.re - r) ×ℂ Ico 0 1, f y := by
        rw [setLIntegral_reProdIm_Ico_intCast_add_natCast hf measurableSet_Ioi]
        norm_num
    _ ≤ 2 * ∫⁻ y in Ioi (z₀.re - r) ×ℂ Icc 0 1, f y := by
        gcongr
        exact reProdIm_subset_iff.2 (prod_mono le_rfl Ico_subset_Icc_self)

/-- **Integrals over far-out half-strips tend to zero.** If the integral of `f` over the
half-strip `(a, ∞) ×ℂ t` is finite, then its integral over `(R, ∞) ×ℂ t` tends to zero as
`R → ∞`. No measurability of `f` or `t` is assumed. -/
theorem tendsto_setLIntegral_reProdIm_Ioi_atTop {t : Set ℝ} {a : ℝ}
    (hf : ∫⁻ z in Ioi a ×ℂ t, f z ≠ ∞) :
    Tendsto (fun R ↦ ∫⁻ z in Ioi R ×ℂ t, f z) atTop (𝓝 0) := by
  set ν := (volume.restrict (Ioi a ×ℂ t)).withDensity f
  have hmeas (R : ℝ) : MeasurableSet (re ⁻¹' Ioi R) :=
    measurableSet_Ioi.preimage continuous_re.measurable
  have hν (R : ℝ) : ν (re ⁻¹' Ioi R) = ∫⁻ z in re ⁻¹' Ioi R ∩ (Ioi a ×ℂ t), f z := by
    rw [withDensity_apply _ (hmeas R), Measure.restrict_restrict (hmeas R)]
  -- The `ν`-measures of the half-planes `re z > R` decrease to the measure of their empty
  -- intersection.
  have hlim : Tendsto (fun R ↦ ν (re ⁻¹' Ioi R)) atTop (𝓝 0) := by
    have hempty : ⋂ R : ℝ, re ⁻¹' Ioi R = ∅ :=
      eq_empty_of_forall_notMem fun z hz ↦ lt_irrefl z.re (mem_iInter.1 hz z.re)
    have h := tendsto_measure_iInter_atTop (μ := ν) (fun R ↦ (hmeas R).nullMeasurableSet)
      (fun _ _ h ↦ preimage_mono (Ioi_subset_Ioi h))
      ⟨a, by rw [hν]; exact ne_top_of_le_ne_top hf (lintegral_mono_set inter_subset_right)⟩
    rwa [hempty, measure_empty] at h
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop a] with R hR
  rw [hν]
  congr 2
  ext z
  simp only [mem_inter_iff, mem_preimage, mem_Ioi, mem_reProdIm]
  exact ⟨fun h ↦ ⟨h.1, h.2.2⟩, fun h ↦ ⟨h.1, hR.trans_lt h.1, h.2⟩⟩

end TauCeti
