/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import TauCeti.Analysis.Complex.ReProdIm
import TauCeti.MeasureTheory.Integral.Lebesgue.Strip
import TauCeti.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Lebesgue integrals over horizontal bands in `ℂ`

On a punctured Riemann surface with cylindrical ends, a map on an end is read in the coordinate
`z = s + i t` with `s` along the end and `t` the circle coordinate, so it is a function on `ℂ`
that is periodic in the direction `I`. This file collects the facts about Lebesgue
integrals over the sets `s ×ℂ t = {z | z.re ∈ s ∧ z.im ∈ t}` that are needed to work with such
periodic functions on half-strips.

* For a function periodic under `z ↦ z + I`, translating the band `t` vertically by an integer
  does not change the integral (`Function.Periodic.setLIntegral_reProdIm_preimage_add_intCast`),
  so its integral over a band of `k` periods is `k` times its integral over one period
  (`Function.Periodic.setLIntegral_reProdIm_Ico_intCast_add_natCast`). A disc of radius at most
  `1/2` lies in two periods, so the integral over it is at most twice the integral over one period
  of the half-strip to its right
  (`Function.Periodic.setLIntegral_ball_le_two_mul_setLIntegral_reProdIm_Ioi`), and the same holds
  for the Bochner integral of a nonnegative real function
  (`Function.Periodic.setIntegral_ball_le_two_mul`).
* If the integral over the half-strip `(a, ∞) ×ℂ t` is finite, then the integrals over the
  half-strips `(R, ∞) ×ℂ t` tend to zero as `R → ∞`
  (`TauCeti.tendsto_setLIntegral_reProdIm_Ioi_atTop`). This is the strip lemma
  `TauCeti.tendsto_setLIntegral_of_eventually_subset` transported along `ℂ ≃ ℝ × ℝ`. For the
  energy density of a map on a cylindrical end, it says that a finite-energy end carries less and
  less energy far out.
-/

public section

open Complex Filter Function Metric MeasureTheory Set Topology
open scoped ENNReal

namespace Function.Periodic

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
      rw [← reProdIm_union_right, Ico_union_Ico_eq_Ico
        (le_add_of_nonneg_right (Nat.cast_nonneg k)) (by linarith)]
      push_cast
      rw [add_assoc]
    have hdisj : Disjoint (s ×ℂ Ico (n : ℝ) (n + k)) (s ×ℂ Ico ((n : ℝ) + k) (n + k + 1)) :=
      Set.disjoint_left.2 fun z hz hz' ↦ by
        simp only [mem_reProdIm, mem_Ico] at hz hz'
        linarith [hz.2.2, hz'.2.1]
    have hshift : ∫⁻ z in s ×ℂ Ico ((n : ℝ) + k) (n + k + 1), f z =
        ∫⁻ z in s ×ℂ Ico 0 1, f z := by
      rw [← hf.setLIntegral_reProdIm_preimage_add_intCast s (Ico 0 1) (-(n + k)),
        preimage_add_const_Ico]
      push_cast
      ring_nf
    rw [hunion, lintegral_union (hs.reProdIm measurableSet_Ico) hdisj, ih, hshift]
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
        rw [hf.setLIntegral_reProdIm_Ico_intCast_add_natCast measurableSet_Ioi]
        norm_num
    _ ≤ 2 * ∫⁻ y in Ioi (z₀.re - r) ×ℂ Icc 0 1, f y := by
        gcongr
        exact reProdIm_subset_iff.2 (prod_mono le_rfl Ico_subset_Icc_self)

/-- For a nonnegative real function periodic under `z ↦ z + I`, if its integral over one period
`(R, ∞) ×ℂ [0, 1]` of a half-strip is at most `ε`, then its integral over every disc of radius
`r ≤ 1/2` lying in the half-plane `re > R` is at most `2 ε`. -/
theorem setIntegral_ball_le_two_mul {g : ℂ → ℝ} (hg : Periodic g I) (hg0 : ∀ y, 0 ≤ g y)
    {z₀ : ℂ} {r R ε : ℝ} (hr : r ≤ 1 / 2) (hR : R ≤ z₀.re - r) (hε : 0 ≤ ε)
    (hm : AEStronglyMeasurable g (volume.restrict (ball z₀ r)))
    (hle : ∫⁻ y in Ioi R ×ℂ Icc 0 1, ENNReal.ofReal (g y) ≤ ENNReal.ofReal ε) :
    ∫ y in ball z₀ r, g y ≤ 2 * ε := by
  have hlE : ∫⁻ y in ball z₀ r, ENNReal.ofReal (g y) ≤ ENNReal.ofReal (2 * ε) := by
    calc ∫⁻ y in ball z₀ r, ENNReal.ofReal (g y)
        ≤ 2 * ∫⁻ y in Ioi (z₀.re - r) ×ℂ Icc 0 1, ENNReal.ofReal (g y) :=
          (hg.comp ENNReal.ofReal).setLIntegral_ball_le_two_mul_setLIntegral_reProdIm_Ioi z₀ hr
      _ ≤ 2 * ∫⁻ y in Ioi R ×ℂ Icc 0 1, ENNReal.ofReal (g y) := by
          gcongr
          exact reProdIm_subset_iff.2 (prod_mono (Ioi_subset_Ioi hR) le_rfl)
      _ ≤ 2 * ENNReal.ofReal ε := by gcongr
      _ = ENNReal.ofReal (2 * ε) := by
          rw [ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat]
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hg0) hm]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hlE

end Function.Periodic

namespace TauCeti

variable {f : ℂ → ℝ≥0∞}

/-- **Integrals over far-out half-strips tend to zero.** If the integral of `f` over the
half-strip `(a, ∞) ×ℂ t` is finite, then its integral over `(R, ∞) ×ℂ t` tends to zero as
`R → ∞`. No measurability of `f` or `t` is assumed. -/
theorem tendsto_setLIntegral_reProdIm_Ioi_atTop {t : Set ℝ} {a : ℝ}
    (hf : ∫⁻ z in Ioi a ×ℂ t, f z ≠ ∞) :
    Tendsto (fun R ↦ ∫⁻ z in Ioi R ×ℂ t, f z) atTop (𝓝 0) := by
  -- Transport to `ℝ × ℝ`, where `s ×ℂ t` becomes `s ×ˢ t`, and apply the strip lemma there.
  have he := volume_preserving_equiv_real_prod.symm
  have h (s : Set ℝ) : ∫⁻ z in s ×ℂ t, f z =
      ∫⁻ p in s ×ˢ t, f (measurableEquivRealProd.symm p) :=
    (he.setLIntegral_comp_preimage_emb measurableEquivRealProd.symm.measurableEmbedding f
      (s ×ℂ t)).symm
  simp_rw [h] at hf ⊢
  refine tendsto_setLIntegral_of_eventually_subset hf fun R ↦ ?_
  filter_upwards [eventually_ge_atTop (max a R)] with R' hR' p hp
  have h₁ : max a R < p.1 := hR'.trans_lt hp.1
  exact ⟨⟨(le_max_left _ _).trans_lt h₁, hp.2⟩,
    ((le_max_right _ _).trans h₁.le).trans (le_abs_self _)⟩

end TauCeti
