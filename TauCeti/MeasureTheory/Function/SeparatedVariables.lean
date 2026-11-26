/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Average
public import TauCeti.MeasureTheory.Measure.Haar.EuclideanSpace
import TauCeti.MeasureTheory.Function.Lp.Iterated

/-!
# Functions of separated variables on `ℝⁿ⁺¹ = ℝ × ℝⁿ`

Splitting off the first coordinate, `EuclideanSpace.consEquivL ℝ n`, identifies `ℝⁿ⁺¹` with
`ℝ × ℝⁿ` and its volume with the product of the volumes of `ℝ` and `ℝⁿ`
(`EuclideanSpace.measurePreserving_consEquivL`). Write `y = (t, x)` accordingly. This file records
how this identification acts on functions of one of the two variables and on products
`g(x) h(t)` of such functions:

* `EuclideanSpace.eLpNorm_mul_comp_consEquivL_symm`: the `Lᵖ` seminorm of `y ↦ g(x) h(t)` is the
  product of the `Lᵖ` seminorms of `h` on `ℝ` and of `g` on `ℝⁿ`, for every `p`; with its `lpNorm`
  and `MemLp` forms `EuclideanSpace.lpNorm_mul_comp_consEquivL_symm` and
  `MeasureTheory.MemLp.mul_comp_consEquivL_symm`, and the support statement
  `HasCompactSupport.mul_comp_consEquivL_symm`.
* `EuclideanSpace.setLIntegral_ball_comp_snd_consEquivL_symm_le` and
  `EuclideanSpace.setLAverage_ball_comp_snd_consEquivL_symm_le`: for a function `G` of `x` alone,
  the integral of `G` over a ball `B(c, s)` of `ℝⁿ⁺¹` is at most `2 s` times its integral over the
  ball `B(x_c, s)` of `ℝⁿ`, and its average over `B(c, s)` at most `2ⁿ⁺¹` times its average over
  `B(x_c, s)`. So functions of fewer variables inherit integrability on balls
  (`MeasureTheory.LocallyIntegrable.integrableOn_ball_comp_snd_consEquivL_symm`) and bounds on mean
  oscillations.
-/

public section

open MeasureTheory Metric Set
open scoped ENNReal

namespace MeasureTheory

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F]

/-- A function of the last `n` coordinates of `ℝⁿ⁺¹` is a.e. strongly measurable when it is on
`ℝⁿ`. -/
theorem AEStronglyMeasurable.comp_snd_consEquivL_symm {f : EuclideanSpace ℝ (Fin n) → F}
    (hf : AEStronglyMeasurable f volume) :
    AEStronglyMeasurable (fun y => f ((EuclideanSpace.consEquivL ℝ n).symm y).2) volume := by
  have hmp : MeasurePreserving (EuclideanSpace.consEquivL ℝ n).toHomeomorph.toMeasurableEquiv
      volume volume :=
    EuclideanSpace.measurePreserving_consEquivL n
  have h : AEStronglyMeasurable (fun z : ℝ × EuclideanSpace ℝ (Fin n) => f z.2) volume := by
    rw [Measure.volume_eq_prod]
    exact hf.comp_snd
  exact h.comp_measurePreserving hmp.symm

/-- A function of the first coordinate of `ℝⁿ⁺¹` is a.e. strongly measurable when it is on
`ℝ`. -/
theorem AEStronglyMeasurable.comp_fst_consEquivL_symm {h : ℝ → F}
    (hh : AEStronglyMeasurable h volume) :
    AEStronglyMeasurable (fun y => h ((EuclideanSpace.consEquivL ℝ n).symm y).1)
      (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) := by
  have hmp : MeasurePreserving (EuclideanSpace.consEquivL ℝ n).toHomeomorph.toMeasurableEquiv
      volume volume :=
    EuclideanSpace.measurePreserving_consEquivL n
  have h : AEStronglyMeasurable (fun z : ℝ × EuclideanSpace ℝ (Fin n) => h z.1) volume := by
    rw [Measure.volume_eq_prod]
    exact hh.comp_fst
  exact h.comp_measurePreserving hmp.symm

end MeasureTheory

/-- The product `y ↦ g(x) h(t)` of two functions with compact support has compact support. -/
theorem HasCompactSupport.mul_comp_consEquivL_symm {n : ℕ} {g : EuclideanSpace ℝ (Fin n) → ℝ}
    {h : ℝ → ℝ} (hg : HasCompactSupport g) (hh : HasCompactSupport h) :
    HasCompactSupport fun y => g ((EuclideanSpace.consEquivL ℝ n).symm y).2 *
      h ((EuclideanSpace.consEquivL ℝ n).symm y).1 := by
  refine HasCompactSupport.intro
    ((hh.prod hg).image (EuclideanSpace.consEquivL ℝ n).continuous) fun y hy => ?_
  have hy' : (EuclideanSpace.consEquivL ℝ n).symm y ∉ tsupport h ×ˢ tsupport g := fun hmem =>
    hy ⟨_, hmem, (EuclideanSpace.consEquivL ℝ n).apply_symm_apply y⟩
  rcases not_and_or.1 (mem_prod.not.1 hy') with h1 | h2
  · rw [image_eq_zero_of_notMem_tsupport h1, mul_zero]
  · rw [image_eq_zero_of_notMem_tsupport h2, zero_mul]

namespace EuclideanSpace

variable {n : ℕ} {p : ℝ≥0∞}

/-- **The `Lᵖ` seminorm of a function of separated variables.** On `ℝⁿ⁺¹ = ℝ × ℝⁿ`, the `Lᵖ`
seminorm of `y ↦ g(x) h(t)` is the product of those of `h` and `g`, for every exponent. -/
theorem eLpNorm_mul_comp_consEquivL_symm {g : EuclideanSpace ℝ (Fin n) → ℝ} {h : ℝ → ℝ}
    (hg : AEStronglyMeasurable g volume) (hh : AEStronglyMeasurable h volume) :
    eLpNorm (fun y => g ((consEquivL ℝ n).symm y).2 * h ((consEquivL ℝ n).symm y).1) p volume =
      eLpNorm h p volume * eLpNorm g p volume := by
  have hmp : MeasurePreserving (consEquivL ℝ n).toHomeomorph.toMeasurableEquiv volume volume :=
    measurePreserving_consEquivL n
  have hprod := TauCeti.eLpNorm_prod_smul (p := p) (μ := (volume : Measure ℝ))
    (ν := (volume : Measure (EuclideanSpace ℝ (Fin n)))) hh hg
  rw [← Measure.volume_eq_prod] at hprod
  rw [← hprod, ← eLpNorm_comp_measurePreserving (p := p) ?_ hmp.symm]
  · congr 1
    ext y
    simp [mul_comm]
  · rw [Measure.volume_eq_prod]
    exact hh.comp_fst.smul hg.comp_snd

/-- The `lpNorm` form of `EuclideanSpace.eLpNorm_mul_comp_consEquivL_symm`. -/
theorem lpNorm_mul_comp_consEquivL_symm {g : EuclideanSpace ℝ (Fin n) → ℝ} {h : ℝ → ℝ}
    (hg : AEStronglyMeasurable g volume) (hh : AEStronglyMeasurable h volume) :
    lpNorm (fun y => g ((consEquivL ℝ n).symm y).2 * h ((consEquivL ℝ n).symm y).1) p volume =
      lpNorm h p volume * lpNorm g p volume := by
  rw [lpNorm, eLpNorm_mul_comp_consEquivL_symm hg hh, ENNReal.toReal_mul, lpNorm, lpNorm]

end EuclideanSpace

/-- The product `y ↦ g(x) h(t)` of an `Lᵖ` function on `ℝⁿ` and an `Lᵖ` function on `ℝ` is an
`Lᵖ` function on `ℝⁿ⁺¹`. -/
theorem MeasureTheory.MemLp.mul_comp_consEquivL_symm {n : ℕ} {p : ℝ≥0∞}
    {g : EuclideanSpace ℝ (Fin n) → ℝ} {h : ℝ → ℝ} (hg : MemLp g p volume)
    (hh : MemLp h p volume) :
    MemLp (fun y => g ((EuclideanSpace.consEquivL ℝ n).symm y).2 *
      h ((EuclideanSpace.consEquivL ℝ n).symm y).1) p volume := by
  rw [memLp_iff, EuclideanSpace.eLpNorm_mul_comp_consEquivL_symm hg.aestronglyMeasurable
    hh.aestronglyMeasurable]
  exact ENNReal.mul_lt_top hh.eLpNorm_lt_top hg.eLpNorm_lt_top

namespace EuclideanSpace

variable {n : ℕ}

/-- The integral over a ball `B(c, s)` of `ℝⁿ⁺¹` of a function of the last `n` coordinates is at
most `2 s` times its integral over the ball `B(x_c, s)` of `ℝⁿ`, `x_c` the last `n` coordinates of
`c`. -/
theorem setLIntegral_ball_comp_snd_consEquivL_symm_le {G : EuclideanSpace ℝ (Fin n) → ℝ≥0∞}
    (hG : AEMeasurable G) (c : EuclideanSpace ℝ (Fin (n + 1))) (s : ℝ) :
    ∫⁻ y in ball c s, G ((consEquivL ℝ n).symm y).2 ≤
      ENNReal.ofReal (2 * s) * ∫⁻ x in ball ((consEquivL ℝ n).symm c).2 s, G x := by
  set e := consEquivL ℝ n
  set w := e.symm c
  have hmp := measurePreserving_consEquivL n
  have hemb : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  have hc : c = e w := (e.apply_symm_apply c).symm
  calc ∫⁻ y in ball c s, G (e.symm y).2
      = ∫⁻ z in e ⁻¹' ball c s, G (e.symm (e z)).2 :=
        (hmp.setLIntegral_comp_preimage_emb hemb (fun y => G (e.symm y).2) _).symm
    _ = ∫⁻ z in e ⁻¹' ball c s, G z.2 := by simp only [ContinuousLinearEquiv.symm_apply_apply]
    _ ≤ ∫⁻ z in ball w.1 s ×ˢ ball w.2 s, G z.2 :=
        lintegral_mono_set (hc ▸ preimage_consEquivL_ball_subset w s)
    _ = ENNReal.ofReal (2 * s) * ∫⁻ x in ball w.2 s, G x := by
        rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
        have := lintegral_prod_mul (μ := volume.restrict (ball w.1 s))
          (ν := volume.restrict (ball w.2 s)) (f := fun _ => (1 : ℝ≥0∞)) aemeasurable_const
          hG.restrict
        simpa only [one_mul, lintegral_const, Measure.restrict_apply_univ, Real.volume_ball]
          using this

/-- A ball `B(c, s)` of `ℝⁿ⁺¹` has volume at least `s` times that of the ball `B(x_c, s / 2)` of
`ℝⁿ`, `x_c` the last `n` coordinates of `c`. -/
theorem ofReal_mul_volume_ball_le_volume_ball (c : EuclideanSpace ℝ (Fin (n + 1))) {s : ℝ}
    (hs : 0 < s) :
    ENNReal.ofReal s * volume (ball ((consEquivL ℝ n).symm c).2 (s / 2)) ≤ volume (ball c s) := by
  set e := consEquivL ℝ n
  set w := e.symm c
  have hmp := measurePreserving_consEquivL n
  have hemb : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  have hc : c = e w := (e.apply_symm_apply c).symm
  calc ENNReal.ofReal s * volume (ball w.2 (s / 2))
      = volume (ball w.1 (s / 2) ×ˢ ball w.2 (s / 2)) := by
        rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_ball]
        congr 2
        ring
    _ ≤ volume (e ⁻¹' ball c s) :=
        measure_mono (hc ▸ ball_prod_ball_subset_preimage_consEquivL_ball w hs)
    _ = volume (ball c s) := hmp.measure_preimage_emb hemb _

/-- The average over a ball `B(c, s)` of `ℝⁿ⁺¹` of a function of the last `n` coordinates is at
most `2ⁿ⁺¹` times its average over the ball `B(x_c, s)` of `ℝⁿ`, `x_c` the last `n` coordinates of
`c`. -/
theorem setLAverage_ball_comp_snd_consEquivL_symm_le {G : EuclideanSpace ℝ (Fin n) → ℝ≥0∞}
    (hG : AEMeasurable G) (c : EuclideanSpace ℝ (Fin (n + 1))) (s : ℝ) :
    ⨍⁻ y in ball c s, G ((consEquivL ℝ n).symm y).2 ≤
      2 ^ (n + 1) * ⨍⁻ x in ball ((consEquivL ℝ n).symm c).2 s, G x := by
  rcases le_or_gt s 0 with hs | hs
  · simp [ball_eq_empty.2 hs]
  set x₀ := ((consEquivL ℝ n).symm c).2
  set V := volume (ball x₀ (s / 2))
  have hball : volume (ball x₀ s) = 2 ^ n * V := by
    simp only [V]
    rw [Measure.addHaar_ball_of_pos _ _ hs, Measure.addHaar_ball_of_pos _ _ (half_pos hs),
      finrank_euclideanSpace_fin, ← mul_assoc, show s ^ n = 2 ^ n * (s / 2) ^ n by
        rw [← mul_pow]; ring_nf, ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat]
  have hs0 : ENNReal.ofReal s ≠ 0 := (ENNReal.ofReal_pos.2 hs).ne'
  rw [setLAverage_eq, setLAverage_eq, hball]
  calc (∫⁻ y in ball c s, G ((consEquivL ℝ n).symm y).2) / volume (ball c s)
      ≤ (ENNReal.ofReal (2 * s) * ∫⁻ x in ball x₀ s, G x) / (ENNReal.ofReal s * V) :=
        ENNReal.div_le_div (setLIntegral_ball_comp_snd_consEquivL_symm_le hG c s)
          (ofReal_mul_volume_ball_le_volume_ball c hs)
    _ = 2 ^ (n + 1) * ((∫⁻ x in ball x₀ s, G x) / (2 ^ n * V)) := by
      have h2n : (2 : ℝ≥0∞) ^ n ≠ 0 := pow_ne_zero _ two_ne_zero
      have h2n' : (2 : ℝ≥0∞) ^ n ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
      rw [ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat, mul_assoc, mul_left_comm,
        ENNReal.mul_div_mul_left _ _ hs0 ENNReal.ofReal_ne_top, ← mul_div_assoc, pow_succ,
        mul_assoc, ENNReal.mul_div_mul_left _ _ h2n h2n', mul_div_assoc]

end EuclideanSpace

/-- A function of the last `n` coordinates of `ℝⁿ⁺¹` is integrable on every ball when it is locally
integrable on `ℝⁿ`. -/
theorem MeasureTheory.LocallyIntegrable.integrableOn_ball_comp_snd_consEquivL_symm {n : ℕ}
    {F : Type*} [NormedAddCommGroup F] {f : EuclideanSpace ℝ (Fin n) → F}
    (hf : LocallyIntegrable f volume) (c : EuclideanSpace ℝ (Fin (n + 1))) (s : ℝ) :
    IntegrableOn (fun y => f ((EuclideanSpace.consEquivL ℝ n).symm y).2) (ball c s) volume := by
  refine ⟨hf.aestronglyMeasurable.comp_snd_consEquivL_symm.restrict, ?_⟩
  have hball : IntegrableOn f (ball ((EuclideanSpace.consEquivL ℝ n).symm c).2 s) volume :=
    (hf.integrableOn_isCompact (isCompact_closedBall _ s)).mono_set ball_subset_closedBall
  rw [HasFiniteIntegral]
  exact (EuclideanSpace.setLIntegral_ball_comp_snd_consEquivL_symm_le
    hf.aestronglyMeasurable.eNorm c s).trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hball.2)
