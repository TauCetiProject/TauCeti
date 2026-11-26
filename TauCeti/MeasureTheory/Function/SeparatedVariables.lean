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
`g(x) • h(t)` of such functions:

* `EuclideanSpace.eLpNorm_smul_comp_consEquivL_symm`: the `Lᵖ` seminorm of `y ↦ g(x) • h(t)` is
  the product of the `Lᵖ` seminorms of `h` on `ℝ` and of `g` on `ℝⁿ`, for every `p` and every
  scalar action compatible with the extended norms; with its `lpNorm` and `MemLp` forms
  `EuclideanSpace.lpNorm_smul_comp_consEquivL_symm` and
  `MeasureTheory.MemLp.smul_comp_consEquivL_symm`, and the support statement
  `HasCompactSupport.smul_comp_consEquivL_symm`.
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

end MeasureTheory

/-- The product `y ↦ g(x) • h(t)` of two functions with compact support has compact support. -/
theorem HasCompactSupport.smul_comp_consEquivL_symm {n : ℕ} {𝕜 E : Type*} [Zero 𝕜] [Zero E]
    [SMulWithZero 𝕜 E] {g : EuclideanSpace ℝ (Fin n) → 𝕜} {h : ℝ → E} (hg : HasCompactSupport g)
    (hh : HasCompactSupport h) :
    HasCompactSupport fun y => g ((EuclideanSpace.consEquivL ℝ n).symm y).2 •
      h ((EuclideanSpace.consEquivL ℝ n).symm y).1 := by
  refine HasCompactSupport.intro
    ((hh.prod hg).image (EuclideanSpace.consEquivL ℝ n).continuous) fun y hy => ?_
  have hy' : (EuclideanSpace.consEquivL ℝ n).symm y ∉ tsupport h ×ˢ tsupport g := fun hmem =>
    hy ⟨_, hmem, (EuclideanSpace.consEquivL ℝ n).apply_symm_apply y⟩
  rcases not_and_or.1 (mem_prod.not.1 hy') with h1 | h2
  · rw [image_eq_zero_of_notMem_tsupport h1, smul_zero]
  · rw [image_eq_zero_of_notMem_tsupport h2, zero_smul]

namespace EuclideanSpace

variable {n : ℕ} {p : ℝ≥0∞}

/-- **The `Lᵖ` seminorm of a function of separated variables.** On `ℝⁿ⁺¹ = ℝ × ℝⁿ`, the `Lᵖ`
seminorm of `y ↦ g(x) • h(t)` is the product of those of `h` and `g`, for every exponent. -/
theorem eLpNorm_smul_comp_consEquivL_symm {𝕜 ε : Type*} [TopologicalSpace 𝕜]
    [ContinuousENorm 𝕜] [TopologicalSpace ε] [ContinuousENorm ε] [SMul 𝕜 ε] [ContinuousSMul 𝕜 ε]
    [ENormSMulClass 𝕜 ε] {g : EuclideanSpace ℝ (Fin n) → 𝕜} {h : ℝ → ε}
    (hg : AEStronglyMeasurable g volume) (hh : AEStronglyMeasurable h volume) :
    eLpNorm (fun y => g ((consEquivL ℝ n).symm y).2 • h ((consEquivL ℝ n).symm y).1) p volume =
      eLpNorm h p volume * eLpNorm g p volume := by
  -- `y ↦ (x, t)` carries the volume of `ℝⁿ⁺¹` to the product volume on `ℝⁿ × ℝ`.
  have hmp : MeasurePreserving (fun y => ((consEquivL ℝ n).symm y).swap) volume
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).prod (volume : Measure ℝ)) := by
    have he : MeasurePreserving (consEquivL ℝ n).toHomeomorph.toMeasurableEquiv volume volume :=
      measurePreserving_consEquivL n
    have he' := he.symm
    rw [Measure.volume_eq_prod] at he'
    exact Measure.measurePreserving_swap.comp he'
  have hgh : AEStronglyMeasurable (fun z : EuclideanSpace ℝ (Fin n) × ℝ => g z.1 • h z.2)
      (volume.prod volume) :=
    hg.comp_fst.smul hh.comp_snd
  rw [mul_comm, ← TauCeti.eLpNorm_prod_smul hg hh, ← eLpNorm_comp_measurePreserving hgh hmp]
  -- The two integrands agree pointwise: `((t, x).swap).1 = x` and `((t, x).swap).2 = t`.
  rfl

/-- The `lpNorm` form of `EuclideanSpace.eLpNorm_smul_comp_consEquivL_symm`. -/
theorem lpNorm_smul_comp_consEquivL_symm {𝕜 E : Type*} [NormedAddCommGroup 𝕜]
    [NormedAddCommGroup E] [SMul 𝕜 E] [ContinuousSMul 𝕜 E] [ENormSMulClass 𝕜 E]
    {g : EuclideanSpace ℝ (Fin n) → 𝕜} {h : ℝ → E}
    (hg : AEStronglyMeasurable g volume) (hh : AEStronglyMeasurable h volume) :
    lpNorm (fun y => g ((consEquivL ℝ n).symm y).2 • h ((consEquivL ℝ n).symm y).1) p volume =
      lpNorm h p volume * lpNorm g p volume := by
  rw [lpNorm, eLpNorm_smul_comp_consEquivL_symm hg hh, ENNReal.toReal_mul, lpNorm, lpNorm]

end EuclideanSpace

/-- The product `y ↦ g(x) • h(t)` of an `Lᵖ` function on `ℝⁿ` and an `Lᵖ` function on `ℝ` is an
`Lᵖ` function on `ℝⁿ⁺¹`. -/
theorem MeasureTheory.MemLp.smul_comp_consEquivL_symm {n : ℕ} {p : ℝ≥0∞} {𝕜 ε : Type*}
    [TopologicalSpace 𝕜] [ContinuousENorm 𝕜] [TopologicalSpace ε] [ContinuousENorm ε] [SMul 𝕜 ε]
    [ContinuousSMul 𝕜 ε] [ENormSMulClass 𝕜 ε] {g : EuclideanSpace ℝ (Fin n) → 𝕜} {h : ℝ → ε}
    (hg : MemLp g p volume) (hh : MemLp h p volume) :
    MemLp (fun y => g ((EuclideanSpace.consEquivL ℝ n).symm y).2 •
      h ((EuclideanSpace.consEquivL ℝ n).symm y).1) p volume := by
  rw [memLp_iff, EuclideanSpace.eLpNorm_smul_comp_consEquivL_symm hg.aestronglyMeasurable
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

/-- The ball `B(x, s)` of `ℝⁿ` has `2ⁿ` times the volume of the ball `B(x, s / 2)`. -/
private theorem volume_ball_eq_two_pow_mul (x : EuclideanSpace ℝ (Fin n)) (s : ℝ) :
    volume (ball x s) = 2 ^ n * volume (ball x (s / 2)) := by
  have h := Measure.addHaar_ball_mul_of_pos (volume : Measure (EuclideanSpace ℝ (Fin n))) x
    two_pos (s / 2)
  rw [mul_div_cancel₀ s two_ne_zero] at h
  rw [h, Measure.addHaar_ball_center volume x, finrank_euclideanSpace_fin,
    ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat]

/-- The arithmetic of `EuclideanSpace.setLAverage_ball_comp_snd_consEquivL_symm_le`:
`2 s I / (s V) = 2ⁿ⁺¹ (I / (2ⁿ V))` for `s > 0`. -/
private theorem ofReal_two_mul_mul_div_ofReal_mul_eq {s : ℝ} (hs : 0 < s) (I V : ℝ≥0∞) :
    ENNReal.ofReal (2 * s) * I / (ENNReal.ofReal s * V) = 2 ^ (n + 1) * (I / (2 ^ n * V)) := by
  have hs0 : ENNReal.ofReal s ≠ 0 := (ENNReal.ofReal_pos.2 hs).ne'
  have h2n : (2 : ℝ≥0∞) ^ n ≠ 0 := pow_ne_zero _ two_ne_zero
  have h2n' : (2 : ℝ≥0∞) ^ n ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  rw [ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat]
  calc 2 * ENNReal.ofReal s * I / (ENNReal.ofReal s * V)
      = ENNReal.ofReal s * (2 * I) / (ENNReal.ofReal s * V) := by congr 1; ring
    _ = 2 ^ n * (2 * I) / (2 ^ n * V) := by
      rw [ENNReal.mul_div_mul_left _ _ hs0 ENNReal.ofReal_ne_top,
        ENNReal.mul_div_mul_left _ _ h2n h2n']
    _ = 2 ^ (n + 1) * (I / (2 ^ n * V)) := by simp only [div_eq_mul_inv]; ring

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
  rw [setLAverage_eq, setLAverage_eq, volume_ball_eq_two_pow_mul x₀ s,
    ← ofReal_two_mul_mul_div_ofReal_mul_eq hs]
  exact ENNReal.div_le_div (setLIntegral_ball_comp_snd_consEquivL_symm_le hG c s)
    (ofReal_mul_volume_ball_le_volume_ball c hs)

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
