/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.CalderonZygmund.Decomposition
import TauCeti.MeasureTheory.Function.Lp.InfiniteSum

/-!
# Singular integral operators of weak type `(1, 1)`

Let `T` be a bounded linear operator on `L²(ℝⁿ)`. The **Calderón–Zygmund theorem** says that `T`
is of weak type `(1, 1)` as soon as it satisfies a **cancellation condition**: there is a constant
`B` such that for every closed ball `closedBall y r` and every `b ∈ L²` vanishing off
that ball with integral zero,

`∫_{ℝⁿ \ closedBall y (2r)} ‖T b‖ ≤ B ‖b‖₁`.

The conclusion is that for every `f ∈ L²` and every `t`,

`t · |{‖T f‖ > t}| ≤ (2ⁿ (4 ‖T‖² + 1) + 4 B) ‖f‖₁`
(`TauCeti.mul_volume_lt_enorm_le_of_setLIntegral_compl_closedBall_le`).

The cancellation condition holds for an operator given off the support of `b` by a kernel,
`T b x = ∫ K x y (b y) dy`, satisfying **Hörmander's kernel condition**

`∫_{dist x y' > 2 dist y y'} ‖K x y - K x y'‖ dx ≤ B` for all `y`, `y'`
(`TauCeti.setLIntegral_compl_closedBall_enorm_le_of_hormander`). Since `b` has mean zero, `K x y₀`
can be subtracted from the kernel, and for `y` in the ball and `x` outside the doubled ball the
difference `K x y - K x y₀` is controlled by Hörmander's condition. Combining the two gives the
classical form of the theorem (`TauCeti.mul_volume_lt_enorm_le_of_hormander`). The weak-type bound
is the endpoint estimate that Marcinkiewicz interpolation against the `L²` bound turns into `Lᵖ`
bounds for `1 < p < 2`.

## The proof

Decompose `f = g + ∑_Q b_Q` at height `t` (`TauCeti.calderonZygmundGood`,
`TauCeti.calderonZygmundBad`). The good part satisfies `‖g‖₂² ≤ 2ⁿ t ‖f‖₁`, so Chebyshev's
inequality and the `L²` bound give `t · |{‖T g‖ > t / 2}| ≤ 4 · 2ⁿ ‖T‖² ‖f‖₁`. Each cube `Q` lies in
the closed sup-norm ball `B_Q` of radius half its side, and the union `Ω` of the doubled balls
`2 B_Q` has `t |Ω| ≤ 2ⁿ ‖f‖₁`. Off `Ω`, the cancellation condition applied to each `b_Q` gives
`∫_{ℝⁿ \ Ω} ‖T b‖ ≤ ∑_Q B ‖b_Q‖₁ ≤ 2 B ‖f‖₁`, where `‖T b‖ ≤ ∑_Q ‖T b_Q‖` almost everywhere because
the `b_Q` sum to `b` in `L²` (`MeasureTheory.Lp.ae_enorm_le_tsum_enorm_of_hasSum`). A last
application of Chebyshev's inequality bounds `t · |{‖T b‖ > t / 2} \ Ω|` by `4 B ‖f‖₁`.

Points of `ℝⁿ` are functions `ι → ℝ`, so distances and balls are taken in the sup norm.

## Main declarations

* `TauCeti.mul_volume_lt_enorm_le_of_setLIntegral_compl_closedBall_le`: an `L²`-bounded operator
  satisfying the cancellation condition is of weak type `(1, 1)`.
* `TauCeti.setLIntegral_compl_closedBall_enorm_le_of_hormander`: Hörmander's kernel condition
  implies the cancellation condition, in any metric measure space.
* `TauCeti.mul_volume_lt_enorm_le_of_hormander`: an `L²`-bounded operator with a kernel satisfying
  Hörmander's condition is of weak type `(1, 1)`.

## References

* A. P. Calderón and A. Zygmund, *On the existence of certain singular integrals*, Acta Math.
  **88** (1952), 85–139.
* L. Hörmander, *Estimates for translation invariant operators in Lᵖ spaces*, Acta Math. **104**
  (1960), 93–140.
* E. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter II, §2.
* L. Grafakos, *Classical Fourier Analysis*, Section 5.3.
-/

public section

namespace TauCeti

open Filter MeasureTheory Metric Set
open scoped ENNReal Topology

section Kernel

variable {X E F : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  {μ : Measure X} [SFinite μ]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **Hörmander's kernel condition implies the cancellation condition.** Let `K` be a kernel whose
differences satisfy `∫_{dist x y' > 2 dist y y'} ‖K x y - K x y'‖ dx ≤ B` for all `y`, `y'`. If `b`
is integrable, vanishes off `closedBall y₀ r` and has integral zero, and `h x = ∫ K x y (b y) dy`
for almost every `x` off that ball, then the integral of `‖h‖` off `closedBall y₀ (2 r)` is at
most `B ‖b‖₁`. -/
theorem setLIntegral_compl_closedBall_enorm_le_of_hormander {K : X → X → E →L[ℝ] F}
    (hK : StronglyMeasurable (Function.uncurry K)) {B : ℝ≥0∞}
    (hB : ∀ y y', ∫⁻ x in {x | 2 * dist y y' < dist x y'}, ‖K x y - K x y'‖ₑ ∂μ ≤ B)
    {b : X → E} (hb : Integrable b μ) {y₀ : X} {r : ℝ}
    (hsupp : ∀ᵐ y ∂μ, y ∉ closedBall y₀ r → b y = 0) (hmean : ∫ y, b y ∂μ = 0) {h : X → F}
    (hrep : ∀ᵐ x ∂μ, x ∉ closedBall y₀ r → h x = ∫ y, K x y (b y) ∂μ) :
    ∫⁻ x in (closedBall y₀ (2 * r))ᶜ, ‖h x‖ₑ ∂μ ≤ B * ∫⁻ y, ‖b y‖ₑ ∂μ := by
  have hKd : StronglyMeasurable fun p : X × X => K p.1 p.2 - K p.1 y₀ :=
    hK.sub (hK.comp_measurable (measurable_fst.prodMk measurable_const))
  -- Off the doubled ball, `h x` is the integral of `(K x y - K x y₀) (b y)`, since `b` has mean
  -- zero, and is bounded by the integral of `‖K x y - K x y₀‖ ‖b y‖`.
  have hpt : ∀ᵐ x ∂μ, x ∈ (closedBall y₀ (2 * r))ᶜ →
      ‖h x‖ₑ ≤ ∫⁻ y, ‖K x y - K x y₀‖ₑ * ‖b y‖ₑ ∂μ := by
    filter_upwards [hrep] with x hx hx2
    have hxr : x ∉ closedBall y₀ r := fun hxr => hx2 <| by
      simp only [mem_closedBall] at hxr ⊢
      linarith [dist_nonneg (x := x) (y := y₀)]
    rw [hx hxr]
    rcases eq_or_ne (∫⁻ y, ‖K x y - K x y₀‖ₑ * ‖b y‖ₑ ∂μ) ∞ with hD | hD
    · exact hD ▸ le_top
    have hint : Integrable (fun y => (K x y - K x y₀) (b y)) μ :=
      ⟨(ContinuousLinearMap.apply ℝ F).aestronglyMeasurable_comp₂ hb.1
        (hKd.comp_measurable measurable_prodMk_left).aestronglyMeasurable,
        (lintegral_mono fun y => ContinuousLinearMap.le_opENorm _ _).trans_lt hD.lt_top⟩
    have heq : ∫ y, K x y (b y) ∂μ = ∫ y, (K x y - K x y₀) (b y) ∂μ := by
      have hint₀ := (K x y₀).integrable_comp hb
      have h0 : ∫ y, K x y₀ (b y) ∂μ = 0 := by
        rw [ContinuousLinearMap.integral_comp_comm _ hb, hmean, map_zero]
      rw [← sub_zero (∫ y, K x y (b y) ∂μ), ← h0,
        ← integral_sub ((hint.add hint₀).congr (.of_forall fun y => by simp)) hint₀]
      simp
    rw [heq]
    exact (enorm_integral_le_lintegral_enorm _).trans
      (lintegral_mono fun y => ContinuousLinearMap.le_opENorm _ _)
  have hmeas : AEMeasurable (Function.uncurry fun x y => ‖K x y - K x y₀‖ₑ * ‖b y‖ₑ)
      ((μ.restrict (closedBall y₀ (2 * r))ᶜ).prod μ) :=
    hKd.enorm.aemeasurable.mul hb.1.enorm.comp_snd
  calc ∫⁻ x in (closedBall y₀ (2 * r))ᶜ, ‖h x‖ₑ ∂μ
      ≤ ∫⁻ x in (closedBall y₀ (2 * r))ᶜ, ∫⁻ y, ‖K x y - K x y₀‖ₑ * ‖b y‖ₑ ∂μ ∂μ :=
        setLIntegral_mono_ae' isClosed_closedBall.measurableSet.compl hpt
    _ = ∫⁻ y, ‖b y‖ₑ * ∫⁻ x in (closedBall y₀ (2 * r))ᶜ, ‖K x y - K x y₀‖ₑ ∂μ ∂μ := by
        rw [lintegral_lintegral_swap hmeas]
        refine lintegral_congr fun y => ?_
        have hKy : Measurable fun x => ‖K x y - K x y₀‖ₑ :=
          (hKd.comp_measurable measurable_prodMk_right).enorm
        rw [lintegral_mul_const'' _ hKy.aemeasurable, mul_comm]
    _ ≤ ∫⁻ y, ‖b y‖ₑ * B ∂μ := by
        -- For `y` in the ball, the complement of the doubled ball lies in the region of
        -- Hörmander's condition; off the ball, `b y = 0`.
        refine lintegral_mono_ae ?_
        filter_upwards [hsupp] with y hy
        by_cases hyr : y ∈ closedBall y₀ r
        · refine mul_le_mul_right ((lintegral_mono_set fun x hx => ?_).trans (hB y y₀)) _
          simp only [mem_compl_iff, mem_closedBall, not_le] at hx hyr
          exact (mul_le_mul_of_nonneg_left hyr zero_le_two).trans_lt hx
        · simp [hy hyr]
    _ = B * ∫⁻ y, ‖b y‖ₑ ∂μ := by rw [lintegral_mul_const'' _ hb.1.enorm, mul_comm]

end Kernel

section WeakType

variable {ι : Type*} [Fintype ι] {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The doubled ball around the centre of a dyadic cube of level `k`, of radius `2ᵏ`, has `2ⁿ`
times the volume of the cube. -/
private theorem volume_closedBall_dyadicCube (k : ℤ) (m : ι → ℤ) :
    volume (closedBall (fun i => ((m i : ℝ) + 2⁻¹) * 2 ^ k) (2 * (2 ^ k / 2))) =
      2 ^ Fintype.card ι * volume (dyadicCube k m) := by
  rw [Real.volume_pi_closedBall _ (by positivity), volume_dyadicCube,
    show (2 : ℝ) * (2 * (2 ^ k / 2)) = 2 * 2 ^ k by ring, mul_pow,
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat]

/-- The union of the doubled balls around the Calderón–Zygmund cubes of `g` at height `t` has
measure at most `2ⁿ / t` times the integral of `g`. -/
private theorem mul_volume_biUnion_closedBall_le (g : (ι → ℝ) → ℝ≥0∞) (t : ℝ≥0∞) :
    t * volume (⋃ q ∈ calderonZygmundCubes g t,
        closedBall (fun i => ((q.2 i : ℝ) + 2⁻¹) * 2 ^ q.1) (2 * (2 ^ q.1 / 2))) ≤
      2 ^ Fintype.card ι * ∫⁻ x, g x := by
  calc _ ≤ t * ∑' q : calderonZygmundCubes g t, volume
        (closedBall (fun i => ((q.1.2 i : ℝ) + 2⁻¹) * 2 ^ q.1.1) (2 * (2 ^ q.1.1 / 2))) :=
        mul_le_mul_right (measure_biUnion_le _ (to_countable _) _) _
    _ = 2 ^ Fintype.card ι *
          (t * volume (⋃ q ∈ calderonZygmundCubes g t, dyadicCube q.1 q.2)) := by
        simp_rw [volume_closedBall_dyadicCube]
        rw [ENNReal.tsum_mul_left, measure_biUnion (to_countable _)
          pairwiseDisjoint_calderonZygmundCubes fun q _ => measurableSet_dyadicCube q.1 q.2]
        ring
    _ ≤ 2 ^ Fintype.card ι * ∫⁻ x, g x :=
        mul_le_mul_right (mul_volume_biUnion_calderonZygmundCubes_le.trans
          (setLIntegral_le_lintegral _ _)) _

omit [CompleteSpace E] in
/-- Chebyshev's inequality for the image of the good part under an operator bounded on `L²`. -/
private theorem mul_volume_lt_enorm_calderonZygmundGood_le [Nonempty ι]
    (T : Lp E 2 (volume : Measure (ι → ℝ)) →L[ℝ] Lp F 2 (volume : Measure (ι → ℝ)))
    {f : (ι → ℝ) → E} (hf : Integrable f) {t : ℝ≥0∞} (ht : t ≠ 0) (ht' : t ≠ ∞) :
    t * volume {x | t / 2 < ‖T ((memLp_two_calderonZygmundGood hf ht ht').toLp _) x‖ₑ} ≤
      4 * 2 ^ Fintype.card ι * ‖T‖ₑ ^ 2 * ∫⁻ x, ‖f x‖ₑ := by
  set u := T ((memLp_two_calderonZygmundGood hf ht ht').toLp _)
  set V := volume {x | t / 2 < ‖u x‖ₑ}
  have hs : t / 2 ≠ 0 := ENNReal.div_ne_zero.2 ⟨ht, ENNReal.ofNat_ne_top⟩
  have hs' : t / 2 ≠ ∞ := ENNReal.div_ne_top ht' two_ne_zero
  have hcheb : (t / 2) ^ 2 * V ≤ eLpNorm u 2 volume ^ 2 := by
    have h := mul_meas_ge_le_pow_eLpNorm' (μ := volume) two_ne_zero ENNReal.ofNat_ne_top
      (f := u) (t / 2)
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat] at h
    have hV : V ≤ volume {x | t / 2 ≤ ‖u x‖ₑ} :=
      measure_mono (ofPred_subset_ofPred.2 fun _ hx => hx.le)
    exact (mul_le_mul_right hV _).trans h
  have hu : eLpNorm u 2 volume ^ 2 ≤
      ‖T‖ₑ ^ 2 * (2 ^ Fintype.card ι * t * ∫⁻ x, ‖f x‖ₑ) := by
    rw [← Lp.enorm_def]
    calc ‖u‖ₑ ^ 2 ≤ (‖T‖ₑ * ‖(memLp_two_calderonZygmundGood hf ht ht').toLp _‖ₑ) ^ 2 :=
          pow_le_pow_left₀ zero_le (T.le_opENorm _) 2
      _ = ‖T‖ₑ ^ 2 * eLpNorm (calderonZygmundGood f t) 2 volume ^ 2 := by
          rw [mul_pow, Lp.enorm_toLp]
      _ ≤ _ := mul_le_mul_right (sq_eLpNorm_calderonZygmundGood_le hf ht) _
  -- With `t = 2 s`, the two bounds read `s² V ≤ ‖T‖² 2ⁿ (2 s) ‖f‖₁`; cancel one factor of `s`.
  have ht2 : t = 2 * (t / 2) := (ENNReal.mul_div_cancel two_ne_zero ENNReal.ofNat_ne_top).symm
  rw [← ENNReal.mul_le_mul_iff_right hs hs']
  calc t / 2 * (t * V) = 2 * ((t / 2) ^ 2 * V) := by
        nth_rewrite 2 [ht2]
        ring
    _ ≤ 2 * (‖T‖ₑ ^ 2 * (2 ^ Fintype.card ι * t * ∫⁻ x, ‖f x‖ₑ)) :=
        mul_le_mul_right (hcheb.trans hu) _
    _ = t / 2 * (4 * 2 ^ Fintype.card ι * ‖T‖ₑ ^ 2 * ∫⁻ x, ‖f x‖ₑ) := by
        nth_rewrite 1 [ht2]
        ring

/-- Off the doubled balls around the Calderón–Zygmund cubes, the cancellation condition bounds the
image of the sum of the bad parts in `L¹` by `2 B ‖f‖₁`. -/
private theorem setLIntegral_compl_enorm_calderonZygmundBad_le [Nonempty ι]
    (T : Lp E 2 (volume : Measure (ι → ℝ)) →L[ℝ] Lp F 2 (volume : Measure (ι → ℝ))) {B : ℝ≥0∞}
    (hT : ∀ (b : Lp E 2 (volume : Measure (ι → ℝ))) (y : ι → ℝ) (r : ℝ),
      (∀ᵐ x, x ∉ closedBall y r → b x = 0) → ∫ x, b x = 0 →
        ∫⁻ x in (closedBall y (2 * r))ᶜ, ‖T b x‖ₑ ≤ B * ∫⁻ x, ‖b x‖ₑ)
    (f : Lp E 2 (volume : Measure (ι → ℝ))) (hf : Integrable f) {t : ℝ≥0∞} (ht : t ≠ 0)
    (ht' : t ≠ ∞) :
    ∫⁻ x in (⋃ q ∈ calderonZygmundCubes (‖f ·‖ₑ) t,
        closedBall (fun i => ((q.2 i : ℝ) + 2⁻¹) * 2 ^ q.1) (2 * (2 ^ q.1 / 2)))ᶜ,
        ‖T (((Lp.memLp f).sub (memLp_two_calderonZygmundGood hf ht ht')).toLp _) x‖ₑ ≤
      2 * B * ∫⁻ x, ‖f x‖ₑ := by
  set 𝒬 := calderonZygmundCubes (‖f ·‖ₑ) t
  set Ω := ⋃ q ∈ 𝒬, closedBall (fun i => ((q.2 i : ℝ) + 2⁻¹) * 2 ^ q.1) (2 * (2 ^ q.1 / 2))
  set b : 𝒬 → Lp E 2 (volume : Measure (ι → ℝ)) := fun q =>
    (memLp_calderonZygmundBad (Lp.memLp f) q.1).toLp _
  have hsum := Lp.ae_enorm_le_tsum_enorm_of_hasSum <| T.hasSum <|
    hasSum_toLp_calderonZygmundBad ENNReal.ofNat_ne_top (Lp.memLp f)
      (memLp_two_calderonZygmundGood hf ht ht')
  -- Each bad part vanishes off the ball around its cube and has integral zero.
  have hb (q : 𝒬) : ∫⁻ x in (closedBall (fun i => ((q.1.2 i : ℝ) + 2⁻¹) * 2 ^ q.1.1)
      (2 * (2 ^ q.1.1 / 2)))ᶜ, ‖T (b q) x‖ₑ ≤
        B * (2 * ∫⁻ x in dyadicCube q.1.1 q.1.2, ‖f x‖ₑ) := by
    have hcoe := (memLp_calderonZygmundBad (Lp.memLp f) q.1).coeFn_toLp
    refine (hT (b q) _ _ ?_ ?_).trans (mul_le_mul_right ?_ _)
    · filter_upwards [hcoe] with x hx hxb
      rw [hx]
      exact calderonZygmundBad_of_notMem fun hxc => hxb (dyadicCube_subset_closedBall _ _ hxc)
    · rw [integral_congr_ae hcoe, integral_calderonZygmundBad]
    · rw [lintegral_congr_ae (hcoe.mono fun x hx => congrArg enorm hx)]
      exact lintegral_enorm_calderonZygmundBad_le _ _
  calc ∫⁻ x in Ωᶜ, ‖T (((Lp.memLp f).sub (memLp_two_calderonZygmundGood hf ht ht')).toLp _) x‖ₑ
      ≤ ∫⁻ x in Ωᶜ, ∑' q : 𝒬, ‖T (b q) x‖ₑ := lintegral_mono_ae (ae_restrict_of_ae hsum)
    _ = ∑' q : 𝒬, ∫⁻ x in Ωᶜ, ‖T (b q) x‖ₑ :=
        lintegral_tsum fun q => (Lp.aestronglyMeasurable _).enorm.restrict
    _ ≤ ∑' q : 𝒬, B * (2 * ∫⁻ x in dyadicCube q.1.1 q.1.2, ‖f x‖ₑ) :=
        ENNReal.tsum_le_tsum fun q => (lintegral_mono_set
          (compl_subset_compl.2 (subset_biUnion_of_mem (u := fun q : ℤ × (ι → ℤ) =>
            closedBall (fun i => ((q.2 i : ℝ) + 2⁻¹) * 2 ^ q.1) (2 * (2 ^ q.1 / 2))) q.2))).trans
          (hb q)
    _ = 2 * B * ∫⁻ x in ⋃ q ∈ 𝒬, dyadicCube q.1 q.2, ‖f x‖ₑ := by
        rw [lintegral_biUnion (to_countable _) (fun q _ => measurableSet_dyadicCube q.1 q.2)
          pairwiseDisjoint_calderonZygmundCubes, ← ENNReal.tsum_mul_left]
        exact tsum_congr fun q => by ring
    _ ≤ 2 * B * ∫⁻ x, ‖f x‖ₑ := mul_le_mul_right (setLIntegral_le_lintegral _ _) _

/-- **The Calderón–Zygmund theorem**, weak type `(1, 1)`. Let `T` be a bounded linear operator on
`L²(ℝⁿ)` satisfying the cancellation condition: for every `b ∈ L²` vanishing off a closed ball
`closedBall y r` with integral zero, `∫_{ℝⁿ \ closedBall y (2r)} ‖T b‖ ≤ B ‖b‖₁`. Then for every
`f ∈ L²` and every `t`,

`t · |{‖T f‖ > t}| ≤ (2ⁿ (4 ‖T‖² + 1) + 4 B) ‖f‖₁`.

The bound is vacuous unless `f` is also integrable. -/
theorem mul_volume_lt_enorm_le_of_setLIntegral_compl_closedBall_le [Nonempty ι]
    (T : Lp E 2 (volume : Measure (ι → ℝ)) →L[ℝ] Lp F 2 (volume : Measure (ι → ℝ))) {B : ℝ≥0∞}
    (hT : ∀ (b : Lp E 2 (volume : Measure (ι → ℝ))) (y : ι → ℝ) (r : ℝ),
      (∀ᵐ x, x ∉ closedBall y r → b x = 0) → ∫ x, b x = 0 →
        ∫⁻ x in (closedBall y (2 * r))ᶜ, ‖T b x‖ₑ ≤ B * ∫⁻ x, ‖b x‖ₑ)
    (f : Lp E 2 (volume : Measure (ι → ℝ))) (t : ℝ≥0∞) :
    t * volume {x | t < ‖T f x‖ₑ} ≤
      (2 ^ Fintype.card ι * (4 * ‖T‖ₑ ^ 2 + 1) + 4 * B) * ∫⁻ x, ‖f x‖ₑ := by
  rcases eq_or_ne (∫⁻ x, ‖f x‖ₑ) ∞ with hI | hI
  · rw [hI, ENNReal.mul_top (by positivity)]
    exact le_top
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  rcases eq_or_ne t ∞ with rfl | ht'
  · simp
  have hf : Integrable f := ⟨Lp.aestronglyMeasurable f, hasFiniteIntegral_iff_enorm.2 hI.lt_top⟩
  have hg := memLp_two_calderonZygmundGood hf ht ht'
  set g := hg.toLp _
  set b := ((Lp.memLp f).sub hg).toLp _
  set Ω := ⋃ q ∈ calderonZygmundCubes (‖f ·‖ₑ) t,
    closedBall (fun i => ((q.2 i : ℝ) + 2⁻¹) * 2 ^ q.1) (2 * (2 ^ q.1 / 2))
  have hΩ : MeasurableSet Ω :=
    .biUnion (to_countable _) fun q _ => isClosed_closedBall.measurableSet
  -- `T f = T g + T b`, so where `‖T f‖ > t` either `‖T g‖ > t / 2`, or `‖T b‖ > t / 2`, the latter
  -- either in `Ω` or off it.
  have hfgb : f = g + b := by
    refine Lp.ext ?_
    filter_upwards [Lp.coeFn_add g b, hg.coeFn_toLp, ((Lp.memLp f).sub hg).coeFn_toLp]
      with x hx hgx hbx
    rw [hx, Pi.add_apply, hgx, hbx, Pi.sub_apply, add_sub_cancel]
  have hsub : {x | t < ‖T f x‖ₑ} ≤ᵐ[volume]
      {x | t / 2 < ‖T g x‖ₑ} ∪ Ω ∪ ({x | t / 2 < ‖T b x‖ₑ} ∩ Ωᶜ) := by
    filter_upwards [Lp.coeFn_add (T g) (T b)] with x hx hxt
    by_contra hnot
    simp only [mem_union, mem_inter_iff, mem_ofPred_eq, mem_compl_iff, not_or, not_and,
      not_not, not_lt] at hnot hxt
    obtain ⟨⟨hgx, hxΩ⟩, hbx⟩ := hnot
    refine (hxt.trans_le ?_).false
    rw [hfgb, map_add, hx, Pi.add_apply, ← ENNReal.add_halves t]
    exact (enorm_add_le _ _).trans (add_le_add hgx (not_lt.1 fun h => hxΩ (hbx h)))
  -- The part of `{‖T b‖ > t / 2}` off `Ω`, by Chebyshev's inequality.
  have hbad : t * volume ({x | t / 2 < ‖T b x‖ₑ} ∩ Ωᶜ) ≤ 4 * B * ∫⁻ x, ‖f x‖ₑ := by
    have ht2 : t = 2 * (t / 2) := (ENNReal.mul_div_cancel two_ne_zero ENNReal.ofNat_ne_top).symm
    rw [← Measure.restrict_apply' hΩ.compl]
    nth_rewrite 1 [ht2]
    rw [mul_assoc]
    calc 2 * (t / 2 * volume.restrict Ωᶜ {x | t / 2 < ‖T b x‖ₑ})
        ≤ 2 * ∫⁻ x in Ωᶜ, ‖T b x‖ₑ := mul_le_mul_right ((mul_le_mul_right
          (measure_mono (ofPred_subset_ofPred.2 fun _ hx => hx.le)) _).trans
            (mul_meas_ge_le_lintegral₀ (Lp.aestronglyMeasurable _).enorm.restrict _)) _
      _ ≤ 2 * (2 * B * ∫⁻ x, ‖f x‖ₑ) := mul_le_mul_right
          (setLIntegral_compl_enorm_calderonZygmundBad_le T hT f hf ht ht') _
      _ = 4 * B * ∫⁻ x, ‖f x‖ₑ := by ring
  calc t * volume {x | t < ‖T f x‖ₑ}
      ≤ t * volume {x | t / 2 < ‖T g x‖ₑ} + t * volume Ω +
          t * volume ({x | t / 2 < ‖T b x‖ₑ} ∩ Ωᶜ) := by
        rw [← mul_add, ← mul_add]
        exact mul_le_mul_right ((measure_mono_ae hsub).trans <| (measure_union_le _ _).trans <|
          add_le_add_left (measure_union_le _ _) _) _
    _ ≤ 4 * 2 ^ Fintype.card ι * ‖T‖ₑ ^ 2 * (∫⁻ x, ‖f x‖ₑ) +
          2 ^ Fintype.card ι * (∫⁻ x, ‖f x‖ₑ) + 4 * B * ∫⁻ x, ‖f x‖ₑ := by
        exact add_le_add (add_le_add (mul_volume_lt_enorm_calderonZygmundGood_le T hf ht ht')
          (mul_volume_biUnion_closedBall_le (fun x => ‖f x‖ₑ) t)) hbad
    _ = (2 ^ Fintype.card ι * (4 * ‖T‖ₑ ^ 2 + 1) + 4 * B) * ∫⁻ x, ‖f x‖ₑ := by ring

/-- **The Calderón–Zygmund theorem** for an operator given by a kernel. Let `T` be a bounded linear
operator on `L²(ℝⁿ)` such that `T b x = ∫ K x y (b y) dy` for almost every `x` off any closed ball
outside which `b` vanishes, where the kernel `K` satisfies Hörmander's condition
`∫_{dist x y' > 2 dist y y'} ‖K x y - K x y'‖ dx ≤ B` for all `y`, `y'`. Then for every `f ∈ L²` and
every `t`,

`t · |{‖T f‖ > t}| ≤ (2ⁿ (4 ‖T‖² + 1) + 4 B) ‖f‖₁`. -/
theorem mul_volume_lt_enorm_le_of_hormander [Nonempty ι] [CompleteSpace F]
    (T : Lp E 2 (volume : Measure (ι → ℝ)) →L[ℝ] Lp F 2 (volume : Measure (ι → ℝ)))
    {K : (ι → ℝ) → (ι → ℝ) → E →L[ℝ] F} (hK : StronglyMeasurable (Function.uncurry K))
    {B : ℝ≥0∞} (hB : ∀ y y', ∫⁻ x in {x | 2 * dist y y' < dist x y'}, ‖K x y - K x y'‖ₑ ≤ B)
    (hrep : ∀ (b : Lp E 2 (volume : Measure (ι → ℝ))) (y : ι → ℝ) (r : ℝ),
      (∀ᵐ x, x ∉ closedBall y r → b x = 0) →
        ∀ᵐ x, x ∉ closedBall y r → T b x = ∫ z, K x z (b z))
    (f : Lp E 2 (volume : Measure (ι → ℝ))) (t : ℝ≥0∞) :
    t * volume {x | t < ‖T f x‖ₑ} ≤
      (2 ^ Fintype.card ι * (4 * ‖T‖ₑ ^ 2 + 1) + 4 * B) * ∫⁻ x, ‖f x‖ₑ := by
  refine mul_volume_lt_enorm_le_of_setLIntegral_compl_closedBall_le T
    (fun b y r hsupp hmean => ?_) f t
  -- A function in `L²` vanishing off a ball is integrable.
  have : IsFiniteMeasure (volume.restrict (closedBall y r)) :=
    isFiniteMeasure_restrict.2 measure_closedBall_lt_top.ne
  have hb : Integrable b := IntegrableOn.integrable_of_ae_notMem_eq_zero
    (((Lp.memLp b).restrict _).integrable one_le_two) hsupp
  exact setLIntegral_compl_closedBall_enorm_le_of_hormander hK hB hb hsupp hmean
    (hrep b y r hsupp)

end WeakType

end TauCeti
