/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.MeasureTheory.Integral.CalderonZygmund.Decomposition
public import TauCeti.MeasureTheory.Integral.MaximalFunction
import TauCeti.Analysis.MeanInequalities
import TauCeti.Analysis.SpecialFunctions.Pow.NNReal
import TauCeti.MeasureTheory.Integral.MinkowskiIntegral
import TauCeti.MeasureTheory.Integral.Marcinkiewicz.General

/-!
# The vector-valued maximal inequality below the diagonal

For `1 < r < ∞` and a countable family `f = (fᵢ)` of functions on `ℝⁿ`, the **`ℓʳ`-valued maximal
function** is `(∑' i, (M fᵢ) ^ r) ^ (1 / r)`, where `M` is the centred Hardy–Littlewood maximal
function `TauCeti.maximalFunction`. The **vector-valued maximal inequality of Fefferman and Stein**
says that it is bounded on `Lᵖ(ℓʳ)` for every `1 < p < ∞`:

`∫⁻ (∑' i, (M fᵢ) ^ r) ^ (p / r) ≤ C(n, r, p) ∫⁻ (∑' i, ‖fᵢ‖ₑ ^ r) ^ (p / r)`.

The diagonal case `p = r` is the scalar maximal inequality summed over `i`
(`TauCeti.lintegral_tsum_maximalFunction_rpow_le`), and the case `r < p` follows from the weighted
maximal inequality by duality (`TauCeti.lintegral_rpow_tsum_maximalFunction_rpow_le`).
This file proves the remaining case `1 < p < r`. With `r = 2` it is the square-function form
`‖(∑' i, (M fᵢ) ^ 2) ^ (1 / 2)‖_p ≤ C ‖(∑' i, ‖fᵢ‖ ^ 2) ^ (1 / 2)‖_p` for `1 < p < 2`, the range
in which Littlewood–Paley theory needs it below `L²`.

The statements are on `ℝⁿ = ι → ℝ`, `n ≥ 1`, with Lebesgue measure and balls taken in the sup
distance, where the Calderón–Zygmund decomposition (`TauCeti.calderonZygmundCubes`) runs on dyadic
cubes.

## The argument

The case `p < r` is Marcinkiewicz interpolation between the diagonal bound and a **weak type
`(1, 1)` bound** for the `ℓʳ`-valued maximal function
(`TauCeti.mul_volume_lt_rpow_tsum_maximalFunction_rpow_le`):

`t · |{(∑' i, (M fᵢ) ^ r) ^ (1 / r) > t}| ≤ C(n, r) ∫⁻ (∑' i, ‖fᵢ‖ₑ ^ r) ^ (1 / r)`.

Write `gᵢ = ‖fᵢ‖ₑ` and `G = (∑' i, gᵢ ^ r) ^ (1 / r)`. Take the Calderón–Zygmund cubes `Q` of `G` at
height `t`, the maximal dyadic cubes with `⨍_Q G > t`, so that `⨍_Q G ≤ 2ⁿ t` and `G ≤ t` almost
everywhere off them. Let `hᵢ` be `gᵢ` off the cubes and its average `⨍_Q gᵢ` on each cube `Q`.

* By Minkowski's integral inequality (`TauCeti.lintegral_Lp_lintegral_le`, for the counting
  measure on the index type), on each cube the `ℓʳ` norm of the averages is at most the average of
  `G`. So the `ℓʳ` norm `H` of `h` is at most `2ⁿ t` almost everywhere and `∫⁻ H ≤ ∫⁻ G`, hence
  `∫⁻ ∑' i, hᵢ ^ r ≤ (2ⁿ t) ^ (r - 1) ∫⁻ G`. The diagonal inequality and Chebyshev's inequality then
  bound the measure of `{(∑' i, (M hᵢ) ^ r) ^ (1 / r) > t}` by a multiple of `∫⁻ G / t`.
* Let `Q*` be the concentric cube of twice the side. If `x ∉ Q*` and a ball `B(x, ρ)` meets `Q`,
  then `Q ⊆ B(x, 3ρ)`. Since `hᵢ` has the same integral as `gᵢ` over each cube, for `x` outside
  every `Q*` this gives `∫_{B(x, ρ)} gᵢ ≤ ∫_{B(x, 3ρ)} hᵢ`, so `M gᵢ x ≤ 3ⁿ M hᵢ x`. The maximal
  function cannot see the cancellation of `gᵢ - hᵢ`, but it does not need to: the enlarged ball
  swallows every cube it meets.
* The cubes `Q*` have total measure at most `2ⁿ ∑ |Q| ≤ 2ⁿ ∫⁻ G / t`.

For the strong bound at a height `t`, split each `gᵢ` according to whether `G` exceeds `t`. The
part above the height contributes through the weak type `(1, 1)` bound and the part below it
through the diagonal `Lʳ` bound, which is the hypothesis of the Marcinkiewicz engine
`TauCeti.lintegral_rpow_le_of_meas_ofReal_lt_le`.

## Main declarations

* `TauCeti.mul_volume_lt_rpow_tsum_maximalFunction_rpow_le`: the weak type `(1, 1)` bound for the
  `ℓʳ`-valued maximal function.
* `TauCeti.lintegral_rpow_tsum_maximalFunction_rpow_le_of_one_lt_of_lt`: the vector-valued
  maximal inequality for `1 < p < r`.

## References

* C. Fefferman, E. M. Stein, *Some maximal inequalities*, Amer. J. Math. **93** (1971), 107–115,
  Theorem 1.
* E. M. Stein, *Harmonic Analysis: Real-Variable Methods, Orthogonality, and Oscillatory
  Integrals*, Chapter II, §1.
* L. Grafakos, *Classical Fourier Analysis*, 3rd ed., Section 5.6.
-/

public section

namespace TauCeti

open MeasureTheory Metric Set
open scoped ENNReal

variable {ι κ : Type*} [Fintype ι] [Countable κ]

section Average

/-- The family `g` averaged over the Calderón–Zygmund cubes of `G` at height `t`: on each cube
`Q` the function `g i` is replaced by its average over `Q`, and off the cubes it is left
unchanged. -/
private noncomputable def cubeAverage (G : (ι → ℝ) → ℝ≥0∞) (t : ℝ≥0∞) (g : (ι → ℝ) → ℝ≥0∞) :
    (ι → ℝ) → ℝ≥0∞ :=
  fun x => (⋃ q ∈ calderonZygmundCubes G t, dyadicCube q.1 q.2)ᶜ.indicator g x +
    ∑' q : calderonZygmundCubes G t,
      (dyadicCube q.1.1 q.1.2).indicator (fun _ => ⨍⁻ y in dyadicCube q.1.1 q.1.2, g y) x

variable {G g : (ι → ℝ) → ℝ≥0∞} {t : ℝ≥0∞} {q : ℤ × (ι → ℤ)} {x : ι → ℝ}

private theorem cubeAverage_of_mem (hq : q ∈ calderonZygmundCubes G t)
    (hx : x ∈ dyadicCube q.1 q.2) :
    cubeAverage G t g x = ⨍⁻ y in dyadicCube q.1 q.2, g y := by
  have hsum : ∑' q' : calderonZygmundCubes G t,
      (dyadicCube q'.1.1 q'.1.2).indicator (fun _ => ⨍⁻ y in dyadicCube q'.1.1 q'.1.2, g y) x =
      ⨍⁻ y in dyadicCube q.1 q.2, g y := by
    rw [tsum_eq_single ⟨q, hq⟩ fun q' hne => indicator_of_notMem (fun hx' =>
      Set.disjoint_left.1 (pairwiseDisjoint_calderonZygmundCubes q'.2 hq
        fun h => hne (Subtype.ext h)) hx' hx) _]
    exact indicator_of_mem hx _
  rw [cubeAverage, hsum, indicator_of_notMem (notMem_compl_iff.2 (mem_biUnion hq hx)), zero_add]

private theorem cubeAverage_of_forall_notMem
    (hx : ∀ q ∈ calderonZygmundCubes G t, x ∉ dyadicCube q.1 q.2) :
    cubeAverage G t g x = g x := by
  have hx' : x ∈ (⋃ q ∈ calderonZygmundCubes G t, dyadicCube q.1 q.2)ᶜ := by
    simpa using hx
  rw [cubeAverage, indicator_of_mem hx']
  simp [fun q : calderonZygmundCubes G t =>
    indicator_of_notMem (hx q.1 q.2) (fun _ => ⨍⁻ y in dyadicCube q.1.1 q.1.2, g y)]

private theorem measurable_cubeAverage (hg : Measurable g) : Measurable (cubeAverage G t g) :=
  ((hg.indicator (measurableSet_biUnion_calderonZygmundCubes G t).compl).add
    (Measurable.tsum fun q => measurable_const.indicator
      (measurableSet_dyadicCube q.1.1 q.1.2)))

/-- Over a Calderón–Zygmund cube, the averaged function has the same integral as `g`. -/
private theorem setLIntegral_cubeAverage (hq : q ∈ calderonZygmundCubes G t) :
    ∫⁻ y in dyadicCube q.1 q.2, cubeAverage G t g y = ∫⁻ y in dyadicCube q.1 q.2, g y := by
  rw [setLIntegral_congr_fun (measurableSet_dyadicCube q.1 q.2)
      fun y hy => cubeAverage_of_mem hq hy, setLIntegral_const,
    mul_comm, measure_mul_setLAverage _ (volume_dyadicCube_ne_top _ _)]

/-- Away from the doubled Calderón–Zygmund cubes, the integral of `g` over a ball is at most the
integral of the averaged function over the concentric ball of three times the radius. -/
private theorem setLIntegral_ball_le_setLIntegral_cubeAverage
    (hx : ∀ q ∈ calderonZygmundCubes G t,
      x ∉ ball (fun i => ((q.2 i : ℝ) + 2⁻¹) * 2 ^ q.1) (2 ^ q.1)) {ρ : ℝ}
    (hρ : 0 < ρ) :
    ∫⁻ y in ball x ρ, g y ≤ ∫⁻ y in ball x (3 * ρ), cubeAverage G t g y := by
  set C := calderonZygmundCubes G t
  set Ω := ⋃ q ∈ C, dyadicCube q.1 q.2
  have hΩ : MeasurableSet Ω := measurableSet_biUnion_calderonZygmundCubes G t
  have hdisj := pairwiseDisjoint_calderonZygmundCubes (g := G) (t := t)
  -- The part of the ball inside the cubes, cube by cube.
  have hin : ∫⁻ y in ball x ρ ∩ Ω, g y ≤ ∫⁻ y in ball x (3 * ρ) ∩ Ω, cubeAverage G t g y := by
    simp only [Ω, inter_iUnion₂]
    rw [lintegral_biUnion C.to_countable (fun q _ => measurableSet_ball.inter
        (measurableSet_dyadicCube _ _)) (hdisj.mono fun _ => inter_subset_right),
      lintegral_biUnion C.to_countable (fun q _ => measurableSet_ball.inter
        (measurableSet_dyadicCube _ _)) (hdisj.mono fun _ => inter_subset_right)]
    refine tsum_le_tsum fun q => ?_
    rcases (ball x ρ ∩ dyadicCube q.1.1 q.1.2).eq_empty_or_nonempty with hempty | hmeet
    · simp [hempty]
    rw [inter_eq_right.2 (dyadicCube_subset_ball_three_mul (hx q.1 q.2) hmeet),
      setLIntegral_cubeAverage q.2]
    exact lintegral_mono_set inter_subset_right
  -- The part of the ball outside the cubes, where the averaged function is `g`.
  have hout : ∫⁻ y in ball x ρ \ Ω, g y ≤ ∫⁻ y in ball x (3 * ρ) \ Ω, cubeAverage G t g y := by
    rw [setLIntegral_congr_fun (measurableSet_ball.diff hΩ) fun y hy =>
      (cubeAverage_of_forall_notMem fun q hq hyq => hy.2 (mem_biUnion hq hyq)).symm]
    exact lintegral_mono_set (sdiff_subset_sdiff_left (ball_subset_ball (by linarith)))
  rw [← lintegral_inter_add_sdiff _ _ hΩ, ← lintegral_inter_add_sdiff _ (ball x (3 * ρ)) hΩ]
  exact add_le_add hin hout

/-- Away from the doubled Calderón–Zygmund cubes, the maximal function of `g` is at most `3ⁿ`
times the maximal function of the averaged function. -/
private theorem maximalFunction_le_three_pow_mul_maximalFunction_cubeAverage
    (hx : ∀ q ∈ calderonZygmundCubes G t,
      x ∉ ball (fun i => ((q.2 i : ℝ) + 2⁻¹) * 2 ^ q.1) (2 ^ q.1)) :
    maximalFunction volume g x ≤
      3 ^ Fintype.card ι * maximalFunction volume (cubeAverage G t g) x := by
  refine maximalFunction_le fun ρ hρ => ?_
  have hvol : volume (ball x (3 * ρ)) = 3 ^ Fintype.card ι * volume (ball x ρ) := by
    rw [Real.volume_pi_ball _ (by positivity), Real.volume_pi_ball _ hρ,
      show 2 * (3 * ρ) = 3 * (2 * ρ) by ring, mul_pow, ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
  have h3 : (3 : ℝ≥0∞) ^ Fintype.card ι ≠ 0 := pow_ne_zero _ (by norm_num)
  have h3' : (3 : ℝ≥0∞) ^ Fintype.card ι ≠ ∞ := ENNReal.pow_ne_top (by norm_num)
  calc ⨍⁻ y in ball x ρ, ‖g y‖ₑ = (∫⁻ y in ball x ρ, g y) / volume (ball x ρ) := by
        simp only [eNorm_eq_self, setLAverage_eq]
    _ ≤ (∫⁻ y in ball x (3 * ρ), cubeAverage G t g y) / volume (ball x ρ) :=
        ENNReal.div_le_div_right (setLIntegral_ball_le_setLIntegral_cubeAverage hx hρ) _
    _ = 3 ^ Fintype.card ι * ⨍⁻ y in ball x (3 * ρ), ‖cubeAverage G t g y‖ₑ := by
        simp only [eNorm_eq_self, setLAverage_eq, hvol]
        rw [← mul_div_assoc, ENNReal.mul_div_mul_left _ _ h3 h3']
    _ ≤ 3 ^ Fintype.card ι * maximalFunction volume (cubeAverage G t g) x := by
        gcongr
        exact setLAverage_le_maximalFunction _ _ _ (by positivity)

end Average

section Family

variable {g : κ → (ι → ℝ) → ℝ≥0∞} {r : ℝ} {t : ℝ≥0∞} {q : ℤ × (ι → ℤ)} {x : ι → ℝ}

/-- On a Calderón–Zygmund cube `Q` of `G`, the `ℓʳ` norm of the averaged family is the `ℓʳ` norm
of the averages of `g` over `Q`, which by Minkowski's integral inequality is at most the average of
the `ℓʳ` norm of `g` over `Q`. -/
private theorem tsum_cubeAverage_rpow_rpow_le {G : (ι → ℝ) → ℝ≥0∞} (hg : ∀ i, Measurable (g i))
    (hr : 1 ≤ r) (hq : q ∈ calderonZygmundCubes G t) (hx : x ∈ dyadicCube q.1 q.2) :
    (∑' i, cubeAverage G t (g i) x ^ r) ^ (1 / r) ≤
      ⨍⁻ y in dyadicCube q.1 q.2, (∑' i, g i y ^ r) ^ (1 / r) := by
  simp only [cubeAverage_of_mem hq hx]
  let _ : MeasurableSpace κ := ⊤
  have : MeasurableSingletonClass κ := ⟨fun _ => trivial⟩
  have key := lintegral_Lp_lintegral_le (μ := (Measure.count : Measure κ))
    (ν := ((volume.restrict (dyadicCube q.1 q.2)) univ)⁻¹ • volume.restrict (dyadicCube q.1 q.2))
    (f := g) (measurable_from_prod_countable_right fun i => hg i).aemeasurable hr
  simpa only [lintegral_count, ← laverage_eq'] using key

/-- Averaging over the Calderón–Zygmund cubes of the `ℓʳ` norm `G` of `g` does not increase the
integral of the `ℓʳ` norm. -/
private theorem lintegral_tsum_cubeAverage_rpow_rpow_le (hg : ∀ i, Measurable (g i)) (hr : 1 ≤ r)
    (t : ℝ≥0∞) :
    ∫⁻ x, (∑' i, cubeAverage (fun y => (∑' i, g i y ^ r) ^ (1 / r)) t (g i) x ^ r) ^ (1 / r) ≤
      ∫⁻ x, (∑' i, g i x ^ r) ^ (1 / r) := by
  set G : (ι → ℝ) → ℝ≥0∞ := fun y => (∑' i, g i y ^ r) ^ (1 / r)
  set C := calderonZygmundCubes G t
  set Ω := ⋃ q ∈ C, dyadicCube q.1 q.2
  have hΩ : MeasurableSet Ω := measurableSet_biUnion_calderonZygmundCubes G t
  have hdisj := pairwiseDisjoint_calderonZygmundCubes (g := G) (t := t)
  rw [← lintegral_add_compl _ hΩ, ← lintegral_add_compl G hΩ]
  refine add_le_add ?_ (le_of_eq (setLIntegral_congr_fun hΩ.compl fun y hy => ?_))
  · rw [lintegral_biUnion C.to_countable (fun q _ => measurableSet_dyadicCube _ _) hdisj,
      lintegral_biUnion C.to_countable (fun q _ => measurableSet_dyadicCube _ _) hdisj]
    refine tsum_le_tsum fun q => ?_
    calc ∫⁻ y in dyadicCube q.1.1 q.1.2, (∑' i, cubeAverage G t (g i) y ^ r) ^ (1 / r)
        ≤ ∫⁻ _ in dyadicCube q.1.1 q.1.2, ⨍⁻ y in dyadicCube q.1.1 q.1.2, G y :=
          setLIntegral_mono measurable_const fun y hy => tsum_cubeAverage_rpow_rpow_le hg hr q.2 hy
      _ = ∫⁻ y in dyadicCube q.1.1 q.1.2, G y := by
          rw [setLIntegral_const, mul_comm,
            measure_mul_setLAverage _ (volume_dyadicCube_ne_top _ _)]
  · simp only [cubeAverage_of_forall_notMem fun _ hq hyq => hy (mem_biUnion hq hyq), G]

omit [Countable κ] in
/-- Away from the doubled Calderón–Zygmund cubes of `G`, the `ℓʳ` norm of the maximal functions
of `g` is at most `3ⁿ` times that of the maximal functions of the averaged family. -/
private theorem rpow_tsum_maximalFunction_rpow_le_three_pow_mul {G : (ι → ℝ) → ℝ≥0∞} (hr : 0 < r)
    (hx : ∀ q ∈ calderonZygmundCubes G t,
      x ∉ ball (fun i => ((q.2 i : ℝ) + 2⁻¹) * 2 ^ q.1) (2 ^ q.1)) :
    (∑' i, maximalFunction volume (g i) x ^ r) ^ (1 / r) ≤
      3 ^ Fintype.card ι *
        (∑' i, maximalFunction volume (cubeAverage G t (g i)) x ^ r) ^ (1 / r) := by
  -- The common factor `3ⁿ` leaves the `ℓʳ` norm.
  rw [← ENNReal.rpow_rpow_inv hr.ne' (3 ^ Fintype.card ι), ← one_div,
    ← ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.2 hr.le), ← ENNReal.tsum_mul_left]
  gcongr with i
  rw [← ENNReal.mul_rpow_of_nonneg _ _ hr.le]
  gcongr
  exact maximalFunction_le_three_pow_mul_maximalFunction_cubeAverage hx

/-- Chebyshev's inequality and the diagonal vector-valued maximal inequality for a measurable
family `g`: the sum `∑' i, (M gᵢ) ^ r` reaches `s` on a set of measure at most
`cᵣ 4ⁿ ∫⁻ ∑' i, gᵢ ^ r / s`. -/
private theorem mul_volume_le_tsum_maximalFunction_rpow (hg : ∀ i, Measurable (g i)) (hr : 1 < r)
    (s : ℝ≥0∞) :
    s * volume {x | s ≤ ∑' i, maximalFunction volume (g i) x ^ r} ≤
      ENNReal.ofReal (2 * r * 2 ^ (r - 1) / (r - 1)) * 4 ^ Fintype.card ι *
        ∫⁻ x, ∑' i, g i x ^ r := by
  have hM : Measurable fun x => ∑' i, maximalFunction volume (g i) x ^ r :=
    Measurable.tsum fun i => (measurable_maximalFunction volume (g i)).pow_const r
  have hdiag := lintegral_tsum_maximalFunction_rpow_le volume (f := g)
    (fun i => (hg i).eNorm.aemeasurable) hr
  simp only [eNorm_eq_self, Module.finrank_fintype_fun_eq_card] at hdiag
  exact (mul_meas_ge_le_lintegral₀ hM.aemeasurable s).trans hdiag

variable [Nonempty ι]

/-- The `ℓʳ` norm of the family averaged over the Calderón–Zygmund cubes of the `ℓʳ` norm `G` of
`g` at a height `t ≠ 0` is at most `2ⁿ t` almost everywhere. -/
private theorem ae_tsum_cubeAverage_rpow_rpow_le (hg : ∀ i, Measurable (g i)) (hr : 1 ≤ r)
    (hfin : ∫⁻ x, (∑' i, g i x ^ r) ^ (1 / r) ≠ ∞) (ht : t ≠ 0) :
    ∀ᵐ x, (∑' i, cubeAverage (fun y => (∑' i, g i y ^ r) ^ (1 / r)) t (g i) x ^ r) ^ (1 / r) ≤
      2 ^ Fintype.card ι * t := by
  set G : (ι → ℝ) → ℝ≥0∞ := fun y => (∑' i, g i y ^ r) ^ (1 / r)
  have hG : Measurable G := (Measurable.tsum fun i => (hg i).pow_const r).pow_const _
  filter_upwards [ae_le_of_forall_notMem_calderonZygmundCubes hG.aemeasurable hfin ht] with x hx
  by_cases hmem : ∃ q ∈ calderonZygmundCubes G t, x ∈ dyadicCube q.1 q.2
  · obtain ⟨q, hq, hxq⟩ := hmem
    exact (tsum_cubeAverage_rpow_rpow_le hg hr hq hxq).trans
      (setLAverage_le_of_mem_calderonZygmundCubes hq)
  · push Not at hmem
    simp only [cubeAverage_of_forall_notMem hmem]
    exact (hx hmem).trans (le_mul_of_one_le_left' (one_le_pow₀ (by norm_num)))

/-- The `r`-th powers of the family averaged over the Calderón–Zygmund cubes of the `ℓʳ` norm `G`
of `g` at a height `t ≠ 0` have integral at most `(2ⁿ t) ^ (r - 1) ∫⁻ G`. -/
private theorem lintegral_tsum_cubeAverage_rpow_le (hg : ∀ i, Measurable (g i)) (hr : 1 ≤ r)
    (hfin : ∫⁻ x, (∑' i, g i x ^ r) ^ (1 / r) ≠ ∞) (ht : t ≠ 0) :
    ∫⁻ x, ∑' i, cubeAverage (fun y => (∑' i, g i y ^ r) ^ (1 / r)) t (g i) x ^ r ≤
      (2 ^ Fintype.card ι * t) ^ (r - 1) * ∫⁻ x, (∑' i, g i x ^ r) ^ (1 / r) := by
  set G : (ι → ℝ) → ℝ≥0∞ := fun y => (∑' i, g i y ^ r) ^ (1 / r)
  set H : (ι → ℝ) → ℝ≥0∞ := fun x => (∑' i, cubeAverage G t (g i) x ^ r) ^ (1 / r)
  have hr0 : r ≠ 0 := (zero_lt_one.trans_le hr).ne'
  have hH : Measurable H := (Measurable.tsum fun i =>
    (measurable_cubeAverage (hg i)).pow_const r).pow_const _
  have hpow (x : ι → ℝ) : ∑' i, cubeAverage G t (g i) x ^ r = H x ^ (r - 1) * H x := by
    conv_rhs => enter [2]; rw [← ENNReal.rpow_one (H x)]
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by linarith) zero_le_one, sub_add_cancel]
    simp only [H, one_div, ENNReal.rpow_inv_rpow hr0]
  calc ∫⁻ x, ∑' i, cubeAverage G t (g i) x ^ r
      = ∫⁻ x, H x ^ (r - 1) * H x := lintegral_congr fun x => hpow x
    _ ≤ ∫⁻ x, (2 ^ Fintype.card ι * t) ^ (r - 1) * H x := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_tsum_cubeAverage_rpow_rpow_le hg hr hfin ht] with x hx
        gcongr
    _ = (2 ^ Fintype.card ι * t) ^ (r - 1) * ∫⁻ x, H x := lintegral_const_mul _ hH
    _ ≤ (2 ^ Fintype.card ι * t) ^ (r - 1) * ∫⁻ x, G x :=
        mul_le_mul_right (lintegral_tsum_cubeAverage_rpow_rpow_le hg hr t) _

/-- Chebyshev's inequality and the diagonal vector-valued maximal inequality, applied to the family
averaged over the Calderón–Zygmund cubes of the `ℓʳ` norm `G` of `g` at a height `t`: the `ℓʳ`
norm of its maximal functions reaches `t` on a set of measure at most
`cᵣ 4ⁿ (2ⁿ) ^ (r - 1) ∫⁻ G / t`. -/
private theorem mul_volume_le_tsum_maximalFunction_cubeAverage_rpow (hg : ∀ i, Measurable (g i))
    (hr : 1 < r) (hfin : ∫⁻ x, (∑' i, g i x ^ r) ^ (1 / r) ≠ ∞) (ht : t ≠ 0) (ht' : t ≠ ∞) :
    t * volume {x | t ^ r ≤ ∑' i, maximalFunction volume
        (cubeAverage (fun y => (∑' i, g i y ^ r) ^ (1 / r)) t (g i)) x ^ r} ≤
      ENNReal.ofReal (2 * r * 2 ^ (r - 1) / (r - 1)) * 4 ^ Fintype.card ι *
        (2 ^ Fintype.card ι) ^ (r - 1) * ∫⁻ x, (∑' i, g i x ^ r) ^ (1 / r) := by
  set n := Fintype.card ι
  set G : (ι → ℝ) → ℝ≥0∞ := fun y => (∑' i, g i y ^ r) ^ (1 / r)
  set h : κ → (ι → ℝ) → ℝ≥0∞ := fun i => cubeAverage G t (g i)
  set cr := ENNReal.ofReal (2 * r * 2 ^ (r - 1) / (r - 1)) * 4 ^ n
  set S := {x | t ^ r ≤ ∑' i, maximalFunction volume (h i) x ^ r}
  have htr : t ^ (r - 1) ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.2 ht) ht').ne'
  have htr' : t ^ (r - 1) ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by linarith) ht'
  refine (ENNReal.mul_le_mul_iff_right htr htr').1 ?_
  calc t ^ (r - 1) * (t * volume S) = t ^ r * volume S := by
        conv_rhs => rw [← sub_add_cancel r 1]
        rw [ENNReal.rpow_add_of_nonneg _ _ (by linarith) zero_le_one, ENNReal.rpow_one,
          mul_assoc]
    _ ≤ cr * ∫⁻ x, ∑' i, h i x ^ r :=
        mul_volume_le_tsum_maximalFunction_rpow (fun i => measurable_cubeAverage (hg i)) hr _
    _ ≤ cr * ((2 ^ n * t) ^ (r - 1) * ∫⁻ x, G x) := by
        gcongr
        exact lintegral_tsum_cubeAverage_rpow_le hg hr.le hfin ht
    _ = t ^ (r - 1) * (cr * (2 ^ n) ^ (r - 1) * ∫⁻ x, G x) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by linarith)]
        ring

/-- The weak type `(1, 1)` estimate for a measurable family, at the height `3ⁿ t`: off the doubled
Calderón–Zygmund cubes of the `ℓʳ` norm of `g`, the maximal functions of `g` are controlled by
those of the averaged family. -/
private theorem mul_volume_lt_three_pow_mul_le (hg : ∀ i, Measurable (g i)) (hr : 1 < r)
    (hfin : ∫⁻ x, (∑' i, g i x ^ r) ^ (1 / r) ≠ ∞) (ht : t ≠ 0) (ht' : t ≠ ∞) :
    t * volume {x | 3 ^ Fintype.card ι * t <
        (∑' i, maximalFunction volume (g i) x ^ r) ^ (1 / r)} ≤
      (2 ^ Fintype.card ι + ENNReal.ofReal (2 * r * 2 ^ (r - 1) / (r - 1)) *
        4 ^ Fintype.card ι * (2 ^ Fintype.card ι) ^ (r - 1)) *
        ∫⁻ x, (∑' i, g i x ^ r) ^ (1 / r) := by
  set n := Fintype.card ι
  set G : (ι → ℝ) → ℝ≥0∞ := fun y => (∑' i, g i y ^ r) ^ (1 / r)
  set C := calderonZygmundCubes G t
  set h : κ → (ι → ℝ) → ℝ≥0∞ := fun i => cubeAverage G t (g i)
  set Ωs := ⋃ q ∈ C, ball (fun i => ((q.2 i : ℝ) + 2⁻¹) * 2 ^ q.1) (2 ^ q.1)
  set S := {x | t ^ r ≤ ∑' i, maximalFunction volume (h i) x ^ r}
  have hr0 : 0 < r := by linarith
  -- The doubled cubes lie in the closed balls of radius twice half the side around the cubes.
  have hΩs : t * volume Ωs ≤ 2 ^ n * ∫⁻ x, G x := by
    calc t * volume Ωs ≤ t * volume (⋃ q ∈ C,
          closedBall (fun i => ((q.2 i : ℝ) + 2⁻¹) * 2 ^ q.1) (2 * (2 ^ q.1 / 2))) := by
          refine mul_le_mul_right (measure_mono (biUnion_mono subset_rfl fun q _ => ?_)) _
          rw [show (2 : ℝ) * (2 ^ q.1 / 2) = 2 ^ q.1 by ring]
          exact ball_subset_closedBall
      _ ≤ 2 ^ n * ∫⁻ x, G x := by
          simpa only [ENNReal.ofReal_ofNat] using
            mul_volume_biUnion_closedBall_calderonZygmundCubes_le 2 G t
  have hsub : {x | 3 ^ n * t < (∑' i, maximalFunction volume (g i) x ^ r) ^ (1 / r)} ⊆
      Ωs ∪ S := by
    intro x hx
    by_cases hxΩ : x ∈ Ωs
    · exact Or.inl hxΩ
    have hlt : t < (∑' i, maximalFunction volume (h i) x ^ r) ^ (1 / r) :=
      lt_of_mul_lt_mul_left (hx.trans_le (rpow_tsum_maximalFunction_rpow_le_three_pow_mul hr0
        fun q hq hxq => hxΩ (mem_biUnion hq hxq))) zero_le
    rw [one_div, ENNReal.lt_rpow_inv_iff hr0] at hlt
    exact Or.inr hlt.le
  calc t * volume {x | 3 ^ n * t < (∑' i, maximalFunction volume (g i) x ^ r) ^ (1 / r)}
      ≤ t * (volume Ωs + volume S) := by
        gcongr
        exact (measure_mono hsub).trans (measure_union_le _ _)
    _ = t * volume Ωs + t * volume S := mul_add _ _ _
    _ ≤ (2 ^ n * ∫⁻ x, G x) + ENNReal.ofReal (2 * r * 2 ^ (r - 1) / (r - 1)) * 4 ^ n *
          (2 ^ n) ^ (r - 1) * ∫⁻ x, G x :=
        add_le_add hΩs
          (mul_volume_le_tsum_maximalFunction_cubeAverage_rpow hg hr hfin ht ht')
    _ = _ := by ring

end Family

section Main

variable {F : Type*} [ENorm F] {f : κ → (ι → ℝ) → F} {r : ℝ}

/-- The part of a measurable family on a measurable set `V`, through the diagonal `Lʳ` bound and
Chebyshev's inequality: the `ℓʳ` norm of its maximal functions reaches `t / 2` on a set of measure
at most `2 ^ r cᵣ 4ⁿ t ^ (-r) ∫_V G ^ r`, where `G` is the `ℓʳ` norm of the family. -/
private theorem volume_half_rpow_le_setLIntegral {g : κ → (ι → ℝ) → ℝ≥0∞}
    (hg : ∀ i, Measurable (g i)) (hr : 1 < r) {V : Set (ι → ℝ)} (hV : MeasurableSet V) {t : ℝ}
    (ht : 0 < t) :
    volume {x | (ENNReal.ofReal t / 2) ^ r ≤
        ∑' i, maximalFunction volume (V.indicator (g i)) x ^ r} ≤
      2 ^ r * (ENNReal.ofReal (2 * r * 2 ^ (r - 1) / (r - 1)) * 4 ^ Fintype.card ι) *
        ENNReal.ofReal (t ^ (-r)) * ∫⁻ x in V, ((∑' i, g i x ^ r) ^ (1 / r)) ^ r := by
  set G : (ι → ℝ) → ℝ≥0∞ := fun y => (∑' i, g i y ^ r) ^ (1 / r)
  set cr := ENNReal.ofReal (2 * r * 2 ^ (r - 1) / (r - 1)) * 4 ^ Fintype.card ι
  set T := ENNReal.ofReal t
  set S := {x | (T / 2) ^ r ≤ ∑' i, maximalFunction volume (V.indicator (g i)) x ^ r}
  have hr0 : 0 < r := by linarith
  have hT2 : T / 2 ≠ 0 := (ENNReal.div_pos (ENNReal.ofReal_pos.2 ht).ne' (by norm_num)).ne'
  have hT2' : T / 2 ≠ ∞ := ENNReal.div_ne_top ENNReal.ofReal_ne_top (by norm_num)
  have hpow (x : ι → ℝ) : ∑' i, V.indicator (g i) x ^ r = V.indicator (fun y => G y ^ r) x := by
    calc ∑' i, V.indicator (g i) x ^ r = ((∑' i, V.indicator (g i) x ^ r) ^ (1 / r)) ^ r := by
          rw [one_div, ENNReal.rpow_inv_rpow hr0.ne']
      _ = V.indicator G x ^ r := by rw [rpow_tsum_indicator_rpow V g hr0]
      _ = V.indicator (fun y => G y ^ r) x :=
          congrFun (indicator_comp_of_zero (g := fun a : ℝ≥0∞ => a ^ r)
            (ENNReal.zero_rpow_of_pos hr0)).symm x
  have hTr : (T / 2) ^ r ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.2 hT2) hT2').ne'
  have hTr' : (T / 2) ^ r ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hr0.le hT2'
  have hTrinv : ((T / 2) ^ r)⁻¹ = 2 ^ r * ENNReal.ofReal (t ^ (-r)) := by
    rw [ENNReal.div_rpow_of_nonneg _ _ hr0.le, ENNReal.inv_div
      (.inl (ENNReal.rpow_ne_top_of_nonneg hr0.le ENNReal.ofNat_ne_top))
      (.inl (ENNReal.rpow_pos (by norm_num) ENNReal.ofNat_ne_top).ne'), div_eq_mul_inv,
      ← ENNReal.rpow_neg, ENNReal.ofReal_rpow_of_pos ht]
  calc volume S = ((T / 2) ^ r)⁻¹ * ((T / 2) ^ r * volume S) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hTr hTr', one_mul]
    _ ≤ ((T / 2) ^ r)⁻¹ * (cr * ∫⁻ x, ∑' i, V.indicator (g i) x ^ r) :=
        mul_le_mul_right
          (mul_volume_le_tsum_maximalFunction_rpow (fun i => (hg i).indicator hV) hr _) _
    _ = 2 ^ r * cr * ENNReal.ofReal (t ^ (-r)) * ∫⁻ x in V, G x ^ r := by
        rw [lintegral_congr hpow, lintegral_indicator hV, hTrinv]
        ring

variable [Nonempty ι]

/-- **The vector-valued maximal inequality of Fefferman and Stein**, weak type `(1, 1)`: for
`1 < r` and a countable family `f` on `ℝⁿ = ι → ℝ`, `n ≥ 1`, with balls taken in the sup distance,

`t · |{(∑' i, (M fᵢ) ^ r) ^ (1 / r) > t}| ≤ C ∫⁻ (∑' i, ‖fᵢ‖ₑ ^ r) ^ (1 / r)`,

with `C = 3ⁿ (2ⁿ + cᵣ 4ⁿ (2ⁿ) ^ (r - 1))` and `cᵣ = 2 r 2 ^ (r - 1) / (r - 1)`, which depends only
on `n` and `r`. -/
theorem mul_volume_lt_rpow_tsum_maximalFunction_rpow_le
    (hf : ∀ i, AEMeasurable (fun x => ‖f i x‖ₑ)) (hr : 1 < r) (t : ℝ≥0∞) :
    t * volume {x | t < (∑' i, maximalFunction volume (f i) x ^ r) ^ (1 / r)} ≤
      3 ^ Fintype.card ι * (2 ^ Fintype.card ι + ENNReal.ofReal (2 * r * 2 ^ (r - 1) / (r - 1)) *
        4 ^ Fintype.card ι * (2 ^ Fintype.card ι) ^ (r - 1)) *
        ∫⁻ x, (∑' i, ‖f i x‖ₑ ^ r) ^ (1 / r) := by
  obtain ⟨g, hg, hM, hfg⟩ := exists_measurable_maximalFunction_eq hf
  have hint : ∫⁻ x, (∑' i, ‖f i x‖ₑ ^ r) ^ (1 / r) = ∫⁻ x, (∑' i, g i x ^ r) ^ (1 / r) :=
    lintegral_congr_ae (by filter_upwards [hfg] with x hx; simp only [hx])
  simp only [hM, hint]
  set n := Fintype.card ι
  have h3 : (3 : ℝ≥0∞) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have h3' : (3 : ℝ≥0∞) ^ n ≠ ∞ := ENNReal.pow_ne_top (by norm_num)
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  rcases eq_or_ne t ∞ with rfl | ht'
  · simp
  rcases eq_or_ne (∫⁻ x, (∑' i, g i x ^ r) ^ (1 / r)) ∞ with hfin | hfin
  · rw [hfin, ENNReal.mul_top (mul_ne_zero h3 (by simp))]
    exact le_top
  -- Apply the estimate at the height `3ⁿ s` with `s = t / 3ⁿ`.
  set s := t / 3 ^ n
  have hts : t = 3 ^ n * s := (ENNReal.mul_div_cancel h3 h3').symm
  calc t * volume {x | t < (∑' i, maximalFunction volume (g i) x ^ r) ^ (1 / r)}
      = 3 ^ n * (s * volume {x | 3 ^ n * s <
          (∑' i, maximalFunction volume (g i) x ^ r) ^ (1 / r)}) := by
        rw [← mul_assoc, ← hts]
    _ ≤ _ := by
        rw [mul_assoc (3 ^ n : ℝ≥0∞)]
        exact mul_le_mul_right (mul_volume_lt_three_pow_mul_le hg hr hfin
          (ENNReal.div_pos ht h3').ne' (ENNReal.div_ne_top ht' h3)) _

/-- The part of a measurable family on a measurable set `V`, through the weak type `(1, 1)` bound:
the `ℓʳ` norm of its maximal functions exceeds `t / 2` on a set of measure at most
`2 C₁ t⁻¹ ∫_V G`, where `G` is the `ℓʳ` norm of the family. -/
private theorem volume_lt_half_le_setLIntegral {g : κ → (ι → ℝ) → ℝ≥0∞}
    (hg : ∀ i, Measurable (g i)) (hr : 1 < r) {V : Set (ι → ℝ)} (hV : MeasurableSet V) {t : ℝ}
    (ht : 0 < t) :
    volume {x | ENNReal.ofReal t / 2 <
        (∑' i, maximalFunction volume (V.indicator (g i)) x ^ r) ^ (1 / r)} ≤
      2 * (3 ^ Fintype.card ι * (2 ^ Fintype.card ι + ENNReal.ofReal (2 * r * 2 ^ (r - 1) /
        (r - 1)) * 4 ^ Fintype.card ι * (2 ^ Fintype.card ι) ^ (r - 1))) *
        ENNReal.ofReal (t ^ (-1 : ℝ)) * ∫⁻ x in V, (∑' i, g i x ^ r) ^ (1 / r) := by
  set T := ENNReal.ofReal t
  set S := {x | T / 2 < (∑' i, maximalFunction volume (V.indicator (g i)) x ^ r) ^ (1 / r)}
  have hT2 : T / 2 ≠ 0 := (ENNReal.div_pos (ENNReal.ofReal_pos.2 ht).ne' (by norm_num)).ne'
  have hT2' : T / 2 ≠ ∞ := ENNReal.div_ne_top ENNReal.ofReal_ne_top (by norm_num)
  have hTinv : (T / 2)⁻¹ = 2 * ENNReal.ofReal (t ^ (-1 : ℝ)) := by
    rw [ENNReal.inv_div (.inl ENNReal.ofNat_ne_top) (.inl two_ne_zero), div_eq_mul_inv,
      Real.rpow_neg_one, ENNReal.ofReal_inv_of_pos ht]
  have h := mul_volume_lt_rpow_tsum_maximalFunction_rpow_le
    (fun i => ((hg i).indicator hV).eNorm.aemeasurable) hr (T / 2)
  simp only [eNorm_eq_self, rpow_tsum_indicator_rpow V g (by linarith : 0 < r),
    lintegral_indicator hV] at h
  calc volume S = (T / 2)⁻¹ * (T / 2 * volume S) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hT2 hT2', one_mul]
    _ ≤ (T / 2)⁻¹ * (3 ^ Fintype.card ι * (2 ^ Fintype.card ι +
          ENNReal.ofReal (2 * r * 2 ^ (r - 1) / (r - 1)) * 4 ^ Fintype.card ι *
            (2 ^ Fintype.card ι) ^ (r - 1)) * ∫⁻ x in V, (∑' i, g i x ^ r) ^ (1 / r)) :=
        mul_le_mul_right h _
    _ = _ := by
        rw [hTinv]
        ring

/-- The distributional estimate behind the strong type `(p, p)` bound for `1 < p < r`: at each
height `t`, only the part of `g` whose `ℓʳ` norm exceeds `t` contributes through the weak type
`(1, 1)` bound, and the rest through the diagonal `Lʳ` bound. -/
private theorem volume_lt_rpow_tsum_maximalFunction_rpow_le {g : κ → (ι → ℝ) → ℝ≥0∞}
    (hg : ∀ i, Measurable (g i)) (hr : 1 < r) {t : ℝ} (ht : 0 < t) :
    volume {x | ENNReal.ofReal t < (∑' i, maximalFunction volume (g i) x ^ r) ^ (1 / r)} ≤
      2 * (3 ^ Fintype.card ι * (2 ^ Fintype.card ι + ENNReal.ofReal (2 * r * 2 ^ (r - 1) /
        (r - 1)) * 4 ^ Fintype.card ι * (2 ^ Fintype.card ι) ^ (r - 1))) *
        ENNReal.ofReal (t ^ (-1 : ℝ)) * (∫⁻ x in {x | ENNReal.ofReal (1 * t) <
          (∑' i, g i x ^ r) ^ (1 / r)}, ((∑' i, g i x ^ r) ^ (1 / r)) ^ (1 : ℝ)) +
      2 ^ r * (ENNReal.ofReal (2 * r * 2 ^ (r - 1) / (r - 1)) * 4 ^ Fintype.card ι) *
        ENNReal.ofReal (t ^ (-r)) * ∫⁻ x in {x | (∑' i, g i x ^ r) ^ (1 / r) ≤
          ENNReal.ofReal (1 * t)}, ((∑' i, g i x ^ r) ^ (1 / r)) ^ r := by
  rw [one_mul]
  simp only [ENNReal.rpow_one]
  set G : (ι → ℝ) → ℝ≥0∞ := fun y => (∑' i, g i y ^ r) ^ (1 / r)
  set T := ENNReal.ofReal t
  set U := {x | T < G x}
  have hU : MeasurableSet U :=
    measurableSet_lt measurable_const ((Measurable.tsum fun i => (hg i).pow_const r).pow_const _)
  -- Split `g` at the height `t`: `g = U.indicator g + Uᶜ.indicator g`.
  have hsplit (x : ι → ℝ) : (∑' i, maximalFunction volume (g i) x ^ r) ^ (1 / r) ≤
      (∑' i, maximalFunction volume (U.indicator (g i)) x ^ r) ^ (1 / r) +
        (∑' i, maximalFunction volume (Uᶜ.indicator (g i)) x ^ r) ^ (1 / r) := by
    refine le_trans ?_ (ENNReal.Lp_add_le_tsum _ _ hr.le)
    gcongr with i
    have h := maximalFunction_add_le (μ := volume) (g := Uᶜ.indicator (g i))
      ((hg i).indicator hU).eNorm.aemeasurable x
    rwa [indicator_self_add_compl] at h
  have hsub : {x | T < (∑' i, maximalFunction volume (g i) x ^ r) ^ (1 / r)} ⊆
      {x | T / 2 < (∑' i, maximalFunction volume (U.indicator (g i)) x ^ r) ^ (1 / r)} ∪
        {x | (T / 2) ^ r ≤ ∑' i, maximalFunction volume (Uᶜ.indicator (g i)) x ^ r} := by
    intro x hx
    by_contra hnot
    simp only [mem_union, mem_ofPred_eq, not_or, not_lt, not_le] at hnot
    have hlo : (∑' i, maximalFunction volume (Uᶜ.indicator (g i)) x ^ r) ^ (1 / r) ≤ T / 2 := by
      rw [one_div, ENNReal.rpow_inv_le_iff (by linarith)]
      exact hnot.2.le
    exact (mem_ofPred_eq ▸ hx).not_ge
      ((hsplit x).trans ((add_le_add hnot.1 hlo).trans (ENNReal.add_halves T).le))
  have hU' : Uᶜ = {x | G x ≤ T} := by
    ext x
    simp [U]
  rw [← hU']
  exact (measure_mono hsub).trans ((measure_union_le _ _).trans
    (add_le_add (volume_lt_half_le_setLIntegral hg hr hU ht)
      (volume_half_rpow_le_setLIntegral hg hr hU.compl ht)))

/-- **The vector-valued maximal inequality of Fefferman and Stein** for `1 < p < r`: on
`ℝⁿ = ι → ℝ`, `n ≥ 1`, with balls taken in the sup distance, the `ℓʳ`-valued maximal function is
bounded on `Lᵖ(ℓʳ)`,

`∫⁻ (∑' i, (M fᵢ) ^ r) ^ (p / r) ≤ C * ∫⁻ (∑' i, ‖fᵢ‖ₑ ^ r) ^ (p / r)`,

with `C = p / (p - 1) · 2 C₁ + p / (r - p) · 2 ^ r cᵣ 4ⁿ`, where
`C₁ = 3ⁿ (2ⁿ + cᵣ 4ⁿ (2ⁿ) ^ (r - 1))` is the weak type `(1, 1)` constant of
`TauCeti.mul_volume_lt_rpow_tsum_maximalFunction_rpow_le` and `cᵣ = 2 r 2 ^ (r - 1) / (r - 1)`;
it depends only on `n`, `r` and `p`. Together with the diagonal case
`TauCeti.lintegral_tsum_maximalFunction_rpow_le` and the case `r < p`
(`TauCeti.lintegral_rpow_tsum_maximalFunction_rpow_le`) this covers every `1 < p < ∞`; for
`r = 2` it is the square-function form
`‖(∑' i, (M fᵢ) ^ 2) ^ (1 / 2)‖_p ≤ C' ‖(∑' i, ‖fᵢ‖ ^ 2) ^ (1 / 2)‖_p` for `1 < p < 2`. -/
theorem lintegral_rpow_tsum_maximalFunction_rpow_le_of_one_lt_of_lt
    (hf : ∀ i, AEMeasurable (fun x => ‖f i x‖ₑ)) {p : ℝ} (hp : 1 < p) (hpr : p < r) :
    ∫⁻ x, (∑' i, maximalFunction volume (f i) x ^ r) ^ (p / r) ≤
      (ENNReal.ofReal (p / (p - 1)) * (2 * (3 ^ Fintype.card ι * (2 ^ Fintype.card ι +
          ENNReal.ofReal (2 * r * 2 ^ (r - 1) / (r - 1)) * 4 ^ Fintype.card ι *
            (2 ^ Fintype.card ι) ^ (r - 1)))) +
        ENNReal.ofReal (p / (r - p)) * (2 ^ r * (ENNReal.ofReal (2 * r * 2 ^ (r - 1) / (r - 1)) *
          4 ^ Fintype.card ι))) *
        ∫⁻ x, (∑' i, ‖f i x‖ₑ ^ r) ^ (p / r) := by
  obtain ⟨g, hg, hM, hfg⟩ := exists_measurable_maximalFunction_eq hf
  have hint : ∫⁻ x, (∑' i, ‖f i x‖ₑ ^ r) ^ (p / r) = ∫⁻ x, (∑' i, g i x ^ r) ^ (p / r) :=
    lintegral_congr_ae (by filter_upwards [hfg] with x hx; simp only [hx])
  simp only [hM, hint]
  have hpow (a : ℝ≥0∞) : (a ^ (1 / r)) ^ p = a ^ (p / r) := by
    rw [← ENNReal.rpow_mul, one_div_mul_eq_div]
  -- Marcinkiewicz interpolation between the exponents `1` and `r`, splitting at the height `t`.
  have key := lintegral_rpow_le_of_meas_ofReal_lt_le (μ := volume) (ν := volume)
    (f := fun x => (∑' i, g i x ^ r) ^ (1 / r))
    (u := fun x => (∑' i, maximalFunction volume (g i) x ^ r) ^ (1 / r))
    ((Measurable.tsum fun i => (hg i).pow_const r).pow_const _).aemeasurable
    ((Measurable.tsum fun i =>
      (measurable_maximalFunction volume (g i)).pow_const r).pow_const _).aemeasurable
    zero_lt_one hp hpr one_pos fun t ht =>
      volume_lt_rpow_tsum_maximalFunction_rpow_le hg (hp.trans hpr) ht
  simpa only [hpow, Real.one_rpow, mul_one] using key

end Main

end TauCeti
