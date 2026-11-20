/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.CalderonZygmund.Decomposition
public import TauCeti.MeasureTheory.Integral.MaximalFunction
import Mathlib.MeasureTheory.Measure.Haar.Unique
import TauCeti.Analysis.SpecialFunctions.Pow.NNReal
import TauCeti.MeasureTheory.Integral.Marcinkiewicz.General
import TauCeti.MeasureTheory.Integral.MinkowskiIntegral

/-!
# The vector-valued maximal inequality below the diagonal

Let `μ` be an additive Haar measure on a finite-dimensional real normed space `E`, let `M` be the
centred Hardy–Littlewood maximal function (`TauCeti.maximalFunction`) and let `1 < r < ∞`. The
**vector-valued maximal inequality** of Fefferman and Stein says that the `ℓʳ`-valued maximal
function `x ↦ (∑' i, (M fᵢ x) ^ r) ^ (1 / r)` of a countable family is bounded on `Lᵖ(ℓʳ)` for
every `1 < p < ∞`. For `r = 2` this bounds the maximal functions of the pieces of a square function,
the form Littlewood–Paley theory uses. The range `r ≤ p` is
`TauCeti.lintegral_tsum_maximalFunction_rpow_le` and
`TauCeti.lintegral_rpow_tsum_maximalFunction_rpow_le_of_exponent_lt`, proved from the weighted
inequality by duality. This file proves the weak type `(1, 1)` endpoint
(`TauCeti.mul_measure_lt_tsum_maximalFunction_rpow_rpow_inv_le`) and the remaining range
`1 < p < r` (`TauCeti.lintegral_rpow_tsum_maximalFunction_rpow_le_of_lt_exponent`), which for
`r = 2` is the square-function form for `1 < p < 2`.

## The argument

The weak type `(1, 1)` bound is proved on `ι → ℝ` with the sup norm, whose balls are cubes, by the
Calderón–Zygmund decomposition at height `t` of the pointwise `ℓʳ` norm
`F = (∑' i, ‖fᵢ‖ₑ ^ r) ^ (1 / r)` (`TauCeti.calderonZygmundCubes`).

* **The good part.** Off the cubes `F ≤ t` almost everywhere, so the family restricted off the
  cubes has `∫⁻ ∑' i, ‖gᵢ‖ₑ ^ r ≤ t ^ (r - 1) ∫⁻ F`, and the diagonal `Lʳ(ℓʳ)` bound with
  Chebyshev's inequality controls it.
* **The bad part.** Replace each `fᵢ` on a cube `Q` by its average over `Q`. By Minkowski's
  inequality the averages have `ℓʳ` norm at most the average of `F`, which is at most `2ⁿ t`, so
  the averaged family is again controlled in `Lʳ(ℓʳ)`. A ball about a point outside the concentric
  cubes `3Q` that meets `Q` contains `Q` once its radius is doubled, so there the maximal function
  of `fᵢ` restricted to the cubes is at most `2ⁿ` times that of the averaged family.
* **The exceptional set.** The cubes `3Q` have total measure at most `3ⁿ ∫⁻ F / t`.

The strong bound for `1 < p < r` then follows by Marcinkiewicz interpolation between the weak type
`(1, 1)` bound and the diagonal `Lʳ(ℓʳ)` bound
(`TauCeti.lintegral_rpow_le_of_meas_ofReal_lt_le`), splitting the family according to whether `F`
exceeds the height. A continuous linear equivalence `e : E ≃L[ℝ] (ι → ℝ)` transports both bounds
to `E`, at the cost of the factor `(‖e‖ ‖e⁻¹‖)ⁿ` comparing the balls of the two norms
(`TauCeti.maximalFunction_le_ofReal_mul_maximalFunction_map`).

## Main declarations

* `TauCeti.vectorMaximalFunctionWeakConst`: the constant of the weak type `(1, 1)` bound on
  `ι → ℝ`.
* `TauCeti.mul_measure_lt_tsum_maximalFunction_rpow_rpow_inv_le`: the weak type `(1, 1)` bound
  for the `ℓʳ`-valued maximal function.
* `TauCeti.lintegral_rpow_tsum_maximalFunction_rpow_le_of_lt_exponent`: its `Lᵖ(ℓʳ)` bound for
  `1 < p < r`, below the exponent `r` of the sum.

## References

* C. Fefferman, E. M. Stein, *Some maximal inequalities*, Amer. J. Math. **93** (1971), 107–115,
  Theorem 1.
* L. Grafakos, *Classical Fourier Analysis*, Section 5.6.
-/

public section

namespace TauCeti

open Filter MeasureTheory Metric Module Set
open scoped ENNReal

variable {ι κ : Type*} [Fintype ι]

/-! ### Elementary estimates: powers in `ℝ≥0∞` and Chebyshev -/

/-- If `s ^ r < ∑' i, (a i + b i) ^ r` with `1 ≤ r`, then `(s / 2) ^ r` lies below one of
`∑' i, a i ^ r` and `∑' i, b i ^ r`. -/
private theorem rpow_div_two_lt_or_of_rpow_lt_tsum_add {r : ℝ} (hr : 1 ≤ r) {a b : κ → ℝ≥0∞}
    {s : ℝ≥0∞} (h : s ^ r < ∑' i, (a i + b i) ^ r) :
    (s / 2) ^ r < ∑' i, a i ^ r ∨ (s / 2) ^ r < ∑' i, b i ^ r := by
  by_contra! hab
  refine h.not_ge ?_
  calc ∑' i, (a i + b i) ^ r ≤ ∑' i, 2 ^ (r - 1) * (a i ^ r + b i ^ r) :=
        tsum_le_tsum fun i => ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hr
    _ = 2 ^ (r - 1) * (∑' i, a i ^ r + ∑' i, b i ^ r) := by
        rw [ENNReal.tsum_mul_left, tsum_add]
    _ ≤ 2 ^ (r - 1) * ((s / 2) ^ r + (s / 2) ^ r) := by gcongr <;> [exact hab.1; exact hab.2]
    _ = s ^ r := by
        have h2 : (2 : ℝ≥0∞) ^ (r - 1) * 2 = 2 ^ r := by
          nth_rw 2 [← ENNReal.rpow_one 2]
          rw [← ENNReal.rpow_add _ _ two_ne_zero ENNReal.ofNat_ne_top, sub_add_cancel]
        rw [← two_mul, ← mul_assoc, h2, ← ENNReal.mul_rpow_of_nonneg _ _ (by linarith),
          ENNReal.mul_div_cancel two_ne_zero ENNReal.ofNat_ne_top]

/-- Chebyshev's inequality at the level `(s / 2) ^ r`:
`μ {(s / 2) ^ r < Ψ} ≤ 2 ^ r (s ^ r)⁻¹ ∫⁻ Ψ`. -/
private theorem measure_rpow_div_two_lt_le {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {Ψ : X → ℝ≥0∞} (hΨ : AEMeasurable Ψ μ) {r : ℝ} (hr : 0 < r) {s : ℝ≥0∞} (hs : s ≠ 0)
    (hs' : s ≠ ∞) :
    μ {x | (s / 2) ^ r < Ψ x} ≤ 2 ^ r * (s ^ r)⁻¹ * ∫⁻ x, Ψ x ∂μ := by
  have h0 : (s / 2) ^ r ≠ 0 :=
    (ENNReal.rpow_pos (ENNReal.div_pos hs ENNReal.ofNat_ne_top) (ENNReal.div_ne_top hs'
      two_ne_zero)).ne'
  have htop : (s / 2) ^ r ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hr.le (ENNReal.div_ne_top hs'
    two_ne_zero)
  calc μ {x | (s / 2) ^ r < Ψ x} ≤ μ {x | (s / 2) ^ r ≤ Ψ x} :=
        measure_mono fun _ hx => by simp only [mem_ofPred_eq] at hx ⊢; exact hx.le
    _ ≤ (∫⁻ x, Ψ x ∂μ) / (s / 2) ^ r := meas_ge_le_lintegral_div hΨ h0 htop
    _ = 2 ^ r * (s ^ r)⁻¹ * ∫⁻ x, Ψ x ∂μ := by
        rw [ENNReal.div_rpow_of_nonneg _ _ hr.le, div_eq_mul_inv,
          ENNReal.inv_div (.inl (ENNReal.rpow_ne_top_of_nonneg hr.le ENNReal.ofNat_ne_top))
            (.inl (ENNReal.rpow_pos two_pos ENNReal.ofNat_ne_top).ne'),
          div_eq_mul_inv]
        ring

/-- Chebyshev's inequality for `Ψ` with `∫⁻ Ψ ≤ K t ^ (r - 1) I`:
`t μ {(t / 2) ^ r < Ψ} ≤ 2 ^ r K I`. This is how the `Lʳ` bounds of the good and the bad part
become weak type `(1, 1)` bounds. -/
private theorem mul_measure_rpow_div_two_lt_le {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {Ψ : X → ℝ≥0∞} (hΨ : AEMeasurable Ψ μ) {r : ℝ} (hr : 0 < r) {t K I : ℝ≥0∞} (ht : t ≠ 0)
    (ht' : t ≠ ∞) (h : ∫⁻ x, Ψ x ∂μ ≤ K * t ^ (r - 1) * I) :
    t * μ {x | (t / 2) ^ r < Ψ x} ≤ 2 ^ r * K * I := by
  have htr : t * t ^ (r - 1) * (t ^ r)⁻¹ = 1 := by
    nth_rw 1 [← ENNReal.rpow_one t]
    rw [← ENNReal.rpow_add _ _ ht ht', add_sub_cancel,
      ENNReal.mul_inv_cancel (ENNReal.rpow_pos (pos_iff_ne_zero.2 ht) ht').ne'
        (ENNReal.rpow_ne_top_of_nonneg hr.le ht')]
  calc t * μ {x | (t / 2) ^ r < Ψ x} ≤ t * (2 ^ r * (t ^ r)⁻¹ * (K * t ^ (r - 1) * I)) := by
        gcongr
        exact (measure_rpow_div_two_lt_le hΨ hr ht ht').trans (by gcongr)
    _ = 2 ^ r * K * I * (t * t ^ (r - 1) * (t ^ r)⁻¹) := by ring
    _ = 2 ^ r * K * I := by rw [htr, mul_one]

/-! ### Averages over a family of dyadic cubes -/

/-- The function equal to `0` off the dyadic cubes of `T` and, when they are pairwise disjoint, to
the average of `g` over the cube of `T` containing the point. -/
private noncomputable def cubeAverage (T : Set (ℤ × (ι → ℤ))) (g : (ι → ℝ) → ℝ≥0∞)
    (y : ι → ℝ) : ℝ≥0∞ :=
  ∑' q : T,
    (dyadicCube q.val.1 q.val.2).indicator (fun _ => ⨍⁻ z in dyadicCube q.val.1 q.val.2, g z) y

variable {T : Set (ℤ × (ι → ℤ))} {g : (ι → ℝ) → ℝ≥0∞}

private theorem measurable_cubeAverage (T : Set (ℤ × (ι → ℤ))) (g : (ι → ℝ) → ℝ≥0∞) :
    Measurable (cubeAverage T g) :=
  Measurable.tsum fun _ => measurable_const.indicator (measurableSet_dyadicCube _ _)

private theorem cubeAverage_of_mem (hT : T.PairwiseDisjoint fun q => dyadicCube q.1 q.2)
    {q : ℤ × (ι → ℤ)} (hq : q ∈ T) {y : ι → ℝ} (hy : y ∈ dyadicCube q.1 q.2) :
    cubeAverage T g y = ⨍⁻ z in dyadicCube q.1 q.2, g z := by
  rw [cubeAverage.eq_def, tsum_eq_single ⟨q, hq⟩ fun q' hq' => indicator_of_notMem (fun hy' =>
    (hT q'.property hq (fun h => hq' (Subtype.ext h))).le_bot ⟨hy', hy⟩) _]
  exact indicator_of_mem hy _

private theorem cubeAverage_of_forall_notMem {y : ι → ℝ}
    (hy : ∀ q ∈ T, y ∉ dyadicCube q.1 q.2) : cubeAverage T g y = 0 :=
  tsum_eq_zero_iff.2 fun q => indicator_of_notMem (hy q.val q.property) _

/-- The integral of `cubeAverage T g` over a set `A`. -/
private theorem setLIntegral_cubeAverage (A : Set (ι → ℝ)) :
    ∫⁻ y in A, cubeAverage T g y =
      ∑' q : T, (⨍⁻ z in dyadicCube q.val.1 q.val.2, g z) *
        volume (A ∩ dyadicCube q.val.1 q.val.2) := by
  unfold cubeAverage
  rw [lintegral_tsum fun _ =>
    (measurable_const.indicator (measurableSet_dyadicCube _ _)).aemeasurable]
  refine tsum_congr fun q => ?_
  rw [lintegral_indicator_const (measurableSet_dyadicCube _ _),
    Measure.restrict_apply (measurableSet_dyadicCube _ _), inter_comm]

/-- **The bad part.** Let `x` lie outside the threefold enlargements of the dyadic cubes of `T`.
Then the maximal function at `x` of the restriction of `g` to the cubes is at most `2ⁿ` times
that of the cube averages of `g`: a ball about `x` that meets one of the cubes contains it once
its radius is doubled. -/
private theorem maximalFunction_indicator_biUnion_le {x : ι → ℝ}
    (hx : ∀ q ∈ T, x ∉ ball (fun i => ((q.2 i : ℝ) + 2⁻¹) * 2 ^ q.1) (3 * (2 ^ q.1 / 2))) :
    maximalFunction volume ((⋃ q ∈ T, dyadicCube q.1 q.2).indicator g) x ≤
      2 ^ Fintype.card ι * maximalFunction volume (cubeAverage T g) x := by
  have hU : MeasurableSet (⋃ q ∈ T, dyadicCube q.1 q.2) :=
    MeasurableSet.biUnion T.to_countable fun q _ => measurableSet_dyadicCube _ _
  refine maximalFunction_le fun ρ hρ => ?_
  have h2B : volume (ball x (2 * ρ)) = 2 ^ Fintype.card ι * volume (ball x ρ) := by
    rw [volume.addHaar_ball_mul_of_pos x two_pos, ENNReal.ofReal_pow zero_le_two,
      ENNReal.ofReal_ofNat, Module.finrank_fintype_fun_eq_card, volume.addHaar_ball_center x]
  simp only [eNorm_eq_self]
  rw [setLAverage_eq]
  refine ENNReal.div_le_of_le_mul ?_
  calc ∫⁻ y in ball x ρ, (⋃ q ∈ T, dyadicCube q.1 q.2).indicator g y
      = ∫⁻ y in ⋃ q : T, dyadicCube q.val.1 q.val.2, g y ∂volume.restrict (ball x ρ) := by
        rw [lintegral_indicator hU, biUnion_eq_iUnion]
    _ ≤ ∑' q : T, ∫⁻ y in dyadicCube q.val.1 q.val.2, g y ∂volume.restrict (ball x ρ) :=
        lintegral_iUnion_le _ _
    _ ≤ ∑' q : T, (⨍⁻ z in dyadicCube q.val.1 q.val.2, g z) *
          volume (ball x (2 * ρ) ∩ dyadicCube q.val.1 q.val.2) := by
        refine tsum_le_tsum fun q => ?_
        rw [Measure.restrict_restrict (measurableSet_dyadicCube _ _)]
        rcases (ball x ρ ∩ dyadicCube q.val.1 q.val.2).eq_empty_or_nonempty with h | h
        · rw [inter_comm, h]
          simp
        · rw [inter_eq_right.2 (dyadicCube_subset_ball_two_mul (hx q.val q.property) h), mul_comm,
            measure_mul_setLAverage _ (volume_dyadicCube_ne_top _ _)]
          exact lintegral_mono_set inter_subset_left
    _ = ∫⁻ y in ball x (2 * ρ), cubeAverage T g y := (setLIntegral_cubeAverage _).symm
    _ ≤ volume (ball x (2 * ρ)) * maximalFunction volume (cubeAverage T g) x := by
        simpa only [eNorm_eq_self] using setLIntegral_ball_le_measure_mul_maximalFunction
          (μ := volume) (f := cubeAverage T g) (x := x) (by positivity) measure_ball_lt_top.ne
    _ = 2 ^ Fintype.card ι * maximalFunction volume (cubeAverage T g) x * volume (ball x ρ) := by
        rw [h2B]
        ring

/-! ### The Calderón–Zygmund cubes of the pointwise `ℓʳ` norm -/

/-- The constant `3ⁿ + 2 ^ r (1 + (2ⁿ) ^ (2 r - 1)) c(n, r)` of the weak type `(1, 1)` bound for the
`ℓʳ`-valued maximal function on `ι → ℝ` in dimension `n`
(`TauCeti.mul_measure_lt_tsum_maximalFunction_rpow_rpow_inv_le`), where `c(n, r)` is the constant
`TauCeti.maximalFunctionConst n r` of the scalar maximal inequality. -/
noncomputable def vectorMaximalFunctionWeakConst (n : ℕ) (r : ℝ) : ℝ≥0∞ :=
  3 ^ n + 2 ^ r * (1 + (2 ^ n) ^ (2 * r - 1)) * maximalFunctionConst n r

theorem vectorMaximalFunctionWeakConst_def (n : ℕ) (r : ℝ) :
    vectorMaximalFunctionWeakConst n r =
      3 ^ n + 2 ^ r * (1 + (2 ^ n) ^ (2 * r - 1)) * maximalFunctionConst n r := (rfl)

section Cubes

variable [Countable κ] {g : κ → (ι → ℝ) → ℝ≥0∞} {r : ℝ} {t : ℝ≥0∞}

/-- On the Calderón–Zygmund cubes at height `t` of the pointwise `ℓʳ` norm
`F = (∑' i, gᵢ ^ r) ^ r⁻¹`, the cube averages of the `gᵢ` have `ℓʳ` norm at most `2ⁿ t`, and so
`∑' i, (cube average of gᵢ) ^ r ≤ (2ⁿ t) ^ (r - 1) · (cube average of F)`. -/
private theorem tsum_cubeAverage_rpow_le (hg : ∀ i, Measurable (g i)) (hr : 1 ≤ r)
    (y : ι → ℝ) :
    ∑' i, cubeAverage (calderonZygmundCubes (fun x => (∑' i, g i x ^ r) ^ r⁻¹) t) (g i) y ^ r ≤
      (2 ^ Fintype.card ι * t) ^ (r - 1) *
        cubeAverage (calderonZygmundCubes (fun x => (∑' i, g i x ^ r) ^ r⁻¹) t)
          (fun x => (∑' i, g i x ^ r) ^ r⁻¹) y := by
  by_cases hy : ∃ q ∈ calderonZygmundCubes (fun x => (∑' i, g i x ^ r) ^ r⁻¹) t,
      y ∈ dyadicCube q.1 q.2
  · obtain ⟨q, hq, hyq⟩ := hy
    simp only [cubeAverage_of_mem pairwiseDisjoint_calderonZygmundCubes hq hyq]
    exact (tsum_setLAverage_rpow_le _ hg hr).trans
      (ENNReal.rpow_le_rpow_sub_one_mul (setLAverage_le_of_mem_calderonZygmundCubes hq) hr)
  · simp only [not_exists, not_and] at hy
    simp only [cubeAverage_of_forall_notMem hy, ENNReal.zero_rpow_of_pos (by linarith : 0 < r),
      tsum_zero, mul_zero, le_refl]

/-- The integral form of `tsum_cubeAverage_rpow_le`:
`∫⁻ ∑' i, (cube average of gᵢ) ^ r ≤ (2ⁿ t) ^ (r - 1) ∫⁻ F`. -/
private theorem lintegral_tsum_cubeAverage_rpow_le (hg : ∀ i, Measurable (g i)) (hr : 1 ≤ r) :
    ∫⁻ y, ∑' i,
        cubeAverage (calderonZygmundCubes (fun x => (∑' i, g i x ^ r) ^ r⁻¹) t) (g i) y ^ r ≤
      (2 ^ Fintype.card ι * t) ^ (r - 1) * ∫⁻ x, (∑' i, g i x ^ r) ^ r⁻¹ := by
  set F : (ι → ℝ) → ℝ≥0∞ := fun x => (∑' i, g i x ^ r) ^ r⁻¹
  calc ∫⁻ y, ∑' i, cubeAverage (calderonZygmundCubes F t) (g i) y ^ r
      ≤ ∫⁻ y, (2 ^ Fintype.card ι * t) ^ (r - 1) * cubeAverage (calderonZygmundCubes F t) F y :=
        lintegral_mono fun y => tsum_cubeAverage_rpow_le hg hr y
    _ = (2 ^ Fintype.card ι * t) ^ (r - 1) * ∫⁻ y, cubeAverage (calderonZygmundCubes F t) F y :=
        lintegral_const_mul _ (measurable_cubeAverage _ _)
    _ ≤ (2 ^ Fintype.card ι * t) ^ (r - 1) * ∫⁻ x, F x := by
        gcongr (2 ^ Fintype.card ι * t) ^ (r - 1) * ?_
        have h := setLIntegral_cubeAverage (T := calderonZygmundCubes F t) (g := F) univ
        simp only [Measure.restrict_univ, univ_inter] at h
        rw [h]
        simp_rw [mul_comm (⨍⁻ z in _, F z),
          measure_mul_setLAverage _ (volume_dyadicCube_ne_top _ _)]
        rw [← lintegral_biUnion (to_countable _) (fun q _ => measurableSet_dyadicCube _ _)
          pairwiseDisjoint_calderonZygmundCubes]
        exact setLIntegral_le_lintegral _ _

/-- **The good part.** Off its Calderón–Zygmund cubes at a positive height `t`, the pointwise `ℓʳ`
norm `F` is at most `t` almost everywhere, so that
`∑' i, (gᵢ restricted off the cubes) ^ r ≤ t ^ (r - 1) F` almost everywhere. -/
private theorem ae_tsum_indicator_compl_rpow_le [Nonempty ι] (hg : ∀ i, Measurable (g i))
    (hr : 1 ≤ r) (hF : ∫⁻ x, (∑' i, g i x ^ r) ^ r⁻¹ ≠ ∞) (ht : t ≠ 0) :
    ∀ᵐ y, ∑' i, (⋃ q ∈ calderonZygmundCubes (fun x => (∑' i, g i x ^ r) ^ r⁻¹) t,
        dyadicCube q.1 q.2)ᶜ.indicator (g i) y ^ r ≤ t ^ (r - 1) * (∑' i, g i y ^ r) ^ r⁻¹ := by
  have hFm : Measurable fun x => (∑' i, g i x ^ r) ^ r⁻¹ :=
    (Measurable.tsum fun i => (hg i).pow_const r).pow_const _
  filter_upwards [ae_le_of_forall_notMem_calderonZygmundCubes hFm.aemeasurable le_rfl
    (by simpa only [ENNReal.rpow_one] using hF) ht] with y hy
  by_cases hyU : y ∈ ⋃ q ∈ calderonZygmundCubes (fun x => (∑' i, g i x ^ r) ^ r⁻¹) t,
      dyadicCube q.1 q.2
  · simp only [indicator_of_notMem (notMem_compl_iff.2 hyU),
      ENNReal.zero_rpow_of_pos (by linarith : 0 < r), tsum_zero]
    exact bot_le
  · simp only [indicator_of_mem (mem_compl hyU)]
    have hle := hy (by simpa only [mem_iUnion, not_exists] using hyU)
    calc ∑' i, g i y ^ r = ((∑' i, g i y ^ r) ^ r⁻¹) ^ r :=
          (ENNReal.rpow_inv_rpow (by linarith) _).symm
      _ ≤ t ^ (r - 1) * (∑' i, g i y ^ r) ^ r⁻¹ := ENNReal.rpow_le_rpow_sub_one_mul hle hr

omit [Countable κ] in
/-- **The splitting.** Let `T` be a family of dyadic cubes. A point where the `ℓʳ` norm of the
maximal functions of the `gᵢ` exceeds `t` lies in the concentric cube of three times the side of a
cube of `T`, or there the `ℓʳ` norm of the maximal functions of the `gᵢ` restricted off the cubes,
or `2ⁿ` times that of the maximal functions of their cube averages, exceeds `t / 2`. -/
private theorem setOf_rpow_lt_tsum_maximalFunction_subset (hg : ∀ i, Measurable (g i))
    (hr : 1 ≤ r) (T : Set (ℤ × (ι → ℤ))) (t : ℝ≥0∞) :
    {x | t ^ r < ∑' i, maximalFunction volume (g i) x ^ r} ⊆
      (⋃ q ∈ T, ball (fun i => ((q.2 i : ℝ) + 2⁻¹) * 2 ^ q.1) (3 * (2 ^ q.1 / 2))) ∪
        {x | (t / 2) ^ r < ∑' i,
          maximalFunction volume ((⋃ q ∈ T, dyadicCube q.1 q.2)ᶜ.indicator (g i)) x ^ r} ∪
        {x | (t / 2) ^ r < ∑' i,
          (2 ^ Fintype.card ι * maximalFunction volume (cubeAverage T (g i)) x) ^ r} := by
  intro x hx
  rw [mem_ofPred_eq] at hx
  set U := ⋃ q ∈ T, dyadicCube q.1 q.2
  have hU : MeasurableSet U :=
    MeasurableSet.biUnion T.to_countable fun q _ => measurableSet_dyadicCube _ _
  by_cases hxS : x ∈ ⋃ q ∈ T, ball (fun i => ((q.2 i : ℝ) + 2⁻¹) * 2 ^ q.1) (3 * (2 ^ q.1 / 2))
  · exact .inl (.inl hxS)
  have hxT : ∀ q ∈ T, x ∉ ball (fun i => ((q.2 i : ℝ) + 2⁻¹) * 2 ^ q.1) (3 * (2 ^ q.1 / 2)) := by
    simpa only [mem_iUnion, not_exists] using hxS
  -- `gᵢ` is its part off the cubes plus its part on the cubes.
  have hle : ∀ i, maximalFunction volume (g i) x ≤ maximalFunction volume (Uᶜ.indicator (g i)) x +
      2 ^ Fintype.card ι * maximalFunction volume (cubeAverage T (g i)) x := fun i =>
    calc maximalFunction volume (g i) x
        = maximalFunction volume (Uᶜ.indicator (g i) + U.indicator (g i)) x := by
          rw [indicator_compl_add_self U (g i)]
      _ ≤ maximalFunction volume (Uᶜ.indicator (g i)) x +
            maximalFunction volume (U.indicator (g i)) x :=
          maximalFunction_add_le (by simpa only [eNorm_eq_self] using
            ((hg i).indicator hU.compl).aemeasurable) x
      _ ≤ _ := by
          gcongr
          exact maximalFunction_indicator_biUnion_le hxT
  rcases rpow_div_two_lt_or_of_rpow_lt_tsum_add hr
    (hx.trans_le (tsum_le_tsum fun i => by gcongr; exact hle i)) with h1 | h1
  · exact .inl (.inr h1)
  · exact .inr h1

/-- **The good part, in measure.** Restricted off the Calderón–Zygmund cubes of the pointwise
`ℓʳ` norm `F` at height `t`, the family has `ℓʳ` norm of its maximal functions above `t / 2` on a
set of measure at most `2 ^ r c(n, r) ∫⁻ F / t`. -/
private theorem mul_volume_lt_tsum_maximalFunction_indicator_compl_le [Nonempty ι]
    (hg : ∀ i, Measurable (g i)) (hr : 1 < r) (hF : ∫⁻ x, (∑' i, g i x ^ r) ^ r⁻¹ ≠ ∞)
    (ht : t ≠ 0) (ht' : t ≠ ∞) :
    t * volume {x | (t / 2) ^ r < ∑' i, maximalFunction volume
        ((⋃ q ∈ calderonZygmundCubes (fun x => (∑' i, g i x ^ r) ^ r⁻¹) t,
          dyadicCube q.1 q.2)ᶜ.indicator (g i)) x ^ r} ≤
      2 ^ r * maximalFunctionConst (Fintype.card ι) r * ∫⁻ x, (∑' i, g i x ^ r) ^ r⁻¹ := by
  have hU := measurableSet_biUnion_calderonZygmundCubes (fun x => (∑' i, g i x ^ r) ^ r⁻¹) t
  refine mul_measure_rpow_div_two_lt_le
    (Measurable.tsum fun i => (measurable_maximalFunction volume _).pow_const r).aemeasurable
    (by linarith) ht ht' ?_
  calc _ ≤ maximalFunctionConst (Fintype.card ι) r * ∫⁻ x, ∑' i,
        (⋃ q ∈ calderonZygmundCubes (fun x => (∑' i, g i x ^ r) ^ r⁻¹) t,
          dyadicCube q.1 q.2)ᶜ.indicator (g i) x ^ r := by
        simpa only [Module.finrank_fintype_fun_eq_card, eNorm_eq_self] using
          lintegral_tsum_maximalFunction_rpow_le (volume : Measure (ι → ℝ))
            (f := fun i => (⋃ q ∈ calderonZygmundCubes (fun x => (∑' i, g i x ^ r) ^ r⁻¹) t,
              dyadicCube q.1 q.2)ᶜ.indicator (g i)) (fun i => by
            simpa only [eNorm_eq_self] using ((hg i).indicator hU.compl).aemeasurable) hr
    _ ≤ maximalFunctionConst (Fintype.card ι) r * ∫⁻ x, t ^ (r - 1) * (∑' i, g i x ^ r) ^ r⁻¹ := by
        gcongr maximalFunctionConst (Fintype.card ι) r * ?_
        exact lintegral_mono_ae (ae_tsum_indicator_compl_rpow_le hg hr.le hF ht)
    _ = _ := by
        rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith) ht'), mul_assoc]

/-- **The bad part, in measure.** The cube averages of the family over the Calderón–Zygmund
cubes of the pointwise `ℓʳ` norm `F` at height `t` have `2ⁿ` times the `ℓʳ` norm of their maximal
functions above `t / 2` on a set of measure at most a multiple of `∫⁻ F / t`. -/
private theorem mul_volume_lt_tsum_maximalFunction_cubeAverage_le (hg : ∀ i, Measurable (g i))
    (hr : 1 < r) (ht : t ≠ 0) (ht' : t ≠ ∞) :
    t * volume {x | (t / 2) ^ r < ∑' i, (2 ^ Fintype.card ι * maximalFunction volume
        (cubeAverage (calderonZygmundCubes (fun x => (∑' i, g i x ^ r) ^ r⁻¹) t) (g i)) x) ^ r} ≤
      2 ^ r * ((2 ^ Fintype.card ι) ^ r * maximalFunctionConst (Fintype.card ι) r *
        (2 ^ Fintype.card ι) ^ (r - 1)) * ∫⁻ x, (∑' i, g i x ^ r) ^ r⁻¹ := by
  have hr0 : 0 < r := by linarith
  refine mul_measure_rpow_div_two_lt_le
    (Measurable.tsum fun i => ((measurable_maximalFunction volume _).const_mul _).pow_const
      r).aemeasurable hr0 ht ht' ?_
  simp only [ENNReal.mul_rpow_of_nonneg _ _ hr0.le, ENNReal.tsum_mul_left]
  rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hr0.le (by simp))]
  calc _ ≤ (2 ^ Fintype.card ι) ^ r * (maximalFunctionConst (Fintype.card ι) r * ∫⁻ x, ∑' i,
          cubeAverage (calderonZygmundCubes (fun x => (∑' i, g i x ^ r) ^ r⁻¹) t) (g i) x ^ r) := by
        gcongr
        simpa only [Module.finrank_fintype_fun_eq_card, eNorm_eq_self] using
          lintegral_tsum_maximalFunction_rpow_le (volume : Measure (ι → ℝ))
            (f := fun i => cubeAverage (calderonZygmundCubes (fun x => (∑' i, g i x ^ r) ^ r⁻¹) t)
              (g i)) (fun i => by
            simpa only [eNorm_eq_self] using (measurable_cubeAverage _ (g i)).aemeasurable) hr
    _ ≤ (2 ^ Fintype.card ι) ^ r * (maximalFunctionConst (Fintype.card ι) r *
          ((2 ^ Fintype.card ι * t) ^ (r - 1) * ∫⁻ x, (∑' i, g i x ^ r) ^ r⁻¹)) := by
        gcongr
        exact lintegral_tsum_cubeAverage_rpow_le hg hr.le
    _ = _ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by linarith)]
        ring

/-- The weak type `(1, 1)` bound for measurable `ℝ≥0∞`-valued families on `ι → ℝ`. -/
private theorem mul_volume_lt_tsum_maximalFunction_rpow_rpow_inv_le_of_measurable [Nonempty ι]
    (hg : ∀ i, Measurable (g i)) (hr : 1 < r) (t : ℝ≥0∞) :
    t * volume {x | t < (∑' i, maximalFunction volume (g i) x ^ r) ^ r⁻¹} ≤
      vectorMaximalFunctionWeakConst (Fintype.card ι) r * ∫⁻ x, (∑' i, g i x ^ r) ^ r⁻¹ := by
  set n := Fintype.card ι
  set F : (ι → ℝ) → ℝ≥0∞ := fun x => (∑' i, g i x ^ r) ^ r⁻¹
  rcases eq_or_ne t 0 with rfl | ht0
  · simp
  rcases eq_or_ne t ∞ with rfl | httop
  · simp
  rcases eq_or_ne (∫⁻ x, F x) ∞ with hFi | hFi
  · rw [hFi, ENNReal.mul_top (by rw [vectorMaximalFunctionWeakConst_def]; positivity)]
    exact le_top
  -- Split along the Calderón–Zygmund cubes of `F` at height `t`.
  have hsub := (setOf_rpow_lt_tsum_maximalFunction_subset hg hr.le (calderonZygmundCubes F t) t)
  replace hsub : {x | t < (∑' i, maximalFunction volume (g i) x ^ r) ^ r⁻¹} ⊆ _ := fun x hx =>
    hsub ((ENNReal.lt_rpow_inv_iff (by linarith)).1 hx)
  have hS : t * volume (⋃ q ∈ calderonZygmundCubes F t,
      ball (fun i => ((q.2 i : ℝ) + 2⁻¹) * 2 ^ q.1) (3 * (2 ^ q.1 / 2))) ≤ 3 ^ n * ∫⁻ x, F x := by
    calc _ ≤ t * volume (⋃ q ∈ calderonZygmundCubes F t,
          closedBall (fun i => ((q.2 i : ℝ) + 2⁻¹) * 2 ^ q.1) (3 * (2 ^ q.1 / 2))) := by
          gcongr
          exact ball_subset_closedBall
      _ ≤ 3 ^ n * ∫⁻ x, F x := by
          simpa only [ENNReal.ofReal_ofNat] using
            mul_volume_biUnion_closedBall_calderonZygmundCubes_le (g := F) (t := t) 3
  have hgood := mul_volume_lt_tsum_maximalFunction_indicator_compl_le hg hr hFi ht0 httop
  have hbad := mul_volume_lt_tsum_maximalFunction_cubeAverage_le hg hr ht0 httop
  have h2n : ((2 : ℝ≥0∞) ^ n) ^ r * (2 ^ n) ^ (r - 1) = (2 ^ n) ^ (2 * r - 1) := by
    rw [← ENNReal.rpow_add _ _ (by simp) (by simp)]
    ring_nf
  set I := ∫⁻ x, F x
  calc _ ≤ t * (volume (⋃ q ∈ calderonZygmundCubes F t,
          ball (fun i => ((q.2 i : ℝ) + 2⁻¹) * 2 ^ q.1) (3 * (2 ^ q.1 / 2))) +
        volume {x | (t / 2) ^ r < ∑' i, maximalFunction volume
          ((⋃ q ∈ calderonZygmundCubes F t, dyadicCube q.1 q.2)ᶜ.indicator (g i)) x ^ r} +
        volume {x | (t / 2) ^ r < ∑' i, (2 ^ n * maximalFunction volume
          (cubeAverage (calderonZygmundCubes F t) (g i)) x) ^ r}) := by
        gcongr
        refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
        exact add_le_add (measure_union_le _ _) le_rfl
    _ ≤ 3 ^ n * I + 2 ^ r * maximalFunctionConst n r * I +
          2 ^ r * ((2 ^ n) ^ r * maximalFunctionConst n r * (2 ^ n) ^ (r - 1)) * I := by
        rw [mul_add, mul_add]
        exact add_le_add (add_le_add hS hgood) hbad
    _ = _ := by
        rw [vectorMaximalFunctionWeakConst_def, ← h2n]
        ring

omit [Countable κ] in
/-- **Splitting at a height.** Restricting the family to a measurable set `A` and to its
complement splits the superlevel set of the `ℓʳ` norm of the maximal functions at `s` into two
superlevel sets at `s / 2`. -/
private theorem setOf_lt_tsum_maximalFunction_rpow_rpow_inv_subset (hg : ∀ i, Measurable (g i))
    (hr : 1 < r) {A : Set (ι → ℝ)} (hA : MeasurableSet A) (s : ℝ≥0∞) :
    {x | s < (∑' i, maximalFunction volume (g i) x ^ r) ^ r⁻¹} ⊆
      {x | s / 2 < (∑' i, maximalFunction volume (A.indicator (g i)) x ^ r) ^ r⁻¹} ∪
        {x | (s / 2) ^ r < ∑' i, maximalFunction volume (Aᶜ.indicator (g i)) x ^ r} := by
  have hr0 : 0 < r := by linarith
  intro x hx
  simp only [mem_ofPred_eq, ENNReal.lt_rpow_inv_iff hr0] at hx
  have hlt : s ^ r < ∑' i, (maximalFunction volume (A.indicator (g i)) x +
      maximalFunction volume (Aᶜ.indicator (g i)) x) ^ r := by
    refine hx.trans_le (tsum_le_tsum fun i => ?_)
    gcongr
    calc maximalFunction volume (g i) x
        = maximalFunction volume (A.indicator (g i) + Aᶜ.indicator (g i)) x := by
          rw [indicator_self_add_compl A (g i)]
      _ ≤ _ := maximalFunction_add_le (by simpa only [eNorm_eq_self] using
          ((hg i).indicator hA).aemeasurable) x
  rcases rpow_div_two_lt_or_of_rpow_lt_tsum_add hr.le hlt with h1 | h1
  · exact .inl (by rwa [mem_ofPred_eq, ENNReal.lt_rpow_inv_iff hr0])
  · exact .inr h1

/-- **The distributional estimate behind the interpolation.** Splitting the family according to
whether its pointwise `ℓʳ` norm `F` exceeds `s`, the weak type `(1, 1)` bound controls the part
above `s` and the diagonal `Lʳ(ℓʳ)` bound the part below. -/
private theorem volume_lt_tsum_maximalFunction_rpow_rpow_inv_le [Nonempty ι]
    (hg : ∀ i, Measurable (g i)) (hr : 1 < r) {s : ℝ≥0∞} (hs : s ≠ 0) (hs' : s ≠ ∞) :
    volume {x | s < (∑' i, maximalFunction volume (g i) x ^ r) ^ r⁻¹} ≤
      2 * vectorMaximalFunctionWeakConst (Fintype.card ι) r * s⁻¹ *
          (∫⁻ x in {x | s < (∑' i, g i x ^ r) ^ r⁻¹}, (∑' i, g i x ^ r) ^ r⁻¹) +
        2 ^ r * maximalFunctionConst (Fintype.card ι) r * (s ^ r)⁻¹ *
          ∫⁻ x in {x | (∑' i, g i x ^ r) ^ r⁻¹ ≤ s}, ((∑' i, g i x ^ r) ^ r⁻¹) ^ r := by
  have hr0 : 0 < r := by linarith
  set F : (ι → ℝ) → ℝ≥0∞ := fun x => (∑' i, g i x ^ r) ^ r⁻¹
  have hF : Measurable F := (Measurable.tsum fun i => (hg i).pow_const r).pow_const _
  set A := {x | s < F x}
  have hA : MeasurableSet A := measurableSet_lt measurable_const hF
  refine (measure_mono (setOf_lt_tsum_maximalFunction_rpow_rpow_inv_subset hg hr hA s)).trans
    ((measure_union_le _ _).trans (add_le_add ?_ ?_))
  · -- Above `s`: the weak type `(1, 1)` bound at the height `s / 2`.
    have hFA : ∀ x, (∑' i, A.indicator (g i) x ^ r) ^ r⁻¹ = A.indicator F x := fun x => by
      by_cases hx : x ∈ A
      · simp only [indicator_of_mem hx, F]
      · simp only [indicator_of_notMem hx, ENNReal.zero_rpow_of_pos hr0, tsum_zero,
          ENNReal.zero_rpow_of_pos (inv_pos.2 hr0)]
    have hw := mul_volume_lt_tsum_maximalFunction_rpow_rpow_inv_le_of_measurable
      (fun i => (hg i).indicator hA) hr (s / 2)
    simp only [hFA, lintegral_indicator hA] at hw
    rw [mul_comm, ← ENNReal.le_div_iff_mul_le (.inl (ENNReal.div_pos hs ENNReal.ofNat_ne_top).ne')
      (.inl (ENNReal.div_ne_top hs' two_ne_zero))] at hw
    refine hw.trans (le_of_eq ?_)
    rw [div_eq_mul_inv, ENNReal.inv_div (a := s) (b := 2) (.inl ENNReal.ofNat_ne_top)
      (.inl two_ne_zero), div_eq_mul_inv]
    ring
  · -- Below `s`: Chebyshev's inequality and the diagonal bound in `Lʳ(ℓʳ)`.
    have hFAc : ∀ x, ∑' i, Aᶜ.indicator (g i) x ^ r = Aᶜ.indicator (fun x => F x ^ r) x :=
      fun x => by
        by_cases hx : x ∈ Aᶜ
        · simp only [indicator_of_mem hx, F, ENNReal.rpow_inv_rpow hr0.ne']
        · simp only [indicator_of_notMem hx, ENNReal.zero_rpow_of_pos hr0, tsum_zero]
    have hdiag := lintegral_tsum_maximalFunction_rpow_le (volume : Measure (ι → ℝ))
      (f := fun i => Aᶜ.indicator (g i))
      (fun i => by simpa only [eNorm_eq_self] using ((hg i).indicator hA.compl).aemeasurable) hr
    simp only [Module.finrank_fintype_fun_eq_card, eNorm_eq_self, hFAc,
      lintegral_indicator hA.compl] at hdiag
    have hAc : Aᶜ = {x | F x ≤ s} := by ext x; simp [A]
    rw [← hAc]
    refine (measure_rpow_div_two_lt_le
      (Measurable.tsum fun i => (measurable_maximalFunction volume _).pow_const r).aemeasurable
      hr0 hs hs').trans ?_
    calc _ ≤ 2 ^ r * (s ^ r)⁻¹ *
            (maximalFunctionConst (Fintype.card ι) r * ∫⁻ x in Aᶜ, F x ^ r) := by gcongr
      _ = _ := by ring

/-- The strong type `(p, p)` bound below the diagonal for measurable `ℝ≥0∞`-valued families on
`ι → ℝ`, by Marcinkiewicz interpolation of `volume_lt_tsum_maximalFunction_rpow_rpow_inv_le`. -/
private theorem lintegral_rpow_tsum_maximalFunction_rpow_le_of_lt_exponent_of_measurable
    [Nonempty ι] (hg : ∀ i, Measurable (g i)) {p : ℝ} (hp : 1 < p) (hpr : p < r) :
    ∫⁻ x, (∑' i, maximalFunction volume (g i) x ^ r) ^ (p / r) ≤
      (ENNReal.ofReal (p / (p - 1)) * (2 * vectorMaximalFunctionWeakConst (Fintype.card ι) r) +
        ENNReal.ofReal (p / (r - p)) * (2 ^ r * maximalFunctionConst (Fintype.card ι) r)) *
        ∫⁻ x, (∑' i, g i x ^ r) ^ (p / r) := by
  have hr : 1 < r := hp.trans hpr
  have hpow : ∀ a : ℝ≥0∞, (a ^ r⁻¹) ^ p = a ^ (p / r) := fun a => by
    rw [← ENNReal.rpow_mul, inv_mul_eq_div]
  have key := lintegral_rpow_le_of_meas_ofReal_lt_le (μ := volume) (ν := volume)
    (f := fun x => (∑' i, g i x ^ r) ^ r⁻¹)
    (u := fun x => (∑' i, maximalFunction volume (g i) x ^ r) ^ r⁻¹) (p₀ := 1) (p₁ := r) (c := 1)
    (A₀ := 2 * vectorMaximalFunctionWeakConst (Fintype.card ι) r)
    (A₁ := 2 ^ r * maximalFunctionConst (Fintype.card ι) r)
    ((Measurable.tsum fun i => (hg i).pow_const r).pow_const _).aemeasurable
    ((Measurable.tsum fun i => (measurable_maximalFunction volume _).pow_const r).pow_const
      _).aemeasurable one_pos hp hpr one_pos fun t ht => ?_
  · simpa only [Real.one_rpow, mul_one, hpow] using key
  have h := volume_lt_tsum_maximalFunction_rpow_rpow_inv_le hg hr
    (ENNReal.ofReal_pos.2 ht).ne' ENNReal.ofReal_ne_top
  simp only [one_mul, ENNReal.rpow_one]
  rwa [Real.rpow_neg_one, ENNReal.ofReal_inv_of_pos ht,
    Real.rpow_neg ht.le, ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos ht r),
    ← ENNReal.ofReal_rpow_of_pos ht]

end Cubes

/-! ### Transfer to a finite-dimensional real normed space -/

/-- Replacing each `‖fᵢ‖ₑ` by a measurable modification changes neither the maximal functions nor
the integrals of the pointwise `ℓʳ` norm. -/
private theorem exists_measurable_maximalFunction_eq [Countable κ] {X F : Type*}
    [PseudoMetricSpace X] [MeasurableSpace X] [ENorm F] (μ : Measure X) {f : κ → X → F}
    (hf : ∀ i, AEMeasurable (fun x => ‖f i x‖ₑ) μ) :
    ∃ g : κ → X → ℝ≥0∞, (∀ i, Measurable (g i)) ∧
      (∀ i, maximalFunction μ (f i) = maximalFunction μ (g i)) ∧
      ∀ᵐ x ∂μ, ∀ i, ‖f i x‖ₑ = g i x :=
  ⟨fun i => (hf i).mk _, fun i => (hf i).measurable_mk,
    fun i => funext fun x => maximalFunction_congr_ae (by
      filter_upwards [(hf i).ae_eq_mk] with y hy
      rw [hy, eNorm_eq_self]),
    ae_all_iff.2 fun i => (hf i).ae_eq_mk⟩

section Transfer

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [ENorm F] [Countable κ] [Nonempty ι] {r : ℝ}

/-- **Transport to `ι → ℝ`.** Let `Gᵢ = gᵢ ∘ e⁻¹` for measurable modifications `gᵢ` of `‖fᵢ‖ₑ`.
Then `e_* μ = c • volume` for some `c`, the pointwise `ℓʳ` norm of the maximal functions of the
`fᵢ` for `μ` at `x` is at most `(‖e‖ ‖e⁻¹‖)ⁿ` times that of the `Gᵢ` for `volume` at `e x`, and
integrals against `μ` of functions of the pointwise sum `∑' i, ‖fᵢ‖ₑ ^ r` are `c` times the
corresponding integrals of `∑' i, Gᵢ ^ r` against `volume`. -/
private theorem exists_map_eq_smul_volume_and_tsum_maximalFunction_rpow_rpow_inv_le
    (μ : Measure E) [μ.IsAddHaarMeasure] (e : E ≃L[ℝ] (ι → ℝ)) {f : κ → E → F}
    (hf : ∀ i, AEMeasurable (fun x => ‖f i x‖ₑ) μ) (hr : 0 < r) :
    ∃ (G : κ → (ι → ℝ) → ℝ≥0∞) (c : ℝ≥0∞), (∀ i, Measurable (G i)) ∧ μ.map e = c • volume ∧
      (∀ x, (∑' i, maximalFunction μ (f i) x ^ r) ^ r⁻¹ ≤
        ENNReal.ofReal ((‖(e : E →L[ℝ] (ι → ℝ))‖ * ‖(e.symm : (ι → ℝ) →L[ℝ] E)‖) ^
          Fintype.card ι) * (∑' i, maximalFunction volume (G i) (e x) ^ r) ^ r⁻¹) ∧
      ∀ φ : ℝ≥0∞ → ℝ≥0∞, Measurable φ →
        ∫⁻ x, φ (∑' i, ‖f i x‖ₑ ^ r) ∂μ = c * ∫⁻ z, φ (∑' i, G i z ^ r) := by
  obtain ⟨g, hg, hM, hae⟩ := exists_measurable_maximalFunction_eq μ hf
  have : Nontrivial E := e.toEquiv.nontrivial
  have : FiniteDimensional ℝ E := e.symm.toLinearEquiv.finiteDimensional
  have : (μ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  obtain ⟨c, hc, hc', hν⟩ : ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧ μ.map e = c • volume :=
    ⟨Measure.addHaarScalarFactor (μ.map e) volume, by simpa only [ne_eq, ENNReal.coe_eq_zero] using
      (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure (μ.map e) volume).ne',
      ENNReal.coe_ne_top, Measure.isAddLeftInvariant_eq_smul _ _⟩
  have hfin : finrank ℝ E = Fintype.card ι :=
    e.toLinearEquiv.finrank_eq.trans (Module.finrank_fintype_fun_eq_card ℝ)
  have hG : ∀ i, Measurable fun z => g i (e.symm z) :=
    fun i => (hg i).comp e.symm.continuous.measurable
  refine ⟨fun i z => g i (e.symm z), c, hG, hν, fun x => ?_, fun φ hφ => ?_⟩
  · -- The `ℓʳ` norm is monotone and positively homogeneous.
    have hhom : ∀ (K : ℝ≥0∞) {a b : κ → ℝ≥0∞}, (∀ i, a i ≤ K * b i) →
        (∑' i, a i ^ r) ^ r⁻¹ ≤ K * (∑' i, b i ^ r) ^ r⁻¹ := fun K a b h => by
      calc (∑' i, a i ^ r) ^ r⁻¹ ≤ (∑' i, (K * b i) ^ r) ^ r⁻¹ := by
            gcongr with i
            exact h i
        _ = K * (∑' i, b i ^ r) ^ r⁻¹ := by
            simp only [ENNReal.mul_rpow_of_nonneg _ _ hr.le, ENNReal.tsum_mul_left]
            rw [ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.2 hr.le), ENNReal.rpow_rpow_inv hr.ne']
    refine hhom _ fun i => ?_
    have h := maximalFunction_le_ofReal_mul_maximalFunction_map μ e e.norm_pos e.norm_symm_pos
      (fun y => (e : E →L[ℝ] (ι → ℝ)).le_opNorm y)
      (fun z => (e.symm : (ι → ℝ) →L[ℝ] E).le_opNorm z) (g i) x
    rwa [hfin, hν, maximalFunction_smul_measure hc hc', ← hM i] at h
  · rw [← smul_eq_mul, ← lintegral_smul_measure, ← hν,
      lintegral_map (f := fun z => φ (∑' i, g i (e.symm z) ^ r))
        (hφ.comp (Measurable.tsum fun i => (hG i).pow_const r)) e.continuous.measurable]
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with x hx
    simp only [hx, e.symm_apply_apply]

/-- **The vector-valued maximal inequality of Fefferman and Stein, weak type `(1, 1)`.** Let `μ` be
an additive Haar measure on a real normed space `E` of positive dimension `n`, let
`e : E ≃L[ℝ] (ι → ℝ)` be a continuous linear equivalence, and let `1 < r`. For every countable
family `fᵢ`, the `ℓʳ`-valued maximal function satisfies

`t μ {(∑' i, (M fᵢ) ^ r) ^ (1 / r) > t} ≤ C ∫⁻ (∑' i, ‖fᵢ‖ₑ ^ r) ^ (1 / r) ∂μ`

with `C = (‖e‖ ‖e⁻¹‖)ⁿ A`, where `A = 3ⁿ + 2 ^ r (1 + (2ⁿ) ^ (2 r - 1)) c(n, r)` is
`TauCeti.vectorMaximalFunctionWeakConst n r` and `c(n, r)` is the constant
`TauCeti.maximalFunctionConst n r` of the scalar maximal inequality. The constant depends on `E`
only through `‖e‖ ‖e⁻¹‖`; on `ι → ℝ`, with the identity, it depends only on `n` and `r`.

The proof is on `ι → ℝ` with the sup norm, where balls are cubes: the Calderón–Zygmund cubes of
the pointwise `ℓʳ` norm split the family into a part bounded by `t`, handled by the `Lʳ(ℓʳ)`
bound `TauCeti.lintegral_tsum_maximalFunction_rpow_le`, and a part carried by the cubes, whose
maximal functions away from the threefold cubes are controlled by those of the cube averages.
`e` transports the bound to `E` (`TauCeti.maximalFunction_le_ofReal_mul_maximalFunction_map`). -/
theorem mul_measure_lt_tsum_maximalFunction_rpow_rpow_inv_le (μ : Measure E)
    [μ.IsAddHaarMeasure] (e : E ≃L[ℝ] (ι → ℝ)) {f : κ → E → F}
    (hf : ∀ i, AEMeasurable (fun x => ‖f i x‖ₑ) μ) (hr : 1 < r) (t : ℝ≥0∞) :
    t * μ {x | t < (∑' i, maximalFunction μ (f i) x ^ r) ^ r⁻¹} ≤
      ENNReal.ofReal ((‖(e : E →L[ℝ] (ι → ℝ))‖ * ‖(e.symm : (ι → ℝ) →L[ℝ] E)‖) ^
          Fintype.card ι) * vectorMaximalFunctionWeakConst (Fintype.card ι) r *
        ∫⁻ x, (∑' i, ‖f i x‖ₑ ^ r) ^ r⁻¹ ∂μ := by
  have hr0 : 0 < r := by linarith
  obtain ⟨G, c, hG, hν, hM, hI⟩ :=
    exists_map_eq_smul_volume_and_tsum_maximalFunction_rpow_rpow_inv_le μ e hf hr0
  have : Nontrivial E := e.toEquiv.nontrivial
  set K := ENNReal.ofReal ((‖(e : E →L[ℝ] (ι → ℝ))‖ * ‖(e.symm : (ι → ℝ) →L[ℝ] E)‖) ^
    Fintype.card ι)
  have hK : K ≠ 0 := (ENNReal.ofReal_pos.2 (pow_pos (mul_pos e.norm_pos e.norm_symm_pos) _)).ne'
  have hK' : K ≠ ∞ := ENNReal.ofReal_ne_top
  -- The `ℓʳ` norm of the maximal functions of the transported family.
  set u : (ι → ℝ) → ℝ≥0∞ := fun z => (∑' i, maximalFunction volume (G i) z ^ r) ^ r⁻¹
  have hu : Measurable u :=
    (Measurable.tsum fun i => (measurable_maximalFunction volume _).pow_const r).pow_const _
  have hsub : {x | t < (∑' i, maximalFunction μ (f i) x ^ r) ^ r⁻¹} ⊆ e ⁻¹' {z | t / K < u z} :=
    fun x hx => by
      rw [mem_ofPred_eq] at hx
      rw [mem_preimage, mem_ofPred_eq, ENNReal.div_lt_iff (.inl hK) (.inl hK'), mul_comm]
      exact hx.trans_le (hM x)
  have hI' := hI (· ^ r⁻¹) (measurable_id.pow_const _)
  calc t * μ {x | t < (∑' i, maximalFunction μ (f i) x ^ r) ^ r⁻¹}
      ≤ K * (t / K) * (c * volume {z | t / K < u z}) := by
        rw [ENNReal.mul_div_cancel hK hK']
        gcongr
        refine (measure_mono hsub).trans (le_of_eq ?_)
        rw [← Measure.map_apply e.continuous.measurable (measurableSet_lt measurable_const hu), hν,
          smul_apply, smul_eq_mul]
    _ = K * c * ((t / K) * volume {z | t / K < u z}) := by ring
    _ ≤ K * c * (vectorMaximalFunctionWeakConst (Fintype.card ι) r *
          ∫⁻ z, (∑' i, G i z ^ r) ^ r⁻¹) := by
        gcongr K * c * ?_
        exact mul_volume_lt_tsum_maximalFunction_rpow_rpow_inv_le_of_measurable hG hr _
    _ = _ := by
        rw [hI']
        ring

/-- **The vector-valued maximal inequality of Fefferman and Stein below the exponent of the sum.**
Let `μ` be an additive Haar measure on a real normed space `E` of positive dimension `n`, let
`e : E ≃L[ℝ] (ι → ℝ)` be a continuous linear equivalence, and let `1 < p < r`. For every countable
family `fᵢ`, the `ℓʳ`-valued maximal function is bounded on `Lᵖ(ℓʳ)`:

`∫⁻ (∑' i, (M fᵢ) ^ r) ^ (p / r) ∂μ ≤ C ∫⁻ (∑' i, ‖fᵢ‖ₑ ^ r) ^ (p / r) ∂μ`,

with `C = (‖e‖ ‖e⁻¹‖) ^ (n p) (p / (p - 1) · 2 A + p / (r - p) · 2 ^ r c(n, r))`, where `A` is the
constant `TauCeti.vectorMaximalFunctionWeakConst n r` of the weak type `(1, 1)` bound
`TauCeti.mul_measure_lt_tsum_maximalFunction_rpow_rpow_inv_le` and `c(n, r)` is the constant
`TauCeti.maximalFunctionConst n r` of the scalar maximal inequality. Together with
`TauCeti.lintegral_tsum_maximalFunction_rpow_le` for `p = r` and
`TauCeti.lintegral_rpow_tsum_maximalFunction_rpow_le_of_exponent_lt` for `r < p`, this covers every
`1 < p, r < ∞`; for `r = 2` it is the square-function form
`‖(∑' i, (M fᵢ) ^ 2) ^ (1 / 2)‖_p ≤ C' ‖(∑' i, ‖fᵢ‖ ^ 2) ^ (1 / 2)‖_p` for `1 < p < 2`. The suffix
`_of_lt_exponent` records that `p` lies below the exponent `r` of the sum.

The proof interpolates, by Marcinkiewicz's theorem
(`TauCeti.lintegral_rpow_le_of_meas_ofReal_lt_le`), between the weak type `(1, 1)` bound and the
diagonal `Lʳ(ℓʳ)` bound. -/
theorem lintegral_rpow_tsum_maximalFunction_rpow_le_of_lt_exponent (μ : Measure E)
    [μ.IsAddHaarMeasure] (e : E ≃L[ℝ] (ι → ℝ)) {f : κ → E → F}
    (hf : ∀ i, AEMeasurable (fun x => ‖f i x‖ₑ) μ) {p : ℝ} (hp : 1 < p) (hpr : p < r) :
    ∫⁻ x, (∑' i, maximalFunction μ (f i) x ^ r) ^ (p / r) ∂μ ≤
      ENNReal.ofReal ((‖(e : E →L[ℝ] (ι → ℝ))‖ * ‖(e.symm : (ι → ℝ) →L[ℝ] E)‖) ^
          Fintype.card ι) ^ p *
        (ENNReal.ofReal (p / (p - 1)) * (2 * vectorMaximalFunctionWeakConst (Fintype.card ι) r) +
          ENNReal.ofReal (p / (r - p)) * (2 ^ r * maximalFunctionConst (Fintype.card ι) r)) *
        ∫⁻ x, (∑' i, ‖f i x‖ₑ ^ r) ^ (p / r) ∂μ := by
  have hr0 : 0 < r := by linarith
  have hp0 : 0 < p := by linarith
  obtain ⟨G, c, hG, hν, hM, hI⟩ :=
    exists_map_eq_smul_volume_and_tsum_maximalFunction_rpow_rpow_inv_le μ e hf hr0
  set K := ENNReal.ofReal ((‖(e : E →L[ℝ] (ι → ℝ))‖ * ‖(e.symm : (ι → ℝ) →L[ℝ] E)‖) ^
    Fintype.card ι)
  have hpow : ∀ a : ℝ≥0∞, (a ^ r⁻¹) ^ p = a ^ (p / r) := fun a => by
    rw [← ENNReal.rpow_mul, inv_mul_eq_div]
  have hu : Measurable fun z => (∑' i, maximalFunction volume (G i) z ^ r) ^ (p / r) :=
    (Measurable.tsum fun i => (measurable_maximalFunction volume _).pow_const r).pow_const _
  have hI' := hI (· ^ (p / r)) (measurable_id.pow_const _)
  calc ∫⁻ x, (∑' i, maximalFunction μ (f i) x ^ r) ^ (p / r) ∂μ
      ≤ ∫⁻ x, K ^ p * (∑' i, maximalFunction volume (G i) (e x) ^ r) ^ (p / r) ∂μ := by
        refine lintegral_mono fun x => ?_
        rw [← hpow, ← hpow, ← ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
        gcongr
        exact hM x
    _ = K ^ p * (c * ∫⁻ z, (∑' i, maximalFunction volume (G i) z ^ r) ^ (p / r)) := by
        rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp0.le ENNReal.ofReal_ne_top),
          ← lintegral_map hu e.continuous.measurable, hν, lintegral_smul_measure, smul_eq_mul]
    _ ≤ K ^ p * (c * (_ * ∫⁻ z, (∑' i, G i z ^ r) ^ (p / r))) := by
        gcongr
        exact lintegral_rpow_tsum_maximalFunction_rpow_le_of_lt_exponent_of_measurable hG hp hpr
    _ = _ := by
        rw [hI']
        ring

end Transfer

end TauCeti
