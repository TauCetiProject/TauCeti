/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.MaximalFunction
import TauCeti.MeasureTheory.Integral.DyadicMaximalFunction
import TauCeti.MeasureTheory.Integral.Marcinkiewicz.General
import TauCeti.MeasureTheory.Integral.MinkowskiIntegral

/-!
# The vector-valued maximal inequality in the full range

For `1 < r < ∞` and a countable family `f = (fᵢ)` of functions on `ℝⁿ`, the
**vector-valued maximal inequality of Fefferman and Stein** says that the `ℓʳ`-valued maximal
function is bounded on `Lᵖ(ℓʳ)` for every `1 < p < ∞`:

`∫⁻ (∑' i, (M fᵢ) ^ r) ^ (p / r) ≤ C(n, r, p) * ∫⁻ (∑' i, ‖fᵢ‖ₑ ^ r) ^ (p / r)`.

The range `r ≤ p` holds on any finite-dimensional normed space: the diagonal case `p = r` is
`TauCeti.lintegral_tsum_maximalFunction_rpow_le`, the sum of the scalar inequalities, and the case
`r < p` is `TauCeti.lintegral_rpow_tsum_maximalFunction_rpow_le`, proved by duality from the
weighted maximal inequality. This file proves the range `1 < p < r` on `ℝⁿ = ι → ℝ` with the sup
norm, and assembles the whole range. With `r = 2` it bounds the maximal functions of the pieces
of a square function in every `Lᵖ`, `1 < p < ∞`, which is the form Littlewood–Paley theory uses.

## The proof

The range below `r` is Marcinkiewicz interpolation between the diagonal bound in `Lʳ(ℓʳ)` and a
**weak type `(1, 1)` bound** for the `ℓʳ`-valued maximal function,

`t * |{(∑' i, (M fᵢ) ^ r) ^ (1 / r) > t}| ≤ A(n, r) * ∫⁻ (∑' i, ‖fᵢ‖ₑ ^ r) ^ (1 / r)`.

That bound comes from a Calderón–Zygmund decomposition of the scalar function
`G = (∑' i, ‖fᵢ‖ₑ ^ r) ^ (1 / r)` at height `t`. Let `Ω` be the union of the Calderón–Zygmund
cubes `Q`, so that `t |Ω| ≤ ∫⁻ G` and `G ≤ t` almost everywhere off `Ω`, and let `Ω*` be the union
of the concentric cubes `3Q`, of measure at most `3ⁿ |Ω|`. Split each `fᵢ` into its part off `Ω`
and its part on `Ω`.

* The part off `Ω` has `ℓʳ` norm at most `t`, so its `Lʳ(ℓʳ)` norm to the power `r` is at most
  `t ^ (r - 1) ∫⁻ G`, and the diagonal bound controls its maximal functions.
* At a point `x` off `Ω*`, a ball about `x` that meets a cube `Q` is larger than `Q`, and `Q` lies
  in the ball of twice the radius. So the maximal function of the part on `Ω` is at most `2ⁿ`
  times the maximal function of `hᵢ`, the function equal to the average of `‖fᵢ‖ₑ` over `Q` on
  each cube `Q`. By Minkowski's inequality (`TauCeti.tsum_rpow_lintegral_le`) the `ℓʳ` norm of
  `(hᵢ)` on `Q` is at most the average of `G` over `Q`, which is at most `2ⁿ t`; so the diagonal
  bound controls these maximal functions too.

Chebyshev's inequality on the complement of `Ω*` then gives the weak-type bound. No cancellation
is used: the maximal operator is positive, so the bad part needs no mean zero.

## Main declarations

* `TauCeti.mul_volume_lt_tsum_maximalFunction_rpow_rpow_inv_le`: the weak type `(1, 1)` bound for
  the `ℓʳ`-valued maximal function.
* `TauCeti.lintegral_rpow_tsum_maximalFunction_rpow_le_of_lt`: the vector-valued maximal
  inequality for `1 < p < r`.
* `TauCeti.exists_lintegral_rpow_tsum_maximalFunction_rpow_le`: the vector-valued maximal
  inequality for every `1 < p < ∞`, with a constant depending only on `n`, `r` and `p`.

## References

* C. Fefferman, E. M. Stein, *Some maximal inequalities*, Amer. J. Math. **93** (1971), 107–115.
* L. Grafakos, *Classical Fourier Analysis*, Section 5.6, Theorem 5.6.6.
-/

public section

namespace TauCeti

open MeasureTheory Metric Set
open scoped ENNReal

variable {ι κ : Type*} [Fintype ι] [Countable κ]

section CubeAverage

variable {C : Set (ℤ × (ι → ℤ))} {a : (ι → ℝ) → ℝ≥0∞} {q : ℤ × (ι → ℤ)} {x y : ι → ℝ}

/-- The function equal to the average of `a` over `Q` on each dyadic cube `Q` of the family `C`,
and to `0` off them. -/
private noncomputable def cubeAverage (C : Set (ℤ × (ι → ℤ))) (a : (ι → ℝ) → ℝ≥0∞)
    (y : ι → ℝ) : ℝ≥0∞ :=
  ∑' q : C, (dyadicCube q.1.1 q.1.2).indicator
    (fun _ => ⨍⁻ z in dyadicCube q.1.1 q.1.2, a z ∂volume) y

private theorem cubeAverage_of_mem (hC : C.PairwiseDisjoint fun q => dyadicCube q.1 q.2)
    (hq : q ∈ C) (hy : y ∈ dyadicCube q.1 q.2) :
    cubeAverage C a y = ⨍⁻ z in dyadicCube q.1 q.2, a z ∂volume := by
  rw [cubeAverage, tsum_eq_single ⟨q, hq⟩ fun q' hne => indicator_of_notMem (fun hy' =>
    Set.disjoint_left.1 (hC q'.2 hq fun h => hne (Subtype.ext h)) hy' hy) _]
  exact indicator_of_mem hy _

private theorem cubeAverage_of_forall_notMem (hy : ∀ q ∈ C, y ∉ dyadicCube q.1 q.2) :
    cubeAverage C a y = 0 :=
  tsum_eq_zero_iff.2 fun q => indicator_of_notMem (hy q q.2) _

private theorem measurable_cubeAverage : Measurable (cubeAverage C a) :=
  .tsum fun _ => measurable_const.indicator (measurableSet_dyadicCube _ _)

/-- On a cube of the family, `cubeAverage C a` has the same integral as `a`. -/
private theorem setLIntegral_cubeAverage (hC : C.PairwiseDisjoint fun q => dyadicCube q.1 q.2)
    (hq : q ∈ C) :
    ∫⁻ y in dyadicCube q.1 q.2, cubeAverage C a y = ∫⁻ y in dyadicCube q.1 q.2, a y := by
  rw [setLIntegral_congr_fun (measurableSet_dyadicCube _ _) fun y hy =>
      cubeAverage_of_mem hC hq hy, setLIntegral_const, mul_comm,
    measure_mul_setLAverage _ (volume_dyadicCube_ne_top _ _)]

private theorem lintegral_cubeAverage_le (hC : C.PairwiseDisjoint fun q => dyadicCube q.1 q.2) :
    ∫⁻ y, cubeAverage C a y ≤ ∫⁻ y, a y := by
  calc ∫⁻ y, cubeAverage C a y
      = ∫⁻ y in ⋃ q ∈ C, dyadicCube q.1 q.2, cubeAverage C a y := by
        refine (setLIntegral_eq_of_support_subset fun y hy => ?_).symm
        by_contra hnot
        simp only [mem_iUnion, not_exists] at hnot
        exact hy (cubeAverage_of_forall_notMem fun q hq => hnot q hq)
    _ = ∑' q : C, ∫⁻ y in dyadicCube q.1.1 q.1.2, a y := by
        rw [lintegral_biUnion C.to_countable (fun q _ => measurableSet_dyadicCube _ _) hC]
        exact tsum_congr fun q => setLIntegral_cubeAverage hC q.2
    _ = ∫⁻ y in ⋃ q ∈ C, dyadicCube q.1 q.2, a y :=
        (lintegral_biUnion C.to_countable (fun q _ => measurableSet_dyadicCube _ _) hC _).symm
    _ ≤ ∫⁻ y, a y := setLIntegral_le_lintegral _ _

/-- The centre of the dyadic cube `q`. -/
private noncomputable def cubeCentre (q : ℤ × (ι → ℤ)) : ι → ℝ :=
  fun i => ((q.2 i : ℝ) + 2⁻¹) * 2 ^ q.1

/-- A ball about a point outside the concentric cube `3Q` that meets `Q` is larger than `Q`, and
`Q` lies in the ball of twice the radius. -/
private theorem dyadicCube_subset_ball_two_mul {ρ : ℝ}
    (hx : x ∉ ball (cubeCentre q) (3 * 2 ^ q.1 / 2)) (hy : y ∈ ball x ρ)
    (hyQ : y ∈ dyadicCube q.1 q.2) : dyadicCube q.1 q.2 ⊆ ball x (2 * ρ) := by
  have hQ := dyadicCube_subset_closedBall (ι := ι) q.1 q.2
  have hyc : dist y (cubeCentre q) ≤ 2 ^ q.1 / 2 := mem_closedBall.1 (hQ hyQ)
  have hxc : 3 * 2 ^ q.1 / 2 ≤ dist x (cubeCentre q) := le_of_not_gt fun h => hx (mem_ball.2 h)
  have hxy : dist x y < ρ := mem_ball'.1 hy
  intro z hz
  have hzc : dist z (cubeCentre q) ≤ 2 ^ q.1 / 2 := mem_closedBall.1 (hQ hz)
  have h1 := dist_triangle x y (cubeCentre q)
  have h2 := dist_triangle z (cubeCentre q) x
  rw [dist_comm (cubeCentre q) x] at h2
  exact mem_ball.2 (by linarith)

/-- Off the concentric triples of the cubes of a pairwise disjoint family `C`, the maximal function
of the restriction of `a` to the cubes is at most `2ⁿ` times the maximal function of
`cubeAverage C a`. -/
private theorem maximalFunction_indicator_le
    (hC : C.PairwiseDisjoint fun q => dyadicCube q.1 q.2)
    (hx : ∀ q ∈ C, x ∉ ball (cubeCentre q) (3 * 2 ^ q.1 / 2)) :
    maximalFunction volume ((⋃ q ∈ C, dyadicCube q.1 q.2).indicator a) x ≤
      2 ^ Fintype.card ι * maximalFunction volume (cubeAverage C a) x := by
  have hΩ : MeasurableSet (⋃ q ∈ C, dyadicCube q.1 q.2) :=
    .biUnion C.to_countable fun q _ => measurableSet_dyadicCube _ _
  refine maximalFunction_le fun ρ hρ => ?_
  -- Each cube meeting `B(x, ρ)` lies in `B(x, 2ρ)`, where `cubeAverage C a` has the same integral.
  have hint : ∫⁻ y in ball x ρ, (⋃ q ∈ C, dyadicCube q.1 q.2).indicator a y ≤
      ∫⁻ y in ball x (2 * ρ), cubeAverage C a y := by
    rw [setLIntegral_indicator hΩ, iUnion₂_inter,
      lintegral_biUnion C.to_countable (fun q _ => (measurableSet_dyadicCube _ _).inter
        measurableSet_ball) (hC.mono fun q => inter_subset_left)]
    calc ∑' q : C, ∫⁻ y in dyadicCube q.1.1 q.1.2 ∩ ball x ρ, a y
        ≤ ∑' q : C, ∫⁻ y in dyadicCube q.1.1 q.1.2 ∩ ball x (2 * ρ), cubeAverage C a y := by
          refine tsum_le_tsum fun q => ?_
          rcases (dyadicCube q.1.1 q.1.2 ∩ ball x ρ).eq_empty_or_nonempty with h | ⟨y, hyQ, hyB⟩
          · simp [h]
          rw [inter_eq_left.2 (dyadicCube_subset_ball_two_mul (hx q q.2) hyB hyQ),
            setLIntegral_cubeAverage hC q.2]
          exact lintegral_mono_set inter_subset_left
      _ = ∫⁻ y in (⋃ q ∈ C, dyadicCube q.1 q.2) ∩ ball x (2 * ρ), cubeAverage C a y := by
          rw [iUnion₂_inter, lintegral_biUnion C.to_countable (fun q _ =>
            (measurableSet_dyadicCube _ _).inter measurableSet_ball)
            (hC.mono fun q => inter_subset_left)]
      _ ≤ ∫⁻ y in ball x (2 * ρ), cubeAverage C a y := lintegral_mono_set inter_subset_right
  have hvol : volume (ball x (2 * ρ)) = 2 ^ Fintype.card ι * volume (ball x ρ) := by
    rw [Real.volume_pi_ball _ (by positivity), Real.volume_pi_ball _ hρ, mul_pow,
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
  have h2 : (2 : ℝ≥0∞) ^ Fintype.card ι ≠ 0 := pow_ne_zero _ two_ne_zero
  have h2' : (2 : ℝ≥0∞) ^ Fintype.card ι ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  simp only [enorm_eq_self]
  calc ⨍⁻ y in ball x ρ, (⋃ q ∈ C, dyadicCube q.1 q.2).indicator a y ∂volume
      ≤ (∫⁻ y in ball x (2 * ρ), cubeAverage C a y) / volume (ball x ρ) := by
        rw [setLAverage_eq]
        gcongr
    _ = 2 ^ Fintype.card ι * ⨍⁻ y in ball x (2 * ρ), cubeAverage C a y ∂volume := by
        rw [setLAverage_eq, hvol, ← mul_div_assoc, ENNReal.mul_div_mul_left _ _ h2 h2']
    _ ≤ 2 ^ Fintype.card ι * maximalFunction volume (cubeAverage C a) x := by
        gcongr
        simpa only [enorm_eq_self] using
          setLAverage_le_maximalFunction volume (cubeAverage C a) x (by positivity : 0 < 2 * ρ)

end CubeAverage

section WeakType

variable {g : κ → (ι → ℝ) → ℝ≥0∞} {G : (ι → ℝ) → ℝ≥0∞} {r : ℝ} {t : ℝ≥0∞}

/-- The diagonal vector-valued maximal inequality on `ℝⁿ`, for nonnegative functions. -/
private theorem lintegral_tsum_maximalFunction_rpow_le_of_measurable (hg : ∀ i, Measurable (g i))
    (hr : 1 < r) :
    ∫⁻ x, ∑' i, maximalFunction volume (g i) x ^ r ≤
      ENNReal.ofReal (2 * r * 2 ^ (r - 1) / (r - 1)) * 4 ^ Fintype.card ι *
        ∫⁻ x, ∑' i, g i x ^ r := by
  simpa only [enorm_eq_self, Module.finrank_fintype_fun_eq_card] using
    lintegral_tsum_maximalFunction_rpow_le volume (f := g)
      (fun i => by simpa only [enorm_eq_self] using (hg i).aemeasurable) hr

/-- The part of the family off the Calderón–Zygmund cubes of its `ℓʳ` norm `G` at height `t`:
there `G ≤ t`, so its `Lʳ(ℓʳ)` norm to the power `r` is at most `t ^ (r - 1) ∫⁻ G`. -/
private theorem lintegral_tsum_maximalFunction_indicator_compl_le [Nonempty ι]
    (hg : ∀ i, Measurable (g i)) (hr : 1 < r) (hGdef : ∀ x, G x = (∑' i, g i x ^ r) ^ r⁻¹)
    (hGm : Measurable G) (hG : ∫⁻ x, G x ≠ ∞) (ht : t ≠ 0) :
    ∫⁻ x, ∑' i, maximalFunction volume
        ((⋃ q ∈ calderonZygmundCubes G t, dyadicCube q.1 q.2)ᶜ.indicator (g i)) x ^ r ≤
      ENNReal.ofReal (2 * r * 2 ^ (r - 1) / (r - 1)) * 4 ^ Fintype.card ι *
        (t ^ (r - 1) * ∫⁻ x, G x) := by
  set Ω := ⋃ q ∈ calderonZygmundCubes G t, dyadicCube q.1 q.2
  have hΩ : MeasurableSet Ω := measurableSet_biUnion_calderonZygmundCubes G t
  have hr0 : 0 < r := zero_lt_one.trans hr
  refine (lintegral_tsum_maximalFunction_rpow_le_of_measurable
    (fun i => (hg i).indicator hΩ.compl) hr).trans ?_
  rw [← lintegral_const_mul _ hGm]
  gcongr _ * ?_
  refine lintegral_mono_ae ?_
  filter_upwards [ae_le_of_forall_notMem_calderonZygmundCubes hGm.aemeasurable hG ht] with x hx
  by_cases hxΩ : x ∈ Ω
  · simp [indicator_of_notMem (notMem_compl_iff.2 hxΩ), ENNReal.zero_rpow_of_pos hr0]
  have hGx : G x ≤ t := hx fun q hq hxq => hxΩ (mem_biUnion hq hxq)
  simp only [indicator_of_mem (mem_compl hxΩ)]
  calc ∑' i, g i x ^ r = G x ^ ((r - 1) + 1) := by
        rw [sub_add_cancel, hGdef, ENNReal.rpow_inv_rpow hr0.ne']
    _ = G x ^ (r - 1) * G x := by
        rw [ENNReal.rpow_add_of_nonneg _ _ (by linarith) zero_le_one, ENNReal.rpow_one]
    _ ≤ t ^ (r - 1) * G x := by gcongr

/-- On a cube `Q` of the family, the `ℓʳ` norm of the averages of the `gᵢ` over `Q` is at most the
average of their `ℓʳ` norm `G`, which is at most `2ⁿ t`. -/
private theorem tsum_cubeAverage_rpow_le (hg : ∀ i, Measurable (g i)) (hr : 1 < r)
    (hGdef : ∀ x, G x = (∑' i, g i x ^ r) ^ r⁻¹) (x : ι → ℝ) :
    ∑' i, cubeAverage (calderonZygmundCubes G t) (g i) x ^ r ≤
      (2 ^ Fintype.card ι * t) ^ (r - 1) * cubeAverage (calderonZygmundCubes G t) G x := by
  have hr0 : 0 < r := zero_lt_one.trans hr
  by_cases hx : ∃ q ∈ calderonZygmundCubes G t, x ∈ dyadicCube q.1 q.2
  · obtain ⟨q, hq, hxq⟩ := hx
    have hC := pairwiseDisjoint_calderonZygmundCubes (g := G) (t := t)
    simp only [cubeAverage_of_mem hC hq hxq, setLAverage_eq']
    calc ∑' i, (∫⁻ y, g i y ∂(volume (dyadicCube q.1 q.2))⁻¹ •
          volume.restrict (dyadicCube q.1 q.2)) ^ r
        ≤ (∫⁻ y, G y ∂(volume (dyadicCube q.1 q.2))⁻¹ •
          volume.restrict (dyadicCube q.1 q.2)) ^ ((r - 1) + 1) := by
          simpa only [sub_add_cancel, ← hGdef] using tsum_rpow_lintegral_le hg hr.le
      _ ≤ (2 ^ Fintype.card ι * t) ^ (r - 1) * ∫⁻ y, G y ∂(volume (dyadicCube q.1 q.2))⁻¹ •
          volume.restrict (dyadicCube q.1 q.2) := by
          rw [ENNReal.rpow_add_of_nonneg _ _ (by linarith) zero_le_one, ENNReal.rpow_one]
          gcongr
          rw [← setLAverage_eq']
          exact setLAverage_le_of_mem_calderonZygmundCubes hq
  · simp only [not_exists, not_and] at hx
    simp [cubeAverage_of_forall_notMem hx, ENNReal.zero_rpow_of_pos hr0]

/-- The part of the family on the Calderón–Zygmund cubes, replaced by its averages over the
cubes: its `Lʳ(ℓʳ)` norm to the power `r` is at most `(2ⁿ t) ^ (r - 1) ∫⁻ G`. -/
private theorem lintegral_tsum_maximalFunction_cubeAverage_le
    (hg : ∀ i, Measurable (g i)) (hr : 1 < r) (hGdef : ∀ x, G x = (∑' i, g i x ^ r) ^ r⁻¹) :
    ∫⁻ x, ∑' i, maximalFunction volume (cubeAverage (calderonZygmundCubes G t) (g i)) x ^ r ≤
      ENNReal.ofReal (2 * r * 2 ^ (r - 1) / (r - 1)) * 4 ^ Fintype.card ι *
        ((2 ^ Fintype.card ι * t) ^ (r - 1) * ∫⁻ x, G x) := by
  refine (lintegral_tsum_maximalFunction_rpow_le_of_measurable
    (fun _ => measurable_cubeAverage) hr).trans ?_
  gcongr _ * ?_
  calc ∫⁻ x, ∑' i, cubeAverage (calderonZygmundCubes G t) (g i) x ^ r
      ≤ ∫⁻ x, (2 ^ Fintype.card ι * t) ^ (r - 1) * cubeAverage (calderonZygmundCubes G t) G x :=
        lintegral_mono fun x => tsum_cubeAverage_rpow_le hg hr hGdef x
    _ ≤ (2 ^ Fintype.card ι * t) ^ (r - 1) * ∫⁻ x, G x := by
        rw [lintegral_const_mul _ measurable_cubeAverage]
        exact mul_le_mul' le_rfl (lintegral_cubeAverage_le pairwiseDisjoint_calderonZygmundCubes)

omit [Countable κ] in
/-- The pointwise split behind the weak type bound. Off the concentric triples of the
Calderón–Zygmund cubes of `G` at height `t`, the `ℓʳ`-valued maximal function of `(gᵢ)` is
controlled by the maximal functions of the parts of the `gᵢ` off the cubes and of their averages
over the cubes. -/
private theorem tsum_maximalFunction_rpow_le_of_forall_notMem_ball (hg : ∀ i, Measurable (g i))
    (hr : 1 < r) {x : ι → ℝ}
    (hx : ∀ q ∈ calderonZygmundCubes G t, x ∉ ball (cubeCentre q) (3 * 2 ^ q.1 / 2)) :
    ∑' i, maximalFunction volume (g i) x ^ r ≤
      2 ^ (r - 1) * (∑' i, maximalFunction volume
          ((⋃ q ∈ calderonZygmundCubes G t, dyadicCube q.1 q.2)ᶜ.indicator (g i)) x ^ r +
        (2 ^ Fintype.card ι) ^ r *
          ∑' i, maximalFunction volume (cubeAverage (calderonZygmundCubes G t) (g i)) x ^ r) := by
  set Ω := ⋃ q ∈ calderonZygmundCubes G t, dyadicCube q.1 q.2
  have hΩ : MeasurableSet Ω := measurableSet_biUnion_calderonZygmundCubes G t
  rw [← ENNReal.tsum_mul_left, ← tsum_add, ← ENNReal.tsum_mul_left]
  refine tsum_le_tsum fun i => ?_
  have hsplit : maximalFunction volume (g i) x ≤ maximalFunction volume (Ωᶜ.indicator (g i)) x +
      2 ^ Fintype.card ι *
        maximalFunction volume (cubeAverage (calderonZygmundCubes G t) (g i)) x := by
    calc maximalFunction volume (g i) x
        = maximalFunction volume (Ωᶜ.indicator (g i) + Ω.indicator (g i)) x := by
          rw [add_comm, indicator_self_add_compl]
      _ ≤ maximalFunction volume (Ωᶜ.indicator (g i)) x +
          maximalFunction volume (Ω.indicator (g i)) x :=
        maximalFunction_add_le
          (by simpa only [enorm_eq_self] using ((hg i).indicator hΩ.compl).aemeasurable) x
      _ ≤ _ := by
        gcongr
        exact maximalFunction_indicator_le pairwiseDisjoint_calderonZygmundCubes hx
  calc maximalFunction volume (g i) x ^ r
      ≤ (maximalFunction volume (Ωᶜ.indicator (g i)) x + 2 ^ Fintype.card ι *
          maximalFunction volume (cubeAverage (calderonZygmundCubes G t) (g i)) x) ^ r :=
        ENNReal.rpow_le_rpow hsplit (by linarith)
    _ ≤ _ := ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hr.le
    _ = _ := by rw [ENNReal.mul_rpow_of_nonneg _ _ (by linarith)]

/-- The concentric triples of the Calderón–Zygmund cubes of `G` at height `t` have measure at
most `3ⁿ ∫⁻ G / t`. -/
private theorem mul_volume_biUnion_ball_le (G : (ι → ℝ) → ℝ≥0∞) (t : ℝ≥0∞) :
    t * volume (⋃ q ∈ calderonZygmundCubes G t, ball (cubeCentre q) (3 * 2 ^ q.1 / 2)) ≤
      3 ^ Fintype.card ι * ∫⁻ x, G x :=
  calc t * volume (⋃ q ∈ calderonZygmundCubes G t, ball (cubeCentre q) (3 * 2 ^ q.1 / 2))
      ≤ t * (3 ^ Fintype.card ι *
          volume (⋃ q ∈ calderonZygmundCubes G t, dyadicCube q.1 q.2)) :=
        mul_le_mul' le_rfl (volume_biUnion_ball_calderonZygmundCubes_le G t)
    _ = 3 ^ Fintype.card ι * (t * volume (⋃ q ∈ calderonZygmundCubes G t, dyadicCube q.1 q.2)) :=
        mul_left_comm _ _ _
    _ ≤ 3 ^ Fintype.card ι * ∫⁻ x, G x :=
        mul_le_mul' le_rfl
          (mul_volume_biUnion_calderonZygmundCubes_le.trans (setLIntegral_le_lintegral _ _))

/-- The weak type `(1, 1)` bound in positive dimension, for measurable nonnegative functions,
an integrable `ℓʳ` norm and a finite nonzero height. -/
private theorem mul_volume_lt_tsum_maximalFunction_rpow_le_of_measurable [Nonempty ι]
    (hg : ∀ i, Measurable (g i)) (hr : 1 < r) (hG : ∫⁻ x, (∑' i, g i x ^ r) ^ r⁻¹ ≠ ∞)
    (ht : t ≠ 0) (ht' : t ≠ ∞) :
    t * volume {x | t ^ r < ∑' i, maximalFunction volume (g i) x ^ r} ≤
      (3 ^ Fintype.card ι + 2 ^ (r - 1) *
        (ENNReal.ofReal (2 * r * 2 ^ (r - 1) / (r - 1)) * 4 ^ Fintype.card ι) *
          (1 + (2 ^ Fintype.card ι) ^ (2 * r - 1))) * ∫⁻ x, (∑' i, g i x ^ r) ^ r⁻¹ := by
  set n := Fintype.card ι
  set c := ENNReal.ofReal (2 * r * 2 ^ (r - 1) / (r - 1)) * 4 ^ n
  set G : (ι → ℝ) → ℝ≥0∞ := fun x => (∑' i, g i x ^ r) ^ r⁻¹
  have hGm : Measurable G := (Measurable.tsum fun i => (hg i).pow_const r).pow_const _
  have hr1 : 0 ≤ r - 1 := by linarith
  set Ω := ⋃ q ∈ calderonZygmundCubes G t, dyadicCube q.1 q.2
  set Ωs := ⋃ q ∈ calderonZygmundCubes G t, ball (cubeCentre q) (3 * 2 ^ q.1 / 2)
  set A := fun x => ∑' i, maximalFunction volume (Ωᶜ.indicator (g i)) x ^ r
  set H := fun x =>
    ∑' i, maximalFunction volume (cubeAverage (calderonZygmundCubes G t) (g i)) x ^ r
  have hA : Measurable A := .tsum fun i => (measurable_maximalFunction volume _).pow_const r
  have hH : Measurable H := .tsum fun i => (measurable_maximalFunction volume _).pow_const r
  -- Chebyshev's inequality for the two controlling maximal functions.
  have h2 : (2 : ℝ≥0∞) ^ n ≠ 0 := pow_ne_zero _ two_ne_zero
  have h2' : (2 : ℝ≥0∞) ^ n ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  have hΦ : ∫⁻ x, 2 ^ (r - 1) * (A x + (2 ^ n) ^ r * H x) ≤
      t ^ (r - 1) * (2 ^ (r - 1) * c * (1 + (2 ^ n) ^ (2 * r - 1)) * ∫⁻ x, G x) := by
    have hΦm : Measurable fun x => A x + (2 ^ n) ^ r * H x := hA.add (hH.const_mul _)
    rw [lintegral_const_mul _ hΦm, lintegral_add_left hA, lintegral_const_mul _ hH]
    calc 2 ^ (r - 1) * ((∫⁻ x, A x) + (2 ^ n) ^ r * ∫⁻ x, H x)
        ≤ 2 ^ (r - 1) * (c * (t ^ (r - 1) * ∫⁻ x, G x) +
            (2 ^ n) ^ r * (c * ((2 ^ n * t) ^ (r - 1) * ∫⁻ x, G x))) :=
          mul_le_mul' le_rfl (add_le_add
            (lintegral_tsum_maximalFunction_indicator_compl_le hg hr (fun _ => rfl) hGm hG ht)
            (mul_le_mul' le_rfl (lintegral_tsum_maximalFunction_cubeAverage_le hg hr
              fun _ => rfl)))
      _ = _ := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hr1, show 2 * r - 1 = r + (r - 1) by ring,
            ENNReal.rpow_add _ _ h2 h2']
          ring
  have hΦm : Measurable fun x => 2 ^ (r - 1) * (A x + (2 ^ n) ^ r * H x) :=
    (hA.add (hH.const_mul _)).const_mul _
  have hcheb := mul_meas_ge_le_lintegral₀ (μ := volume) hΦm.aemeasurable (t ^ r)
  have htr : t ^ r = t ^ (r - 1) * t := by
    conv_lhs => rw [show r = (r - 1) + 1 by ring]
    rw [ENNReal.rpow_add_of_nonneg _ _ hr1 zero_le_one, ENNReal.rpow_one]
  rw [htr, mul_assoc] at hcheb
  have hT := (ENNReal.mul_le_mul_iff_right (ENNReal.rpow_pos (pos_iff_ne_zero.2 ht) ht').ne'
    (ENNReal.rpow_ne_top_of_nonneg hr1 ht')).1 (hcheb.trans hΦ)
  -- Off `Ωs` the `ℓʳ`-valued maximal function is controlled by `A` and `H`.
  have hsub : {x | t ^ r < ∑' i, maximalFunction volume (g i) x ^ r} ⊆
      Ωs ∪ {x | t ^ (r - 1) * t ≤ 2 ^ (r - 1) * (A x + (2 ^ n) ^ r * H x)} := by
    intro x hx
    by_cases hxs : x ∈ Ωs
    · exact Or.inl hxs
    rw [mem_ofPred_eq, htr] at hx
    exact Or.inr (hx.le.trans (tsum_maximalFunction_rpow_le_of_forall_notMem_ball hg hr
      fun q hq hxq => hxs (mem_biUnion hq hxq)))
  calc t * volume {x | t ^ r < ∑' i, maximalFunction volume (g i) x ^ r}
      ≤ t * volume Ωs +
          t * volume {x | t ^ (r - 1) * t ≤ 2 ^ (r - 1) * (A x + (2 ^ n) ^ r * H x)} := by
        rw [← mul_add]
        gcongr
        exact (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ 3 ^ n * (∫⁻ x, G x) + 2 ^ (r - 1) * c * (1 + (2 ^ n) ^ (2 * r - 1)) * ∫⁻ x, G x :=
        add_le_add (mul_volume_biUnion_ball_le G t) hT
    _ = _ := by rw [add_mul]

/-- In dimension zero the whole space, a single point, has volume `1`. -/
private theorem volume_univ_of_isEmpty [IsEmpty ι] : volume (univ : Set (ι → ℝ)) = 1 := by
  have hQ : dyadicCube 0 (0 : ι → ℤ) = univ :=
    eq_univ_of_forall fun y => mem_dyadicCube.2 (Subsingleton.elim _ _)
  rw [← hQ, volume_dyadicCube, Fintype.card_eq_zero, pow_zero, ENNReal.ofReal_one]

/-- In dimension zero the maximal function of `a` is at most its integral: every ball is the
whole space, of volume `1`. -/
private theorem maximalFunction_le_lintegral_of_isEmpty [IsEmpty ι] (a : (ι → ℝ) → ℝ≥0∞)
    (x : ι → ℝ) : maximalFunction volume a x ≤ ∫⁻ y, a y := by
  have hvol : volume (univ : Set (ι → ℝ)) = 1 := volume_univ_of_isEmpty
  refine maximalFunction_le fun ρ hρ => ?_
  have hball : ball x ρ = univ :=
    eq_univ_of_forall fun y => by simpa [Subsingleton.elim y x] using hρ
  rw [hball, setLAverage_eq, Measure.restrict_univ, hvol, div_one]
  simp only [enorm_eq_self, le_refl]

/-- In dimension zero the weak type bound holds with constant `1`: by Minkowski's inequality the
`ℓʳ` norm of the maximal functions is at most `∫⁻ (∑' i, gᵢ ^ r) ^ (1 / r)`. -/
private theorem mul_volume_lt_tsum_maximalFunction_rpow_le_of_isEmpty [IsEmpty ι]
    (hg : ∀ i, Measurable (g i)) (hr : 1 < r) (t : ℝ≥0∞) :
    t * volume {x | t ^ r < ∑' i, maximalFunction volume (g i) x ^ r} ≤
      ∫⁻ x, (∑' i, g i x ^ r) ^ r⁻¹ := by
  have hr0 : 0 < r := zero_lt_one.trans hr
  rcases {x | t ^ r < ∑' i, maximalFunction volume (g i) x ^ r}.eq_empty_or_nonempty with
    hS | ⟨x, hx⟩
  · simp [hS]
  have hlt : t < ∫⁻ x, (∑' i, g i x ^ r) ^ r⁻¹ := by
    rw [← ENNReal.rpow_lt_rpow_iff hr0]
    calc t ^ r < ∑' i, maximalFunction volume (g i) x ^ r := hx
      _ ≤ ∑' i, (∫⁻ y, g i y) ^ r := tsum_le_tsum fun i =>
          ENNReal.rpow_le_rpow (maximalFunction_le_lintegral_of_isEmpty _ x) hr0.le
      _ ≤ _ := tsum_rpow_lintegral_le hg hr.le
  calc t * volume {x | t ^ r < ∑' i, maximalFunction volume (g i) x ^ r}
      ≤ t * volume (univ : Set (ι → ℝ)) := by gcongr; exact subset_univ _
    _ ≤ _ := by rw [volume_univ_of_isEmpty, mul_one]; exact hlt.le

end WeakType

section VectorValued

variable {F : Type*} [ENorm F] {f : κ → (ι → ℝ) → F} {r : ℝ}

/-- A countable family of functions with a.e. measurable norms has a family of measurable
modifications of its norms, with the same maximal functions. -/
private theorem exists_measurable_ae_eq (hf : ∀ i, AEMeasurable (fun x => ‖f i x‖ₑ)) :
    ∃ g : κ → (ι → ℝ) → ℝ≥0∞, (∀ i, Measurable (g i)) ∧
      (∀ i x, maximalFunction volume (f i) x = maximalFunction volume (g i) x) ∧
      ∀ᵐ x, ∀ i, ‖f i x‖ₑ = g i x :=
  ⟨fun i => (hf i).mk _, fun i => (hf i).measurable_mk, fun i _ => maximalFunction_congr_ae
    ((hf i).ae_eq_mk.mono fun _ hy => by simpa only [enorm_eq_self] using hy),
    ae_all_iff.2 fun i => (hf i).ae_eq_mk⟩

/-- **The weak type `(1, 1)` bound for the `ℓʳ`-valued maximal function** on `ℝⁿ` with the sup
norm, for `1 < r < ∞` and a countable family `(fᵢ)`:

`t * |{(∑' i, (M fᵢ) ^ r) ^ (1 / r) > t}| ≤ A * ∫⁻ (∑' i, ‖fᵢ‖ₑ ^ r) ^ (1 / r)`,

with `A = 3ⁿ + 2 ^ (r - 1) * c * (1 + (2ⁿ) ^ (2 r - 1))`, where
`c = 2 r 2 ^ (r - 1) / (r - 1) * 4ⁿ` is the constant of the diagonal bound
`TauCeti.lintegral_tsum_maximalFunction_rpow_le`. The constant depends only on `n` and `r`.

No integrability hypothesis is needed: the bound is vacuous when the right-hand integral is
infinite. -/
theorem mul_volume_lt_tsum_maximalFunction_rpow_rpow_inv_le
    (hf : ∀ i, AEMeasurable (fun x => ‖f i x‖ₑ)) (hr : 1 < r) (t : ℝ≥0∞) :
    t * volume {x | t < (∑' i, maximalFunction volume (f i) x ^ r) ^ r⁻¹} ≤
      (3 ^ Fintype.card ι + 2 ^ (r - 1) *
        (ENNReal.ofReal (2 * r * 2 ^ (r - 1) / (r - 1)) * 4 ^ Fintype.card ι) *
          (1 + (2 ^ Fintype.card ι) ^ (2 * r - 1))) * ∫⁻ x, (∑' i, ‖f i x‖ₑ ^ r) ^ r⁻¹ := by
  have hr0 : 0 < r := zero_lt_one.trans hr
  obtain ⟨g, hg, hM, hfg⟩ := exists_measurable_ae_eq hf
  have hI : ∫⁻ x, (∑' i, ‖f i x‖ₑ ^ r) ^ r⁻¹ = ∫⁻ x, (∑' i, g i x ^ r) ^ r⁻¹ :=
    lintegral_congr_ae (hfg.mono fun x hx => by simp only [hx])
  simp only [hM, hI, ENNReal.lt_rpow_inv_iff hr0]
  have hA : (1 : ℝ≥0∞) ≤ 3 ^ Fintype.card ι + 2 ^ (r - 1) *
      (ENNReal.ofReal (2 * r * 2 ^ (r - 1) / (r - 1)) * 4 ^ Fintype.card ι) *
        (1 + (2 ^ Fintype.card ι) ^ (2 * r - 1)) :=
    le_add_right (one_le_pow₀ (by norm_num))
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  rcases eq_or_ne t ∞ with rfl | ht'
  · simp [ENNReal.top_rpow_of_pos hr0]
  rcases eq_or_ne (∫⁻ x, (∑' i, g i x ^ r) ^ r⁻¹) ∞ with hG | hG
  · rw [hG, ENNReal.mul_top (zero_lt_one.trans_le hA).ne']
    exact le_top
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact (mul_volume_lt_tsum_maximalFunction_rpow_le_of_isEmpty hg hr t).trans
      (le_mul_of_one_le_left' hA)
  · exact mul_volume_lt_tsum_maximalFunction_rpow_le_of_measurable hg hr hG ht ht'

omit [Countable κ] in
/-- The maximal functions of a family split along a measurable set `H`: their `ℓʳ` norm to the
power `r` is at most `2 ^ (r - 1)` times the sum of those of the restrictions to `H` and to its
complement. -/
private theorem tsum_maximalFunction_rpow_le_indicator {g : κ → (ι → ℝ) → ℝ≥0∞}
    (hg : ∀ i, Measurable (g i)) (hr : 1 < r) {H : Set (ι → ℝ)} (hH : MeasurableSet H)
    (x : ι → ℝ) :
    ∑' i, maximalFunction volume (g i) x ^ r ≤
      2 ^ (r - 1) * (∑' i, maximalFunction volume (H.indicator (g i)) x ^ r +
        ∑' i, maximalFunction volume (Hᶜ.indicator (g i)) x ^ r) := by
  rw [← tsum_add, ← ENNReal.tsum_mul_left]
  refine tsum_le_tsum fun i => ?_
  calc maximalFunction volume (g i) x ^ r
      = maximalFunction volume (H.indicator (g i) + Hᶜ.indicator (g i)) x ^ r := by
        rw [indicator_self_add_compl]
    _ ≤ (maximalFunction volume (H.indicator (g i)) x +
          maximalFunction volume (Hᶜ.indicator (g i)) x) ^ r :=
        ENNReal.rpow_le_rpow (maximalFunction_add_le
          (by simpa only [enorm_eq_self] using ((hg i).indicator hH).aemeasurable) x) (by linarith)
    _ ≤ _ := ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hr.le

/-- The reciprocal of half a positive height: `(t / 2)⁻¹ = 2 t⁻¹`. -/
private theorem inv_ofReal_half {t : ℝ} (ht : 0 < t) :
    (ENNReal.ofReal (t / 2))⁻¹ = 2 * ENNReal.ofReal (t ^ (-1 : ℝ)) := by
  rw [← ENNReal.ofReal_inv_of_pos (half_pos ht), Real.rpow_neg_one, ← ENNReal.ofReal_ofNat 2,
    ← ENNReal.ofReal_mul zero_le_two, inv_div, div_eq_mul_inv]

/-- The reciprocal of a power of half a positive height: `((t / 2) ^ r)⁻¹ = 2 ^ r t ^ (-r)`. -/
private theorem inv_ofReal_half_rpow {t : ℝ} (ht : 0 < t) :
    (ENNReal.ofReal (t / 2) ^ r)⁻¹ = 2 ^ r * ENNReal.ofReal (t ^ (-r)) := by
  rw [ENNReal.ofReal_rpow_of_pos (half_pos ht),
    ← ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos (half_pos ht) r),
    Real.div_rpow ht.le zero_le_two, inv_div, div_eq_mul_inv, ← Real.rpow_neg ht.le,
    ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_rpow_of_pos two_pos,
    ENNReal.ofReal_ofNat, mul_comm]

/-- The **distributional estimate** behind the interpolation. Given a weak type `(1, 1)` bound
with constant `A` and a strong `(r, r)` bound with constant `c` for the `ℓʳ`-valued maximal
function, split `(gᵢ)` according to whether its `ℓʳ` norm `G` exceeds `t`: the part above `t` is
measured by the weak bound and the part below it by the strong bound. -/
private theorem volume_lt_tsum_maximalFunction_rpow_rpow_inv_le {g : κ → (ι → ℝ) → ℝ≥0∞}
    {G : (ι → ℝ) → ℝ≥0∞} {A c : ℝ≥0∞}
    (hweak : ∀ h : κ → (ι → ℝ) → ℝ≥0∞, (∀ i, Measurable (h i)) → ∀ s : ℝ≥0∞,
      s * volume {x | s < (∑' i, maximalFunction volume (h i) x ^ r) ^ r⁻¹} ≤
        A * ∫⁻ x, (∑' i, h i x ^ r) ^ r⁻¹)
    (hdiag : ∀ h : κ → (ι → ℝ) → ℝ≥0∞, (∀ i, Measurable (h i)) →
      ∫⁻ x, ∑' i, maximalFunction volume (h i) x ^ r ≤ c * ∫⁻ x, ∑' i, h i x ^ r)
    (hg : ∀ i, Measurable (g i)) (hr : 1 < r) (hGdef : ∀ x, G x = (∑' i, g i x ^ r) ^ r⁻¹)
    {t : ℝ} (ht : 0 < t) :
    volume {x | ENNReal.ofReal t < (∑' i, maximalFunction volume (g i) x ^ r) ^ r⁻¹} ≤
      2 * A * ENNReal.ofReal (t ^ (-1 : ℝ)) * (∫⁻ x in {x | ENNReal.ofReal t < G x}, G x) +
        2 ^ r * c * ENNReal.ofReal (t ^ (-r)) *
          ∫⁻ x in {x | G x ≤ ENNReal.ofReal t}, G x ^ r := by
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hGm : Measurable G := by
    simp only [funext hGdef]
    exact (Measurable.tsum fun i => (hg i).pow_const r).pow_const _
  set H := {x | ENNReal.ofReal t < G x}
  have hH : MeasurableSet H := measurableSet_lt measurable_const hGm
  have hHc : Hᶜ = {x | G x ≤ ENNReal.ofReal t} := by ext x; simp [H]
  set s := ENNReal.ofReal (t / 2)
  have hs0 : s ≠ 0 := (ENNReal.ofReal_pos.2 (half_pos ht)).ne'
  have hs : s ≠ ∞ := ENNReal.ofReal_ne_top
  have hsr0 : s ^ r ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.2 hs0) hs).ne'
  have hsr : s ^ r ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hr0.le hs
  set Uh := fun x => ∑' i, maximalFunction volume (H.indicator (g i)) x ^ r
  set Ul := fun x => ∑' i, maximalFunction volume (Hᶜ.indicator (g i)) x ^ r
  have hUl : Measurable Ul := .tsum fun i => (measurable_maximalFunction volume _).pow_const r
  -- The height `t` is twice `s`, and a point above it has `Uh` or `Ul` above `s ^ r`.
  have h2r : (2 : ℝ≥0∞) ^ (r - 1) * 2 = 2 ^ r := by
    conv_rhs => rw [show r = (r - 1) + 1 by ring]
    rw [ENNReal.rpow_add_of_nonneg _ _ (by linarith) zero_le_one, ENNReal.rpow_one]
  have hts : ENNReal.ofReal t ^ r = 2 ^ (r - 1) * (s ^ r + s ^ r) := by
    rw [← two_mul, ← mul_assoc, h2r, ← ENNReal.mul_rpow_of_nonneg _ _ hr0.le,
      ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul zero_le_two]
    congr 2
    ring
  have hsub : {x | ENNReal.ofReal t < (∑' i, maximalFunction volume (g i) x ^ r) ^ r⁻¹} ⊆
      {x | s < (Uh x) ^ r⁻¹} ∪ {x | s ^ r ≤ Ul x} := by
    intro x hx
    rw [mem_ofPred_eq, ENNReal.lt_rpow_inv_iff hr0, hts] at hx
    by_contra hnot
    simp only [mem_union, mem_ofPred_eq, ENNReal.lt_rpow_inv_iff hr0, not_or, not_lt,
      not_le] at hnot
    exact hx.not_ge ((tsum_maximalFunction_rpow_le_indicator hg hr hH x).trans
      (by gcongr; exacts [hnot.1, hnot.2.le]))
  -- The part above `t`, by the weak type bound.
  have hhigh : volume {x | s < (Uh x) ^ r⁻¹} ≤
      A * (∫⁻ x in {x | ENNReal.ofReal t < G x}, G x) / s := by
    rw [ENNReal.le_div_iff_mul_le (.inl hs0) (.inl hs), mul_comm]
    refine (hweak _ (fun i => (hg i).indicator hH) s).trans_eq ?_
    rw [← lintegral_indicator hH]
    congr 2
    ext x
    by_cases hx : x ∈ H
    · simp [indicator_of_mem hx, hGdef]
    · simp [indicator_of_notMem hx, ENNReal.zero_rpow_of_pos hr0,
        ENNReal.zero_rpow_of_pos (inv_pos.2 hr0)]
  -- The part below `t`, by Chebyshev's inequality and the strong `(r, r)` bound.
  have hlow : volume {x | s ^ r ≤ Ul x} ≤
      c * (∫⁻ x in {x | G x ≤ ENNReal.ofReal t}, G x ^ r) / s ^ r := by
    refine (meas_ge_le_lintegral_div hUl.aemeasurable hsr0 hsr).trans ?_
    gcongr
    refine (hdiag _ fun i => (hg i).indicator hH.compl).trans_eq ?_
    rw [← hHc, ← lintegral_indicator hH.compl]
    congr 2
    ext x
    by_cases hx : x ∈ Hᶜ
    · simp [indicator_of_mem hx, hGdef, ENNReal.rpow_inv_rpow hr0.ne']
    · simp [indicator_of_notMem hx, ENNReal.zero_rpow_of_pos hr0]
  calc volume {x | ENNReal.ofReal t < (∑' i, maximalFunction volume (g i) x ^ r) ^ r⁻¹}
      ≤ volume {x | s < (Uh x) ^ r⁻¹} + volume {x | s ^ r ≤ Ul x} :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ A * (∫⁻ x in {x | ENNReal.ofReal t < G x}, G x) / s +
          c * (∫⁻ x in {x | G x ≤ ENNReal.ofReal t}, G x ^ r) / s ^ r := add_le_add hhigh hlow
    _ = _ := by
        rw [div_eq_mul_inv, div_eq_mul_inv, inv_ofReal_half ht, inv_ofReal_half_rpow ht]
        ring

/-- **The vector-valued maximal inequality of Fefferman and Stein below the inner exponent**: for
`1 < p < r < ∞` and a countable family `(fᵢ)` on `ℝⁿ` with the sup norm,

`∫⁻ (∑' i, (M fᵢ) ^ r) ^ (p / r) ≤ C * ∫⁻ (∑' i, ‖fᵢ‖ₑ ^ r) ^ (p / r)`,

with `C = p / (p - 1) * 2 A + p / (r - p) * 2 ^ r c`, where `A` is the constant of the weak type
`(1, 1)` bound `TauCeti.mul_volume_lt_tsum_maximalFunction_rpow_rpow_inv_le` and `c` that of the
diagonal bound `TauCeti.lintegral_tsum_maximalFunction_rpow_le`. The constant depends only on `n`,
`r` and `p`, and degenerates as `p` approaches `1` or `r`. The range `r ≤ p` is
`TauCeti.lintegral_rpow_tsum_maximalFunction_rpow_le`. -/
theorem lintegral_rpow_tsum_maximalFunction_rpow_le_of_lt
    (hf : ∀ i, AEMeasurable (fun x => ‖f i x‖ₑ)) {p : ℝ} (hp : 1 < p) (hpr : p < r) :
    ∫⁻ x, (∑' i, maximalFunction volume (f i) x ^ r) ^ (p / r) ≤
      (ENNReal.ofReal (p / (p - 1)) * (2 * (3 ^ Fintype.card ι + 2 ^ (r - 1) *
          (ENNReal.ofReal (2 * r * 2 ^ (r - 1) / (r - 1)) * 4 ^ Fintype.card ι) *
            (1 + (2 ^ Fintype.card ι) ^ (2 * r - 1)))) +
        ENNReal.ofReal (p / (r - p)) *
          (2 ^ r * (ENNReal.ofReal (2 * r * 2 ^ (r - 1) / (r - 1)) * 4 ^ Fintype.card ι))) *
        ∫⁻ x, (∑' i, ‖f i x‖ₑ ^ r) ^ (p / r) := by
  have hr : 1 < r := hp.trans hpr
  obtain ⟨g, hg, hM, hfg⟩ := exists_measurable_ae_eq hf
  have hI : ∫⁻ x, (∑' i, ‖f i x‖ₑ ^ r) ^ (p / r) = ∫⁻ x, (∑' i, g i x ^ r) ^ (p / r) :=
    lintegral_congr_ae (hfg.mono fun x hx => by simp only [hx])
  simp only [hM, hI]
  have hu : Measurable fun x => (∑' i, maximalFunction volume (g i) x ^ r) ^ r⁻¹ :=
    (Measurable.tsum fun i => (measurable_maximalFunction volume _).pow_const r).pow_const _
  have hG : Measurable fun x => (∑' i, g i x ^ r) ^ r⁻¹ :=
    (Measurable.tsum fun i => (hg i).pow_const r).pow_const _
  have key := lintegral_rpow_le_of_meas_ofReal_lt_le (μ := volume) (ν := volume)
    hG.aemeasurable hu.aemeasurable zero_lt_one
    hp hpr zero_lt_one fun t ht => by
      simpa only [one_mul, ENNReal.rpow_one] using
        volume_lt_tsum_maximalFunction_rpow_rpow_inv_le
          (fun h hh s => by
            simpa only [enorm_eq_self] using
              mul_volume_lt_tsum_maximalFunction_rpow_rpow_inv_le (f := h)
                (fun i => (hh i).aemeasurable) hr s)
          (fun h hh => lintegral_tsum_maximalFunction_rpow_le_of_measurable hh hr) hg hr
          (fun _ => rfl) ht
  simpa only [Real.one_rpow, mul_one, ← ENNReal.rpow_mul, inv_mul_eq_div] using key

/-- **The vector-valued maximal inequality of Fefferman and Stein** on `ℝⁿ` with the sup norm,
in the full range: for `1 < r < ∞` and `1 < p < ∞` there is a finite constant `C`, depending only
on `n`, `r` and `p`, such that every countable family `(fᵢ)` of functions with a.e. measurable
norms satisfies

`∫⁻ (∑' i, (M fᵢ) ^ r) ^ (p / r) ≤ C * ∫⁻ (∑' i, ‖fᵢ‖ₑ ^ r) ^ (p / r)`.

With `r = 2` this is the square-function form
`‖(∑ (M fᵢ) ^ 2) ^ (1 / 2)‖_p ≲ ‖(∑ ‖fᵢ‖ ^ 2) ^ (1 / 2)‖_p`.
The explicit constants are those of `TauCeti.lintegral_rpow_tsum_maximalFunction_rpow_le_of_lt`
for `p < r`, `TauCeti.lintegral_tsum_maximalFunction_rpow_le` for `p = r` and
`TauCeti.lintegral_rpow_tsum_maximalFunction_rpow_le` for `r < p`. -/
theorem exists_lintegral_rpow_tsum_maximalFunction_rpow_le {p : ℝ} (hr : 1 < r) (hp : 1 < p) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ f : κ → (ι → ℝ) → F, (∀ i, AEMeasurable (fun x => ‖f i x‖ₑ)) →
      ∫⁻ x, (∑' i, maximalFunction volume (f i) x ^ r) ^ (p / r) ≤
        C * ∫⁻ x, (∑' i, ‖f i x‖ₑ ^ r) ^ (p / r) := by
  rcases lt_trichotomy p r with hpr | rfl | hrp
  · exact ⟨_, by finiteness, fun f hf =>
      lintegral_rpow_tsum_maximalFunction_rpow_le_of_lt hf hp hpr⟩
  · refine ⟨ENNReal.ofReal (2 * p * 2 ^ (p - 1) / (p - 1)) * 4 ^ Fintype.card ι, by finiteness,
      fun f hf => ?_⟩
    simpa only [div_self (zero_lt_one.trans hp).ne', ENNReal.rpow_one,
      Module.finrank_fintype_fun_eq_card] using lintegral_tsum_maximalFunction_rpow_le volume hf hp
  · refine ⟨(ENNReal.ofReal (2 * r * 2 ^ (r - 1) / (r - 1)) * 5 ^ Fintype.card ι *
      (ENNReal.ofReal (2 * (p / (p - r)) * 2 ^ (p / (p - r) - 1) / (p / (p - r) - 1)) *
        4 ^ Fintype.card ι) ^ ((p - r) / p)) ^ (p / r), by finiteness, fun f hf => ?_⟩
    simpa only [Module.finrank_fintype_fun_eq_card] using
      lintegral_rpow_tsum_maximalFunction_rpow_le volume hf hr hrp

end VectorValued

end TauCeti
