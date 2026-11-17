/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable
import TauCeti.Analysis.PSeries

/-!
# The lattice Epstein zeta function on the upper half-plane

For `z ∈ ℍ` and `s > 1`, the **lattice Epstein zeta function** is
$$Z(z, s) = \sum_{(m, n) \in \mathbb{Z}^2 \setminus \{(0, 0)\}}
  \frac{(\operatorname{Im} z)^s}{|m z + n|^{2 s}}.$$
Unimodal sum-versus-integral comparison along each horizontal line `n ∈ ℤ` (`m ≥ 1`) gives
$$\left|Z(z, s) - 2 (\operatorname{Im} z)^{1 - s} \zeta(2 s - 1)
    \int_{-\infty}^{\infty} (1 + u^2)^{-s}\,du\right|
  \le \left(2 (\operatorname{Im} z)^s + 4 (\operatorname{Im} z)^{-s}\right) \zeta(2 s),$$
yielding `lim_{s → 1⁺} (s - 1) Z(z, s) = π` and the uniform polynomial bound
`(s - 1) Z(z, s) ≤ 6 π + 36 + 4 (Im z)²` for `Im z ≥ 1 / 2` and `s ∈ (1, 2]`.

## Main definitions

* `TauCeti.EisensteinSeries.realAnalyticEpstein`: the lattice Epstein zeta function `Z(z, s)`.

## Main results

* `TauCeti.EisensteinSeries.summable_realAnalyticEpstein_summand`: convergence for `s > 1`.
* `TauCeti.EisensteinSeries.tendsto_sub_one_mul_realAnalyticEpstein`:
  `lim_{s → 1⁺} (s - 1) Z(z, s) = π`.
* `TauCeti.EisensteinSeries.sub_one_mul_realAnalyticEpstein_le`: uniform bound
  `(s - 1) Z(z, s) ≤ 6 π + 36 + 4 (Im z)²` for `1 / 2 ≤ Im z` and `s ∈ (1, 2]`.

## References

* [H. Iwaniec, *Spectral methods of automorphic forms*][iwaniec2002], Chapter 3.
* [D. Bump, *Automorphic forms and representations*][bump1997], §1.6.
-/

public section

noncomputable section

open MeasureTheory Filter Topology Real Complex UpperHalfPlane

namespace TauCeti.EisensteinSeries

/-! ### Elementary `p`-series and unimodal sum-vs-integral bounds -/

private abbrev pSum (r : ℝ) : ℝ := ∑' n : ℕ, (n : ℝ) ^ (-r)

private theorem pSum_shift {r : ℝ} (hr : 1 < r) :
    (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ (-r)) = pSum r := by
  have hsum : Summable fun n : ℕ ↦ (n : ℝ) ^ (-r) := Real.summable_nat_rpow.mpr (by linarith)
  rw [pSum, hsum.tsum_eq_zero_add, Nat.cast_zero, zero_rpow (by linarith), zero_add]

private theorem pSum_bounds {r : ℝ} (hr : 1 < r) :
    (r - 1)⁻¹ ≤ pSum r ∧ pSum r ≤ 1 + (r - 1)⁻¹ := by
  have hanti : AntitoneOn (fun t : ℝ ↦ t ^ (-r)) (Set.Ici (1 : ℕ)) := fun x hx _ _ hxy ↦
    rpow_le_rpow_of_nonpos (lt_of_lt_of_le zero_lt_one (by simpa using hx)) hxy (by linarith)
  have hsum : Summable fun n : ℕ ↦ (n : ℝ) ^ (-r) := Real.summable_nat_rpow.mpr (by linarith)
  have hnn : ∀ t ∈ Set.Ioi (1 : ℝ), 0 ≤ t ^ (-r) := fun t ht ↦
    rpow_nonneg (lt_trans zero_lt_one ht).le _
  have heval : ∫ t in Set.Ioi (1 : ℝ), t ^ (-r) = (r - 1)⁻¹ := by
    rw [integral_Ioi_rpow_of_lt (by linarith) zero_lt_one, one_rpow, neg_div, ← div_neg, one_div]
    congr 1; ring
  refine ⟨by simpa [heval, ← pSum_shift hr, Nat.cast_add, Nat.cast_one] using
    hanti.integral_le_tsum_comp_add 1 hsum (by simpa using hnn), ?_⟩
  have htail := hanti.tsum_comp_add_le_integral 1
    (by simpa using integrableOn_Ioi_rpow_of_lt (by linarith : -r < -1) zero_lt_one)
    (by simpa using hnn)
  rw [Nat.cast_one, heval] at htail
  rw [← pSum_shift hr, ((summable_nat_add_iff 1).mpr hsum).tsum_eq_zero_add]
  simp only [zero_add, Nat.cast_one, one_rpow]; linarith

private theorem tendsto_sub_one_mul_pSum :
    Tendsto (fun r : ℝ ↦ (r - 1) * pSum r) (𝓝[>] 1) (𝓝 1) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id) ?_ ?_ <;>
    filter_upwards [self_mem_nhdsWithin] with r hr
  · have hr' : 0 < r - 1 := sub_pos.mpr hr
    exact (mul_inv_cancel₀ hr'.ne').symm.trans_le
      (mul_le_mul_of_nonneg_left (pSum_bounds hr).1 hr'.le)
  · have hr' : 0 < r - 1 := sub_pos.mpr hr
    exact (mul_le_mul_of_nonneg_left (pSum_bounds hr).2 hr'.le).trans_eq
      (by dsimp only [id]; rw [mul_add, mul_one, mul_inv_cancel₀ hr'.ne']; ring)

private theorem one_add_sq_rpow_neg_le {s : ℝ} (hs : 1 ≤ s) (u : ℝ) :
    (1 + u ^ 2) ^ (-s) ≤ (1 + u ^ 2)⁻¹ :=
  rpow_neg_one (1 + u ^ 2) ▸
    rpow_le_rpow_of_exponent_le (le_add_of_nonneg_right (sq_nonneg u)) (by linarith)

private theorem continuous_one_add_sq_rpow_neg (s : ℝ) :
    Continuous fun u : ℝ ↦ (1 + u ^ 2) ^ (-s) :=
  (continuous_const.add (continuous_pow 2)).rpow continuous_const fun u ↦
    Or.inl (by positivity : (0 : ℝ) < 1 + u ^ 2).ne'

private theorem integrable_one_add_sq_rpow_neg {s : ℝ} (hs : 1 ≤ s) :
    Integrable fun u : ℝ ↦ (1 + u ^ 2) ^ (-s) :=
  integrable_inv_one_add_sq.mono' (continuous_one_add_sq_rpow_neg s).aestronglyMeasurable
    (ae_of_all _ fun u ↦ by
      rw [Real.norm_of_nonneg (rpow_nonneg (by positivity) _)]
      exact one_add_sq_rpow_neg_le hs u)

private theorem tendsto_integral_one_add_sq_rpow_neg :
    Tendsto (fun s : ℝ ↦ ∫ u : ℝ, (1 + u ^ 2) ^ (-s)) (𝓝[>] 1) (𝓝 π) := by
  rw [← integral_univ_inv_one_add_sq]
  refine tendsto_integral_filter_of_dominated_convergence (fun u : ℝ ↦ (1 + u ^ 2)⁻¹)
    (Eventually.of_forall fun s ↦ (continuous_one_add_sq_rpow_neg s).aestronglyMeasurable)
    ?_ integrable_inv_one_add_sq (ae_of_all _ fun u ↦ ?_)
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact ae_of_all _ fun u ↦ by
      rw [Real.norm_of_nonneg (rpow_nonneg (by positivity) _)]
      exact one_add_sq_rpow_neg_le (Set.mem_Ioi.mp hs).le u
  · have hc : Continuous fun s : ℝ ↦ (1 + u ^ 2) ^ (-s) :=
      continuous_const.rpow continuous_neg fun _ ↦ Or.inl (by positivity : (0 : ℝ) < 1 + u ^ 2).ne'
    simpa [rpow_neg_one] using (hc.continuousAt (x := (1 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds

private theorem integral_add_sq_add_sq_rpow_neg (a : ℝ) {b s : ℝ} (hb : 0 < b) :
    ∫ t : ℝ, ((t + a) ^ 2 + b ^ 2) ^ (-s) = b ^ (1 - 2 * s) * ∫ u : ℝ, (1 + u ^ 2) ^ (-s) := by
  rw [integral_add_right_eq_self (fun t : ℝ ↦ (t ^ 2 + b ^ 2) ^ (-s)) a]
  have hsc := Measure.integral_comp_mul_left (fun t : ℝ ↦ (t ^ 2 + b ^ 2) ^ (-s)) b
  rw [abs_inv, abs_of_pos hb, smul_eq_mul] at hsc
  rw [show ∫ t : ℝ, (t ^ 2 + b ^ 2) ^ (-s) = b * ∫ x : ℝ, ((b * x) ^ 2 + b ^ 2) ^ (-s) by
      rw [hsc, ← mul_assoc, mul_inv_cancel₀ hb.ne', one_mul],
    ← integral_const_mul, ← integral_const_mul]
  congr 1; ext u
  rw [show (b * u) ^ 2 + b ^ 2 = b ^ 2 * (1 + u ^ 2) by ring,
    mul_rpow (sq_nonneg b) (by positivity), ← rpow_natCast b 2, ← rpow_mul hb.le,
    ← mul_assoc, mul_comm b, ← rpow_add_one hb.ne']
  congr 2; push_cast; ring

private theorem integrable_add_sq_add_sq_rpow_neg (a : ℝ) {b s : ℝ} (hb : 0 < b) (hs : 1 ≤ s) :
    Integrable fun t : ℝ ↦ ((t + a) ^ 2 + b ^ 2) ^ (-s) := by
  refine (((integrable_one_add_sq_rpow_neg hs).const_mul (b ^ (-2 * s))).comp_mul_left'
    (inv_ne_zero hb.ne') |>.comp_add_right a).congr (ae_of_all _ fun t ↦ ?_)
  dsimp only
  rw [show (t + a) ^ 2 + b ^ 2 = b ^ 2 * (1 + (b⁻¹ * (t + a)) ^ 2) by field_simp [hb.ne']; ring,
    mul_rpow (sq_nonneg b) (by positivity), ← rpow_natCast b 2, ← rpow_mul hb.le]
  congr 2; push_cast; ring

private theorem abs_tsum_int_add_sq_add_sq_rpow_neg_sub_integral_le (a : ℝ) {b s : ℝ}
    (hb : 0 < b) (hs : 1 ≤ s) :
    |(∑' n : ℤ, (((n : ℝ) + a) ^ 2 + b ^ 2) ^ (-s)) - ∫ t : ℝ, ((t + a) ^ 2 + b ^ 2) ^ (-s)| ≤
      2 * b ^ (-2 * s) := by
  let φ : ℝ → ℝ := fun t ↦ ((t + a) ^ 2 + b ^ 2) ^ (-s)
  let k : ℤ := ⌊-a⌋
  have hk_le : (k : ℝ) ≤ -a := Int.floor_le (-a)
  have hk_lt : -a < (k : ℝ) + 1 := Int.lt_floor_add_one (-a)
  have hφ_nn (t : ℝ) : 0 ≤ φ t := rpow_nonneg (by positivity) _
  have hφ_le (t : ℝ) : φ t ≤ b ^ (-2 * s) :=
    (rpow_le_rpow_of_nonpos (sq_pos_of_pos hb) (le_add_of_nonneg_left (sq_nonneg _))
      (by linarith)).trans_eq (by
        rw [← rpow_natCast b 2, ← rpow_mul hb.le]; congr 1; push_cast; ring)
  have hφ_int : Integrable φ := integrable_add_sq_add_sq_rpow_neg a hb hs
  let fR : ℝ → ℝ := fun u ↦ φ ((k : ℝ) + 1 + u)
  let fL : ℝ → ℝ := fun u ↦ φ ((k : ℝ) - u)
  have hfR_anti : AntitoneOn fR (Set.Ici 0) := fun u hu _ _ huv ↦
    rpow_le_rpow_of_nonpos (by positivity) (by nlinarith [Set.mem_Ici.mp hu]) (by linarith)
  have hfL_anti : AntitoneOn fL (Set.Ici 0) := fun u hu _ _ huv ↦
    rpow_le_rpow_of_nonpos (by positivity) (by nlinarith [Set.mem_Ici.mp hu]) (by linarith)
  have hfR_int : IntegrableOn fR (Set.Ioi 0) := (hφ_int.comp_add_left ((k : ℝ) + 1)).integrableOn
  have hfL_int : IntegrableOn fL (Set.Ioi 0) := (hφ_int.comp_sub_left (k : ℝ)).integrableOn
  have hfR_sum := hfR_anti.summable_of_integrableOn_Ioi_zero hfR_int fun _ _ ↦ hφ_nn _
  have hfL_sum := hfL_anti.summable_of_integrableOn_Ioi_zero hfL_int fun _ _ ↦ hφ_nn _
  have hsum_split : ∑' n : ℤ, φ n = (∑' n : ℕ, fR n) + ∑' n : ℕ, fL n := by
    rw [← (Equiv.addLeft (k + 1)).tsum_eq]
    refine (tsum_of_nat_of_neg_add_one
      (hfR_sum.congr fun n ↦ by dsimp [fR]; congr 1; push_cast; ring)
      (hfL_sum.congr fun n ↦ by dsimp [fL]; congr 1; push_cast; ring)).trans ?_
    congr 1 <;> exact tsum_congr fun n ↦ by dsimp [fR, fL]; congr 1; push_cast; ring
  have hI_R : ∫ u in Set.Ioi (0 : ℝ), fR u = ∫ t in Set.Ioi ((k : ℝ) + 1), φ t := by
    rw [← show ((k : ℝ) + 1 + ·) '' Set.Ioi (0 : ℝ) = Set.Ioi ((k : ℝ) + 1) by
        ext t; simp only [Set.mem_image, Set.mem_Ioi]
        exact ⟨fun ⟨u, hu, h⟩ ↦ by linarith, fun ht ↦ ⟨t - (k + 1), by linarith, by ring⟩⟩,
      (measurePreserving_add_left volume _).setIntegral_image_emb (measurableEmbedding_addLeft _)]
  have hI_L : ∫ u in Set.Ioi (0 : ℝ), fL u = ∫ t in Set.Iio (k : ℝ), φ t := by
    rw [← show ((k : ℝ) - ·) '' Set.Ioi (0 : ℝ) = Set.Iio (k : ℝ) by
        ext t; simp only [Set.mem_image, Set.mem_Ioi, Set.mem_Iio]
        exact ⟨fun ⟨u, hu, h⟩ ↦ by linarith, fun ht ↦ ⟨k - t, by linarith, by ring⟩⟩,
      (volume.measurePreserving_sub_left _).setIntegral_image_emb (measurableEmbedding_subLeft _)]
  have hI_split : ∫ t : ℝ, φ t = (∫ t in Set.Iio (k : ℝ), φ t) +
      (∫ t in Set.Icc (k : ℝ) ((k : ℝ) + 1), φ t) + ∫ t in Set.Ioi ((k : ℝ) + 1), φ t := by
    rw [← setIntegral_union ((Set.Iio_disjoint_Ici le_rfl).mono_right Set.Icc_subset_Ici_self)
      measurableSet_Icc hφ_int.integrableOn hφ_int.integrableOn,
      Set.Iio_union_Icc_eq_Iic (by linarith),
      ← setIntegral_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
      hφ_int.integrableOn hφ_int.integrableOn, Set.Iic_union_Ioi, setIntegral_univ]
  have hI_mid_nn : 0 ≤ ∫ t in Set.Icc (k : ℝ) ((k : ℝ) + 1), φ t :=
    setIntegral_nonneg measurableSet_Icc fun t _ ↦ hφ_nn t
  have hI_mid_le : ∫ t in Set.Icc (k : ℝ) ((k : ℝ) + 1), φ t ≤ b ^ (-2 * s) :=
    (setIntegral_mono_on hφ_int.integrableOn (integrableOn_const (by simp))
      measurableSet_Icc fun t _ ↦ hφ_le t).trans_eq (by simp)
  rw [abs_le]
  constructor <;> linarith [hfR_anti.tsum_le_integral hfR_int fun _ _ ↦ hφ_nn _,
    hfR_anti.integral_le_tsum hfR_sum fun _ _ ↦ hφ_nn _,
    hfL_anti.tsum_le_integral hfL_int fun _ _ ↦ hφ_nn _,
    hfL_anti.integral_le_tsum hfL_sum fun _ _ ↦ hφ_nn _,
    hφ_le ((k : ℝ) + 1 + 0), hφ_le ((k : ℝ) - 0)]

/-! ### The lattice Epstein zeta function on `ℍ` -/

/-- **The lattice Epstein zeta function on `ℍ`**:
`Z(z, s) = ∑' (m, n) ∈ ℤ² \ {(0, 0)}, (Im z) ^ s / ‖m z + n‖ ^ (2 * s)`. -/
def realAnalyticEpstein (z : ℍ) (s : ℝ) : ℝ :=
  ∑' p : ℤ × ℤ, if p = 0 then 0 else z.im ^ s / ‖(p.1 : ℂ) * z + p.2‖ ^ (2 * s)

/-- Unfolding of `realAnalyticEpstein`. -/
theorem realAnalyticEpstein_def (z : ℍ) (s : ℝ) :
    realAnalyticEpstein z s =
      ∑' p : ℤ × ℤ, if p = 0 then 0 else z.im ^ s / ‖(p.1 : ℂ) * z + p.2‖ ^ (2 * s) := (rfl)

/-- Every term of `realAnalyticEpstein` is nonnegative. -/
theorem realAnalyticEpstein_nonneg (z : ℍ) (s : ℝ) : 0 ≤ realAnalyticEpstein z s :=
  tsum_nonneg fun p ↦ by split_ifs <;> positivity

/-- Summability of the defining series of `realAnalyticEpstein z s` for `s > 1`. -/
theorem summable_realAnalyticEpstein_summand (z : ℍ) {s : ℝ} (hs : 1 < s) :
    Summable fun p : ℤ × ℤ ↦ if p = 0 then 0 else z.im ^ s / ‖(p.1 : ℂ) * z + p.2‖ ^ (2 * s) := by
  rw [← (finTwoArrowEquiv ℤ).summable_iff]
  refine _root_.EisensteinSeries.summable_of_isBigO_rpow_norm (a := 2 * s) (by linarith) ?_
  obtain ⟨C, hCpos, hC⟩ := (_root_.EisensteinSeries.isBigO_linear_add_const_vec z 0 0).exists_pos
  rw [Asymptotics.isBigOWith_iff] at hC
  refine Asymptotics.isBigO_iff.mpr ⟨z.im ^ s * C ^ (2 * s), ?_⟩
  filter_upwards [hC] with m hm
  simp only [Function.comp_apply, finTwoArrowEquiv_apply]
  split_ifs
  · simp only [norm_zero]; positivity
  · simp only [Int.cast_zero, add_zero, norm_inv, norm_norm] at hm
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity),
      div_eq_mul_inv, ← inv_rpow (norm_nonneg _), mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (rpow_nonneg z.im_pos.le s)
    exact (rpow_le_rpow (by positivity) hm (by linarith)).trans_eq
      (by rw [mul_rpow hCpos.le (by positivity), inv_rpow (norm_nonneg m)])

private theorem norm_int_mul_coe_add_int_rpow (z : ℍ) (m n : ℤ) (s : ℝ) :
    z.im ^ s / ‖(m : ℂ) * z + n‖ ^ (2 * s) =
      z.im ^ s * (((n : ℝ) + (m : ℝ) * z.re) ^ 2 + ((m : ℝ) * z.im) ^ 2) ^ (-s) := by
  rw [div_eq_mul_inv, ← rpow_neg (norm_nonneg _)]
  congr 1
  have hsq : ‖(m : ℂ) * z + n‖ ^ 2 = ((n : ℝ) + (m : ℝ) * z.re) ^ 2 + ((m : ℝ) * z.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp [coe_re, coe_im]; ring
  rw [← hsq, ← rpow_natCast ‖(m : ℂ) * z + n‖ 2, ← rpow_mul (norm_nonneg _)]
  congr 1; push_cast; ring

private theorem realAnalyticEpstein_eq_row_sum (z : ℍ) {s : ℝ} (hs : 1 < s) :
    realAnalyticEpstein z s =
      2 * z.im ^ s * pSum (2 * s) + 2 * ∑' m : ℕ, ∑' n : ℤ,
        z.im ^ s * (((n : ℝ) + ((m + 1 : ℕ) : ℝ) * z.re) ^ 2 +
          (((m + 1 : ℕ) : ℝ) * z.im) ^ 2) ^ (-s) := by
  let F : ℤ → ℤ → ℝ := fun m n ↦
    if (m, n) = (0, 0) then 0 else z.im ^ s / ‖(m : ℂ) * z + n‖ ^ (2 * s)
  have hF : Summable (Function.uncurry F) := summable_realAnalyticEpstein_summand z hs
  have hrow (m : ℤ) : Summable (F m) := hF.prod_factor m
  have houter : Summable fun m : ℤ ↦ ∑' n : ℤ, F m n :=
    (hF.hasSum.prod_fiberwise fun m ↦ (hrow m).hasSum).summable
  have hsym (m n : ℤ) : F (-m) (-n) = F m n := by
    simp only [F]
    have hiff : (-m, -n) = (0, 0) ↔ (m, n) = (0, 0) := by simp [Prod.mk.injEq]
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd (hiff.mp h1) h2
    · exact absurd (hiff.mpr h2) h1
    · congr 2; rw [show ((-m : ℤ) : ℂ) * z + (-n : ℤ) = -((m : ℂ) * z + n) by push_cast; ring,
        norm_neg]
  have hneg (m : ℤ) : ∑' n : ℤ, F (-m) n = ∑' n : ℤ, F m n := by
    rw [← (Equiv.neg ℤ).tsum_eq]; exact tsum_congr fun n ↦ hsym m n
  have hrow0 : ∑' n : ℤ, F 0 n = 2 * z.im ^ s * pSum (2 * s) := by
    have h1 : Summable fun n : ℕ ↦ F 0 (n : ℤ) := (hrow 0).comp_injective Nat.cast_injective
    have h2 : Summable fun n : ℕ ↦ F 0 (-((n : ℤ) + 1)) :=
      (hrow 0).comp_injective fun _ _ h ↦ by omega
    have hpos (n : ℕ) : F 0 ((n + 1 : ℕ) : ℤ) = z.im ^ s * ((n + 1 : ℕ) : ℝ) ^ (-(2 * s)) := by
      have hne : ((0 : ℤ), ((n + 1 : ℕ) : ℤ)) ≠ (0, 0) := by simp; omega
      simp only [F, hne, ↓reduceIte, Int.cast_zero, zero_mul, zero_add, div_eq_mul_inv,
        ← rpow_neg (norm_nonneg _), Int.cast_natCast, Complex.norm_natCast]
    have hneg0 (n : ℕ) : F 0 (-((n : ℤ) + 1)) = F 0 ((n + 1 : ℕ) : ℤ) := by
      simpa [Nat.cast_add, Nat.cast_one] using hsym 0 ((n : ℤ) + 1)
    rw [tsum_of_nat_of_neg_add_one h1 h2, h1.tsum_eq_zero_add,
      show F 0 ((0 : ℕ) : ℤ) = 0 by simp [F], zero_add, tsum_congr hneg0, ← two_mul,
      tsum_congr hpos, tsum_mul_left, pSum_shift (by linarith)]
    ring
  have ho1 : Summable fun m : ℕ ↦ ∑' n : ℤ, F (m : ℤ) n := houter.comp_injective Nat.cast_injective
  have ho2 : Summable fun m : ℕ ↦ ∑' n : ℤ, F (-((m : ℤ) + 1)) n :=
    houter.comp_injective fun _ _ h ↦ by omega
  have hEq : (fun p : ℤ × ℤ ↦ if p = 0 then 0 else z.im ^ s / ‖(p.1 : ℂ) * z + p.2‖ ^ (2 * s)) =
      Function.uncurry F := funext fun ⟨_, _⟩ ↦ rfl
  rw [realAnalyticEpstein_def, hEq, hF.tsum_prod' hrow]
  simp only [Function.uncurry_apply_pair]
  rw [tsum_of_nat_of_neg_add_one ho1 ho2, ho1.tsum_eq_zero_add, Nat.cast_zero, hrow0, add_assoc]
  congr 1
  have hpair : ∑' m : ℕ, ∑' n : ℤ, F (-((m : ℤ) + 1)) n =
      ∑' m : ℕ, ∑' n : ℤ, F (((m + 1 : ℕ) : ℤ)) n :=
    tsum_congr fun m ↦ by simpa [Nat.cast_add, Nat.cast_one] using hneg ((m : ℤ) + 1)
  rw [hpair, ← two_mul]
  refine congrArg _ (tsum_congr fun m ↦ tsum_congr fun n ↦ ?_)
  have hne : (((m + 1 : ℕ) : ℤ), n) ≠ (0, 0) := fun h ↦ by have := congrArg Prod.fst h; omega
  simp only [F, hne, ↓reduceIte, norm_int_mul_coe_add_int_rpow, Int.cast_natCast]

private theorem abs_row_sub_approx_le (z : ℍ) {s : ℝ} (hs : 1 < s) (m : ℕ) :
    |(∑' n : ℤ, z.im ^ s * (((n : ℝ) + ((m + 1 : ℕ) : ℝ) * z.re) ^ 2 +
          (((m + 1 : ℕ) : ℝ) * z.im) ^ 2) ^ (-s)) -
        z.im ^ (1 - s) * (∫ u : ℝ, (1 + u ^ 2) ^ (-s)) * ((m + 1 : ℕ) : ℝ) ^ (-(2 * s - 1))| ≤
      2 * z.im ^ (-s) * ((m + 1 : ℕ) : ℝ) ^ (-(2 * s)) := by
  have hm' : (0 : ℝ) < (m + 1 : ℕ) := Nat.cast_pos.mpr (Nat.succ_pos m)
  have hb : 0 < ((m + 1 : ℕ) : ℝ) * z.im := mul_pos hm' z.im_pos
  have hterm := abs_tsum_int_add_sq_add_sq_rpow_neg_sub_integral_le
    (((m + 1 : ℕ) : ℝ) * z.re) hb hs.le
  rw [integral_add_sq_add_sq_rpow_neg _ hb] at hterm
  have hmul := mul_le_mul_of_nonneg_left hterm (rpow_nonneg z.im_pos.le s)
  conv_lhs at hmul => rw [← abs_of_nonneg (rpow_nonneg z.im_pos.le s), ← abs_mul, mul_sub]
  have hpow (c : ℝ) : z.im ^ s * (((m + 1 : ℕ) : ℝ) * z.im) ^ c =
      z.im ^ (s + c) * ((m + 1 : ℕ) : ℝ) ^ c := by
    rw [mul_rpow hm'.le z.im_pos.le, ← mul_assoc, mul_comm (z.im ^ s), mul_assoc,
      ← rpow_add z.im_pos, mul_comm]
  have h1 : z.im ^ s * (((m + 1 : ℕ) : ℝ) * z.im) ^ (1 - 2 * s) =
      z.im ^ (1 - s) * ((m + 1 : ℕ) : ℝ) ^ (-(2 * s - 1)) :=
    (hpow (1 - 2 * s)).trans (by congr 1 <;> congr 1 <;> ring)
  have h2 : z.im ^ s * (((m + 1 : ℕ) : ℝ) * z.im) ^ (-2 * s) =
      z.im ^ (-s) * ((m + 1 : ℕ) : ℝ) ^ (-(2 * s)) :=
    (hpow (-2 * s)).trans (by congr 1 <;> congr 1 <;> ring)
  rw [← tsum_mul_left, ← mul_assoc, h1, mul_right_comm, ← mul_assoc, mul_comm (z.im ^ s) 2,
    mul_assoc 2, h2] at hmul
  simpa [mul_assoc] using hmul

private theorem abs_realAnalyticEpstein_sub_le (z : ℍ) {s : ℝ} (hs : 1 < s) :
    |realAnalyticEpstein z s -
        2 * z.im ^ (1 - s) * (∫ u : ℝ, (1 + u ^ 2) ^ (-s)) * pSum (2 * s - 1)| ≤
      (2 * z.im ^ s + 4 * z.im ^ (-s)) * pSum (2 * s) := by
  let I : ℝ := ∫ u : ℝ, (1 + u ^ 2) ^ (-s)
  let f : ℕ → ℝ := fun m ↦ ∑' n : ℤ, z.im ^ s *
    (((n : ℝ) + ((m + 1 : ℕ) : ℝ) * z.re) ^ 2 + (((m + 1 : ℕ) : ℝ) * z.im) ^ 2) ^ (-s)
  let g : ℕ → ℝ := fun m ↦ z.im ^ (1 - s) * I * ((m + 1 : ℕ) : ℝ) ^ (-(2 * s - 1))
  have hz1 : Summable fun m : ℕ ↦ (m : ℝ) ^ (-(2 * s - 1)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hz2 : Summable fun m : ℕ ↦ (m : ℝ) ^ (-(2 * s)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hsum_g : Summable g := ((summable_nat_add_iff 1).mpr hz1).mul_left _
  have hsum_err : Summable fun m : ℕ ↦ 2 * z.im ^ (-s) * ((m + 1 : ℕ) : ℝ) ^ (-(2 * s)) :=
    ((summable_nat_add_iff 1).mpr hz2).mul_left _
  have hdiff_le := abs_row_sub_approx_le z hs
  have hsum_diff : Summable fun m : ℕ ↦ f m - g m :=
    Summable.of_norm_bounded hsum_err fun m ↦ by simpa only [Real.norm_eq_abs] using hdiff_le m
  have hsum_f : Summable f := by simpa only [sub_add_cancel] using hsum_diff.add hsum_g
  have htsum_diff : |(∑' m : ℕ, f m) - ∑' m : ℕ, g m| ≤ 2 * z.im ^ (-s) * pSum (2 * s) := by
    rw [← hsum_f.tsum_sub hsum_g, ← pSum_shift (by linarith), ← tsum_mul_left]
    exact (by simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hsum_diff.norm :
      |∑' m, (f m - g m)| ≤ ∑' m, |f m - g m|).trans
      (Summable.tsum_le_tsum hdiff_le hsum_diff.abs hsum_err)
  have htsum_g : ∑' m : ℕ, g m = z.im ^ (1 - s) * I * pSum (2 * s - 1) := by
    rw [tsum_mul_left, pSum_shift (by linarith)]
  rw [realAnalyticEpstein_eq_row_sum z hs,
    show 2 * z.im ^ s * pSum (2 * s) + 2 * (∑' m : ℕ, f m) - 2 * z.im ^ (1 - s) * I *
        pSum (2 * s - 1) =
      2 * z.im ^ s * pSum (2 * s) + 2 * ((∑' m : ℕ, f m) - ∑' m : ℕ, g m) by rw [htsum_g]; ring]
  calc |2 * z.im ^ s * pSum (2 * s) + 2 * ((∑' m, f m) - ∑' m, g m)|
      ≤ |2 * z.im ^ s * pSum (2 * s)| + |2 * ((∑' m, f m) - ∑' m, g m)| := abs_add_le _ _
    _ = 2 * z.im ^ s * pSum (2 * s) + 2 * |(∑' m, f m) - ∑' m, g m| := by
        rw [abs_of_nonneg (mul_nonneg (by positivity) (tsum_nonneg fun _ ↦ by positivity)),
          abs_mul, abs_of_pos two_pos]
    _ ≤ (2 * z.im ^ s + 4 * z.im ^ (-s)) * pSum (2 * s) := by linarith

/-- **Residue of the lattice Epstein zeta function**: for every `z ∈ ℍ`,
`lim_{s → 1⁺} (s - 1) Z(z, s) = π`. -/
theorem tendsto_sub_one_mul_realAnalyticEpstein (z : ℍ) :
    Tendsto (fun s : ℝ ↦ (s - 1) * realAnalyticEpstein z s) (𝓝[>] 1) (𝓝 π) := by
  let M : ℝ → ℝ := fun s ↦
    z.im ^ (1 - s) * (∫ u : ℝ, (1 + u ^ 2) ^ (-s)) * (((2 * s - 1) - 1) * pSum (2 * s - 1))
  have hM : Tendsto M (𝓝[>] 1) (𝓝 π) := by
    have h1 : Tendsto (fun s : ℝ ↦ z.im ^ (1 - s)) (𝓝[>] 1) (𝓝 1) := by
      have hc : Continuous fun s : ℝ ↦ z.im ^ (1 - s) :=
        continuous_const.rpow (continuous_const.sub continuous_id) fun _ ↦ Or.inl z.im_ne_zero
      simpa using (hc.continuousAt (x := (1 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun s : ℝ ↦ 2 * s - 1) (𝓝[>] 1) (𝓝[>] 1) :=
      tendsto_nhdsWithin_iff.mpr
        ⟨by have h : Tendsto (fun s : ℝ ↦ 2 * s - 1) (𝓝[>] (1 : ℝ)) (𝓝 (2 * (1 : ℝ) - 1)) :=
              ((tendsto_id.mono_left nhdsWithin_le_nhds).const_mul 2).sub tendsto_const_nhds
            norm_num at h; exact h,
          by filter_upwards [self_mem_nhdsWithin] with s hs
             exact Set.mem_Ioi.mpr (by linarith [Set.mem_Ioi.mp hs])⟩
    simpa [M] using (h1.mul tendsto_integral_one_add_sq_rpow_neg).mul
      (tendsto_sub_one_mul_pSum.comp h2)
  have herr : Tendsto (fun s : ℝ ↦ (s - 1) * realAnalyticEpstein z s - M s) (𝓝[>] 1) (𝓝 0) := by
    refine squeeze_zero_norm'
      (a := fun s : ℝ ↦ (s - 1) * ((2 * z.im ^ s + 4 * z.im ^ (-s)) * 2)) ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with s hs
      have hs' : 1 < s := Set.mem_Ioi.mp hs
      rw [Real.norm_eq_abs, show (s - 1) * realAnalyticEpstein z s - M s =
          (s - 1) * (realAnalyticEpstein z s - 2 * z.im ^ (1 - s) *
            (∫ u : ℝ, (1 + u ^ 2) ^ (-s)) * pSum (2 * s - 1)) by simp only [M]; ring,
        abs_mul, abs_of_pos (sub_pos.mpr hs')]
      exact (mul_le_mul_of_nonneg_left (abs_realAnalyticEpstein_sub_le z hs')
        (sub_pos.mpr hs').le).trans
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (TauCeti.tsum_nat_rpow_neg_le_two (by linarith)) (by positivity)) (sub_pos.mpr hs').le)
    · have hc : Continuous fun s : ℝ ↦ (s - 1) * ((2 * z.im ^ s + 4 * z.im ^ (-s)) * 2) :=
        (continuous_id.sub continuous_const).mul (((continuous_const.mul
          (continuous_const.rpow continuous_id fun _ ↦ Or.inl z.im_ne_zero)).add
          (continuous_const.mul
            (continuous_const.rpow continuous_neg fun _ ↦ Or.inl z.im_ne_zero))).mul
          continuous_const)
      simpa using (hc.continuousAt (x := (1 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  simpa using herr.add hM

/-- **Uniform polynomial bound for `(s - 1) Z(z, s)`**: for `Im z ≥ 1 / 2` and `s ∈ (1, 2]`,
`(s - 1) Z(z, s) ≤ 6 π + 36 + 4 (Im z)²`. -/
theorem sub_one_mul_realAnalyticEpstein_le (z : ℍ) (hz : 1 / 2 ≤ z.im) {s : ℝ}
    (hs1 : 1 < s) (hs2 : s ≤ 2) :
    (s - 1) * realAnalyticEpstein z s ≤ 6 * π + 36 + 4 * z.im ^ 2 := by
  have hmain := (abs_le.mp (abs_realAnalyticEpstein_sub_le z hs1)).2
  have hneg_pow {a b : ℝ} (ha : a ≤ 0) (hab : b ≤ a) : z.im ^ a ≤ (1 / 2 : ℝ) ^ b :=
    (rpow_le_rpow_of_nonpos (by norm_num) hz ha).trans
      (rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hab)
  have hy_inv_s : z.im ^ (1 - s) ≤ 2 :=
    (hneg_pow (by linarith) (by linarith : -(1 : ℝ) ≤ 1 - s)).trans_eq (by norm_num)
  have hy_neg_s : z.im ^ (-s) ≤ 4 :=
    (hneg_pow (by linarith) (by linarith : -(2 : ℝ) ≤ -s)).trans_eq (by norm_num)
  have hy_s : z.im ^ s ≤ 1 + z.im ^ 2 := by
    rcases le_total z.im 1 with h | h
    · nlinarith [rpow_le_one z.im_pos.le h (by linarith : 0 ≤ s), sq_nonneg z.im]
    · have := rpow_le_rpow_of_exponent_le h hs2; rw [rpow_two] at this; linarith
  have hI : ∫ u : ℝ, (1 + u ^ 2) ^ (-s) ≤ π := integral_univ_inv_one_add_sq ▸
    integral_mono (integrable_one_add_sq_rpow_neg hs1.le) integrable_inv_one_add_sq
      (one_add_sq_rpow_neg_le hs1.le)
  have hzeta1 : (2 * s - 2) * pSum (2 * s - 1) ≤ 3 := by
    have hb := (pSum_bounds (r := 2 * s - 1) (by linarith)).2
    have hpos : 0 < 2 * s - 2 := by linarith
    rw [show (2 * s - 1) - 1 = 2 * s - 2 by ring] at hb
    exact (mul_le_mul_of_nonneg_left hb hpos.le).trans
      (by rw [mul_add, mul_one, mul_inv_cancel₀ hpos.ne']; linarith)
  have hterm1 : (s - 1) * (2 * z.im ^ (1 - s) * (∫ u : ℝ, (1 + u ^ 2) ^ (-s)) *
      pSum (2 * s - 1)) ≤ 6 * π := by
    rw [show (s - 1) * (2 * z.im ^ (1 - s) * (∫ u : ℝ, (1 + u ^ 2) ^ (-s)) * pSum (2 * s - 1)) =
        (z.im ^ (1 - s) * ∫ u : ℝ, (1 + u ^ 2) ^ (-s)) * ((2 * s - 2) * pSum (2 * s - 1)) by ring]
    exact (mul_le_mul (mul_le_mul hy_inv_s hI
      (integral_nonneg fun _ ↦ rpow_nonneg (by positivity) _) (by norm_num)) hzeta1
      (mul_nonneg (by linarith) (tsum_nonneg fun m ↦ rpow_nonneg (Nat.cast_nonneg m) _))
      (by positivity)).trans_eq (by ring)
  have hterm2 :
      (s - 1) * ((2 * z.im ^ s + 4 * z.im ^ (-s)) * pSum (2 * s)) ≤ 36 + 4 * z.im ^ 2 := by
    have hinner : (2 * z.im ^ s + 4 * z.im ^ (-s)) * pSum (2 * s) ≤
        (2 * (1 + z.im ^ 2) + 4 * 4) * 2 :=
      mul_le_mul (by linarith) (TauCeti.tsum_nat_rpow_neg_le_two (by linarith))
        (tsum_nonneg fun m ↦ rpow_nonneg (Nat.cast_nonneg m) _) (by positivity)
    exact (mul_le_mul (by linarith : s - 1 ≤ 1) hinner (mul_nonneg (by positivity)
      (tsum_nonneg fun m ↦ rpow_nonneg (Nat.cast_nonneg m) _)) zero_le_one).trans_eq (by ring)
  linarith [mul_le_mul_of_nonneg_left hmain (sub_pos.mpr hs1).le]

end TauCeti.EisensteinSeries
