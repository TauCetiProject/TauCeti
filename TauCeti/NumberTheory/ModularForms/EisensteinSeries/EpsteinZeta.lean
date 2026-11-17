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

For a point `z ∈ ℍ` and a real parameter `s > 1`, the **lattice Epstein zeta function** is
$$Z(z, s) = \sum_{(m, n) \in \mathbb{Z}^2 \setminus \{(0, 0)\}}
  \frac{(\operatorname{Im} z)^s}{|m z + n|^{2 s}}.$$

By unimodal sum-versus-integral comparison along each horizontal line `n ∈ ℤ` (for fixed `m ≥ 1`),
`Z(z, s)` satisfies the elementary estimate
$$\left|Z(z, s) - 2 (\operatorname{Im} z)^{1 - s} \zeta(2 s - 1)
    \int_{-\infty}^{\infty} (1 + u^2)^{-s}\,du\right|
  \le \left(2 (\operatorname{Im} z)^s + 4 (\operatorname{Im} z)^{-s}\right) \zeta(2 s).$$
This yields both the residue `lim_{s → 1⁺} (s - 1) Z(z, s) = π` (independent of `z`) and a
uniform polynomial-in-`Im z` bound `(s - 1) Z(z, s) ≤ 6 π + 36 + 4 (Im z)²` for `Im z ≥ 1 / 2`
and `s ∈ (1, 2]`.

## Main definitions

* `TauCeti.EisensteinSeries.realAnalyticEpstein`: the lattice Epstein zeta function `Z(z, s)`.

## Main results

* `TauCeti.EisensteinSeries.summable_realAnalyticEpstein_summand`: convergence of the lattice
  series for `s > 1`.
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

/-- Integral comparison lower bound for the real `p`-series: `(r - 1)⁻¹ ≤ ∑' n, n ^ (-r)`. -/
private theorem inv_sub_one_le_tsum_nat_rpow_neg {r : ℝ} (hr : 1 < r) :
    (r - 1)⁻¹ ≤ ∑' n : ℕ, (n : ℝ) ^ (-r) := by
  have hanti : AntitoneOn (fun t : ℝ ↦ t ^ (-r)) (Set.Ici (1 : ℕ)) := fun x hx _ _ hxy ↦
    rpow_le_rpow_of_nonpos (lt_of_lt_of_le zero_lt_one (by simpa using hx)) hxy (by linarith)
  have hsum : Summable fun n : ℕ ↦ (n : ℝ) ^ (-r) := Real.summable_nat_rpow.mpr (by linarith)
  have hint := hanti.integral_le_tsum_comp_add 1 hsum fun t ht ↦
    rpow_nonneg (lt_trans zero_lt_one (by simpa using ht)).le _
  rw [Nat.cast_one, integral_Ioi_rpow_of_lt (by linarith) zero_lt_one] at hint
  have heval : -(1 : ℝ) ^ (-r + 1) / (-r + 1) = (r - 1)⁻¹ := by
    rw [one_rpow, neg_div, ← div_neg, one_div]; congr 1; ring
  rw [heval] at hint
  refine hint.trans_eq ?_
  rw [hsum.tsum_eq_zero_add, Nat.cast_zero, zero_rpow (by linarith), zero_add]

/-- Integral comparison upper bound for the real `p`-series: `∑' n, n ^ (-r) ≤ 1 + (r - 1)⁻¹`. -/
private theorem tsum_nat_rpow_neg_le_one_add_inv_sub_one {r : ℝ} (hr : 1 < r) :
    ∑' n : ℕ, (n : ℝ) ^ (-r) ≤ 1 + (r - 1)⁻¹ := by
  have hanti : AntitoneOn (fun t : ℝ ↦ t ^ (-r)) (Set.Ici (1 : ℕ)) := fun x hx _ _ hxy ↦
    rpow_le_rpow_of_nonpos (lt_of_lt_of_le zero_lt_one (by simpa using hx)) hxy (by linarith)
  have hsum : Summable fun n : ℕ ↦ (n : ℝ) ^ (-r) := Real.summable_nat_rpow.mpr (by linarith)
  have htail := hanti.tsum_comp_add_le_integral 1
    (by simpa using integrableOn_Ioi_rpow_of_lt (by linarith : -r < -1) zero_lt_one)
    fun t ht ↦ rpow_nonneg (lt_trans zero_lt_one (by simpa using ht)).le _
  rw [Nat.cast_one, integral_Ioi_rpow_of_lt (by linarith) zero_lt_one] at htail
  have heval : -(1 : ℝ) ^ (-r + 1) / (-r + 1) = (r - 1)⁻¹ := by
    rw [one_rpow, neg_div, ← div_neg, one_div]; congr 1; ring
  rw [heval] at htail
  rw [hsum.tsum_eq_zero_add, Nat.cast_zero, zero_rpow (by linarith), zero_add,
    ((summable_nat_add_iff 1).mpr hsum).tsum_eq_zero_add]
  simp only [zero_add, Nat.cast_one, one_rpow]
  linarith

/-- The real `p`-series has residue `1` at `r = 1⁺`: `(r - 1) * ∑' n, n ^ (-r) → 1`. -/
private theorem tendsto_sub_one_mul_tsum_nat_rpow_neg :
    Tendsto (fun r : ℝ ↦ (r - 1) * ∑' n : ℕ, (n : ℝ) ^ (-r)) (𝓝[>] 1) (𝓝 1) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (show Tendsto (fun r : ℝ ↦ r) (𝓝[>] 1) (𝓝 1) from tendsto_nhdsWithin_of_tendsto_nhds tendsto_id)
    ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with r hr
    have hr' : 0 < r - 1 := sub_pos.mpr hr
    calc (1 : ℝ) = (r - 1) * (r - 1)⁻¹ := (mul_inv_cancel₀ hr'.ne').symm
      _ ≤ (r - 1) * ∑' n : ℕ, (n : ℝ) ^ (-r) :=
          mul_le_mul_of_nonneg_left (inv_sub_one_le_tsum_nat_rpow_neg hr) hr'.le
  · filter_upwards [self_mem_nhdsWithin] with r hr
    have hr' : 0 < r - 1 := sub_pos.mpr hr
    calc (r - 1) * ∑' n : ℕ, (n : ℝ) ^ (-r)
        ≤ (r - 1) * (1 + (r - 1)⁻¹) :=
          mul_le_mul_of_nonneg_left (tsum_nat_rpow_neg_le_one_add_inv_sub_one hr) hr'.le
      _ = r := by rw [mul_add, mul_one, mul_inv_cancel₀ hr'.ne']; ring

/-- Continuity of `u ↦ (1 + u ^ 2) ^ (-s)` on `ℝ`. -/
private theorem continuous_one_add_sq_rpow_neg (s : ℝ) :
    Continuous fun u : ℝ ↦ (1 + u ^ 2) ^ (-s) :=
  (continuous_const.add (continuous_pow 2)).rpow continuous_const fun u ↦
    Or.inl (by positivity : (0 : ℝ) < 1 + u ^ 2).ne'

/-- For `s ≥ 1`, `(1 + u ^ 2) ^ (-s)` is integrable on `ℝ` and bounded by `(1 + u ^ 2)⁻¹`. -/
private theorem integrable_one_add_sq_rpow_neg {s : ℝ} (hs : 1 ≤ s) :
    Integrable fun u : ℝ ↦ (1 + u ^ 2) ^ (-s) := by
  refine integrable_inv_one_add_sq.mono'
    (continuous_one_add_sq_rpow_neg s).aestronglyMeasurable (ae_of_all _ fun u ↦ ?_)
  have h1 : (1 : ℝ) ≤ 1 + u ^ 2 := le_add_of_nonneg_right (sq_nonneg u)
  rw [Real.norm_of_nonneg (rpow_nonneg (by positivity) _), ← rpow_neg_one]
  exact rpow_le_rpow_of_exponent_le h1 (by linarith)

/-- For `s ≥ 1`, `∫ u, (1 + u ^ 2) ^ (-s) ≤ π`. -/
private theorem integral_one_add_sq_rpow_neg_le_pi {s : ℝ} (hs : 1 ≤ s) :
    ∫ u : ℝ, (1 + u ^ 2) ^ (-s) ≤ π := by
  rw [← integral_univ_inv_one_add_sq]
  refine integral_mono (integrable_one_add_sq_rpow_neg hs) integrable_inv_one_add_sq fun u ↦ ?_
  have h1 : (1 : ℝ) ≤ 1 + u ^ 2 := le_add_of_nonneg_right (sq_nonneg u)
  rw [← rpow_neg_one]
  exact rpow_le_rpow_of_exponent_le h1 (by linarith)

/-- Dominated convergence gives `∫ u, (1 + u ^ 2) ^ (-s) → π` as `s → 1⁺`. -/
private theorem tendsto_integral_one_add_sq_rpow_neg :
    Tendsto (fun s : ℝ ↦ ∫ u : ℝ, (1 + u ^ 2) ^ (-s)) (𝓝[>] 1) (𝓝 π) := by
  rw [← integral_univ_inv_one_add_sq]
  refine tendsto_integral_filter_of_dominated_convergence (fun u : ℝ ↦ (1 + u ^ 2)⁻¹)
    (Eventually.of_forall fun s ↦ (continuous_one_add_sq_rpow_neg s).aestronglyMeasurable)
    ?_ integrable_inv_one_add_sq ?_
  · filter_upwards [self_mem_nhdsWithin] with s hs
    refine ae_of_all _ fun u ↦ ?_
    have h1 : (1 : ℝ) ≤ 1 + u ^ 2 := le_add_of_nonneg_right (sq_nonneg u)
    rw [Real.norm_of_nonneg (rpow_nonneg (by positivity) _), ← rpow_neg_one]
    exact rpow_le_rpow_of_exponent_le h1 (by linarith [Set.mem_Ioi.mp hs])
  · refine ae_of_all _ fun u ↦ ?_
    have hpos : 0 < 1 + u ^ 2 := by positivity
    have hcont : Continuous fun s : ℝ ↦ (1 + u ^ 2) ^ (-s) :=
      continuous_const.rpow continuous_neg fun _ ↦ Or.inl hpos.ne'
    simpa [rpow_neg_one] using
      (hcont.continuousAt (x := (1 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds

/-- Affine change of variables evaluating `∫ t, ((t + a) ^ 2 + b ^ 2) ^ (-s)`. -/
private theorem integral_add_sq_add_sq_rpow_neg (a : ℝ) {b s : ℝ} (hb : 0 < b) :
    ∫ t : ℝ, ((t + a) ^ 2 + b ^ 2) ^ (-s) = b ^ (1 - 2 * s) * ∫ u : ℝ, (1 + u ^ 2) ^ (-s) := by
  have h1 : ∫ t : ℝ, ((t + a) ^ 2 + b ^ 2) ^ (-s) = ∫ t : ℝ, (t ^ 2 + b ^ 2) ^ (-s) :=
    integral_add_right_eq_self (fun t : ℝ ↦ (t ^ 2 + b ^ 2) ^ (-s)) a
  rw [h1]
  have hscale := Measure.integral_comp_mul_left (fun t : ℝ ↦ (t ^ 2 + b ^ 2) ^ (-s)) b
  rw [abs_inv, abs_of_pos hb, smul_eq_mul] at hscale
  have hscale' : ∫ t : ℝ, (t ^ 2 + b ^ 2) ^ (-s) = b * ∫ x : ℝ, ((b * x) ^ 2 + b ^ 2) ^ (-s) := by
    rw [hscale, ← mul_assoc, mul_inv_cancel₀ hb.ne', one_mul]
  rw [hscale', ← integral_const_mul, ← integral_const_mul]
  congr 1; ext u
  have hfac : (b * u) ^ 2 + b ^ 2 = b ^ 2 * (1 + u ^ 2) := by ring
  rw [hfac, mul_rpow (sq_nonneg b) (by positivity), ← rpow_natCast b 2,
    ← rpow_mul hb.le, ← mul_assoc, mul_comm b, ← rpow_add_one hb.ne']
  congr 2; push_cast; ring

/-- Integrability of `t ↦ ((t + a) ^ 2 + b ^ 2) ^ (-s)` on `ℝ` for `s ≥ 1` and `b > 0`. -/
private theorem integrable_add_sq_add_sq_rpow_neg (a : ℝ) {b s : ℝ} (hb : 0 < b) (hs : 1 ≤ s) :
    Integrable fun t : ℝ ↦ ((t + a) ^ 2 + b ^ 2) ^ (-s) := by
  have h0 : Integrable fun u : ℝ ↦ b ^ (-2 * s) * (1 + u ^ 2) ^ (-s) :=
    (integrable_one_add_sq_rpow_neg hs).const_mul _
  have h1 : Integrable fun t : ℝ ↦ b ^ (-2 * s) * (1 + (b⁻¹ * (t + a)) ^ 2) ^ (-s) :=
    (h0.comp_mul_left' (inv_ne_zero hb.ne')).comp_add_right a
  refine h1.congr (ae_of_all _ fun t ↦ ?_)
  dsimp only
  have hfac : (t + a) ^ 2 + b ^ 2 = b ^ 2 * (1 + (b⁻¹ * (t + a)) ^ 2) := by
    field_simp [hb.ne']; ring
  rw [hfac, mul_rpow (sq_nonneg b) (by positivity), ← rpow_natCast b 2, ← rpow_mul hb.le]
  congr 2; push_cast; ring

/-- Split an integer sum `∑' n : ℤ, φ n` at a cutoff `k : ℤ` into its right (`k + 1 + n`) and
left (`k - n`) tails. -/
private theorem tsum_int_split_at (φ : ℝ → ℝ) (k : ℤ)
    (hR : Summable fun n : ℕ ↦ φ ((k : ℝ) + 1 + n))
    (hL : Summable fun n : ℕ ↦ φ ((k : ℝ) - n)) :
    ∑' n : ℤ, φ n = (∑' n : ℕ, φ ((k : ℝ) + 1 + n)) + ∑' n : ℕ, φ ((k : ℝ) - n) := by
  let S : Set ℤ := {n : ℤ | k < n}
  let eR : ℕ ≃ S :=
    { toFun := fun n ↦ ⟨k + 1 + (n : ℤ), by change k < k + 1 + (n : ℤ); omega⟩
      invFun := fun m ↦ (m.1 - (k + 1)).toNat
      left_inv := fun n ↦ by simp
      right_inv := fun m ↦ Subtype.ext (by dsimp only; have hm : k < m.1 := m.2; omega) }
  let eL : ℕ ≃ (Sᶜ : Set ℤ) :=
    { toFun := fun n ↦ ⟨k - (n : ℤ), by change ¬ k < k - (n : ℤ); omega⟩
      invFun := fun m ↦ (k - m.1).toNat
      left_inv := fun n ↦ by simp
      right_inv := fun m ↦ Subtype.ext (by dsimp only; have hm : ¬ k < m.1 := m.2; omega) }
  have hsum_R : Summable (fun m : S ↦ φ (m.1 : ℝ)) :=
    eR.summable_iff.mp (hR.congr fun n ↦ by simp [eR])
  have hsum_L : Summable (fun m : (Sᶜ : Set ℤ) ↦ φ (m.1 : ℝ)) :=
    eL.summable_iff.mp (hL.congr fun n ↦ by simp [eL])
  rw [← hsum_R.tsum_add_tsum_compl hsum_L, ← eR.tsum_eq, ← eL.tsum_eq]
  congr 1 <;> exact tsum_congr fun n ↦ by simp [eR, eL]

/-- Split `∫ t : ℝ, φ t` into `Iio c`, `Icc c (c + 1)`, and `Ioi (c + 1)`. -/
private theorem integral_split_Iio_Icc_Ioi {φ : ℝ → ℝ} (hφ : Integrable φ) (c : ℝ) :
    ∫ t : ℝ, φ t =
      (∫ t in Set.Iio c, φ t) + (∫ t in Set.Icc c (c + 1), φ t) +
        ∫ t in Set.Ioi (c + 1), φ t := by
  have h1 : ∫ t : ℝ, φ t = (∫ t in Set.Iic (c + 1), φ t) + ∫ t in Set.Ioi (c + 1), φ t := by
    rw [← setIntegral_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
      hφ.integrableOn hφ.integrableOn, Set.Iic_union_Ioi, setIntegral_univ]
  have h2 : ∫ t in Set.Iic (c + 1), φ t =
      (∫ t in Set.Iio c, φ t) + ∫ t in Set.Icc c (c + 1), φ t := by
    rw [← setIntegral_union ((Set.Iio_disjoint_Ici le_rfl).mono_right Set.Icc_subset_Ici_self)
      measurableSet_Icc hφ.integrableOn hφ.integrableOn, Set.Iio_union_Icc_eq_Iic (by linarith)]
  rw [h1, h2]

/-- Shift `∫ u in Ioi 0, φ (c + u)` and `∫ u in Ioi 0, φ (c - u)` to `Ioi c` and `Iio c`. -/
private theorem setIntegral_Ioi_add_and_sub (φ : ℝ → ℝ) (c : ℝ) :
    (∫ u in Set.Ioi (0 : ℝ), φ (c + u)) = ∫ t in Set.Ioi c, φ t ∧
      (∫ u in Set.Ioi (0 : ℝ), φ (c - u)) = ∫ t in Set.Iio c, φ t := by
  constructor
  · have himg : (c + ·) '' Set.Ioi (0 : ℝ) = Set.Ioi c := by
      ext t; simp only [Set.mem_image, Set.mem_Ioi]; constructor
      · rintro ⟨u, hu, rfl⟩; linarith
      · intro ht; exact ⟨t - c, by linarith, by ring⟩
    rw [← himg, (MeasureTheory.measurePreserving_add_left volume c).setIntegral_image_emb
      (measurableEmbedding_addLeft _)]
  · have himg : (c - ·) '' Set.Ioi (0 : ℝ) = Set.Iio c := by
      ext t; simp only [Set.mem_image, Set.mem_Ioi, Set.mem_Iio]; constructor
      · rintro ⟨u, hu, rfl⟩; linarith
      · intro ht; exact ⟨c - t, by linarith, by ring⟩
    rw [← himg, (volume.measurePreserving_sub_left c).setIntegral_image_emb
      (measurableEmbedding_subLeft _)]

/-- Unimodal sum-versus-integral comparison on `ℤ`:
`|∑' n : ℤ, ((n + a)² + b²) ^ (-s) - ∫ t, ((t + a)² + b²) ^ (-s)| ≤ 2 * b ^ (-2 * s)`. -/
private theorem abs_tsum_int_add_sq_add_sq_rpow_neg_sub_integral_le (a : ℝ) {b s : ℝ}
    (hb : 0 < b) (hs : 1 ≤ s) :
    |(∑' n : ℤ, (((n : ℝ) + a) ^ 2 + b ^ 2) ^ (-s)) - ∫ t : ℝ, ((t + a) ^ 2 + b ^ 2) ^ (-s)| ≤
      2 * b ^ (-2 * s) := by
  let φ : ℝ → ℝ := fun t ↦ ((t + a) ^ 2 + b ^ 2) ^ (-s)
  let k : ℤ := ⌊-a⌋
  have hk_le : (k : ℝ) ≤ -a := Int.floor_le (-a)
  have hk_lt : -a < (k : ℝ) + 1 := Int.lt_floor_add_one (-a)
  have hφ_nn : ∀ t, 0 ≤ φ t := fun t ↦ rpow_nonneg (by positivity) _
  have hφ_le : ∀ t, φ t ≤ b ^ (-2 * s) := fun t ↦ by
    calc φ t ≤ (b ^ 2) ^ (-s) :=
          rpow_le_rpow_of_nonpos (sq_pos_of_pos hb)
            (le_add_of_nonneg_left (sq_nonneg _)) (by linarith)
      _ = b ^ (-2 * s) := by rw [← rpow_natCast b 2, ← rpow_mul hb.le]; congr 1; push_cast; ring
  have hφ_int : Integrable φ := integrable_add_sq_add_sq_rpow_neg a hb hs
  let fR : ℝ → ℝ := fun u ↦ φ ((k : ℝ) + 1 + u)
  let fL : ℝ → ℝ := fun u ↦ φ ((k : ℝ) - u)
  have hfR_anti : AntitoneOn fR (Set.Ici 0) := fun u hu _ _ huv ↦ by
    have h0 : 0 ≤ (k : ℝ) + 1 + u + a := by linarith [Set.mem_Ici.mp hu]
    exact rpow_le_rpow_of_nonpos (by positivity) (by nlinarith) (by linarith)
  have hfL_anti : AntitoneOn fL (Set.Ici 0) := fun u hu _ _ huv ↦ by
    have h0 : (k : ℝ) - u + a ≤ 0 := by linarith [Set.mem_Ici.mp hu]
    exact rpow_le_rpow_of_nonpos (by positivity) (by nlinarith) (by linarith)
  have hfR_int : IntegrableOn fR (Set.Ioi 0) := (hφ_int.comp_add_left ((k : ℝ) + 1)).integrableOn
  have hfL_int : IntegrableOn fL (Set.Ioi 0) := (hφ_int.comp_sub_left (k : ℝ)).integrableOn
  have hfR_sum : Summable fun n : ℕ ↦ fR n :=
    hfR_anti.summable_of_integrableOn_Ioi_zero hfR_int fun _ _ ↦ hφ_nn _
  have hfL_sum : Summable fun n : ℕ ↦ fL n :=
    hfL_anti.summable_of_integrableOn_Ioi_zero hfL_int fun _ _ ↦ hφ_nn _
  have hsum_split : ∑' n : ℤ, φ n = (∑' n : ℕ, fR n) + ∑' n : ℕ, fL n :=
    tsum_int_split_at φ k hfR_sum hfL_sum
  have hI_R : ∫ u in Set.Ioi (0 : ℝ), fR u = ∫ t in Set.Ioi ((k : ℝ) + 1), φ t :=
    (setIntegral_Ioi_add_and_sub φ ((k : ℝ) + 1)).1
  have hI_L : ∫ u in Set.Ioi (0 : ℝ), fL u = ∫ t in Set.Iio (k : ℝ), φ t :=
    (setIntegral_Ioi_add_and_sub φ (k : ℝ)).2
  have hI_split := integral_split_Iio_Icc_Ioi hφ_int (k : ℝ)
  have hI_mid_nn : 0 ≤ ∫ t in Set.Icc (k : ℝ) ((k : ℝ) + 1), φ t :=
    setIntegral_nonneg measurableSet_Icc fun t _ ↦ hφ_nn t
  have hI_mid_le : ∫ t in Set.Icc (k : ℝ) ((k : ℝ) + 1), φ t ≤ b ^ (-2 * s) := by
    calc ∫ t in Set.Icc (k : ℝ) ((k : ℝ) + 1), φ t
        ≤ ∫ _ in Set.Icc (k : ℝ) ((k : ℝ) + 1), b ^ (-2 * s) :=
          setIntegral_mono_on hφ_int.integrableOn (integrableOn_const (by simp))
            measurableSet_Icc fun t _ ↦ hφ_le t
      _ = b ^ (-2 * s) := by simp
  have hR_le := hfR_anti.tsum_le_integral hfR_int fun _ _ ↦ hφ_nn _
  have hR_ge := hfR_anti.integral_le_tsum hfR_sum fun _ _ ↦ hφ_nn _
  have hL_le := hfL_anti.tsum_le_integral hfL_int fun _ _ ↦ hφ_nn _
  have hL_ge := hfL_anti.integral_le_tsum hfL_sum fun _ _ ↦ hφ_nn _
  have hfR0 : fR 0 ≤ b ^ (-2 * s) := hφ_le _
  have hfL0 : fL 0 ≤ b ^ (-2 * s) := hφ_le _
  rw [abs_le]; constructor <;> linarith

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
  have hO := _root_.EisensteinSeries.isBigO_linear_add_const_vec z 0 0
  obtain ⟨C, hCpos, hC⟩ := hO.exists_pos
  rw [Asymptotics.isBigOWith_iff] at hC
  rw [Asymptotics.isBigO_iff]
  refine ⟨z.im ^ s * C ^ (2 * s), ?_⟩
  filter_upwards [hC] with m hm
  simp only [Function.comp_apply, finTwoArrowEquiv_apply]
  split_ifs with h0
  · simp only [norm_zero]; positivity
  · simp only [Int.cast_zero, add_zero, norm_inv, norm_norm] at hm
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity),
      div_eq_mul_inv, ← inv_rpow (norm_nonneg _), mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (rpow_nonneg z.im_pos.le s)
    calc (‖(m 0 : ℂ) * z + m 1‖⁻¹) ^ (2 * s)
        ≤ (C * ‖m‖⁻¹) ^ (2 * s) := rpow_le_rpow (by positivity) hm (by linarith)
      _ = C ^ (2 * s) * (‖m‖ ^ (2 * s))⁻¹ := by
          rw [mul_rpow hCpos.le (by positivity), inv_rpow (norm_nonneg m)]

/-- Rewrite `z.im ^ s / ‖m z + n‖ ^ (2 * s)` in Cartesian coordinates `(n + m x)² + (m y)²`. -/
private theorem norm_int_mul_coe_add_int_rpow (z : ℍ) (m n : ℤ) (s : ℝ) :
    z.im ^ s / ‖(m : ℂ) * z + n‖ ^ (2 * s) =
      z.im ^ s * (((n : ℝ) + (m : ℝ) * z.re) ^ 2 + ((m : ℝ) * z.im) ^ 2) ^ (-s) := by
  rw [div_eq_mul_inv, ← rpow_neg (norm_nonneg _)]
  congr 1
  have hsq : ‖(m : ℂ) * z + n‖ ^ 2 = ((n : ℝ) + (m : ℝ) * z.re) ^ 2 + ((m : ℝ) * z.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [coe_re, coe_im]; ring
  rw [← hsq, ← rpow_natCast ‖(m : ℂ) * z + n‖ 2, ← rpow_mul (norm_nonneg _)]
  congr 1; push_cast; ring

/-- The `m = 0` row of `realAnalyticEpstein` equals `2 y^s ζ(2s)`. -/
private theorem realAnalyticEpstein_row_zero (z : ℍ) {s : ℝ} (hs : 1 < s)
    (hrow0 : Summable fun n : ℤ ↦
      if ((0 : ℤ), n) = (0, 0) then 0 else z.im ^ s / ‖((0 : ℤ) : ℂ) * z + n‖ ^ (2 * s)) :
    (∑' n : ℤ, if ((0 : ℤ), n) = (0, 0) then 0 else
        z.im ^ s / ‖((0 : ℤ) : ℂ) * z + n‖ ^ (2 * s)) =
      2 * z.im ^ s * ∑' n : ℕ, (n : ℝ) ^ (-(2 * s)) := by
  let g : ℤ → ℝ := fun n ↦
    if ((0 : ℤ), n) = (0, 0) then 0 else z.im ^ s / ‖((0 : ℤ) : ℂ) * z + n‖ ^ (2 * s)
  have h1 : Summable fun n : ℕ ↦ g (n : ℤ) := hrow0.comp_injective Nat.cast_injective
  have h2 : Summable fun n : ℕ ↦ g (-((n : ℤ) + 1)) :=
    hrow0.comp_injective fun _ _ h ↦ by omega
  have hpos (n : ℕ) : g (((n + 1 : ℕ) : ℤ)) = z.im ^ s * ((n + 1 : ℕ) : ℝ) ^ (-(2 * s)) := by
    have hne : ((0 : ℤ), ((n + 1 : ℕ) : ℤ)) ≠ (0, 0) := by simp; omega
    simp only [g, hne, ↓reduceIte, Int.cast_zero, zero_mul, zero_add, div_eq_mul_inv,
      ← rpow_neg (norm_nonneg _), Int.cast_natCast, Complex.norm_natCast]
  have hneg (n : ℕ) : g (-((n : ℤ) + 1)) = z.im ^ s * ((n + 1 : ℕ) : ℝ) ^ (-(2 * s)) := by
    have hne : ((0 : ℤ), -((n : ℤ) + 1)) ≠ (0, 0) := by simp; omega
    simp only [g, hne, ↓reduceIte, Int.cast_zero, zero_mul, zero_add, div_eq_mul_inv,
      ← rpow_neg (norm_nonneg _), Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one,
      norm_neg]
    congr 2
    rw [show ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
  have hsum_nat : Summable fun n : ℕ ↦ (n : ℝ) ^ (-(2 * s)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  change ∑' n : ℤ, g n = _
  rw [tsum_of_nat_of_neg_add_one h1 h2, h1.tsum_eq_zero_add]
  have hg0 : g ((0 : ℕ) : ℤ) = 0 := by simp [g]
  rw [hg0, zero_add, tsum_congr hpos, tsum_congr hneg, tsum_mul_left,
    hsum_nat.tsum_eq_zero_add, Nat.cast_zero, zero_rpow (by linarith : -(2 * s) ≠ 0), zero_add]
  ring

/-- Summing `realAnalyticEpstein` by rows `m ∈ ℤ`: the `m = 0` row is `2 y^s ζ(2s)`, and the
`m ≠ 0` rows pair `±m` to give twice the sum over `m ≥ 1`. -/
private theorem realAnalyticEpstein_eq_row_sum (z : ℍ) {s : ℝ} (hs : 1 < s) :
    realAnalyticEpstein z s =
      2 * z.im ^ s * (∑' n : ℕ, (n : ℝ) ^ (-(2 * s))) +
        2 * ∑' m : ℕ, if m = 0 then 0 else
          ∑' n : ℤ, z.im ^ s * (((n : ℝ) + (m : ℝ) * z.re) ^ 2 + ((m : ℝ) * z.im) ^ 2) ^ (-s) := by
  let F : ℤ → ℤ → ℝ := fun m n ↦
    if (m, n) = (0, 0) then 0 else z.im ^ s / ‖(m : ℂ) * z + n‖ ^ (2 * s)
  have hEq : (fun p : ℤ × ℤ ↦ if p = 0 then 0 else z.im ^ s / ‖(p.1 : ℂ) * z + p.2‖ ^ (2 * s)) =
      Function.uncurry F := funext fun ⟨_, _⟩ ↦ rfl
  have hF : Summable (Function.uncurry F) := hEq ▸ summable_realAnalyticEpstein_summand z hs
  have hrow (m : ℤ) : Summable (F m) := hF.prod_factor m
  have houter : Summable fun m : ℤ ↦ ∑' n : ℤ, F m n :=
    (hF.hasSum.prod_fiberwise fun m ↦ (hrow m).hasSum).summable
  have hneg (m : ℤ) : ∑' n : ℤ, F (-m) n = ∑' n : ℤ, F m n := by
    rw [← (Equiv.neg ℤ).tsum_eq]
    refine tsum_congr fun n ↦ ?_
    simp only [Equiv.neg_apply, F]
    by_cases h0 : (m, n) = (0, 0)
    · have h0' : (-m, -n) = (0, 0) := by simpa [Prod.mk.injEq, neg_eq_zero] using h0
      simp [h0, h0']
    · have h0' : (-m, -n) ≠ (0, 0) := fun h ↦ h0 (by simpa [Prod.mk.injEq, neg_eq_zero] using h)
      simp only [h0, h0', ↓reduceIte]
      congr 2
      have hlin : ((-m : ℤ) : ℂ) * z + (-n : ℤ) = -((m : ℂ) * z + n) := by push_cast; ring
      rw [hlin, norm_neg]
  have ho1 : Summable fun m : ℕ ↦ ∑' n : ℤ, F (m : ℤ) n :=
    houter.comp_injective Nat.cast_injective
  have ho2 : Summable fun m : ℕ ↦ ∑' n : ℤ, F (-((m : ℤ) + 1)) n :=
    houter.comp_injective fun _ _ h ↦ by omega
  have houter_nat : Summable fun m : ℕ ↦ if m = 0 then 0 else ∑' n : ℤ, F m n := by
    refine ((summable_nat_add_iff 1).mp ?_).congr fun _ ↦ rfl
    exact (houter.comp_injective (fun _ _ h ↦ Nat.succ.inj (Int.ofNat.inj h) :
      Function.Injective fun m : ℕ ↦ ((m + 1 : ℕ) : ℤ))).congr fun m ↦ by simp
  rw [realAnalyticEpstein_def, hEq, hF.tsum_prod' hrow]
  simp only [Function.uncurry_apply_pair]
  rw [tsum_of_nat_of_neg_add_one ho1 ho2, ho1.tsum_eq_zero_add, Nat.cast_zero,
    realAnalyticEpstein_row_zero z hs (hrow 0), add_assoc]
  congr 1
  have hpair : ∑' m : ℕ, ∑' n : ℤ, F (-((m : ℤ) + 1)) n =
      ∑' m : ℕ, ∑' n : ℤ, F (((m + 1 : ℕ) : ℤ)) n :=
    tsum_congr fun m ↦ by simpa [Nat.cast_add, Nat.cast_one] using hneg ((m : ℤ) + 1)
  rw [hpair, ← two_mul]
  congr 1
  have hterm (m : ℕ) :
      (if m = 0 then 0 else ∑' n : ℤ, F m n) =
        if m = 0 then 0 else
          ∑' n : ℤ, z.im ^ s * (((n : ℝ) + (m : ℝ) * z.re) ^ 2 + ((m : ℝ) * z.im) ^ 2) ^ (-s) := by
    by_cases hm : m = 0
    · simp [hm]
    · simp only [hm, ↓reduceIte]
      refine tsum_congr fun n ↦ ?_
      have hne : ((m : ℤ), n) ≠ (0, 0) := by simp [hm]
      simp only [F, hne, ↓reduceIte, norm_int_mul_coe_add_int_rpow, Int.cast_natCast]
  rw [← tsum_congr hterm, houter_nat.tsum_eq_zero_add]
  simp only [↓reduceIte, zero_add]
  refine tsum_congr fun m ↦ ?_
  simp only [Nat.succ_ne_zero, ↓reduceIte]

/-- Row-wise comparison between the `m`-th row of `Z(z, s)` and its integral approximation. -/
private theorem abs_row_sub_approx_le (z : ℍ) {s : ℝ} (hs : 1 < s) (m : ℕ) :
    |(if m = 0 then 0 else
        ∑' n : ℤ, z.im ^ s * (((n : ℝ) + (m : ℝ) * z.re) ^ 2 + ((m : ℝ) * z.im) ^ 2) ^ (-s)) -
        z.im ^ (1 - s) * (∫ u : ℝ, (1 + u ^ 2) ^ (-s)) * (m : ℝ) ^ (-(2 * s - 1))| ≤
      2 * z.im ^ (-s) * (m : ℝ) ^ (-(2 * s)) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [↓reduceIte, Nat.cast_zero, zero_rpow (by linarith : -(2 * s - 1) ≠ 0),
      mul_zero, sub_self, abs_zero]
    positivity
  · have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
    have hb : 0 < (m : ℝ) * z.im := mul_pos hm' z.im_pos
    have hterm := abs_tsum_int_add_sq_add_sq_rpow_neg_sub_integral_le ((m : ℝ) * z.re) hb hs.le
    rw [integral_add_sq_add_sq_rpow_neg _ hb] at hterm
    have hmul := mul_le_mul_of_nonneg_left hterm (rpow_nonneg z.im_pos.le s)
    conv_lhs at hmul => rw [← abs_of_nonneg (rpow_nonneg z.im_pos.le s), ← abs_mul, mul_sub]
    have hf_eq : z.im ^ s *
        ∑' n : ℤ, (((n : ℝ) + (m : ℝ) * z.re) ^ 2 + ((m : ℝ) * z.im) ^ 2) ^ (-s) =
        if m = 0 then 0 else
          ∑' n : ℤ, z.im ^ s * (((n : ℝ) + (m : ℝ) * z.re) ^ 2 + ((m : ℝ) * z.im) ^ 2) ^ (-s) := by
      simp only [hm.ne', ↓reduceIte, tsum_mul_left]
    have hg_eq : z.im ^ s * (((m : ℝ) * z.im) ^ (1 - 2 * s) * ∫ u : ℝ, (1 + u ^ 2) ^ (-s)) =
        z.im ^ (1 - s) * (∫ u : ℝ, (1 + u ^ 2) ^ (-s)) * (m : ℝ) ^ (-(2 * s - 1)) := by
      rw [mul_rpow hm'.le z.im_pos.le,
        show z.im ^ s * ((m : ℝ) ^ (1 - 2 * s) * z.im ^ (1 - 2 * s) *
            ∫ u : ℝ, (1 + u ^ 2) ^ (-s)) =
          (z.im ^ s * z.im ^ (1 - 2 * s)) * (∫ u : ℝ, (1 + u ^ 2) ^ (-s)) *
            (m : ℝ) ^ (1 - 2 * s) by ring,
        ← rpow_add z.im_pos]
      congr 1
      · congr 2; ring
      · congr 1; ring
    have herr_eq : z.im ^ s * (2 * ((m : ℝ) * z.im) ^ (-2 * s)) =
        2 * z.im ^ (-s) * (m : ℝ) ^ (-(2 * s)) := by
      rw [mul_rpow hm'.le z.im_pos.le,
        show z.im ^ s * (2 * ((m : ℝ) ^ (-2 * s) * z.im ^ (-2 * s))) =
          2 * (z.im ^ s * z.im ^ (-2 * s)) * (m : ℝ) ^ (-2 * s) by ring,
        ← rpow_add z.im_pos]
      congr 1
      · congr 2; ring
      · congr 1; ring
    rwa [hf_eq, hg_eq, herr_eq] at hmul

/-- **Key elementary estimate for the lattice Epstein zeta function**: for `z ∈ ℍ` and `s > 1`,
`|Z(z, s) - 2 y^{1 - s} I(s) ζ(2s - 1)| ≤ (2 y^s + 4 y^{-s}) ζ(2s)`. -/
private theorem abs_realAnalyticEpstein_sub_le (z : ℍ) {s : ℝ} (hs : 1 < s) :
    |realAnalyticEpstein z s -
        2 * z.im ^ (1 - s) * (∫ u : ℝ, (1 + u ^ 2) ^ (-s)) *
          (∑' m : ℕ, (m : ℝ) ^ (-(2 * s - 1)))| ≤
      (2 * z.im ^ s + 4 * z.im ^ (-s)) * (∑' m : ℕ, (m : ℝ) ^ (-(2 * s))) := by
  let I : ℝ := ∫ u : ℝ, (1 + u ^ 2) ^ (-s)
  let f : ℕ → ℝ := fun m ↦ if m = 0 then 0 else
    ∑' n : ℤ, z.im ^ s * (((n : ℝ) + (m : ℝ) * z.re) ^ 2 + ((m : ℝ) * z.im) ^ 2) ^ (-s)
  let g : ℕ → ℝ := fun m ↦ z.im ^ (1 - s) * I * (m : ℝ) ^ (-(2 * s - 1))
  have hsum_g : Summable g := (Real.summable_nat_rpow.mpr (by linarith)).mul_left _
  have hsum_err : Summable fun m : ℕ ↦ 2 * z.im ^ (-s) * (m : ℝ) ^ (-(2 * s)) :=
    (Real.summable_nat_rpow.mpr (by linarith)).mul_left _
  have hdiff_le : ∀ m : ℕ, |f m - g m| ≤ 2 * z.im ^ (-s) * (m : ℝ) ^ (-(2 * s)) :=
    abs_row_sub_approx_le z hs
  have hsum_diff : Summable fun m : ℕ ↦ f m - g m :=
    Summable.of_norm_bounded hsum_err fun m ↦ by simpa only [Real.norm_eq_abs] using hdiff_le m
  have hsum_f : Summable f := by simpa only [sub_add_cancel] using hsum_diff.add hsum_g
  have htsum_diff : |(∑' m : ℕ, f m) - ∑' m : ℕ, g m| ≤
      2 * z.im ^ (-s) * ∑' m : ℕ, (m : ℝ) ^ (-(2 * s)) := by
    rw [← hsum_f.tsum_sub hsum_g, ← tsum_mul_left]
    calc |∑' m : ℕ, (f m - g m)|
        ≤ ∑' m : ℕ, |f m - g m| := by
          simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hsum_diff.norm
      _ ≤ ∑' m : ℕ, 2 * z.im ^ (-s) * (m : ℝ) ^ (-(2 * s)) :=
          Summable.tsum_le_tsum hdiff_le hsum_diff.abs hsum_err
  rw [realAnalyticEpstein_eq_row_sum z hs]
  have htsum_g : ∑' m : ℕ, g m = z.im ^ (1 - s) * I * ∑' m : ℕ, (m : ℝ) ^ (-(2 * s - 1)) :=
    tsum_mul_left
  have hrearr :
      2 * z.im ^ s * (∑' n : ℕ, (n : ℝ) ^ (-(2 * s))) + 2 * (∑' m : ℕ, f m) -
        2 * z.im ^ (1 - s) * I * (∑' m : ℕ, (m : ℝ) ^ (-(2 * s - 1))) =
      2 * z.im ^ s * (∑' n : ℕ, (n : ℝ) ^ (-(2 * s))) + 2 * ((∑' m : ℕ, f m) - ∑' m : ℕ, g m) := by
    rw [htsum_g]; ring
  rw [hrearr]
  calc |2 * z.im ^ s * (∑' n : ℕ, (n : ℝ) ^ (-(2 * s))) +
          2 * ((∑' m : ℕ, f m) - ∑' m : ℕ, g m)|
      ≤ |2 * z.im ^ s * (∑' n : ℕ, (n : ℝ) ^ (-(2 * s)))| +
          |2 * ((∑' m : ℕ, f m) - ∑' m : ℕ, g m)| := abs_add_le _ _
    _ = 2 * z.im ^ s * (∑' n : ℕ, (n : ℝ) ^ (-(2 * s))) +
          2 * |(∑' m : ℕ, f m) - ∑' m : ℕ, g m| := by
        rw [abs_of_nonneg (by positivity), abs_mul, abs_of_pos two_pos]
    _ ≤ 2 * z.im ^ s * (∑' n : ℕ, (n : ℝ) ^ (-(2 * s))) +
          2 * (2 * z.im ^ (-s) * ∑' m : ℕ, (m : ℝ) ^ (-(2 * s))) := by linarith
    _ = (2 * z.im ^ s + 4 * z.im ^ (-s)) * ∑' m : ℕ, (m : ℝ) ^ (-(2 * s)) := by ring

/-- **Residue of the lattice Epstein zeta function**: for every `z ∈ ℍ`,
`lim_{s → 1⁺} (s - 1) Z(z, s) = π`. -/
theorem tendsto_sub_one_mul_realAnalyticEpstein (z : ℍ) :
    Tendsto (fun s : ℝ ↦ (s - 1) * realAnalyticEpstein z s) (𝓝[>] 1) (𝓝 π) := by
  let M : ℝ → ℝ := fun s ↦
    z.im ^ (1 - s) * (∫ u : ℝ, (1 + u ^ 2) ^ (-s)) *
      (((2 * s - 1) - 1) * ∑' m : ℕ, (m : ℝ) ^ (-(2 * s - 1)))
  have hM : Tendsto M (𝓝[>] 1) (𝓝 π) := by
    have h1 : Tendsto (fun s : ℝ ↦ z.im ^ (1 - s)) (𝓝[>] 1) (𝓝 1) := by
      have hcont : Continuous fun s : ℝ ↦ z.im ^ (1 - s) :=
        continuous_const.rpow (continuous_const.sub continuous_id) fun _ ↦ Or.inl z.im_ne_zero
      simpa using (hcont.continuousAt (x := (1 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun s : ℝ ↦ 2 * s - 1) (𝓝[>] 1) (𝓝[>] 1) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have hcont : Continuous fun s : ℝ ↦ 2 * s - 1 :=
          (continuous_const.mul continuous_id).sub continuous_const
        convert (hcont.continuousAt (x := (1 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
        norm_num
      · filter_upwards [self_mem_nhdsWithin] with s hs; simp only [Set.mem_Ioi] at hs ⊢; linarith
    have h3 : Tendsto (fun s : ℝ ↦ ((2 * s - 1) - 1) * ∑' m : ℕ, (m : ℝ) ^ (-(2 * s - 1)))
        (𝓝[>] 1) (𝓝 1) := tendsto_sub_one_mul_tsum_nat_rpow_neg.comp h2
    simpa [M] using (h1.mul tendsto_integral_one_add_sq_rpow_neg).mul h3
  have herr : Tendsto (fun s : ℝ ↦ (s - 1) * realAnalyticEpstein z s - M s) (𝓝[>] 1) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (show Tendsto
      (fun s : ℝ ↦ (s - 1) * (2 * z.im ^ s + 4 * z.im ^ (-s)) * 2) (𝓝[>] 1) (𝓝 0) from ?_)
    · filter_upwards [self_mem_nhdsWithin] with s hs
      have hs' : 1 < s := Set.mem_Ioi.mp hs
      have hsub : (s - 1) * realAnalyticEpstein z s - M s =
          (s - 1) * (realAnalyticEpstein z s -
            2 * z.im ^ (1 - s) * (∫ u : ℝ, (1 + u ^ 2) ^ (-s)) *
              (∑' m : ℕ, (m : ℝ) ^ (-(2 * s - 1)))) := by simp only [M]; ring
      rw [Real.norm_eq_abs, hsub, abs_mul, abs_of_pos (sub_pos.mpr hs')]
      calc (s - 1) * |realAnalyticEpstein z s -
              2 * z.im ^ (1 - s) * (∫ u : ℝ, (1 + u ^ 2) ^ (-s)) *
                (∑' m : ℕ, (m : ℝ) ^ (-(2 * s - 1)))|
          ≤ (s - 1) * ((2 * z.im ^ s + 4 * z.im ^ (-s)) * ∑' m : ℕ, (m : ℝ) ^ (-(2 * s))) :=
            mul_le_mul_of_nonneg_left (abs_realAnalyticEpstein_sub_le z hs') (sub_pos.mpr hs').le
        _ ≤ (s - 1) * ((2 * z.im ^ s + 4 * z.im ^ (-s)) * 2) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
              (TauCeti.tsum_nat_rpow_neg_le_two (by linarith)) (by positivity)) (sub_pos.mpr hs').le
        _ = (s - 1) * (2 * z.im ^ s + 4 * z.im ^ (-s)) * 2 := by ring
    · have h0 : Tendsto (fun s : ℝ ↦ s - 1) (𝓝[>] 1) (𝓝 0) := by
        have hcont : Continuous fun s : ℝ ↦ s - 1 := continuous_id.sub continuous_const
        simpa using (hcont.continuousAt (x := (1 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
      have hfac : Tendsto (fun s : ℝ ↦ 2 * z.im ^ s + 4 * z.im ^ (-s)) (𝓝[>] 1)
          (𝓝 (2 * z.im ^ (1 : ℝ) + 4 * z.im ^ (-(1 : ℝ)))) := by
        have hcont : Continuous fun s : ℝ ↦ 2 * z.im ^ s + 4 * z.im ^ (-s) :=
          (continuous_const.mul
              (continuous_const.rpow continuous_id fun _ ↦ Or.inl z.im_ne_zero)).add
            (continuous_const.mul
              (continuous_const.rpow continuous_neg fun _ ↦ Or.inl z.im_ne_zero))
        exact (hcont.continuousAt (x := (1 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
      simpa using (h0.mul hfac).mul tendsto_const_nhds
  simpa using herr.add hM

/-- **Uniform polynomial bound for `(s - 1) Z(z, s)`**: for `Im z ≥ 1 / 2` and `s ∈ (1, 2]`,
`(s - 1) Z(z, s) ≤ 6 π + 36 + 4 (Im z)²`. -/
theorem sub_one_mul_realAnalyticEpstein_le (z : ℍ) (hz : 1 / 2 ≤ z.im) {s : ℝ}
    (hs1 : 1 < s) (hs2 : s ≤ 2) :
    (s - 1) * realAnalyticEpstein z s ≤ 6 * π + 36 + 4 * z.im ^ 2 := by
  have hmain := (abs_le.mp (abs_realAnalyticEpstein_sub_le z hs1)).2
  have hs1' : 0 < s - 1 := sub_pos.mpr hs1
  have hy_inv_s : z.im ^ (1 - s) ≤ 2 := by
    calc z.im ^ (1 - s) ≤ (1 / 2 : ℝ) ^ (1 - s) :=
          rpow_le_rpow_of_nonpos (by norm_num) hz (by linarith)
      _ ≤ (1 / 2 : ℝ) ^ (-(1 : ℝ)) :=
          rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by linarith)
      _ = 2 := by norm_num
  have hI : ∫ u : ℝ, (1 + u ^ 2) ^ (-s) ≤ π := integral_one_add_sq_rpow_neg_le_pi hs1.le
  have hInn : 0 ≤ ∫ u : ℝ, (1 + u ^ 2) ^ (-s) :=
    integral_nonneg fun u ↦ rpow_nonneg (by positivity) _
  have hzeta1 : (2 * s - 2) * (∑' m : ℕ, (m : ℝ) ^ (-(2 * s - 1))) ≤ 3 := by
    have hb := tsum_nat_rpow_neg_le_one_add_inv_sub_one (r := 2 * s - 1) (by linarith)
    have hpos : 0 < 2 * s - 2 := by linarith
    rw [show (2 * s - 1) - 1 = 2 * s - 2 by ring] at hb
    calc (2 * s - 2) * (∑' m : ℕ, (m : ℝ) ^ (-(2 * s - 1)))
        ≤ (2 * s - 2) * (1 + (2 * s - 2)⁻¹) := mul_le_mul_of_nonneg_left hb hpos.le
      _ = 2 * s - 1 := by rw [mul_add, mul_one, mul_inv_cancel₀ hpos.ne']; ring
      _ ≤ 3 := by linarith
  have hzeta2 : ∑' m : ℕ, (m : ℝ) ^ (-(2 * s)) ≤ 2 :=
    TauCeti.tsum_nat_rpow_neg_le_two (by linarith)
  have hy_s : z.im ^ s ≤ 1 + z.im ^ 2 := by
    rcases le_total z.im 1 with h | h
    · have : z.im ^ s ≤ 1 := rpow_le_one z.im_pos.le h (by linarith)
      nlinarith [sq_nonneg z.im]
    · have : z.im ^ s ≤ z.im ^ (2 : ℝ) := rpow_le_rpow_of_exponent_le h hs2
      rw [rpow_two] at this; linarith
  have hy_neg_s : z.im ^ (-s) ≤ 4 := by
    calc z.im ^ (-s) ≤ (1 / 2 : ℝ) ^ (-s) := rpow_le_rpow_of_nonpos (by norm_num) hz (by linarith)
      _ ≤ (1 / 2 : ℝ) ^ (-(2 : ℝ)) :=
          rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by linarith)
      _ = 4 := by norm_num
  have hterm1 : (s - 1) * (2 * z.im ^ (1 - s) * (∫ u : ℝ, (1 + u ^ 2) ^ (-s)) *
      (∑' m : ℕ, (m : ℝ) ^ (-(2 * s - 1)))) ≤ 6 * π := by
    have heq : (s - 1) * (2 * z.im ^ (1 - s) * (∫ u : ℝ, (1 + u ^ 2) ^ (-s)) *
        (∑' m : ℕ, (m : ℝ) ^ (-(2 * s - 1)))) =
        (z.im ^ (1 - s) * (∫ u : ℝ, (1 + u ^ 2) ^ (-s))) *
          ((2 * s - 2) * ∑' m : ℕ, (m : ℝ) ^ (-(2 * s - 1))) := by ring
    rw [heq]
    have hprod : z.im ^ (1 - s) * (∫ u : ℝ, (1 + u ^ 2) ^ (-s)) ≤ 2 * π :=
      mul_le_mul hy_inv_s hI hInn (by norm_num)
    have hznn : 0 ≤ (2 * s - 2) * ∑' m : ℕ, (m : ℝ) ^ (-(2 * s - 1)) :=
      mul_nonneg (by linarith) (tsum_nonneg fun m ↦ rpow_nonneg (Nat.cast_nonneg m) _)
    calc (z.im ^ (1 - s) * (∫ u : ℝ, (1 + u ^ 2) ^ (-s))) *
            ((2 * s - 2) * ∑' m : ℕ, (m : ℝ) ^ (-(2 * s - 1)))
        ≤ (2 * π) * 3 := mul_le_mul hprod hzeta1 hznn (by positivity)
      _ = 6 * π := by ring
  have hterm2 : (s - 1) * ((2 * z.im ^ s + 4 * z.im ^ (-s)) *
      (∑' m : ℕ, (m : ℝ) ^ (-(2 * s)))) ≤ 36 + 4 * z.im ^ 2 := by
    have hinner : (2 * z.im ^ s + 4 * z.im ^ (-s)) *
        (∑' m : ℕ, (m : ℝ) ^ (-(2 * s))) ≤ (2 * (1 + z.im ^ 2) + 4 * 4) * 2 :=
      mul_le_mul (by linarith) hzeta2 (tsum_nonneg fun m ↦ rpow_nonneg (Nat.cast_nonneg m) _)
        (by positivity)
    have hnn : 0 ≤ (2 * z.im ^ s + 4 * z.im ^ (-s)) * ∑' m : ℕ, (m : ℝ) ^ (-(2 * s)) :=
      mul_nonneg (by positivity) (tsum_nonneg fun m ↦ rpow_nonneg (Nat.cast_nonneg m) _)
    calc (s - 1) * ((2 * z.im ^ s + 4 * z.im ^ (-s)) * ∑' m : ℕ, (m : ℝ) ^ (-(2 * s)))
        ≤ 1 * ((2 * (1 + z.im ^ 2) + 4 * 4) * 2) :=
          mul_le_mul (by linarith) hinner hnn zero_le_one
      _ = 36 + 4 * z.im ^ 2 := by ring
  have hmul := mul_le_mul_of_nonneg_left hmain hs1'.le
  linarith

end TauCeti.EisensteinSeries
