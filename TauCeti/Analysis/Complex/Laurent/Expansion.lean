/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Laurent.Series

/-!
# Laurent series expansion, uniqueness, removable singularities, and differentiation

Let `E` be a complex normed space. Building on the two-circle Cauchy integral formula and radius
invariance of `TauCeti.circleLaurentCoeff` from `TauCeti.Analysis.Complex.Laurent.Basic` together
with `TauCeti.HasLaurentSeriesOnAnnulus` from `TauCeti.Analysis.Complex.Laurent.Series`, this file
proves:

1. **Cauchy-Laurent geometric expansions on circles** (without completeness): the nonnegative circle
   Laurent series on `C(c, R)` sums inside `Metric.ball c R` to the outer Cauchy integral, and the
   negative circle Laurent series on `C(c, r)` (`0 < r`) sums outside `Metric.closedBall c r` to
   minus the inner Cauchy integral, adapting Mathlib's
   `hasSum_two_pi_I_cauchyPowerSeries_integral` (by Yury Kudryashov) to the exterior of `C(c, r)`.
2. **Coefficient extraction and uniqueness** (for complete `E`): on every interior circle of radius
   `ρ ∈ (r, R)`, `circleLaurentCoeff f c ρ` recovers the coefficients of any convergent Laurent
   series of `f`, so Laurent series coefficients on an open annulus are unique.
3. **Laurent's theorem** (for complete `E`): every function continuous on an open concentric annulus
   `Metric.eball c R \ Metric.closedBall c r` (`0 ≤ r`, `ENNReal.ofReal r < R`, allowing `r = 0` and
   `R = ⊤`) and complex-differentiable outside a countable subset admits a convergent Laurent series
   with coefficients `circleLaurentCoeff f c ρ` for any `ρ ∈ (r, R)`.
4. **Removable-singularity characterization** (for complete `E`): a convergent Laurent series on a
   punctured disk `Metric.eball c R \ {c}` agrees near `c` with a function analytic at `c` if and
   only if all negative-degree coefficients vanish.
5. **Term-by-term differentiation** (for complete `E`): differentiating a convergent Laurent series
   shifts coefficients by `n ↦ (n + 1) • a (n + 1)`.

## Main results

* `TauCeti.hasSum_circleLaurentCoeff_natCast` and
  `TauCeti.hasSum_circleLaurentCoeff_neg_add_one`: expansion of outer and inner Cauchy integrals.
* `TauCeti.HasLaurentSeriesOnAnnulus.circleLaurentCoeff_eq` and
  `TauCeti.HasLaurentSeriesOnAnnulus.coeff_unique`: circle-integral coefficient formula and
  uniqueness of Laurent expansions.
* `TauCeti.hasLaurentSeriesOnAnnulus_of_differentiable_off_countable`,
  `DifferentiableOn.hasLaurentSeriesOnAnnulus`, and
  `TauCeti.differentiableOn_iff_exists_hasLaurentSeriesOnAnnulus`: Laurent's theorem on concentric
  open annuli.
* `TauCeti.HasLaurentSeriesOnAnnulus.exists_analyticAt_eventuallyEq_iff`: removable singularities on
  punctured disks via vanishing of negative Laurent coefficients.
* `TauCeti.HasLaurentSeriesOnAnnulus.deriv` and
  `TauCeti.HasLaurentSeriesOnAnnulus.hasSum_deriv`: term-by-term differentiation of Laurent series.

## References

* John B. Conway, *Functions of One Complex Variable I*, Graduate Texts in Mathematics 11,
  Springer, 2nd edition, 1978, Chapter V, §1.
* Lars V. Ahlfors, *Complex Analysis*, 3rd edition, McGraw-Hill, 1979, Chapter 5, §1.2.
-/

public section

open Complex Set Metric Filter
open scoped Real NNReal ENNReal Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-! ### Geometric series expansions of outer and inner Cauchy integrals -/

/-- For any circle-integrable function `f` on `C(c, R)` and any `w ∈ Metric.ball c R`, the
nonnegative circle Laurent series converges to the outer Cauchy integral
`(2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • f z`. -/
theorem hasSum_circleLaurentCoeff_natCast {f : ℂ → E} {c w : ℂ} {R : ℝ}
    (hf : CircleIntegrable f c R) (hw : w ∈ ball c R) :
    HasSum (fun n : ℕ => (w - c) ^ n • circleLaurentCoeff f c R n)
      ((2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • f z) := by
  have hw' : ‖w - c‖ < R := mem_ball_iff_norm.1 hw
  have hsum := hasSum_cauchyPowerSeries_integral hf hw'
  rw [add_sub_cancel] at hsum
  refine hsum.congr_fun fun n => ?_
  rw [(cauchyPowerSeries f c R).apply_eq_pow_smul_coeff, circleLaurentCoeff_natCast]

/-- For any circle-integrable function `f` on `C(c, r)` (`0 < r`) and any `w` outside the closed
disk `Metric.closedBall c r`, the geometric series expansion of `(w - z)⁻¹` converges under the
circle integral to `∮ z in C(c, r), (w - z)⁻¹ • f z`. -/
theorem hasSum_circleIntegral_geometric_inv_sub {f : ℂ → E} {c w : ℂ} {r : ℝ}
    (hr : 0 < r) (hf : CircleIntegrable f c r) (hw : r < dist w c) :
    HasSum (fun n : ℕ => ∮ z in C(c, r), ((z - c) / (w - c)) ^ n • (w - c)⁻¹ • f z)
      (∮ z in C(c, r), (w - z)⁻¹ • f z) := by
  have hw_norm : r < ‖w - c‖ := by simpa only [dist_eq_norm] using hw
  have hwc_pos : 0 < ‖w - c‖ := hr.trans hw_norm
  have hwc_ne : w - c ≠ 0 := norm_pos_iff.mp hwc_pos
  have hrw : r / ‖w - c‖ ∈ Ico (0 : ℝ) 1 :=
    ⟨div_nonneg hr.le hwc_pos.le, (div_lt_one hwc_pos).2 hw_norm⟩
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun n θ => (r * ‖w - c‖⁻¹) * ‖f (circleMap c r θ)‖ * (r / ‖w - c‖) ^ n)
      (fun n => ?_) (fun n => ?_) ?_ ?_ ?_
  · simp only [deriv_circleMap]
    apply_rules [MeasureTheory.AEStronglyMeasurable.smul, hf.def'.1] <;>
      apply Measurable.aestronglyMeasurable
    · fun_prop
    · fun_prop
    · fun_prop
  · refine Eventually.of_forall fun θ _ => ?_
    simp only [deriv_circleMap, circleMap_sub_center, norm_smul, norm_mul, norm_circleMap_zero,
      abs_of_pos hr, norm_I, mul_one, norm_pow, norm_div, norm_inv]
    exact le_of_eq (by ring)
  · exact Eventually.of_forall fun _ _ => (summable_geometric_of_lt_one hrw.1 hrw.2).mul_left _
  · have hint :
        IntervalIntegrable (fun θ => ‖f (circleMap c r θ)‖) MeasureTheory.volume 0 (2 * π) :=
      hf.norm
    simpa only [tsum_mul_left, tsum_geometric_of_lt_one hrw.1 hrw.2, mul_assoc] using
      (hint.const_mul (r * ‖w - c‖⁻¹)).mul_const (1 - r / ‖w - c‖)⁻¹
  · refine Eventually.of_forall fun θ _ => HasSum.const_smul _ ?_
    simp only [smul_smul]
    refine HasSum.smul_const ?_ _
    have hlt : ‖(circleMap c r θ - c) / (w - c)‖ < 1 := by
      simpa only [circleMap_sub_center, norm_div, norm_circleMap_zero, abs_of_pos hr] using hrw.2
    have hlim : (1 - (circleMap c r θ - c) / (w - c))⁻¹ * (w - c)⁻¹ =
        (w - circleMap c r θ)⁻¹ := by
      rw [← mul_inv]
      congr 1
      rw [sub_mul, one_mul, div_mul_cancel₀ _ hwc_ne]
      ring
    rw [← hlim]
    exact (hasSum_geometric_of_norm_lt_one hlt).mul_right (w - c)⁻¹

/-- For any circle-integrable function `f` on `C(c, r)` (`0 < r`) and any `w` with `r < dist w c`,
the negative-degree circle Laurent series converges to minus the inner Cauchy integral
`-((2 * π * I : ℂ)⁻¹ • ∮ z in C(c, r), (z - w)⁻¹ • f z)`. -/
theorem hasSum_circleLaurentCoeff_neg_add_one {f : ℂ → E} {c w : ℂ} {r : ℝ}
    (hr : 0 < r) (hf : CircleIntegrable f c r) (hw : r < dist w c) :
    HasSum (fun n : ℕ => (w - c) ^ (-((n : ℤ) + 1)) • circleLaurentCoeff f c r (-((n : ℤ) + 1)))
      (-((2 * π * I : ℂ)⁻¹ • ∮ z in C(c, r), (z - w)⁻¹ • f z)) := by
  have hsum := (hasSum_circleIntegral_geometric_inv_sub hr hf hw).const_smul
    (2 * π * I : ℂ)⁻¹
  have hrhs : (2 * π * I : ℂ)⁻¹ • (∮ z in C(c, r), (w - z)⁻¹ • f z) =
      -((2 * π * I : ℂ)⁻¹ • ∮ z in C(c, r), (z - w)⁻¹ • f z) := by
    have hcongr : (∮ z in C(c, r), (w - z)⁻¹ • f z) =
        ∮ z in C(c, r), (-1 : ℂ) • ((z - w)⁻¹ • f z) := by
      refine circleIntegral.integral_congr hr.le fun z _ => ?_
      have hneg : w - z = -(z - w) := by ring
      rw [hneg, inv_neg, neg_one_smul, neg_smul]
    rw [hcongr, circleIntegral.integral_smul, neg_one_smul, smul_neg]
  rw [hrhs] at hsum
  refine hsum.congr_fun fun n => ?_
  have hexp : -(-((n : ℤ) + 1)) - 1 = (n : ℤ) := by omega
  rw [circleLaurentCoeff_def, hexp, smul_comm ((w - c) ^ (-((n : ℤ) + 1))),
    ← circleIntegral.integral_smul]
  congr 1
  refine circleIntegral.integral_congr hr.le fun z _ => ?_
  rw [zpow_natCast, ← Nat.cast_add_one, zpow_neg, zpow_natCast, pow_succ, mul_inv, ← inv_pow,
    div_eq_mul_inv, mul_pow, smul_smul, smul_smul]
  congr 1
  ring

/-! ### Coefficient extraction, uniqueness, and Laurent's theorem -/

section CompleteSpace

variable [CompleteSpace E]

/-- If `∑_{k ∈ ℤ} (z - c) ^ k • a k` converges to `f z` on `Metric.sphere c ρ` (`0 < ρ`) with
summable norm bounds `∑_{k ∈ ℤ} ‖a k‖ * ρ ^ k < ∞`, then `circleLaurentCoeff f c ρ n = a n` for
every `n : ℤ`. -/
theorem circleLaurentCoeff_eq_of_hasSum_sphere {f : ℂ → E} {a : ℤ → E} {c : ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) (hs : ∀ z ∈ sphere c ρ, HasSum (fun k : ℤ => (z - c) ^ k • a k) (f z))
    (hnorm : Summable (fun k : ℤ => ‖a k‖ * ρ ^ k)) (n : ℤ) :
    circleLaurentCoeff f c ρ n = a n := by
  -- Interchange the circle integral with the integer-indexed series via a constant norm majorant.
  have hsum_int : HasSum
      (fun k : ℤ => ∮ z in C(c, ρ), (z - c) ^ (-n - 1) • (z - c) ^ k • a k)
      (∮ z in C(c, ρ), (z - c) ^ (-n - 1) • f z) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
        (fun k _ => ρ ^ (-n) * (‖a k‖ * ρ ^ k)) (fun k => ?_) (fun k => ?_) ?_ ?_ ?_
    · have hcont : Continuous (fun θ : ℝ => deriv (circleMap c ρ) θ •
          (circleMap c ρ θ - c) ^ (-n - 1) • ((circleMap c ρ θ - c) ^ k • a k)) := by
        have hne : ∀ θ : ℝ, circleMap c ρ θ - c ≠ 0 :=
          fun θ => sub_ne_zero.mpr (circleMap_ne_center hρ.ne')
        refine Continuous.smul ?_ (Continuous.smul ?_ (Continuous.smul ?_ continuous_const))
        · rw [funext (deriv_circleMap c ρ)]
          fun_prop
        · exact ((continuous_circleMap c ρ).sub continuous_const).zpow₀ (-n - 1)
            fun θ => Or.inl (hne θ)
        · exact ((continuous_circleMap c ρ).sub continuous_const).zpow₀ k
            fun θ => Or.inl (hne θ)
      exact hcont.aestronglyMeasurable
    · refine Eventually.of_forall fun θ _ => ?_
      have hp : ρ * ρ ^ (-n - 1) = ρ ^ (-n) := by
        calc
          ρ * ρ ^ (-n - 1) = ρ ^ (1 : ℤ) * ρ ^ (-n - 1) := by rw [zpow_one]
          _ = ρ ^ (1 + (-n - 1)) := (zpow_add₀ hρ.ne' _ _).symm
          _ = ρ ^ (-n) := by congr 1; ring
      simp only [deriv_circleMap, circleMap_sub_center, norm_smul, norm_mul, norm_circleMap_zero,
        abs_of_pos hρ, norm_I, mul_one, norm_zpow]
      rw [← mul_assoc, hp]
      exact le_of_eq (by ring)
    · exact Eventually.of_forall fun _ _ => hnorm.mul_left (ρ ^ (-n))
    · exact intervalIntegrable_const
    · exact Eventually.of_forall fun θ _ =>
        ((hs _ (circleMap_mem_sphere c hρ.le θ)).const_smul _).const_smul _
  -- Evaluate each monomial integral via `circleLaurentCoeff_sub_zpow_smul`.
  have hsum_coeff : HasSum
      (fun k : ℤ => circleLaurentCoeff (fun z => (z - c) ^ k • a k) c ρ n)
      (circleLaurentCoeff f c ρ n) := by
    simp_rw [circleLaurentCoeff_def]
    exact hsum_int.const_smul (2 * π * I : ℂ)⁻¹
  have hsingle : HasSum
      (fun k : ℤ => circleLaurentCoeff (fun z => (z - c) ^ k • a k) c ρ n) (a n) := by
    refine (hasSum_ite_eq n (a n)).congr_fun fun k => ?_
    rw [circleLaurentCoeff_sub_zpow_smul (a k) c hρ k n]
    by_cases hkn : k = n
    · subst k; simp
    · rw [ite_eq_right (Ne.symm hkn), ite_eq_right hkn]
  exact hsum_coeff.unique hsingle

namespace HasLaurentSeriesOnAnnulus

/-- **Cauchy-Laurent coefficient formula.** For any convergent Laurent series on
`Metric.eball c R \ Metric.closedBall c r` and any interior circle radius `ρ ∈ (r, R)`, the
`n`-th Laurent coefficient is `circleLaurentCoeff f c ρ n`. -/
theorem circleLaurentCoeff_eq {f : ℂ → E} {a : ℤ → E} {c : ℂ} {r ρ : ℝ} {R : ℝ≥0∞}
    (h : HasLaurentSeriesOnAnnulus f a c r R) (hrρ : r < ρ) (hρR : ENNReal.ofReal ρ < R)
    (n : ℤ) : circleLaurentCoeff f c ρ n = a n := by
  have hρ_pos : 0 < ρ := h.r_nonneg.trans_lt hrρ
  have hsphere : sphere c ρ ⊆ eball c R \ closedBall c r := fun z hz => by
    have hdist : dist z c = ρ := mem_sphere.mp hz
    refine ⟨?_, ?_⟩
    · rw [mem_eball, edist_dist, hdist]
      exact hρR
    · rw [mem_closedBall, hdist, not_le]
      exact hrρ
  exact circleLaurentCoeff_eq_of_hasSum_sphere hρ_pos (fun z hz => h.hasSum (hsphere hz))
    (h.summable_norm_mul_zpow hrρ hρR) n

/-- **Uniqueness of Laurent series coefficients.** Two Laurent series converging to the same
function on the same open annulus have identical coefficients. -/
theorem coeff_unique {f : ℂ → E} {a b : ℤ → E} {c : ℂ} {r : ℝ} {R : ℝ≥0∞}
    (ha : HasLaurentSeriesOnAnnulus f a c r R) (hb : HasLaurentSeriesOnAnnulus f b c r R) :
    a = b := by
  obtain ⟨q, hrq, hqR⟩ := exists_between ha.r_lt
  lift q to ℝ≥0 using hqR.ne_top
  have hrq' : r < (q : ℝ) := (ENNReal.ofReal_lt_coe_iff ha.r_nonneg).mp hrq
  have hqR' : ENNReal.ofReal (q : ℝ) < R := by simpa using hqR
  funext n
  exact (ha.circleLaurentCoeff_eq hrq' hqR' n).symm.trans (hb.circleLaurentCoeff_eq hrq' hqR' n)

end HasLaurentSeriesOnAnnulus

/-- **Pointwise Laurent expansion on a closed annulus.** If `f` is continuous on the closed annulus
`Metric.closedBall c R \ Metric.ball c r` (`0 < r`) and complex-differentiable outside a countable
set in the open annulus, then at every `w ∈ Metric.ball c R \ Metric.closedBall c r` and for every
integrating radius `ρ ∈ [r, R]`, the Laurent series with coefficients `circleLaurentCoeff f c ρ`
converges to `f w`. -/
theorem hasSum_circleLaurentCoeff_of_differentiable_on_annulus_off_countable
    {f : ℂ → E} {c w : ℂ} {r ρ R : ℝ} {s : Set ℂ}
    (hr : 0 < r) (hrρ : r ≤ ρ) (hρR : ρ ≤ R) (hs : s.Countable)
    (hw : w ∈ ball c R \ closedBall c r)
    (hc : ContinuousOn f (closedBall c R \ ball c r))
    (hd : ∀ z ∈ (ball c R \ closedBall c r) \ s, DifferentiableAt ℂ f z) :
    HasSum (fun n : ℤ => (w - c) ^ n • circleLaurentCoeff f c ρ n) (f w) := by
  have hrw : r < dist w c := not_le.mp (mt mem_closedBall.mpr hw.2)
  have hrR : r ≤ R := hrρ.trans hρR
  have hR_pos : 0 < R := hr.trans_le hrR
  have hρ_pos : 0 < ρ := hr.trans_le hrρ
  -- Coefficients at `R` and at `r` both agree with those at `ρ`.
  have hcoeff_R : ∀ n : ℤ, circleLaurentCoeff f c R n = circleLaurentCoeff f c ρ n := fun n =>
    circleLaurentCoeff_eq_of_differentiable_on_annulus_off_countable hρ_pos hρR hs
      (hc.mono fun z hz => ⟨hz.1, fun h => hz.2 (ball_subset_ball hrρ h)⟩)
      (fun z hz => hd z ⟨⟨hz.1.1, fun h => hz.1.2 (closedBall_subset_closedBall hrρ h)⟩, hz.2⟩) n
  have hcoeff_r : ∀ n : ℤ, circleLaurentCoeff f c ρ n = circleLaurentCoeff f c r n := fun n =>
    circleLaurentCoeff_eq_of_differentiable_on_annulus_off_countable hr hrρ hs
      (hc.mono fun z hz => ⟨closedBall_subset_closedBall hρR hz.1, hz.2⟩)
      (fun z hz => hd z ⟨⟨ball_subset_ball hρR hz.1.1, hz.1.2⟩, hz.2⟩) n
  have hint_R : CircleIntegrable f c R :=
    (hc.mono fun z hz => ⟨sphere_subset_closedBall hz,
      fun hzr => (not_lt_of_ge hrR) ((mem_sphere.mp hz) ▸ hzr)⟩).circleIntegrable hR_pos.le
  have hint_r : CircleIntegrable f c r :=
    (hc.mono fun z hz => ⟨closedBall_subset_closedBall hrR (sphere_subset_closedBall hz),
      fun h => (ne_of_lt h) (mem_sphere.mp hz)⟩).circleIntegrable hr.le
  have hpos : HasSum (fun n : ℕ => (w - c) ^ (n : ℤ) • circleLaurentCoeff f c ρ (n : ℤ))
      ((2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • f z) := by
    refine (hasSum_circleLaurentCoeff_natCast hint_R hw.1).congr_fun fun n => ?_
    rw [zpow_natCast, hcoeff_R]
  have hneg : HasSum
      (fun n : ℕ => (w - c) ^ (-((n : ℤ) + 1)) • circleLaurentCoeff f c ρ (-((n : ℤ) + 1)))
      (-((2 * π * I : ℂ)⁻¹ • ∮ z in C(c, r), (z - w)⁻¹ • f z)) := by
    refine (hasSum_circleLaurentCoeff_neg_add_one hr hint_r hrw).congr_fun fun n => ?_
    rw [hcoeff_r]
  have hcauchy :=
    two_pi_I_inv_smul_circleIntegral_sub_inv_smul_sub_of_differentiable_on_annulus_off_countable
      hr hs hw hc hd
  rw [smul_sub, sub_eq_add_neg] at hcauchy
  exact hcauchy ▸ hpos.of_nat_of_neg_add_one hneg

/-- **Laurent's theorem on an open concentric annulus (with countable exceptional set).**
Let `0 ≤ r` and `r < ρ` with `ENNReal.ofReal ρ < R` (allowing `r = 0` for punctured disks and
`R = ⊤` for exteriors of closed disks or `ℂ \ {c}`). If `f : ℂ → E` is continuous on the open
annulus `Metric.eball c R \ Metric.closedBall c r` and complex-differentiable outside a countable
set `s`, then `f` has the convergent Laurent series with coefficients `circleLaurentCoeff f c ρ`
throughout `Metric.eball c R \ Metric.closedBall c r`. -/
theorem hasLaurentSeriesOnAnnulus_of_differentiable_off_countable
    {f : ℂ → E} {c : ℂ} {r ρ : ℝ} {R : ℝ≥0∞} {s : Set ℂ}
    (hr : 0 ≤ r) (hrρ : r < ρ) (hρR : ENNReal.ofReal ρ < R) (hs : s.Countable)
    (hc : ContinuousOn f (eball c R \ closedBall c r))
    (hd : ∀ z ∈ (eball c R \ closedBall c r) \ s, DifferentiableAt ℂ f z) :
    HasLaurentSeriesOnAnnulus f (circleLaurentCoeff f c ρ) c r R where
  r_nonneg := hr
  r_lt := (ENNReal.ofReal_le_ofReal hrρ.le).trans_lt hρR
  hasSum {w} hw := by
    have hrw : r < dist w c := not_le.mp (mt mem_closedBall.mpr hw.2)
    let r' : ℝ := (r + min ρ (dist w c)) / 2
    have hrr' : r < r' := by
      have hmin : r < min ρ (dist w c) := lt_min hrρ hrw
      dsimp [r']; linarith
    have hr'_pos : 0 < r' := hr.trans_lt hrr'
    have hr'ρ : r' ≤ ρ := by
      have hle : min ρ (dist w c) ≤ ρ := min_le_left _ _
      dsimp [r']; linarith
    have hr'w : r' < dist w c := by
      have hle : min ρ (dist w c) ≤ dist w c := min_le_right _ _
      dsimp [r']; linarith
    have hwR : ENNReal.ofReal (dist w c) < R := by simpa only [mem_eball, edist_dist] using hw.1
    obtain ⟨q, hq_gt, hqR⟩ := exists_between (max_lt hρR hwR)
    lift q to ℝ≥0 using hqR.ne_top
    have hρq : ρ ≤ (q : ℝ) :=
      ((ENNReal.ofReal_lt_coe_iff (hr.trans_lt hrρ).le).mp ((le_max_left _ _).trans_lt hq_gt)).le
    have hwq : dist w c < (q : ℝ) :=
      (ENNReal.ofReal_lt_coe_iff dist_nonneg).mp ((le_max_right _ _).trans_lt hq_gt)
    have hqR' : ENNReal.ofReal (q : ℝ) < R := by simpa using hqR
    have hsub : closedBall c (q : ℝ) \ ball c r' ⊆ eball c R \ closedBall c r := fun z hz =>
      ⟨by rw [mem_eball, edist_dist]; exact (ENNReal.ofReal_le_ofReal hz.1).trans_lt hqR',
        fun hzr => hz.2 (lt_of_le_of_lt hzr hrr')⟩
    exact hasSum_circleLaurentCoeff_of_differentiable_on_annulus_off_countable
      hr'_pos hr'ρ hρq hs ⟨hwq, not_le.mpr hr'w⟩ (hc.mono hsub)
      (fun z hz => hd z ⟨hsub ⟨ball_subset_closedBall hz.1.1,
        fun h => hz.1.2 (ball_subset_closedBall h)⟩, hz.2⟩)

/-- **Laurent's theorem on an open concentric annulus.** Every function `f : ℂ → E` into a complex
Banach space that is complex-differentiable on `Metric.eball c R \ Metric.closedBall c r` (`0 ≤ r`,
`r < ρ`, `ENNReal.ofReal ρ < R`) expands in a convergent Laurent series with coefficients
`circleLaurentCoeff f c ρ`. -/
theorem _root_.DifferentiableOn.hasLaurentSeriesOnAnnulus
    {f : ℂ → E} {c : ℂ} {r ρ : ℝ} {R : ℝ≥0∞}
    (hf : DifferentiableOn ℂ f (eball c R \ closedBall c r))
    (hr : 0 ≤ r) (hrρ : r < ρ) (hρR : ENNReal.ofReal ρ < R) :
    HasLaurentSeriesOnAnnulus f (circleLaurentCoeff f c ρ) c r R := by
  have hopen : IsOpen (eball c R \ closedBall c r) := isOpen_eball.sdiff isClosed_closedBall
  exact hasLaurentSeriesOnAnnulus_of_differentiable_off_countable hr hrρ hρR countable_empty
    hf.continuousOn fun z hz => (hf z hz.1).differentiableAt (hopen.mem_nhds hz.1)

/-- For a complete target space `E`, complex differentiability on a nonempty open concentric annulus
is equivalent to admitting a convergent Laurent series on that annulus. -/
theorem differentiableOn_iff_exists_hasLaurentSeriesOnAnnulus
    {f : ℂ → E} {c : ℂ} {r : ℝ} {R : ℝ≥0∞} (hr : 0 ≤ r) (hrR : ENNReal.ofReal r < R) :
    DifferentiableOn ℂ f (eball c R \ closedBall c r) ↔
      ∃ a : ℤ → E, HasLaurentSeriesOnAnnulus f a c r R := by
  refine ⟨fun hf => ?_, fun ⟨_, ha⟩ => ha.differentiableOn⟩
  obtain ⟨q, hrq, hqR⟩ := exists_between hrR
  lift q to ℝ≥0 using hqR.ne_top
  exact ⟨circleLaurentCoeff f c (q : ℝ),
    hf.hasLaurentSeriesOnAnnulus hr ((ENNReal.ofReal_lt_coe_iff hr).mp hrq) (by simpa using hqR)⟩

/-- For a complete target space `E`, complex analyticity on a nonempty open concentric annulus is
equivalent to admitting a convergent Laurent series on that annulus. -/
theorem analyticOnNhd_iff_exists_hasLaurentSeriesOnAnnulus
    {f : ℂ → E} {c : ℂ} {r : ℝ} {R : ℝ≥0∞} (hr : 0 ≤ r) (hrR : ENNReal.ofReal r < R) :
    AnalyticOnNhd ℂ f (eball c R \ closedBall c r) ↔
      ∃ a : ℤ → E, HasLaurentSeriesOnAnnulus f a c r R :=
  ⟨fun hf => (differentiableOn_iff_exists_hasLaurentSeriesOnAnnulus hr hrR).mp hf.differentiableOn,
    fun ⟨_, ha⟩ => ha.analyticOnNhd⟩

/-! ### Removable-singularity characterization on punctured disks -/

namespace HasLaurentSeriesOnAnnulus

private theorem coeff_eq_of_hasFPowerSeriesOnBall_eventuallyEq
    {f g : ℂ → E} {a : ℤ → E} {p : FormalMultilinearSeries ℂ ℂ E} {c : ℂ} {R R₀ : ℝ≥0∞}
    (h : HasLaurentSeriesOnAnnulus f a c 0 R) (hp : HasFPowerSeriesOnBall g p c R₀)
    (hfg : f =ᶠ[𝓝[≠] c] g) :
    a = fun n : ℤ => if 0 ≤ n then p.coeff n.toNat else 0 := by
  obtain ⟨ε, hε, hεfg⟩ := EMetric.mem_nhdsWithin_iff.1 hfg.symm
  let R₁ : ℝ≥0∞ := min R (min R₀ ε)
  have hR₁_pos : ENNReal.ofReal 0 < R₁ := by
    simpa [R₁] using lt_min h.r_pos (lt_min hp.r_pos hε)
  have h₁ := h.mono le_rfl (min_le_left _ _) hR₁_pos
  have h₂_g := hp.hasLaurentSeriesOnAnnulus.mono le_rfl
    ((min_le_right _ _).trans (min_le_left _ _)) hR₁_pos
  have h₂ := h₂_g.congr fun z hz => hεfg ⟨eball_subset_eball
    ((min_le_right _ _).trans (min_le_right _ _)) hz.1, by simpa using hz.2⟩
  exact h₁.coeff_unique h₂

/-- If `f` has a Laurent series on `Metric.eball c R \ {c}` and agrees on a punctured neighborhood
of `c` with a function analytic at `c`, then all negative-degree coefficients of `a` vanish. -/
theorem coeff_neg_add_one_eq_zero_of_analyticAt {f g : ℂ → E} {a : ℤ → E} {c : ℂ} {R : ℝ≥0∞}
    (h : HasLaurentSeriesOnAnnulus f a c 0 R) (hg : AnalyticAt ℂ g c) (hfg : f =ᶠ[𝓝[≠] c] g)
    (k : ℕ) : a (-((k : ℤ) + 1)) = 0 := by
  obtain ⟨p, R₀, hp⟩ := hg
  have heq := congrFun (h.coeff_eq_of_hasFPowerSeriesOnBall_eventuallyEq hp hfg) (-((k : ℤ) + 1))
  split_ifs at heq with hge
  · omega
  · exact heq

/-- If `f` has a Laurent series on `Metric.eball c R \ {c}` and agrees on a punctured neighborhood
of `c` with a function `g` analytic at `c`, then `a 0 = g c`. -/
theorem coeff_zero_eq_of_analyticAt {f g : ℂ → E} {a : ℤ → E} {c : ℂ} {R : ℝ≥0∞}
    (h : HasLaurentSeriesOnAnnulus f a c 0 R) (hg : AnalyticAt ℂ g c) (hfg : f =ᶠ[𝓝[≠] c] g) :
    a 0 = g c := by
  obtain ⟨p, R₀, hp⟩ := hg
  have heq := congrFun (h.coeff_eq_of_hasFPowerSeriesOnBall_eventuallyEq hp hfg) 0
  simpa [FormalMultilinearSeries.coeff] using heq.trans (hp.coeff_zero 1)

/-- **Characterization of removable singularities via Laurent coefficients.** A function with a
convergent Laurent series on `Metric.eball c R \ {c}` agrees on a punctured neighborhood of `c`
with a function analytic at `c` if and only if all of its negative-degree coefficients vanish. -/
theorem exists_analyticAt_eventuallyEq_iff {f : ℂ → E} {a : ℤ → E} {c : ℂ} {R : ℝ≥0∞}
    (h : HasLaurentSeriesOnAnnulus f a c 0 R) :
    (∃ g : ℂ → E, AnalyticAt ℂ g c ∧ f =ᶠ[𝓝[≠] c] g) ↔
      ∀ k : ℕ, a (-((k : ℤ) + 1)) = 0 := by
  refine ⟨fun ⟨g, hg, hfg⟩ k => h.coeff_neg_add_one_eq_zero_of_analyticAt hg hfg k, fun ha => ?_⟩
  refine ⟨Function.update f c (a 0),
    (h.analyticOnNhd_update_of_neg_eq_zero ha) c (mem_eball_self h.r_pos), ?_⟩
  exact eventually_nhdsWithin_iff.2
    (Eventually.of_forall fun z hzc => (Function.update_of_ne hzc _ _).symm)

end HasLaurentSeriesOnAnnulus

/-! ### Term-by-term differentiation of Laurent series -/

namespace HasLaurentSeriesOnAnnulus

/-- **Term-by-term differentiation of a convergent Laurent series.** If `f` has the Laurent series
with coefficients `a` on an open annulus, then `deriv f` has the Laurent series with coefficients
`n ↦ ((n + 1 : ℤ) : ℂ) • a (n + 1)` on the same open annulus. -/
theorem deriv {f : ℂ → E} {a : ℤ → E} {c : ℂ} {r : ℝ} {R : ℝ≥0∞}
    (h : HasLaurentSeriesOnAnnulus f a c r R) :
    HasLaurentSeriesOnAnnulus (_root_.deriv f)
      (fun n : ℤ => ((n + 1 : ℤ) : ℂ) • a (n + 1)) c r R := by
  have hopen : IsOpen (eball c R \ closedBall c r) := isOpen_eball.sdiff isClosed_closedBall
  obtain ⟨q, hrq, hqR⟩ := exists_between h.r_lt
  lift q to ℝ≥0 using hqR.ne_top
  have hrq' : r < (q : ℝ) := (ENNReal.ofReal_lt_coe_iff h.r_nonneg).mp hrq
  have hqR' : ENNReal.ofReal (q : ℝ) < R := by simpa using hqR
  have hser := (h.differentiableOn.deriv hopen).hasLaurentSeriesOnAnnulus h.r_nonneg hrq' hqR'
  have hcoeff : circleLaurentCoeff (_root_.deriv f) c (q : ℝ) =
      fun n : ℤ => ((n + 1 : ℤ) : ℂ) • a (n + 1) := by
    funext n
    rw [circleLaurentCoeff_deriv h.differentiableOn h.r_nonneg hrq' hqR' n,
      h.circleLaurentCoeff_eq hrq' hqR' (n + 1)]
  rwa [hcoeff] at hser

/-- Unshifted term-by-term differentiation formula: on the open annulus,
`∑_{n ∈ ℤ} (n * (w - c) ^ (n - 1)) • a n` converges to `deriv f w`. -/
theorem hasSum_deriv {f : ℂ → E} {a : ℤ → E} {c w : ℂ} {r : ℝ} {R : ℝ≥0∞}
    (h : HasLaurentSeriesOnAnnulus f a c r R) (hw : w ∈ eball c R \ closedBall c r) :
    HasSum (fun n : ℤ => ((n : ℂ) * (w - c) ^ (n - 1)) • a n) (_root_.deriv f w) := by
  rw [← (Equiv.addRight (1 : ℤ)).hasSum_iff]
  refine (h.deriv.hasSum hw).congr_fun fun n => ?_
  simp only [Function.comp_def, Equiv.coe_addRight, add_sub_cancel_right]
  rw [mul_comm, mul_smul]

end HasLaurentSeriesOnAnnulus

end CompleteSpace

end TauCeti
