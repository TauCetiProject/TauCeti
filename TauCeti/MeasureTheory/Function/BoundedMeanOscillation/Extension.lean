/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.BoundedMeanOscillation

/-!
# Extending a function from a ball with control of its mean oscillation

Let `E` be a real normed space of finite dimension `n` with an additive Haar measure `μ`, and let
`b : E → F` be locally integrable. Its VMO modulus `η_b(ρ)` (`TauCeti.vmoModulus`) is the
supremum of the mean oscillations of `b` over the balls of radius at most `ρ`. This file shows
that on a ball `B(c, r)` the function `b` agrees with a function of bounded mean oscillation
whose BMO seminorm is controlled by the mean oscillation of `b` on balls of radius at most `8 r`:
there is a locally integrable `g` with `g = b` on `B(c, r)`, `g` constant off `B(c, 2 r)`, and

`‖g‖_{BMO} ≤ 2 (1 + 2ⁿ⁺³ + 8ⁿ) η_b(8 r)`

(`TauCeti.exists_eqOn_ball_and_bmoSeminorm_le_vmoModulus`). The constant depends only on the
dimension. For a function of vanishing mean oscillation the right-hand side tends to `0` with
`r`.

This is how perturbation arguments for operators with coefficients of vanishing mean oscillation
localize the global estimates of a function of bounded mean oscillation: an operator built from
`b` and acting on functions supported in `B(c, r)` only sees `b` on `B(c, r)`, so it is unchanged
when `b` is replaced by `g`. For instance, if `f` vanishes off `B(c, r)`, then the commutator
`b T f - T (b f)` of a singular integral operator `T` with multiplication by `b` agrees on
`B(c, r)` with `g T f - T (g f)`, and a bound for commutators in terms of the BMO seminorm becomes a
bound in terms of `η_b(8 r)`.

## The construction

Let `a = b_{B(c, r)}` be the average of `b` over `B(c, r)` and let `φ` be the cutoff equal to `1`
on `B(c, r)`, to `0` off `B(c, 2 r)`, and `1 / r`-Lipschitz, given by Mathlib's
`thickenedIndicator` of `B(c, r)` at width `r`. Put

`g = φ • (b - a) + a`.

The mean oscillation of `g` on a ball `B = B(x, s)` is estimated in three cases.

* If `s ≥ r`, then `‖g - a‖ ≤ ‖b - a‖` on `B(c, 2 r)` and `g = a` off it, so the average of
  `‖g - a‖` over `B` is at most `2ⁿ` times the average of `‖b - a‖` over `B(c, 2 r)`, which is at
  most `(1 + 2ⁿ) η_b(2 r)`.
* If `s < r` and `x ∈ B(c, 3 r)`, compare `g` with the constant
  `φ(x) • (b_B - a) + a`: the difference is `φ • (b - b_B) + (φ - φ(x)) • (b_B - a)`, and
  `|φ - φ(x)| ≤ s / r` on `B`. The averages of `b` over the concentric balls `B(x, 2ʲ s)` drift by
  at most `2ⁿ η_b(8 r)` per doubling up to a radius `R ∈ (4 r, 8 r]`, where `B(x, R)` contains
  `B(c, r)`, so `‖b_B - a‖ ≤ (j 2ⁿ + 8ⁿ) η_b(8 r)` with `2ʲ s = R`. The logarithmic number `j` of
  doublings is compensated by the factor `s / r ≤ 8 / 2ʲ`.
* If `s < r` and `x ∉ B(c, 3 r)`, then `B` does not meet `B(c, 2 r)` and `g` is constant on `B`.

A cutoff that jumps, `g = b` on `B(c, r)` and `g = a` off it, does not work: on a small ball
across the sphere the oscillation of `g` is about `|b_B - a|`, which can grow like
`log (r / s) η_b(r)`.

## Main declarations

* `TauCeti.exists_eqOn_ball_and_bmoSeminorm_le_vmoModulus`: the extension of `b` from `B(c, r)`
  with BMO seminorm at most `2 (1 + 2ⁿ⁺³ + 8ⁿ) η_b(8 r)`.

## References

* F. Chiarenza, M. Frasca, P. Longo, *Interior `W^{2,p}` estimates for nondivergence elliptic
  equations with discontinuous coefficients*, Ricerche Mat. **40** (1991), 149–168 (the
  localization of commutator estimates to small balls for coefficients of vanishing mean
  oscillation).
-/

public section

namespace TauCeti

open MeasureTheory Metric Set Module
open scoped ENNReal NNReal

/-! ### The cutoff -/

section Cutoff

variable {E : Type*} [PseudoMetricSpace E] {c : E} {r : ℝ}

/-- The cutoff `thickenedIndicator hr (ball c r)` as a real function: it equals `1` on `B(c, r)`,
vanishes off `B(c, 2 r)`, and is `1 / r`-Lipschitz. -/
private noncomputable def ballCutoff (hr : 0 < r) (c : E) (y : E) : ℝ :=
  thickenedIndicator hr (ball c r) y

private theorem ballCutoff_nonneg (hr : 0 < r) (c y : E) : 0 ≤ ballCutoff hr c y :=
  NNReal.coe_nonneg _

private theorem ballCutoff_le_one (hr : 0 < r) (c y : E) : ballCutoff hr c y ≤ 1 :=
  NNReal.coe_le_one.2 (thickenedIndicator_le_one hr _ y)

private theorem ballCutoff_eq_one (hr : 0 < r) {y : E} (hy : y ∈ ball c r) :
    ballCutoff hr c y = 1 := by
  rw [ballCutoff, thickenedIndicator_one hr _ hy, NNReal.coe_one]

private theorem ballCutoff_eq_zero (hr : 0 < r) {y : E} (hy : y ∉ ball c (2 * r)) :
    ballCutoff hr c y = 0 := by
  refine NNReal.coe_eq_zero.2 (thickenedIndicator_zero hr _ fun h => hy ?_)
  simpa [two_mul] using thickening_ball c r r h

private theorem abs_ballCutoff_sub_le (hr : 0 < r) (c x y : E) :
    |ballCutoff hr c y - ballCutoff hr c x| ≤ dist y x / r := by
  have h := (lipschitzWith_thickenedIndicator hr (ball c r)).dist_le_mul y x
  rwa [NNReal.dist_eq, NNReal.coe_inv, Real.coe_toNNReal _ hr.le, inv_mul_eq_div] at h

private theorem continuous_ballCutoff (hr : 0 < r) (c : E) : Continuous (ballCutoff hr c) :=
  NNReal.continuous_coe.comp (thickenedIndicator hr (ball c r)).continuous

end Cutoff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [FiniteDimensional ℝ E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The extension `φ • (b - a) + a` of `b` from `B(c, r)`, where `a` is the average of `b` over
`B(c, r)` and `φ` is `ballCutoff hr c`. -/
private noncomputable def ballExtension (μ : Measure E) (b : E → F) {r : ℝ} (hr : 0 < r) (c : E)
    (y : E) : F :=
  ballCutoff hr c y • (b y - ⨍ z in ball c r, b z ∂μ) + ⨍ z in ball c r, b z ∂μ

/-! ### The three cases -/

/-- On a ball of radius `s ≥ r`, the extension stays within `2ⁿ (1 + 2ⁿ) η_b(2 r)` of `a` on
average. -/
private theorem setLAverage_enorm_ballExtension_sub_le_of_le {b : E → F}
    (hb : LocallyIntegrable b μ) (c : E) {r s : ℝ} (hr : 0 < r) (hrs : r ≤ s) (x : E) :
    ⨍⁻ y in ball x s, ‖ballExtension μ b hr c y - ⨍ z in ball c r, b z ∂μ‖ₑ ∂μ ≤
      2 ^ finrank ℝ E * ((1 + 2 ^ finrank ℝ E) * vmoModulus b μ (2 * r)) := by
  set n := finrank ℝ E
  set a := ⨍ z in ball c r, b z ∂μ
  have hpt (y : E) : ‖ballExtension μ b hr c y - a‖ₑ ≤
      (ball c (2 * r)).indicator (fun y => ‖b y - a‖ₑ) y := by
    rw [ballExtension, add_sub_cancel_right, eNorm_smul]
    by_cases hy : y ∈ ball c (2 * r)
    · rw [indicator_of_mem hy]
      refine mul_le_of_le_one_left' ?_
      rw [Real.eNorm_eq_ofReal (ballCutoff_nonneg hr c y)]
      exact ENNReal.ofReal_le_one.2 (ballCutoff_le_one hr c y)
    · rw [indicator_of_notMem hy, ballCutoff_eq_zero hr hy, eNorm_zero, zero_mul]
  -- The average of `‖b - a‖` over `B(c, 2 r)`.
  have hX : ⨍⁻ y in ball c (2 * r), ‖b y - a‖ₑ ∂μ ≤ (1 + 2 ^ n) * vmoModulus b μ (2 * r) := by
    have hdrift := enorm_setAverage_ball_sub_setAverage_ball_le_vmoModulus
      hb.aestronglyMeasurable (μ := μ) c hr 1
    rw [pow_one, Nat.cast_one, one_mul] at hdrift
    calc ⨍⁻ y in ball c (2 * r), ‖b y - a‖ₑ ∂μ
        ≤ ⨍⁻ y in ball c (2 * r), ‖b y - ⨍ z in ball c (2 * r), b z ∂μ‖ₑ ∂μ +
            ‖(⨍ z in ball c (2 * r), b z ∂μ) - a‖ₑ :=
          setLAverage_enorm_sub_le_setLAverage_enorm_sub_add_enorm_sub _ _ _ _
      _ ≤ vmoModulus b μ (2 * r) + 2 ^ n * vmoModulus b μ (2 * r) :=
          add_le_add (setLAverage_enorm_sub_setAverage_le_vmoModulus b μ c le_rfl) hdrift
      _ = (1 + 2 ^ n) * vmoModulus b μ (2 * r) := by ring
  have h0 : μ (ball x s) ≠ 0 := (measure_ball_pos μ x (hr.trans_le hrs)).ne'
  have htop : μ (ball x s) ≠ ∞ := measure_ball_lt_top.ne
  have hμ : μ (ball c (2 * r)) ≤ 2 ^ n * μ (ball x s) := by
    rw [μ.addHaar_ball_mul_of_pos c two_pos, ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat,
      ← μ.addHaar_ball_center x r]
    gcongr
  calc ⨍⁻ y in ball x s, ‖ballExtension μ b hr c y - a‖ₑ ∂μ
      = (∫⁻ y in ball x s, ‖ballExtension μ b hr c y - a‖ₑ ∂μ) / μ (ball x s) := by
        rw [setLAverage_eq]
    _ ≤ (∫⁻ y in ball c (2 * r), ‖b y - a‖ₑ ∂μ) / μ (ball x s) := by
        refine ENNReal.div_le_div_right ?_ _
        calc ∫⁻ y in ball x s, ‖ballExtension μ b hr c y - a‖ₑ ∂μ
            ≤ ∫⁻ y in ball x s, (ball c (2 * r)).indicator (fun y => ‖b y - a‖ₑ) y ∂μ :=
              lintegral_mono hpt
          _ ≤ ∫⁻ y, (ball c (2 * r)).indicator (fun y => ‖b y - a‖ₑ) y ∂μ :=
              setLIntegral_le_lintegral _ _
          _ = ∫⁻ y in ball c (2 * r), ‖b y - a‖ₑ ∂μ := lintegral_indicator measurableSet_ball _
    _ = μ (ball c (2 * r)) * (⨍⁻ y in ball c (2 * r), ‖b y - a‖ₑ ∂μ) / μ (ball x s) := by
        rw [measure_mul_setLAverage _ measure_ball_lt_top.ne]
    _ ≤ 2 ^ n * μ (ball x s) * ((1 + 2 ^ n) * vmoModulus b μ (2 * r)) / μ (ball x s) := by
        gcongr
    _ = 2 ^ n * ((1 + 2 ^ n) * vmoModulus b μ (2 * r)) := by
        rw [mul_right_comm, ENNReal.mul_div_cancel_right h0 htop]

/-- If `2ᵏ⁺¹ s ≤ 8 r`, then `(s / r) (k + 1) ≤ 8`: the number of doublings from `s` to a radius at
most `8 r` is compensated by the ratio `s / r`. -/
private theorem ofReal_div_mul_natCast_succ_le {r s : ℝ} (hr : 0 < r) (hs : 0 < s) {k : ℕ}
    (hk : 2 ^ (k + 1) * s ≤ 8 * r) : ENNReal.ofReal (s / r) * (k + 1 : ℕ) ≤ 8 := by
  calc ENNReal.ofReal (s / r) * (k + 1 : ℕ) ≤ ENNReal.ofReal (s / r) * 2 ^ (k + 1) := by
        gcongr
        exact_mod_cast (k + 1).lt_two_pow_self.le
    _ = ENNReal.ofReal (2 ^ (k + 1) * s / r) := by
        rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_pow zero_le_two,
          ← ENNReal.ofReal_mul (div_nonneg hs.le hr.le), mul_div_assoc, mul_comm]
    _ ≤ ENNReal.ofReal 8 := ENNReal.ofReal_le_ofReal ((div_le_iff₀ hr).2 hk)
    _ = 8 := ENNReal.ofReal_ofNat 8

/-- **Averages over a small ball near `B(c, r)`.** If `0 < s < r` and `x` lies in `B(c, 3 r)`,
the averages of `b` over `B(x, s)` and over `B(c, r)` differ by `O(log (r / s) η_b(8 r))`; the
factor `s / r` absorbs the logarithm:

`(s / r) ‖b_{B(x, s)} - b_{B(c, r)}‖ ≤ (2ⁿ⁺³ + 8ⁿ) η_b(8 r)`. -/
private theorem ofReal_div_mul_enorm_setAverage_sub_setAverage_le {b : E → F}
    (hb : AEStronglyMeasurable b μ) {c x : E} {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (hsr : s < r)
    (hx : dist x c < 3 * r) :
    ENNReal.ofReal (s / r) * ‖(⨍ z in ball x s, b z ∂μ) - ⨍ z in ball c r, b z ∂μ‖ₑ ≤
      (2 ^ (finrank ℝ E + 3) + 8 ^ finrank ℝ E) * vmoModulus b μ (8 * r) := by
  set n := finrank ℝ E
  set a := ⨍ z in ball c r, b z ∂μ
  set b' := ⨍ z in ball x s, b z ∂μ
  -- Choose `R = 2^(k+1) s ∈ (4 r, 8 r]`, so that `B(c, r) ⊆ B(x, R)`.
  obtain ⟨k, hk₁, hk₂⟩ := exists_nat_pow_near (x := 4 * r / s) (y := (2 : ℝ))
    ((le_div_iff₀ hs).2 (by linarith)) one_lt_two
  set R := 2 ^ (k + 1) * s
  have hR₄ : 4 * r < R := (div_lt_iff₀ hs).1 hk₂
  have hR₈ : R ≤ 8 * r := by
    have := (le_div_iff₀ hs).1 hk₁
    simp only [R, pow_succ]
    linarith
  have hsub : ball c r ⊆ ball x R := fun y hy => by
    rw [mem_ball] at hy ⊢
    linarith [dist_triangle y c x, dist_comm x c]
  -- The drift of the averages from `B(x, s)` to `B(x, R)`, and from `B(x, R)` to `B(c, r)`.
  have hdrift : ‖(⨍ z in ball x R, b z ∂μ) - b'‖ₑ ≤
      (k + 1 : ℕ) * 2 ^ n * vmoModulus b μ (8 * r) :=
    (enorm_setAverage_ball_sub_setAverage_ball_le_vmoModulus hb x hs
      (k + 1)).trans (by gcongr; exact monotone_vmoModulus b μ hR₈)
  have hfar : ‖a - ⨍ z in ball x R, b z ∂μ‖ₑ ≤ 8 ^ n * vmoModulus b μ (8 * r) := by
    have hμ : μ (ball x R) ≤ 8 ^ n * μ (ball c r) := by
      calc μ (ball x R) ≤ μ (ball x (8 * r)) := measure_mono (ball_subset_ball hR₈)
        _ = 8 ^ n * μ (ball c r) := by
          rw [μ.addHaar_ball_mul_of_pos x (by norm_num : (0 : ℝ) < 8),
            ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat, ← μ.addHaar_ball_center c r]
    refine (enorm_setAverage_sub_le_of_subset hsub (measure_ball_pos μ c hr).ne'
      measure_ball_lt_top.ne hb.restrict _).trans ?_
    gcongr
    · exact ENNReal.div_le_of_le_mul hμ
    · exact (setLAverage_enorm_sub_setAverage_le_vmoModulus b μ x hR₈)
  -- The factor `s / r` absorbs the number `k + 1` of doublings.
  have hfac := ofReal_div_mul_natCast_succ_le hr hs hR₈
  have hsr' : ENNReal.ofReal (s / r) ≤ 1 := ENNReal.ofReal_le_one.2 ((div_le_one hr).2 hsr.le)
  have htri : ‖b' - a‖ₑ ≤ ‖(⨍ z in ball x R, b z ∂μ) - b'‖ₑ + ‖a - ⨍ z in ball x R, b z ∂μ‖ₑ := by
    rw [eNorm_sub_rev _ b', eNorm_sub_rev a]
    simpa only [eDist_eq_eNorm_sub] using edist_triangle b' (⨍ z in ball x R, b z ∂μ) a
  calc ENNReal.ofReal (s / r) * ‖b' - a‖ₑ
      ≤ ENNReal.ofReal (s / r) * ((k + 1 : ℕ) * 2 ^ n * vmoModulus b μ (8 * r) +
          8 ^ n * vmoModulus b μ (8 * r)) := by
        gcongr
        exact htri.trans (add_le_add hdrift hfar)
    _ = ENNReal.ofReal (s / r) * (k + 1 : ℕ) * (2 ^ n * vmoModulus b μ (8 * r)) +
          ENNReal.ofReal (s / r) * (8 ^ n * vmoModulus b μ (8 * r)) := by ring
    _ ≤ 8 * (2 ^ n * vmoModulus b μ (8 * r)) + 1 * (8 ^ n * vmoModulus b μ (8 * r)) := by
        gcongr
    _ = (2 ^ (n + 3) + 8 ^ n) * vmoModulus b μ (8 * r) := by ring

/-- On a ball `B = B(x, s)` with `s < r` and centre in `B(c, 3 r)`, the extension stays within
`(1 + 2ⁿ⁺³ + 8ⁿ) η_b(8 r)` on average of the constant `φ(x) • (b_B - a) + a`. -/
private theorem setLAverage_enorm_ballExtension_sub_le_of_lt {b : E → F}
    (hb : LocallyIntegrable b μ) {c x : E} {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (hsr : s < r)
    (hx : dist x c < 3 * r) :
    ⨍⁻ y in ball x s, ‖ballExtension μ b hr c y -
        (ballCutoff hr c x • ((⨍ z in ball x s, b z ∂μ) - ⨍ z in ball c r, b z ∂μ) +
          ⨍ z in ball c r, b z ∂μ)‖ₑ ∂μ ≤
      (1 + 2 ^ (finrank ℝ E + 3) + 8 ^ finrank ℝ E) * vmoModulus b μ (8 * r) := by
  set n := finrank ℝ E
  set a := ⨍ z in ball c r, b z ∂μ
  set b' := ⨍ z in ball x s, b z ∂μ
  -- The pointwise comparison on `B(x, s)`.
  have hpt : ∀ y ∈ ball x s, ‖ballExtension μ b hr c y - (ballCutoff hr c x • (b' - a) + a)‖ₑ ≤
      ‖b y - b'‖ₑ + ENNReal.ofReal (s / r) * ‖b' - a‖ₑ := by
    intro y hy
    have heq : ballExtension μ b hr c y - (ballCutoff hr c x • (b' - a) + a) =
        ballCutoff hr c y • (b y - b') + (ballCutoff hr c y - ballCutoff hr c x) • (b' - a) := by
      simp only [ballExtension, a]
      module
    rw [heq]
    refine (eNorm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [eNorm_smul]
      refine mul_le_of_le_one_left' ?_
      rw [Real.eNorm_eq_ofReal (ballCutoff_nonneg hr c y)]
      exact ENNReal.ofReal_le_one.2 (ballCutoff_le_one hr c y)
    · rw [eNorm_smul, Real.eNorm_eq_ofReal_abs]
      gcongr
      exact (abs_ballCutoff_sub_le hr c x y).trans
        (div_le_div_of_nonneg_right (mem_ball.1 hy).le hr.le)
  calc ⨍⁻ y in ball x s, ‖ballExtension μ b hr c y - (ballCutoff hr c x • (b' - a) + a)‖ₑ ∂μ
      ≤ ⨍⁻ y in ball x s, (‖b y - b'‖ₑ + ENNReal.ofReal (s / r) * ‖b' - a‖ₑ) ∂μ :=
        laverage_mono_ae ((ae_restrict_mem measurableSet_ball).mono hpt)
    _ ≤ ⨍⁻ y in ball x s, ‖b y - b'‖ₑ ∂μ + ENNReal.ofReal (s / r) * ‖b' - a‖ₑ :=
        laverage_add_const_le _ _
    _ ≤ vmoModulus b μ (8 * r) + (2 ^ (n + 3) + 8 ^ n) * vmoModulus b μ (8 * r) :=
        add_le_add (setLAverage_enorm_sub_setAverage_le_vmoModulus b μ x (by linarith))
          (ofReal_div_mul_enorm_setAverage_sub_setAverage_le hb.aestronglyMeasurable hr hs hsr hx)
    _ = (1 + 2 ^ (n + 3) + 8 ^ n) * vmoModulus b μ (8 * r) := by ring

omit [NormedSpace ℝ E] [BorelSpace E] [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure]
  [CompleteSpace F] in
/-- On a ball `B = B(x, s)` with `s < r` and centre off `B(c, 3 r)`, the extension is the constant
`a`. -/
private theorem ballExtension_eq_of_le_dist {b : E → F} {c x : E} {r s : ℝ} (hr : 0 < r)
    (hsr : s < r) (hx : 3 * r ≤ dist x c) {y : E} (hy : y ∈ ball x s) :
    ballExtension μ b hr c y = ⨍ z in ball c r, b z ∂μ := by
  have hy' : y ∉ ball c (2 * r) := by
    rw [mem_ball, not_lt]
    linarith [dist_triangle x y c, dist_comm x y, mem_ball.1 hy]
  rw [ballExtension, ballCutoff_eq_zero hr hy', zero_smul, zero_add]

/-- On every ball `B(x, s)`, the extension stays within `(1 + 2ⁿ⁺³ + 8ⁿ) η_b(8 r)` on average of
some constant. -/
private theorem exists_setLAverage_enorm_ballExtension_sub_le {b : E → F}
    (hb : LocallyIntegrable b μ) {c x : E} {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    ∃ m : F, ⨍⁻ y in ball x s, ‖ballExtension μ b hr c y - m‖ₑ ∂μ ≤
      (1 + 2 ^ (finrank ℝ E + 3) + 8 ^ finrank ℝ E) * vmoModulus b μ (8 * r) := by
  set n := finrank ℝ E
  set a := ⨍ z in ball c r, b z ∂μ
  set K : ℝ≥0∞ := 1 + 2 ^ (n + 3) + 8 ^ n
  rcases le_or_gt r s with hrs | hsr
  · -- Large balls.
    refine ⟨a, (setLAverage_enorm_ballExtension_sub_le_of_le hb c hr hrs x).trans ?_⟩
    calc 2 ^ n * ((1 + 2 ^ n) * vmoModulus b μ (2 * r))
        = (2 ^ n + 4 ^ n) * vmoModulus b μ (2 * r) := by
          rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num, mul_pow]
          ring
      _ ≤ K * vmoModulus b μ (8 * r) := by
          gcongr ?_ * ?_
          · calc (2 : ℝ≥0∞) ^ n + 4 ^ n ≤ 2 ^ (n + 3) + 8 ^ n := by
                  gcongr
                  · exact one_le_two
                  · omega
                  · norm_num
              _ ≤ K := by simp only [K, add_assoc]; exact le_add_self
          · exact monotone_vmoModulus b μ (by linarith)
  rcases lt_or_ge (dist x c) (3 * r) with hx | hx
  · -- Small balls near `B(c, 2 r)`.
    exact ⟨_, setLAverage_enorm_ballExtension_sub_le_of_lt hb hr hs hsr hx⟩
  · -- Small balls far from `B(c, 2 r)`, on which the extension is constant.
    refine ⟨a, (laverage_mono_ae (g := fun _ => 0) ?_).trans (by simp)⟩
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    rw [ballExtension_eq_of_le_dist hr hsr hx hy, sub_self, eNorm_zero]


/-! ### The extension -/

/-- **Extension from a ball with control of the mean oscillation.** Let `b` be locally integrable
on a real normed space of finite dimension `n` with an additive Haar measure. For every ball
`B(c, r)`, there is a locally integrable `g` equal to `b` on `B(c, r)`, equal to the average of
`b` over `B(c, r)` off `B(c, 2 r)`, and with BMO seminorm at most `2 (1 + 2ⁿ⁺³ + 8ⁿ) η_b(8 r)`,
where `η_b` is the VMO modulus of `b`. -/
theorem exists_eqOn_ball_and_bmoSeminorm_le_vmoModulus {b : E → F} (hb : LocallyIntegrable b μ)
    (c : E) (r : ℝ) :
    ∃ g : E → F, LocallyIntegrable g μ ∧ EqOn g b (ball c r) ∧
      EqOn g (fun _ => ⨍ z in ball c r, b z ∂μ) (ball c (2 * r))ᶜ ∧
      bmoSeminorm g μ ≤
        2 * (1 + 2 ^ (finrank ℝ E + 3) + 8 ^ finrank ℝ E) * vmoModulus b μ (8 * r) := by
  set n := finrank ℝ E
  set a := ⨍ z in ball c r, b z ∂μ
  set K : ℝ≥0∞ := 1 + 2 ^ (n + 3) + 8 ^ n
  rcases le_or_gt r 0 with hr | hr
  · -- The ball is empty, and the constant `a` works.
    refine ⟨fun _ => a, locallyIntegrable_const a, by simp [ball_eq_empty.2 hr], fun _ _ => rfl,
      ?_⟩
    rw [bmoSeminorm_const]
    exact zero_le
  have hloc : LocallyIntegrable (ballExtension μ b hr c) μ :=
    ((hb.sub (locallyIntegrable_const a)).continuous_smul (continuous_ballCutoff hr c)).add
      (locallyIntegrable_const a)
  refine ⟨ballExtension μ b hr c, hloc, fun y hy => ?_, fun y hy => ?_,
    bmoSeminorm_le fun x s => ?_⟩
  · rw [ballExtension, ballCutoff_eq_one hr hy, one_smul, sub_add_cancel]
  · rw [ballExtension, ballCutoff_eq_zero hr hy, zero_smul, zero_add]
  rcases le_or_gt s 0 with hs | hs
  · simp [ball_eq_empty.2 hs]
  have hint : IntegrableOn (ballExtension μ b hr c) (ball x s) μ :=
    (hloc.integrableOn_isCompact (isCompact_closedBall x s)).mono_set ball_subset_closedBall
  -- The mean oscillation about the average is at most twice the mean distance from a constant.
  obtain ⟨m, hm⟩ := exists_setLAverage_enorm_ballExtension_sub_le hb (c := c) hr hs (x := x)
  calc _ ≤ 2 * ⨍⁻ y in ball x s, ‖ballExtension μ b hr c y - m‖ₑ ∂μ :=
        setLAverage_enorm_sub_setAverage_le hint m
    _ ≤ 2 * (K * vmoModulus b μ (8 * r)) := by gcongr
    _ = 2 * K * vmoModulus b μ (8 * r) := (mul_assoc _ _ _).symm

end TauCeti
