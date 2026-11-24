/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.BoundedMeanOscillation
import Mathlib.Analysis.Convex.Integral
import TauCeti.Analysis.Normed.Group.Basic
import TauCeti.Analysis.SpecialFunctions.Ramp

/-!
# Localizing a function to a ball in BMO

Let `μ` be an additive Haar measure on a real normed space `E` of finite dimension `n`, and let
`b : E → F` be locally integrable. Multiplying `b` minus its average over a ball `B(x₀, R)` by a
cutoff `ψ` that vanishes off that ball gives a function

`b' = ψ • (b - b_{B(x₀, R)})`

whose BMO seminorm is controlled by the mean oscillation of `b` on balls of radius at most `8 R`
alone: if `ψ` is `K`-Lipschitz and bounded by `L`, then

`‖b'‖_{BMO} ≤ 2 (L + 5 · 8ⁿ K R) η_b(8 R)`

(`TauCeti.bmoSeminorm_smul_sub_setAverage_le`), where `η_b` is the VMO modulus. Where `ψ = 1`, the
function `b'` is `b` up to an additive constant. This is how a statement about functions of
bounded mean oscillation is localized: an estimate in terms of `‖b'‖_{BMO}` becomes, near `x₀`, an
estimate in terms of `η_b(8 R)`, which is small for small `R` when `b` has vanishing mean
oscillation. In particular commutators `[b, T]` of singular integrals restricted to a small ball
are small for such `b`.

## The argument

On a ball `B(c, s)` with `s ≥ R`, the mean oscillation of `b'` is at most twice its mean size,
which is at most `L` times the mean oscillation of `b` on `B(x₀, R)`. On a ball `B(c, s)` with
`s < R` meeting the support of `ψ`, compare `b'` with the constant
`ψ(c) (b_{B(c, s)} - b_{B(x₀, R)})`: the error is at most
`L |b - b_{B(c, s)}| + K s |b_{B(c, s)} - b_{B(x₀, R)}|`. The averages of `b` over the concentric
balls `B(c, 2ʲ s)` drift by at most `2ⁿ η_b` per doubling, so
`|b_{B(c, s)} - b_{B(x₀, R)}|` grows only like `log (R / s)`, and the factor `s` absorbs it.

Taking for `ψ` the ramp from `1` on `B(x₀, r)` to `0` off `B(x₀, 2 r)` shows that `b` agrees on
`B(x₀, r)`, up to a constant, with an integrable function of BMO seminorm at most
`(2 + 20 · 8ⁿ) η_b(16 r)` (`MeasureTheory.LocallyIntegrable.exists_bmoSeminorm_le_and_eqOn`).
Adding the constant back gives `ψ b + (1 - ψ) b_{B(x₀, 2 r)}`, which agrees with `b` on `B(x₀, r)`
and takes its values in every closed convex set containing the values of `b` on `B(x₀, 2 r)`
(`MeasureTheory.LocallyIntegrable.exists_forall_mem_and_bmoSeminorm_le_and_eqOn`). For a field of
coefficient matrices and the closed convex set of uniformly elliptic matrices, this extends a
field of small mean oscillation on small balls from a ball to the whole space, keeping it
uniformly elliptic.

## Main declarations

* `TauCeti.bmoSeminorm_smul_sub_setAverage_le`: the BMO bound for the localized function.
* `MeasureTheory.LocallyIntegrable.exists_bmoSeminorm_le_and_eqOn`: extension from a ball, up to a
  constant, with control by the VMO modulus.
* `MeasureTheory.LocallyIntegrable.exists_forall_mem_and_bmoSeminorm_le_and_eqOn`: extension from
  a ball with values in a closed convex set, with control by the VMO modulus.

## References

* L. Grafakos, *Modern Fourier Analysis*, 3rd ed., Section 3.1 (the averages of a function of
  bounded mean oscillation over nested balls).
-/

public section

namespace TauCeti

open MeasureTheory Metric Set
open scoped ENNReal NNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] {μ : Measure E} [μ.IsAddHaarMeasure] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [CompleteSpace F]

/-- If `B(x₀, R) ⊆ B(c, ρ)` with `ρ ≤ 8 R`, the averages of `b` over the two balls differ by at
most `8ⁿ η_b(8 R)`. -/
private theorem enorm_setAverage_ball_sub_setAverage_ball_le_of_subset {b : E → F}
    (hb : AEStronglyMeasurable b μ) {c x₀ : E} {ρ R : ℝ} (hR : 0 < R)
    (hsub : ball x₀ R ⊆ ball c ρ) (hρ : ρ ≤ 8 * R) :
    ‖(⨍ y in ball c ρ, b y ∂μ) - ⨍ y in ball x₀ R, b y ∂μ‖ₑ ≤
      8 ^ Module.finrank ℝ E * vmoModulus b μ (8 * R) := by
  rw [eNorm_sub_rev]
  refine (enorm_setAverage_sub_le_of_subset hsub (measure_ball_pos μ x₀ hR).ne'
    measure_ball_lt_top.ne hb.restrict _).trans ?_
  have hmeas : μ (ball c ρ) ≤ 8 ^ Module.finrank ℝ E * μ (ball x₀ R) := by
    calc μ (ball c ρ) ≤ μ (ball x₀ (8 * R)) := by
          rw [μ.addHaar_ball_center c, μ.addHaar_ball_center x₀]
          exact measure_mono (ball_subset_ball hρ)
      _ = 8 ^ Module.finrank ℝ E * μ (ball x₀ R) := by
          rw [μ.addHaar_ball_mul_of_pos x₀ (by norm_num : (0 : ℝ) < 8),
            μ.addHaar_ball_center x₀, ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
  exact mul_le_mul' (ENNReal.div_le_of_le_mul hmeas)
    (setLAverage_enorm_sub_setAverage_le_vmoModulus b μ c hρ)

/-- **Averages over a small ball and a large ball.** If `0 < s ≤ R` and `dist c x₀ < 2 R`, the
averages of `b` over `B(c, s)` and over `B(x₀, R)` differ by at most a multiple of
`log (R / s) η_b(8 R)`; multiplied by `s`, this is at most `5 · 8ⁿ R η_b(8 R)`. -/
private theorem ofReal_mul_enorm_setAverage_ball_sub_le {b : E → F}
    (hb : AEStronglyMeasurable b μ) {c x₀ : E} {s R : ℝ} (hs : 0 < s) (hsR : s ≤ R)
    (hc : dist c x₀ < 2 * R) :
    ENNReal.ofReal s * ‖(⨍ y in ball c s, b y ∂μ) - ⨍ y in ball x₀ R, b y ∂μ‖ₑ ≤
      5 * 8 ^ Module.finrank ℝ E * ENNReal.ofReal R * vmoModulus b μ (8 * R) := by
  set n := Module.finrank ℝ E
  set η := vmoModulus b μ (8 * R)
  -- The dyadic multiple `ρ = 2ʲ⁺¹ s` of `s` in `(4 R, 8 R]`.
  obtain ⟨j, hj, hj'⟩ := exists_nat_pow_near (x := 4 * R / s) (y := (2 : ℝ))
    ((one_le_div hs).2 (by linarith)) one_lt_two
  have hj4 := (le_div_iff₀ hs).1 hj
  have hρ4 : 4 * R < 2 ^ (j + 1) * s := (div_lt_iff₀ hs).1 hj'
  have hρ8 : 2 ^ (j + 1) * s ≤ 8 * R := by rw [pow_succ]; linarith
  -- From `B(c, s)` to `B(c, 2ʲ⁺¹ s)` by doubling, then to `B(x₀, R) ⊆ B(c, 2ʲ⁺¹ s)`.
  have hchain : ‖(⨍ y in ball c s, b y ∂μ) - ⨍ y in ball c (2 ^ (j + 1) * s), b y ∂μ‖ₑ ≤
      (j + 1) * 2 ^ n * η := by
    rw [eNorm_sub_rev]
    refine (enorm_setAverage_ball_sub_setAverage_ball_le_vmoModulus hb c hs (j + 1)).trans ?_
    push_cast
    gcongr
    exact monotone_vmoModulus b μ hρ8
  have hbig := enorm_setAverage_ball_sub_setAverage_ball_le_of_subset hb (hs.trans_le hsR)
    (ball_subset_ball' (by rw [dist_comm]; linarith)) hρ8 (c := c) (x₀ := x₀)
  -- The factor `s` absorbs the number `j + 1 ≤ 2ʲ ≤ 4 R / s` of doublings.
  have hs' : ENNReal.ofReal s * (j + 1) ≤ 4 * ENNReal.ofReal R := by
    have h1 : ((j + 1 : ℕ) : ℝ) ≤ 2 ^ j := by exact_mod_cast Nat.lt_two_pow_self
    push_cast at h1
    rw [← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_mul (by norm_num),
      show ((j : ℝ≥0∞) + 1) = ENNReal.ofReal (j + 1) by
        rw [ENNReal.ofReal_add (by positivity) zero_le_one, ENNReal.ofReal_natCast,
          ENNReal.ofReal_one],
      ← ENNReal.ofReal_mul hs.le]
    exact ENNReal.ofReal_le_ofReal (by nlinarith)
  have h28 : (2 : ℝ≥0∞) ^ n ≤ 8 ^ n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
  calc ENNReal.ofReal s * ‖(⨍ y in ball c s, b y ∂μ) - ⨍ y in ball x₀ R, b y ∂μ‖ₑ
      ≤ ENNReal.ofReal s * ((j + 1) * 2 ^ n * η + 8 ^ n * η) := by
        gcongr
        exact (eNorm_sub_le_eNorm_sub_add_eNorm_sub _ _ _).trans (add_le_add hchain hbig)
    _ = ENNReal.ofReal s * (j + 1) * 2 ^ n * η + ENNReal.ofReal s * 8 ^ n * η := by ring
    _ ≤ 4 * ENNReal.ofReal R * 8 ^ n * η + ENNReal.ofReal R * 8 ^ n * η := by
        gcongr
    _ = 5 * 8 ^ n * ENNReal.ofReal R * η := by ring

variable {b : E → F} {ψ : E → ℝ} {K L : ℝ≥0} {x₀ c : E} {R s : ℝ}

omit [CompleteSpace F] in
/-- A Lipschitz `ψ` vanishing off `B(x₀, R)` has compact support, so `ψ • (b - κ)` is integrable
for a locally integrable `b` and a constant `κ`. -/
private theorem integrable_smul_sub_of_lipschitzWith (hb : LocallyIntegrable b μ)
    (hψ : LipschitzWith K ψ) (hψ0 : ∀ x, R ≤ dist x x₀ → ψ x = 0) (κ : F) :
    Integrable (fun x => ψ x • (b x - κ)) μ :=
  (hb.sub (locallyIntegrable_const κ)).integrable_smul_left_of_hasCompactSupport hψ.continuous
    (HasCompactSupport.intro (isCompact_closedBall x₀ R) fun x hx =>
      hψ0 x (not_le.1 (by simpa using hx)).le)

/-- The mean oscillation of `ψ • (b - b_{B(x₀, R)})` on a ball `B(c, s)` of radius `s ≥ R`. -/
private theorem setLAverage_enorm_smul_sub_le_of_le
    (hint : Integrable (fun x => ψ x • (b x - ⨍ y in ball x₀ R, b y ∂μ)) μ)
    (hψL : ∀ x, ‖ψ x‖ₑ ≤ L) (hψ0 : ∀ x, R ≤ dist x x₀ → ψ x = 0) (hRs : R ≤ s) :
    ⨍⁻ x in ball c s, ‖ψ x • (b x - ⨍ y in ball x₀ R, b y ∂μ) -
        ⨍ z in ball c s, ψ z • (b z - ⨍ y in ball x₀ R, b y ∂μ) ∂μ‖ₑ ∂μ ≤
      2 * (L * vmoModulus b μ R) := by
  set κ := ⨍ y in ball x₀ R, b y ∂μ
  -- The mean oscillation is at most twice the mean size, which only sees `B(x₀, R)`.
  refine (setLAverage_enorm_sub_setAverage_le hint.integrableOn 0).trans ?_
  have hpt (x : E) : ‖ψ x • (b x - κ) - 0‖ₑ ≤
      (ball x₀ R).indicator (fun x => L * ‖b x - κ‖ₑ) x := by
    by_cases hx : x ∈ ball x₀ R
    · rw [sub_zero, indicator_of_mem hx, eNorm_smul]
      gcongr
      exact hψL x
    · simp [indicator_of_notMem hx, hψ0 x (not_lt.1 hx)]
  have hlint : ∫⁻ x in ball c s, ‖ψ x • (b x - κ) - 0‖ₑ ∂μ ≤
      L * vmoModulus b μ R * μ (ball c s) := by
    calc ∫⁻ x in ball c s, ‖ψ x • (b x - κ) - 0‖ₑ ∂μ
        ≤ ∫⁻ x, (ball x₀ R).indicator (fun x => L * ‖b x - κ‖ₑ) x ∂μ :=
          setLIntegral_le_lintegral _ _ |>.trans' (lintegral_mono hpt)
      _ = L * (μ (ball x₀ R) * ⨍⁻ x in ball x₀ R, ‖b x - κ‖ₑ ∂μ) := by
          rw [lintegral_indicator measurableSet_ball, lintegral_const_mul' _ _ (by simp),
            measure_mul_setLAverage _ measure_ball_lt_top.ne]
      _ ≤ L * (μ (ball c s) * vmoModulus b μ R) := by
          have hμ : μ (ball x₀ R) ≤ μ (ball c s) := by
            rw [μ.addHaar_ball_center x₀, μ.addHaar_ball_center c]
            exact measure_mono (ball_subset_ball hRs)
          exact mul_le_mul' le_rfl (mul_le_mul' hμ
            (setLAverage_enorm_sub_setAverage_le_vmoModulus b μ x₀ le_rfl))
      _ = L * vmoModulus b μ R * μ (ball c s) := by ring
  rw [setLAverage_eq]
  gcongr
  exact ENNReal.div_le_of_le_mul hlint

/-- The mean oscillation of `ψ • (b - b_{B(x₀, R)})` on a ball `B(c, s)` of radius `0 < s < R`. -/
private theorem setLAverage_enorm_smul_sub_le_of_lt
    (hint : Integrable (fun x => ψ x • (b x - ⨍ y in ball x₀ R, b y ∂μ)) μ)
    (hb : AEStronglyMeasurable b μ) (hψ : LipschitzWith K ψ) (hψL : ∀ x, ‖ψ x‖ₑ ≤ L)
    (hψ0 : ∀ x, R ≤ dist x x₀ → ψ x = 0) (hs : 0 < s) (hsR : s < R) :
    ⨍⁻ x in ball c s, ‖ψ x • (b x - ⨍ y in ball x₀ R, b y ∂μ) -
        ⨍ z in ball c s, ψ z • (b z - ⨍ y in ball x₀ R, b y ∂μ) ∂μ‖ₑ ∂μ ≤
      2 * ((L + 5 * 8 ^ Module.finrank ℝ E * K * ENNReal.ofReal R) *
        vmoModulus b μ (8 * R)) := by
  set κ := ⨍ y in ball x₀ R, b y ∂μ
  set m := ⨍ y in ball c s, b y ∂μ
  -- Compare with the constant `ψ c • (b_{B(c, s)} - κ)`.
  refine (setLAverage_enorm_sub_setAverage_le hint.integrableOn (ψ c • (m - κ))).trans ?_
  gcongr 2 * ?_
  rcases le_or_gt (2 * R) (dist c x₀) with hfar | hnear
  · -- The ball does not meet the support of `ψ`.
    have hzero (x : E) (hx : x ∈ ball c s) : ψ x = 0 :=
      hψ0 x (by have := dist_triangle c x x₀; rw [mem_ball'] at hx; linarith)
    rw [setLAverage_congr_fun measurableSet_ball (g := fun _ => 0) fun x hx => by
      simp [hzero x hx, hψ0 c (by linarith)]]
    simp
  have hpt : ∀ x ∈ ball c s, ‖ψ x • (b x - κ) - ψ c • (m - κ)‖ₑ ≤
      L * ‖b x - m‖ₑ + K * ENNReal.ofReal s * ‖m - κ‖ₑ := fun x hx => by
    rw [show ψ x • (b x - κ) - ψ c • (m - κ) = ψ x • (b x - m) + (ψ x - ψ c) • (m - κ) by
      simp only [smul_sub, sub_smul]; abel]
    refine (eNorm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [eNorm_smul]; gcongr; exact hψL x
    · rw [eNorm_smul, ← eDist_eq_eNorm_sub]
      gcongr
      refine (hψ.edist_le_mul x c).trans ?_
      gcongr
      rw [edist_dist]
      exact ENNReal.ofReal_le_ofReal (mem_ball.1 hx).le
  have h0 : μ (ball c s) ≠ 0 := (measure_ball_pos μ c hs).ne'
  calc ⨍⁻ x in ball c s, ‖ψ x • (b x - κ) - ψ c • (m - κ)‖ₑ ∂μ
      ≤ ⨍⁻ x in ball c s, (L * ‖b x - m‖ₑ + K * ENNReal.ofReal s * ‖m - κ‖ₑ) ∂μ :=
        laverage_mono_ae ((ae_restrict_iff' measurableSet_ball).2 (.of_forall hpt))
    _ = L * ⨍⁻ x in ball c s, ‖b x - m‖ₑ ∂μ + K * ENNReal.ofReal s * ‖m - κ‖ₑ := by
        rw [setLAverage_eq, setLAverage_eq, lintegral_add_right _ measurable_const,
          lintegral_const_mul' _ _ (by simp), setLIntegral_const, ENNReal.add_div,
          mul_div_assoc, ENNReal.mul_div_cancel_right h0 measure_ball_lt_top.ne]
    _ ≤ L * vmoModulus b μ (8 * R) +
          K * (5 * 8 ^ Module.finrank ℝ E * ENNReal.ofReal R * vmoModulus b μ (8 * R)) := by
        rw [mul_assoc (K : ℝ≥0∞)]
        exact add_le_add (mul_le_mul' le_rfl
          (setLAverage_enorm_sub_setAverage_le_vmoModulus b μ c (by linarith)))
          (mul_le_mul' le_rfl (ofReal_mul_enorm_setAverage_ball_sub_le hb hs hsR.le hnear))
    _ = (L + 5 * 8 ^ Module.finrank ℝ E * K * ENNReal.ofReal R) * vmoModulus b μ (8 * R) := by
        ring

/-- **Localizing a function to a ball in BMO.** Let `ψ : E → ℝ` be `K`-Lipschitz, bounded by `L`
and zero off the ball `B(x₀, R)`. For a locally integrable `b`, the function
`ψ • (b - b_{B(x₀, R)})` has BMO seminorm at most `2 (L + 5 · 8ⁿ K R) η_b(8 R)`, where `n` is the
dimension of `E` and `η_b` the VMO modulus of `b`. -/
theorem bmoSeminorm_smul_sub_setAverage_le (hb : LocallyIntegrable b μ) (hψ : LipschitzWith K ψ)
    (hψL : ∀ x, ‖ψ x‖ ≤ L) (hψ0 : ∀ x, R ≤ dist x x₀ → ψ x = 0) :
    bmoSeminorm (fun x => ψ x • (b x - ⨍ y in ball x₀ R, b y ∂μ)) μ ≤
      2 * (L + 5 * 8 ^ Module.finrank ℝ E * K * ENNReal.ofReal R) * vmoModulus b μ (8 * R) := by
  rcases le_or_gt R 0 with hR | hR
  · -- For `R ≤ 0` the cutoff vanishes identically.
    have : (fun x => ψ x • (b x - ⨍ y in ball x₀ R, b y ∂μ)) = 0 :=
      funext fun x => by simp [hψ0 x (hR.trans dist_nonneg)]
    rw [this, bmoSeminorm_zero]
    exact zero_le
  have hψL' (x : E) : ‖ψ x‖ₑ ≤ L := by
    rw [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal (hψL x)
  have hint := integrable_smul_sub_of_lipschitzWith hb hψ hψ0 (⨍ y in ball x₀ R, b y ∂μ)
  refine bmoSeminorm_le fun c s => ?_
  rcases le_or_gt s 0 with hs | hs
  · simp [ball_eq_empty.2 hs]
  rw [mul_assoc]
  rcases le_or_gt R s with hRs | hsR
  · refine (setLAverage_enorm_smul_sub_le_of_le hint hψL' hψ0 hRs).trans ?_
    gcongr 2 * ?_
    exact mul_le_mul' le_self_add (monotone_vmoModulus b μ (by linarith))
  · exact setLAverage_enorm_smul_sub_le_of_lt hint hb.aestronglyMeasurable hψ hψL' hψ0 hs hsR

/-- The ramp from `1` on `B(x₀, r)` to `0` off `B(x₀, 2 r)`. -/
private noncomputable def ballRamp (x₀ : E) (r : ℝ) (y : E) : ℝ :=
  ramp (-(2 * r)) r (-dist y x₀)

omit [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
private theorem lipschitzWith_ballRamp (x₀ : E) (r : ℝ) : LipschitzWith ‖r‖₊⁻¹ (ballRamp x₀ r) := by
  have h := (lipschitzWith_ramp (-(2 * r)) r).comp
    (lipschitzWith_neg_iff.2 (LipschitzWith.dist_left x₀))
  rw [mul_one] at h
  exact h

omit [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
private theorem ballRamp_mem_Icc (x₀ : E) (r : ℝ) (y : E) : ballRamp x₀ r y ∈ Icc 0 1 :=
  ⟨ramp_nonneg _ _ _, ramp_le_one _ _ _⟩

omit [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
private theorem ballRamp_eq_zero (hr : 0 < r) {y : E} (hy : 2 * r ≤ dist y x₀) :
    ballRamp x₀ r y = 0 :=
  ramp_eq_zero hr.le (by linarith)

omit [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
private theorem ballRamp_eq_one (hr : 0 < r) {y : E} (hy : y ∈ ball x₀ r) :
    ballRamp x₀ r y = 1 :=
  ramp_eq_one hr (by rw [mem_ball] at hy; linarith)

/-- The cutoff of `b` minus its average over `B(x₀, 2 r)` by the ramp from `1` on `B(x₀, r)` to
`0` off `B(x₀, 2 r)` is integrable, with BMO seminorm at most `(2 + 20 · 8ⁿ) η_b(16 r)`. -/
private theorem integrable_ballRamp_smul_sub_and_bmoSeminorm_le (hb : LocallyIntegrable b μ)
    (hr : 0 < r) :
    Integrable (fun y => ballRamp x₀ r y • (b y - ⨍ z in ball x₀ (2 * r), b z ∂μ)) μ ∧
      bmoSeminorm (fun y => ballRamp x₀ r y • (b y - ⨍ z in ball x₀ (2 * r), b z ∂μ)) μ ≤
        (2 + 20 * 8 ^ Module.finrank ℝ E) * vmoModulus b μ (16 * r) := by
  have hψ1 (y : E) : ‖ballRamp x₀ r y‖ ≤ (1 : ℝ≥0) := by
    rw [Real.norm_of_nonneg (ballRamp_mem_Icc x₀ r y).1]
    exact (ballRamp_mem_Icc x₀ r y).2
  have hψ0 (y : E) (hy : 2 * r ≤ dist y x₀) : ballRamp x₀ r y = 0 := ballRamp_eq_zero hr hy
  refine ⟨integrable_smul_sub_of_lipschitzWith hb (lipschitzWith_ballRamp x₀ r) hψ0 _,
    (bmoSeminorm_smul_sub_setAverage_le hb (lipschitzWith_ballRamp x₀ r) hψ1 hψ0).trans_eq ?_⟩
  have hKR : ((‖r‖₊⁻¹ : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal (2 * r) = 2 := by
    have hinv : ((‖r‖₊⁻¹ : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal r⁻¹ := by
      rw [← ENNReal.ofReal_coe_nnreal]
      simp [abs_of_pos hr]
    rw [hinv, ← ENNReal.ofReal_mul (inv_nonneg.2 hr.le),
      show r⁻¹ * (2 * r) = 2 by field_simp, ENNReal.ofReal_ofNat]
  rw [show 8 * (2 * r) = 16 * r by ring, mul_assoc _ ((‖r‖₊⁻¹ : ℝ≥0) : ℝ≥0∞), hKR]
  push_cast
  ring

/-- **Extension from a ball in BMO.** A locally integrable `b` agrees on the ball `B(x₀, r)`, up
to an additive constant, with an integrable function whose BMO seminorm is at most
`(2 + 20 · 8ⁿ) η_b(16 r)`, where `n` is the dimension of `E` and `η_b` the VMO modulus of `b`. -/
theorem _root_.MeasureTheory.LocallyIntegrable.exists_bmoSeminorm_le_and_eqOn
    (hb : LocallyIntegrable b μ) (x₀ : E) (r : ℝ) :
    ∃ (b' : E → F) (c : F), Integrable b' μ ∧
      bmoSeminorm b' μ ≤ (2 + 20 * 8 ^ Module.finrank ℝ E) * vmoModulus b μ (16 * r) ∧
      EqOn b' (fun y => b y - c) (ball x₀ r) := by
  rcases le_or_gt r 0 with hr | hr
  · exact ⟨0, 0, integrable_zero _ _ _, by simp, by simp [ball_eq_empty.2 hr]⟩
  obtain ⟨hint, hbmo⟩ := integrable_ballRamp_smul_sub_and_bmoSeminorm_le (x₀ := x₀) hb hr
  refine ⟨_, ⨍ z in ball x₀ (2 * r), b z ∂μ, hint, hbmo, fun y hy => ?_⟩
  simp only [ballRamp_eq_one hr hy, one_smul]

/-- **Extension from a ball inside a closed convex set.** Let `b` be locally integrable, with
values in a closed convex set `S` on the ball `B(x₀, 2 r)`, `r > 0`. Then `b` agrees on `B(x₀, r)`
with a locally integrable function with values in `S` everywhere, whose BMO seminorm is at most
`(2 + 20 · 8ⁿ) η_b(16 r)`, where `n` is the dimension of `E` and `η_b` the VMO modulus of `b`. The
function is `ψ b + (1 - ψ) b_{B(x₀, 2 r)}` for the ramp `ψ` from `1` on `B(x₀, r)` to `0` off
`B(x₀, 2 r)`. -/
theorem _root_.MeasureTheory.LocallyIntegrable.exists_forall_mem_and_bmoSeminorm_le_and_eqOn
    {S : Set F} (hS : Convex ℝ S) (hSc : IsClosed S) (hb : LocallyIntegrable b μ) (hr : 0 < r)
    (hbS : ∀ y ∈ ball x₀ (2 * r), b y ∈ S) :
    ∃ b' : E → F, LocallyIntegrable b' μ ∧ (∀ y, b' y ∈ S) ∧
      bmoSeminorm b' μ ≤ (2 + 20 * 8 ^ Module.finrank ℝ E) * vmoModulus b μ (16 * r) ∧
      EqOn b' b (ball x₀ r) := by
  set b₀ := ⨍ z in ball x₀ (2 * r), b z ∂μ
  have hb₀ : b₀ ∈ S :=
    Convex.set_average_mem hS hSc (measure_ball_pos μ x₀ (by positivity)).ne'
      measure_ball_lt_top.ne ((ae_restrict_iff' measurableSet_ball).2 (ae_of_all _ hbS))
      ((hb.integrableOn_isCompact (isCompact_closedBall x₀ (2 * r))).mono_set
        ball_subset_closedBall)
  obtain ⟨hint, hbmo⟩ := integrable_ballRamp_smul_sub_and_bmoSeminorm_le (x₀ := x₀) hb hr
  refine ⟨fun y => ballRamp x₀ r y • (b y - b₀) + b₀, hint.locallyIntegrable.add
    (locallyIntegrable_const b₀), fun y => ?_, ?_, fun y hy => ?_⟩
  · -- `ψ (b - b₀) + b₀ = ψ b + (1 - ψ) b₀` is a convex combination of points of `S`.
    dsimp only
    by_cases hy : y ∈ ball x₀ (2 * r)
    · have e : ballRamp x₀ r y • (b y - b₀) + b₀ =
          ballRamp x₀ r y • b y + (1 - ballRamp x₀ r y) • b₀ := by module
      have h01 := ballRamp_mem_Icc x₀ r y
      rw [e]
      exact hS (hbS y hy) hb₀ h01.1 (by linarith [h01.2]) (by ring)
    · rw [ballRamp_eq_zero hr (not_lt.1 (by simpa [mem_ball] using hy)), zero_smul, zero_add]
      exact hb₀
  · rw [bmoSeminorm_add_const hint.aestronglyMeasurable b₀]
    exact hbmo
  · simp only [ballRamp_eq_one hr hy, one_smul, sub_add_cancel]

end TauCeti
