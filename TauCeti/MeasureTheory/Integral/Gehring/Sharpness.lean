/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.Analysis.SpecialFunctions.Pow.NNReal
import TauCeti.MeasureTheory.Integral.NormRpow

/-!
# Power weights and the sharpness of Gehring's lemma

Let `E` be a real normed space of finite dimension `d ≥ 1` with an additive Haar measure `μ`.
Gehring's lemma (`TauCeti.exists_setLAverage_rpow_add_le`) says that a function satisfying the
reverse Hölder inequality

`⨍_{B(y, ρ)} g ^ q ≤ b (⨍_{B(y, 2ρ)} g) ^ q`

on all balls is integrable to a higher power `q + δ`, for every `δ` up to a gain `δ₀ > 0`
depending on `d`, `q` and `b`. This file shows that the gain cannot be chosen independently of
the constant `b`: it tends to zero as `b` grows.

The witnesses are the power weights `g(x) = ‖x‖ ^ (-a)` with `0 ≤ a q < d`. Such a weight
satisfies the reverse Hölder inequality on every ball, with the constant `d 4ᵈ / (d - a q)`
(`TauCeti.setLAverage_ball_enorm_rpow_neg_rpow_le`), which blows up as `a q ↑ d`. But `g ^ p` is
integrable near the origin exactly when `a p < d`
(`TauCeti.integrableOn_norm_rpow_ball_iff`), so Gehring's conclusion fails at every gain `δ`
with `a (q + δ) ≥ d`. The weight with `a (q + δ) = d` has the constant `4ᵈ (q + δ) / δ`, so
this bounds every admissible gain: if Gehring's conclusion holds with the constant `b > 4ᵈ` and
the gain `δ`, then

`δ < q 4ᵈ / (b - 4ᵈ)`

(`TauCeti.lt_div_sub_of_forall_setLAverage_rpow_add_le`). In particular no single `δ > 0` serves
every `b` (`TauCeti.not_exists_forall_exists_setLAverage_rpow_add_le`). For `q = 2` and
`g = |x| ^ (-a)` on `ℝⁿ`, the reverse Hölder inequality holds for every `a < n / 2`, with a
constant that blows up as `a ↑ n / 2`, while `g ∈ L^{2 + ε}` near the origin exactly when
`(2 + ε) a < n`.

## The reverse Hölder inequality for a power weight

Fix a ball `B(y, ρ)` and put `L = ‖y‖ + 2ρ`. On `B(y, 2ρ)` the weight is at least `L ^ (-a)`, so the
right-hand side is at least `b L ^ (-a q)`. For the left-hand side there are two cases.

* If `‖y‖ ≥ 2ρ`, the ball `B(y, ρ)` stays at distance at least `L / 4` from the origin, so the
  weight is at most `4 ^ a L ^ (-a)` there.
* If `‖y‖ < 2ρ`, then `B(y, ρ)` lies in the closed ball of radius `3ρ` about the origin, and the
  exact integral of `‖x‖ ^ (-a q)` over that closed ball
  (`TauCeti.setLIntegral_closedBall_enorm_sub_rpow`), divided by the measure of
  `B(y, ρ)`, is `d 3 ^ (d - a q) ρ ^ (-a q) / (d - a q)`, while `L ≤ 4ρ`.

## References

* F. W. Gehring, *The `Lᵖ`-integrability of the partial derivatives of a quasiconformal mapping*,
  Acta Math. **130** (1973), 265–277.
* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, 2nd ed., Section 6.4.
-/

public section

namespace TauCeti

open MeasureTheory Metric Set Module
open scoped ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

omit [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure] in
/-- The upper half of the reverse Hölder inequality for `‖x‖ ^ (-s)` on a ball `B(y, ρ)` with
`‖y‖ ≥ 2ρ`, which stays away from the origin. -/
private theorem setLAverage_ball_enorm_rpow_neg_le_of_le_norm {s : ℝ} (hs : 0 ≤ s)
    (hsd : s < finrank ℝ E) {y : E} {ρ : ℝ} (hρ : 0 < ρ) (hy : 2 * ρ ≤ ‖y‖) :
    ⨍⁻ x in ball y ρ, ‖x‖ₑ ^ (-s) ∂μ ≤
      ENNReal.ofReal (finrank ℝ E * 4 ^ finrank ℝ E / (finrank ℝ E - s) *
        (‖y‖ + 2 * ρ) ^ (-s)) := by
  set d := finrank ℝ E
  set D : ℝ := (d : ℝ)
  have ht : 0 < D - s := sub_pos.2 hsd
  set L := ‖y‖ + 2 * ρ
  have hL : 0 < L := by positivity
  -- Far from the origin the weight is at most `(L / 4) ^ (-s) = 4 ^ s L ^ (-s)`.
  have hpt : ∀ x ∈ ball y ρ, ‖x‖ₑ ^ (-s) ≤ ENNReal.ofReal ((L / 4) ^ (-s)) := fun x hx => by
    rw [← ENNReal.ofReal_rpow_of_pos (by positivity), ← ofReal_norm]
    exact ENNReal.rpow_le_rpow_of_nonpos (ENNReal.ofReal_le_ofReal
      (by linarith [norm_sub_norm_le y x, mem_ball_iff_norm'.1 hx])) (neg_nonpos.2 hs)
  refine ((laverage_le_essSup _).trans (essSup_le_of_ae_le _
    ((ae_restrict_mem measurableSet_ball).mono hpt))).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [div_eq_mul_inv, Real.mul_rpow hL.le (by norm_num), Real.inv_rpow (by norm_num),
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4), inv_inv, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hL.le _)
  calc (4 : ℝ) ^ s ≤ 4 ^ D := Real.rpow_le_rpow_of_exponent_le (by norm_num) hsd.le
    _ = 4 ^ d := Real.rpow_natCast 4 d
    _ ≤ D * 4 ^ d / (D - s) := by
      rw [le_div_iff₀ ht]
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < 4) d]

/-- The real inequality closing the case `‖y‖ < 2ρ` of the reverse Hölder inequality for a power
weight: for `0 ≤ s < d` and `0 < L ≤ 4ρ`,
`d / (d - s) · (3ρ) ^ (d - s) / ρ ^ d ≤ d 4ᵈ / (d - s) · L ^ (-s)`. -/
private theorem div_mul_rpow_three_mul_div_le {s ρ L : ℝ} {d : ℕ} (hs : 0 ≤ s)
    (ht : 0 < (d : ℝ) - s) (hρ : 0 < ρ) (hL : 0 < L) (hL4 : L ≤ 4 * ρ) :
    (d : ℝ) / (d - s) * ((3 * ρ) ^ ((d : ℝ) - s) / ρ ^ d) ≤
      d * 4 ^ d / (d - s) * L ^ (-s) := by
  have hpow : (3 * ρ) ^ ((d : ℝ) - s) / ρ ^ d = 3 ^ ((d : ℝ) - s) * ρ ^ (-s) := by
    rw [Real.mul_rpow (by norm_num) hρ.le, mul_div_assoc, ← Real.rpow_natCast,
      ← Real.rpow_sub hρ]
    congr 2
    ring
  have h44 : (4 : ℝ) ^ d * (4 * ρ) ^ (-s) = 4 ^ ((d : ℝ) - s) * ρ ^ (-s) := by
    rw [Real.mul_rpow (by norm_num) hρ.le, ← mul_assoc, ← Real.rpow_natCast,
      ← Real.rpow_add (by norm_num), sub_eq_add_neg]
  have h34 : (3 : ℝ) ^ ((d : ℝ) - s) ≤ 4 ^ ((d : ℝ) - s) :=
    Real.rpow_le_rpow (by norm_num) (by norm_num) ht.le
  rw [hpow]
  calc (d : ℝ) / (d - s) * (3 ^ ((d : ℝ) - s) * ρ ^ (-s))
      ≤ d / (d - s) * (4 ^ ((d : ℝ) - s) * ρ ^ (-s)) := by
        gcongr
    _ = d * 4 ^ d / (d - s) * (4 * ρ) ^ (-s) := by
        rw [← h44]
        ring
    _ ≤ d * 4 ^ d / (d - s) * L ^ (-s) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hL hL4 (by linarith))
          (div_nonneg (by positivity) ht.le)

/-- The upper half of the reverse Hölder inequality for `‖x‖ ^ (-s)` on a ball `B(y, ρ)` with
`‖y‖ < 2ρ`, which lies in `closedBall 0 (3ρ)`. -/
private theorem setLAverage_ball_enorm_rpow_neg_le_of_norm_lt {s : ℝ} (hs : 0 ≤ s)
    (hsd : s < finrank ℝ E) {y : E} {ρ : ℝ} (hρ : 0 < ρ) (hy : ‖y‖ < 2 * ρ) :
    ⨍⁻ x in ball y ρ, ‖x‖ₑ ^ (-s) ∂μ ≤
      ENNReal.ofReal (finrank ℝ E * 4 ^ finrank ℝ E / (finrank ℝ E - s) *
        (‖y‖ + 2 * ρ) ^ (-s)) := by
  have hd0 : 0 < finrank ℝ E := by exact_mod_cast hs.trans_lt hsd
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) hd0
  set d := finrank ℝ E
  set D : ℝ := (d : ℝ)
  have ht : 0 < D - s := sub_pos.2 hsd
  set L := ‖y‖ + 2 * ρ
  have hL : 0 < L := by positivity
  -- Near the origin, `B(y, ρ) ⊆ closedBall 0 (3ρ)`, where the integral is explicit.
  have hsub : ball y ρ ⊆ closedBall (0 : E) (3 * ρ) := fun x hx => by
    rw [mem_closedBall, dist_zero_right]
    linarith [norm_le_norm_add_norm_sub' x y, mem_ball_iff_norm.1 hx]
  have hint : ∫⁻ x in ball y ρ, ‖x‖ₑ ^ (-s) ∂μ ≤
      ENNReal.ofReal (D * μ.real (ball (0 : E) 1) * ((3 * ρ) ^ (D + -s) / (D + -s))) := by
    calc ∫⁻ x in ball y ρ, ‖x‖ₑ ^ (-s) ∂μ
        ≤ ∫⁻ x in closedBall (0 : E) (3 * ρ), ‖x‖ₑ ^ (-s) ∂μ := lintegral_mono_set hsub
      _ = ∫⁻ x in closedBall (0 : E) (3 * ρ), ‖(0 : E) - x‖ₑ ^ (-s) ∂μ := by
          simp only [zero_sub, eNorm_neg]
      _ = _ := setLIntegral_closedBall_enorm_sub_rpow (by linarith) (by positivity) 0
  have hm : 0 < μ.real (ball (0 : E) 1) :=
    ENNReal.toReal_pos (measure_ball_pos μ 0 one_pos).ne' measure_ball_lt_top.ne
  have hvol : μ (ball y ρ) = ENNReal.ofReal (ρ ^ d * μ.real (ball (0 : E) 1)) := by
    rw [Measure.addHaar_ball μ y hρ.le, ENNReal.ofReal_mul (by positivity), measureReal_def,
      ENNReal.ofReal_toReal measure_ball_lt_top.ne]
  rw [setLAverage_eq, hvol]
  refine (ENNReal.div_le_div_right hint _).trans ?_
  rw [← ENNReal.ofReal_div_of_pos (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hlhs : D * μ.real (ball (0 : E) 1) * ((3 * ρ) ^ (D + -s) / (D + -s)) /
      (ρ ^ d * μ.real (ball (0 : E) 1)) = D / (D - s) * ((3 * ρ) ^ (D - s) / ρ ^ d) := by
    rw [← sub_eq_add_neg]
    field_simp
  rw [hlhs]
  exact div_mul_rpow_three_mul_div_le hs ht hρ hL (by linarith)

/-- The upper half of the reverse Hölder inequality for `‖x‖ ^ (-s)`: its average over `B(y, ρ)`
is at most `d 4ᵈ / (d - s)` times `(‖y‖ + 2ρ) ^ (-s)`. -/
private theorem setLAverage_ball_enorm_rpow_neg_le {s : ℝ} (hs : 0 ≤ s)
    (hsd : s < finrank ℝ E) (y : E) {ρ : ℝ} (hρ : 0 < ρ) :
    ⨍⁻ x in ball y ρ, ‖x‖ₑ ^ (-s) ∂μ ≤
      ENNReal.ofReal (finrank ℝ E * 4 ^ finrank ℝ E / (finrank ℝ E - s) *
        (‖y‖ + 2 * ρ) ^ (-s)) := by
  rcases le_or_gt (2 * ρ) ‖y‖ with hy | hy
  · exact setLAverage_ball_enorm_rpow_neg_le_of_le_norm hs hsd hρ hy
  · exact setLAverage_ball_enorm_rpow_neg_le_of_norm_lt hs hsd hρ hy

/-- **The reverse Hölder inequality for a power weight.** Let `E` have dimension `d`, let `a ≥ 0`
and `q ≥ 0` with `a q < d`. On every ball, the weight `g(x) = ‖x‖ ^ (-a)` satisfies

`⨍_{B(y, ρ)} g ^ q ≤ d 4ᵈ / (d - a q) · (⨍_{B(y, 2ρ)} g) ^ q`.

The constant blows up as `a q ↑ d`; at `a q = d` the left side is infinite for balls around the
origin. -/
theorem setLAverage_ball_enorm_rpow_neg_rpow_le {a q : ℝ} (ha : 0 ≤ a) (hq : 0 ≤ q)
    (haq : a * q < finrank ℝ E) (y : E) {ρ : ℝ} (hρ : 0 < ρ) :
    ⨍⁻ x in ball y ρ, (‖x‖ₑ ^ (-a)) ^ q ∂μ ≤
      ENNReal.ofReal (finrank ℝ E * 4 ^ finrank ℝ E / (finrank ℝ E - a * q)) *
        (⨍⁻ x in ball y (2 * ρ), ‖x‖ₑ ^ (-a) ∂μ) ^ q := by
  have hL : 0 < ‖y‖ + 2 * ρ := by positivity
  -- On `B(y, 2ρ)` the weight is at least `(‖y‖ + 2ρ) ^ (-a)`.
  have hlow : ENNReal.ofReal ((‖y‖ + 2 * ρ) ^ (-a)) ≤
      ⨍⁻ x in ball y (2 * ρ), ‖x‖ₑ ^ (-a) ∂μ := by
    calc ENNReal.ofReal ((‖y‖ + 2 * ρ) ^ (-a))
        = ⨍⁻ _x in ball y (2 * ρ), ENNReal.ofReal ((‖y‖ + 2 * ρ) ^ (-a)) ∂μ :=
          (setLAverage_const (measure_ball_pos μ y (by positivity)).ne'
            measure_ball_lt_top.ne _).symm
      _ ≤ ⨍⁻ x in ball y (2 * ρ), ‖x‖ₑ ^ (-a) ∂μ :=
          laverage_mono_ae ((ae_restrict_mem measurableSet_ball).mono fun x hx => by
            dsimp only
            rw [← ENNReal.ofReal_rpow_of_pos hL, ← ofReal_norm]
            exact ENNReal.rpow_le_rpow_of_nonpos (ENNReal.ofReal_le_ofReal
              (by linarith [norm_le_norm_add_norm_sub' x y, mem_ball_iff_norm.1 hx]))
              (neg_nonpos.2 ha))
  have hs : 0 ≤ a * q := mul_nonneg ha hq
  simp_rw [← ENNReal.rpow_mul, neg_mul]
  calc ⨍⁻ x in ball y ρ, ‖x‖ₑ ^ (-(a * q)) ∂μ
      ≤ ENNReal.ofReal (finrank ℝ E * 4 ^ finrank ℝ E / (finrank ℝ E - a * q) *
          (‖y‖ + 2 * ρ) ^ (-(a * q))) :=
        setLAverage_ball_enorm_rpow_neg_le hs haq y hρ
    _ = ENNReal.ofReal (finrank ℝ E * 4 ^ finrank ℝ E / (finrank ℝ E - a * q)) *
          ENNReal.ofReal ((‖y‖ + 2 * ρ) ^ (-a)) ^ q := by
        rw [ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos hL _), ← Real.rpow_mul hL.le,
          ENNReal.ofReal_mul (div_nonneg (by positivity) (sub_pos.2 haq).le), neg_mul]
    _ ≤ _ := by
        gcongr

/-- **The gain in Gehring's lemma degenerates as the constant grows.** Let `E` be nontrivial of
dimension `d`, let `q > 0`, and let `b > 4ᵈ`. Suppose that for some gain `δ > 0` and some constant
`C` the conclusion of Gehring's lemma (`TauCeti.exists_setLAverage_rpow_add_le`) holds: every `g`
satisfying the reverse Hölder inequality with constant `b` and error term `h` on the balls of
`B(x₀, R)` satisfies

`⨍_{B(x₀, R/2)} g ^ (q + δ) ≤ C ((⨍_{B(x₀, R)} g ^ q) ^ ((q + δ) / q) + ⨍_{B(x₀, R)} h ^ (q + δ))`.

Then `δ < q 4ᵈ / (b - 4ᵈ)`. Otherwise the power weight `‖x‖ ^ (-a)` with `a (q + δ) = d`, whose
reverse Hölder constant `d 4ᵈ / (d - a q) = 4ᵈ (q + δ) / δ` is at most `b`, would violate it. -/
theorem lt_div_sub_of_forall_setLAverage_rpow_add_le [Nontrivial E] {q δ : ℝ} (hq : 0 < q)
    (hδ : 0 < δ) {b C : ℝ≥0} (hb : (4 : ℝ) ^ finrank ℝ E < b)
    (hC : ∀ {g h : E → ℝ≥0∞} {x₀ : E} {R : ℝ},
      AEMeasurable g (μ.restrict (ball x₀ R)) →
      AEMeasurable h (μ.restrict (ball x₀ R)) →
      (∀ y ρ, 0 < ρ → ball y (2 * ρ) ⊆ ball x₀ R →
        ⨍⁻ x in ball y ρ, g x ^ q ∂μ ≤
          b * (⨍⁻ x in ball y (2 * ρ), g x ∂μ) ^ q + ⨍⁻ x in ball y (2 * ρ), h x ^ q ∂μ) →
      ⨍⁻ x in ball x₀ (R / 2), g x ^ (q + δ) ∂μ ≤
        C * ((⨍⁻ x in ball x₀ R, g x ^ q ∂μ) ^ ((q + δ) / q) +
          ⨍⁻ x in ball x₀ R, h x ^ (q + δ) ∂μ)) :
    δ < q * 4 ^ finrank ℝ E / (b - 4 ^ finrank ℝ E) := by
  set d := finrank ℝ E
  set D : ℝ := (d : ℝ)
  have hD : 0 < D := Nat.cast_pos.2 Module.finrank_pos
  have hb4 : 0 < (b : ℝ) - 4 ^ d := sub_pos.2 hb
  by_contra! hge
  have hge' : q * 4 ^ d ≤ δ * (b - 4 ^ d) := (div_le_iff₀ hb4).1 hge
  -- The power weight `‖x‖ ^ (-a)` with `a (q + δ) = d` has reverse Hölder constant
  -- `d 4ᵈ / (d - a q) = 4ᵈ (q + δ) / δ`, which is at most `b`.
  set a := D / (q + δ) with ha_def
  have hqδ : 0 < q + δ := by linarith
  have hexp : -a * (q + δ) = -D := by rw [neg_mul, ha_def, div_mul_cancel₀ _ hqδ.ne']
  have hDa : D - a * q = D * δ / (q + δ) := by
    rw [ha_def]
    field_simp
    ring
  have haq : a * q < D := by
    rw [← sub_pos, hDa]
    positivity
  have hconst : ENNReal.ofReal (D * 4 ^ d / (D - a * q)) ≤ b := by
    rw [← ENNReal.ofReal_coe_nnreal]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hDa, div_div_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hge' hD.le]
  -- Gehring's conclusion for `g = ‖x‖ ^ (-a)`, `h = 0` on the unit ball.
  have key := hC (g := fun x => ‖x‖ₑ ^ (-a)) (h := fun _ => 0) (x₀ := 0) (R := 1)
    (by fun_prop) aemeasurable_const fun y ρ hρ _ => by
      simp only [ENNReal.zero_rpow_of_pos hq, laverage_zero, add_zero]
      exact (setLAverage_ball_enorm_rpow_neg_rpow_le (by positivity) hq.le haq y hρ).trans
        (by gcongr)
  simp only [ENNReal.zero_rpow_of_pos hqδ, laverage_zero, add_zero, ← ENNReal.rpow_mul,
    hexp] at key
  -- The left side is infinite, since `a (q + δ) = d`, and the right side is finite, since
  -- `a q < d`.
  have htop := setLAverage_ball_enorm_sub_rpow_eq_top (mu := μ) le_rfl (0 : E)
    (by norm_num : (0 : ℝ) < 1 / 2)
  have hfin := setLAverage_ball_enorm_sub_rpow_lt_top (mu := μ) (neg_lt_neg haq) (0 : E) 1
  simp only [zero_sub, eNorm_neg] at htop hfin
  rw [htop, neg_mul] at key
  refine (lt_irrefl (⊤ : ℝ≥0∞)) (key.trans_lt ?_)
  refine ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.rpow_lt_top_of_nonneg ?_ hfin.ne)
  positivity

/-- **Gehring's lemma has no gain independent of the constant.** On a nontrivial space and for
`q > 0`, there is no `δ > 0` such that for every constant `b` the conclusion of Gehring's lemma
(`TauCeti.exists_setLAverage_rpow_add_le`) holds with the gain `δ` and some constant `C`. -/
theorem not_exists_forall_exists_setLAverage_rpow_add_le [Nontrivial E] {q : ℝ} (hq : 0 < q) :
    ¬ ∃ δ : ℝ, 0 < δ ∧ ∀ b : ℝ≥0, ∃ C : ℝ≥0, ∀ {g h : E → ℝ≥0∞} {x₀ : E} {R : ℝ},
      AEMeasurable g (μ.restrict (ball x₀ R)) →
      AEMeasurable h (μ.restrict (ball x₀ R)) →
      (∀ y ρ, 0 < ρ → ball y (2 * ρ) ⊆ ball x₀ R →
        ⨍⁻ x in ball y ρ, g x ^ q ∂μ ≤
          b * (⨍⁻ x in ball y (2 * ρ), g x ∂μ) ^ q + ⨍⁻ x in ball y (2 * ρ), h x ^ q ∂μ) →
      ⨍⁻ x in ball x₀ (R / 2), g x ^ (q + δ) ∂μ ≤
        C * ((⨍⁻ x in ball x₀ R, g x ^ q ∂μ) ^ ((q + δ) / q) +
          ⨍⁻ x in ball x₀ R, h x ^ (q + δ) ∂μ) := by
  rintro ⟨δ, hδ, hG⟩
  set c : ℝ := 4 ^ finrank ℝ E
  have hc : 0 < c := by positivity
  -- For `b = c (1 + q / δ)` the bound `δ < q c / (b - c)` reads `δ < δ`.
  set b : ℝ≥0 := Real.toNNReal (c * (1 + q / δ))
  have hbc : (b : ℝ) = c * (1 + q / δ) := Real.coe_toNNReal _ (by positivity)
  obtain ⟨C, hC⟩ := hG b
  have hlt := lt_div_sub_of_forall_setLAverage_rpow_add_le (μ := μ) hq hδ
    (by rw [hbc]; nlinarith [div_pos hq hδ]) hC
  rw [hbc, show c * (1 + q / δ) - c = c * q / δ by ring] at hlt
  field_simp at hlt
  linarith

end TauCeti
