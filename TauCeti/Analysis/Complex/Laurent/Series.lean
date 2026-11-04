/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import TauCeti.Analysis.Complex.Laurent.Basic

/-!
# Convergent Laurent series on concentric annuli

Let `E` be a complex normed space. This file defines convergent Laurent series on open concentric
annuli `Metric.eball c R \ Metric.closedBall c r` (`0 ≤ r`, `ENNReal.ofReal r < R`, including
punctured open disks when `r = 0`, exteriors of closed disks when `R = ⊤`, and the whole punctured
plane `ℂ \ {c}` when `r = 0` and `R = ⊤`) and establishes their analytic properties.

Any integer-indexed Laurent series that converges pointwise on an open annulus automatically has
summable norm bounds `∑_{n ∈ ℤ} ‖a n‖ * ρ ^ n < ∞` on every interior circle `ρ ∈ (r, R)`. For
complete `E`, it converges uniformly on every closed concentric subannulus and splits on the open
annulus as `f = laurentPosPart a c + laurentNegPart a c`, where `laurentPosPart a c` converges as a
formal power series on the entire outer disk `Metric.eball c R` and `laurentNegPart a c` is
complex-analytic on the entire exterior `(Metric.closedBall c r)ᶜ` and vanishes at infinity. When
all negative-degree coefficients vanish on a punctured disk (`r = 0`), updating `f` at `c` with
`a 0` extends `f` to a power-series-analytic function on all of `Metric.eball c R`.

Circle-integral coefficient extraction, uniqueness, Laurent's theorem for holomorphic functions on
annuli, removable-singularity characterization, and term-by-term differentiation are developed in
`TauCeti.Analysis.Complex.Laurent.Expansion`.

## Main definitions

* `TauCeti.HasLaurentSeriesOnAnnulus f a c r R`: `0 ≤ r`, `ENNReal.ofReal r < R`, and the
  integer-indexed series `∑_{n ∈ ℤ} (w - c) ^ n • a n` has sum `f w` at every point `w` of the open
  annulus `Metric.eball c R \ Metric.closedBall c r`.
* `TauCeti.laurentPosPowerSeries a`: the formal multilinear power series with `n`-th coefficient
  `a n` (`n : ℕ`), which equals `cauchyPowerSeries f c R` for `a = circleLaurentCoeff f c R`.
* `TauCeti.laurentPosPart a c`: the nonnegative sum `w ↦ ∑' n : ℕ, (w - c) ^ n • a n`.
* `TauCeti.laurentNegPart a c`: the principal sum
  `w ↦ ∑' n : ℕ, (w - c) ^ (-((n : ℤ) + 1)) • a (-((n : ℤ) + 1))`.

## Main results

* `HasFPowerSeriesOnBall.hasLaurentSeriesOnAnnulus`: views a formal power series on
  `Metric.eball c R` as a Laurent series on `Metric.eball c R \ {c}` with vanishing negative
  coefficients.
* `TauCeti.HasLaurentSeriesOnAnnulus.summable_norm_mul_zpow` and
  `TauCeti.HasLaurentSeriesOnAnnulus.tendstoUniformlyOn_closedAnnulus`: automatic absolute
  summability on interior circles and uniform convergence on closed concentric subannuli.
* `TauCeti.HasLaurentSeriesOnAnnulus.hasFPowerSeriesOnBall_laurentPosPart`,
  `TauCeti.HasLaurentSeriesOnAnnulus.analyticOnNhd_laurentNegPart`, and
  `TauCeti.HasLaurentSeriesOnAnnulus.tendsto_laurentNegPart_cocompact`: convergence and analyticity
  of the positive part on `Metric.eball c R` and of the negative part on `(Metric.closedBall c r)ᶜ`,
  with vanishing at infinity.
* `TauCeti.HasLaurentSeriesOnAnnulus.eq_laurentPosPart_add_laurentNegPart` and
  `TauCeti.HasLaurentSeriesOnAnnulus.analyticOnNhd`: Laurent splitting and analyticity of the sum on
  the open annulus.
* `TauCeti.HasLaurentSeriesOnAnnulus.hasFPowerSeriesOnBall_update_of_neg_eq_zero`:
  removable-singularity extension across `c` when negative coefficients vanish.

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

/-- `HasLaurentSeriesOnAnnulus f a c r R` states that `0 ≤ r`, `ENNReal.ofReal r < R`, and at every
point `w` of the open concentric annulus `Metric.eball c R \ Metric.closedBall c r` the
integer-indexed Laurent series `∑_{n ∈ ℤ} (w - c) ^ n • a n` has sum `f w`.

When `r = 0`, `Metric.closedBall c 0 = {c}`, so the domain is the punctured open disk
`Metric.eball c R \ {c}` (or the whole punctured plane `ℂ \ {c}` when `R = ⊤`). -/
structure HasLaurentSeriesOnAnnulus (f : ℂ → E) (a : ℤ → E) (c : ℂ) (r : ℝ) (R : ℝ≥0∞) : Prop where
  /-- The inner radius is nonnegative, excluding the center `c` from the open annulus. -/
  r_nonneg : 0 ≤ r
  /-- The open annulus is nonempty. -/
  r_lt : ENNReal.ofReal r < R
  /-- Pointwise convergence of the integer-indexed Laurent series on the open annulus. -/
  hasSum : ∀ {w : ℂ}, w ∈ eball c R \ closedBall c r →
    HasSum (fun n : ℤ => (w - c) ^ n • a n) (f w)

/-- Unbundled characterization of `HasLaurentSeriesOnAnnulus`. -/
theorem hasLaurentSeriesOnAnnulus_iff {f : ℂ → E} {a : ℤ → E} {c : ℂ} {r : ℝ} {R : ℝ≥0∞} :
    HasLaurentSeriesOnAnnulus f a c r R ↔
      0 ≤ r ∧ ENNReal.ofReal r < R ∧
        ∀ ⦃w : ℂ⦄, w ∈ eball c R \ closedBall c r →
          HasSum (fun n : ℤ => (w - c) ^ n • a n) (f w) :=
  ⟨fun h => ⟨h.r_nonneg, h.r_lt, fun _ hw => h.hasSum hw⟩,
    fun ⟨hr, hlt, hs⟩ => ⟨hr, hlt, fun hw => hs hw⟩⟩

/-- A formal power series expansion on `Metric.eball c R` restricts to a Laurent series expansion on
the punctured disk `Metric.eball c R \ Metric.closedBall c 0` whose negative-degree coefficients
vanish and whose nonnegative-degree coefficients are `p.coeff n`. -/
theorem _root_.HasFPowerSeriesOnBall.hasLaurentSeriesOnAnnulus
    {f : ℂ → E} {p : FormalMultilinearSeries ℂ ℂ E} {c : ℂ} {R : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f p c R) :
    HasLaurentSeriesOnAnnulus f
      (fun n : ℤ => if 0 ≤ n then p.coeff n.toNat else 0) c 0 R where
  r_nonneg := le_rfl
  r_lt := by
    rw [ENNReal.ofReal_zero]
    exact hf.r_pos
  hasSum {w} hw := by
    let b : ℤ → E := fun n => if 0 ≤ n then p.coeff n.toNat else 0
    have hp : HasSum (fun n : ℕ => (w - c) ^ (n : ℤ) • b (n : ℤ)) (f w) := by
      refine (hf.hasSum_sub hw.1).congr_fun fun n => ?_
      have hb : b (n : ℤ) = p.coeff n := by
        dsimp only [b]
        rw [ite_eq_left (Int.natCast_nonneg n), Int.toNat_natCast]
      rw [hb, zpow_natCast, p.apply_eq_pow_smul_coeff]
    have hn : HasSum (fun n : ℕ => (w - c) ^ (-((n : ℤ) + 1)) • b (-((n : ℤ) + 1))) 0 := by
      have hzero : ∀ n : ℕ, (w - c) ^ (-((n : ℤ) + 1)) • b (-((n : ℤ) + 1)) = 0 := fun n => by
        have hnot : ¬ (0 : ℤ) ≤ -((n : ℤ) + 1) := by omega
        dsimp only [b]
        rw [ite_eq_right hnot, smul_zero]
      simp_rw [hzero]
      exact hasSum_zero
    have htot := HasSum.of_nat_of_neg_add_one (f := fun n : ℤ => (w - c) ^ n • b n) hp hn
    rwa [add_zero] at htot

/-- The formal multilinear power series whose `n`-th coefficient is `a n` (`n : ℕ`), representing
the nonnegative part of a Laurent series. -/
noncomputable def laurentPosPowerSeries (a : ℤ → E) : FormalMultilinearSeries ℂ ℂ E :=
  fun n => ContinuousMultilinearMap.mkPiRing ℂ (Fin n) (a n)

/-- Defining formula for the `n`-th term of `laurentPosPowerSeries`. -/
theorem laurentPosPowerSeries_def (a : ℤ → E) (n : ℕ) :
    laurentPosPowerSeries a n = ContinuousMultilinearMap.mkPiRing ℂ (Fin n) (a n) := (rfl)

/-- The `n`-th scalar coefficient of `laurentPosPowerSeries a` is `a n`. -/
@[simp]
theorem coeff_laurentPosPowerSeries (a : ℤ → E) (n : ℕ) :
    (laurentPosPowerSeries a).coeff n = a n := by
  simp [laurentPosPowerSeries, FormalMultilinearSeries.coeff]

/-- The operator norm of `laurentPosPowerSeries a n` equals `‖a n‖`. -/
theorem norm_laurentPosPowerSeries (a : ℤ → E) (n : ℕ) :
    ‖laurentPosPowerSeries a n‖ = ‖a n‖ :=
  ContinuousMultilinearMap.norm_mkPiRing (a n)

/-- Evaluating `laurentPosPowerSeries a n` on the constant tuple `fun _ => y` yields `y ^ n • a n`.
-/
theorem laurentPosPowerSeries_apply (a : ℤ → E) (n : ℕ) (y : ℂ) :
    laurentPosPowerSeries a n (fun _ => y) = y ^ n • a n := by
  simp [laurentPosPowerSeries]

/-- For circle Laurent coefficients, `laurentPosPowerSeries` is literally Mathlib's
`cauchyPowerSeries`. -/
@[simp]
theorem laurentPosPowerSeries_circleLaurentCoeff (f : ℂ → E) (c : ℂ) (R : ℝ) :
    laurentPosPowerSeries (circleLaurentCoeff f c R) = cauchyPowerSeries f c R := by
  ext1 n
  rw [laurentPosPowerSeries, circleLaurentCoeff_natCast]
  exact (cauchyPowerSeries f c R).mkPiRing_coeff_eq n

/-- The nonnegative-degree sum `∑' n : ℕ, (w - c) ^ n • a n` of a Laurent series. -/
noncomputable def laurentPosPart (a : ℤ → E) (c w : ℂ) : E :=
  ∑' n : ℕ, (w - c) ^ n • a n

/-- Defining series formula for `laurentPosPart`. -/
theorem laurentPosPart_def (a : ℤ → E) (c w : ℂ) :
    laurentPosPart a c w = ∑' n : ℕ, (w - c) ^ n • a n := (rfl)

/-- The negative-degree (principal) sum `∑' n : ℕ, (w - c) ^ (-(n + 1)) • a (-(n + 1))` of a
Laurent series. -/
noncomputable def laurentNegPart (a : ℤ → E) (c w : ℂ) : E :=
  ∑' n : ℕ, (w - c) ^ (-((n : ℤ) + 1)) • a (-((n : ℤ) + 1))

/-- Defining series formula for `laurentNegPart`. -/
theorem laurentNegPart_def (a : ℤ → E) (c w : ℂ) :
    laurentNegPart a c w = ∑' n : ℕ, (w - c) ^ (-((n : ℤ) + 1)) • a (-((n : ℤ) + 1)) := (rfl)

/-- At the center `c`, `laurentPosPart a c c` evaluates to the constant term `a 0`. -/
@[simp]
theorem laurentPosPart_at_center (a : ℤ → E) (c : ℂ) :
    laurentPosPart a c c = a 0 := by
  rw [laurentPosPart, sub_self, tsum_eq_single 0]
  · simp
  · intro n hn
    rw [zero_pow hn, zero_smul]

/-- When all negative-degree Laurent coefficients vanish, `laurentNegPart` is identically zero. -/
theorem laurentNegPart_eq_zero_of_neg_eq_zero {a : ℤ → E}
    (ha : ∀ k : ℕ, a (-((k : ℤ) + 1)) = 0) (c w : ℂ) :
    laurentNegPart a c w = 0 := by
  rw [laurentNegPart_def]
  simp_rw [ha, smul_zero, tsum_zero]

namespace HasLaurentSeriesOnAnnulus

/-- The outer radius of a convergent Laurent series on an open annulus is strictly positive. -/
theorem r_pos {f : ℂ → E} {a : ℤ → E} {c : ℂ} {r : ℝ} {R : ℝ≥0∞}
    (h : HasLaurentSeriesOnAnnulus f a c r R) : 0 < R :=
  lt_of_le_of_lt zero_le h.r_lt

/-- Restriction of a Laurent series expansion to a concentric subannulus. -/
theorem mono {f : ℂ → E} {a : ℤ → E} {c : ℂ} {r r' : ℝ} {R R' : ℝ≥0∞}
    (h : HasLaurentSeriesOnAnnulus f a c r R) (hr : r ≤ r') (hR : R' ≤ R)
    (hrR' : ENNReal.ofReal r' < R') :
    HasLaurentSeriesOnAnnulus f a c r' R' where
  r_nonneg := h.r_nonneg.trans hr
  r_lt := hrR'
  hasSum hw := h.hasSum ⟨eball_subset_eball hR hw.1,
    fun hmem => hw.2 (closedBall_subset_closedBall hr hmem)⟩

/-- Functions agreeing on the open annulus share the same Laurent series expansions. -/
theorem congr {f g : ℂ → E} {a : ℤ → E} {c : ℂ} {r : ℝ} {R : ℝ≥0∞}
    (h : HasLaurentSeriesOnAnnulus f a c r R)
    (hfg : EqOn f g (eball c R \ closedBall c r)) :
    HasLaurentSeriesOnAnnulus g a c r R where
  r_nonneg := h.r_nonneg
  r_lt := h.r_lt
  hasSum hw := hfg hw ▸ h.hasSum hw

/-- The zero function has the zero Laurent series on any nonempty open annulus. -/
theorem zero (c : ℂ) {r : ℝ} {R : ℝ≥0∞} (hr : 0 ≤ r) (hrR : ENNReal.ofReal r < R) :
    HasLaurentSeriesOnAnnulus (fun _ => (0 : E)) (fun _ => 0) c r R where
  r_nonneg := hr
  r_lt := hrR
  hasSum _ := by simp

/-- Termwise addition of Laurent series on the same open annulus. -/
theorem add {f g : ℂ → E} {a b : ℤ → E} {c : ℂ} {r : ℝ} {R : ℝ≥0∞}
    (hf : HasLaurentSeriesOnAnnulus f a c r R)
    (hg : HasLaurentSeriesOnAnnulus g b c r R) :
    HasLaurentSeriesOnAnnulus (fun w => f w + g w) (fun n => a n + b n) c r R where
  r_nonneg := hf.r_nonneg
  r_lt := hf.r_lt
  hasSum hw := by
    simpa only [smul_add] using (hf.hasSum hw).add (hg.hasSum hw)

/-- Termwise negation of a Laurent series on an open annulus. -/
theorem neg {f : ℂ → E} {a : ℤ → E} {c : ℂ} {r : ℝ} {R : ℝ≥0∞}
    (hf : HasLaurentSeriesOnAnnulus f a c r R) :
    HasLaurentSeriesOnAnnulus (fun w => -f w) (fun n => -a n) c r R where
  r_nonneg := hf.r_nonneg
  r_lt := hf.r_lt
  hasSum hw := by
    simpa only [smul_neg] using (hf.hasSum hw).neg

/-- Termwise subtraction of Laurent series on the same open annulus. -/
theorem sub {f g : ℂ → E} {a b : ℤ → E} {c : ℂ} {r : ℝ} {R : ℝ≥0∞}
    (hf : HasLaurentSeriesOnAnnulus f a c r R)
    (hg : HasLaurentSeriesOnAnnulus g b c r R) :
    HasLaurentSeriesOnAnnulus (fun w => f w - g w) (fun n => a n - b n) c r R where
  r_nonneg := hf.r_nonneg
  r_lt := hf.r_lt
  hasSum hw := by
    simpa only [smul_sub] using (hf.hasSum hw).sub (hg.hasSum hw)

/-- Scalar multiplication of a Laurent series by a complex constant. -/
theorem const_smul {f : ℂ → E} {a : ℤ → E} {c : ℂ} {r : ℝ} {R : ℝ≥0∞}
    (hf : HasLaurentSeriesOnAnnulus f a c r R) (b : ℂ) :
    HasLaurentSeriesOnAnnulus (fun w => b • f w) (fun n => b • a n) c r R where
  r_nonneg := hf.r_nonneg
  r_lt := hf.r_lt
  hasSum hw := by
    simpa only [smul_comm _ b] using (hf.hasSum hw).const_smul b

/-- A Laurent monomial `(w - c) ^ m • v` has the single-term Laurent expansion supported at `m`. -/
theorem sub_zpow_smul (v : E) (c : ℂ) (m : ℤ) {r : ℝ} {R : ℝ≥0∞}
    (hr : 0 ≤ r) (hrR : ENNReal.ofReal r < R) :
    HasLaurentSeriesOnAnnulus (fun w => (w - c) ^ m • v)
      (fun n => if n = m then v else 0) c r R where
  r_nonneg := hr
  r_lt := hrR
  hasSum {w} _ := by
    refine (hasSum_ite_eq m ((w - c) ^ m • v)).congr_fun fun n => ?_
    split_ifs with hnm
    · subst n; rfl
    · simp

/-- Pointwise convergence of a Laurent series on an open annulus implies absolute norm-power
summability of its nonnegative-degree terms on every interior circle of radius `ρ ∈ (r, R)`. -/
theorem summable_norm_mul_pow {f : ℂ → E} {a : ℤ → E} {c : ℂ} {r ρ : ℝ} {R : ℝ≥0∞}
    (h : HasLaurentSeriesOnAnnulus f a c r R) (hrρ : r < ρ) (hρR : ENNReal.ofReal ρ < R) :
    Summable (fun n : ℕ => ‖a n‖ * ρ ^ n) := by
  have hρ_pos : 0 < ρ := h.r_nonneg.trans_lt hrρ
  obtain ⟨q, hρq, hqR⟩ := exists_between hρR
  lift q to ℝ≥0 using hqR.ne_top
  have hρq' : ρ < (q : ℝ) := (ENNReal.ofReal_lt_coe_iff hρ_pos.le).mp hρq
  have hq_pos : 0 < (q : ℝ) := hρ_pos.trans hρq'
  let w₁ : ℂ := c + (q : ℝ)
  have hw₁_dist : dist w₁ c = (q : ℝ) := by
    simp [w₁, dist_eq_norm, abs_of_pos hq_pos]
  have hw₁ : w₁ ∈ eball c R \ closedBall c r := by
    refine ⟨?_, ?_⟩
    · rw [mem_eball, edist_dist, hw₁_dist, ENNReal.ofReal_coe_nnreal]
      exact hqR
    · rw [mem_closedBall, hw₁_dist, not_le]
      exact hrρ.trans hρq'
  have htend₁ : Tendsto (fun n : ℕ => ‖(w₁ - c) ^ (n : ℤ) • a n‖) atTop (𝓝 0) := by
    have hcof := (h.hasSum hw₁).summable.tendsto_cofinite_zero
    simpa only [Nat.cofinite_eq_atTop, Function.comp_def, norm_zero] using
      (hcof.comp Nat.cast_injective.tendsto_cofinite).norm
  have hev₁ : ∀ᶠ n : ℕ in atTop, ‖a n‖ * ρ ^ n ≤ (ρ / (q : ℝ)) ^ n := by
    filter_upwards [htend₁.eventually (Iio_mem_nhds zero_lt_one)] with n hn
    have hsub : w₁ - c = (q : ℝ) := add_sub_cancel_left c (q : ℝ)
    have hn' : (q : ℝ) ^ n * ‖a n‖ ≤ 1 := by
      have hn_lt : (q : ℝ) ^ n * ‖a n‖ < 1 := by
        simpa only [zpow_natCast, norm_smul, norm_pow, hsub, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hq_pos, mem_Iio] using hn
      exact hn_lt.le
    calc
      ‖a n‖ * ρ ^ n = ((q : ℝ) ^ n * ‖a n‖) * (ρ / (q : ℝ)) ^ n := by
        rw [div_pow, mul_comm ((q : ℝ) ^ n), mul_assoc,
          mul_div_cancel₀ _ (pow_ne_zero n hq_pos.ne')]
      _ ≤ 1 * (ρ / (q : ℝ)) ^ n :=
        mul_le_mul_of_nonneg_right hn' (pow_nonneg (div_nonneg hρ_pos.le hq_pos.le) n)
      _ = (ρ / (q : ℝ)) ^ n := one_mul _
  exact Summable.of_norm_bounded_eventually_nat
    (summable_geometric_of_lt_one (div_nonneg hρ_pos.le hq_pos.le) ((div_lt_one hq_pos).2 hρq'))
    (hev₁.mono fun n hn => by
      rwa [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg hρ_pos.le _))])

/-- Pointwise convergence of a Laurent series on an open annulus implies absolute norm-power
summability of its negative-degree terms on every interior circle of radius `ρ ∈ (r, R)`. -/
theorem summable_norm_mul_zpow_neg_add_one {f : ℂ → E} {a : ℤ → E} {c : ℂ} {r ρ : ℝ} {R : ℝ≥0∞}
    (h : HasLaurentSeriesOnAnnulus f a c r R) (hrρ : r < ρ) (hρR : ENNReal.ofReal ρ < R) :
    Summable (fun n : ℕ => ‖a (-((n : ℤ) + 1))‖ * ρ ^ (-((n : ℤ) + 1))) := by
  have hρ_pos : 0 < ρ := h.r_nonneg.trans_lt hrρ
  let r₁ : ℝ := (r + ρ) / 2
  have hr₁_pos : 0 < r₁ := by dsimp [r₁]; linarith [h.r_nonneg]
  have hrr₁ : r < r₁ := by dsimp [r₁]; linarith
  have hr₁ρ : r₁ < ρ := by dsimp [r₁]; linarith
  let w₂ : ℂ := c + r₁
  have hw₂_dist : dist w₂ c = r₁ := by
    simp [w₂, dist_eq_norm, abs_of_pos hr₁_pos]
  have hw₂ : w₂ ∈ eball c R \ closedBall c r := by
    refine ⟨?_, ?_⟩
    · rw [mem_eball, edist_dist, hw₂_dist]
      exact (ENNReal.ofReal_lt_ofReal_iff hρ_pos).mpr hr₁ρ |>.trans hρR
    · rw [mem_closedBall, hw₂_dist, not_le]
      exact hrr₁
  have hinj : Function.Injective (fun n : ℕ => -((n : ℤ) + 1)) := by
    intro m n hmn; dsimp only at hmn; omega
  have htend₂ : Tendsto (fun n : ℕ =>
      ‖(w₂ - c) ^ (-((n : ℤ) + 1)) • a (-((n : ℤ) + 1))‖) atTop (𝓝 0) := by
    simpa only [Nat.cofinite_eq_atTop, Function.comp_def, norm_zero] using
      ((h.hasSum hw₂).summable.tendsto_cofinite_zero.comp hinj.tendsto_cofinite).norm
  have hev₂ : ∀ᶠ n : ℕ in atTop,
      ‖a (-((n : ℤ) + 1))‖ * ρ ^ (-((n : ℤ) + 1)) ≤ (r₁ / ρ) ^ (n + 1) := by
    filter_upwards [htend₂.eventually (Iio_mem_nhds zero_lt_one)] with n hn
    have hsub : w₂ - c = r₁ := add_sub_cancel_left c r₁
    have hn' : r₁ ^ (-((n : ℤ) + 1)) * ‖a (-((n : ℤ) + 1))‖ ≤ 1 := by
      have hn_lt : r₁ ^ (-((n : ℤ) + 1)) * ‖a (-((n : ℤ) + 1))‖ < 1 := by
        simpa only [norm_smul, norm_zpow, hsub, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hr₁_pos, mem_Iio] using hn
      exact hn_lt.le
    calc
      ‖a (-((n : ℤ) + 1))‖ * ρ ^ (-((n : ℤ) + 1))
          = (r₁ ^ (-((n : ℤ) + 1)) * ‖a (-((n : ℤ) + 1))‖) * (r₁ / ρ) ^ (n + 1) := by
        simp only [div_pow, ← Nat.cast_add_one, zpow_neg, zpow_natCast]
        field_simp [hr₁_pos.ne', hρ_pos.ne']
      _ ≤ 1 * (r₁ / ρ) ^ (n + 1) :=
        mul_le_mul_of_nonneg_right hn' (pow_nonneg (div_nonneg hr₁_pos.le hρ_pos.le) _)
      _ = (r₁ / ρ) ^ (n + 1) := one_mul _
  have hgeom : Summable (fun n : ℕ => (r₁ / ρ) ^ (n + 1)) :=
    (summable_nat_add_iff 1).2 <|
      summable_geometric_of_lt_one (div_nonneg hr₁_pos.le hρ_pos.le) ((div_lt_one hρ_pos).2 hr₁ρ)
  exact Summable.of_norm_bounded_eventually_nat hgeom
    (hev₂.mono fun n hn => by
      rwa [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (zpow_nonneg hρ_pos.le _))])

/-- Pointwise convergence of a Laurent series on an open annulus automatically yields absolute
norm-power summability `∑_{n ∈ ℤ} ‖a n‖ * ρ ^ n < ∞` on every interior circle of radius
`ρ ∈ (r, R)`. -/
theorem summable_norm_mul_zpow {f : ℂ → E} {a : ℤ → E} {c : ℂ} {r ρ : ℝ} {R : ℝ≥0∞}
    (h : HasLaurentSeriesOnAnnulus f a c r R) (hrρ : r < ρ) (hρR : ENNReal.ofReal ρ < R) :
    Summable (fun n : ℤ => ‖a n‖ * ρ ^ n) :=
  Summable.of_nat_of_neg_add_one
    (by simpa only [zpow_natCast] using h.summable_norm_mul_pow hrρ hρR)
    (h.summable_norm_mul_zpow_neg_add_one hrρ hρR)

/-- On any closed concentric subannulus `Metric.closedBall c R' \ Metric.ball c r'` inside the open
annulus, the Laurent terms admit a uniform summable norm majorant. -/
theorem exists_summable_norm_bound_on_closedAnnulus {f : ℂ → E} {a : ℤ → E} {c : ℂ}
    {r r' R' : ℝ} {R : ℝ≥0∞} (h : HasLaurentSeriesOnAnnulus f a c r R)
    (hrr' : r < r') (hr'R' : r' ≤ R') (hR'R : ENNReal.ofReal R' < R) :
    ∃ B : ℤ → ℝ, Summable B ∧
      ∀ n : ℤ, ∀ w ∈ closedBall c R' \ ball c r', ‖(w - c) ^ n • a n‖ ≤ B n := by
  have hr'_pos : 0 < r' := h.r_nonneg.trans_lt hrr'
  have hrR' : r < R' := hrr'.trans_le hr'R'
  have hr'R : ENNReal.ofReal r' < R :=
    (ENNReal.ofReal_le_ofReal hr'R').trans_lt hR'R
  refine ⟨fun n : ℤ => if 0 ≤ n then ‖a n‖ * R' ^ n else ‖a n‖ * r' ^ n, ?_, ?_⟩
  · apply Summable.of_nat_of_neg_add_one
    · simpa only [Nat.cast_nonneg, ↓reduceIte, zpow_natCast] using
        h.summable_norm_mul_pow hrR' hR'R
    · have hneg : ∀ n : ℕ, ¬(0 ≤ -((n : ℤ) + 1)) := fun n => by omega
      simpa only [hneg, ↓reduceIte] using h.summable_norm_mul_zpow_neg_add_one hrr' hr'R
  · intro n w hw
    have hw_le : ‖w - c‖ ≤ R' := by simpa only [mem_closedBall, dist_eq_norm] using hw.1
    have hr'_le : r' ≤ ‖w - c‖ := by simpa only [mem_ball, dist_eq_norm, not_lt] using hw.2
    dsimp only
    rw [norm_smul, norm_zpow, mul_comm]
    split_ifs with hn
    · lift n to ℕ using hn
      rw [zpow_natCast, zpow_natCast]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hw_le n) (norm_nonneg _)
    · have hn' : n < 0 := not_le.mp hn
      obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -((k : ℤ) + 1) := ⟨(-n - 1).toNat, by omega⟩
      rw [← Nat.cast_add_one, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      exact inv_anti₀ (pow_pos hr'_pos (k + 1)) (pow_le_pow_left₀ hr'_pos.le hr'_le (k + 1))

/-- The radius of convergence of the nonnegative formal power series `laurentPosPowerSeries a` is
at least the outer radius `R`. -/
theorem le_radius_laurentPosPowerSeries {f : ℂ → E} {a : ℤ → E} {c : ℂ} {r : ℝ} {R : ℝ≥0∞}
    (h : HasLaurentSeriesOnAnnulus f a c r R) :
    R ≤ (laurentPosPowerSeries a).radius := by
  refine le_of_forall_lt fun q hqR => ?_
  have hmax : max (ENNReal.ofReal r) q < R := max_lt h.r_lt hqR
  obtain ⟨q', hq'max, hq'R⟩ := exists_between hmax
  lift q' to ℝ≥0 using hq'R.ne_top
  have hrq' : r < (q' : ℝ) :=
    (ENNReal.ofReal_lt_coe_iff h.r_nonneg).mp ((le_max_left _ _).trans_lt hq'max)
  have hqq' : q < (q' : ℝ≥0∞) := (le_max_right _ _).trans_lt hq'max
  have hq'_in : ENNReal.ofReal (q' : ℝ) < R := by simpa using hq'R
  have hrad : (q' : ℝ≥0∞) ≤ (laurentPosPowerSeries a).radius := by
    refine (laurentPosPowerSeries a).le_radius_of_summable_norm ?_
    simpa only [norm_laurentPosPowerSeries] using h.summable_norm_mul_pow hrq' hq'_in
  exact hqq'.trans_le hrad

/-- Auxiliary formal power series in the inverted coordinate `(w - c)⁻¹`, with zero constant term
and `(n + 1)`-th coefficient `a (-(n + 1))`. -/
private noncomputable def negCoordPowerSeries (a : ℤ → E) : FormalMultilinearSeries ℂ ℂ E
  | 0 => 0
  | n + 1 => ContinuousMultilinearMap.mkPiRing ℂ (Fin (n + 1)) (a (-((n : ℤ) + 1)))

private theorem negCoordPowerSeries_apply_zero (a : ℤ → E) (u : ℂ) :
    negCoordPowerSeries a 0 (fun _ => u) = 0 := (rfl)

private theorem negCoordPowerSeries_apply_succ (a : ℤ → E) (n : ℕ) (u : ℂ) :
    negCoordPowerSeries a (n + 1) (fun _ => u) = u ^ (n + 1) • a (-((n : ℤ) + 1)) := by
  simp [negCoordPowerSeries]

private theorem norm_negCoordPowerSeries_succ (a : ℤ → E) (n : ℕ) :
    ‖negCoordPowerSeries a (n + 1)‖ = ‖a (-((n : ℤ) + 1))‖ :=
  ContinuousMultilinearMap.norm_mkPiRing (a (-((n : ℤ) + 1)))

private theorem le_radius_negCoordPowerSeries {f : ℂ → E} {a : ℤ → E} {c : ℂ} {r ρ : ℝ} {R : ℝ≥0∞}
    (h : HasLaurentSeriesOnAnnulus f a c r R) (hrρ : r < ρ) (hρR : ENNReal.ofReal ρ < R) :
    ENNReal.ofReal ρ⁻¹ ≤ (negCoordPowerSeries a).radius := by
  have hρ_pos : 0 < ρ := h.r_nonneg.trans_lt hrρ
  have hsum' : Summable (fun n : ℕ => ‖negCoordPowerSeries a n‖ * (ρ⁻¹) ^ n) := by
    rw [← summable_nat_add_iff 1]
    refine (h.summable_norm_mul_zpow_neg_add_one hrρ hρR).congr fun n => ?_
    rw [norm_negCoordPowerSeries_succ, ← Nat.cast_add_one, zpow_neg, zpow_natCast, inv_pow]
  let ρnn : ℝ≥0 := ⟨ρ⁻¹, inv_nonneg.2 hρ_pos.le⟩
  have hrad : (ρnn : ℝ≥0∞) ≤ (negCoordPowerSeries a).radius :=
    (negCoordPowerSeries a).le_radius_of_summable_norm (r := ρnn) hsum'
  rwa [← ENNReal.ofReal_coe_nnreal] at hrad

private theorem inv_sub_mem_eball_radius_negCoordPowerSeries
    {f : ℂ → E} {a : ℤ → E} {c w : ℂ} {r : ℝ} {R : ℝ≥0∞}
    (h : HasLaurentSeriesOnAnnulus f a c r R) (hw : w ∉ closedBall c r) :
    (w - c)⁻¹ ∈ eball (0 : ℂ) (negCoordPowerSeries a).radius := by
  have hrw : r < dist w c := not_le.mp (mt mem_closedBall.mpr hw)
  have hmin : ENNReal.ofReal r < min (ENNReal.ofReal (dist w c)) R :=
    lt_min ((ENNReal.ofReal_lt_ofReal_iff (h.r_nonneg.trans_lt hrw)).mpr hrw) h.r_lt
  obtain ⟨q, hrq, hqmin⟩ := exists_between hmin
  lift q to ℝ≥0 using (hqmin.trans_le (min_le_right _ _)).ne_top
  have hrq' : r < (q : ℝ) := (ENNReal.ofReal_lt_coe_iff h.r_nonneg).mp hrq
  have hq_pos : 0 < (q : ℝ) := h.r_nonneg.trans_lt hrq'
  have hqw : (q : ℝ) < dist w c :=
    ENNReal.coe_lt_ofReal.mp (hqmin.trans_le (min_le_left _ _))
  have hqR : ENNReal.ofReal (q : ℝ) < R := by
    simpa using hqmin.trans_le (min_le_right _ _)
  refine eball_subset_eball (h.le_radius_negCoordPowerSeries hrq' hqR) ?_
  rw [mem_eball, edist_zero_right, enorm_eq_nnnorm]
  have hnorm : ‖(w - c)⁻¹‖ < (q : ℝ)⁻¹ := by
    rw [norm_inv]
    exact inv_strictAnti₀ hq_pos (by simpa only [dist_eq_norm] using hqw)
  exact ENNReal.coe_lt_ofReal.mpr hnorm

private theorem radius_negCoordPowerSeries_pos
    {f : ℂ → E} {a : ℤ → E} {c : ℂ} {r : ℝ} {R : ℝ≥0∞}
    (h : HasLaurentSeriesOnAnnulus f a c r R) :
    0 < (negCoordPowerSeries a).radius := by
  have hw : c + ((r + 1 : ℝ) : ℂ) ∉ closedBall c r := by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith [h.r_nonneg])]
    linarith
  exact zero_le.trans_lt (mem_eball.mp (h.inv_sub_mem_eball_radius_negCoordPowerSeries hw))

section CompleteSpace

variable [CompleteSpace E]

/-- On any closed concentric subannulus inside the open annulus, the finite partial sums of the
Laurent series converge uniformly to `f`. -/
theorem tendstoUniformlyOn_closedAnnulus {f : ℂ → E} {a : ℤ → E} {c : ℂ}
    {r r' R' : ℝ} {R : ℝ≥0∞} (h : HasLaurentSeriesOnAnnulus f a c r R)
    (hrr' : r < r') (hr'R' : r' ≤ R') (hR'R : ENNReal.ofReal R' < R) :
    TendstoUniformlyOn (fun (t : Finset ℤ) w => ∑ n ∈ t, (w - c) ^ n • a n) f atTop
      (closedBall c R' \ ball c r') := by
  obtain ⟨B, hB, hbound⟩ := h.exists_summable_norm_bound_on_closedAnnulus hrr' hr'R' hR'R
  have hsub : closedBall c R' \ ball c r' ⊆ eball c R \ closedBall c r := by
    intro w hw
    refine ⟨?_, ?_⟩
    · rw [mem_eball, edist_dist]
      exact (ENNReal.ofReal_le_ofReal hw.1).trans_lt hR'R
    · intro hwr
      exact hw.2 (lt_of_le_of_lt hwr hrr')
  refine (tendstoUniformlyOn_tsum hB hbound).congr_right fun w hw => ?_
  exact (h.hasSum (hsub hw)).tsum_eq

/-- The positive-degree part of a Laurent series on `Metric.eball c R \ Metric.closedBall c r`
converges as a formal power series on the entire open disk `Metric.eball c R`, including at `c`. -/
theorem hasFPowerSeriesOnBall_laurentPosPart {f : ℂ → E} {a : ℤ → E} {c : ℂ} {r : ℝ} {R : ℝ≥0∞}
    (h : HasLaurentSeriesOnAnnulus f a c r R) :
    HasFPowerSeriesOnBall (laurentPosPart a c) (laurentPosPowerSeries a) c R where
  r_le := h.le_radius_laurentPosPowerSeries
  r_pos := h.r_pos
  hasSum {y} hy := by
    have hp := (laurentPosPowerSeries a).hasSum
      (eball_subset_eball h.le_radius_laurentPosPowerSeries hy)
    rw [FormalMultilinearSeries.sum] at hp
    simpa only [laurentPosPowerSeries_apply, laurentPosPart, add_sub_cancel_left] using hp

/-- The nonnegative part `laurentPosPart a c` has convergent series throughout `Metric.eball c R`.
-/
theorem hasSum_laurentPosPart {f : ℂ → E} {a : ℤ → E} {c w : ℂ} {r : ℝ} {R : ℝ≥0∞}
    (h : HasLaurentSeriesOnAnnulus f a c r R) (hw : w ∈ eball c R) :
    HasSum (fun n : ℕ => (w - c) ^ n • a n) (laurentPosPart a c w) := by
  simpa only [laurentPosPowerSeries_apply] using
    h.hasFPowerSeriesOnBall_laurentPosPart.hasSum_sub hw

/-- The nonnegative part `laurentPosPart a c` is complex-analytic on the entire disk
`Metric.eball c R`. -/
theorem analyticOnNhd_laurentPosPart {f : ℂ → E} {a : ℤ → E} {c : ℂ} {r : ℝ} {R : ℝ≥0∞}
    (h : HasLaurentSeriesOnAnnulus f a c r R) :
    AnalyticOnNhd ℂ (laurentPosPart a c) (eball c R) :=
  h.hasFPowerSeriesOnBall_laurentPosPart.analyticOnNhd

/-- The nonnegative part `laurentPosPart a c` is complex-differentiable on the entire disk
`Metric.eball c R`. -/
theorem differentiableOn_laurentPosPart {f : ℂ → E} {a : ℤ → E} {c : ℂ} {r : ℝ} {R : ℝ≥0∞}
    (h : HasLaurentSeriesOnAnnulus f a c r R) :
    DifferentiableOn ℂ (laurentPosPart a c) (eball c R) :=
  h.analyticOnNhd_laurentPosPart.differentiableOn

private theorem hasSum_negCoordPowerSeries_sum
    {f : ℂ → E} {a : ℤ → E} {c w : ℂ} {r : ℝ} {R : ℝ≥0∞}
    (h : HasLaurentSeriesOnAnnulus f a c r R) (hw : w ∉ closedBall c r) :
    HasSum (fun n : ℕ => (w - c) ^ (-((n : ℤ) + 1)) • a (-((n : ℤ) + 1)))
      ((negCoordPowerSeries a).sum (w - c)⁻¹) := by
  have hp := (negCoordPowerSeries a).hasSum (h.inv_sub_mem_eball_radius_negCoordPowerSeries hw)
  rw [← hasSum_nat_add_iff' 1] at hp
  simpa only [Finset.sum_range_one, negCoordPowerSeries_apply_zero, sub_zero,
    negCoordPowerSeries_apply_succ, inv_pow, ← Nat.cast_add_one, zpow_neg, zpow_natCast] using hp

private theorem laurentNegPart_eq_negCoordPowerSeries_sum
    {f : ℂ → E} {a : ℤ → E} {c w : ℂ} {r : ℝ} {R : ℝ≥0∞}
    (h : HasLaurentSeriesOnAnnulus f a c r R) (hw : w ∉ closedBall c r) :
    laurentNegPart a c w = (negCoordPowerSeries a).sum (w - c)⁻¹ := by
  rw [laurentNegPart]
  exact (h.hasSum_negCoordPowerSeries_sum hw).tsum_eq

/-- The negative part `laurentNegPart a c` converges at every point outside `Metric.closedBall c r`
(in particular on the whole punctured plane `ℂ \ {c}` when `r = 0`). -/
theorem hasSum_laurentNegPart {f : ℂ → E} {a : ℤ → E} {c w : ℂ} {r : ℝ} {R : ℝ≥0∞}
    (h : HasLaurentSeriesOnAnnulus f a c r R) (hw : w ∉ closedBall c r) :
    HasSum (fun n : ℕ => (w - c) ^ (-((n : ℤ) + 1)) • a (-((n : ℤ) + 1)))
      (laurentNegPart a c w) := by
  rw [h.laurentNegPart_eq_negCoordPowerSeries_sum hw]
  exact h.hasSum_negCoordPowerSeries_sum hw

/-- The negative part `laurentNegPart a c` is complex-analytic on `(Metric.closedBall c r)ᶜ`
(the whole punctured plane `ℂ \ {c}` when `r = 0`). -/
theorem analyticOnNhd_laurentNegPart {f : ℂ → E} {a : ℤ → E} {c : ℂ} {r : ℝ} {R : ℝ≥0∞}
    (h : HasLaurentSeriesOnAnnulus f a c r R) :
    AnalyticOnNhd ℂ (laurentNegPart a c) (closedBall c r)ᶜ := by
  intro w₀ hw₀
  have hfp := (negCoordPowerSeries a).hasFPowerSeriesOnBall h.radius_negCoordPowerSeries_pos
  have han_sum : AnalyticAt ℂ (negCoordPowerSeries a).sum (w₀ - c)⁻¹ :=
    hfp.analyticOnNhd _ (h.inv_sub_mem_eball_radius_negCoordPowerSeries hw₀)
  have hw₀_ne : w₀ - c ≠ 0 :=
    sub_ne_zero.mpr (dist_pos.mp (h.r_nonneg.trans_lt (not_le.mp (mt mem_closedBall.mpr hw₀))))
  have hinv_an : AnalyticAt ℂ (fun z : ℂ => (z - c)⁻¹) w₀ :=
    ((analyticAt_id (𝕜 := ℂ)).fun_sub analyticAt_const).fun_inv hw₀_ne
  refine (AnalyticAt.comp (f := fun z : ℂ => (z - c)⁻¹) (x := w₀) han_sum hinv_an).congr ?_
  filter_upwards [isClosed_closedBall.isOpen_compl.mem_nhds hw₀] with z hz
  exact (h.laurentNegPart_eq_negCoordPowerSeries_sum hz).symm

/-- The negative part `laurentNegPart a c` is complex-differentiable on `(Metric.closedBall c r)ᶜ`.
-/
theorem differentiableOn_laurentNegPart {f : ℂ → E} {a : ℤ → E} {c : ℂ} {r : ℝ} {R : ℝ≥0∞}
    (h : HasLaurentSeriesOnAnnulus f a c r R) :
    DifferentiableOn ℂ (laurentNegPart a c) (closedBall c r)ᶜ :=
  h.analyticOnNhd_laurentNegPart.differentiableOn

/-- The negative part `laurentNegPart a c` vanishes at infinity (`Filter.cocompact ℂ`). -/
theorem tendsto_laurentNegPart_cocompact {f : ℂ → E} {a : ℤ → E} {c : ℂ} {r : ℝ} {R : ℝ≥0∞}
    (h : HasLaurentSeriesOnAnnulus f a c r R) :
    Tendsto (laurentNegPart a c) (cocompact ℂ) (𝓝 0) := by
  have h0_mem : (0 : ℂ) ∈ eball (0 : ℂ) (negCoordPowerSeries a).radius :=
    mem_eball_self h.radius_negCoordPowerSeries_pos
  have hcont0 : ContinuousAt (negCoordPowerSeries a).sum 0 :=
    (negCoordPowerSeries a).continuousOn.continuousAt (isOpen_eball.mem_nhds h0_mem)
  have hsum0 : (negCoordPowerSeries a).sum 0 = 0 := by
    rw [FormalMultilinearSeries.sum, tsum_eq_single 0]
    · exact negCoordPowerSeries_apply_zero a 0
    · intro n hn
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
      rw [negCoordPowerSeries_apply_succ]
      simp
  have hinv : Tendsto (fun z : ℂ => (z - c)⁻¹) (cocompact ℂ) (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [(isCompact_closedBall c ε⁻¹).compl_mem_cocompact] with z hz
    have hlt : ε⁻¹ < ‖z - c‖ := by
      simpa only [mem_compl_iff, mem_closedBall, dist_eq_norm, not_le] using hz
    rw [dist_zero_right, norm_inv]
    exact inv_lt_of_inv_lt₀ hε hlt
  have hcomp : Tendsto (fun z : ℂ => (negCoordPowerSeries a).sum (z - c)⁻¹) (cocompact ℂ) (𝓝 0) :=
    hsum0 ▸ hcont0.tendsto.comp hinv
  refine hcomp.congr' ?_
  filter_upwards [(isCompact_closedBall c r).compl_mem_cocompact] with z hz
  exact (h.laurentNegPart_eq_negCoordPowerSeries_sum hz).symm

/-- On the open annulus, `f` splits as the sum of its nonnegative and negative Laurent parts. -/
theorem eq_laurentPosPart_add_laurentNegPart {f : ℂ → E} {a : ℤ → E} {c w : ℂ} {r : ℝ} {R : ℝ≥0∞}
    (h : HasLaurentSeriesOnAnnulus f a c r R) (hw : w ∈ eball c R \ closedBall c r) :
    f w = laurentPosPart a c w + laurentNegPart a c w := by
  have hp : HasSum (fun n : ℕ => (w - c) ^ (n : ℤ) • a (n : ℤ)) (laurentPosPart a c w) := by
    simpa only [zpow_natCast] using h.hasSum_laurentPosPart hw.1
  have hn := h.hasSum_laurentNegPart hw.2
  exact (h.hasSum hw).unique (hp.of_nat_of_neg_add_one hn)

/-- Any function admitting a convergent Laurent series on an open annulus is complex-analytic on
that annulus. -/
theorem analyticOnNhd {f : ℂ → E} {a : ℤ → E} {c : ℂ} {r : ℝ} {R : ℝ≥0∞}
    (h : HasLaurentSeriesOnAnnulus f a c r R) :
    AnalyticOnNhd ℂ f (eball c R \ closedBall c r) := by
  have hopen : IsOpen (eball c R \ closedBall c r) := isOpen_eball.sdiff isClosed_closedBall
  intro w hw
  refine ((h.analyticOnNhd_laurentPosPart w hw.1).add
    (h.analyticOnNhd_laurentNegPart w hw.2)).congr ?_
  filter_upwards [hopen.mem_nhds hw] with z hz
  exact (h.eq_laurentPosPart_add_laurentNegPart hz).symm

/-- Any function admitting a convergent Laurent series on an open annulus is complex-differentiable
on that annulus. -/
theorem differentiableOn {f : ℂ → E} {a : ℤ → E} {c : ℂ} {r : ℝ} {R : ℝ≥0∞}
    (h : HasLaurentSeriesOnAnnulus f a c r R) :
    DifferentiableOn ℂ f (eball c R \ closedBall c r) :=
  h.analyticOnNhd.differentiableOn

/-- Any function admitting a convergent Laurent series on an open annulus is continuous on that
annulus. -/
theorem continuousOn {f : ℂ → E} {a : ℤ → E} {c : ℂ} {r : ℝ} {R : ℝ≥0∞}
    (h : HasLaurentSeriesOnAnnulus f a c r R) :
    ContinuousOn f (eball c R \ closedBall c r) :=
  h.differentiableOn.continuousOn

/-- If all negative-degree coefficients vanish, a function with a Laurent series on an open annulus
agrees on that annulus with its nonnegative-degree sum `laurentPosPart a c`. -/
theorem eqOn_laurentPosPart_of_neg_eq_zero {f : ℂ → E} {a : ℤ → E} {c : ℂ} {r : ℝ} {R : ℝ≥0∞}
    (h : HasLaurentSeriesOnAnnulus f a c r R) (ha : ∀ k : ℕ, a (-((k : ℤ) + 1)) = 0) :
    EqOn f (laurentPosPart a c) (eball c R \ closedBall c r) := by
  intro w hw
  rw [h.eq_laurentPosPart_add_laurentNegPart hw, laurentNegPart_eq_zero_of_neg_eq_zero ha, add_zero]

/-- On a punctured disk (`r = 0`), if all negative-degree coefficients vanish, updating `f` at the
center `c` with `a 0` makes it agree with `laurentPosPart a c` on the whole disk `Metric.eball c R`.
-/
theorem eqOn_update_laurentPosPart_of_neg_eq_zero {f : ℂ → E} {a : ℤ → E} {c : ℂ} {R : ℝ≥0∞}
    (h : HasLaurentSeriesOnAnnulus f a c 0 R) (ha : ∀ k : ℕ, a (-((k : ℤ) + 1)) = 0) :
    EqOn (Function.update f c (a 0)) (laurentPosPart a c) (eball c R) := by
  intro w hw
  rcases eq_or_ne w c with rfl | hwc
  · simp
  · rw [Function.update_of_ne hwc]
    exact h.eqOn_laurentPosPart_of_neg_eq_zero ha ⟨hw, by simpa using hwc⟩

/-- **Removable-singularity power series extension.** If a convergent Laurent series on the
punctured disk `Metric.eball c R \ {c}` has vanishing negative-degree coefficients, then
`Function.update f c (a 0)` has the formal power series `laurentPosPowerSeries a` on all of
`Metric.eball c R`. -/
theorem hasFPowerSeriesOnBall_update_of_neg_eq_zero {f : ℂ → E} {a : ℤ → E} {c : ℂ} {R : ℝ≥0∞}
    (h : HasLaurentSeriesOnAnnulus f a c 0 R) (ha : ∀ k : ℕ, a (-((k : ℤ) + 1)) = 0) :
    HasFPowerSeriesOnBall (Function.update f c (a 0)) (laurentPosPowerSeries a) c R :=
  h.hasFPowerSeriesOnBall_laurentPosPart.congr
    (h.eqOn_update_laurentPosPart_of_neg_eq_zero ha).symm

/-- If a convergent Laurent series on `Metric.eball c R \ {c}` has vanishing negative-degree
coefficients, then `Function.update f c (a 0)` is complex-analytic on `Metric.eball c R`. -/
theorem analyticOnNhd_update_of_neg_eq_zero {f : ℂ → E} {a : ℤ → E} {c : ℂ} {R : ℝ≥0∞}
    (h : HasLaurentSeriesOnAnnulus f a c 0 R) (ha : ∀ k : ℕ, a (-((k : ℤ) + 1)) = 0) :
    AnalyticOnNhd ℂ (Function.update f c (a 0)) (eball c R) :=
  (h.hasFPowerSeriesOnBall_update_of_neg_eq_zero ha).analyticOnNhd

end CompleteSpace

end HasLaurentSeriesOnAnnulus

end TauCeti
