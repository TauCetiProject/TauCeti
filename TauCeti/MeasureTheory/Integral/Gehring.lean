/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.Analysis.SpecificLimits.Absorption
import TauCeti.MeasureTheory.Covering.DensityTheorem
import TauCeti.MeasureTheory.Covering.Vitali
import TauCeti.MeasureTheory.Integral.Average
import TauCeti.MeasureTheory.Integral.LayerCake
import TauCeti.MeasureTheory.Measure.Haar.Average
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Gehring's lemma

Let `E` be a finite-dimensional real normed space with an additive Haar measure `μ`, let `q > 1`
and `b ≥ 0`. **Gehring's lemma** says that the reverse Hölder inequality

`⨍_{B(y, ρ)} g ^ q ≤ b (⨍_{B(y, 2ρ)} g) ^ q + ⨍_{B(y, 2ρ)} h ^ q`,

assumed on every ball with `B(y, 2ρ) ⊆ B(x₀, R)`, improves itself: there is `δ₀ > 0` such that for
`0 < δ ≤ δ₀`

`⨍_{B(x₀, R/2)} g ^ (q + δ) ≤ C ((⨍_{B(x₀, R)} g ^ q) ^ ((q + δ) / q) + ⨍_{B(x₀, R)} h ^ (q + δ))`

(`TauCeti.exists_setLAverage_rpow_add_le`). The gain `δ₀` and the constant `C` do not depend on
`g`, `h`, the centre `x₀` or the radius `R`. No integrability of `g` or `h` is assumed, and the
averages are extended-valued: when `g ^ q` and `h ^ (q + δ)` have finite integrals over
`B(x₀, R)`, the right-hand side is finite, so `g` lies in `L^{q + δ}` of the half ball.

The lemma is the source of higher integrability in elliptic regularity. For a weak solution of a
divergence-form equation with bounded measurable coefficients, Caccioppoli's inequality combined
with the Sobolev–Poincaré inequality is a reverse Hölder inequality for a power of `‖∇u‖`, and
Gehring's lemma then gives Meyers' estimate `∇u ∈ L^{2 + ε}_loc`.

## The argument

* `setLIntegral_indicator_rpow_le`: the level-set estimate. For every height `t` above a threshold,
  the part of `g ^ q` above `t` on `B(x₀, r)` is bounded by `t ^ (q - 1)` times the part of `g`
  above `ε t` on `B(x₀, s)`, plus the part of `h ^ q` above `ε t`. Almost every point where
  `g > t` is the centre of a stopping ball on which the average of `g ^ q` crosses `t ^ q`; the
  reverse Hölder inequality on such a ball and a disjoint Vitali subfamily give the bound.
* `setLIntegral_mul_min_rpow_le`: integrating the level-set estimate against `δ t ^ (δ - 1)` with
  the layer-cake formula bounds `∫_{B(x₀, r)} g ^ q min(g, k) ^ δ` by a small multiple of the
  same quantity on `B(x₀, s)`, plus terms that blow up only like a power of `(s - r)⁻¹`.
* The absorption lemma over the radii `R / 2 ≤ r < s ≤ R`
  (`TauCeti.exists_le_mul_mul_rpow_add_of_le_mul_add`) removes the small multiple; the truncation
  at `k` keeps every quantity finite, and monotone convergence lets `k → ∞`.

This is the classical scheme of Gehring and of Giaquinta–Modica: a level-set estimate integrated
against a power of the height, followed by absorption. Stopping balls and the Vitali covering
lemma replace the Calderón–Zygmund cubes of the textbook proofs.

## References

* F. W. Gehring, *The `Lᵖ`-integrability of the partial derivatives of a quasiconformal mapping*,
  Acta Math. **130** (1973), 265–277, Lemma 3.
* M. Giaquinta, G. Modica, *Regularity results for some classes of higher order nonlinear elliptic
  systems*, J. Reine Angew. Math. **311/312** (1979), 145–169.
* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, 2nd ed., Section 6.4, Theorem 6.38.
-/

public section

namespace TauCeti

open MeasureTheory Metric Set Filter Module
open scoped ENNReal NNReal Topology

section General

variable {α : Type*} [MeasurableSpace α]

/-- **The estimate on a stopping set.** Let `q > 1` and let `B'` have finite measure. Suppose the
average of `g ^ q` over a set `B` is at least `t ^ q`, its average over `B'` is at most `t ^ q`,
and the reverse Hölder inequality holds from `B` to `B'`. If `b ε + ε ^ q ≤ 1 / 2`, the measure of
`B'` is controlled by the parts of `g` and `h ^ q` on `B'` above the height `ε t`. -/
private theorem measure_mul_rpow_le_of_le_setLAverage {μ : Measure α} {q : ℝ} (hq : 1 < q)
    {b ε : ℝ≥0∞} (hε : b * ε + ε ^ q ≤ 2⁻¹) {g h : α → ℝ≥0∞} {B B' : Set α}
    (hg : AEMeasurable g (μ.restrict B')) (hB' : μ B' ≠ ∞) {t : ℝ≥0∞} (ht : t ≠ ∞)
    (hlow : t ^ q ≤ ⨍⁻ x in B, g x ^ q ∂μ) (hup : ⨍⁻ x in B', g x ^ q ∂μ ≤ t ^ q)
    (hRH : ⨍⁻ x in B, g x ^ q ∂μ ≤ b * (⨍⁻ x in B', g x ∂μ) ^ q + ⨍⁻ x in B', h x ^ q ∂μ) :
    μ B' * t ^ q ≤ 2 * (b * t ^ (q - 1) * ∫⁻ x in B', {x | ε * t < g x}.indicator g x ∂μ +
      ∫⁻ x in B', {x | ε * t < h x}.indicator (fun x => h x ^ q) x ∂μ) := by
  have hq0 : 0 < q := one_pos.trans hq
  set A := ⨍⁻ x in B', g x ∂μ
  -- Jensen's inequality bounds the average of `g` by `t`, so `A ^ q ≤ t ^ (q - 1) A`.
  have hA : A ≤ t := by
    have := (rpow_laverage_le_laverage_rpow hg hq.le).trans hup
    exact (ENNReal.rpow_le_rpow_iff hq0).1 this
  have hAq : A ^ q ≤ t ^ (q - 1) * A := by
    calc A ^ q = A ^ (q - 1) * A ^ (1 : ℝ) := by
          rw [← ENNReal.rpow_add_of_nonneg _ _ (by linarith) zero_le_one, sub_add_cancel]
      _ ≤ t ^ (q - 1) * A := by
          rw [ENNReal.rpow_one]
          gcongr
  -- Split `g` and `h ^ q` at the height `ε t`.
  have hgsplit : ∫⁻ x in B', g x ∂μ ≤
      ∫⁻ x in B', {x | ε * t < g x}.indicator g x ∂μ + ε * t * μ B' := by
    rw [← setLIntegral_const, ← lintegral_add_right _ measurable_const]
    refine lintegral_mono fun x => ?_
    by_cases hx : ε * t < g x
    · rw [indicator_of_mem hx]
      exact le_self_add
    · rw [indicator_of_notMem hx, zero_add]
      exact not_lt.1 hx
  have hhsplit : ∫⁻ x in B', h x ^ q ∂μ ≤
      ∫⁻ x in B', {x | ε * t < h x}.indicator (fun x => h x ^ q) x ∂μ + ε ^ q * t ^ q * μ B' := by
    rw [← setLIntegral_const, ← lintegral_add_right _ measurable_const]
    refine lintegral_mono fun x => ?_
    by_cases hx : ε * t < h x
    · rw [indicator_of_mem hx]
      exact le_self_add
    · rw [indicator_of_notMem hx, zero_add, ← ENNReal.mul_rpow_of_nonneg _ _ hq0.le]
      exact ENNReal.rpow_le_rpow (not_lt.1 hx) hq0.le
  set G := ∫⁻ x in B', {x | ε * t < g x}.indicator g x ∂μ
  set H := ∫⁻ x in B', {x | ε * t < h x}.indicator (fun x => h x ^ q) x ∂μ
  set Y := μ B' * t ^ q with hYdef
  have hY : Y ≠ ∞ := ENNReal.mul_ne_top hB' (ENNReal.rpow_ne_top_of_nonneg hq0.le ht)
  have htt : t ^ (q - 1) * t = t ^ q := by
    conv_rhs => rw [← sub_add_cancel q 1]
    rw [ENNReal.rpow_add_of_nonneg _ _ (by linarith) zero_le_one, ENNReal.rpow_one]
  have hmain : Y ≤ b * t ^ (q - 1) * G + H + 2⁻¹ * Y := by
    calc Y ≤ μ B' * (b * A ^ q + ⨍⁻ x in B', h x ^ q ∂μ) :=
          mul_le_mul_right (hlow.trans hRH) _
      _ = b * (A ^ q * μ B') + ∫⁻ x in B', h x ^ q ∂μ := by
          rw [mul_add, measure_mul_setLAverage _ hB']
          ring
      _ ≤ b * (t ^ (q - 1) * (A * μ B')) + (H + ε ^ q * t ^ q * μ B') := by
          refine add_le_add (mul_le_mul_right ?_ _) hhsplit
          rw [← mul_assoc]
          exact mul_le_mul_left hAq _
      _ ≤ b * (t ^ (q - 1) * (G + ε * t * μ B')) + (H + ε ^ q * t ^ q * μ B') := by
          rw [mul_comm A, measure_mul_setLAverage _ hB']
          gcongr
      _ = b * t ^ (q - 1) * G + H + (b * ε + ε ^ q) * Y := by
          rw [hYdef, ← htt]
          ring
      _ ≤ b * t ^ (q - 1) * G + H + 2⁻¹ * Y := by gcongr
  -- Absorb half of `Y` into the left-hand side.
  have hhalf : 2⁻¹ * Y ≤ b * t ^ (q - 1) * G + H := by
    have h2 : 2⁻¹ * Y + 2⁻¹ * Y = Y := by rw [← add_mul, ENNReal.inv_two_add_inv_two, one_mul]
    have hne : 2⁻¹ * Y ≠ ∞ := ENNReal.mul_ne_top (by simp) hY
    exact (ENNReal.add_le_add_iff_right hne).1 (by rw [h2]; exact hmain)
  calc Y = 2 * (2⁻¹ * Y) := by rw [← mul_assoc, ENNReal.mul_inv_cancel two_ne_zero
          ENNReal.ofNat_ne_top, one_mul]
    _ ≤ 2 * (b * t ^ (q - 1) * G + H) := by gcongr

/-- The arithmetic of the thresholds in Gehring's lemma. For `q > 1`, `b ≥ 0` and a dimension `d`
there is a height ratio `ε ∈ (0, 1]` with `b ε + ε ^ q ≤ 1 / 2`, and a gain `δ₀ > 0` such that for
`0 < δ ≤ δ₀` the absorption coefficient `2 · 4 ^ d · b · δ / (q + δ - 1) · ε ^ (1 - q - δ)` is at
most `1 / 2`. -/
private theorem exists_gehring_constants {q : ℝ} (hq : 1 < q) (b : ℝ≥0) (d : ℕ) :
    ∃ ε : ℝ≥0∞, ε ≠ 0 ∧ ε ≤ 1 ∧ (b : ℝ≥0∞) * ε + ε ^ q ≤ 2⁻¹ ∧
      ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ, 0 < δ → δ ≤ δ₀ →
        2 * ENNReal.ofReal (4 ^ d) *
          (b * ENNReal.ofReal (δ / (q + δ - 1)) * ε⁻¹ ^ (q + δ - 1)) ≤ 2⁻¹ := by
  have hq0 : 0 < q := one_pos.trans hq
  have hb : (0 : ℝ) ≤ b := b.2
  set e : ℝ := (4 * ((b : ℝ) + 1))⁻¹ with he
  have he0 : 0 < e := by positivity
  have he4 : e ≤ 4⁻¹ := inv_anti₀ (by norm_num) (by linarith)
  have he1 : e ≤ 1 := he4.trans (by norm_num)
  have hbe : (b : ℝ) * e ≤ 4⁻¹ := by
    rw [he, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    linarith
  have heq : e ^ q ≤ e := by simpa using Real.rpow_le_rpow_of_exponent_ge he0 he1 hq.le
  have hhalf : (2 : ℝ≥0∞)⁻¹ = ENNReal.ofReal 2⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]
  have hinv : (ENNReal.ofReal e)⁻¹ = ENNReal.ofReal e⁻¹ := (ENNReal.ofReal_inv_of_pos he0).symm
  refine ⟨ENNReal.ofReal e, by simpa using he0, ENNReal.ofReal_le_one.2 he1, ?_, ?_⟩
  · rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul hb,
      ENNReal.ofReal_rpow_of_nonneg he0.le hq0.le, ← ENNReal.ofReal_add (by positivity)
      (by positivity), hhalf]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  set D : ℝ := 4 ^ d with hD
  have hD0 : 0 < D := by positivity
  have heq0 : 0 < e ^ q := Real.rpow_pos_of_pos he0 q
  refine ⟨min 1 ((q - 1) * e ^ q / (4 * D * (b + 1))),
    lt_min one_pos (by have := sub_pos.2 hq; positivity), fun δ hδ hδ₀ => ?_⟩
  have hp : 0 < q + δ - 1 := by linarith
  have hδ1 : δ ≤ 1 := hδ₀.trans (min_le_left _ _)
  have hδ2 : δ ≤ (q - 1) * e ^ q / (4 * D * (b + 1)) := hδ₀.trans (min_le_right _ _)
  -- The real form of the coefficient.
  have hreal : 2 * D * b * (δ / (q + δ - 1)) * e⁻¹ ^ (q + δ - 1) ≤ 2⁻¹ := by
    have h1 : e⁻¹ ^ (q + δ - 1) ≤ (e ^ q)⁻¹ := by
      rw [← Real.inv_rpow he0.le]
      exact Real.rpow_le_rpow_of_exponent_le (one_le_inv₀ he0 |>.2 he1) (by linarith)
    have h2 : δ / (q + δ - 1) ≤ δ / (q - 1) :=
      div_le_div_of_nonneg_left hδ.le (sub_pos.2 hq) (by linarith)
    have h3 : δ / (q - 1) * (e ^ q)⁻¹ ≤ (4 * D * (b + 1))⁻¹ := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (sub_pos.2 hq), ← div_eq_mul_inv,
        div_le_iff₀ heq0, inv_mul_eq_div, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      rw [le_div_iff₀ (by positivity)] at hδ2
      linarith
    calc 2 * D * b * (δ / (q + δ - 1)) * e⁻¹ ^ (q + δ - 1)
        ≤ 2 * D * b * (δ / (q - 1)) * (e ^ q)⁻¹ := by gcongr
      _ = 2 * D * b * (δ / (q - 1) * (e ^ q)⁻¹) := by ring
      _ ≤ 2 * D * b * (4 * D * (b + 1))⁻¹ := by gcongr
      _ ≤ 2⁻¹ := by
        rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]
        nlinarith
  rw [hhalf, hinv, ENNReal.ofReal_rpow_of_nonneg (inv_nonneg.2 he0.le) hp.le,
    ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul hb,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_ofNat 2,
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal (by simpa [mul_assoc] using hreal)

/-- `t₀ ^ δ` for the threshold `t₀ = ((16 R / u) ^ d a) ^ (1 / q)` of Gehring's lemma, written as a
power of the gap `u`. -/
private theorem rpow_inv_rpow_eq {d : ℕ} {q δ R a u : ℝ} (hR : 0 ≤ R) (ha : 0 ≤ a) (hu : 0 < u) :
    (((16 * R / u) ^ d * a) ^ q⁻¹) ^ δ =
      (16 * R) ^ (d * δ / q) * a ^ (δ / q) * u ^ (-(d * δ / q)) := by
  have h16 : 0 ≤ 16 * R / u := by positivity
  rw [← Real.rpow_mul (by positivity), Real.mul_rpow (by positivity) ha, ← Real.rpow_natCast,
    ← Real.rpow_mul h16, Real.div_rpow (by positivity) hu.le, Real.rpow_neg hu.le]
  field_simp

end General

section Euclidean

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- **The level-set estimate behind Gehring's lemma.** Let `r < s ≤ R` and let `g` satisfy
the reverse Hölder inequality on every ball `B(y, ρ)` with `B(y, 2ρ) ⊆ B(x₀, R)`. At every height
`t` whose `q`-th power dominates `(16 R / (s - r)) ^ dim E` times the average of `g ^ q` over
`B(x₀, R)`, the part of `g ^ q` on `B(x₀, r)` above `t` is controlled on `B(x₀, s)` by the parts
of `g` and `h ^ q` above `ε t`. -/
private theorem setLIntegral_indicator_rpow_le {q : ℝ} (hq : 1 < q) {b ε : ℝ≥0∞}
    (hε : b * ε + ε ^ q ≤ 2⁻¹) {g h : E → ℝ≥0∞} (hg : Measurable g) {x₀ : E} {R r s : ℝ}
    (hrs : r < s) (hsR : s ≤ R) (hfin : ∫⁻ x in ball x₀ R, g x ^ q ∂μ ≠ ∞)
    (hRH : ∀ y ρ, 0 < ρ → ball y (2 * ρ) ⊆ ball x₀ R →
      ⨍⁻ x in ball y ρ, g x ^ q ∂μ ≤
        b * (⨍⁻ x in ball y (2 * ρ), g x ∂μ) ^ q + ⨍⁻ x in ball y (2 * ρ), h x ^ q ∂μ)
    {t : ℝ≥0∞} (ht : t ≠ ∞)
    (hT : ENNReal.ofReal ((16 * R / (s - r)) ^ finrank ℝ E) * ⨍⁻ x in ball x₀ R, g x ^ q ∂μ ≤
      t ^ q) :
    ∫⁻ x in ball x₀ r, {x | t < g x}.indicator (fun x => g x ^ q) x ∂μ ≤
      2 * ENNReal.ofReal (4 ^ finrank ℝ E) *
        (b * t ^ (q - 1) * ∫⁻ x in ball x₀ s, {x | ε * t < g x}.indicator g x ∂μ +
          ∫⁻ x in ball x₀ s, {x | ε * t < h x}.indicator (fun x => h x ^ q) x ∂μ) := by
  have hq0 : 0 < q := one_pos.trans hq
  set ρm := (s - r) / 16 with hρm
  have hρm0 : 0 < ρm := by rw [hρm]; linarith
  set G : E → ℝ≥0∞ := fun x => g x ^ q with hGdef
  -- The radii at which the average of `g ^ q` over `B(x, ρ)` exceeds `t ^ q`.
  set S : E → Set ℝ := fun x => {ρ | 0 < ρ ∧ ρ ≤ ρm ∧ t ^ q < ⨍⁻ y in ball x ρ, G y ∂μ}
  have hsub : ∀ x ∈ ball x₀ r, ∀ ρ, ρ ≤ 8 * ρm → ball x ρ ⊆ ball x₀ s := by
    intro x hx ρ hρ
    refine ball_subset_ball' ?_
    rw [mem_ball] at hx
    linarith
  have hsubR : ball x₀ s ⊆ ball x₀ R := ball_subset_ball hsR
  -- Averages over balls of radius between `ρm` and `8 ρm` are controlled by `hT`.
  have hlarge : ∀ x ∈ ball x₀ r, ∀ ρ, ρm < ρ → ρ ≤ 8 * ρm →
      ⨍⁻ y in ball x ρ, G y ∂μ ≤ t ^ q := by
    intro x hx ρ h1 h2
    have hρ0 : 0 < ρ := hρm0.trans h1
    refine (setLAverage_ball_le G hρ0 ((hsub x hx ρ h2).trans hsubR)).trans (le_trans ?_ hT)
    have hR : 0 ≤ R := by
      have := mem_ball.1 hx
      linarith [dist_nonneg (x := x) (y := x₀)]
    have hle : R / ρ ≤ 16 * R / (s - r) := by
      rw [div_le_div_iff₀ hρ0 (by linarith)]
      rw [hρm] at h1
      nlinarith
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal
      (pow_le_pow_left₀ (div_nonneg hR hρ0.le) hle _)) _
  -- The stopping radius: no radius in `S x` is twice as large.
  have hstop : ∀ x ∈ ball x₀ r, (S x).Nonempty → ∃ ρ ∈ S x, ∀ ρ', 2 * ρ ≤ ρ' → ρ' ≤ 8 * ρm →
      ⨍⁻ y in ball x ρ', G y ∂μ ≤ t ^ q := by
    intro x hx hne
    have hbdd : BddAbove (S x) := ⟨ρm, fun ρ hρ => hρ.2.1⟩
    have hσ : 0 < sSup (S x) := hne.some_mem.1.trans_le (le_csSup hbdd hne.some_mem)
    obtain ⟨ρ, hρS, hρ⟩ := exists_lt_of_lt_csSup hne (half_lt_self hσ)
    have hmax : ∀ ρ' ∈ S x, ρ' < 2 * ρ := fun ρ' hρ' => by linarith [le_csSup hbdd hρ']
    refine ⟨ρ, hρS, fun ρ' h1 h2 => ?_⟩
    rcases le_or_gt ρ' ρm with h3 | h3
    · by_contra hcon
      exact (not_lt.2 h1) (hmax ρ' ⟨by linarith [hρS.1], h3, not_le.1 hcon⟩)
    · exact hlarge x hx ρ' h3 h2
  -- Lebesgue's differentiation theorem: almost every point where `g > t` has a radius in `S x`.
  have hleb : ∀ᵐ x ∂μ, x ∈ ball x₀ r → t < g x → (S x).Nonempty := by
    set F := (ball x₀ R).indicator G
    have hF : AEMeasurable F μ := ((hg.pow_const q).indicator measurableSet_ball).aemeasurable
    have hFfin : ∫⁻ x, F x ∂μ ≠ ∞ := by rwa [lintegral_indicator measurableSet_ball]
    filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_setLAverage_closedBall μ hF hFfin]
      with x hx hxr htg
    have hxR : x ∈ ball x₀ R := hsubR (ball_subset_ball hrs.le hxr)
    have hFx : F x = G x := indicator_of_mem hxR G
    have hev : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), t ^ q < ⨍⁻ y in closedBall x ρ, F y ∂μ :=
      hx (Ioi_mem_nhds (by rw [hFx]; exact ENNReal.rpow_lt_rpow htg hq0))
    have hpos : 0 < min ρm (R - dist x x₀) := lt_min hρm0 (sub_pos.2 (mem_ball.1 hxR))
    have hev2 : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ρ < min ρm (R - dist x x₀) :=
      nhdsWithin_le_nhds (Iio_mem_nhds hpos)
    obtain ⟨ρ, h1, h2, h3⟩ := (hev.and (hev2.and self_mem_nhdsWithin)).exists
    refine ⟨ρ, h3, (h2.trans_le (min_le_left _ _)).le, ?_⟩
    -- Pass from the closed ball, on which `F = G`, to the open ball.
    have hcl : closedBall x ρ ⊆ ball x₀ R :=
      closedBall_subset_ball' (by linarith [h2.trans_le (min_le_right _ _)])
    have hae := μ.addHaar_closedBall_ae_eq_ball_of_ne_zero x ρ (ne_of_gt h3)
    rwa [setLAverage_eq, setLIntegral_congr_fun measurableSet_closedBall
        (fun y hy => indicator_of_mem (hcl hy) G), setLIntegral_congr hae, measure_congr hae,
      ← setLAverage_eq] at h1
  -- Choose the stopping radii; on each stopping ball the estimate on a stopping set applies.
  choose! ρ hρS hρbig using hstop
  set X := {x | x ∈ ball x₀ r ∧ (S x).Nonempty}
  have hball : ∀ a ∈ X, ∫⁻ x in ball a (4 * (2 * ρ a)), G x ∂μ ≤
      2 * ENNReal.ofReal (4 ^ finrank ℝ E) *
        (b * t ^ (q - 1) * ∫⁻ x in ball a (2 * ρ a), {x | ε * t < g x}.indicator g x ∂μ +
          ∫⁻ x in ball a (2 * ρ a), {x | ε * t < h x}.indicator (fun x => h x ^ q) x ∂μ) := by
    intro a ha
    have hS := hρS a ha.1 ha.2
    have hint : ∫⁻ x in ball a (4 * (2 * ρ a)), G x ∂μ ≤ t ^ q * μ (ball a (4 * (2 * ρ a))) := by
      rw [← measure_mul_setLAverage _ measure_ball_lt_top.ne, mul_comm]
      gcongr
      exact hρbig a ha.1 ha.2 _ (by linarith [hS.1]) (by linarith [hS.2.1])
    have hstopb := measure_mul_rpow_le_of_le_setLAverage hq hε (B := ball a (ρ a))
      (B' := ball a (2 * ρ a)) hg.aemeasurable measure_ball_lt_top.ne ht hS.2.2.le
      (hρbig a ha.1 ha.2 _ le_rfl (by linarith [hS.2.1]))
      (hRH a (ρ a) hS.1 ((hsub a ha.1 _ (by linarith [hS.2.1])).trans hsubR))
    calc _ ≤ t ^ q * μ (ball a (4 * (2 * ρ a))) := hint
      _ = ENNReal.ofReal (4 ^ finrank ℝ E) * (μ (ball a (2 * ρ a)) * t ^ q) := by
          rw [Measure.addHaar_ball_mul_of_pos μ _ (by norm_num : (0 : ℝ) < 4),
            ← Measure.addHaar_ball_center μ a]
          ring
      _ ≤ ENNReal.ofReal (4 ^ finrank ℝ E) * (2 * _) := mul_le_mul_right hstopb _
      _ = _ := by ring
  obtain ⟨U, hUm, hXU, hU⟩ := exists_superset_setLIntegral_le (μ := μ) (X := X) (S := ball x₀ s)
    (fun a ha => ⟨(hρS a ha.1 ha.2).1, (hρS a ha.1 ha.2).2.1⟩)
    (fun a ha => hsub a ha.1 _ (by linarith [(hρS a ha.1 ha.2).2.1])) hball
  -- Almost every point of the superlevel set lies in `X`, hence in `U`.
  refine le_trans ?_ hU
  calc _ ≤ ∫⁻ x in ball x₀ r, U.indicator G x ∂μ := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_of_ae hleb, ae_restrict_mem measurableSet_ball] with x hx hxr
        by_cases htg : t < g x
        · rw [indicator_of_mem htg, indicator_of_mem (hXU ⟨hxr, hx hxr htg⟩)]
        · rw [indicator_of_notMem htg]
          exact zero_le
    _ ≤ ∫⁻ x, U.indicator G x ∂μ := setLIntegral_le_lintegral _ _
    _ = ∫⁻ x in U, G x ∂μ := lintegral_indicator hUm _

/-- **The integrated level-set estimate.** Integrating `setLIntegral_indicator_rpow_le` against
`δ t ^ (δ - 1)` over the heights `0 < t < k` bounds the truncated integral
`Φ(r) = ∫_{B(x₀, r)} g ^ q min(g, k) ^ δ` by a small multiple of `Φ(s)`, for `δ` small. -/
private theorem setLIntegral_mul_min_rpow_le {q : ℝ} (hq : 1 < q) {b ε : ℝ≥0∞}
    (hε : b * ε + ε ^ q ≤ 2⁻¹) (hε0 : ε ≠ 0) (hε1 : ε ≤ 1) {g h : E → ℝ≥0∞} (hg : Measurable g)
    (hh : Measurable h) {x₀ : E} {R r s : ℝ} (hrs : r < s) (hsR : s ≤ R)
    (hfin : ∫⁻ x in ball x₀ R, g x ^ q ∂μ ≠ ∞)
    (hRH : ∀ y ρ, 0 < ρ → ball y (2 * ρ) ⊆ ball x₀ R →
      ⨍⁻ x in ball y ρ, g x ^ q ∂μ ≤
        b * (⨍⁻ x in ball y (2 * ρ), g x ∂μ) ^ q + ⨍⁻ x in ball y (2 * ρ), h x ^ q ∂μ)
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀)
    (hT : ENNReal.ofReal ((16 * R / (s - r)) ^ finrank ℝ E) * ⨍⁻ x in ball x₀ R, g x ^ q ∂μ ≤
      ENNReal.ofReal t₀ ^ q) (k : ℝ≥0) {δ : ℝ} (hδ : 0 < δ) :
    ∫⁻ x in ball x₀ r, g x ^ q * min (g x) k ^ δ ∂μ ≤
      ENNReal.ofReal (t₀ ^ δ) * ∫⁻ x in ball x₀ r, g x ^ q ∂μ +
        2 * ENNReal.ofReal (4 ^ finrank ℝ E) *
          (b * ENNReal.ofReal (δ / (q + δ - 1)) * ε⁻¹ ^ (q + δ - 1) *
              ∫⁻ x in ball x₀ s, g x ^ q * min (g x) k ^ δ ∂μ +
            ε⁻¹ ^ δ * ∫⁻ x in ball x₀ s, h x ^ (q + δ) ∂μ) := by
  have hq0 : 0 < q := one_pos.trans hq
  have hεtop : ε ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top hε1
  set K := 2 * ENNReal.ofReal (4 ^ finrank ℝ E)
  set G : E → ℝ≥0∞ := fun x => g x ^ q
  set ν := (μ.restrict (ball x₀ r)).withDensity G
  set ν₁ := (μ.restrict (ball x₀ s)).withDensity g
  set ν₂ := (μ.restrict (ball x₀ s)).withDensity (fun x => h x ^ q)
  set w : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (t ^ (δ - 1))
  have hw : Measurable w := (measurable_id.pow_const _).ennreal_ofReal
  have hGm : Measurable G := hg.pow_const q
  -- The superlevel sets of `g / ε` and `h / ε` are those of `g` and `h` above `ε t`.
  have hset : ∀ (f : E → ℝ≥0∞) (c : ℝ≥0∞), {x | c < f x * ε⁻¹} = {x | ε * c < f x} := by
    intro f c
    ext x
    simp only [mem_ofPred_eq, ← div_eq_mul_inv]
    rw [ENNReal.lt_div_iff_mul_lt (Or.inl hε0) (Or.inl hεtop), mul_comm]
  -- The pointwise bound on the distribution function of `g` with respect to `ν`.
  set A : ℝ → ℝ≥0∞ := fun t => ν {x | ENNReal.ofReal t < ENNReal.ofReal t₀}
  set N₁ : ℝ → ℝ≥0∞ := fun t => ν₁ {x | ENNReal.ofReal t < g x * ε⁻¹}
  set N₂ : ℝ → ℝ≥0∞ := fun t => ν₂ {x | ENNReal.ofReal t < h x * ε⁻¹}
  have hpt : ∀ t, 0 < t → ν {x | ENNReal.ofReal t < g x} ≤
      A t + K * (b * ENNReal.ofReal t ^ (q - 1) * N₁ t + N₂ t) := by
    intro t ht
    rcases lt_or_ge t t₀ with htt | htt
    · have : {x : E | ENNReal.ofReal t < ENNReal.ofReal t₀} = univ :=
        eq_univ_of_forall fun _ => (ENNReal.ofReal_lt_ofReal_iff (ht.trans htt)).2 htt
      calc ν {x | ENNReal.ofReal t < g x} ≤ A t := by
            simp only [A, this]
            exact measure_mono (subset_univ _)
        _ ≤ _ := le_self_add
    · refine le_add_left ?_
      have hlev := setLIntegral_indicator_rpow_le hq hε hg (μ := μ) (h := h) hrs hsR hfin hRH
        ENNReal.ofReal_ne_top (hT.trans (ENNReal.rpow_le_rpow
          (ENNReal.ofReal_le_ofReal htt) hq0.le))
      have hg' := measurableSet_lt (measurable_const (a := ENNReal.ofReal t)) hg
      have hg'' := measurableSet_lt (measurable_const (a := ε * ENNReal.ofReal t)) hg
      have hh'' := measurableSet_lt (measurable_const (a := ε * ENNReal.ofReal t)) hh
      simp only [N₁, N₂, ν, ν₁, ν₂, hset, withDensity_apply _ hg', withDensity_apply _ hg'',
        withDensity_apply _ hh'', ← lintegral_indicator hg', ← lintegral_indicator hg'',
        ← lintegral_indicator hh'']
      exact hlev
  -- Measurability of the pieces in `t`.
  have hAm : Measurable A := Measure.measurable_measure_ofReal_lt _ _
  have hN₁m : Measurable N₁ := Measure.measurable_measure_ofReal_lt _ _
  have hN₂m : Measurable N₂ := Measure.measurable_measure_ofReal_lt _ _
  have hpowm : Measurable fun t : ℝ => ENNReal.ofReal t ^ (q - 1) :=
    ENNReal.measurable_ofReal.pow_const _
  -- The three layer cake bounds.
  have hIA : ENNReal.ofReal δ * ∫⁻ t in Ioo 0 (k : ℝ), A t * w t ≤
      ENNReal.ofReal (t₀ ^ δ) * ∫⁻ x in ball x₀ r, g x ^ q ∂μ := by
    refine (Measure.ofReal_mul_setLIntegral_measure_lt_const_le ν ht₀ k hδ).trans_eq ?_
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hIB := Measure.ofReal_mul_setLIntegral_withDensity_lt_le (μ.restrict (ball x₀ s)) hg hε0 hε1
    b k hq hδ
  have hIC := Measure.ofReal_mul_setLIntegral_withDensity_rpow_lt_le (μ.restrict (ball x₀ s)) hh
    hε0 k hq0.le hδ
  -- Assemble.
  have hlhs : ∫⁻ x in ball x₀ r, g x ^ q * min (g x) k ^ δ ∂μ =
      ENNReal.ofReal δ * ∫⁻ t in Ioo 0 (k : ℝ), ν {x | ENNReal.ofReal t < g x} * w t := by
    rw [← Measure.lintegral_min_rpow_eq ν hg.aemeasurable k hδ,
      lintegral_withDensity_eq_lintegral_mul _ hGm ((hg.min measurable_const).pow_const _)]
    rfl
  rw [hlhs]
  calc ENNReal.ofReal δ * ∫⁻ t in Ioo 0 (k : ℝ), ν {x | ENNReal.ofReal t < g x} * w t
      ≤ ENNReal.ofReal δ * ∫⁻ t in Ioo 0 (k : ℝ), (A t * w t +
          (K * (b * ENNReal.ofReal t ^ (q - 1) * N₁ t * w t) + K * (N₂ t * w t))) := by
        refine mul_le_mul_right (setLIntegral_mono' measurableSet_Ioo fun t ht => ?_) _
        calc ν {x | ENNReal.ofReal t < g x} * w t
            ≤ (A t + K * (b * ENNReal.ofReal t ^ (q - 1) * N₁ t + N₂ t)) * w t := by
              gcongr
              exact hpt t ht.1
          _ = _ := by ring
    _ = ENNReal.ofReal δ * (∫⁻ t in Ioo 0 (k : ℝ), A t * w t) +
          K * (ENNReal.ofReal δ *
              (∫⁻ t in Ioo 0 (k : ℝ), b * ENNReal.ofReal t ^ (q - 1) * N₁ t * w t) +
            ENNReal.ofReal δ * ∫⁻ t in Ioo 0 (k : ℝ), N₂ t * w t) := by
        have h1 : Measurable fun t => A t * w t := hAm.mul hw
        have h2 : Measurable fun t => b * ENNReal.ofReal t ^ (q - 1) * N₁ t * w t :=
          ((measurable_const.mul hpowm).mul hN₁m).mul hw
        have h3 : Measurable fun t => N₂ t * w t := hN₂m.mul hw
        have h4 : Measurable fun t => K * (b * ENNReal.ofReal t ^ (q - 1) * N₁ t * w t) :=
          measurable_const.mul h2
        rw [lintegral_add_left h1, lintegral_add_left h4,
          lintegral_const_mul _ h2, lintegral_const_mul _ h3]
        ring
    _ ≤ _ := add_le_add hIA (mul_le_mul_right (add_le_add hIB hIC) _)

/-- **Absorption for a fixed truncation.** Feeding `setLIntegral_mul_min_rpow_le` into the
absorption lemma bounds the truncated integral `∫_{B(x₀, R / 2)} g ^ q min(g, k) ^ δ` independently
of `k`. Here `C₀` is the constant of the absorption lemma for the coefficient `θ` of
`setLIntegral_mul_min_rpow_le` and the exponent `dim E · δ / q`. -/
private theorem toReal_setLIntegral_mul_min_rpow_le {q : ℝ} (hq : 1 < q) {b ε : ℝ≥0∞}
    (hε : b * ε + ε ^ q ≤ 2⁻¹) (hε0 : ε ≠ 0) (hε1 : ε ≤ 1) {δ C₀ : ℝ} (hδ : 0 < δ)
    (hθ : 2 * ENNReal.ofReal (4 ^ finrank ℝ E) *
      (b * ENNReal.ofReal (δ / (q + δ - 1)) * ε⁻¹ ^ (q + δ - 1)) ≤ 2⁻¹)
    (hC₀ : ∀ {f : ℝ → ℝ} {r₀ r₁ A B : ℝ}, r₀ < r₁ → 0 ≤ A → 0 ≤ B →
      BddAbove (f '' Icc r₀ r₁) →
      (∀ s t, r₀ ≤ s → s < t → t ≤ r₁ → f s ≤
        (2 * ENNReal.ofReal (4 ^ finrank ℝ E) *
          (b * ENNReal.ofReal (δ / (q + δ - 1)) * ε⁻¹ ^ (q + δ - 1))).toReal * f t +
          A * (t - s) ^ (-(finrank ℝ E * δ / q)) + B) →
      f r₀ ≤ C₀ * (A * (r₁ - r₀) ^ (-(finrank ℝ E * δ / q)) + B))
    {g h : E → ℝ≥0∞} (hg : Measurable g) (hh : Measurable h) {x₀ : E} {R : ℝ} (hR : 0 < R)
    (hRH : ∀ y ρ, 0 < ρ → ball y (2 * ρ) ⊆ ball x₀ R →
      ⨍⁻ x in ball y ρ, g x ^ q ∂μ ≤
        b * (⨍⁻ x in ball y (2 * ρ), g x ∂μ) ^ q + ⨍⁻ x in ball y (2 * ρ), h x ^ q ∂μ)
    (hIg : ∫⁻ x in ball x₀ R, g x ^ q ∂μ ≠ ∞) (hIh : ∫⁻ x in ball x₀ R, h x ^ (q + δ) ∂μ ≠ ∞)
    (k : ℝ≥0) :
    ∫⁻ x in ball x₀ (R / 2), g x ^ q * min (g x) k ^ δ ∂μ ≤ ENNReal.ofReal
      (C₀ * ((16 * R) ^ (finrank ℝ E * δ / q) * (⨍⁻ x in ball x₀ R, g x ^ q ∂μ).toReal ^ (δ / q) *
          (∫⁻ x in ball x₀ R, g x ^ q ∂μ).toReal * (R / 2) ^ (-(finrank ℝ E * δ / q)) +
        (2 * ENNReal.ofReal (4 ^ finrank ℝ E) * ε⁻¹ ^ δ *
          ∫⁻ x in ball x₀ R, h x ^ (q + δ) ∂μ).toReal)) := by
  have hq0 : 0 < q := one_pos.trans hq
  set d := finrank ℝ E
  set β : ℝ := d * δ / q
  set K := 2 * ENNReal.ofReal (4 ^ d)
  set θE := K * (b * ENNReal.ofReal (δ / (q + δ - 1)) * ε⁻¹ ^ (q + δ - 1))
  set Ig := ∫⁻ x in ball x₀ R, g x ^ q ∂μ
  set Ih := ∫⁻ x in ball x₀ R, h x ^ (q + δ) ∂μ
  set a := (⨍⁻ x in ball x₀ R, g x ^ q ∂μ).toReal
  set Φ : ℝ → ℝ≥0∞ := fun ρ => ∫⁻ x in ball x₀ ρ, g x ^ q * min (g x) k ^ δ ∂μ
  have hθtop : θE ≠ ∞ := ne_top_of_le_ne_top (by simp) hθ
  have hKtop : K * ε⁻¹ ^ δ * Ih ≠ ∞ := ENNReal.mul_ne_top (ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top)
    (ENNReal.rpow_ne_top_of_nonneg hδ.le (ENNReal.inv_ne_top.2 hε0))) hIh
  have hav : ⨍⁻ x in ball x₀ R, g x ^ q ∂μ = ENNReal.ofReal a := by
    rw [ENNReal.ofReal_toReal]
    rw [setLAverage_eq]
    exact ENNReal.div_ne_top hIg (measure_ball_pos μ x₀ hR).ne'
  -- The truncated integrals are finite.
  have hΦtop : ∀ ρ ≤ R, Φ ρ ≤ (k : ℝ≥0∞) ^ δ * Ig := by
    intro ρ hρ
    calc Φ ρ ≤ ∫⁻ x in ball x₀ R, g x ^ q * min (g x) k ^ δ ∂μ :=
          lintegral_mono_set (ball_subset_ball hρ)
      _ ≤ ∫⁻ x in ball x₀ R, (k : ℝ≥0∞) ^ δ * g x ^ q ∂μ := by
          refine lintegral_mono fun x => ?_
          rw [mul_comm]
          gcongr
          exact min_le_right _ _
      _ = _ := lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hδ.le ENNReal.coe_ne_top)
  have hkI : (k : ℝ≥0∞) ^ δ * Ig ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hδ.le ENNReal.coe_ne_top) hIg
  have hΦne : ∀ ρ ≤ R, Φ ρ ≠ ∞ := fun ρ hρ => ne_top_of_le_ne_top hkI (hΦtop ρ hρ)
  -- The step inequality between radii `R / 2 ≤ r < s ≤ R`.
  have hstep : ∀ r s, R / 2 ≤ r → r < s → s ≤ R → (Φ r).toReal ≤
      θE.toReal * (Φ s).toReal + (16 * R) ^ β * a ^ (δ / q) * Ig.toReal * (s - r) ^ (-β) +
        (K * ε⁻¹ ^ δ * Ih).toReal := by
    intro r s hr hrs hsR
    have hu : 0 < s - r := sub_pos.2 hrs
    set X := (16 * R / (s - r)) ^ d * a
    have hX : 0 ≤ X := by positivity
    have hT : ENNReal.ofReal ((16 * R / (s - r)) ^ d) * ⨍⁻ x in ball x₀ R, g x ^ q ∂μ ≤
        ENNReal.ofReal (X ^ q⁻¹) ^ q := by
      rw [hav, ← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_rpow_of_nonneg
        (by positivity) hq0.le, Real.rpow_inv_rpow hX hq0.ne']
    have h3 := setLIntegral_mul_min_rpow_le hq hε hε0 hε1 hg hh hrs hsR hIg hRH
      (by positivity) hT k hδ
    have hle : Φ r ≤ ENNReal.ofReal ((X ^ q⁻¹) ^ δ) * Ig + θE * Φ s + K * ε⁻¹ ^ δ * Ih := by
      refine h3.trans ?_
      have h0 : ∫⁻ x in ball x₀ r, g x ^ q ∂μ ≤ Ig :=
        lintegral_mono_set (ball_subset_ball (hrs.le.trans hsR))
      have h1 : ∫⁻ x in ball x₀ s, h x ^ (q + δ) ∂μ ≤ Ih :=
        lintegral_mono_set (ball_subset_ball hsR)
      calc _ ≤ ENNReal.ofReal ((X ^ q⁻¹) ^ δ) * Ig + K * (b * ENNReal.ofReal (δ / (q + δ - 1)) *
            ε⁻¹ ^ (q + δ - 1) * Φ s + ε⁻¹ ^ δ * Ih) := by gcongr
        _ = _ := by ring
    have hfin1 : ENNReal.ofReal ((X ^ q⁻¹) ^ δ) * Ig ≠ ∞ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hIg
    have hfin2 : θE * Φ s ≠ ∞ := ENNReal.mul_ne_top hθtop (hΦne s hsR)
    have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨hfin1, hfin2⟩, hKtop⟩)
      hle
    rw [ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨hfin1, hfin2⟩) hKtop,
      ENNReal.toReal_add hfin1 hfin2,
      ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
      rpow_inv_rpow_eq hR.le ENNReal.toReal_nonneg hu] at this
    linarith
  have hbdd : BddAbove ((fun ρ => (Φ ρ).toReal) '' Icc (R / 2) R) :=
    ⟨((k : ℝ≥0∞) ^ δ * Ig).toReal, by
      rintro _ ⟨ρ, hρ, rfl⟩
      exact ENNReal.toReal_mono hkI (hΦtop ρ hρ.2)⟩
  have := hC₀ (f := fun ρ => (Φ ρ).toReal) (by linarith) (by positivity) ENNReal.toReal_nonneg hbdd
    hstep
  rw [show R - R / 2 = R / 2 by ring] at this
  exact (ENNReal.le_ofReal_iff_toReal_le (hΦne _ (by linarith))
    (ENNReal.toReal_nonneg.trans this)).2 this

/-- Gehring's lemma for measurable functions; see `exists_setLAverage_rpow_add_le`. -/
private theorem exists_setLAverage_rpow_add_le_of_measurable {q : ℝ} (hq : 1 < q) (b : ℝ≥0) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ, 0 < δ → δ ≤ δ₀ → ∃ C : ℝ≥0, ∀ {g h : E → ℝ≥0∞} {x₀ : E} {R : ℝ},
      0 < R → Measurable g → Measurable h →
      (∀ y ρ, 0 < ρ → ball y (2 * ρ) ⊆ ball x₀ R →
        ⨍⁻ x in ball y ρ, g x ^ q ∂μ ≤
          b * (⨍⁻ x in ball y (2 * ρ), g x ∂μ) ^ q + ⨍⁻ x in ball y (2 * ρ), h x ^ q ∂μ) →
      ⨍⁻ x in ball x₀ (R / 2), g x ^ (q + δ) ∂μ ≤
        C * ((⨍⁻ x in ball x₀ R, g x ^ q ∂μ) ^ ((q + δ) / q) +
          ⨍⁻ x in ball x₀ R, h x ^ (q + δ) ∂μ) := by
  have hq0 : 0 < q := one_pos.trans hq
  obtain ⟨ε, hε0, hε1, hε, δ₀, hδ₀, hθ⟩ := exists_gehring_constants hq b (finrank ℝ E)
  refine ⟨δ₀, hδ₀, fun δ hδ hδδ₀ => ?_⟩
  set d := finrank ℝ E
  set β : ℝ := d * δ / q
  have hθE := hθ δ hδ hδδ₀
  have hθ1 : (2 * ENNReal.ofReal (4 ^ d) *
      ((b : ℝ≥0∞) * ENNReal.ofReal (δ / (q + δ - 1)) * ε⁻¹ ^ (q + δ - 1))).toReal < 1 := by
    have := ENNReal.toReal_mono (by simp) hθE
    rw [ENNReal.toReal_inv, ENNReal.toReal_ofNat] at this
    linarith
  obtain ⟨C₀, hC₀pos, hC₀⟩ := exists_le_mul_mul_rpow_add_of_le_mul_add ENNReal.toReal_nonneg hθ1 β
  set Kh := (2 * ENNReal.ofReal (4 ^ d) * ε⁻¹ ^ δ).toReal
  have hKh : 0 ≤ Kh := ENNReal.toReal_nonneg
  set C : ℝ := C₀ * 2 ^ d * (32 ^ β + Kh)
  have hC : 0 < C := by positivity
  refine ⟨C.toNNReal, fun {g h x₀ R} hR hg hh hRH => ?_⟩
  have hCne : (C.toNNReal : ℝ≥0∞) ≠ 0 := by simpa using hC
  have hB₀ : μ (ball x₀ R) ≠ ∞ := measure_ball_lt_top.ne
  -- If either integral on the right is infinite, there is nothing to prove.
  by_cases hIg : ∫⁻ x in ball x₀ R, g x ^ q ∂μ = ∞
  · rw [setLAverage_eq μ (fun x => g x ^ q) (ball x₀ R), hIg, ENNReal.top_div_of_ne_top hB₀,
      ENNReal.top_rpow_of_pos (by positivity), top_add, ENNReal.mul_top hCne]
    exact le_top
  by_cases hIh : ∫⁻ x in ball x₀ R, h x ^ (q + δ) ∂μ = ∞
  · rw [setLAverage_eq μ (fun x => h x ^ (q + δ)) (ball x₀ R), hIh, ENNReal.top_div_of_ne_top hB₀,
      add_top, ENNReal.mul_top hCne]
    exact le_top
  -- Let the truncation level tend to infinity.
  have hk := toReal_setLIntegral_mul_min_rpow_le hq hε hε0 hε1 hδ hθE hC₀ hg hh hR hRH hIg hIh
  have hlim := Measure.tendsto_lintegral_mul_min_rpow (μ.restrict (ball x₀ (R / 2))) hg hq0.le hδ
  have hJ := le_of_tendsto' hlim fun k => hk k
  -- Rewrite both sides in terms of real numbers.
  set m := μ (ball x₀ (R / 2))
  have hm0 : m ≠ 0 := (measure_ball_pos μ x₀ (by positivity)).ne'
  have hmtop : m ≠ ∞ := measure_ball_lt_top.ne
  set mr := m.toReal
  have hmr : 0 < mr := ENNReal.toReal_pos hm0 hmtop
  have hB₀eq : μ (ball x₀ R) = ENNReal.ofReal (2 ^ d * mr) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hmtop]
    conv_lhs => rw [show R = 2 * (R / 2) by ring]
    rw [Measure.addHaar_ball_mul_of_pos μ x₀ two_pos (R / 2), ← Measure.addHaar_ball_center μ x₀]
  set a := (⨍⁻ x in ball x₀ R, g x ^ q ∂μ).toReal
  have ha : 0 ≤ a := ENNReal.toReal_nonneg
  have hav : ⨍⁻ x in ball x₀ R, g x ^ q ∂μ = ENNReal.ofReal a := by
    rw [ENNReal.ofReal_toReal]
    rw [setLAverage_eq]
    exact ENNReal.div_ne_top hIg (measure_ball_pos μ x₀ hR).ne'
  have hIgr : (∫⁻ x in ball x₀ R, g x ^ q ∂μ).toReal = 2 ^ d * mr * a := by
    rw [← measure_mul_setLAverage _ hB₀, hav, hB₀eq, ← ENNReal.ofReal_mul (by positivity),
      ENNReal.toReal_ofReal (by positivity)]
  set Ihr := (∫⁻ x in ball x₀ R, h x ^ (q + δ) ∂μ).toReal
  have hIhr : 0 ≤ Ihr := ENNReal.toReal_nonneg
  have havh : ⨍⁻ x in ball x₀ R, h x ^ (q + δ) ∂μ = ENNReal.ofReal (Ihr / (2 ^ d * mr)) := by
    rw [setLAverage_eq, hB₀eq, ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_toReal hIh]
  have h32 : (16 * R) ^ β * (R / 2) ^ (-β) = 32 ^ β := by
    rw [Real.rpow_neg (by positivity), ← div_eq_mul_inv, ← Real.div_rpow (by positivity)
      (by positivity)]
    congr 1
    field_simp
    norm_num
  have hP : a ^ (δ / q) * a = a ^ ((q + δ) / q) := by
    rw [show (q + δ) / q = δ / q + 1 by field_simp; ring, Real.rpow_add' ha (by positivity),
      Real.rpow_one]
  set P := a ^ ((q + δ) / q)
  have hP0 : 0 ≤ P := by positivity
  rw [setLAverage_eq, hav, havh, ENNReal.ofReal_rpow_of_nonneg ha (by positivity),
    ← ENNReal.ofReal_add hP0 (by positivity), ← ENNReal.ofReal.eq_def, ← ENNReal.ofReal_mul hC.le,
    ENNReal.div_le_iff hm0 hmtop, ← ENNReal.ofReal_toReal hmtop,
    ← ENNReal.ofReal_mul (by positivity)]
  refine hJ.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [hIgr, ENNReal.toReal_mul]
  have hrhs : C * (P + Ihr / (2 ^ d * mr)) * mr =
      C₀ * (2 ^ d * 32 ^ β * mr * P + 2 ^ d * Kh * mr * P + 32 ^ β * Ihr + Kh * Ihr) := by
    simp only [C]
    field_simp
    ring
  calc C₀ * ((16 * R) ^ β * a ^ (δ / q) * (2 ^ d * mr * a) * (R / 2) ^ (-β) + Kh * Ihr)
      = C₀ * (2 ^ d * 32 ^ β * mr * P + Kh * Ihr) := by
        rw [← h32, ← hP]
        ring
    _ ≤ _ := by
        rw [hrhs]
        gcongr
        have : 0 ≤ 2 ^ d * Kh * mr * P + 32 ^ β * Ihr := by positivity
        linarith

/-- **Gehring's lemma.** Let `q > 1` and `b ≥ 0`. There is `δ₀ > 0` such that for every
`0 < δ ≤ δ₀` there is a constant `C`, independent of the functions, the centre and the radius, with
the following property. Let `g` and `h` be nonnegative and a.e. measurable on a ball `B(x₀, R)`,
and suppose that `g` satisfies the reverse Hölder inequality

`⨍_{B(y, ρ)} g ^ q ≤ b (⨍_{B(y, 2ρ)} g) ^ q + ⨍_{B(y, 2ρ)} h ^ q`

on every ball with `B(y, 2ρ) ⊆ B(x₀, R)`. Then

`⨍_{B(x₀, R/2)} g ^ (q + δ) ≤ C ((⨍_{B(x₀, R)} g ^ q) ^ ((q + δ) / q) + ⨍_{B(x₀, R)} h ^ (q + δ))`.

No integrability is assumed and the averages are extended-valued. If the integrals of `g ^ q` and
`h ^ (q + δ)` over `B(x₀, R)` are finite, the right-hand side is finite, so `g` is integrable to the
higher power `q + δ` on the half ball; otherwise the right-hand side is infinite. -/
theorem exists_setLAverage_rpow_add_le {q : ℝ} (hq : 1 < q) (b : ℝ≥0) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ, 0 < δ → δ ≤ δ₀ → ∃ C : ℝ≥0, ∀ {g h : E → ℝ≥0∞} {x₀ : E} {R : ℝ},
      AEMeasurable g (μ.restrict (ball x₀ R)) →
      AEMeasurable h (μ.restrict (ball x₀ R)) →
      (∀ y ρ, 0 < ρ → ball y (2 * ρ) ⊆ ball x₀ R →
        ⨍⁻ x in ball y ρ, g x ^ q ∂μ ≤
          b * (⨍⁻ x in ball y (2 * ρ), g x ∂μ) ^ q + ⨍⁻ x in ball y (2 * ρ), h x ^ q ∂μ) →
      ⨍⁻ x in ball x₀ (R / 2), g x ^ (q + δ) ∂μ ≤
        C * ((⨍⁻ x in ball x₀ R, g x ^ q ∂μ) ^ ((q + δ) / q) +
          ⨍⁻ x in ball x₀ R, h x ^ (q + δ) ∂μ) := by
  obtain ⟨δ₀, hδ₀, hmain⟩ := exists_setLAverage_rpow_add_le_of_measurable (μ := μ) hq b
  refine ⟨δ₀, hδ₀, fun δ hδ hδδ₀ => ?_⟩
  obtain ⟨C, hC⟩ := hmain δ hδ hδδ₀
  refine ⟨C, fun {g h x₀ R} hg hh hRH => ?_⟩
  -- For `R ≤ 0` the half ball is empty.
  rcases le_or_gt R 0 with hR | hR
  · simp [ball_eq_empty.2 (by linarith : R / 2 ≤ 0)]
  -- Replace `g` and `h` by measurable functions equal to them almost everywhere on `B(x₀, R)`.
  have hav : ∀ {A : Set E}, A ⊆ ball x₀ R → ∀ {f f' : E → ℝ≥0∞},
      f =ᵐ[μ.restrict (ball x₀ R)] f' → ⨍⁻ x in A, f x ∂μ = ⨍⁻ x in A, f' x ∂μ :=
    fun hA _ _ hff' => laverage_congr (ae_restrict_of_ae_restrict_of_subset hA hff')
  have hgp : ∀ p : ℝ, (fun x => g x ^ p) =ᵐ[μ.restrict (ball x₀ R)] fun x => hg.mk g x ^ p :=
    fun p => hg.ae_eq_mk.mono fun x hx => by simp only [hx]
  have hhp : ∀ p : ℝ, (fun x => h x ^ p) =ᵐ[μ.restrict (ball x₀ R)] fun x => hh.mk h x ^ p :=
    fun p => hh.ae_eq_mk.mono fun x hx => by simp only [hx]
  have key := hC hR hg.measurable_mk hh.measurable_mk fun y ρ hρ hsub => by
    have hsub' : ball y ρ ⊆ ball x₀ R := (ball_subset_ball (by linarith)).trans hsub
    rw [← hav hsub' (hgp q), ← hav hsub hg.ae_eq_mk, ← hav hsub (hhp q)]
    exact hRH y ρ hρ hsub
  rwa [← hav (ball_subset_ball (by linarith)) (hgp (q + δ)), ← hav subset_rfl (hgp q),
    ← hav subset_rfl (hhp (q + δ))] at key

end Euclidean

end TauCeti
