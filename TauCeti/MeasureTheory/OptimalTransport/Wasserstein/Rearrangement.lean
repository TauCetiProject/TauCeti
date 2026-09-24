/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Infinity.Basic
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Quantile
-- Proof-only: the level-set formula for a positive part, powers as mixtures of hinges, and the
-- `L^∞` seminorm as the limit of the `Lᵖ` seminorms.
import TauCeti.MeasureTheory.Function.Lp.TendstoExponentTop
import TauCeti.MeasureTheory.Integral.LayerCake

/-!
# The monotone rearrangement is optimal for every Wasserstein exponent

For two probability laws `μ` and `ν` on `ℝ` and every exponent `1 ≤ p ≤ ∞`,

`W_p (μ, ν) = ‖μ.quantile - ν.quantile‖_{Lᵖ (0, 1)}`,

and the monotone coupling `MeasureTheory.Measure.quantileCoupling` attains it. For `p < ∞` the
right-hand side is `(∫₀¹ |μ.quantile t - ν.quantile t| ^ p dt) ^ (1 / p)`, and at `p = ∞` it is
the essential supremum of `|μ.quantile - ν.quantile|` on `(0, 1)`, by the `eLpNorm` convention. All
of these are identities in `[0, ∞]` and need no moment hypothesis.

The upper bound is `TauCeti.wassersteinEDist_le_eLpNorm_quantile_sub`; the content here is the
lower bound, a rearrangement inequality for the costs `|x - y| ^ p`. It rests on two facts.

* **The Fréchet–Hoeffding bound.** Every plan of `μ` and `ν` puts mass at least
  `cdf μ a - cdf ν b` on the quadrant `Iic a ×ˢ Ioi b`, and the monotone coupling puts exactly the
  positive part of that gap there. By the level-set formula for a positive part, the monotone
  coupling therefore has the least expected *hinge cost* `(y - x - r)⁺` for every threshold `r`,
  and symmetrically for `(x - y - r)⁺`.
* **Powers are mixtures of hinges.** For `1 < p`, `|x - y| ^ p` is the integral over `r > 0` of
  `p (p - 1) r ^ (p - 2) ((y - x - r)⁺ + (x - y - r)⁺)`, and for `p = 1` it is the sum of the two
  hinges at `r = 0` (`TauCeti.edist_rpow_eq_lintegral` and
  `TauCeti.ofReal_sub_sub_add_ofReal_sub_sub`). Integrating the hinge inequalities against this
  nonnegative weight gives the inequality for the power cost.

The exponent `∞` then follows from the finite exponents: both sides are limits of their
finite-exponent values, by `TauCeti.tendsto_wassersteinEDist_atTop` and
`TauCeti.tendsto_eLpNorm_atTop`.

## Main statements

* `TauCeti.ofReal_cdf_sub_le_measure` — the Fréchet–Hoeffding bound on quadrants, attained by
  the monotone coupling (`MeasureTheory.Measure.quantileCoupling_Iic_prod_Ioi`);
* `TauCeti.lintegral_ofReal_sub_sub_quantileCoupling_le` — the monotone coupling minimizes every
  hinge cost;
* `TauCeti.lintegral_edist_rpow_quantileCoupling_le` and
  `MeasureTheory.Measure.isOptimalCoupling_quantileCoupling` — the monotone coupling is an optimal
  plan for the cost `|x - y| ^ p` whenever `1 ≤ p`;
* `TauCeti.wassersteinEDist_eq_eLpNorm_quantile_sub` — the quantile formula for `W_p`, for every
  `1 ≤ p ≤ ∞`, unfolded at the two kinds of exponent as
  `TauCeti.wassersteinEDist_eq_lintegral_rpow_enorm_quantile_sub` (the integral and root, for
  `p < ∞`) and `TauCeti.wassersteinEDist_top_eq_essSup_enorm_quantile_sub` (the essential
  supremum, for `p = ∞`).

## References

* C. Villani, *Topics in Optimal Transportation*, GSM 58, AMS 2003, §2.2, where the monotone
  rearrangement is shown optimal for the costs `h (x - y)` with `h` convex.
* F. Santambrogio, *Optimal Transport for Applied Mathematicians*, Birkhäuser 2015, §2.2.
* S. Cambanis, G. Simons and W. Stout, *Inequalities for `E k(X, Y)` when the marginals are fixed*,
  Z. Wahrscheinlichkeitstheorie verw. Gebiete 36 (1976), 285–294.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace TauCeti

section Quadrant

variable {μ ν : Measure ℝ} [IsProbabilityMeasure μ] {π : Measure (ℝ × ℝ)}

/-- **The Fréchet–Hoeffding bound on a quadrant.** Every transport plan of two real laws gives the
quadrant `Iic a ×ˢ Ioi b` mass at least `cdf μ a - cdf ν b`: the pairs with first coordinate at most
`a` carry mass `cdf μ a`, and at most `cdf ν b` of it has second coordinate at most `b`. -/
theorem ofReal_cdf_sub_le_measure (hπ : IsCoupling π μ ν) (a b : ℝ) :
    ENNReal.ofReal (cdf μ a - cdf ν b) ≤ π (Iic a ×ˢ Ioi b) := by
  have : IsProbabilityMeasure ν := hπ.isProbabilityMeasure_right
  rw [ENNReal.ofReal_sub _ (cdf_nonneg ν b), ofReal_cdf, ofReal_cdf,
    ← hπ.measure_prod_univ measurableSet_Iic, ← hπ.measure_univ_prod measurableSet_Iic,
    tsub_le_iff_right]
  refine (measure_mono fun z hz ↦ ?_).trans (measure_union_le _ _)
  simp only [mem_prod, mem_Iic, mem_univ, and_true, true_and, mem_union, mem_Ioi] at hz ⊢
  exact (le_or_gt z.2 b).symm.imp (⟨hz, ·⟩) id

/-- The expected hinge cost `(y - x - r)⁺` of a plan is the integral, over the levels `a`, of the
mass the plan gives to the quadrant `Iic a ×ˢ Ioi (a + r)`. -/
private theorem lintegral_ofReal_sub_sub_eq (m : Measure (ℝ × ℝ)) [SFinite m] (r : ℝ) :
    ∫⁻ z, ENNReal.ofReal (z.2 - z.1 - r) ∂m = ∫⁻ a, m (Iic a ×ˢ Ioi (a + r)) := by
  simp_rw [sub_right_comm _ _ r]
  rw [lintegral_ofReal_sub_eq_lintegral_measure m measurable_fst.aemeasurable
      (measurable_snd.sub_const r).aemeasurable]
  refine lintegral_congr fun a ↦ congrArg m ?_
  ext z
  simp [lt_sub_iff_add_lt]

/-- **The monotone coupling minimizes every hinge cost.** For every threshold `r`, no transport plan
of two real laws has smaller expected hinge cost `(y - x - r)⁺` than the monotone coupling. -/
theorem lintegral_ofReal_sub_sub_quantileCoupling_le (hπ : IsCoupling π μ ν) (r : ℝ) :
    ∫⁻ z, ENNReal.ofReal (z.2 - z.1 - r) ∂μ.quantileCoupling ν
      ≤ ∫⁻ z, ENNReal.ofReal (z.2 - z.1 - r) ∂π := by
  have : IsProbabilityMeasure π := hπ.isProbabilityMeasure
  rw [lintegral_ofReal_sub_sub_eq, lintegral_ofReal_sub_sub_eq]
  exact lintegral_mono fun a ↦ (Measure.quantileCoupling_Iic_prod_Ioi μ ν a (a + r)).trans_le
    (ofReal_cdf_sub_le_measure hπ a (a + r))

/-- The sum of the two hinge costs of a plan with threshold `r` is minimized by the monotone
coupling: the hinge `(x - y - r)⁺` is the hinge `(y - x - r)⁺` of the swapped plan. -/
private theorem lintegral_hinge_add_hinge_quantileCoupling_le (hπ : IsCoupling π μ ν) (r : ℝ) :
    ∫⁻ z, ENNReal.ofReal (z.2 - z.1 - r) ∂μ.quantileCoupling ν
        + ∫⁻ z, ENNReal.ofReal (z.1 - z.2 - r) ∂μ.quantileCoupling ν
      ≤ ∫⁻ z, ENNReal.ofReal (z.2 - z.1 - r) ∂π + ∫⁻ z, ENNReal.ofReal (z.1 - z.2 - r) ∂π := by
  have : IsProbabilityMeasure ν := hπ.isProbabilityMeasure_right
  have hswap := lintegral_ofReal_sub_sub_quantileCoupling_le hπ.swap r
  have hf : Measurable fun z : ℝ × ℝ ↦ ENNReal.ofReal (z.2 - z.1 - r) := by fun_prop
  rw [← Measure.map_swap_quantileCoupling, lintegral_map hf measurable_swap,
    lintegral_map hf measurable_swap] at hswap
  simp only [Prod.fst_swap, Prod.snd_swap] at hswap
  exact add_le_add (lintegral_ofReal_sub_sub_quantileCoupling_le hπ r) hswap

end Quadrant

section Power

/-- The transport objective of the cost `|x - y| ^ p`, for `1 < p`, as the corresponding mixture
of the two hinge objectives. -/
private theorem lintegral_edist_rpow_eq {p : ℝ} (hp : 1 < p) (m : Measure (ℝ × ℝ)) [SFinite m] :
    ∫⁻ z, edist z.1 z.2 ^ p ∂m = ∫⁻ r in Ioi 0, ENNReal.ofReal (p * (p - 1) * r ^ (p - 2))
      * (∫⁻ z, ENNReal.ofReal (z.2 - z.1 - r) ∂m + ∫⁻ z, ENNReal.ofReal (z.1 - z.2 - r) ∂m) := by
  simp_rw [edist_rpow_eq_lintegral hp]
  rw [lintegral_lintegral_swap (by fun_prop)]
  refine lintegral_congr fun r ↦ ?_
  rw [lintegral_const_mul _ (by fun_prop), lintegral_add_left (by fun_prop)]

variable {μ ν : Measure ℝ} [IsProbabilityMeasure μ] {π : Measure (ℝ × ℝ)}

/-- **The rearrangement inequality for powers of the distance.** For every exponent `1 ≤ p`, no
transport plan of two real laws has a smaller expected cost `|x - y| ^ p` than the monotone
coupling. -/
theorem lintegral_edist_rpow_quantileCoupling_le (hπ : IsCoupling π μ ν) {p : ℝ} (hp : 1 ≤ p) :
    ∫⁻ z, edist z.1 z.2 ^ p ∂μ.quantileCoupling ν ≤ ∫⁻ z, edist z.1 z.2 ^ p ∂π := by
  have : IsProbabilityMeasure π := hπ.isProbabilityMeasure
  rcases hp.eq_or_lt with rfl | hp
  · -- At `p = 1` the distance is the sum of the two hinge costs with threshold `0`.
    have hsplit : ∀ (m : Measure (ℝ × ℝ)), ∫⁻ z, edist z.1 z.2 ^ (1 : ℝ) ∂m
        = ∫⁻ z, ENNReal.ofReal (z.2 - z.1 - 0) ∂m + ∫⁻ z, ENNReal.ofReal (z.1 - z.2 - 0) ∂m :=
      fun m ↦ by
        rw [← lintegral_add_left (by fun_prop)]
        refine lintegral_congr fun z ↦ ?_
        rw [ENNReal.rpow_one, ofReal_sub_sub_add_ofReal_sub_sub le_rfl, sub_zero, edist_dist,
          Real.dist_eq]
    rw [hsplit, hsplit]
    exact lintegral_hinge_add_hinge_quantileCoupling_le hπ 0
  · rw [lintegral_edist_rpow_eq hp, lintegral_edist_rpow_eq hp]
    exact lintegral_mono fun r ↦
      mul_le_mul_right (lintegral_hinge_add_hinge_quantileCoupling_le hπ r) _

end Power

section Wasserstein

/-- **The one-dimensional quantile formula.** For every exponent `1 ≤ p ≤ ∞`, the `p`-Wasserstein
distance of two probability laws on `ℝ` is the `Lᵖ (0, 1)` distance of their quantile functions.
The identity holds in `[0, ∞]`, without moment hypotheses. -/
theorem wassersteinEDist_eq_eLpNorm_quantile_sub {p : ℝ≥0∞} (hp : 1 ≤ p) (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    wassersteinEDist p μ ν
      = eLpNorm (fun t ↦ μ.quantile t - ν.quantile t) p (volume.restrict (Ioo (0 : ℝ) 1)) := by
  -- The finite exponents: every plan costs at least as much as the monotone coupling.
  have hfin : ∀ q : ℝ≥0∞, 1 ≤ q → q ≠ ∞ → wassersteinEDist q μ ν
      = eLpNorm (fun t ↦ μ.quantile t - ν.quantile t) q (volume.restrict (Ioo (0 : ℝ) 1)) := by
    intro q hq hq_top
    have hq0 : q ≠ 0 := (zero_lt_one.trans_le hq).ne'
    refine le_antisymm (wassersteinEDist_le_eLpNorm_quantile_sub q μ ν)
      (le_wassersteinEDist fun π hπ ↦ ?_)
    rw [← eLpNorm_edist_quantileCoupling, eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hq_top,
      eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hq_top]
    simp only [enorm_eq_self]
    exact ENNReal.rpow_le_rpow (lintegral_edist_rpow_quantileCoupling_le hπ
      (by simpa using ENNReal.toReal_mono hq_top hq)) (by positivity)
  rcases eq_or_ne p ∞ with rfl | hp_top
  · -- The exponent `∞`: both sides are the limits of their finite-exponent values.
    refine tendsto_nhds_unique ((tendsto_wassersteinEDist_atTop μ ν).congr' ?_)
      (tendsto_eLpNorm_atTop ((Measure.measurable_quantile μ).sub
        (Measure.measurable_quantile ν)).aestronglyMeasurable)
    filter_upwards [eventually_ge_atTop 1] with q hq
    exact hfin q (by exact_mod_cast hq) ENNReal.coe_ne_top
  · exact hfin p hp hp_top

/-- **The quantile formula at a finite exponent.** For `1 ≤ p < ∞`, the `p`-Wasserstein distance of
two probability laws on `ℝ` is `(∫₀¹ |μ.quantile t - ν.quantile t| ^ p dt) ^ (1 / p)`. -/
theorem wassersteinEDist_eq_lintegral_rpow_enorm_quantile_sub {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hp_top : p ≠ ∞) (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    wassersteinEDist p μ ν
      = (∫⁻ t in Ioo (0 : ℝ) 1, ‖μ.quantile t - ν.quantile t‖ₑ ^ p.toReal) ^ (1 / p.toReal) := by
  rw [wassersteinEDist_eq_eLpNorm_quantile_sub hp,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (zero_lt_one.trans_le hp).ne' hp_top]

/-- **The quantile formula at the exponent `∞`.** The `∞`-Wasserstein distance of two probability
laws on `ℝ` is the essential supremum of `|μ.quantile - ν.quantile|` on `(0, 1)`. -/
theorem wassersteinEDist_top_eq_essSup_enorm_quantile_sub (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    wassersteinEDist ∞ μ ν
      = essSup (fun t ↦ ‖μ.quantile t - ν.quantile t‖ₑ) (volume.restrict (Ioo (0 : ℝ) 1)) := by
  rw [wassersteinEDist_eq_eLpNorm_quantile_sub le_top, eLpNorm_exponent_top, eLpNormEssSup]

end Wasserstein

end TauCeti

namespace MeasureTheory.Measure

/-- **The monotone rearrangement is optimal.** For every exponent `1 ≤ p`, the monotone coupling of
two real laws is an optimal transport plan for the cost `|x - y| ^ p`. -/
theorem isOptimalCoupling_quantileCoupling (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {p : ℝ} (hp : 1 ≤ p) :
    TauCeti.IsOptimalCoupling (fun z : ℝ × ℝ ↦ edist z.1 z.2 ^ p) (μ.quantileCoupling ν) μ ν where
  toIsCoupling := μ.isCoupling_quantileCoupling ν
  lintegral_eq := le_antisymm
    (TauCeti.le_transportCost fun _ hπ ↦ TauCeti.lintegral_edist_rpow_quantileCoupling_le hπ hp)
    (TauCeti.transportCost_le_lintegral (μ.isCoupling_quantileCoupling ν) _)

end MeasureTheory.Measure
