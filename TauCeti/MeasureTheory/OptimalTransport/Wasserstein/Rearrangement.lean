/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Infinity.Basic
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Quantile
-- Proof-only: the level-set formula for a positive part, the layer-cake formula, the power
-- integral, and the `L^∞` seminorm as the limit of the `Lᵖ` seminorms.
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Layercake
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
  hinges at `r = 0`. Integrating the hinge inequalities against this nonnegative weight gives the
  inequality for the power cost.

The exponent `∞` then follows from the finite exponents: both sides are limits of their
finite-exponent values, by `TauCeti.tendsto_wassersteinEDist_atTop` and
`TauCeti.tendsto_eLpNorm_atTop`.

## Main statements

* `MeasureTheory.Measure.quantileCoupling_Iic_prod_Ioi` and `TauCeti.ofReal_cdf_sub_le_measure` —
  the Fréchet–Hoeffding bound on quadrants, attained by the monotone coupling;
* `TauCeti.lintegral_ofReal_sub_sub_quantileCoupling_le` — the monotone coupling minimizes every
  hinge cost;
* `TauCeti.lintegral_edist_rpow_quantileCoupling_le` and
  `MeasureTheory.Measure.isOptimalCoupling_quantileCoupling` — the monotone coupling is an optimal
  plan for the cost `|x - y| ^ p` whenever `1 ≤ p`;
* `TauCeti.wassersteinEDist_eq_eLpNorm_quantile_sub` — the quantile formula for `W_p`, for every
  `1 ≤ p ≤ ∞`.

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

namespace MeasureTheory.Measure

/-- Exchanging the coordinates of the monotone coupling of `μ` and `ν` gives the monotone coupling
of `ν` and `μ`. -/
@[simp]
theorem map_swap_quantileCoupling (μ ν : Measure ℝ) :
    (μ.quantileCoupling ν).map Prod.swap = ν.quantileCoupling μ := by
  rw [quantileCoupling_def, quantileCoupling_def, map_map measurable_swap (by fun_prop)]
  simp only [Function.comp_def, Prod.swap_prod_mk]

/-- **The monotone coupling on a quadrant.** The monotone coupling of two real laws gives the
quadrant `Iic a ×ˢ Ioi b` the positive part of the gap `cdf μ a - cdf ν b`: the uniform levels `t`
with `μ.quantile t ≤ a < b < ν.quantile t` are those with `cdf ν b < t ≤ cdf μ a`. -/
theorem quantileCoupling_Iic_prod_Ioi (μ ν : Measure ℝ) (a b : ℝ) :
    μ.quantileCoupling ν (Iic a ×ˢ Ioi b) = ENNReal.ofReal (cdf μ a - cdf ν b) := by
  have hmeas : MeasurableSet (Iic a ×ˢ Ioi b) := measurableSet_Iic.prod measurableSet_Ioi
  rw [quantileCoupling_def, map_apply (by fun_prop) hmeas,
    restrict_apply (hmeas.preimage (by fun_prop))]
  have hset : (fun t ↦ (μ.quantile t, ν.quantile t)) ⁻¹' (Iic a ×ˢ Ioi b) ∩ Ioo 0 1
      = Ioc (cdf ν b) (cdf μ a) ∩ Ioo 0 1 := by
    ext t
    simp only [mem_inter_iff, mem_preimage, mem_prod, mem_Iic, mem_Ioi, mem_Ioc, mem_Ioo,
      and_congr_left_iff]
    rintro ⟨ht0, ht1⟩
    rw [quantile_le_iff μ ht0 ht1, lt_quantile_iff ν ht0 ht1, and_comm]
  rw [hset]
  refine le_antisymm ((measure_mono inter_subset_left).trans_eq Real.volume_Ioc) ?_
  rw [← Real.volume_Ioo]
  exact measure_mono fun t ht ↦ ⟨Ioo_subset_Ioc_self ht, (cdf_nonneg ν b).trans_lt ht.1,
    ht.2.trans_le (cdf_le_one μ a)⟩

end MeasureTheory.Measure

namespace TauCeti

section Quadrant

variable {μ ν : Measure ℝ} [IsProbabilityMeasure μ] {π : Measure (ℝ × ℝ)}

/-- **The Fréchet–Hoeffding bound on a quadrant.** Every transport plan of two real laws gives the
quadrant `Iic a ×ˢ Ioi b` mass at least `cdf μ a - cdf ν b`: the pairs with first coordinate at most
`a` carry mass `cdf μ a`, and at most `cdf ν b` of it has second coordinate at most `b`. -/
theorem ofReal_cdf_sub_le_measure (hπ : IsCoupling π μ ν) (a b : ℝ) :
    ENNReal.ofReal (cdf μ a - cdf ν b) ≤ π (Iic a ×ˢ Ioi b) := by
  have : IsProbabilityMeasure ν := ⟨by rw [← hπ.measure_univ_eq, measure_univ]⟩
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
  rw [lintegral_congr fun z ↦ by rw [sub_right_comm],
    lintegral_ofReal_sub_eq_lintegral_measure m measurable_fst.aemeasurable
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
  have : IsProbabilityMeasure ν := ⟨by rw [← hπ.measure_univ_eq, measure_univ]⟩
  have hswap := lintegral_ofReal_sub_sub_quantileCoupling_le hπ.swap r
  have hf : Measurable fun z : ℝ × ℝ ↦ ENNReal.ofReal (z.2 - z.1 - r) := by fun_prop
  rw [← Measure.map_swap_quantileCoupling, lintegral_map hf measurable_swap,
    lintegral_map hf measurable_swap] at hswap
  exact add_le_add (lintegral_ofReal_sub_sub_quantileCoupling_le hπ r) hswap

end Quadrant

section Power

/-- For a nonnegative threshold `r`, the two hinges of a pair of reals add up to the single hinge
`(|x - y| - r)⁺` of their distance, since at most one of `y - x - r` and `x - y - r` is positive. -/
private theorem ofReal_sub_sub_add_ofReal_sub_sub {r : ℝ} (hr : 0 ≤ r) (x y : ℝ) :
    ENNReal.ofReal (y - x - r) + ENNReal.ofReal (x - y - r) = ENNReal.ofReal (|x - y| - r) := by
  rcases le_total x y with h | h
  · rw [ENNReal.ofReal_of_nonpos (by linarith : x - y - r ≤ 0), add_zero, abs_sub_comm,
      abs_of_nonneg (sub_nonneg.2 h)]
  · rw [ENNReal.ofReal_of_nonpos (by linarith : y - x - r ≤ 0), zero_add,
      abs_of_nonneg (sub_nonneg.2 h)]

/-- The power integral `∫₀ˢ q t ^ (q - 1) dt = s ^ q`, for a positive exponent `q`. -/
private theorem integral_mul_rpow_sub_one {q : ℝ} (hq : 0 < q) (s : ℝ) :
    ∫ t in 0..s, q * t ^ (q - 1) = s ^ q := by
  rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith)), sub_add_cancel,
    Real.zero_rpow hq.ne', sub_zero]
  field_simp

/-- **Powers are mixtures of hinges.** For `1 < p` and `d ≥ 0`,
`d ^ p = ∫_{r > 0} p (p - 1) r ^ (p - 2) (d - r)⁺ dr`: two layer-cake formulas, one against
Lebesgue measure on `(0, d)` and one against the Dirac mass at `d`. -/
private theorem lintegral_mul_ofReal_sub_eq {p d : ℝ} (hp : 1 < p) (hd : 0 ≤ d) :
    ∫⁻ r in Ioi 0, ENNReal.ofReal (p * (p - 1) * r ^ (p - 2)) * ENNReal.ofReal (d - r)
      = ENNReal.ofReal (d ^ p) := by
  have hint : ∀ s, ∫ t in 0..s, p * (p - 1) * t ^ (p - 2) = p * s ^ (p - 1) := fun s ↦ by
    simp_rw [mul_assoc, show p - 2 = p - 1 - 1 by ring]
    rw [intervalIntegral.integral_const_mul, integral_mul_rpow_sub_one (by linarith)]
  -- Against Lebesgue measure on `(0, d)`, the mass above a level `r > 0` is `d - r`.
  have hlayer := lintegral_comp_eq_lintegral_meas_lt_mul (volume.restrict (Ioo 0 d)) (f := id)
    (g := fun t ↦ p * (p - 1) * t ^ (p - 2))
    (ae_restrict_of_forall_mem measurableSet_Ioo fun s hs ↦ hs.1.le) aemeasurable_id
    (fun _ _ ↦ (intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul _)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht ↦
      mul_nonneg (by nlinarith) (Real.rpow_nonneg (le_of_lt ht) _))
  -- Against the Dirac mass at `d`, a level `t > 0` is exceeded exactly when `t < d`.
  have hdirac := lintegral_comp_eq_lintegral_meas_lt_mul (Measure.dirac d) (f := id)
    (g := fun t ↦ p * t ^ (p - 1))
    ((ae_dirac_iff (measurableSet_le measurable_const measurable_id)).2 hd) aemeasurable_id
    (fun _ _ ↦ (intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul _)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht ↦
      mul_nonneg (by linarith) (Real.rpow_nonneg (le_of_lt ht) _))
  simp only [id_eq, hint, integral_mul_rpow_sub_one (by linarith : 0 < p), lintegral_dirac]
    at hlayer hdirac
  calc ∫⁻ r in Ioi 0, ENNReal.ofReal (p * (p - 1) * r ^ (p - 2)) * ENNReal.ofReal (d - r)
      = ∫⁻ r in Ioi 0, volume.restrict (Ioo 0 d) {s | r < s}
          * ENNReal.ofReal (p * (p - 1) * r ^ (p - 2)) := by
        refine setLIntegral_congr_fun measurableSet_Ioi fun r (hr : 0 < r) ↦ ?_
        rw [mul_comm, Measure.restrict_apply' measurableSet_Ioo, ← Real.volume_Ioo]
        congr 2
        ext s
        simp only [mem_inter_iff, mem_ofPred_eq, mem_Ioo]
        exact ⟨fun h ↦ ⟨h.1, hr.trans h.1, h.2⟩, fun h ↦ ⟨h.1, h.2.2⟩⟩
    _ = ∫⁻ s in Ioo 0 d, ENNReal.ofReal (p * s ^ (p - 1)) := hlayer.symm
    _ = ∫⁻ t in Ioi 0, (Iio d).indicator (fun t ↦ ENNReal.ofReal (p * t ^ (p - 1))) t := by
        rw [lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
          Iio_inter_Ioi]
    _ = ∫⁻ t in Ioi 0, Measure.dirac d {s | t < s} * ENNReal.ofReal (p * t ^ (p - 1)) := by
        refine lintegral_congr fun t ↦ ?_
        rw [Measure.dirac_apply]
        by_cases h : t < d <;> simp [h]
    _ = ENNReal.ofReal (d ^ p) := hdirac.symm

/-- **The power cost as a mixture of hinge costs.** For `1 < p`, the cost `|x - y| ^ p` is the
integral, over the thresholds `r > 0` with weight `p (p - 1) r ^ (p - 2)`, of the two hinge costs
`(y - x - r)⁺ + (x - y - r)⁺`. -/
private theorem edist_rpow_eq_lintegral {p : ℝ} (hp : 1 < p) (x y : ℝ) :
    edist x y ^ p = ∫⁻ r in Ioi 0, ENNReal.ofReal (p * (p - 1) * r ^ (p - 2))
      * (ENNReal.ofReal (y - x - r) + ENNReal.ofReal (x - y - r)) := by
  rw [edist_dist, Real.dist_eq, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by linarith),
    ← lintegral_mul_ofReal_sub_eq hp (abs_nonneg _)]
  exact setLIntegral_congr_fun measurableSet_Ioi fun r (hr : 0 < r) ↦ by
    rw [ofReal_sub_sub_add_ofReal_sub_sub hr.le]

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
