/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Finance.BlackScholes.Hedge
public import TauCeti.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Polynomial-growth delta hedges on the full time horizon

For a classical price `C(s,t)`, a uniform bound on `|C| + |s C_s|` by `A (1 + s^p)`
controls both the price and the stock exposure along a positive continuous path up to
maturity. Both belong to every time `Lᵖ`, including `L∞`, before maturity, even if
`C_s` has no limit at maturity. The growth exponent may be any real number: positivity
on the closed horizon also bounds negative powers of the stock.

Consequently the delta hedge has absolutely integrable stock drift and bond gains,
and square-integrable stock diffusion, as soon as the stock coefficients have the
corresponding time integrability. The bond price cancels from its gains coefficient,
so it need only be nonzero, not continuous or bounded away from zero.

These are pathwise integrability inputs to a verification theorem. They do not assert
predictability, stochastic integration, self-financing, or a true-martingale property.
In particular, no moment assumption or probability measure is needed here. Apply the
results separately on each positive continuous sample path. The endpoint at maturity
is omitted, and no derivative or price value at that endpoint is used.

## References

* S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*, Springer,
  2004, §4.5 and §6.4.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti.Finance

variable {C : ℝ → ℝ → ℝ} {S β μ σ r : ℝ → ℝ} {a T A p : ℝ}

/-- A uniform polynomial-growth bound on the price and its delta exposure gives every
finite-horizon time `Lᵖ` bound along a positive continuous stock path. Continuity of the
price and its spot derivative is required only strictly before maturity. -/
theorem memLp_price_path_and_delta_exposure_of_growth
    (hC : ContinuousOn (Function.uncurry C) (Ioi 0 ×ˢ Ico a T))
    (hCs : ContinuousOn (fun q : ℝ × ℝ ↦ deriv (fun s ↦ C s q.2) q.1)
      (Ioi 0 ×ˢ Ico a T))
    (hgrowth : ∀ s > 0, ∀ t ∈ Ico a T,
      |C s t| + |s * deriv (fun x ↦ C x t) s| ≤ A * (1 + s ^ p))
    (hS : ContinuousOn S (Icc a T)) (hpos : ∀ t ∈ Icc a T, 0 < S t) (q : ℝ≥0∞) :
    MemLp (fun t ↦ C (S t) t) q (volume.restrict (Ico a T)) ∧
      MemLp (fun t ↦ S t * deriv (fun s ↦ C s t) (S t)) q
        (volume.restrict (Ico a T)) := by
  have hpath : ContinuousOn (fun t ↦ (S t, t)) (Ico a T) :=
    (hS.mono Ico_subset_Icc_self).prodMk continuousOn_id
  have hmem : MapsTo (fun t ↦ (S t, t)) (Ico a T) (Ioi 0 ×ˢ Ico a T) :=
    fun t ht ↦ ⟨hpos t (Ico_subset_Icc_self ht), ht⟩
  have hprice := (hC.comp hpath hmem).aestronglyMeasurable (μ := volume) measurableSet_Ico
  have hexposure := ((hS.mono Ico_subset_Icc_self).mul
    (hCs.comp hpath hmem)).aestronglyMeasurable (μ := volume) measurableSet_Ico
  have hmajorant : ContinuousOn (fun t ↦ A * (1 + S t ^ p)) (Icc a T) :=
    continuousOn_const.mul (continuousOn_const.add
      (hS.rpow_const fun t ht ↦ Or.inl (ne_of_gt (hpos t ht))))
  have hLp := hmajorant.memLp_restrict_of_subset_isCompact (μ := volume) isCompact_Icc
    measurableSet_Ico Ico_subset_Icc_self q
  constructor
  · refine hLp.mono' hprice ?_
    filter_upwards [ae_restrict_mem measurableSet_Ico] with t ht
    simpa only [Real.norm_eq_abs] using
      (le_add_of_nonneg_right (abs_nonneg _)).trans
        (hgrowth (S t) (hpos t (Ico_subset_Icc_self ht)) t ht)
  · refine hLp.mono' hexposure ?_
    filter_upwards [ae_restrict_mem measurableSet_Ico] with t ht
    simpa only [Real.norm_eq_abs] using
      (le_add_of_nonneg_left (abs_nonneg _)).trans
        (hgrowth (S t) (hpos t (Ico_subset_Icc_self ht)) t ht)

/-- The polynomial-growth delta hedge has integrable stock drift and bond gains and
square-integrable stock diffusion on the full horizon before maturity. Only the actual
coefficient integrability is assumed: the drift and rate may be merely time `L¹`, and
the volatility merely time `L²`. The nonvanishing bond need not be measurable, since
its value cancels from the bond gains. -/
theorem integrable_delta_hedge_gains_of_growth
    (hC : ContinuousOn (Function.uncurry C) (Ioi 0 ×ˢ Ico a T))
    (hCs : ContinuousOn (fun q : ℝ × ℝ ↦ deriv (fun s ↦ C s q.2) q.1)
      (Ioi 0 ×ˢ Ico a T))
    (hgrowth : ∀ s > 0, ∀ t ∈ Ico a T,
      |C s t| + |s * deriv (fun x ↦ C x t) s| ≤ A * (1 + s ^ p))
    (hS : ContinuousOn S (Icc a T)) (hpos : ∀ t ∈ Icc a T, 0 < S t)
    (hμ : IntegrableOn μ (Ico a T)) (hσ : MemLp σ 2 (volume.restrict (Ico a T)))
    (hr : IntegrableOn r (Ico a T))
    (hβ : ∀ᵐ t ∂volume.restrict (Ico a T), β t ≠ 0) :
    IntegrableOn (fun t ↦ μ t * S t * deriv (fun s ↦ C s t) (S t)) (Ico a T) ∧
      MemLp (fun t ↦ σ t * S t * deriv (fun s ↦ C s t) (S t)) 2
        (volume.restrict (Ico a T)) ∧
      IntegrableOn (fun t ↦ r t * β t *
        BlackScholes.hedgeBondHolding (fun s ↦ C s t) (S t) (β t)) (Ico a T) := by
  obtain ⟨hprice, hexposure⟩ :=
    memLp_price_path_and_delta_exposure_of_growth hC hCs hgrowth hS hpos ∞
  refine ⟨?_, ?_, ?_⟩
  · simpa only [IntegrableOn, Pi.mul_def, mul_assoc] using hμ.mul_of_top_left hexposure
  · simpa only [Pi.mul_def, mul_assoc] using hσ.mul hexposure
  · refine (hr.mul_of_top_left (hprice.sub hexposure)).congr ?_
    filter_upwards [hβ] with t hβt
    simp only [BlackScholes.hedgeBondHolding_def, Pi.mul_apply, Pi.sub_apply]
    field_simp [hβt]

end TauCeti.Finance
