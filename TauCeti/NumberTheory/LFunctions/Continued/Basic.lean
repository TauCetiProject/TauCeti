/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Meromorphic.Identity
public import TauCeti.NumberTheory.LFunctions.GammaFactor.Order
public import TauCeti.NumberTheory.LFunctions.Data.Comparison
public import Mathlib.NumberTheory.LSeries.Deriv
public import Mathlib.NumberTheory.LSeries.Injectivity

/-!
# Removing the conductor and gamma factors from a completed L-function

`AnalyticLFunctionData.continuedL` removes the conductor power and the gamma factor
from the completed function. A pole of the completion can be cancelled by a zero of the
reciprocal gamma factor. The raw pointwise product has an incorrect value at such a
removable singularity, so we repair its nonnegative-order germs using Mathlib's
`toMeromorphicNFOn`. When the raw product is meromorphic on `ℂ`, genuine poles retain
the original representative; otherwise the construction returns the zero function.

For a record with meromorphic continuation, the repaired function is meromorphic,
is analytic at every point of nonnegative order, and its order is the order of the
completion minus that of the gamma factor. It agrees with the raw product away from
the recorded poles, and recovers the completion as a punctured germ everywhere.
These statements do not require a functional equation or a Dirichlet series.
With meromorphic continuation and Dirichlet agreement, it agrees with the Dirichlet series
throughout `Re s > 1`, including any gamma poles there.

## References

* H. Iwaniec and E. Kowalski, *Analytic Number Theory* (2004), §5.1.
-/

public section

open Complex ComplexConjugate Filter Topology

namespace TauCeti.LFunctions.AnalyticLFunctionData

variable (d : AnalyticLFunctionData)

/-- The raw product obtained by removing the conductor and gamma factors from the completion.
Its pointwise values at removable singularities need not be the analytic extension values. -/
noncomputable def uncompletedProduct (s : ℂ) : ℂ :=
  ((d.conductor : ℕ) : ℂ) ^ (-s / 2) * d.completed s * d.invGammaFactor s

/-- The pointwise formula for the raw uncompleted product. -/
theorem uncompletedProduct_def (s : ℂ) :
    d.uncompletedProduct s =
      ((d.conductor : ℕ) : ℂ) ^ (-s / 2) * d.completed s * d.invGammaFactor s := (rfl)

/-- Taking the dual card reflects the raw uncompleted product across the real axis. -/
@[simp]
theorem uncompletedProduct_dual (s : ℂ) :
    d.dual.uncompletedProduct s = conj (d.uncompletedProduct (conj s)) := by
  simp only [uncompletedProduct_def, dual_conductor, dual_completed_apply,
    invGammaFactor_def, gammaFactor_dual, map_mul, map_inv₀]
  have hN := TauCeti.ofReal_cpow_conj (d.conductor : ℕ).cast_nonneg (-(conj s) / 2)
  simp only [Complex.ofReal_natCast, map_div₀, map_neg, map_ofNat, conj_conj] at hN
  rw [← hN]

/-- Comparing cards preserves the raw uncompleted product. -/
theorem EqOffZero.uncompletedProduct_eq {d e : AnalyticLFunctionData} (h : d.EqOffZero e) :
    d.uncompletedProduct = e.uncompletedProduct := by
  funext s
  simp only [uncompletedProduct_def, invGammaFactor_def, h.conductor_eq, h.completed_eq,
    h.gammaFactor_eq]

/-- The uncompleted function obtained by removing the conductor and gamma factors.
When the raw product is meromorphic on `ℂ` (in particular, under meromorphic continuation),
its nonnegative-order singularities are repaired analytically and the representative at any
remaining pole is unchanged. Otherwise this is the zero function. -/
noncomputable def continuedL : ℂ → ℂ :=
  toMeromorphicNFOn d.uncompletedProduct {s | 0 ≤ meromorphicOrderAt d.uncompletedProduct s}

/-- The removable-extension construction of the continued uncompleted function. -/
theorem continuedL_def :
    d.continuedL = toMeromorphicNFOn d.uncompletedProduct
      {s | 0 ≤ meromorphicOrderAt d.uncompletedProduct s} :=
  (rfl)

/-- Comparing cards preserves the continued uncompleted function. -/
theorem EqOffZero.continuedL_eq {d e : AnalyticLFunctionData} (h : d.EqOffZero e) :
    d.continuedL = e.continuedL := by
  simp only [continuedL_def, h.uncompletedProduct_eq]

/-- Taking the dual card reflects the continued uncompleted function across the real axis. -/
@[simp]
theorem continuedL_dual (s : ℂ) :
    d.dual.continuedL s = conj (d.continuedL (conj s)) := by
  have hr : d.dual.uncompletedProduct = conj ∘ d.uncompletedProduct ∘ conj :=
    funext d.uncompletedProduct_dual
  have ho (z : ℂ) : meromorphicOrderAt d.dual.uncompletedProduct z =
      meromorphicOrderAt d.uncompletedProduct (conj z) := by
    rw [hr, meromorphicOrderAt_conj_conj]
  -- Reflection preserves the repair set and its meromorphy hypothesis.
  have hm : MeromorphicOn d.dual.uncompletedProduct
      {z | 0 ≤ meromorphicOrderAt d.dual.uncompletedProduct z} ↔
      MeromorphicOn d.uncompletedProduct
        {z | 0 ≤ meromorphicOrderAt d.uncompletedProduct z} := by
    constructor <;> intro h z hz
    · have hz' := h (conj z) (by simpa only [Set.mem_ofPred_eq, ho, conj_conj] using hz)
      simpa only [hr, meromorphicAt_conj_conj_iff, conj_conj] using hz'
    · rw [hr, meromorphicAt_conj_conj_iff]
      exact h _ (by simpa only [Set.mem_ofPred_eq, ho] using hz)
  simp only [continuedL_def]
  by_cases hf : MeromorphicOn d.uncompletedProduct
      {z | 0 ≤ meromorphicOrderAt d.uncompletedProduct z}
  · have hf' := hm.mpr hf
    by_cases hs : 0 ≤ meromorphicOrderAt d.dual.uncompletedProduct s
    · -- On the repair set, the analytic representatives agree by their punctured germs.
      have hs' : 0 ≤ meromorphicOrderAt d.uncompletedProduct (conj s) := by rwa [ho] at hs
      have ha := (meromorphicNFOn_toMeromorphicNFOn _ _ hs).meromorphicOrderAt_nonneg_iff_analyticAt
        |>.mp (by rwa [meromorphicOrderAt_toMeromorphicNFOn hf' hs])
      have hb :=
        (meromorphicNFOn_toMeromorphicNFOn _ _ hs').meromorphicOrderAt_nonneg_iff_analyticAt
        |>.mp (by rwa [meromorphicOrderAt_toMeromorphicNFOn hf hs'])
      have hc : Tendsto conj (𝓝[≠] s) (𝓝[≠] (conj s)) :=
        continuous_conj.continuousWithinAt.tendsto_nhdsWithin fun z hz ↦
          (starRingEnd ℂ).injective.ne hz
      apply (ha.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
        (by simpa only [Function.comp_def, conj_conj] using hb.conj_conj.continuousAt)).mp _
        |>.eq_of_nhds
      filter_upwards [hf'.toMeromorphicNFOn_eq_self_on_nhdsNE hs,
        hc.eventually (hf.toMeromorphicNFOn_eq_self_on_nhdsNE hs')] with z hz hz'
      simpa only [Function.comp_apply, hz, hz'] using d.uncompletedProduct_dual z
    · rw [toMeromorphicNFOn_eq_self_on_compl hf' hs,
        toMeromorphicNFOn_eq_self_on_compl hf (by simpa only [Set.mem_compl_iff,
          Set.mem_ofPred_eq, ← ho] using hs), d.uncompletedProduct_dual]
  · simp only [toMeromorphicNFOn_of_not_meromorphicOn hf,
      toMeromorphicNFOn_of_not_meromorphicOn (hm.not.mpr hf), Pi.zero_apply, map_zero]

private theorem analyticAt_conductorPower (s : ℂ) :
    AnalyticAt ℂ (fun z ↦ ((d.conductor : ℕ) : ℂ) ^ (-z / 2)) s :=
  (((differentiable_id.neg.div_const 2).const_cpow
    (Or.inl (Nat.cast_ne_zero.mpr d.conductor.ne_zero))).analyticAt s)

variable {d} (h : d.HasMeromorphicContinuation)

include h

/-- The raw uncompleted product is meromorphic on the whole plane. -/
@[fun_prop]
theorem HasMeromorphicContinuation.meromorphic_uncompletedProduct :
    Meromorphic d.uncompletedProduct := by
  rw [funext d.uncompletedProduct_def]
  exact fun s ↦ ((analyticAt_conductorPower d s).meromorphicAt.mul (h.meromorphic s)).mul
    (d.analyticAt_invGammaFactor s).meromorphicAt

/-- No repair is needed where the raw uncompleted product is analytic. -/
theorem HasMeromorphicContinuation.continuedL_eq_uncompletedProduct_of_analyticAt {s : ℂ}
    (ha : AnalyticAt ℂ d.uncompletedProduct s) :
    d.continuedL s = d.uncompletedProduct s := by
  rw [continuedL_def, toMeromorphicNFOn_eq_toMeromorphicNFAt
    h.meromorphic_uncompletedProduct.meromorphicOn ha.meromorphicOrderAt_nonneg,
    toMeromorphicNFAt_eq_self.mpr ha.meromorphicNFAt]

/-- Repairing nonnegative-order singularities changes no punctured germ of the raw product. -/
theorem HasMeromorphicContinuation.continuedL_eventuallyEq (s : ℂ) :
    d.continuedL =ᶠ[𝓝[≠] s] d.uncompletedProduct := by
  filter_upwards [(h.meromorphic_uncompletedProduct s).eventually_analyticAt] with z hz
  exact h.continuedL_eq_uncompletedProduct_of_analyticAt hz

/-- The uncompleted function is meromorphic on the whole plane. -/
@[fun_prop]
theorem HasMeromorphicContinuation.meromorphic_continuedL : Meromorphic d.continuedL :=
  fun s ↦ (h.meromorphic_uncompletedProduct s).congr (h.continuedL_eventuallyEq s).symm

/-- Dividing out the gamma factor subtracts its meromorphic order, even where its
pole cancels a pole of the completed function. -/
theorem HasMeromorphicContinuation.meromorphicOrderAt_continuedL (s : ℂ) :
    meromorphicOrderAt d.continuedL s =
      meromorphicOrderAt d.completed s - meromorphicOrderAt d.gammaFactor s := by
  rw [meromorphicOrderAt_congr (h.continuedL_eventuallyEq s)]
  rw [funext d.uncompletedProduct_def]
  rw [fun_meromorphicOrderAt_mul
      (f := fun z ↦ ((d.conductor : ℕ) : ℂ) ^ (-z / 2) * d.completed z)
      ((analyticAt_conductorPower d s).meromorphicAt.mul (h.meromorphic s))
      (d.analyticAt_invGammaFactor s).meromorphicAt,
    fun_meromorphicOrderAt_mul (analyticAt_conductorPower d s).meromorphicAt (h.meromorphic s),
    (analyticAt_conductorPower d s).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr
      (d.conductor_cpow_ne_zero _),
    zero_add, d.meromorphicOrderAt_invGammaFactor, sub_eq_add_neg]

/-- The chosen representative is analytic at every point of nonnegative order. -/
theorem HasMeromorphicContinuation.analyticAt_continuedL {s : ℂ}
    (hs : 0 ≤ meromorphicOrderAt d.continuedL s) : AnalyticAt ℂ d.continuedL s := by
  have hr := hs
  rw [meromorphicOrderAt_congr (h.continuedL_eventuallyEq s)] at hr
  have hnf := meromorphicNFOn_toMeromorphicNFOn d.uncompletedProduct
    {z | 0 ≤ meromorphicOrderAt d.uncompletedProduct z} hr
  rw [← continuedL_def] at hnf
  exact hnf.meromorphicOrderAt_nonneg_iff_analyticAt.mp hs

/-- Nonnegative order exactly characterizes analyticity of the repaired representative. -/
theorem HasMeromorphicContinuation.analyticAt_continuedL_iff (s : ℂ) :
    AnalyticAt ℂ d.continuedL s ↔ 0 ≤ meromorphicOrderAt d.continuedL s :=
  ⟨AnalyticAt.meromorphicOrderAt_nonneg, h.analyticAt_continuedL⟩

/-- Away from the recorded poles, `continuedL` equals the raw uncompleted product. -/
theorem HasMeromorphicContinuation.continuedL_eq {s : ℂ} (hs : d.polarOrder s = 0) :
    d.continuedL s = d.uncompletedProduct s := by
  apply h.continuedL_eq_uncompletedProduct_of_analyticAt
  rw [funext d.uncompletedProduct_def]
  exact ((analyticAt_conductorPower d s).mul (h.analyticAt s hs)).mul
    (d.analyticAt_invGammaFactor s)

/-- At a genuine pole of the uncompleted function, the raw representative is retained. -/
theorem
    HasMeromorphicContinuation.continuedL_eq_uncompletedProduct_of_meromorphicOrderAt_neg {s : ℂ}
    (hs : meromorphicOrderAt d.continuedL s < 0) :
    d.continuedL s = d.uncompletedProduct s := by
  rw [meromorphicOrderAt_congr (h.continuedL_eventuallyEq s)] at hs
  exact toMeromorphicNFOn_eq_self_on_compl
    h.meromorphic_uncompletedProduct.meromorphicOn (not_le.mpr hs)

/-- `continuedL` is analytic at every point where the record has no pole. -/
theorem HasMeromorphicContinuation.analyticAt_continuedL_of_polarOrder_eq_zero {s : ℂ}
    (hs : d.polarOrder s = 0) : AnalyticAt ℂ d.continuedL s := by
  apply h.analyticAt_continuedL
  rw [meromorphicOrderAt_congr (h.continuedL_eventuallyEq s)]
  rw [funext d.uncompletedProduct_def]
  exact (((analyticAt_conductorPower d s).mul (h.analyticAt s hs)).mul
    (d.analyticAt_invGammaFactor s)).meromorphicOrderAt_nonneg

/-- Away from gamma poles, no repair of the raw uncompleted product is needed. -/
theorem HasMeromorphicContinuation.continuedL_eq_of_gammaFactor_ne_zero {s : ℂ}
    (hγ : d.gammaFactor s ≠ 0) : d.continuedL s = d.uncompletedProduct s := by
  by_cases hs : d.polarOrder s = 0
  · exact h.continuedL_eq hs
  · apply h.continuedL_eq_uncompletedProduct_of_meromorphicOrderAt_neg
    rw [h.meromorphicOrderAt_continuedL,
      (d.meromorphicOrderAt_gammaFactor_eq_zero_iff s).mpr hγ, sub_zero,
      h.meromorphicOrderAt_eq s hs]
    exact_mod_cast neg_lt_zero.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hs) :
      (0 : ℤ) < d.polarOrder s)

/-- Away from gamma poles, putting back the conductor and gamma factors recovers
the completed function pointwise, including at recorded poles. -/
theorem HasMeromorphicContinuation.completed_eq_mul_continuedL {s : ℂ}
    (hγ : d.gammaFactor s ≠ 0) :
    d.completed s = ((d.conductor : ℕ) : ℂ) ^ (s / 2) * d.gammaFactor s * d.continuedL s := by
  rw [h.continuedL_eq_of_gammaFactor_ne_zero hγ]
  simp only [uncompletedProduct_def, invGammaFactor_def, neg_div, Complex.cpow_neg]
  have hN := d.conductor_cpow_ne_zero (s / 2)
  field_simp

/-- Putting back the conductor and gamma factors recovers the completed function
as a punctured germ at every point, including the poles. -/
theorem HasMeromorphicContinuation.completed_eventuallyEq_mul_continuedL (s : ℂ) :
    d.completed =ᶠ[𝓝[≠] s]
      fun z ↦ ((d.conductor : ℕ) : ℂ) ^ (z / 2) * d.gammaFactor z * d.continuedL z := by
  filter_upwards [d.eventually_gammaFactor_ne_zero s] with z hzγ
  exact h.completed_eq_mul_continuedL hzγ

/-- A continuous function with the same punctured germ has the repaired value. -/
theorem HasMeromorphicContinuation.continuedL_eq_of_eventuallyEq {g : ℂ → ℂ} {s : ℂ}
    (hg : ContinuousAt g s) (heq : d.continuedL =ᶠ[𝓝[≠] s] g) :
    d.continuedL s = g s := by
  have hga := ((h.meromorphic_continuedL s).congr heq).analyticAt hg
  have ha := h.analyticAt_continuedL
    (by rw [meromorphicOrderAt_congr heq]; exact hga.meromorphicOrderAt_nonneg)
  exact ((ha.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hg).mp heq).eq_of_nhds

omit h in
/-- With meromorphic continuation and Dirichlet agreement, removing the conductor and gamma
factors recovers the Dirichlet series, even at a cancelled gamma pole. -/
theorem HasDirichletAgreement.continuedL_eq_LSeries (hD : d.HasDirichletAgreement)
    (hc : d.HasMeromorphicContinuation) {s : ℂ} (hs : 1 < s.re) :
    d.continuedL s = LSeries d.coeff s := by
  have ha : AnalyticAt ℂ (LSeries d.coeff) s := by
    by_cases hσ : LSeries.abscissaOfAbsConv d.coeff < s.re
    · exact LSeries_analyticOnNhd d.coeff s hσ
    by_cases htop : LSeries.abscissaOfAbsConv d.coeff = ⊤
    · rw [LSeries_eq_zero_of_abscissaOfAbsConv_eq_top htop]
      exact analyticAt_const
    -- A finite abscissa above this point would force the completion to vanish on a strip,
    -- hence everywhere as a meromorphic germ, contradicting the first coefficient.
    obtain ⟨t, ht1, hts⟩ := exists_between hs
    have hz : d.completed =ᶠ[𝓝[≠] (t : ℂ)] 0 := by
      filter_upwards [nhdsWithin_le_nhds (continuous_re.continuousAt.preimage_mem_nhds
        (Ioo_mem_nhds ht1 hts))] with z hz
      rw [Pi.zero_apply, hD.completed_eq z hz.1,
        LSeries.eq_zero_of_not_LSeriesSummable d.coeff z (fun hsum ↦
          (not_lt.mp hσ).not_gt (hsum.abscissaOfAbsConv_le.trans_lt
            (by exact_mod_cast hz.2))), mul_zero]
    have hz' (z : ℂ) : d.completed =ᶠ[𝓝[≠] z] 0 :=
      hc.meromorphic.meromorphicOn.eventuallyEq_of_isPreconnected (MeromorphicOn.const 0)
        isPreconnected_univ (Set.mem_univ _) (Set.mem_univ _) hz
    obtain ⟨r, hσr, _⟩ := EReal.exists_between_coe_real (lt_top_iff_ne_top.mpr htop)
    have hzero : (fun x : ℝ ↦ LSeries d.coeff x) =ᶠ[atTop] 0 := by
      filter_upwards [eventually_gt_atTop (max 1 r)] with x hx
      have hx1 : 1 < (x : ℂ).re := lt_of_le_of_lt (le_max_left _ _) hx
      have hσx : LSeries.abscissaOfAbsConv d.coeff < (x : ℂ).re :=
        hσr.trans (by exact_mod_cast (lt_of_le_of_lt (le_max_right _ _) hx))
      have hax := (LSeries_analyticOnNhd d.coeff (x : ℂ) hσx).continuousAt
      apply ((hax.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE continuousAt_const).mp
        ?_).eq_of_nhds
      filter_upwards [hz' x, d.eventually_gammaFactor_ne_zero x,
        nhdsWithin_le_nhds (continuous_re.continuousAt.preimage_mem_nhds
          (Ioi_mem_nhds hx1))] with z hz hzγ hzre
      have hmul := (hD.completed_eq z hzre).symm.trans hz
      exact (mul_eq_zero.mp hmul).resolve_left
        (mul_ne_zero (d.conductor_cpow_ne_zero _) hzγ)
    have hcoeff := tendsto_nhds_unique (LSeries.tendsto_atTop (lt_top_iff_ne_top.mpr htop))
      (tendsto_const_nhds.congr' hzero.symm)
    exact False.elim (one_ne_zero (hD.coeff_one.symm.trans hcoeff))
  apply hc.continuedL_eq_of_eventuallyEq ha.continuousAt
  filter_upwards [hc.completed_eventuallyEq_mul_continuedL s, d.eventually_gammaFactor_ne_zero s,
    nhdsWithin_le_nhds (continuous_re.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hs))]
    with z hz hzγ hzre
  have hN := d.conductor_cpow_ne_zero (z / 2)
  exact mul_left_cancel₀ (mul_ne_zero hN hzγ) (hz.symm.trans (hD.completed_eq z hzre))

end TauCeti.LFunctions.AnalyticLFunctionData
