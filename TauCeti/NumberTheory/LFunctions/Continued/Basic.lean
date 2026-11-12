/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Meromorphic.NormalForm
public import TauCeti.NumberTheory.LFunctions.GammaFactor.Order
public import TauCeti.NumberTheory.LFunctions.Data.Growth
public import Mathlib.NumberTheory.LSeries.Deriv

/-!
# Removing the archimedean factors from a completed L-function

`AnalyticLFunctionData.continuedL` removes the conductor power and the gamma factor
from the completed function. A pole of the completion can be cancelled by a zero of the
reciprocal gamma factor. The raw pointwise product has an incorrect value at such a
removable singularity, so we repair its nonnegative-order germs using Mathlib's
`toMeromorphicNFOn`. At genuine poles we retain the original representative.

For a record with meromorphic continuation, the repaired function is meromorphic,
is analytic at every point of nonnegative order, and its order is the order of the
completion minus that of the gamma factor. It agrees with the raw product away from
the recorded poles, and recovers the completion as a punctured germ everywhere.
These statements do not require a functional equation or a Dirichlet series.
With Dirichlet agreement and average absolute coefficient growth, it agrees with
the Dirichlet series throughout `Re s > 1`, including any gamma poles there.

## References

* H. Iwaniec and E. Kowalski, *Analytic Number Theory* (2004), §5.1.
-/

public section

open Complex Filter Topology

namespace TauCeti.LFunctions.AnalyticLFunctionData

variable (d : AnalyticLFunctionData)

/-- The raw product obtained by removing the conductor and gamma factors from the completion.
Its pointwise values at removable singularities need not be the analytic extension values. -/
noncomputable def uncompletedProduct (s : ℂ) : ℂ :=
  ((d.conductor : ℕ) : ℂ) ^ (-s / 2) * d.completed s * d.invGammaFactor s

/-- The pointwise formula for the raw uncompleted product. -/
theorem uncompletedProduct_def :
    d.uncompletedProduct =
      fun s ↦ ((d.conductor : ℕ) : ℂ) ^ (-s / 2) * d.completed s * d.invGammaFactor s := (rfl)

/-- The uncompleted function obtained by removing the conductor and gamma factors.
Nonnegative-order singularities of the raw product are repaired analytically;
the representative at any remaining pole is unchanged. -/
noncomputable def continuedL : ℂ → ℂ :=
  toMeromorphicNFOn d.uncompletedProduct {s | 0 ≤ meromorphicOrderAt d.uncompletedProduct s}

/-- The removable-extension construction of the continued uncompleted function. -/
theorem continuedL_def :
    d.continuedL = toMeromorphicNFOn d.uncompletedProduct
      {s | 0 ≤ meromorphicOrderAt d.uncompletedProduct s} :=
  (rfl)

private theorem analyticAt_conductorPower (s : ℂ) :
    AnalyticAt ℂ (fun z ↦ ((d.conductor : ℕ) : ℂ) ^ (-z / 2)) s :=
  (((differentiable_id.neg.div_const 2).const_cpow
    (Or.inl (Nat.cast_ne_zero.mpr d.conductor.ne_zero))).analyticAt s)

private theorem eventually_ne_zero_gammaFactor (s : ℂ) :
    ∀ᶠ z in 𝓝[≠] s, d.gammaFactor z ≠ 0 :=
  (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (d.meromorphic_gammaFactor s)).mp
    (d.meromorphicOrderAt_gammaFactor_ne_top s)

variable {d} (h : d.HasMeromorphicContinuation)

include h

/-- The raw uncompleted product is meromorphic on the whole plane. -/
@[fun_prop]
theorem HasMeromorphicContinuation.meromorphic_uncompletedProduct :
    Meromorphic d.uncompletedProduct := by
  simp only [uncompletedProduct_def]
  exact fun s ↦ ((analyticAt_conductorPower d s).meromorphicAt.mul (h.meromorphic s)).mul
    (d.analyticAt_invGammaFactor s).meromorphicAt

/-- No repair is needed where the raw uncompleted product is analytic. -/
theorem HasMeromorphicContinuation.continuedL_eq_uncompletedProduct_of_analyticAt {s : ℂ}
    (ha : AnalyticAt ℂ d.uncompletedProduct s) :
    d.continuedL s = d.uncompletedProduct s := by
  rw [continuedL_def, toMeromorphicNFOn_eq_toMeromorphicNFAt
    h.meromorphic_uncompletedProduct.meromorphicOn ha.meromorphicOrderAt_nonneg,
    toMeromorphicNFAt_eq_self.mpr ha.meromorphicNFAt]

/-- Removing the archimedean factors changes no punctured germ of the raw product. -/
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
  simp only [uncompletedProduct_def]
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
  simp only [uncompletedProduct_def]
  exact ((analyticAt_conductorPower d s).mul (h.analyticAt s hs)).mul
    (d.analyticAt_invGammaFactor s)

/-- At a genuine pole of the uncompleted function, the raw representative is retained. -/
theorem HasMeromorphicContinuation.continuedL_eq_of_order_neg {s : ℂ}
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
  simp only [uncompletedProduct_def]
  exact (((analyticAt_conductorPower d s).mul (h.analyticAt s hs)).mul
    (d.analyticAt_invGammaFactor s)).meromorphicOrderAt_nonneg

/-- Away from gamma poles and recorded poles, putting back the archimedean factors
recovers the completed function pointwise. -/
theorem HasMeromorphicContinuation.completed_eq_mul_continuedL {s : ℂ}
    (hs : d.polarOrder s = 0) (hγ : d.gammaFactor s ≠ 0) :
    d.completed s = ((d.conductor : ℕ) : ℂ) ^ (s / 2) * d.gammaFactor s * d.continuedL s := by
  rw [h.continuedL_eq hs]
  simp only [uncompletedProduct_def, invGammaFactor_def, neg_div, Complex.cpow_neg]
  have hN := d.conductor_cpow_ne_zero (s / 2)
  field_simp

/-- Putting back the conductor and gamma factors recovers the completed function
as a punctured germ at every point, including the poles. -/
theorem HasMeromorphicContinuation.completed_eventuallyEq_mul_continuedL (s : ℂ) :
    d.completed =ᶠ[𝓝[≠] s]
      fun z ↦ ((d.conductor : ℕ) : ℂ) ^ (z / 2) * d.gammaFactor z * d.continuedL z := by
  filter_upwards [h.continuedL_eventuallyEq s, eventually_ne_zero_gammaFactor d s] with z hz hzγ
  rw [hz]
  simp only [uncompletedProduct_def, invGammaFactor_def, neg_div, Complex.cpow_neg]
  have hN := d.conductor_cpow_ne_zero (z / 2)
  field_simp

/-- An analytic function with the same punctured germ has the repaired value. -/
theorem HasMeromorphicContinuation.continuedL_eq_of_eventuallyEq {g : ℂ → ℂ} {s : ℂ}
    (hg : AnalyticAt ℂ g s) (heq : d.continuedL =ᶠ[𝓝[≠] s] g) :
    d.continuedL s = g s := by
  have ha := h.analyticAt_continuedL
    (by rw [meromorphicOrderAt_congr heq]; exact hg.meromorphicOrderAt_nonneg)
  exact ((ha.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hg.continuousAt).mp
    heq).eq_of_nhds

omit h in
/-- With absolute convergence on the right half-plane, removing the archimedean
factors recovers the Dirichlet series, even at a cancelled gamma pole. -/
theorem HasDirichletAgreement.continuedL_eq_LSeries (hD : d.HasDirichletAgreement)
    (hc : d.HasMeromorphicContinuation) (hg : d.HasAverageCoefficientGrowth)
    {s : ℂ} (hs : 1 < s.re) :
    d.continuedL s = LSeries d.coeff s := by
  have ha := LSeries_analyticOnNhd d.coeff s
    ((hasAverageCoefficientGrowth_iff_abscissaOfAbsConv_le.mp hg).trans_lt
      (by exact_mod_cast hs))
  apply hc.continuedL_eq_of_eventuallyEq ha
  filter_upwards [hc.completed_eventuallyEq_mul_continuedL s, eventually_ne_zero_gammaFactor d s,
    nhdsWithin_le_nhds (continuous_re.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hs))]
    with z hz hzγ hzre
  have hN := d.conductor_cpow_ne_zero (z / 2)
  exact mul_left_cancel₀ (mul_ne_zero hN hzγ) (hz.symm.trans (hD.completed_eq z hzre))

end TauCeti.LFunctions.AnalyticLFunctionData
