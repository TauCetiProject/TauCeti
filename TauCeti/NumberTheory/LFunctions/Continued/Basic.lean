/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Meromorphic.Continuation
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

/-- The uncompleted function obtained by removing the conductor and gamma factors.
Nonnegative-order singularities of the raw product are repaired analytically;
the representative at any remaining pole is unchanged. -/
noncomputable def continuedL : ℂ → ℂ :=
  let R := fun s ↦ ((d.conductor : ℕ) : ℂ) ^ (-s / 2) * d.completed s * d.invGammaFactor s
  toMeromorphicNFOn R {s | 0 ≤ meromorphicOrderAt R s}

/-- The removable-extension construction of the continued uncompleted function. -/
theorem continuedL_def :
    d.continuedL = toMeromorphicNFOn
      (fun s ↦ ((d.conductor : ℕ) : ℂ) ^ (-s / 2) * d.completed s * d.invGammaFactor s)
      {s | 0 ≤ meromorphicOrderAt
        (fun z ↦ ((d.conductor : ℕ) : ℂ) ^ (-z / 2) * d.completed z * d.invGammaFactor z) s} :=
  (rfl)

private theorem analyticAt_conductorPower (s : ℂ) :
    AnalyticAt ℂ (fun z ↦ ((d.conductor : ℕ) : ℂ) ^ (-z / 2)) s :=
  (((differentiable_id.neg.div_const 2).const_cpow
    (Or.inl (Nat.cast_ne_zero.mpr d.conductor.ne_zero))).analyticAt s)

variable {d} (h : d.HasMeromorphicContinuation)

include h

private theorem meromorphic_uncompletedProduct :
    Meromorphic (fun s ↦ ((d.conductor : ℕ) : ℂ) ^ (-s / 2) *
      d.completed s * d.invGammaFactor s) :=
  fun s ↦ ((analyticAt_conductorPower d s).meromorphicAt.mul (h.meromorphic s)).mul
    (d.analyticAt_invGammaFactor s).meromorphicAt

private theorem continuedL_eq_of_analyticAt {s : ℂ}
    (ha : AnalyticAt ℂ
      (fun z ↦ ((d.conductor : ℕ) : ℂ) ^ (-z / 2) * d.completed z * d.invGammaFactor z) s) :
    d.continuedL s = ((d.conductor : ℕ) : ℂ) ^ (-s / 2) * d.completed s * d.invGammaFactor s := by
  rw [continuedL_def, toMeromorphicNFOn_eq_toMeromorphicNFAt
    (meromorphic_uncompletedProduct h).meromorphicOn ha.meromorphicOrderAt_nonneg,
    toMeromorphicNFAt_eq_self.mpr ha.meromorphicNFAt]

/-- Removing the archimedean factors changes no punctured germ of the raw product. -/
theorem HasMeromorphicContinuation.continuedL_eventuallyEq (s : ℂ) :
    d.continuedL =ᶠ[𝓝[≠] s]
      fun z ↦ ((d.conductor : ℕ) : ℂ) ^ (-z / 2) * d.completed z * d.invGammaFactor z := by
  filter_upwards [(meromorphic_uncompletedProduct h s).eventually_analyticAt] with z hz
  exact continuedL_eq_of_analyticAt h hz

/-- The uncompleted function is meromorphic on the whole plane. -/
@[fun_prop]
theorem HasMeromorphicContinuation.meromorphic_continuedL : Meromorphic d.continuedL :=
  fun s ↦ (meromorphic_uncompletedProduct h s).congr (h.continuedL_eventuallyEq s).symm

/-- Dividing out the gamma factor subtracts its meromorphic order, even where its
pole cancels a pole of the completed function. -/
theorem HasMeromorphicContinuation.meromorphicOrderAt_continuedL (s : ℂ) :
    meromorphicOrderAt d.continuedL s =
      meromorphicOrderAt d.completed s - meromorphicOrderAt d.gammaFactor s := by
  rw [meromorphicOrderAt_congr (h.continuedL_eventuallyEq s),
    fun_meromorphicOrderAt_mul
      (f := fun z ↦ ((d.conductor : ℕ) : ℂ) ^ (-z / 2) * d.completed z)
      ((analyticAt_conductorPower d s).meromorphicAt.mul (h.meromorphic s))
      (d.analyticAt_invGammaFactor s).meromorphicAt,
    fun_meromorphicOrderAt_mul (analyticAt_conductorPower d s).meromorphicAt (h.meromorphic s),
    (analyticAt_conductorPower d s).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr
      (Complex.cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr d.conductor.ne_zero))),
    zero_add, d.meromorphicOrderAt_invGammaFactor, sub_eq_add_neg]

/-- The chosen representative is analytic at every point of nonnegative order. -/
theorem HasMeromorphicContinuation.analyticAt_continuedL {s : ℂ}
    (hs : 0 ≤ meromorphicOrderAt d.continuedL s) : AnalyticAt ℂ d.continuedL s := by
  have hr := hs
  rw [meromorphicOrderAt_congr (h.continuedL_eventuallyEq s)] at hr
  have hnf := meromorphicNFOn_toMeromorphicNFOn
    (fun z ↦ ((d.conductor : ℕ) : ℂ) ^ (-z / 2) * d.completed z * d.invGammaFactor z)
    {z | 0 ≤ meromorphicOrderAt
      (fun w ↦ ((d.conductor : ℕ) : ℂ) ^ (-w / 2) * d.completed w * d.invGammaFactor w) z} hr
  rw [← continuedL_def] at hnf
  exact hnf.meromorphicOrderAt_nonneg_iff_analyticAt.mp hs

/-- Nonnegative order exactly characterizes analyticity of the repaired representative. -/
theorem HasMeromorphicContinuation.analyticAt_continuedL_iff (s : ℂ) :
    AnalyticAt ℂ d.continuedL s ↔ 0 ≤ meromorphicOrderAt d.continuedL s :=
  ⟨AnalyticAt.meromorphicOrderAt_nonneg, h.analyticAt_continuedL⟩

/-- Away from the recorded poles, the raw product is already analytic. -/
theorem HasMeromorphicContinuation.continuedL_eq {s : ℂ} (hs : d.polarOrder s = 0) :
    d.continuedL s = ((d.conductor : ℕ) : ℂ) ^ (-s / 2) * d.completed s * d.invGammaFactor s :=
  continuedL_eq_of_analyticAt h
    (((analyticAt_conductorPower d s).mul (h.analyticAt s hs)).mul (d.analyticAt_invGammaFactor s))

/-- At a genuine pole of the uncompleted function, the raw representative is retained. -/
theorem HasMeromorphicContinuation.continuedL_eq_of_order_neg {s : ℂ}
    (hs : meromorphicOrderAt d.continuedL s < 0) :
    d.continuedL s = ((d.conductor : ℕ) : ℂ) ^ (-s / 2) * d.completed s * d.invGammaFactor s := by
  rw [meromorphicOrderAt_congr (h.continuedL_eventuallyEq s)] at hs
  exact toMeromorphicNFOn_eq_self_on_compl
    (meromorphic_uncompletedProduct h).meromorphicOn (not_le.mpr hs)

/-- The defining product needs no repair at points where the completion is analytic. -/
theorem HasMeromorphicContinuation.analyticAt_continuedL_of_polarOrder_eq_zero {s : ℂ}
    (hs : d.polarOrder s = 0) : AnalyticAt ℂ d.continuedL s := by
  apply h.analyticAt_continuedL
  rw [meromorphicOrderAt_congr (h.continuedL_eventuallyEq s)]
  exact (((analyticAt_conductorPower d s).mul (h.analyticAt s hs)).mul
    (d.analyticAt_invGammaFactor s)).meromorphicOrderAt_nonneg

/-- Away from gamma poles and recorded poles, putting back the archimedean factors
recovers the completed function pointwise. -/
theorem HasMeromorphicContinuation.completed_eq_mul_continuedL {s : ℂ}
    (hs : d.polarOrder s = 0) (hγ : d.gammaFactor s ≠ 0) :
    d.completed s = ((d.conductor : ℕ) : ℂ) ^ (s / 2) * d.gammaFactor s * d.continuedL s := by
  rw [h.continuedL_eq hs, invGammaFactor_def, neg_div, Complex.cpow_neg]
  have hN : ((d.conductor : ℕ) : ℂ) ^ (s / 2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr d.conductor.ne_zero))
  field_simp

/-- Putting back the conductor and gamma factors recovers the completed function
as a punctured germ at every point, including the poles. -/
theorem HasMeromorphicContinuation.completed_eventuallyEq_mul_continuedL (s : ℂ) :
    d.completed =ᶠ[𝓝[≠] s]
      fun z ↦ ((d.conductor : ℕ) : ℂ) ^ (z / 2) * d.gammaFactor z * d.continuedL z := by
  have hγ := (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (d.meromorphic_gammaFactor s)).mp
    (d.meromorphicOrderAt_gammaFactor_ne_top s)
  filter_upwards [h.continuedL_eventuallyEq s, hγ] with z hz hzγ
  rw [hz, invGammaFactor_def, neg_div, Complex.cpow_neg]
  have hN : ((d.conductor : ℕ) : ℂ) ^ (z / 2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr d.conductor.ne_zero))
  field_simp

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
  have hγ := (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (d.meromorphic_gammaFactor s)).mp
    (d.meromorphicOrderAt_gammaFactor_ne_top s)
  have heq : d.continuedL =ᶠ[𝓝[≠] s] LSeries d.coeff := by
    filter_upwards [hc.continuedL_eventuallyEq s, hγ,
      nhdsWithin_le_nhds (continuous_re.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hs))]
      with z hz hzγ hzre
    rw [hz, hD.completed_eq z hzre, invGammaFactor_def, neg_div, Complex.cpow_neg]
    have hN : ((d.conductor : ℕ) : ℂ) ^ (z / 2) ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr d.conductor.ne_zero))
    field_simp
  have hcont := hc.analyticAt_continuedL (s := s)
    (by rw [meromorphicOrderAt_congr heq]; exact ha.meromorphicOrderAt_nonneg)
  exact ((hcont.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE ha.continuousAt).mp
    heq).eq_of_nhds

end TauCeti.LFunctions.AnalyticLFunctionData
