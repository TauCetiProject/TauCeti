/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Data.Series
public import TauCeti.NumberTheory.LFunctions.Data.Comparison

/-!
# Removing the conductor and gamma factors from a completed L-function

`AnalyticLFunctionData.continuedL` removes the conductor power and the gamma factor
from the completed function. A pole of the completion can be cancelled by a zero of the
reciprocal gamma factor. The raw pointwise product has an incorrect value at such a
removable singularity, so we repair its nonnegative-order germs using Mathlib's
`toMeromorphicNFOn`. When the raw product is meromorphic on `ℂ`, genuine poles retain
the original representative; otherwise the construction returns the zero function.

The repaired function is always meromorphic and analytic at every point of nonnegative
order. When the completion is meromorphic, its order is the order of the completion minus
that of the gamma factor, and it recovers the completion as a punctured germ everywhere.
Under `HasMeromorphicContinuation`, it also agrees with the raw product away from the recorded
poles. These statements do not require a functional equation or a Dirichlet series.
With a meromorphic completion and Dirichlet agreement, it agrees with the Dirichlet series
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
theorem uncompletedProduct_dual :
    d.dual.uncompletedProduct = conj ∘ d.uncompletedProduct ∘ conj := by
  funext s
  simp only [Function.comp_apply]
  simp only [uncompletedProduct_def, dual_conductor, dual_completed_apply,
    invGammaFactor_def, gammaFactor_dual, map_mul, map_inv₀]
  have hN := TauCeti.ofReal_cpow_conj (d.conductor : ℕ).cast_nonneg (-(conj s) / 2)
  simp only [Complex.ofReal_natCast, map_div₀, map_neg, map_ofNat, conj_conj] at hN
  rw [← hN]

/-- The dual raw product evaluated at a point is the conjugate value at the reflected point. -/
theorem uncompletedProduct_dual_apply (s : ℂ) :
    d.dual.uncompletedProduct s = conj (d.uncompletedProduct (conj s)) :=
  congrFun d.uncompletedProduct_dual s

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
theorem continuedL_dual :
    d.dual.continuedL = conj ∘ d.continuedL ∘ conj := by
  simp only [continuedL_def, uncompletedProduct_dual, meromorphicOrderAt_conj_conj,
    toMeromorphicNFOn_conj_conj, Set.preimage_ofPred_eq, conj_conj]

/-- The dual continued function evaluated at a point is the conjugate value at the
reflected point. -/
theorem continuedL_dual_apply (s : ℂ) :
    d.dual.continuedL s = conj (d.continuedL (conj s)) :=
  congrFun d.continuedL_dual s

private theorem analyticAt_conductorPower (s : ℂ) :
    AnalyticAt ℂ (fun z ↦ ((d.conductor : ℕ) : ℂ) ^ (-z / 2)) s :=
  d.analyticAt_conductor_cpow (by fun_prop)

variable {d}

/-- Away from gamma poles, putting back the conductor and gamma factors recovers
the completion from the raw product, without any meromorphy assumption. -/
theorem completed_eq_mul_uncompletedProduct {s : ℂ} (hγ : d.gammaFactor s ≠ 0) :
    d.completed s = ((d.conductor : ℕ) : ℂ) ^ (s / 2) * d.gammaFactor s *
      d.uncompletedProduct s := by
  simp only [uncompletedProduct_def, invGammaFactor_def, neg_div, Complex.cpow_neg]
  have hN := d.conductor_cpow_ne_zero (s / 2)
  field_simp

/-- Analyticity of the completion passes to the raw uncompleted product. -/
@[fun_prop]
theorem analyticAt_uncompletedProduct {s : ℂ} (ha : AnalyticAt ℂ d.completed s) :
    AnalyticAt ℂ d.uncompletedProduct s := by
  rw [funext d.uncompletedProduct_def]
  exact ((analyticAt_conductorPower d s).mul ha).mul (d.analyticAt_invGammaFactor s)

/-- Meromorphy of the completion passes to the raw uncompleted product at each point. -/
@[fun_prop]
theorem meromorphicAt_uncompletedProduct {s : ℂ} (hm : MeromorphicAt d.completed s) :
    MeromorphicAt d.uncompletedProduct s := by
  rw [funext d.uncompletedProduct_def]
  exact ((analyticAt_conductorPower d s).meromorphicAt.mul hm).mul
    (d.analyticAt_invGammaFactor s).meromorphicAt

/-- The raw product is meromorphic at a point exactly when the completion is. -/
@[simp]
theorem meromorphicAt_uncompletedProduct_iff {s : ℂ} :
    MeromorphicAt d.uncompletedProduct s ↔ MeromorphicAt d.completed s := by
  refine ⟨fun hm ↦ ?_, meromorphicAt_uncompletedProduct⟩
  have hN := d.analyticAt_conductor_cpow (s := s) (g := fun z ↦ z / 2) (by fun_prop)
  have heq : d.completed =ᶠ[𝓝[≠] s]
      fun z ↦ ((d.conductor : ℕ) : ℂ) ^ (z / 2) * d.gammaFactor z *
        d.uncompletedProduct z := by
    filter_upwards [d.eventually_gammaFactor_ne_zero s] with z hz
    exact completed_eq_mul_uncompletedProduct hz
  exact ((hN.meromorphicAt.mul (d.meromorphic_gammaFactor s)).mul hm).congr heq.symm

/-- If the completion is globally meromorphic, so is the raw uncompleted product. -/
@[fun_prop]
theorem meromorphic_uncompletedProduct (hm : Meromorphic d.completed) :
    Meromorphic d.uncompletedProduct :=
  fun s ↦ meromorphicAt_uncompletedProduct (hm s)

/-- The raw product is globally meromorphic exactly when the completion is. -/
@[simp]
theorem meromorphic_uncompletedProduct_iff :
    Meromorphic d.uncompletedProduct ↔ Meromorphic d.completed :=
  ⟨fun hm s ↦ meromorphicAt_uncompletedProduct_iff.mp (hm s), meromorphic_uncompletedProduct⟩

private theorem meromorphic_uncompletedProduct_of_meromorphicOn
    (hm : MeromorphicOn d.uncompletedProduct
      {z | 0 ≤ meromorphicOrderAt d.uncompletedProduct z}) :
    Meromorphic d.uncompletedProduct := by
  -- Off meromorphy the order is zero, so meromorphy on this locus forces global meromorphy.
  intro z
  by_contra hz
  exact hz (hm z (by simp only [Set.mem_ofPred_eq,
    meromorphicOrderAt_of_not_meromorphicAt hz]; exact le_rfl))

/-- Without a globally meromorphic completion, the continued function is identically zero. -/
@[simp]
theorem continuedL_of_not_meromorphic (hm : ¬ Meromorphic d.completed) :
    d.continuedL = 0 := by
  rw [continuedL_def]
  apply toMeromorphicNFOn_of_not_meromorphicOn
  exact fun h ↦ hm (meromorphic_uncompletedProduct_iff.mp
    (meromorphic_uncompletedProduct_of_meromorphicOn h))

/-- With a globally meromorphic completion, no repair is needed where the raw
uncompleted product is analytic. -/
theorem continuedL_eq_uncompletedProduct_of_analyticAt (hm : Meromorphic d.completed) {s : ℂ}
    (ha : AnalyticAt ℂ d.uncompletedProduct s) :
    d.continuedL s = d.uncompletedProduct s := by
  rw [continuedL_def, toMeromorphicNFOn_eq_toMeromorphicNFAt
    (meromorphic_uncompletedProduct hm).meromorphicOn ha.meromorphicOrderAt_nonneg,
    toMeromorphicNFAt_eq_self.mpr ha.meromorphicNFAt]

/-- With a globally meromorphic completion, repairing nonnegative-order singularities
changes no punctured germ of the raw product. -/
theorem continuedL_eventuallyEq (hm : Meromorphic d.completed) (s : ℂ) :
    d.continuedL =ᶠ[𝓝[≠] s] d.uncompletedProduct := by
  filter_upwards [(meromorphic_uncompletedProduct hm s).eventually_analyticAt] with z hz
  exact continuedL_eq_uncompletedProduct_of_analyticAt hm hz

/-- The uncompleted function is meromorphic on the whole plane. -/
@[fun_prop]
theorem meromorphic_continuedL (d : AnalyticLFunctionData) : Meromorphic d.continuedL := by
  by_cases hm : Meromorphic d.completed
  · exact fun s ↦ (meromorphic_uncompletedProduct hm s).congr
      (continuedL_eventuallyEq hm s).symm
  · rw [continuedL_of_not_meromorphic hm]
    exact fun _ ↦ analyticAt_const.meromorphicAt

/-- With a globally meromorphic completion, dividing out the gamma factor subtracts its
meromorphic order, even where its pole cancels a pole of the completed function. -/
theorem meromorphicOrderAt_continuedL (hm : Meromorphic d.completed) (s : ℂ) :
    meromorphicOrderAt d.continuedL s =
      meromorphicOrderAt d.completed s - meromorphicOrderAt d.gammaFactor s := by
  rw [meromorphicOrderAt_congr (continuedL_eventuallyEq hm s)]
  rw [funext d.uncompletedProduct_def]
  rw [fun_meromorphicOrderAt_mul
      (f := fun z ↦ ((d.conductor : ℕ) : ℂ) ^ (-z / 2) * d.completed z)
      ((analyticAt_conductorPower d s).meromorphicAt.mul (hm s))
      (d.analyticAt_invGammaFactor s).meromorphicAt,
    fun_meromorphicOrderAt_mul (analyticAt_conductorPower d s).meromorphicAt (hm s),
    (analyticAt_conductorPower d s).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr
      (d.conductor_cpow_ne_zero _),
    zero_add, d.meromorphicOrderAt_invGammaFactor, sub_eq_add_neg]

/-- The chosen representative is analytic at every point of nonnegative order. -/
theorem analyticAt_continuedL {s : ℂ}
    (hs : 0 ≤ meromorphicOrderAt d.continuedL s) : AnalyticAt ℂ d.continuedL s := by
  by_cases hm : Meromorphic d.completed
  · have hr := hs
    rw [meromorphicOrderAt_congr (continuedL_eventuallyEq hm s)] at hr
    have hnf := meromorphicNFOn_toMeromorphicNFOn d.uncompletedProduct
      {z | 0 ≤ meromorphicOrderAt d.uncompletedProduct z} hr
    rw [← continuedL_def] at hnf
    exact hnf.meromorphicOrderAt_nonneg_iff_analyticAt.mp hs
  · rw [continuedL_of_not_meromorphic hm]
    exact analyticAt_const

/-- Nonnegative order exactly characterizes analyticity of the repaired representative. -/
theorem analyticAt_continuedL_iff (d : AnalyticLFunctionData) (s : ℂ) :
    AnalyticAt ℂ d.continuedL s ↔ 0 ≤ meromorphicOrderAt d.continuedL s :=
  ⟨AnalyticAt.meromorphicOrderAt_nonneg, analyticAt_continuedL⟩

/-- Analyticity of the raw uncompleted product passes to the continued function,
without any global meromorphy assumption. -/
theorem analyticAt_continuedL_of_analyticAt_uncompletedProduct {s : ℂ}
    (ha : AnalyticAt ℂ d.uncompletedProduct s) : AnalyticAt ℂ d.continuedL s := by
  by_cases hm : Meromorphic d.completed
  · apply analyticAt_continuedL
    rw [meromorphicOrderAt_congr (continuedL_eventuallyEq hm s)]
    exact ha.meromorphicOrderAt_nonneg
  · rw [continuedL_of_not_meromorphic hm]
    exact analyticAt_const

/-- Analyticity of the completion passes to the continued uncompleted function,
without any global meromorphy assumption. -/
@[fun_prop]
theorem analyticAt_continuedL_of_analyticAt {s : ℂ} (ha : AnalyticAt ℂ d.completed s) :
    AnalyticAt ℂ d.continuedL s :=
  analyticAt_continuedL_of_analyticAt_uncompletedProduct (analyticAt_uncompletedProduct ha)

/-- Away from the recorded poles, `continuedL` equals the raw uncompleted product. -/
theorem HasMeromorphicContinuation.continuedL_eq (h : d.HasMeromorphicContinuation)
    {s : ℂ} (hs : d.polarOrder s = 0) :
    d.continuedL s = d.uncompletedProduct s := by
  apply continuedL_eq_uncompletedProduct_of_analyticAt h.meromorphic
  exact analyticAt_uncompletedProduct (h.analyticAt s hs)

/-- At a genuine pole of the uncompleted function, the raw representative is retained. -/
theorem continuedL_eq_uncompletedProduct_of_meromorphicOrderAt_neg {s : ℂ}
    (hs : meromorphicOrderAt d.continuedL s < 0) :
    d.continuedL s = d.uncompletedProduct s := by
  by_cases hm : Meromorphic d.completed
  · rw [meromorphicOrderAt_congr (continuedL_eventuallyEq hm s)] at hs
    rw [continuedL_def]
    exact toMeromorphicNFOn_eq_self_on_compl
      (meromorphic_uncompletedProduct hm).meromorphicOn (not_le.mpr hs)
  · rw [continuedL_of_not_meromorphic hm] at hs
    exact False.elim (not_lt_of_ge analyticAt_const.meromorphicOrderAt_nonneg hs)

/-- A normal-form representative of the completion gives a normal-form continued function
at the same point, including the canonical zero value at any remaining pole. -/
theorem meromorphicNFAt_continuedL {s : ℂ}
    (hNF : MeromorphicNFAt d.completed s) : MeromorphicNFAt d.continuedL s := by
  rcases meromorphicNFAt_iff_analyticAt_or.mp hNF with ha | ⟨_, _, hz⟩
  · exact (analyticAt_continuedL_of_analyticAt ha).meromorphicNFAt
  · by_cases hs : 0 ≤ meromorphicOrderAt d.continuedL s
    · exact (analyticAt_continuedL hs).meromorphicNFAt
    · refine meromorphicNFAt_iff_analyticAt_or.mpr
        (Or.inr ⟨d.meromorphic_continuedL s, lt_of_not_ge hs, ?_⟩)
      rw [continuedL_eq_uncompletedProduct_of_meromorphicOrderAt_neg (lt_of_not_ge hs),
        uncompletedProduct_def, hz, mul_zero, zero_mul]

/-- Normal form of the completion on a set passes to the continued uncompleted function. -/
theorem meromorphicNFOn_continuedL {U : Set ℂ}
    (hNF : MeromorphicNFOn d.completed U) : MeromorphicNFOn d.continuedL U :=
  fun _ hs ↦ meromorphicNFAt_continuedL (hNF hs)

/-- `continuedL` is analytic at every point where the record has no pole. -/
theorem HasMeromorphicContinuation.analyticAt_continuedL_of_polarOrder_eq_zero
    (h : d.HasMeromorphicContinuation) {s : ℂ}
    (hs : d.polarOrder s = 0) : AnalyticAt ℂ d.continuedL s :=
  analyticAt_continuedL_of_analyticAt (h.analyticAt s hs)

/-- Away from gamma poles, no repair of the raw uncompleted product is needed. -/
theorem HasMeromorphicContinuation.continuedL_eq_of_gammaFactor_ne_zero
    (h : d.HasMeromorphicContinuation) {s : ℂ}
    (hγ : d.gammaFactor s ≠ 0) : d.continuedL s = d.uncompletedProduct s := by
  by_cases hs : d.polarOrder s = 0
  · exact h.continuedL_eq hs
  · apply continuedL_eq_uncompletedProduct_of_meromorphicOrderAt_neg
    rw [meromorphicOrderAt_continuedL h.meromorphic,
      (d.meromorphicOrderAt_gammaFactor_eq_zero_iff s).mpr hγ, sub_zero,
      h.meromorphicOrderAt_eq s hs]
    exact_mod_cast neg_lt_zero.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hs) :
      (0 : ℤ) < d.polarOrder s)

/-- Away from gamma poles, putting back the conductor and gamma factors recovers
the completed function pointwise, including at recorded poles. -/
theorem HasMeromorphicContinuation.completed_eq_mul_continuedL
    (h : d.HasMeromorphicContinuation) {s : ℂ}
    (hγ : d.gammaFactor s ≠ 0) :
    d.completed s = ((d.conductor : ℕ) : ℂ) ^ (s / 2) * d.gammaFactor s * d.continuedL s := by
  rw [h.continuedL_eq_of_gammaFactor_ne_zero hγ]
  exact completed_eq_mul_uncompletedProduct hγ

/-- With a globally meromorphic completion, putting back the conductor and gamma factors
recovers the completed function as a punctured germ at every point, including the poles. -/
theorem completed_eventuallyEq_mul_continuedL (hm : Meromorphic d.completed) (s : ℂ) :
    d.completed =ᶠ[𝓝[≠] s]
      fun z ↦ ((d.conductor : ℕ) : ℂ) ^ (z / 2) * d.gammaFactor z * d.continuedL z := by
  filter_upwards [continuedL_eventuallyEq hm s, d.eventually_gammaFactor_ne_zero s]
    with z hz hzγ
  rw [hz]
  exact completed_eq_mul_uncompletedProduct hzγ

/-- A continuous function with the same punctured germ has the repaired value. -/
theorem continuedL_eq_of_eventuallyEq {g : ℂ → ℂ} {s : ℂ}
    (hg : ContinuousAt g s) (heq : d.continuedL =ᶠ[𝓝[≠] s] g) :
    d.continuedL s = g s := by
  have hga := ((d.meromorphic_continuedL s).congr heq).analyticAt hg
  have ha := analyticAt_continuedL
    (by rw [meromorphicOrderAt_congr heq]; exact hga.meromorphicOrderAt_nonneg)
  exact ((ha.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hg).mp heq).eq_of_nhds

/-- With a meromorphic completion and Dirichlet agreement, removing the conductor and gamma
factors recovers the Dirichlet series on `Re s > 1`, even at a cancelled gamma pole. -/
theorem HasDirichletAgreement.continuedL_eq_LSeries (hD : d.HasDirichletAgreement)
    (hm : Meromorphic d.completed) {s : ℂ} (hs : 1 < s.re) :
    d.continuedL s = LSeries d.coeff s := by
  apply continuedL_eq_of_eventuallyEq
    (hD.analyticAt_LSeries (hm s) hs).continuousAt
  filter_upwards [completed_eventuallyEq_mul_continuedL hm s, d.eventually_gammaFactor_ne_zero s,
    nhdsWithin_le_nhds (continuous_re.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hs))]
    with z hz hzγ hzre
  have hN := d.conductor_cpow_ne_zero (z / 2)
  exact mul_left_cancel₀ (mul_ne_zero hN hzγ) (hz.symm.trans (hD.completed_eq z hzre))

/-- With Dirichlet agreement, the continued function is analytic on `Re s > 1`,
including at cancelled gamma poles, without any global meromorphy assumption. -/
theorem HasDirichletAgreement.analyticAt_continuedL (hD : d.HasDirichletAgreement)
    {s : ℂ} (hs : 1 < s.re) : AnalyticAt ℂ d.continuedL s := by
  by_cases hm : Meromorphic d.completed
  · apply (hD.analyticAt_LSeries (hm s) hs).congr
    filter_upwards [continuous_re.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hs)] with z hz
    exact (hD.continuedL_eq_LSeries hm hz).symm
  · rw [continuedL_of_not_meromorphic hm]
    exact analyticAt_const

/-- With Dirichlet agreement and a globally meromorphic completion, normalizing the continued
function on the whole plane gives the canonical meromorphic continuation of its Dirichlet series,
including canonical values at poles. -/
theorem HasDirichletAgreement.toMeromorphicNFOn_continuedL (hD : d.HasDirichletAgreement)
    (hm : Meromorphic d.completed) :
    toMeromorphicNFOn d.continuedL Set.univ = meromorphicContinuation 1 (LSeries d.coeff) :=
  (meromorphicContinuation_eq_toMeromorphicNFOn d.meromorphic_continuedL
    (fun _ hs ↦ hD.analyticAt_continuedL hs)
    (fun _ hs ↦ hD.continuedL_eq_LSeries hm hs)).symm

/-- With Dirichlet agreement and a completion in normal form on `ℂ`, the continued uncompleted
function is exactly the canonical meromorphic continuation of its Dirichlet series,
also at remaining poles. -/
theorem HasDirichletAgreement.continuedL_eq_meromorphicContinuation
    (hD : d.HasDirichletAgreement) (hNF : MeromorphicNFOn d.completed Set.univ) :
    d.continuedL = meromorphicContinuation 1 (LSeries d.coeff) := by
  rw [← hD.toMeromorphicNFOn_continuedL (meromorphicOn_univ.mp hNF.meromorphicOn),
    toMeromorphicNFOn_eq_self.mpr (meromorphicNFOn_continuedL hNF)]

end TauCeti.LFunctions.AnalyticLFunctionData
