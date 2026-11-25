/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Meromorphic.TrailingCoefficient
public import TauCeti.Analysis.Meromorphic.LogDeriv
import Mathlib.Analysis.Calculus.LogDeriv

/-!
# Meromorphic Mellin expression for a first Riesz remainder

The kernel of the first Riesz sum is `1 / (s * (s - 1))`. Multiplying the negative
logarithmic derivative by this kernel and subtracting its principal part at `1` gives the
meromorphic expression for the Mellin transform of the corresponding smoothed remainder.
The normalization matters: the total quotient obtained by division by `s - 1` need not take
its limiting value at `1`. Off `0` and `1`, each nonzero order of the input produces a
simple pole with residue `ord / (s * (1 - s))`.

The Dirichlet-character pole formula is used in L. Alpöge's
`Deduction.poleData_char` (<https://github.com/leanprover-community/riemann-hypothesis>).
-/

public section

open Filter Set Topology

namespace TauCeti

/-- The meromorphic normal form of the negative logarithmic derivative times the first Riesz
kernel, with the principal part at `1` subtracted. The subtracted terms are determined by the
order and the finite part of the logarithmic derivative at `1`. -/
noncomputable def rieszRemainderMellin (L : ℂ → ℂ) : ℂ → ℂ :=
  toMeromorphicNFOn (fun s ↦
    (s * logDerivFinitePart L 1 - (meromorphicOrderAt L 1).untop₀ * (s - 1) -
      (logDeriv L s - (meromorphicOrderAt L 1).untop₀ / (s - 1))) / (s * (s - 1))) univ

/-- The Riesz remainder Mellin expression is meromorphic in normal form. -/
theorem meromorphicNFOn_rieszRemainderMellin (L : ℂ → ℂ) :
    MeromorphicNFOn (rieszRemainderMellin L) univ :=
  meromorphicNFOn_toMeromorphicNFOn _ _

/-- The quotient defining the Mellin expression, before normalization, describes its
punctured germ at every point. -/
theorem rieszRemainderMellin_eventuallyEq {L : ℂ → ℂ} (hL : Meromorphic L) (z : ℂ) :
    rieszRemainderMellin L =ᶠ[𝓝[≠] z] fun s ↦
      (s * logDerivFinitePart L 1 - (meromorphicOrderAt L 1).untop₀ * (s - 1) -
        (logDeriv L s - (meromorphicOrderAt L 1).untop₀ / (s - 1))) / (s * (s - 1)) := by
  have hm : Meromorphic (fun s ↦
      (s * logDerivFinitePart L 1 - (meromorphicOrderAt L 1).untop₀ * (s - 1) -
      (logDeriv L s - (meromorphicOrderAt L 1).untop₀ / (s - 1))) / (s * (s - 1))) := by
    have := hL.logDeriv
    fun_prop
  exact (meromorphicOn_univ.mpr hm).toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ z)

/-- At a regular nonzero point of `L` other than `0` or `1`, the Mellin expression is analytic
and its value is given by the defining quotient. -/
theorem rieszRemainderMellin_eq_and_analyticAt {L : ℂ → ℂ} (hL : Meromorphic L) {s : ℂ}
    (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) (ha : AnalyticAt ℂ L s) (hne : L s ≠ 0) :
    rieszRemainderMellin L s =
      (s * logDerivFinitePart L 1 - (meromorphicOrderAt L 1).untop₀ * (s - 1) -
      (logDeriv L s - (meromorphicOrderAt L 1).untop₀ / (s - 1))) / (s * (s - 1)) ∧
      AnalyticAt ℂ (rieszRemainderMellin L) s := by
  have hlog : AnalyticAt ℂ (logDeriv L) s := ha.deriv.fun_div ha hne
  have hsub := sub_ne_zero.mpr hs₁
  have hden := mul_ne_zero hs₀ hsub
  have hq : AnalyticAt ℂ (fun w ↦
      (w * logDerivFinitePart L 1 - (meromorphicOrderAt L 1).untop₀ * (w - 1) -
      (logDeriv L w - (meromorphicOrderAt L 1).untop₀ / (w - 1))) / (w * (w - 1))) s := by
    fun_prop (disch := assumption)
  have hnf := meromorphicNFOn_rieszRemainderMellin L (mem_univ s)
  have heq := (hnf.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds hq.meromorphicNFAt).mp
    (rieszRemainderMellin_eventuallyEq hL s)
  exact ⟨heq.eq_of_nhds, hq.congr heq.symm⟩

/-- The analytic representative of the compensated logarithmic derivative at `1` gives the
value and the analytic germ of the Riesz remainder Mellin expression there. -/
theorem rieszRemainderMellin_eventuallyEq_dslope {L g : ℂ → ℂ} (hL : Meromorphic L)
    (hg : AnalyticAt ℂ g 1) (heq : (fun s ↦
      logDeriv L s - (meromorphicOrderAt L 1).untop₀ / (s - 1)) =ᶠ[𝓝[≠] 1] g) :
    rieszRemainderMellin L =ᶠ[𝓝 1] fun s ↦
      (g 1 - (meromorphicOrderAt L 1).untop₀ - dslope g 1 s) / s := by
  have ha : AnalyticAt ℂ (fun s ↦
      (g 1 - (meromorphicOrderAt L 1).untop₀ - dslope g 1 s) / s) 1 :=
    (analyticAt_const.fun_sub (hg.dslope 1)).fun_div analyticAt_id one_ne_zero
  have hnf := meromorphicNFOn_rieszRemainderMellin L (mem_univ (1 : ℂ))
  apply (hnf.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds ha.meromorphicNFAt).mp
  refine (rieszRemainderMellin_eventuallyEq hL 1).trans ?_
  filter_upwards [heq, self_mem_nhdsWithin] with s hs h₁
  have hne : s ≠ (1 : ℂ) := h₁
  rw [logDerivFinitePart_eq hg heq, hs, dslope_of_ne g hne, slope_def_field]
  by_cases h₀ : s = 0
  · simp [h₀]
  · field_simp [sub_ne_zero.mpr hne]
    ring

/-- The main-term subtraction removes the pole at `1`, including when the input has a pole
there. -/
theorem analyticAt_rieszRemainderMellin_one {L : ℂ → ℂ} (hL : Meromorphic L) :
    AnalyticAt ℂ (rieszRemainderMellin L) 1 := by
  obtain ⟨g, hg, heq⟩ := (hL 1).exists_analyticAt_logDeriv_sub_order_div
  have ha : AnalyticAt ℂ (fun s ↦
      (g 1 - (meromorphicOrderAt L 1).untop₀ - dslope g 1 s) / s) 1 :=
    (analyticAt_const.fun_sub (hg.dslope 1)).fun_div analyticAt_id one_ne_zero
  exact ha.congr (rieszRemainderMellin_eventuallyEq_dslope hL hg heq).symm

/-- Away from `0` and `1`, multiplying the Mellin germ by `s - z` gives an analytic numerator
whose value at `z` is the order of `L` divided by `z * (1 - z)`. -/
theorem exists_analyticAt_mul_rieszRemainderMellin {L : ℂ → ℂ} (hL : Meromorphic L)
    {z : ℂ} (hz₀ : z ≠ 0) (hz₁ : z ≠ 1) {n : ℤ} (hn : meromorphicOrderAt L z = n) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H z ∧ H z = (n : ℂ) / (z * (1 - z)) ∧
      (fun s ↦ (s - z) * rieszRemainderMellin L s) =ᶠ[𝓝[≠] z] H := by
  obtain ⟨g, hg, heq⟩ := (hL z).exists_analyticAt_logDeriv_sub_order_div
  rw [hn, WithTop.untop₀_coe] at heq
  let H (s : ℂ) := ((s - z) * (s * logDerivFinitePart L 1 -
    (meromorphicOrderAt L 1).untop₀ * (s - 1) - g s +
    (meromorphicOrderAt L 1).untop₀ / (s - 1)) - (n : ℂ)) / (s * (s - 1))
  refine ⟨H, ?_, ?_, ?_⟩
  · dsimp only [H]
    have hsub := sub_ne_zero.mpr hz₁
    have hden := mul_ne_zero hz₀ hsub
    fun_prop (disch := assumption)
  · simp only [H, sub_self, zero_mul, zero_sub, neg_div]
    rw [← div_neg, ← mul_neg, neg_sub]
  · filter_upwards [rieszRemainderMellin_eventuallyEq hL z, heq, self_mem_nhdsWithin]
      with s hs ht hu
    have hsz : s ≠ z := hu
    have ht' := sub_eq_iff_eq_add.mp ht
    rw [hs, ht']
    dsimp only [H]
    rw [← mul_div_assoc]
    congr 1
    field_simp [sub_ne_zero.mpr hsz]
    ring

/-- At a point different from `0` and `1` where `L` has finite nonzero order `n`, the Mellin
expression has a simple pole with residue `n / (z * (1 - z))`. -/
theorem rieszRemainderMellin_simplePole {L : ℂ → ℂ} (hL : Meromorphic L)
    {z : ℂ} (hz₀ : z ≠ 0) (hz₁ : z ≠ 1) {n : ℤ} (hn : meromorphicOrderAt L z = n) (hne : n ≠ 0) :
    meromorphicOrderAt (rieszRemainderMellin L) z = -1 ∧
      meromorphicTrailingCoeffAt (rieszRemainderMellin L) z = (n : ℂ) / (z * (1 - z)) := by
  obtain ⟨H, ha, hval, heq⟩ := exists_analyticAt_mul_rieszRemainderMellin hL hz₀ hz₁ hn
  have hH : H z ≠ 0 := by
    rw [hval]
    exact div_ne_zero (Int.cast_ne_zero.mpr hne) (mul_ne_zero hz₀ (sub_ne_zero.mpr hz₁.symm))
  have hrepr : rieszRemainderMellin L =ᶠ[𝓝[≠] z] fun s ↦ (s - z) ^ (-1 : ℤ) • H s := by
    filter_upwards [heq, self_mem_nhdsWithin] with s hs hsz
    rw [zpow_neg_one, smul_eq_mul, ← hs, inv_mul_cancel_left₀ (sub_ne_zero.mpr hsz)]
  have hm := (meromorphicNFOn_rieszRemainderMellin L (mem_univ z)).meromorphicAt
  refine ⟨?_, (ha.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE hH hrepr).trans hval⟩
  exact (meromorphicOrderAt_eq_int_iff hm).mpr ⟨H, ha, hH, hrepr⟩

end TauCeti
