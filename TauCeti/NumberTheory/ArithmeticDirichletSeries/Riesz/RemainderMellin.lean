/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Meromorphic.TrailingCoefficient
public import TauCeti.Analysis.Meromorphic.Continuation
public import TauCeti.Analysis.Meromorphic.LogDeriv
import Mathlib.Analysis.Calculus.LogDeriv
import TauCeti.Analysis.Calculus.LogDeriv
import TauCeti.Analysis.Meromorphic.Order

/-!
# Meromorphic Mellin expression for a first Riesz remainder

The kernel of the first Riesz sum is `1 / (s * (s - 1))`. Multiplying the negative
logarithmic derivative by this kernel and subtracting its principal part at `1` gives a
meromorphic function `TauCeti.rieszRemainderMellin`, the expression that is meant to be
identified with the Mellin transform of the corresponding smoothed remainder. That
identification is not proved here; this file records the function itself, its value at `1`,
and its poles and residues. The normalization matters: the total quotient obtained by
division by `s - 1` need not take its limiting value at `1`. Off `0` and `1`, each nonzero
order of the input produces a simple pole with residue `ord / (s * (1 - s))`.

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
theorem _root_.Meromorphic.rieszRemainderMellin_eventuallyEq {L : ℂ → ℂ}
    (hL : Meromorphic L) (z : ℂ) :
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
theorem _root_.Meromorphic.rieszRemainderMellin_eq_and_analyticAt {L : ℂ → ℂ}
    (hL : Meromorphic L) {s : ℂ} (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) (ha : AnalyticAt ℂ L s)
    (hne : L s ≠ 0) :
    rieszRemainderMellin L s =
      (s * logDerivFinitePart L 1 - (meromorphicOrderAt L 1).untop₀ * (s - 1) -
      (logDeriv L s - (meromorphicOrderAt L 1).untop₀ / (s - 1))) / (s * (s - 1)) ∧
      AnalyticAt ℂ (rieszRemainderMellin L) s := by
  have hsub := sub_ne_zero.mpr hs₁
  have hden := mul_ne_zero hs₀ hsub
  have hq : AnalyticAt ℂ (fun w ↦
      (w * logDerivFinitePart L 1 - (meromorphicOrderAt L 1).untop₀ * (w - 1) -
      (logDeriv L w - (meromorphicOrderAt L 1).untop₀ / (w - 1))) / (w * (w - 1))) s := by
    fun_prop (disch := assumption)
  have hnf := meromorphicNFOn_rieszRemainderMellin L (mem_univ s)
  have heq := (hnf.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds hq.meromorphicNFAt).mp
    (hL.rieszRemainderMellin_eventuallyEq s)
  exact ⟨heq.eq_of_nhds, hq.congr heq.symm⟩

/-- The analytic expression for the Mellin germ at `1` in terms of a representative `g`. -/
private theorem analyticAt_sub_dslope_div {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 1) (c : ℂ) :
    AnalyticAt ℂ (fun s ↦ (g 1 - c - dslope g 1 s) / s) 1 :=
  (analyticAt_const.fun_sub (hg.dslope 1)).fun_div analyticAt_id one_ne_zero

/-- The analytic representative of the compensated logarithmic derivative at `1` gives the
value and the analytic germ of the Riesz remainder Mellin expression there. -/
theorem _root_.Meromorphic.rieszRemainderMellin_eventuallyEq_dslope {L g : ℂ → ℂ}
    (hL : Meromorphic L) (hg : AnalyticAt ℂ g 1) (heq : (fun s ↦
      logDeriv L s - (meromorphicOrderAt L 1).untop₀ / (s - 1)) =ᶠ[𝓝[≠] 1] g) :
    rieszRemainderMellin L =ᶠ[𝓝 1] fun s ↦
      (g 1 - (meromorphicOrderAt L 1).untop₀ - dslope g 1 s) / s := by
  have ha := analyticAt_sub_dslope_div hg (meromorphicOrderAt L 1).untop₀
  have hnf := meromorphicNFOn_rieszRemainderMellin L (mem_univ (1 : ℂ))
  apply (hnf.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds ha.meromorphicNFAt).mp
  refine (hL.rieszRemainderMellin_eventuallyEq 1).trans ?_
  filter_upwards [heq, self_mem_nhdsWithin] with s hs h₁
  have hne : s ≠ (1 : ℂ) := h₁
  rw [hg.logDerivFinitePart_eq heq, hs, dslope_of_ne g hne, slope_def_field]
  by_cases h₀ : s = 0
  · simp [h₀]
  · field_simp [sub_ne_zero.mpr hne]
    ring

/-- The main-term subtraction removes the pole at `1`, including when the input has a pole
there. -/
theorem _root_.Meromorphic.analyticAt_rieszRemainderMellin_one {L : ℂ → ℂ}
    (hL : Meromorphic L) : AnalyticAt ℂ (rieszRemainderMellin L) 1 := by
  obtain ⟨g, hg, heq⟩ := (hL 1).exists_analyticAt_logDeriv_sub_order_div
  exact (analyticAt_sub_dslope_div hg _).congr
    (hL.rieszRemainderMellin_eventuallyEq_dslope hg heq).symm

/-- If `L` is analytic and nonzero at `1`, then with `D = logDeriv L` the Mellin expression
takes the value `D 1 - D′ 1` at `1`. -/
theorem _root_.Meromorphic.rieszRemainderMellin_one {L : ℂ → ℂ} (hL : Meromorphic L)
    (ha : AnalyticAt ℂ L 1) (h₁ : L 1 ≠ 0) :
    rieszRemainderMellin L 1 = logDeriv L 1 - deriv (logDeriv L) 1 := by
  have hord : meromorphicOrderAt L 1 = 0 :=
    ha.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr h₁
  have heq : (fun s ↦ logDeriv L s - (meromorphicOrderAt L 1).untop₀ / (s - 1)) =ᶠ[𝓝[≠] 1]
      logDeriv L := by
    simp [hord]
  have hlog : AnalyticAt ℂ (logDeriv L) 1 := ha.logDeriv h₁
  have h := (hL.rieszRemainderMellin_eventuallyEq_dslope hlog heq).eq_of_nhds
  simpa [hord, dslope_same] using h

/-- Where `L` is analytic and nonzero on `1 < re s`, the Mellin expression is the canonical
meromorphic continuation of the defining quotient from that half-plane. -/
theorem _root_.Meromorphic.meromorphicContinuation_eq_rieszRemainderMellin {L : ℂ → ℂ}
    (hL : Meromorphic L) (ha : AnalyticOnNhd ℂ L {s | 1 < s.re})
    (hne : ∀ s : ℂ, 1 < s.re → L s ≠ 0) :
    meromorphicContinuation 1 (fun s ↦
      (s * logDerivFinitePart L 1 - (meromorphicOrderAt L 1).untop₀ * (s - 1) -
        (logDeriv L s - (meromorphicOrderAt L 1).untop₀ / (s - 1))) / (s * (s - 1))) =
      rieszRemainderMellin L := by
  refine meromorphicContinuation_eq (meromorphicNFOn_rieszRemainderMellin L) fun s hs ↦ ?_
  have hs' : 1 < s.re := hs
  have hs₀ : s ≠ 0 := by rintro rfl; norm_num at hs'
  have hs₁ : s ≠ 1 := by rintro rfl; simp at hs'
  exact (hL.rieszRemainderMellin_eq_and_analyticAt hs₀ hs₁ (ha s hs) (hne s hs')).1

/-- Away from `0` and `1`, multiplying the Mellin germ by `s - z` gives an analytic numerator
whose value at `z` is the order of `L` divided by `z * (1 - z)`. -/
theorem _root_.Meromorphic.exists_analyticAt_mul_rieszRemainderMellin {L : ℂ → ℂ}
    (hL : Meromorphic L) {z : ℂ} (hz₀ : z ≠ 0) (hz₁ : z ≠ 1) {n : ℤ}
    (hn : meromorphicOrderAt L z = n) :
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
  · filter_upwards [hL.rieszRemainderMellin_eventuallyEq z, heq, self_mem_nhdsWithin]
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
theorem _root_.Meromorphic.rieszRemainderMellin_simplePole {L : ℂ → ℂ}
    (hL : Meromorphic L) {z : ℂ} (hz₀ : z ≠ 0) (hz₁ : z ≠ 1) {n : ℤ}
    (hn : meromorphicOrderAt L z = n) (hne : n ≠ 0) :
    meromorphicOrderAt (rieszRemainderMellin L) z = -1 ∧
      meromorphicTrailingCoeffAt (rieszRemainderMellin L) z = (n : ℂ) / (z * (1 - z)) := by
  obtain ⟨H, ha, hval, heq⟩ := hL.exists_analyticAt_mul_rieszRemainderMellin hz₀ hz₁ hn
  have hH : H z ≠ 0 := by
    rw [hval]
    exact div_ne_zero (Int.cast_ne_zero.mpr hne) (mul_ne_zero hz₀ (sub_ne_zero.mpr hz₁.symm))
  have hrepr : rieszRemainderMellin L =ᶠ[𝓝[≠] z] fun s ↦ (s - z) ^ (-1 : ℤ) • H s := by
    filter_upwards [heq, self_mem_nhdsWithin] with s hs hsz
    rw [zpow_neg_one, smul_eq_mul, ← hs, inv_mul_cancel_left₀ (sub_ne_zero.mpr hsz)]
  have hm := (meromorphicNFOn_rieszRemainderMellin L (mem_univ z)).meromorphicAt
  refine ⟨?_, (ha.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE hH hrepr).trans hval⟩
  exact (meromorphicOrderAt_eq_int_iff hm).mpr ⟨H, ha, hH, hrepr⟩

/-- Away from `0` and `1`, the Mellin expression has a pole exactly where the input has
nonzero order, provided the order of the input is finite. In particular a regular nonvanishing
germ does not produce a pole, even if the totalized input is not in normal form. -/
theorem _root_.Meromorphic.meromorphicOrderAt_rieszRemainderMellin_neg_iff {L : ℂ → ℂ}
    (hL : Meromorphic L) {z : ℂ} (hz₀ : z ≠ 0) (hz₁ : z ≠ 1)
    (hfin : meromorphicOrderAt L z ≠ ⊤) :
    meromorphicOrderAt (rieszRemainderMellin L) z < 0 ↔ meromorphicOrderAt L z ≠ 0 := by
  lift meromorphicOrderAt L z to ℤ using hfin with n hn
  rcases eq_or_ne n 0 with rfl | hne
  · suffices 0 ≤ meromorphicOrderAt (rieszRemainderMellin L) z by simp [not_lt.mpr this]
    obtain ⟨H, hH, hz, heq⟩ := hL.exists_analyticAt_mul_rieszRemainderMellin hz₀ hz₁ hn.symm
    have hord := hH.meromorphicOrderAt_pos_iff_eq_zero.mpr (by simpa using hz)
    have hlin : MeromorphicAt (fun s : ℂ ↦ s - z) z :=
      (analyticAt_id.sub analyticAt_const).meromorphicAt
    have hmul := meromorphicOrderAt_mul hlin
      (meromorphicNFOn_rieszRemainderMellin L (mem_univ z)).meromorphicAt
    simp only [Pi.mul_def, meromorphicOrderAt_id_sub_const] at hmul
    rw [← meromorphicOrderAt_congr heq, hmul] at hord
    by_contra! hneg
    lift meromorphicOrderAt (rieszRemainderMellin L) z to ℤ using (hneg.trans_le le_top).ne with m
    norm_cast at hord hneg
    omega
  · have hneg : (-1 : WithTop ℤ) < 0 := by decide
    simp [(hL.rieszRemainderMellin_simplePole hz₀ hz₁ hn.symm hne).1, hne, hneg]

end TauCeti
