/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Meromorphic.NormalForm
public import TauCeti.Analysis.Contour.Residue.Basic
public import TauCeti.NumberTheory.DirichletCharacter.LFunction.Entire
public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Remainder
import Mathlib.Analysis.Calculus.DSlope
import TauCeti.Analysis.Calculus.LogDeriv
import TauCeti.Analysis.Contour.Residue.Germ
import TauCeti.Analysis.Contour.Residue.SimplePole

/-!
# Poles of the one-sided prime remainder transform

For the signed mean of logarithmic derivatives `G_q`, the continued transform of the
normalized first Riesz remainder has germ `(G_q(z) / z - G_q(1)) / (z - 1)`. The point `1`
is removable. Away from `0` and `1`, the only possible poles are simple, and the residue
is the difference of the total untwisted and twisted zero multiplicities divided by
`φ(q) z (1 - z)`. Where the twists do not vanish, the untwisted zeros cannot cancel, and
the residue at a positive real pole is strictly positive. These are the pole and sign
conditions used in one-sided Landau arguments for the remainder.

The normalization and signed multiplicities follow `New.isPolar_primeRemainder` in
`New/Reduction/Zeros/PrimeError` of lsernau/grh-lean at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`.
-/

public section

open Complex Filter Set
open scoped Topology

namespace TauCeti.OneSidedBound

variable (d q : ℕ) [Fact d.Prime] [NeZero q]

local instance : NeZero (q * d) :=
  ⟨Nat.mul_ne_zero (NeZero.ne q) (Fact.out : d.Prime).ne_zero⟩

/-- The meromorphic normal form of `(G_q(z) / z - G_q(1)) / (z - 1)`, the expression for
    the continued Laplace transform of `v ↦ R_q(exp v)` at `z - 1`. -/
noncomputable def primeRemainderTransform : ℂ → ℂ :=
  toMeromorphicNFOn (fun z ↦ (logDerivMean d q z / z - logDerivMean d q 1) / (z - 1)) univ

/-- The continued transform is meromorphic in normal form. -/
theorem meromorphicNFOn_primeRemainderTransform :
    MeromorphicNFOn (primeRemainderTransform d q) univ :=
  meromorphicNFOn_toMeromorphicNFOn _ _

private theorem meromorphic_logDerivMean : Meromorphic (logDerivMean d q) := by
  simp_rw [funext (logDerivMean_def d q)]
  intro s
  refine ((MeromorphicAt.fun_sum (s := Finset.univ) fun ψ _ ↦ ?_).fun_sub
    (MeromorphicAt.const _ _)).fun_div (MeromorphicAt.const _ _)
  exact ((quadraticTwist d ψ).analyticAt_entireLFunction s).meromorphicAt.logDeriv.fun_sub
    (ψ.analyticAt_entireLFunction s).meromorphicAt.logDeriv

/-- The defining quotient represents the punctured germ of the continued transform. -/
theorem primeRemainderTransform_eventuallyEq (s : ℂ) :
    primeRemainderTransform d q =ᶠ[𝓝[≠] s]
      fun z ↦ (logDerivMean d q z / z - logDerivMean d q 1) / (z - 1) := by
  have h := meromorphic_logDerivMean d q
  have hq : Meromorphic (fun z ↦ (logDerivMean d q z / z - logDerivMean d q 1) / (z - 1)) := by
    fun_prop
  exact (meromorphicOn_univ.mpr hq).toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ s)

private theorem primeRemainderTransform_analyticGerm {s : ℂ} (hs : 1 ≤ s.re) :
    AnalyticAt ℂ (primeRemainderTransform d q) s ∧
      primeRemainderTransform d q =ᶠ[𝓝 s] dslope (fun z ↦ logDerivMean d q z / z) 1 := by
  have ha : AnalyticAt ℂ (fun z ↦ logDerivMean d q z / z) s := by
    simp_rw [logDerivMean_def d q]
    refine ((Finset.analyticAt_fun_sum Finset.univ fun ψ _ ↦ ?_).fun_sub analyticAt_const |>.fun_div
      analyticAt_const (Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (NeZero.pos q)).ne')).fun_div
      analyticAt_id (ne_zero_of_re_pos (zero_lt_one.trans_le hs))
    exact (((quadraticTwist d ψ).analyticAt_entireLFunction s).logDeriv
      ((quadraticTwist d ψ).entireLFunction_ne_zero_of_one_le_re hs)).fun_sub
      ((ψ.analyticAt_entireLFunction s).logDeriv (ψ.entireLFunction_ne_zero_of_one_le_re hs))
  have hd := ha.dslope 1
  have hnf := meromorphicNFOn_primeRemainderTransform d q (mem_univ s)
  have he := (hnf.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds hd.meromorphicNFAt).mp <|
    (primeRemainderTransform_eventuallyEq d q s).trans <| by
      have hne : ∀ᶠ z in 𝓝[≠] s, z ≠ (1 : ℂ) := by
        rcases eq_or_ne s 1 with rfl | h
        · exact self_mem_nhdsWithin
        · exact (eventually_ne_nhds h).filter_mono nhdsWithin_le_nhds
      filter_upwards [hne] with z hz
      rw [dslope_of_ne _ hz, slope_def_field, div_one]
  exact ⟨hd.congr he.symm, he⟩

/-- The continued transform is analytic on `Re s ≥ 1`; in particular `1` is removable. -/
theorem analyticAt_primeRemainderTransform_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) :
    AnalyticAt ℂ (primeRemainderTransform d q) s :=
  (primeRemainderTransform_analyticGerm d q hs).1

/-- On `Re s ≥ 1`, the transform is the divided difference of `G_q(z) / z` at `1`.
At `s = 1` this gives the derivative, not the junk value of the defining quotient. -/
theorem primeRemainderTransform_eq_dslope {s : ℂ} (hs : 1 ≤ s.re) :
    primeRemainderTransform d q s = dslope (fun z ↦ logDerivMean d q z / z) 1 s :=
  (primeRemainderTransform_analyticGerm d q hs).2.eq_of_nhds

/-- Multiplying out the polar factor leaves the signed sum of vanishing orders, divided
    by the first Riesz denominator and the number of characters. -/
private theorem tendsto_sub_mul_primeRemainderTransform {s : ℂ} (h₀ : s ≠ 0) :
    Tendsto (fun z ↦ (z - s) * primeRemainderTransform d q z) (𝓝[≠] s)
      (𝓝 ((∑ ψ : DirichletCharacter ℂ q, ((analyticOrderNatAt ψ.entireLFunction s : ℂ) -
        (analyticOrderNatAt (quadraticTwist d ψ).entireLFunction s : ℂ))) /
        ((Nat.totient q : ℂ) * s * (1 - s)))) := by
  have hz : Tendsto (fun z : ℂ ↦ z) (𝓝[≠] s) (𝓝 s) := nhdsWithin_le_nhds
  have hs : Tendsto (fun z ↦ z - s) (𝓝[≠] s) (𝓝 0) := by simpa using hz.sub_const s
  rcases eq_or_ne s 1 with rfl | h₁
  · have h := analyticAt_primeRemainderTransform_of_one_le_re d q (s := 1) (by simp)
    have ht : Tendsto (primeRemainderTransform d q) (𝓝[≠] 1)
        (𝓝 (primeRemainderTransform d q 1)) :=
      h.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    simpa using hs.mul ht
  have hsum := tendsto_finsetSum (Finset.univ : Finset (DirichletCharacter ℂ q)) fun ψ _ ↦
    ((quadraticTwist d ψ).tendsto_sub_mul_logDeriv_entireLFunction s).sub
      (ψ.tendsto_sub_mul_logDeriv_entireLFunction s)
  have hmean := (hsum.sub hs).div_const (Nat.totient q : ℂ)
  have hlim := ((hmean.div hz h₀).sub (hs.mul_const (logDerivMean d q 1))).div
    (hz.sub_const 1) (sub_ne_zero.mpr h₁)
  simp only [sub_zero, zero_mul, ← div_mul_eq_div_div] at hlim
  have hneg (a b : ℂ) : a / b = -a / -b := by rw [neg_div_neg_eq]
  rw [hneg _ (_ * (s - 1)), ← Finset.sum_neg_distrib, ← mul_neg, neg_sub] at hlim
  simp only [neg_sub] at hlim
  refine hlim.congr' ?_
  filter_upwards [primeRemainderTransform_eventuallyEq d q s] with z hz'
  rw [hz', logDerivMean_def d q z]
  simp only [← mul_div_assoc, mul_sub, Finset.mul_sum, mul_one]
  rfl

/-- Away from `0` the continued transform has at most a simple pole. -/
theorem neg_one_le_meromorphicOrderAt_primeRemainderTransform {s : ℂ} (h₀ : s ≠ 0) :
    -1 ≤ meromorphicOrderAt (primeRemainderTransform d q) s :=
  Contour.neg_one_le_meromorphicOrderAt_of_tendsto_sub_mul
    (tendsto_sub_mul_primeRemainderTransform d q h₀)

/-- The residue is the total untwisted vanishing order minus the total twisted vanishing
    order, scaled by `1 / (φ(q) s (1 - s))`. -/
theorem residue_primeRemainderTransform {s : ℂ} (h₀ : s ≠ 0) :
    Contour.residue (primeRemainderTransform d q) s =
      (∑ ψ : DirichletCharacter ℂ q, ((analyticOrderNatAt ψ.entireLFunction s : ℂ) -
        (analyticOrderNatAt (quadraticTwist d ψ).entireLFunction s : ℂ))) /
        ((Nat.totient q : ℂ) * s * (1 - s)) :=
  Contour.residue_eq_of_tendsto_sub_mul
    (meromorphicNFOn_primeRemainderTransform d q (mem_univ s)).meromorphicAt
    (tendsto_sub_mul_primeRemainderTransform d q h₀)

private theorem residue_eq_sum_order_of_twists_ne_zero {s : ℂ} (h₀ : s ≠ 0)
    (ht : ∀ ψ : DirichletCharacter ℂ q, (quadraticTwist d ψ).entireLFunction s ≠ 0) :
    Contour.residue (primeRemainderTransform d q) s =
      ((∑ ψ : DirichletCharacter ℂ q, analyticOrderNatAt ψ.entireLFunction s : ℕ) : ℂ) /
        ((Nat.totient q : ℂ) * s * (1 - s)) := by
  rw [residue_primeRemainderTransform d q h₀, Nat.cast_sum]
  refine congrArg (· / _) (Finset.sum_congr rfl fun ψ _ ↦ ?_)
  have hψ := not_not.mp (mt apply_eq_zero_of_analyticOrderNatAt_ne_zero (ht ψ))
  simp only [hψ, Nat.cast_zero, sub_zero]

/-- At a nonzero point where none of the twisted entire functions vanish, a pole of the
    continued transform detects a zero of an untwisted entire function, and conversely. -/
theorem meromorphicOrderAt_primeRemainderTransform_neg_iff {s : ℂ} (h₀ : s ≠ 0)
    (ht : ∀ ψ : DirichletCharacter ℂ q, (quadraticTwist d ψ).entireLFunction s ≠ 0) :
    meromorphicOrderAt (primeRemainderTransform d q) s < 0 ↔
      ∃ ψ : DirichletCharacter ℂ q, ψ.entireLFunction s = 0 := by
  rcases eq_or_ne s 1 with rfl | h₁
  · have h := analyticAt_primeRemainderTransform_of_one_le_re d q (s := 1) (by simp)
    exact iff_of_false (not_lt.mpr h.meromorphicOrderAt_nonneg) fun ⟨ψ, hψ⟩ ↦
      ψ.entireLFunction_ne_zero_of_one_le_re (by simp) hψ
  have hφ : (Nat.totient q : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  rw [Contour.meromorphicOrderAt_lt_zero_iff_residue_ne_zero
    (meromorphicNFOn_primeRemainderTransform d q (mem_univ s)).meromorphicAt
    (neg_one_le_meromorphicOrderAt_primeRemainderTransform d q h₀),
    residue_eq_sum_order_of_twists_ne_zero d q h₀ ht,
    div_ne_zero_iff, and_iff_left (mul_ne_zero (mul_ne_zero hφ h₀) (sub_ne_zero.mpr h₁.symm)),
    Nat.cast_ne_zero]
  simp only [ne_eq, Finset.sum_eq_zero_iff_of_nonneg (fun _ _ ↦ Nat.zero_le _), Finset.mem_univ,
    true_implies, not_forall]
  refine exists_congr fun ψ ↦ ?_
  rw [analyticOrderNatAt, ENat.toNat_eq_zero,
    or_iff_left (ψ.analyticOrderAt_entireLFunction_ne_top s),
    (ψ.analyticAt_entireLFunction s).analyticOrderAt_eq_zero, not_ne_iff]

/-- At a positive real pole where the twists are nonvanishing, the residue has strictly
    positive real part. -/
theorem re_residue_primeRemainderTransform_pos {σ : ℝ} (hσ : 0 < σ)
    (ht : ∀ ψ : DirichletCharacter ℂ q, (quadraticTwist d ψ).entireLFunction σ ≠ 0)
    (hp : meromorphicOrderAt (primeRemainderTransform d q) (σ : ℂ) < 0) :
    0 < (Contour.residue (primeRemainderTransform d q) σ).re := by
  have h₀ := Complex.ofReal_ne_zero.mpr hσ.ne'
  have h₁ : σ < 1 := by
    by_contra! h
    exact (analyticAt_primeRemainderTransform_of_one_le_re d q (s := σ)
      (by simpa using h)).meromorphicOrderAt_nonneg.not_gt hp
  have hr := (Contour.meromorphicOrderAt_lt_zero_iff_residue_ne_zero
    (meromorphicNFOn_primeRemainderTransform d q (mem_univ (σ : ℂ))).meromorphicAt
    (neg_one_le_meromorphicOrderAt_primeRemainderTransform d q h₀)).mp hp
  rw [residue_eq_sum_order_of_twists_ne_zero d q h₀ ht] at hr ⊢
  have hsum : 0 < ∑ ψ : DirichletCharacter ℂ q, analyticOrderNatAt ψ.entireLFunction σ :=
    Nat.pos_of_ne_zero (Nat.cast_ne_zero.mp (div_ne_zero_iff.mp hr).1)
  have hNum : (0 : ℝ) < ((∑ ψ : DirichletCharacter ℂ q,
    analyticOrderNatAt ψ.entireLFunction σ : ℕ) : ℝ) := Nat.cast_pos.mpr hsum
  have hDen : (0 : ℝ) < (q.totient : ℝ) * σ * (1 - σ) :=
    mul_pos (mul_pos (Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))) hσ) (sub_pos.mpr h₁)
  have heq := congrArg Complex.re (Complex.ofReal_div
    ((∑ ψ : DirichletCharacter ℂ q, analyticOrderNatAt ψ.entireLFunction σ : ℕ) : ℝ)
    ((q.totient : ℝ) * σ * (1 - σ)))
  simp only [Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_natCast,
    Complex.ofReal_re] at heq
  rw [← heq]
  exact div_pos hNum hDen

end TauCeti.OneSidedBound
