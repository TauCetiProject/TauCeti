/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Martingale.Centering
public import TauCeti.Probability.Martingale.ClassD
public import TauCeti.Probability.Process.Filtration.Comp
import TauCeti.MeasureTheory.Function.UniformIntegrable
import TauCeti.MeasureTheory.Integral.Bochner.Basic
import TauCeti.Probability.Martingale.Basic
import TauCeti.Probability.Martingale.DoobMeyer.Discrete

/-!
# Uniform integrability of discrete compensators of class DL submartingales

Sample a submartingale `X` along finite grids `g i 0 ≤ g i 1 ≤ ⋯ ≤ g i (N i) ≤ T` and take the
Doob compensator `A^i` of each sampled process for the sampled filtration. If `X` is of class DL,
the terminal values `A^i_{N i}` form a uniformly integrable family
(`TauCeti.IsClassDL.uniformIntegrable_predictablePart`), whatever the grids are.

This is the compactness step of the construction of the Doob–Meyer compensator: along dyadic
grids, a subsequence of convex combinations of these discrete compensators converges, and its
limit compensates `X`. The proof bounds each tail integral `∫_{c ≤ A_N} A_N` by increments of `X`
between grid stopping times and the grid end `g i (N i) ≤ T`
(`MeasureTheory.Submartingale.exists_setIntegral_predictablePart_le`), over events of probability
at most a multiple of `E[X_{g i (N i)} - X_{g i 0}] / c`. That expectation is bounded uniformly in
`i` because class DL bounds `E|X_t|` for `t ≤ T`, and class DL makes the increments uniformly small
on small events.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, proof of Theorem 1.4.10.
* M. Beiglböck, W. Schachermayer, B. Veliyev, *A short proof of the Doob–Meyer theorem*,
  Stochastic Process. Appl. 122 (2012), 1204–1209.
-/

public section

open Filter MeasureTheory Set
open scoped ENNReal

namespace TauCeti

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [Preorder ι] [Nonempty ι]
  {ℱ : Filtration ι mΩ} {X : ι → Ω → ℝ} {T : ι}

/-- On events of small probability, increments of a class DL process between a grid stopping time
and the end of the grid have small integrals. -/
private theorem setIntegral_sub_stoppedValue_le
    (hU : UniformIntegrable (fun τ : BoundedStoppingTime ℱ T ↦ stoppedValue X τ.val) 1 μ)
    (hX : ∀ t, Integrable (X t) μ) {δ : ℝ≥0∞} {ε' : ℝ} (hε' : 0 ≤ ε')
    (hδ : ∀ (τ : BoundedStoppingTime ℱ T) (s : Set Ω), μ s ≤ δ →
      eLpNorm (stoppedValue X τ.val) 1 (μ.restrict s) ≤ .ofReal ε')
    {g : ℕ → ι} (hg : Monotone g) {N : ℕ} (hgN : g N ≤ T)
    {σ : Ω → WithTop ℕ} (hσ : IsStoppingTime (ℱ.comp hg) σ) (hσN : ∀ ω, σ ω ≤ N)
    (hs : μ {ω | σ ω < N} ≤ δ) :
    ∫ ω in {ω | σ ω < N}, (X (g N) ω - stoppedValue (fun k ↦ X (g k)) σ ω) ∂μ ≤ 2 * ε' := by
  set τ := BoundedStoppingTime.ofComp hg hgN hσ hσN
  have hδN := hδ (BoundedStoppingTime.const hgN) _ hs
  rw [BoundedStoppingTime.stoppedValue_const] at hδN
  have hN := MeasureTheory.norm_integral_le_of_eLpNorm_one_le hε' hδN
  have hτ := MeasureTheory.norm_integral_le_of_eLpNorm_one_le hε' (hδ τ _ hs)
  rw [Real.norm_eq_abs] at hN hτ
  rw [← BoundedStoppingTime.stoppedValue_ofComp hg hgN hσ hσN, integral_sub (hX (g N)).integrableOn
    (memLp_one_iff_integrable.1 (hU.memLp τ)).integrableOn]
  linarith [le_abs_self (∫ ω in {ω | σ ω < N}, X (g N) ω ∂μ),
    neg_abs_le (∫ ω in {ω | σ ω < N}, stoppedValue X τ.val ω ∂μ)]

/-- **Uniform integrability of discrete compensators.** Sample a submartingale `X` of class DL
along grids `g i` with `g i (N i) ≤ T`. The compensators of the sampled processes, for the
sampled filtrations, are uniformly integrable at the ends `N i` of the grids. -/
theorem IsClassDL.uniformIntegrable_predictablePart [IsFiniteMeasure μ]
    (hD : IsClassDL X ℱ μ) (hX : Submartingale X ℱ μ) (T : ι) {κ : Type*}
    {g : κ → ℕ → ι} (hg : ∀ i, Monotone (g i)) {N : κ → ℕ} (hgN : ∀ i, g i (N i) ≤ T) :
    UniformIntegrable
      (fun i ↦ predictablePart (fun k ↦ X (g i k)) (ℱ.comp (hg i)) μ (N i)) 1 μ := by
  have hU := hD.uniformIntegrable T
  have hXi (i : κ) : Submartingale (fun k ↦ X (g i k)) (ℱ.comp (hg i)) μ := hX.comp (hg i)
  -- A uniform bound `K` on the expectations of the values at bounded stopping times.
  set K := (⨆ τ : BoundedStoppingTime ℱ T, eLpNorm (stoppedValue X τ.val) 1 μ).toReal
  have hK0 : 0 ≤ K := ENNReal.toReal_nonneg
  have hK (t : ι) (ht : t ≤ T) : |∫ ω, X t ω ∂μ| ≤ K := by
    have h := MeasureTheory.norm_integral_le_of_eLpNorm_one_le (μ := μ) (f := X t) (ε := K)
      ENNReal.toReal_nonneg ?_
    · simpa using h
    rw [ENNReal.ofReal_toReal hU.iSup_eLpNorm_lt.ne,
      ← BoundedStoppingTime.stoppedValue_const (ℱ := ℱ) (X := X) ht]
    exact le_iSup (fun τ : BoundedStoppingTime ℱ T ↦ eLpNorm (stoppedValue X τ.val) 1 μ)
      (BoundedStoppingTime.const ht)
  refine uniformIntegrable_of_setIntegral_le
    (fun i ↦ integrable_predictablePart (hXi i).integrable _)
    (fun i ↦ (hXi i).predictablePart_nonneg.mono fun _ h ↦ h _) fun ε hε ↦ ?_
  obtain ⟨δ, hδ, hbound⟩ := unifIntegrable_iff.1 hU.unifIntegrable (ENNReal.ofReal (ε / 6))
    (ENNReal.ofReal_pos.2 (by positivity))
  -- Work with a finite positive threshold `d` below `δ`.
  set d := (min δ 1).toReal
  have hd : 0 < d := ENNReal.toReal_pos (lt_min hδ one_pos).ne' (min_lt_of_right_lt
    ENNReal.one_lt_top).ne
  have hdδ : ENNReal.ofReal d ≤ δ := by
    rw [ENNReal.ofReal_toReal (min_lt_of_right_lt ENNReal.one_lt_top).ne]
    exact min_le_left _ _
  refine ⟨4 * K / d + 1, fun i ↦ ?_⟩
  have hc : 0 < 4 * K / d + 1 := by positivity
  obtain ⟨σ, ρ, hσ, hρ, hσN, hρN, hmσ, hmρ, htail⟩ :=
    (hXi i).exists_setIntegral_predictablePart_le (N i) hc
  -- The expected increment of the grid process is at most `2 K`.
  have hinc : ∫ ω, (X (g i (N i)) ω - X (g i 0) ω) ∂μ ≤ 2 * K := by
    rw [integral_sub (hX.integrable _) (hX.integrable _)]
    linarith [le_abs_self (∫ ω, X (g i (N i)) ω ∂μ), neg_abs_le (∫ ω, X (g i 0) ω ∂μ),
      hK _ (hgN i), hK _ ((hg i (Nat.zero_le _)).trans (hgN i))]
  have hsmall {E : Set Ω} (hE : (4 * K / d + 1) * μ.real E ≤ 4 * K) : μ E ≤ δ := by
    refine le_trans ?_ hdδ
    rw [← ofReal_measureReal]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← mul_le_mul_iff_right₀ hc]
    refine hE.trans ?_
    rw [add_mul, div_mul_cancel₀ _ hd.ne']
    linarith
  have hσs := setIntegral_sub_stoppedValue_le hU hX.integrable (by positivity) hbound
    (hg i) (hgN i) hσ hσN (hsmall (by linarith))
  have hρs := setIntegral_sub_stoppedValue_le hU hX.integrable (by positivity) hbound
    (hg i) (hgN i) hρ hρN (hsmall (by linarith))
  linarith

end TauCeti
