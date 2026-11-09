/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Basic
import TauCeti.Analysis.Convex.Exhaustion
import TauCeti.Analysis.Sobolev.Poincare.Potential
import TauCeti.Analysis.Sobolev.W1p.Restriction
import TauCeti.Analysis.Sobolev.Wkp.Local.Approximation
import TauCeti.Data.ENNReal.Inv
import TauCeti.MeasureTheory.Integral.Average
import TauCeti.MeasureTheory.Integral.RieszPotential
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.MeasureTheory.Measure.OpenPos

/-!
# The Sobolev–Poincaré inequality on a convex domain

Let `Ω` be a bounded convex open subset of a finite-dimensional real normed space `E` of
dimension `n`, let `μ` be an additive Haar measure with `ω = μ(B(0, 1))`, and let `S ⊆ Ω` have
positive measure. For `1 ≤ p ≤ q < ∞` with `δ = 1/p - 1/q < 1/n`, this file proves the
**Sobolev–Poincaré inequality**

`‖u - ⨍_S u‖_{L^q(Ω)} ≤ n⁻¹ ω ^ (1 - 1/n) ((1 - δ) / (1/n - δ)) ^ (1 - δ) (diam Ω) ^ n / μ(S)
  · μ(Ω) ^ (1/n - δ) ‖∇u‖_{Lᵖ(Ω)}`,

first for `C¹` functions on `Ω` and then for every `u ∈ W^{1,p}(Ω)`. Unlike the
Poincaré–Wirtinger inequality `TauCeti.W1p.eLpNorm_value_sub_setAverage_le_of_convex`, the
left-hand side is measured at an exponent `q` which may exceed `p`; every `q` below the critical
exponent `p⋆` (and every finite `q` when `p ≥ n`) is covered, but not the critical exponent
itself, where the constant `((1 - δ) / (1/n - δ)) ^ (1 - δ)` blows up. On a ball `B(x₀, R)`
with `S` the ball itself the constant is
`2 ^ n n⁻¹ ω ^ (-δ) ((1 - δ) / (1/n - δ)) ^ (1 - δ) R ^ (1 - n δ)`, where `R ^ (1 - n δ)` is
the power dictated by scaling.

This is the inequality that turns Caccioppoli's inequality for a weak solution into a reverse
Hölder inequality for its gradient: with `p < 2 = q` and `1/p - 1/2 < 1/n`, the oscillation of
`u` in `L²` is controlled by `‖∇u‖` in a strictly smaller exponent, in every dimension.

## The argument

For a `C¹` function the deviation `u x - ⨍_S u` is bounded pointwise by the Riesz potential
`(diam Ω) ^ n / (n μ(S)) ∫_Ω ‖Du y‖ ‖x - y‖ ^ (1 - n) dy`
(`TauCeti.enorm_sub_setAverage_le_of_convex`), and the Riesz potential of order one maps `Lᵖ(Ω)`
to `L^q(Ω)` with the factor `μ(Ω) ^ (1/n - δ)`
(`TauCeti.eLpNorm_setLIntegral_enorm_sub_rpow_mul_le`; Gilbarg–Trudinger, Lemmas 7.12 and 7.16).

A Sobolev function is approximated by test functions only on a convex subdomain `U` whose closure
is a compact subset of `Ω`. Convergence in `W^{1,p}(U)` controls the values only in `Lᵖ`, which
says nothing about their `L^q` norms when `q > p`, so the inequality is not shown to cut out a
closed set by continuity; it does so by lower semicontinuity
(`TauCeti.W1p.isClosed_setOf_eLpNorm_value_sub_setAverage_le`): convergence in `W^{1,p}(U)` gives
an almost everywhere convergent subsequence of the values, the means converge, and Fatou's lemma
`MeasureTheory.Lp.eLpNorm_lim_le_liminf_eLpNorm` passes the bound to the limit. The subdomains are
then increased to `Ω` along a convex exhaustion, and Fatou's lemma applies once more
(`TauCeti.eLpNorm_sub_setAverage_le_of_tendsto_of_monotone`), exactly as in the proof of the
Poincaré–Wirtinger inequality.

## Main declarations

* `TauCeti.eLpNorm_sub_setAverage_le_mul_measure_rpow_mul_eLpNorm_fderiv_of_convex`: the
  inequality for `C¹` functions on a bounded convex open set.
* `TauCeti.W1p.eLpNorm_value_sub_setAverage_le_mul_measure_rpow_mul_enorm_gradient_of_convex`:
  the inequality on `W^{1,p}(Ω)`.
* `TauCeti.W1p.eLpNorm_value_sub_setAverage_le_mul_rpow_mul_enorm_gradient_of_eq_ball`: the
  scale-invariant form on a ball, with constant a multiple of `R ^ (1 - n δ)`.
* `TauCeti.W1p.eLpNorm_value_sub_setAverage_le_mul_rpow_mul_eLpNorm_gradient_of_ball_subset`:
  the same bound for the restriction to a ball `B(x₀, R) ⊆ Ω` of `u ∈ W^{1,p}(Ω)`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Lemmas 7.12 and 7.16.
* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, Section 3.3.
-/

public section

noncomputable section

namespace TauCeti

open Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped Distributions ENNReal Gradient NNReal Topology

section ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {μ : Measure E} [μ.IsAddHaarMeasure] {u : E → F} {Ω S : Set E}

/-- **The Sobolev–Poincaré inequality on a convex domain**, for `C¹` functions. Let `n` be the
dimension and `ω = μ(B(0, 1))`, and let `1 ≤ p ≤ q < ∞` with `δ = 1/p - 1/q < 1/n`. If `u` is
`C¹` on a bounded convex open set `Ω` and `S ⊆ Ω` has positive measure, then

`‖u - ⨍_S u‖_{L^q(Ω)} ≤ n⁻¹ ω ^ (1 - 1/n) ((1 - δ) / (1/n - δ)) ^ (1 - δ) (diam Ω) ^ n / μ(S)
  · μ(Ω) ^ (1/n - δ) ‖Du‖_{Lᵖ(Ω)}`. -/
theorem eLpNorm_sub_setAverage_le_mul_measure_rpow_mul_eLpNorm_fderiv_of_convex
    (hΩ : IsOpen Ω) (hΩc : Convex ℝ Ω) (hb : Bornology.IsBounded Ω) (hu : ContDiffOn ℝ 1 u Ω)
    (hS : S ⊆ Ω) (hS₀ : μ S ≠ 0) {p q : ℝ≥0} (hp : 1 ≤ p) (hpq : p ≤ q) {δ : ℝ}
    (hδ : (p : ℝ)⁻¹ - (q : ℝ)⁻¹ = δ) (hδn : δ < (finrank ℝ E : ℝ)⁻¹) :
    eLpNorm (fun x => u x - ⨍ y in S, u y ∂μ) q (μ.restrict Ω) ≤
      ENNReal.ofReal ((finrank ℝ E : ℝ)⁻¹ * μ.real (ball 0 1) ^ (1 - (finrank ℝ E : ℝ)⁻¹) *
        ((1 - δ) / ((finrank ℝ E : ℝ)⁻¹ - δ)) ^ (1 - δ) * diam Ω ^ finrank ℝ E / μ.real S) *
        μ Ω ^ ((finrank ℝ E : ℝ)⁻¹ - δ) * eLpNorm (fderiv ℝ u) p (μ.restrict Ω) := by
  set n := finrank ℝ E
  set d := diam Ω
  set ω := μ.real (ball (0 : E) 1)
  have hS_top : μ S ≠ ∞ := ((measure_mono hS).trans_lt hb.measure_lt_top).ne
  -- The exponents force `0 ≤ δ < 1/n`, which is impossible in dimension zero.
  have hδ0 : 0 ≤ δ := by
    rw [← hδ, sub_nonneg]
    exact inv_anti₀ (by exact_mod_cast zero_lt_one.trans_le hp) (by exact_mod_cast hpq)
  rcases subsingleton_or_nontrivial E with hE | hE
  · simp only [n, finrank_zero_of_subsingleton, CharP.cast_eq_zero, inv_zero] at hδn
    linarith
  have hn : (1 : ℝ) ≤ n := Nat.one_le_cast.2 finrank_pos
  -- The Riesz potential of order one of `‖Du‖`, over `Ω`.
  set V : E → ℝ≥0∞ := fun x =>
    ∫⁻ y in Ω, ‖x - y‖ₑ ^ ((n : ℝ) * ((n : ℝ)⁻¹ - 1)) * ‖fderiv ℝ u y‖ₑ ∂μ
  -- The pointwise potential bound `‖u x - ⨍_S u‖ ≤ c V x`.
  set c : ℝ≥0∞ := ENNReal.ofReal (d ^ n / n) / μ S
  have hpoint : ∀ x ∈ Ω, ‖u x - ⨍ y in S, u y ∂μ‖ₑ ≤ c * ‖V x‖ₑ := fun x hx => by
    refine (enorm_sub_setAverage_le_of_convex hΩ hΩc hb hu hx hS hS₀).trans_eq ?_
    rw [enorm_eq_self]
    congr 1
    refine lintegral_congr fun y => ?_
    rw [mul_comm, show (n : ℝ) * ((n : ℝ)⁻¹ - 1) = 1 - n by field_simp]
  -- The `Lᵖ`-`L^q` bound for the potential, with `κ = 1/n`.
  have hcont := hu.continuousOn_fderiv_of_isOpen hΩ le_rfl
  have hpot := eLpNorm_setLIntegral_enorm_sub_rpow_mul_le (μ := μ) (p := p) (q := q)
    (κ := (n : ℝ)⁻¹) hp hpq hδ hδn (inv_le_one_of_one_le₀ hn) hΩ.measurableSet
    (hcont.enorm.aemeasurable hΩ.measurableSet)
  have hc : c = ENNReal.ofReal (d ^ n / n / μ.real S) := by
    have hSpos : 0 < μ.real S := ENNReal.toReal_pos hS₀ hS_top
    rw [ENNReal.ofReal_div_of_pos hSpos, ofReal_measureReal hS_top]
  calc eLpNorm (fun x => u x - ⨍ y in S, u y ∂μ) q (μ.restrict Ω)
      ≤ c * eLpNorm V q (μ.restrict Ω) :=
        eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' _
          ((hu.continuousOn.aestronglyMeasurable hΩ.measurableSet).sub aestronglyMeasurable_const)
          ((ae_restrict_iff' hΩ.measurableSet).2 (ae_of_all _ hpoint))
    _ ≤ c * (ENNReal.ofReal (((1 - δ) / ((n : ℝ)⁻¹ - δ)) ^ (1 - δ) * ω ^ (1 - (n : ℝ)⁻¹)) *
          μ Ω ^ ((n : ℝ)⁻¹ - δ) * eLpNorm (fun y => ‖fderiv ℝ u y‖ₑ) p (μ.restrict Ω)) :=
        mul_le_mul_right hpot c
    _ = _ := by
      rw [eLpNorm_enorm _ (hcont.aestronglyMeasurable hΩ.measurableSet), hc, ← mul_assoc,
        ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      congr 3
      ring

end ContDiff

section W1p

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega U : Opens E} {p : ℝ≥0∞} [Fact (1 ≤ p)] {S : Set E}

/-- **The Sobolev–Poincaré inequality for a limit of test functions.** It holds on a bounded
convex `U` for every Sobolev function on `U` that is a `W^{1,p}`-limit of restrictions of test
functions on a larger domain. -/
private theorem eLpNorm_value_sub_setAverage_le_mul_measure_rpow_mul_enorm_gradient_of_mem_closure
    (hp : p ≠ ∞) (hU : U ≤ Omega) (hUc : Convex ℝ (U : Set E))
    (hUb : Bornology.IsBounded (U : Set E)) (hSU : S ⊆ (U : Set E)) (hS0 : mu S ≠ 0)
    {q : ℝ≥0} (hpq : p ≤ q) {δ : ℝ} (hδ : p.toReal⁻¹ - (q : ℝ)⁻¹ = δ)
    (hδn : δ < (finrank ℝ E : ℝ)⁻¹) {v : W1p mu U p}
    (hv : v ∈ closure (Set.range fun (phi : 𝓓(Omega, ℝ)) ↦
      W1p.restrictL hU (W1p.ofTestFunctionₗ mu Omega p phi))) :
    eLpNorm (fun x ↦ W1p.value v x - ⨍ y in S, W1p.value v y ∂mu) q (mu.restrict U) ≤
      ENNReal.ofReal ((finrank ℝ E : ℝ)⁻¹ * mu.real (ball 0 1) ^ (1 - (finrank ℝ E : ℝ)⁻¹) *
        ((1 - δ) / ((finrank ℝ E : ℝ)⁻¹ - δ)) ^ (1 - δ) * diam (U : Set E) ^ finrank ℝ E /
          mu.real S) * mu U ^ ((finrank ℝ E : ℝ)⁻¹ - δ) * ‖W1p.gradient v‖ₑ := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hpp : ((p.toNNReal : ℝ≥0) : ℝ≥0∞) = p := ENNReal.coe_toNNReal hp
  have hUfin : mu (U : Set E) ≠ ∞ :=
    ((measure_mono subset_closure).trans_lt hUb.isCompact_closure.measure_lt_top).ne
  set C : ℝ≥0∞ := ENNReal.ofReal ((finrank ℝ E : ℝ)⁻¹ *
    mu.real (ball 0 1) ^ (1 - (finrank ℝ E : ℝ)⁻¹) *
    ((1 - δ) / ((finrank ℝ E : ℝ)⁻¹ - δ)) ^ (1 - δ) * diam (U : Set E) ^ finrank ℝ E /
      mu.real S) * mu U ^ ((finrank ℝ E : ℝ)⁻¹ - δ)
  have hC : C ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (sub_nonneg.2 hδn.le) hUfin)
  -- Every restricted test function satisfies the inequality, by the `C¹` inequality on `U`.
  have hrange : (Set.range fun (phi : 𝓓(Omega, ℝ)) ↦
      W1p.restrictL hU (W1p.ofTestFunctionₗ mu Omega p phi)) ⊆ {w : W1p mu U p |
        eLpNorm (fun x ↦ W1p.value w x - ⨍ y in S, W1p.value w y ∂mu) q (mu.restrict U) ≤
          C.toNNReal * ‖W1p.gradient w‖ₑ} := by
    rintro w ⟨phi, rfl⟩
    set w := W1p.restrictL hU (W1p.ofTestFunctionₗ mu Omega p phi)
    have haeU : W1p.value w =ᵐ[mu.restrict (U : Set E)] fun x ↦ phi x := by
      refine (W1p.value_restrictL_ae hU _).trans ?_
      rw [W1p.value_ofTestFunctionₗ]
      exact (testFunctionLp_apply_ae (mu := mu) p phi).filter_mono
        (ae_mono (Measure.restrict_mono (SetLike.coe_subset_coe.2 hU) le_rfl))
    have hgradU : W1p.gradient w =ᵐ[mu.restrict (U : Set E)] fun x ↦ ∇ (phi : E → ℝ) x := by
      refine (W1p.gradient_restrictL_ae hU _).trans ?_
      rw [W1p.gradient_ofTestFunctionₗ]
      exact (gradientTestFunctionLp_apply_ae (mu := mu) p phi).filter_mono
        (ae_mono (Measure.restrict_mono (SetLike.coe_subset_coe.2 hU) le_rfl))
    have havg : (⨍ y in S, W1p.value w y ∂mu) = ⨍ y in S, phi y ∂mu :=
      average_congr (haeU.filter_mono (ae_mono (Measure.restrict_mono hSU le_rfl)))
    have hmain := eLpNorm_sub_setAverage_le_mul_measure_rpow_mul_eLpNorm_fderiv_of_convex (μ := mu)
      (u := fun x ↦ (phi : E → ℝ) x) U.isOpen hUc hUb (phi.contDiff.of_le (by simp)).contDiffOn
      hSU hS0 (p := p.toNNReal) (by exact_mod_cast hpp ▸ hp1) (by exact_mod_cast hpp ▸ hpq)
      (by rwa [ENNReal.coe_toNNReal_eq_toReal]) hδn
    rw [hpp] at hmain
    simp only [Set.mem_ofPred_eq, ENNReal.coe_toNNReal hC]
    calc eLpNorm (fun x ↦ W1p.value w x - ⨍ y in S, W1p.value w y ∂mu) q (mu.restrict U)
        = eLpNorm (fun x ↦ (phi : E → ℝ) x - ⨍ y in S, (phi : E → ℝ) y ∂mu) q
            (mu.restrict U) := by
          rw [havg]
          exact eLpNorm_congr_ae (haeU.mono fun x hx ↦ by simp only [hx])
      _ ≤ C * eLpNorm (fderiv ℝ (phi : E → ℝ)) p (mu.restrict U) := hmain
      _ = C * eLpNorm (W1p.gradient w) p (mu.restrict U) := by
          congr 1
          refine eLpNorm_congr_norm_ae
            (phi.contDiff.continuous_fderiv (by simp)).aestronglyMeasurable
            (Lp.aestronglyMeasurable _) ?_
          filter_upwards [hgradU] with x hx
          rw [hx, norm_gradient_eq_norm_fderiv]
      _ = C * ‖W1p.gradient w‖ₑ := by rw [Lp.enorm_def]
  have hv' := closure_minimal hrange
    (W1p.isClosed_setOf_eLpNorm_value_sub_setAverage_le hSU
      (ne_top_of_le_ne_top hUfin (measure_mono hSU)) q C.toNNReal) hv
  simpa only [Set.mem_ofPred_eq, ENNReal.coe_toNNReal hC] using hv'

/-- **The Sobolev–Poincaré inequality on `W^{1,p}(Ω)`.** Let `Ω` be a bounded convex open set in
a finite-dimensional real inner product space of dimension `n`, let `ω = μ(B(0, 1))`, and let
`S ⊆ Ω` be null-measurable of positive measure. For `p ≤ q < ∞` with `δ = 1/p - 1/q < 1/n`,
every `u ∈ W^{1,p}(Ω)` satisfies

`‖u - ⨍_S u‖_{L^q(Ω)} ≤ n⁻¹ ω ^ (1 - 1/n) ((1 - δ) / (1/n - δ)) ^ (1 - δ) (diam Ω) ^ n / μ(S)
  · μ(Ω) ^ (1/n - δ) ‖∇u‖_{Lᵖ(Ω)}`. -/
theorem W1p.eLpNorm_value_sub_setAverage_le_mul_measure_rpow_mul_enorm_gradient_of_convex
    (hp : p ≠ ∞) (hconv : Convex ℝ (Omega : Set E)) (hb : Bornology.IsBounded (Omega : Set E))
    (hSm : NullMeasurableSet S mu) (hS : S ⊆ (Omega : Set E)) (hS0 : mu S ≠ 0) {q : ℝ≥0}
    (hpq : p ≤ q) {δ : ℝ} (hδ : p.toReal⁻¹ - (q : ℝ)⁻¹ = δ) (hδn : δ < (finrank ℝ E : ℝ)⁻¹)
    (u : W1p mu Omega p) :
    eLpNorm (fun x ↦ W1p.value u x - ⨍ y in S, W1p.value u y ∂mu) q (mu.restrict Omega) ≤
      ENNReal.ofReal ((finrank ℝ E : ℝ)⁻¹ * mu.real (ball 0 1) ^ (1 - (finrank ℝ E : ℝ)⁻¹) *
        ((1 - δ) / ((finrank ℝ E : ℝ)⁻¹ - δ)) ^ (1 - δ) * diam (Omega : Set E) ^ finrank ℝ E /
          mu.real S) * mu Omega ^ ((finrank ℝ E : ℝ)⁻¹ - δ) * ‖W1p.gradient u‖ₑ := by
  obtain ⟨V, hVmono, hVopen, hVconv, hVcompact, -, hVclosure, hVunion⟩ :=
    exists_seq_isOpen_convex_isCompact_closure_subset_iUnion_eq Omega.isOpen hconv
  have hVsub : ∀ n, V n ⊆ (Omega : Set E) := fun n ↦ subset_closure.trans (hVclosure n)
  have hWle : ∀ n, (⟨V n, hVopen n⟩ : Opens E) ≤ Omega := fun n ↦
    SetLike.coe_subset_coe.mp (hVsub n)
  have hOfin : mu (Omega : Set E) ≠ ∞ :=
    ((measure_mono subset_closure).trans_lt hb.isCompact_closure.measure_lt_top).ne
  have hSfin : mu S ≠ ∞ := ne_top_of_le_ne_top hOfin (measure_mono hS)
  have hSRpos : 0 < mu.real S := ENNReal.toReal_pos hS0 hSfin
  have hSR0 : mu.real S ≠ 0 := hSRpos.ne'
  have he : 0 ≤ (finrank ℝ E : ℝ)⁻¹ - δ := sub_nonneg.2 hδn.le
  have hSV : S ⊆ ⋃ n, V n := hVunion ▸ hS
  have hmeasR : Tendsto (fun n ↦ mu.real (S ∩ V n)) atTop (𝓝 (mu.real S)) :=
    tendsto_measureReal_inter_of_monotone hVmono hSV hSfin
  have hint : IntegrableOn (W1p.value u) S mu := by
    have : IsFiniteMeasure (mu.restrict S) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hSfin.lt_top⟩
    exact ((Lp.memLp (W1p.value u)).mono_measure
      (Measure.restrict_mono hS le_rfl)).integrable Fact.out
  -- The inequality on each piece, with the diameter and measure of the whole domain.
  set A : ℝ := (finrank ℝ E : ℝ)⁻¹ * mu.real (ball 0 1) ^ (1 - (finrank ℝ E : ℝ)⁻¹) *
    ((1 - δ) / ((finrank ℝ E : ℝ)⁻¹ - δ)) ^ (1 - δ) with hAdef
  have hA : 0 ≤ A := by
    have h1δ : 0 ≤ 1 - δ := by
      linarith [(ENNReal.nonneg_and_le_one_of_inv_sub_inv_eq Fact.out hpq hδ).2]
    rw [hAdef]
    exact mul_nonneg (by positivity) (Real.rpow_nonneg (div_nonneg h1δ he) _)
  set K : ℝ≥0∞ := mu Omega ^ ((finrank ℝ E : ℝ)⁻¹ - δ)
  have hpiece : ∀ n, mu (S ∩ V n) ≠ 0 →
      eLpNorm (fun x ↦ W1p.value u x - ⨍ y in S ∩ V n, W1p.value u y ∂mu) q
          (mu.restrict (V n)) ≤
        ENNReal.ofReal (A * diam (Omega : Set E) ^ finrank ℝ E / mu.real (S ∩ V n)) * K *
          ‖W1p.gradient u‖ₑ := by
    intro n hn
    set W : Opens E := ⟨V n, hVopen n⟩
    set v : W1p mu W p := W1p.restrictL (hWle n) u
    have hval : W1p.value v =ᵐ[mu.restrict (V n)] W1p.value u := W1p.value_restrictL_ae _ u
    have hgrad : W1p.gradient v =ᵐ[mu.restrict (V n)] W1p.gradient u :=
      W1p.gradient_restrictL_ae _ u
    have havg : (⨍ y in S ∩ V n, W1p.value v y ∂mu) = ⨍ y in S ∩ V n, W1p.value u y ∂mu :=
      average_congr (hval.filter_mono
        (ae_mono (Measure.restrict_mono inter_subset_right le_rfl)))
    have hbase := eLpNorm_value_sub_setAverage_le_mul_measure_rpow_mul_enorm_gradient_of_mem_closure
      (S := S ∩ V n) (v := v) hp (hWle n) (hVconv n) (hb.subset (hVsub n)) inter_subset_right hn
      hpq hδ hδn
      (W1p.restrictL_mem_closure_range_ofTestFunctionₗ (U := W) hp (hVcompact n) (hVclosure n) u)
    rw [havg] at hbase
    have hpos : 0 < mu.real (S ∩ V n) :=
      ENNReal.toReal_pos hn (ne_top_of_le_ne_top hSfin (measure_mono inter_subset_left))
    have hcongr : eLpNorm (fun x ↦ W1p.value v x - ⨍ y in S ∩ V n, W1p.value u y ∂mu) q
          (mu.restrict (V n)) =
        eLpNorm (fun x ↦ W1p.value u x - ⨍ y in S ∩ V n, W1p.value u y ∂mu) q
          (mu.restrict (V n)) := by
      refine eLpNorm_congr_ae ?_
      filter_upwards [hval] with x hx
      exact congrArg (· - ⨍ y in S ∩ V n, W1p.value u y ∂mu) hx
    have hconst : A * diam (V n) ^ finrank ℝ E / mu.real (S ∩ V n) ≤
        A * diam (Omega : Set E) ^ finrank ℝ E / mu.real (S ∩ V n) := by
      gcongr
      exact Metric.diam_mono (hVsub n) hb
    have hmeas : mu (W : Set E) ^ ((finrank ℝ E : ℝ)⁻¹ - δ) ≤ K :=
      ENNReal.rpow_le_rpow (measure_mono (hVsub n)) he
    have hgradle : ‖W1p.gradient v‖ₑ ≤ ‖W1p.gradient u‖ₑ :=
      calc ‖W1p.gradient v‖ₑ
          = eLpNorm (W1p.gradient u) p (mu.restrict (V n)) := by
            rw [Lp.enorm_def]
            exact eLpNorm_congr_ae hgrad
        _ ≤ eLpNorm (W1p.gradient u) p (mu.restrict (Omega : Set E)) :=
            eLpNorm_mono_measure _ (Measure.restrict_mono (hVsub n) le_rfl)
        _ = ‖W1p.gradient u‖ₑ := (Lp.enorm_def _).symm
    exact hcongr ▸ hbase.trans
      (mul_le_mul' (mul_le_mul' (ENNReal.ofReal_le_ofReal hconst) hmeas) hgradle)
  -- Fatou along the exhaustion.
  have htend : Tendsto (fun n ↦ ENNReal.ofReal
        (A * diam (Omega : Set E) ^ finrank ℝ E / mu.real (S ∩ V n)) * K * ‖W1p.gradient u‖ₑ)
      atTop (𝓝 (ENNReal.ofReal (A * diam (Omega : Set E) ^ finrank ℝ E / mu.real S) * K *
        ‖W1p.gradient u‖ₑ)) :=
    ENNReal.Tendsto.mul_const (ENNReal.Tendsto.mul_const
      (ENNReal.tendsto_ofReal (tendsto_const_nhds.div hmeasR hSR0))
      (Or.inr (ENNReal.rpow_ne_top_of_nonneg he hOfin))) (Or.inr (by simp))
  refine eLpNorm_sub_setAverage_le_of_tendsto_of_monotone hVmono
    (fun n ↦ (hVopen n).measurableSet) hVunion hSm hS hSfin (Lp.aestronglyMeasurable _) hint
    htend ?_
  filter_upwards [hmeasR.eventually (lt_mem_nhds hSRpos)] with n hn
  refine hpiece n fun h0 ↦ ?_
  rw [measureReal_def, h0] at hn
  simp at hn

/-- **The Sobolev–Poincaré inequality on a ball.** Let `n ≥ 1` be the dimension and
`ω = μ(B(0, 1))`, and let `p ≤ q < ∞` with `δ = 1/p - 1/q < 1/n`. Every `u ∈ W^{1,p}(B(c, R))`
satisfies

`‖u - ⨍_{B(c, R)} u‖_{L^q} ≤ 2 ^ n n⁻¹ ω ^ (-δ) ((1 - δ) / (1/n - δ)) ^ (1 - δ) R ^ (1 - n δ)
  ‖∇u‖_{Lᵖ}`.

The power `R ^ (1 - n δ)` is the one dictated by scaling, so the remaining constant depends only
on `n`, `δ` and the normalization of `μ`. -/
theorem W1p.eLpNorm_value_sub_setAverage_le_mul_rpow_mul_enorm_gradient_of_eq_ball (hp : p ≠ ∞)
    {c : E} {R : ℝ} (hR : 0 < R) (hOmega : (Omega : Set E) = ball c R) {q : ℝ≥0} (hpq : p ≤ q)
    {δ : ℝ} (hδ : p.toReal⁻¹ - (q : ℝ)⁻¹ = δ) (hδn : δ < (finrank ℝ E : ℝ)⁻¹)
    (u : W1p mu Omega p) :
    eLpNorm (fun x ↦ W1p.value u x - ⨍ y in (Omega : Set E), W1p.value u y ∂mu) q
        (mu.restrict Omega) ≤
      ENNReal.ofReal (2 ^ finrank ℝ E * (finrank ℝ E : ℝ)⁻¹ * mu.real (ball 0 1) ^ (-δ) *
        ((1 - δ) / ((finrank ℝ E : ℝ)⁻¹ - δ)) ^ (1 - δ) * R ^ (1 - finrank ℝ E * δ)) *
        ‖W1p.gradient u‖ₑ := by
  set n := finrank ℝ E
  set ω := mu.real (ball (0 : E) 1)
  have hω : 0 < ω := Metric.measureReal_ball_pos mu 0 one_pos
  have he : 0 ≤ (n : ℝ)⁻¹ - δ := sub_nonneg.2 hδn.le
  obtain ⟨hδ0, hδ1⟩ := ENNReal.nonneg_and_le_one_of_inv_sub_inv_eq Fact.out hpq hδ
  have h1δ : 0 ≤ 1 - δ := by linarith
  have hn : (n : ℝ) ≠ 0 := fun h ↦ by
    rw [h, inv_zero] at hδn
    linarith
  have hcδ : 0 ≤ ((1 - δ) / ((n : ℝ)⁻¹ - δ)) ^ (1 - δ) := Real.rpow_nonneg (div_nonneg h1δ he) _
  have hBreal : mu.real (ball c R) = R ^ n * ω := mu.addHaar_real_ball_of_pos c hR
  have hB : mu (Omega : Set E) = ENNReal.ofReal (R ^ n * ω) := by
    rw [hOmega, ← ofReal_measureReal measure_ball_lt_top.ne, hBreal]
  have hpos : mu (Omega : Set E) ≠ 0 := by
    rw [hOmega]
    exact (measure_ball_pos mu c hR).ne'
  refine (W1p.eLpNorm_value_sub_setAverage_le_mul_measure_rpow_mul_enorm_gradient_of_convex hp
    (hOmega ▸ convex_ball c R) (hOmega ▸ Metric.isBounded_ball (x := c) (r := R))
    Omega.isOpen.measurableSet.nullMeasurableSet subset_rfl hpos hpq hδ hδn u).trans
    (mul_le_mul' ?_ le_rfl)
  rw [hB, ENNReal.ofReal_rpow_of_nonneg (by positivity) he, ← ENNReal.ofReal_mul (by
    rw [hOmega, hBreal]; positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [hOmega, hBreal]
  -- `diam B(c, R) ≤ 2R`, and `ω ^ (1 - 1/n) (Rⁿ ω) ^ (1/n - δ) / (Rⁿ ω) = ω ^ (-δ) R ^ (-n δ)`.
  calc (n : ℝ)⁻¹ * ω ^ (1 - (n : ℝ)⁻¹) * ((1 - δ) / ((n : ℝ)⁻¹ - δ)) ^ (1 - δ) *
        diam (ball c R) ^ n / (R ^ n * ω) * (R ^ n * ω) ^ ((n : ℝ)⁻¹ - δ)
      ≤ (n : ℝ)⁻¹ * ω ^ (1 - (n : ℝ)⁻¹) * ((1 - δ) / ((n : ℝ)⁻¹ - δ)) ^ (1 - δ) *
        (2 * R) ^ n / (R ^ n * ω) * (R ^ n * ω) ^ ((n : ℝ)⁻¹ - δ) := by
        gcongr
        exact diam_ball hR.le
    _ = _ := by
        have hR1 : (R ^ n) ^ ((n : ℝ)⁻¹ - δ) = R ^ (1 - n * δ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hR.le]
          congr 1
          field_simp
        have hω' : ω ^ (1 - (n : ℝ)⁻¹) * ω ^ ((n : ℝ)⁻¹ - δ) = ω * ω ^ (-δ) := by
          rw [← Real.rpow_add hω, show 1 - (n : ℝ)⁻¹ + ((n : ℝ)⁻¹ - δ) = 1 + -δ by ring,
            Real.rpow_add hω, Real.rpow_one]
        have hR0 : R ≠ 0 := hR.ne'
        have hω0 : ω ≠ 0 := hω.ne'
        rw [Real.mul_rpow (by positivity) hω.le, hR1, mul_pow]
        calc _ = (n : ℝ)⁻¹ * ((1 - δ) / ((n : ℝ)⁻¹ - δ)) ^ (1 - δ) * 2 ^ n * R ^ (1 - n * δ) *
              (ω ^ (1 - (n : ℝ)⁻¹) * ω ^ ((n : ℝ)⁻¹ - δ)) * (R ^ n / (R ^ n * ω)) := by ring
          _ = _ := by
            rw [hω']
            field_simp

/-- **The Sobolev–Poincaré inequality on a ball inside the domain.** If `u ∈ W^{1,p}(Ω)` and
`B(c, R) ⊆ Ω`, then for `p ≤ q < ∞` with `δ = 1/p - 1/q < 1/n`,

`‖u - ⨍_{B(c, R)} u‖_{L^q(B(c, R))} ≤
  2 ^ n n⁻¹ ω ^ (-δ) ((1 - δ) / (1/n - δ)) ^ (1 - δ) R ^ (1 - n δ) ‖∇u‖_{Lᵖ(B(c, R))}`.

This is `TauCeti.W1p.eLpNorm_value_sub_setAverage_le_mul_rpow_mul_enorm_gradient_of_eq_ball` for
the restriction of `u` to the ball. -/
theorem W1p.eLpNorm_value_sub_setAverage_le_mul_rpow_mul_eLpNorm_gradient_of_ball_subset
    (hp : p ≠ ∞) {c : E} {R : ℝ} (hR : 0 < R) (hball : ball c R ⊆ (Omega : Set E)) {q : ℝ≥0}
    (hpq : p ≤ q) {δ : ℝ} (hδ : p.toReal⁻¹ - (q : ℝ)⁻¹ = δ) (hδn : δ < (finrank ℝ E : ℝ)⁻¹)
    (u : W1p mu Omega p) :
    eLpNorm (fun x ↦ W1p.value u x - ⨍ y in ball c R, W1p.value u y ∂mu) q
        (mu.restrict (ball c R)) ≤
      ENNReal.ofReal (2 ^ finrank ℝ E * (finrank ℝ E : ℝ)⁻¹ * mu.real (ball 0 1) ^ (-δ) *
        ((1 - δ) / ((finrank ℝ E : ℝ)⁻¹ - δ)) ^ (1 - δ) * R ^ (1 - finrank ℝ E * δ)) *
        eLpNorm (W1p.gradient u) p (mu.restrict (ball c R)) := by
  set B : Opens E := ⟨ball c R, isOpen_ball⟩
  have hB : B ≤ Omega := hball
  set uB := W1p.restrictL hB u
  have hval : W1p.value uB =ᵐ[mu.restrict (ball c R)] W1p.value u := W1p.value_restrictL_ae hB u
  have hgrad : W1p.gradient uB =ᵐ[mu.restrict (ball c R)] W1p.gradient u :=
    W1p.gradient_restrictL_ae hB u
  have hP := W1p.eLpNorm_value_sub_setAverage_le_mul_rpow_mul_enorm_gradient_of_eq_ball hp hR
    (rfl : (B : Set E) = ball c R) hpq hδ hδn uB
  have havg : ⨍ y in (B : Set E), W1p.value uB y ∂mu = ⨍ y in ball c R, W1p.value u y ∂mu :=
    average_congr hval
  have hg : eLpNorm (W1p.gradient uB) p (mu.restrict (B : Set E)) =
      eLpNorm (W1p.gradient u) p (mu.restrict (ball c R)) := eLpNorm_congr_ae hgrad
  rw [havg, Lp.enorm_def, hg] at hP
  refine le_of_eq_of_le (eLpNorm_congr_ae ?_) hP
  filter_upwards [hval] with x hx
  rw [hx]

end W1p

end TauCeti
