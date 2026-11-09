/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Basic
import TauCeti.Analysis.Sobolev.Poincare.Potential
import TauCeti.Analysis.Sobolev.W1p.Restriction
import TauCeti.Analysis.Sobolev.Wkp.MeyersSerrin
import TauCeti.MeasureTheory.Integral.Average
import TauCeti.MeasureTheory.Integral.RieszPotential
import TauCeti.MeasureTheory.Measure.OpenPos

/-!
# The Sobolev–Poincaré inequality on convex domains

Let `Ω` be a bounded convex open subset of a finite-dimensional real inner product space `E` of
dimension `n ≥ 1`, let `μ` be an additive Haar measure with `ω = μ(B(0, 1))`, and let `S ⊆ Ω`
have positive measure. For `1 ≤ p ≤ q < ∞` with `δ = 1/p - 1/q < 1/n`, this file proves the
**Sobolev–Poincaré inequality**

`‖u - ⨍_S u‖_{L^q(Ω)} ≤ (diam Ω)ⁿ / (n μ(S)) K ω ^ (1 - 1/n) μ(Ω) ^ (1/n - δ) ‖∇u‖_{Lᵖ(Ω)}`,

with `K = ((1 - δ) / (1/n - δ)) ^ (1 - δ)`, first for `C¹` functions and then for every
`u ∈ W^{1,p}(Ω)`. Unlike the Poincaré–Wirtinger inequality
`TauCeti.W1p.eLpNorm_value_sub_setAverage_le_of_convex`, the deviation from the mean is measured in
a strictly better space `L^q`, `q > p`, than the gradient. The range `δ < 1/n` excludes the
critical exponent `1/q = 1/p - 1/n`, but it is nonempty in every dimension. This matters where
no critical exponent below `∞` is available: for every `p` when `n = 1`, and for the endpoint
`p = 2` when `n = 2` (for `p < 2` the planar critical exponent `2p/(2 - p)` is finite).

On a ball `B` of radius `r`, and written with averages, the inequality reads

`(⨍_B |u - u_B| ^ q) ^ (1/q) ≤ C r (⨍_B ‖∇u‖ ^ p) ^ (1/p)`,

with `C = 2ⁿ / n · K` depending only on `n`, `p` and `q`: both sides scale in the same way under
dilations and the normalization of `μ` cancels. With `p < 2 = q` this is the inequality that
turns Caccioppoli's inequality for a weak solution of a divergence-form equation into a reverse
Hölder inequality for its gradient, the input of Gehring's lemma in Meyers' higher integrability
theorem.

The proof bounds the deviation `u x - ⨍_S u` pointwise by the Riesz potential of order one of
`‖Du‖` (`TauCeti.enorm_sub_setAverage_le_of_convex`, Gilbarg–Trudinger, Lemma 7.16), and bounds
that potential from `Lᵖ(Ω)` to `L^q(Ω)` (`TauCeti.eLpNorm_setLIntegral_enorm_sub_rpow_mul_le` with
`κ = 1/n`, Gilbarg–Trudinger, Lemma 7.12). The Sobolev functions satisfying the inequality form a
closed subset of `W^{1,p}(Ω)`, by Fatou's lemma along an almost everywhere convergent
subsequence, and it contains the functions smooth on `Ω`, which are dense by the Meyers–Serrin
theorem `TauCeti.Wkp.dense_contDiffOn_representatives`.

## Main declarations

* `TauCeti.eLpNorm_sub_setAverage_le_mul_measure_rpow_of_convex`: the inequality for functions
  that are `C¹` on `Ω`.
* `TauCeti.W1p.eLpNorm_value_sub_setAverage_le_mul_measure_rpow_of_convex`: the inequality on
  `W^{1,p}(Ω)`.
* `TauCeti.W1p.setLAverage_rpow_enorm_value_sub_setAverage_le_of_eq_ball`: the scale-invariant
  form on a ball, with averages.
* `TauCeti.W1p.setLAverage_rpow_enorm_value_sub_setAverage_le_of_ball_subset`: the same for a
  ball inside the domain of a Sobolev function of possibly higher integrability.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Lemmas 7.12 and 7.16, and equation (7.45).
-/

public section

noncomputable section

namespace TauCeti

open Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped ENNReal NNReal Topology

section ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] {μ : Measure E} [μ.IsAddHaarMeasure] {u : E → F} {Ω S : Set E}

/-- **The Sobolev–Poincaré inequality for `C¹` functions on a convex domain.** Let `n ≥ 1` be
the dimension and `ω = μ(B(0, 1))`, let `1 ≤ p ≤ q < ∞` with `δ = 1/p - 1/q < 1/n`, and let `u`
be `C¹` on a bounded convex open set `Ω`. For every `S ⊆ Ω` of positive measure,

`‖u - ⨍_S u‖_{L^q(Ω)} ≤ (diam Ω)ⁿ / n · K ω ^ (1 - 1/n) / μ(S) · μ(Ω) ^ (1/n - δ) ‖Du‖_{Lᵖ(Ω)}`,

where `K = ((1 - δ) / (1/n - δ)) ^ (1 - δ)`. -/
theorem eLpNorm_sub_setAverage_le_mul_measure_rpow_of_convex (hΩ : IsOpen Ω)
    (hΩc : Convex ℝ Ω) (hb : Bornology.IsBounded Ω) (hu : ContDiffOn ℝ 1 u Ω) (hS : S ⊆ Ω)
    (hS₀ : μ S ≠ 0) {p q : ℝ≥0} (hp : 1 ≤ p) (hpq : p ≤ q) {δ : ℝ}
    (hδ : (p : ℝ)⁻¹ - (q : ℝ)⁻¹ = δ) (hδn : δ < (finrank ℝ E : ℝ)⁻¹) :
    eLpNorm (fun x => u x - ⨍ y in S, u y ∂μ) q (μ.restrict Ω) ≤
      ENNReal.ofReal (diam Ω ^ finrank ℝ E / finrank ℝ E *
          (((1 - δ) / ((finrank ℝ E : ℝ)⁻¹ - δ)) ^ (1 - δ) *
            μ.real (ball 0 1) ^ (1 - (finrank ℝ E : ℝ)⁻¹))) / μ S *
        μ Ω ^ ((finrank ℝ E : ℝ)⁻¹ - δ) * eLpNorm (fderiv ℝ u) p (μ.restrict Ω) := by
  set n := finrank ℝ E
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast finrank_pos
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hcont : ContinuousOn (fderiv ℝ u) Ω := hu.continuousOn_fderiv_of_isOpen hΩ le_rfl
  have hDm : AEStronglyMeasurable (fderiv ℝ u) (μ.restrict Ω) :=
    hcont.aestronglyMeasurable hΩ.measurableSet
  -- The Riesz potential of order one of `‖Du‖`, over `Ω`.
  set V : E → ℝ≥0∞ := fun x =>
    ∫⁻ y in Ω, ‖x - y‖ₑ ^ ((n : ℝ) * ((n : ℝ)⁻¹ - 1)) * ‖fderiv ℝ u y‖ₑ ∂μ
  set c : ℝ≥0∞ := ENNReal.ofReal (diam Ω ^ n / n) / μ S
  -- The pointwise potential bound `‖u x - ⨍_S u‖ ≤ c V x` on `Ω`.
  have hpt : ∀ᵐ x ∂μ.restrict Ω, ‖u x - ⨍ y in S, u y ∂μ‖ₑ ≤ c * ‖V x‖ₑ := by
    filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
    refine (enorm_sub_setAverage_le_of_convex (μ := μ) hΩ hΩc hb hu hx hS hS₀).trans_eq ?_
    rw [enorm_eq_self]
    congr 1
    refine lintegral_congr fun y => ?_
    have hexp : (n : ℝ) * ((n : ℝ)⁻¹ - 1) = 1 - n := by field_simp
    rw [mul_comm, hexp]
  -- The `Lᵖ`-`L^q` bound for the potential, with `κ = 1/n`.
  have hpot := eLpNorm_setLIntegral_enorm_sub_rpow_mul_le (μ := μ) (p := p) (q := q)
    (κ := (n : ℝ)⁻¹) hp hpq hδ hδn (inv_le_one_of_one_le₀ hn) hΩ.measurableSet
    hDm.enorm
  rw [eLpNorm_enorm _ hDm] at hpot
  have hum : AEStronglyMeasurable (fun x => u x - ⨍ y in S, u y ∂μ) (μ.restrict Ω) :=
    (hu.continuousOn.aestronglyMeasurable hΩ.measurableSet).sub aestronglyMeasurable_const
  calc
    eLpNorm (fun x => u x - ⨍ y in S, u y ∂μ) q (μ.restrict Ω) ≤
        c * eLpNorm V q (μ.restrict Ω) :=
      eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' _ hum hpt
    _ ≤ c * (ENNReal.ofReal (((1 - δ) / ((n : ℝ)⁻¹ - δ)) ^ (1 - δ) *
          μ.real (ball 0 1) ^ (1 - (n : ℝ)⁻¹)) * μ Ω ^ ((n : ℝ)⁻¹ - δ) *
          eLpNorm (fderiv ℝ u) p (μ.restrict Ω)) := mul_le_mul_right hpot _
    _ = _ := by
      simp only [c, ENNReal.div_eq_inv_mul,
        ENNReal.ofReal_mul (div_nonneg (pow_nonneg diam_nonneg _) (Nat.cast_nonneg _))]
      ring

end ContDiff

section W1p

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ℝ≥0∞} [Fact (1 ≤ p)] {S : Set E}

omit [FiniteDimensional ℝ E] in
/-- The Sobolev functions whose deviation from their mean over `S` has `L^q` norm at most `C`
times the `Lᵖ` norm of their gradient form a **closed** subset of `W^{1,p}(Ω)`, for every
exponent `q` and every `S ⊆ Ω` of finite measure.

Continuity of the left-hand side on `W^{1,p}(Ω)` is not available in general, but it is lower
semicontinuous: convergence in `W^{1,p}(Ω)` gives an almost everywhere convergent subsequence of
values and convergent means, and Fatou's lemma applies. -/
theorem W1p.isClosed_setOf_eLpNorm_value_sub_setAverage_le (hS : S ⊆ (Omega : Set E))
    (hSfin : mu S ≠ ∞) (q : ℝ≥0∞) (C : ℝ≥0) :
    IsClosed {u : W1p mu Omega p |
      eLpNorm (fun x ↦ W1p.value u x - ⨍ y in S, W1p.value u y ∂mu) q (mu.restrict Omega) ≤
        C * ‖W1p.gradient u‖ₑ} := by
  refine IsSeqClosed.isClosed fun v u hv hvu => ?_
  have hvalue : Tendsto (fun k => W1p.value (v k)) atTop (𝓝 (W1p.value u)) := by
    simpa only [W1p.valueL_apply, Function.comp_def] using
      ((map_continuous (W1p.valueL (mu := mu) (Omega := Omega) (p := p))).tendsto u).comp hvu
  have hgradient : Tendsto (fun k => W1p.gradient (v k)) atTop (𝓝 (W1p.gradient u)) := by
    simpa only [W1p.gradientL_apply, Function.comp_def] using
      ((map_continuous (W1p.gradientL (mu := mu) (Omega := Omega) (p := p))).tendsto u).comp hvu
  have havg : Tendsto (fun k => ⨍ y in S, W1p.value (v k) y ∂mu) atTop
      (𝓝 (⨍ y in S, W1p.value u y ∂mu)) :=
    ((W1p.continuous_setAverage_value hS hSfin).tendsto u).comp hvu
  have hbound : Tendsto (fun k => (C : ℝ≥0∞) * ‖W1p.gradient (v k)‖ₑ) atTop
      (𝓝 ((C : ℝ≥0∞) * ‖W1p.gradient u‖ₑ)) :=
    ENNReal.Tendsto.const_mul ((continuous_enorm.tendsto _).comp hgradient)
      (Or.inr ENNReal.coe_ne_top)
  obtain ⟨ns, hns, hae⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hvalue).exists_seq_tendsto_ae
  calc eLpNorm (fun x ↦ W1p.value u x - ⨍ y in S, W1p.value u y ∂mu) q (mu.restrict Omega)
      ≤ atTop.liminf fun i => eLpNorm (fun x ↦ W1p.value (v (ns i)) x -
          ⨍ y in S, W1p.value (v (ns i)) y ∂mu) q (mu.restrict Omega) :=
        Lp.eLpNorm_lim_le_liminf_eLpNorm
          (fun _ => (Lp.aestronglyMeasurable _).sub aestronglyMeasurable_const) _
          ((Lp.aestronglyMeasurable _).sub aestronglyMeasurable_const)
          (hae.mono fun x hx => hx.sub (havg.comp hns.tendsto_atTop))
    _ ≤ atTop.liminf fun i => (C : ℝ≥0∞) * ‖W1p.gradient (v (ns i))‖ₑ :=
        liminf_le_liminf (.of_forall fun i => hv (ns i))
    _ = (C : ℝ≥0∞) * ‖W1p.gradient u‖ₑ := (hbound.comp hns.tendsto_atTop).liminf_eq

/-- **The Sobolev–Poincaré inequality on `W^{1,p}(Ω)`.** Let `Ω` be a bounded convex open set in
a real inner product space of finite dimension `n ≥ 1`, let `ω = μ(B(0, 1))`, let `S ⊆ Ω` have
positive measure, and let `p ≤ q < ∞` with `δ = 1/p - 1/q < 1/n`. Every `u ∈ W^{1,p}(Ω)` satisfies

`‖u - ⨍_S u‖_{L^q(Ω)} ≤ (diam Ω)ⁿ / n · K ω ^ (1 - 1/n) / μ(S) · μ(Ω) ^ (1/n - δ) ‖∇u‖_{Lᵖ(Ω)}`,

where `K = ((1 - δ) / (1/n - δ)) ^ (1 - δ)`. In particular `u - ⨍_S u` lies in `L^q(Ω)`. -/
theorem W1p.eLpNorm_value_sub_setAverage_le_mul_measure_rpow_of_convex [Nontrivial E]
    (hp : p ≠ ∞) (hconv : Convex ℝ (Omega : Set E)) (hb : Bornology.IsBounded (Omega : Set E))
    (hS : S ⊆ (Omega : Set E)) (hS0 : mu S ≠ 0) {q : ℝ≥0} (hpq : p ≤ q) {δ : ℝ}
    (hδ : p.toReal⁻¹ - (q : ℝ)⁻¹ = δ) (hδn : δ < (finrank ℝ E : ℝ)⁻¹) (u : W1p mu Omega p) :
    eLpNorm (fun x ↦ W1p.value u x - ⨍ y in S, W1p.value u y ∂mu) q (mu.restrict Omega) ≤
      ENNReal.ofReal (diam (Omega : Set E) ^ finrank ℝ E / finrank ℝ E *
          (((1 - δ) / ((finrank ℝ E : ℝ)⁻¹ - δ)) ^ (1 - δ) *
            mu.real (ball 0 1) ^ (1 - (finrank ℝ E : ℝ)⁻¹))) / mu S *
        mu Omega ^ ((finrank ℝ E : ℝ)⁻¹ - δ) * ‖W1p.gradient u‖ₑ := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hpp : ((p.toNNReal : ℝ≥0) : ℝ≥0∞) = p := ENNReal.coe_toNNReal hp
  have hOfin : mu Omega ≠ ∞ := hb.measure_lt_top.ne
  have hSfin : mu S ≠ ∞ := ne_top_of_le_ne_top hOfin (measure_mono hS)
  set C : ℝ≥0∞ := ENNReal.ofReal (diam (Omega : Set E) ^ finrank ℝ E / finrank ℝ E *
      (((1 - δ) / ((finrank ℝ E : ℝ)⁻¹ - δ)) ^ (1 - δ) *
        mu.real (ball 0 1) ^ (1 - (finrank ℝ E : ℝ)⁻¹))) / mu S *
    mu Omega ^ ((finrank ℝ E : ℝ)⁻¹ - δ)
  have hC : C ≠ ∞ := ENNReal.mul_ne_top (ENNReal.div_ne_top ENNReal.ofReal_ne_top hS0)
    (ENNReal.rpow_ne_top_of_nonneg (sub_nonneg.2 hδn.le) hOfin)
  rw [← ENNReal.coe_toNNReal hC]
  -- By Meyers–Serrin it suffices to treat the elements represented by functions smooth on `Ω`.
  refine closure_minimal (fun (w : Wkp mu Omega p 1) hw => ?_)
    (W1p.isClosed_setOf_eLpNorm_value_sub_setAverage_le hS hSfin q C.toNNReal)
    (Wkp.dense_contDiffOn_representatives hp 1 u)
  obtain ⟨f, hf, hwf⟩ := hw
  rw [Wkp.value_one] at hwf
  have hf1 : ContDiffOn ℝ 1 f Omega := hf.of_le (by simp)
  have hfy : ∀ y ∈ (Omega : Set E), DifferentiableAt ℝ f y := fun y hy =>
    (hf1.differentiableOn one_ne_zero y hy).differentiableAt (Omega.isOpen.mem_nhds hy)
  have hcont : ContinuousOn (fderiv ℝ f) Omega :=
    hf1.continuousOn_fderiv_of_isOpen Omega.isOpen le_rfl
  have hgrad : ∀ᵐ y ∂mu.restrict Omega, innerSL ℝ (W1p.gradient w y) = fderiv ℝ f y :=
    ((W1p.hasWeakFDerivOn w).congr_ae hwf).ae_eq_fderiv
      (hcont.locallyIntegrableOn Omega.isOpen.measurableSet) hfy
  have havg : ⨍ y in S, W1p.value w y ∂mu = ⨍ y in S, f y ∂mu :=
    average_congr (hwf.filter_mono (ae_mono (Measure.restrict_mono hS le_rfl)))
  have hvalue : eLpNorm (fun x ↦ W1p.value w x - ⨍ y in S, W1p.value w y ∂mu) q
      (mu.restrict Omega) = eLpNorm (fun x ↦ f x - ⨍ y in S, f y ∂mu) q (mu.restrict Omega) := by
    rw [havg]
    exact eLpNorm_congr_ae (hwf.mono fun x hx ↦ by simp only [hx])
  have hgradient : ‖W1p.gradient w‖ₑ = eLpNorm (fderiv ℝ f) p (mu.restrict Omega) := by
    rw [Lp.enorm_def]
    refine eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _)
      (hcont.aestronglyMeasurable Omega.isOpen.measurableSet) ?_
    filter_upwards [hgrad] with y hy
    rw [← hy, innerSL_apply_norm]
  have key := eLpNorm_sub_setAverage_le_mul_measure_rpow_of_convex (μ := mu) (p := p.toNNReal)
    (q := q) Omega.isOpen hconv hb hf1 hS hS0 (by exact_mod_cast hpp ▸ hp1)
    (by exact_mod_cast hpp ▸ hpq) (by rwa [ENNReal.coe_toNNReal_eq_toReal]) hδn
  rw [hpp] at key
  have hw : eLpNorm (fun x ↦ W1p.value w x - ⨍ y in S, W1p.value w y ∂mu) q
      (mu.restrict Omega) ≤ (C.toNNReal : ℝ≥0∞) * ‖W1p.gradient w‖ₑ := by
    rw [hvalue, hgradient, ENNReal.coe_toNNReal hC]
    exact key
  exact hw

/-- The constant of `TauCeti.W1p.eLpNorm_value_sub_setAverage_le_mul_measure_rpow_of_convex` on a
ball of radius `r` and measure `m = rⁿ ω`, with `S` the whole ball: since `diam ≤ 2r`, it is at most
`2ⁿ / n · K · r · m ^ (-δ)`, for `κ = 1/n`. -/
private theorem diam_pow_div_mul_div_mul_rpow_le {n : ℕ} {D r ω K κ δ : ℝ} (hnκ : n * κ = 1)
    (hD0 : 0 ≤ D) (hD : D ≤ 2 * r) (hr : 0 < r) (hω : 0 < ω) (hK : 0 ≤ K) :
    D ^ n / n * (K * ω ^ (1 - κ)) / (r ^ n * ω) * (r ^ n * ω) ^ (κ - δ) ≤
      2 ^ n / n * K * r * (r ^ n * ω) ^ (-δ) := by
  have hm : 0 < r ^ n * ω := by positivity
  have hn : (n : ℝ) ≠ 0 := left_ne_zero_of_mul_eq_one hnκ
  have hmκ : (r ^ n * ω) ^ κ = r * ω ^ κ := by
    rw [Real.mul_rpow (by positivity) hω.le, ← Real.rpow_natCast, ← Real.rpow_mul hr.le, hnκ,
      Real.rpow_one]
  have hωκ : ω ^ (1 - κ) * ω ^ κ = ω := by
    rw [← Real.rpow_add hω, sub_add_cancel, Real.rpow_one]
  calc D ^ n / n * (K * ω ^ (1 - κ)) / (r ^ n * ω) * (r ^ n * ω) ^ (κ - δ)
      ≤ (2 * r) ^ n / n * (K * ω ^ (1 - κ)) / (r ^ n * ω) * (r ^ n * ω) ^ (κ - δ) := by
        gcongr
    _ = 2 ^ n / n * K * r * (r ^ n * ω) ^ (-δ) := by
        -- Split `m ^ (κ - δ) = r ω ^ κ · m ^ (-δ)`, then collect the factor `rⁿ ω / m = 1`.
        have hκδ : κ - δ = κ + -δ := sub_eq_add_neg κ δ
        have hcollect : (2 * r) ^ n / n * (K * ω ^ (1 - κ)) / (r ^ n * ω) *
              (r * ω ^ κ * (r ^ n * ω) ^ (-δ)) =
            2 ^ n / n * K * r * (r ^ n * ω) ^ (-δ) *
              (r ^ n * (ω ^ (1 - κ) * ω ^ κ) / (r ^ n * ω)) := by
          ring
        rw [hκδ, Real.rpow_add hm, hmκ, hcollect, hωκ, div_self hm.ne', mul_one]

/-- **The Sobolev–Poincaré inequality on a ball, with averages.** Let `n ≥ 1` be the dimension,
let `p ≤ q < ∞` with `δ = 1/p - 1/q < 1/n`, and let `Ω = B(c, r)`. Every `u ∈ W^{1,p}(Ω)`
satisfies

`(⨍_Ω |u - u_Ω| ^ q) ^ (1/q) ≤ C r (⨍_Ω ‖∇u‖ ^ p) ^ (1/p)`,

where `u_Ω` is the mean of `u` over `Ω` and `C = 2ⁿ / n · ((1 - δ) / (1/n - δ)) ^ (1 - δ)`.
The constant `C` depends only on `n`, `p` and `q`, not on the normalization of `μ`: the
inequality is invariant under dilations. -/
theorem W1p.setLAverage_rpow_enorm_value_sub_setAverage_le_of_eq_ball [Nontrivial E]
    (hp : p ≠ ∞) {c : E} {r : ℝ} (hr : 0 < r) (hOmega : (Omega : Set E) = ball c r) {q : ℝ≥0}
    (hpq : p ≤ q) {δ : ℝ} (hδ : p.toReal⁻¹ - (q : ℝ)⁻¹ = δ)
    (hδn : δ < (finrank ℝ E : ℝ)⁻¹) (u : W1p mu Omega p) :
    (⨍⁻ x in Omega, ‖W1p.value u x - ⨍ y in Omega, W1p.value u y ∂mu‖ₑ ^ (q : ℝ) ∂mu) ^
        (q : ℝ)⁻¹ ≤
      ENNReal.ofReal (2 ^ finrank ℝ E / finrank ℝ E *
          ((1 - δ) / ((finrank ℝ E : ℝ)⁻¹ - δ)) ^ (1 - δ) * r) *
        (⨍⁻ x in Omega, ‖W1p.gradient u x‖ₑ ^ p.toReal ∂mu) ^ p.toReal⁻¹ := by
  set n := finrank ℝ E
  set K := ((1 - δ) / ((n : ℝ)⁻¹ - δ)) ^ (1 - δ)
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast finrank_pos
  have hω : 0 < mu.real (ball (0 : E) 1) := Metric.measureReal_ball_pos mu 0 one_pos
  have hK : 0 ≤ K := Real.rpow_nonneg (div_nonneg
    (by linarith [hδn.trans_le (inv_le_one_of_one_le₀ hn)]) (sub_nonneg.2 hδn.le)) _
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
  have hq0 : (q : ℝ≥0∞) ≠ 0 := ne_bot_of_le_ne_bot hp0 hpq
  -- The measure `m = rⁿ ω` of the ball.
  set m : ℝ := r ^ n * mu.real (ball (0 : E) 1)
  have hm : 0 < m := by positivity
  have hmeas : mu Omega = ENNReal.ofReal m := by
    rw [hOmega, Measure.addHaar_ball_of_pos mu c hr, ← ofReal_measureReal measure_ball_lt_top.ne,
      ← ENNReal.ofReal_mul (by positivity)]
  have hSP := W1p.eLpNorm_value_sub_setAverage_le_mul_measure_rpow_of_convex hp
    (hOmega ▸ convex_ball c r) (hOmega ▸ isBounded_ball) subset_rfl
    (by rw [hmeas]; exact (ENNReal.ofReal_pos.2 hm).ne') hpq hδ hδn u
  rw [hmeas, ENNReal.ofReal_rpow_of_pos hm, ← ENNReal.ofReal_div_of_pos hm,
    ← ENNReal.ofReal_mul (div_nonneg (by positivity) hm.le)] at hSP
  have hconst := diam_pow_div_mul_div_mul_rpow_le (κ := (n : ℝ)⁻¹) (δ := δ)
    (mul_inv_cancel₀ (by positivity)) diam_nonneg
    (hOmega ▸ diam_ball hr.le) hr hω hK
  -- Both averages are `Lᵖ` norms divided by powers of `m`, and `m ^ (-δ - 1/q) = m ^ (-1/p)`.
  have hL := laverage_rpow_enorm_rpow_inv_eq (μ := mu.restrict Omega) (p := q)
    (f := fun x ↦ W1p.value u x - ⨍ y in Omega, W1p.value u y ∂mu) hq0 ENNReal.coe_ne_top
    ((Lp.aestronglyMeasurable _).sub aestronglyMeasurable_const)
  rw [ENNReal.coe_toReal] at hL
  rw [hL, laverage_rpow_enorm_rpow_inv_eq hp0 hp (Lp.aestronglyMeasurable _), ← Lp.enorm_def,
    Measure.restrict_apply_univ, hmeas, ENNReal.ofReal_rpow_of_pos hm,
    ENNReal.ofReal_rpow_of_pos hm, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul,
    ← ENNReal.ofReal_inv_of_pos (by positivity), ← ENNReal.ofReal_inv_of_pos (by positivity)]
  have hexp : m ^ (-δ) * (m ^ (q : ℝ)⁻¹)⁻¹ = (m ^ p.toReal⁻¹)⁻¹ := by
    rw [← Real.rpow_neg hm.le, ← Real.rpow_neg hm.le, ← Real.rpow_add hm, ← hδ]
    ring_nf
  calc ENNReal.ofReal (m ^ (q : ℝ)⁻¹)⁻¹ *
        eLpNorm (fun x ↦ W1p.value u x - ⨍ y in Omega, W1p.value u y ∂mu) q (mu.restrict Omega)
      ≤ ENNReal.ofReal (m ^ (q : ℝ)⁻¹)⁻¹ *
          (ENNReal.ofReal (2 ^ n / n * K * r * m ^ (-δ)) * ‖W1p.gradient u‖ₑ) := by
        gcongr
        exact hSP.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hconst) le_rfl)
    _ = ENNReal.ofReal (2 ^ n / n * K * r) *
          (ENNReal.ofReal (m ^ p.toReal⁻¹)⁻¹ * ‖W1p.gradient u‖ₑ) := by
        rw [← hexp, ENNReal.ofReal_mul (Real.rpow_nonneg hm.le (-δ)),
          ENNReal.ofReal_mul (p := 2 ^ n / n * K * r) (by positivity)]
        ring

/-- **The Sobolev–Poincaré inequality on a ball inside the domain, with averages.** Let `n ≥ 1`
be the dimension, let `p ≤ q < ∞` with `δ = 1/p - 1/q < 1/n`, and let `p ≤ p₀`. If
`u ∈ W^{1,p₀}(Ω)` and `B = B(c, r) ⊆ Ω`, then

`(⨍_B |u - u_B| ^ q) ^ (1/q) ≤ C r (⨍_B ‖∇u‖ ^ p) ^ (1/p)`,

with `C = 2ⁿ / n · ((1 - δ) / (1/n - δ)) ^ (1 - δ)`. This is
`TauCeti.W1p.setLAverage_rpow_enorm_value_sub_setAverage_le_of_eq_ball` for the restriction of `u`
to the ball, which lies in `W^{1,p}(B)` because the ball has finite measure. -/
theorem W1p.setLAverage_rpow_enorm_value_sub_setAverage_le_of_ball_subset [Nontrivial E]
    {p₀ : ℝ≥0∞} [Fact (1 ≤ p₀)] (hp : p ≠ ∞) (hpp₀ : p ≤ p₀) {c : E} {r : ℝ} (hr : 0 < r)
    (hball : ball c r ⊆ (Omega : Set E)) {q : ℝ≥0} (hpq : p ≤ q) {δ : ℝ}
    (hδ : p.toReal⁻¹ - (q : ℝ)⁻¹ = δ) (hδn : δ < (finrank ℝ E : ℝ)⁻¹) (u : W1p mu Omega p₀) :
    (⨍⁻ x in ball c r, ‖W1p.value u x - ⨍ y in ball c r, W1p.value u y ∂mu‖ₑ ^ (q : ℝ) ∂mu) ^
        (q : ℝ)⁻¹ ≤
      ENNReal.ofReal (2 ^ finrank ℝ E / finrank ℝ E *
          ((1 - δ) / ((finrank ℝ E : ℝ)⁻¹ - δ)) ^ (1 - δ) * r) *
        (⨍⁻ x in ball c r, ‖W1p.gradient u x‖ₑ ^ p.toReal ∂mu) ^ p.toReal⁻¹ := by
  -- Restrict `u` to the ball `B = B(c, r)`, viewed as a domain of its own, and lower the exponent.
  set B : Opens E := ⟨ball c r, isOpen_ball⟩
  have hB : B ≤ Omega := hball
  have : IsFiniteMeasure (mu.restrict (B : Set E)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  set uB : W1p mu B p := W1p.ofExponentLE hpp₀ (W1p.restrictL hB u)
  have hval : W1p.value uB =ᵐ[mu.restrict (ball c r)] W1p.value u :=
    (W1p.value_ofExponentLE_ae _ _).trans (W1p.value_restrictL_ae hB u)
  have hgrad : W1p.gradient uB =ᵐ[mu.restrict (ball c r)] W1p.gradient u :=
    (W1p.gradient_ofExponentLE_ae _ _).trans (W1p.gradient_restrictL_ae hB u)
  have havg : ⨍ y in (B : Set E), W1p.value uB y ∂mu = ⨍ y in ball c r, W1p.value u y ∂mu :=
    average_congr hval
  have h := W1p.setLAverage_rpow_enorm_value_sub_setAverage_le_of_eq_ball hp hr rfl hpq hδ hδn uB
  have h1 : ⨍⁻ x in (B : Set E), ‖W1p.value uB x - ⨍ y in (B : Set E), W1p.value uB y ∂mu‖ₑ ^
        (q : ℝ) ∂mu =
      ⨍⁻ x in ball c r, ‖W1p.value u x - ⨍ y in ball c r, W1p.value u y ∂mu‖ₑ ^ (q : ℝ) ∂mu :=
    laverage_congr (hval.mono fun x hx => by simp only [hx, havg])
  have h2 : ⨍⁻ x in (B : Set E), ‖W1p.gradient uB x‖ₑ ^ p.toReal ∂mu =
      ⨍⁻ x in ball c r, ‖W1p.gradient u x‖ₑ ^ p.toReal ∂mu :=
    laverage_congr (hgrad.mono fun x hx => by simp only [hx])
  rwa [h1, h2] at h

end W1p

end TauCeti
