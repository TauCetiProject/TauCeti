/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.ChangeOrigin
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import TauCeti.Analysis.Analytic.OfScalars
public import TauCeti.Analysis.Normed.Algebra.HolomorphicFunctionalCalculus.Basic
import TauCeti.Analysis.Normed.Algebra.GelfandRadius

/-!
# Power series expansions for the holomorphic functional calculus

If a complex function `f` has power series `p` on an open extended ball `Metric.eball z₀ r`
containing `spectrum ℂ a` for an element `a` of a complex Banach algebra `A`, then the
Banach-algebra power series `∑ p.coeff k • (a - z₀ 1) ^ k` converges unconditionally in norm to the
value of the holomorphic functional calculus at `f`.

## Main results

* `TauCeti.hasSum_holomorphicCalculusOn_of_hasFPowerSeriesOnBall`: open-ball form.
* `TauCeti.hasSum_holomorphicCalculus_of_hasFPowerSeriesOnBall` and
  `TauCeti.holomorphicCalculus_eq_tsum_of_hasFPowerSeriesOnBall`: germ forms.
* `TauCeti.holomorphicCalculus_ofScalarsSum`: evaluation on shifted scalar power series
  `FormalMultilinearSeries.ofScalarsSum`.

## References

* H. G. Dales, *Banach Algebras and Automatic Continuity*, §2.4, Theorem 2.4.4.
* J. B. Conway, *A Course in Functional Analysis*, second edition, VII.4, Theorem 4.7.
-/

public noncomputable section

open Complex Filter Set TopologicalSpace Topology
open scoped ENNReal NNReal Real

namespace TauCeti

open HolomorphicFunctions

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

private theorem tendsto_holomorphicCalculusOn_partialSum (a : A) {f : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ} {z₀ : ℂ} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f p z₀ r) (ha : spectrum ℂ a ⊆ Metric.eball z₀ r) :
    Tendsto (fun n : ℕ ↦ ∑ k ∈ Finset.range n, p.coeff k • (a - algebraMap ℂ A z₀) ^ k) atTop
      (𝓝 (holomorphicCalculusOn a ⟨Metric.eball z₀ r, Metric.isOpen_eball⟩ ha
        (of ⟨Metric.eball z₀ r, Metric.isOpen_eball⟩ f hf.differentiableOn))) := by
  let U : Opens ℂ := ⟨Metric.eball z₀ r, Metric.isOpen_eball⟩
  let P : ℕ → Polynomial ℂ := fun n ↦
    ∑ k ∈ Finset.range n, Polynomial.C (p.coeff k) * (Polynomial.X - Polynomial.C z₀) ^ k
  let S : ℕ → holomorphicFunctions U := fun n ↦
    of U (fun z ↦ (P n).eval z) (P n).differentiable.differentiableOn
  have hconv : Tendsto S atTop (𝓝 (of U f hf.differentiableOn)) := by
    rw [tendsto_iff_tendstoLocallyUniformlyOn,
      tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
    convert tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe.mp
      hf.tendstoLocallyUniformlyOn' using 1
    · ext n ⟨z, hz⟩
      rw [extend_apply (S n) ⟨z, hz⟩, of_apply, ← Polynomial.coe_evalRingHom]
      dsimp only [P]
      rw [map_sum]
      simp [Polynomial.coe_evalRingHom, FormalMultilinearSeries.partialSum, mul_comm]
    · ext ⟨z, hz⟩
      simp [extend_apply _ ⟨z, hz⟩]
  have hmap := ((continuous_holomorphicCalculusOn a U ha).tendsto _).comp hconv
  refine hmap.congr fun n ↦ ?_
  simp [S, P, Function.comp_apply, Algebra.smul_def]

/-- **Power series expansion in the holomorphic calculus (open ball form).** If `f` has power
series `p` on `Metric.eball z₀ r` and `spectrum ℂ a ⊆ Metric.eball z₀ r`, then the series
`∑ p.coeff k • (a - z₀ 1) ^ k` converges unconditionally in norm to the calculus value of `f` on
`Metric.eball z₀ r`. -/
theorem hasSum_holomorphicCalculusOn_of_hasFPowerSeriesOnBall (a : A) {f : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ} {z₀ : ℂ} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f p z₀ r) (ha : spectrum ℂ a ⊆ Metric.eball z₀ r) :
    HasSum (fun k : ℕ ↦ p.coeff k • (a - algebraMap ℂ A z₀) ^ k)
      (holomorphicCalculusOn a ⟨Metric.eball z₀ r, Metric.isOpen_eball⟩ ha
        (of ⟨Metric.eball z₀ r, Metric.isOpen_eball⟩ f hf.differentiableOn)) :=
  (hasSum_iff_tendsto_nat_of_summable_norm
    (p.summable_norm_coeff_smul_pow_of_spectrum_subset_eball
      (ha.trans (Metric.eball_subset_eball hf.r_le)))).mpr
    (tendsto_holomorphicCalculusOn_partialSum a hf ha)

/-- **Power series expansion in the holomorphic germ calculus.** If `f` has power series `p` on
`Metric.eball z₀ r` and `spectrum ℂ a ⊆ Metric.eball z₀ r`, then `∑ p.coeff k • (a - z₀ 1) ^ k`
converges unconditionally in norm to `holomorphicCalculus a` at the germ of `f`. -/
theorem hasSum_holomorphicCalculus_of_hasFPowerSeriesOnBall (a : A) {f : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ} {z₀ : ℂ} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f p z₀ r) (ha : spectrum ℂ a ⊆ Metric.eball z₀ r) :
    HasSum (fun k : ℕ ↦ p.coeff k • (a - algebraMap ℂ A z₀) ^ k)
      (holomorphicCalculus a (holomorphicGerms.ofFun f (hf.analyticOnNhd.mono ha))) := by
  have h := hasSum_holomorphicCalculusOn_of_hasFPowerSeriesOnBall a hf ha
  rwa [← holomorphicCalculus_toGerm, toGerm_of] at h

/-- Value of `holomorphicCalculus a` on a convergent power series as a `tsum`. -/
theorem holomorphicCalculus_eq_tsum_of_hasFPowerSeriesOnBall (a : A) {f : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ} {z₀ : ℂ} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f p z₀ r) (ha : spectrum ℂ a ⊆ Metric.eball z₀ r) :
    holomorphicCalculus a (holomorphicGerms.ofFun f (hf.analyticOnNhd.mono ha)) =
      ∑' k : ℕ, p.coeff k • (a - algebraMap ℂ A z₀) ^ k :=
  (hasSum_holomorphicCalculus_of_hasFPowerSeriesOnBall a hf ha).tsum_eq.symm

/-- For a scalar power series `∑' n, c n * (z - z₀) ^ n` whose open disk of convergence contains
`spectrum ℂ a`, the holomorphic germ calculus agrees with `FormalMultilinearSeries.ofScalarsSum`. -/
theorem holomorphicCalculus_ofScalarsSum (c : ℕ → ℂ) (z₀ : ℂ) {a : A}
    (ha : spectrum ℂ a ⊆ Metric.eball z₀ (FormalMultilinearSeries.ofScalars ℂ c).radius) :
    holomorphicCalculus a (holomorphicGerms.ofFun
        (fun z ↦ FormalMultilinearSeries.ofScalarsSum c (z - z₀))
        ((analyticOnNhd_ofScalarsSum_sub c z₀).mono ha)) =
      FormalMultilinearSeries.ofScalarsSum c (a - algebraMap ℂ A z₀) := by
  nontriviality A
  obtain ⟨w, hw, _⟩ := spectrum.exists_eNorm_eq_spectralRadius a
  have hr : 0 < (FormalMultilinearSeries.ofScalars ℂ c).radius :=
    bot_le.trans_lt (Metric.mem_eball.mp (ha hw))
  rw [holomorphicCalculus_eq_tsum_of_hasFPowerSeriesOnBall a
      (hasFPowerSeriesOnBall_ofScalarsSum_sub c z₀ hr) ha,
    FormalMultilinearSeries.ofScalars_sum_eq]
  exact tsum_congr fun n ↦ by rw [FormalMultilinearSeries.coeff_ofScalars]

end TauCeti
