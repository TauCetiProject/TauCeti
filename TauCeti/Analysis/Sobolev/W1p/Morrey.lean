/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Holder
public import TauCeti.Analysis.Sobolev.W1p.Density

import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.Sobolev.Morrey
import TauCeti.Topology.MetricSpace.Holder

/-!
# Morrey's embedding for `W^{1,p}(ℝⁿ)`

Let `E` be a finite-dimensional real inner product space of dimension `n`, with an additive Haar
measure `μ`, and let `n < p < ∞`. This file proves Morrey's embedding on the whole space: every
`u ∈ W^{1,p}(ℝⁿ)` has a representative which is Hölder continuous of exponent `1 - n / p`,

`‖u x - u y‖ ≤ C(n, p, μ) * ‖x - y‖ ^ (1 - n / p) * ‖∇u‖_{Lᵖ}`,

with the explicit constant of Morrey's inequality for `C¹` functions
(`TauCeti.holderWith_of_contDiff_of_finrank_lt`): writing `ω = μ(B(0, 1))` and
`K = n ω (p - 1) / (p - n)`, it is `C = 2 ^ (n + 1) / (n ω) * K ^ (1 - 1 / p) * 2 ^ (1 - n / p)`.
Only the gradient enters the Hölder constant, as it must: adding a constant to `u` changes nothing
on the right-hand side.

## The argument

Test functions are dense in `W^{1,p}(ℝⁿ)` (`TauCeti.W1p.denseRange_ofTestFunctionₗ_top`), so `u` is
the Sobolev limit of test functions `φₖ`. Each `φₖ` satisfies Morrey's inequality with its own
gradient norm, and these norms converge to `‖∇u‖_{Lᵖ}`. Convergence in `Lᵖ` gives a subsequence
converging to `u` almost everywhere, so the Hölder inequality passes to the limit at every pair of
points of a set of full measure. That set is dense, and a Hölder function on a dense set extends
to a Hölder function on the whole space (`HolderOnWith.extend_of_dense`), which is the
required representative.

## Main declarations

* `TauCeti.W1p.exists_holderWith_ae_eq_value`: Morrey's embedding; a function in `W^{1,p}(ℝⁿ)`,
  `n < p < ∞`, agrees almost everywhere with a Hölder continuous function of exponent `1 - n / p`,
  whose Hölder constant is controlled by `‖∇u‖_{Lᵖ}`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 7.17.
* L. C. Evans, *Partial Differential Equations*, §5.6.2, Theorem 4.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Metric Set Module TopologicalSpace Filter Topology
open scoped Distributions ENNReal NNReal Gradient

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]

/-- The `Lᵖ` norm of the derivative of a test function on the whole space is the norm of its
gradient in `W^{1,p}(ℝⁿ)`. -/
private theorem eLpNorm_fderiv_testFunction_eq (phi : 𝓓((⊤ : Opens E), ℝ)) :
    eLpNorm (fderiv ℝ (phi : E → ℝ)) p mu =
      ‖W1p.gradient (W1p.ofTestFunctionₗ mu ⊤ (p : ℝ≥0∞) phi)‖ₑ := by
  rw [W1p.gradient_ofTestFunctionₗ, Lp.enorm_def]
  refine Eq.trans ?_ (eLpNorm_congr_ae
    (Filter.EventuallyEq.symm (gradientTestFunctionLp_apply_ae (mu := mu) (p : ℝ≥0∞) phi)))
  rw [Opens.coe_top, Measure.restrict_univ]
  exact eLpNorm_congr_norm_ae (.of_forall fun x => (norm_gradient_eq_norm_fderiv _ x).symm)

/-- **Morrey's embedding for `W^{1,p}(ℝⁿ)`.** If `p` exceeds the dimension `n` of the space and is
finite, then every `u ∈ W^{1,p}(ℝⁿ)` agrees almost everywhere with a function which is Hölder
continuous of exponent `1 - n / p`, with constant
`2 ^ (n + 1) / (n ω) * K ^ (1 - 1 / p) * 2 ^ (1 - n / p) * ‖∇u‖_{Lᵖ}`, where `ω = μ(B(0, 1))`
and `K = n ω (p - 1) / (p - n)`. -/
theorem W1p.exists_holderWith_ae_eq_value (hp : (finrank ℝ E : ℝ≥0) < p)
    (u : W1p mu ⊤ (p : ℝ≥0∞)) :
    ∃ g : E → ℝ,
      HolderWith (Real.toNNReal (2 ^ (finrank ℝ E + 1) / (finrank ℝ E * mu.real (ball 0 1)) *
          (finrank ℝ E * mu.real (ball 0 1) * (p - 1) / (p - finrank ℝ E)) ^ (1 - 1 / (p : ℝ)) *
            2 ^ (1 - finrank ℝ E / (p : ℝ))) * ‖W1p.gradient u‖₊)
        (1 - finrank ℝ E / p) g ∧
      W1p.value u =ᵐ[mu] g := by
  set C : ℝ≥0 := Real.toNNReal (2 ^ (finrank ℝ E + 1) / (finrank ℝ E * mu.real (ball 0 1)) *
    (finrank ℝ E * mu.real (ball 0 1) * (p - 1) / (p - finrank ℝ E)) ^ (1 - 1 / (p : ℝ)) *
      2 ^ (1 - finrank ℝ E / (p : ℝ)))
  set α : ℝ≥0 := 1 - finrank ℝ E / p
  set T := W1p.ofTestFunctionₗ mu ⊤ (p : ℝ≥0∞)
  have htop : mu.restrict ((⊤ : Opens E) : Set E) = mu := by
    simp only [Opens.coe_top, Measure.restrict_univ]
  have hα : 0 < α := tsub_pos_of_lt ((div_lt_one (zero_le.trans_lt hp)).2 hp)
  -- Morrey's inequality for a single test function, with its Sobolev gradient norm.
  have hmorrey (phi : 𝓓((⊤ : Opens E), ℝ)) (x y : E) :
      edist (phi x) (phi y) ≤
        ((C * ‖W1p.gradient (T phi)‖₊ : ℝ≥0) : ℝ≥0∞) * edist x y ^ (α : ℝ) := by
    have hphi : ContDiff ℝ 1 (phi : E → ℝ) := phi.contDiff.of_le (by simp)
    have hfin : eLpNorm (fderiv ℝ (phi : E → ℝ)) p mu ≠ ∞ := by
      rw [eLpNorm_fderiv_testFunction_eq]
      exact enorm_ne_top
    have h := holderWith_of_contDiff_of_finrank_lt (μ := mu) hphi hp hfin x y
    rwa [eLpNorm_fderiv_testFunction_eq, toNNReal_enorm] at h
  -- Approximate `u` by test functions.
  obtain ⟨v, hvmem, hvlim⟩ := mem_closure_iff_seq_limit.1
    (W1p.denseRange_ofTestFunctionₗ_top (mu := mu) ENNReal.coe_ne_top u)
  choose phi hphi using hvmem
  have hlim : Tendsto (fun k => T (phi k)) atTop (𝓝 u) := by
    rwa [show (fun k => T (phi k)) = v from funext hphi]
  -- A subsequence converges to `u` almost everywhere.
  obtain ⟨ns, hmono, hns⟩ := (tendstoInMeasure_of_tendsto_Lp
    ((W1p.valueL.continuous.tendsto u).comp hlim)).exists_seq_tendsto_ae
  have hval : ∀ᵐ x ∂mu, ∀ k, W1p.value (T (phi k)) x = phi k x := by
    rw [ae_all_iff]
    intro k
    rw [W1p.value_ofTestFunctionₗ]
    exact (testFunctionLp_apply_ae (mu := mu) (p : ℝ≥0∞) (phi k)).filter_mono (ae_mono htop.ge)
  have hA : ∀ᵐ x ∂mu, Tendsto (fun k => phi (ns k) x) atTop (𝓝 (W1p.value u x)) := by
    filter_upwards [hns.filter_mono (ae_mono htop.ge), hval] with x hx hvx
    simpa only [Function.comp_apply, W1p.valueL_apply, hvx] using hx
  set A := {x | Tendsto (fun k => phi (ns k) x) atTop (𝓝 (W1p.value u x))}
  -- On the set of convergence, the Hölder inequality passes to the limit.
  have hgrad : Tendsto (fun k => ((C * ‖W1p.gradient (T (phi (ns k)))‖₊ : ℝ≥0) : ℝ≥0∞)) atTop
      (𝓝 ((C * ‖W1p.gradient u‖₊ : ℝ≥0) : ℝ≥0∞)) := by
    have hG : Tendsto (fun k => W1p.gradient (T (phi (ns k)))) atTop (𝓝 (W1p.gradient u)) := by
      simpa only [Function.comp_def, W1p.gradientL_apply] using
        (W1p.gradientL.continuous.tendsto u).comp (hlim.comp hmono.tendsto_atTop)
    exact ENNReal.tendsto_coe.2 (tendsto_const_nhds.mul ((continuous_nnnorm.tendsto _).comp hG))
  have hholder : HolderOnWith (C * ‖W1p.gradient u‖₊) α (W1p.value u) A := by
    intro x hx y hy
    have hd : edist x y ^ (α : ℝ) ≠ ∞ :=
      ENNReal.rpow_ne_top_of_nonneg (NNReal.coe_nonneg _) (edist_ne_top x y)
    exact le_of_tendsto_of_tendsto' (hx.edist hy) (ENNReal.Tendsto.mul_const hgrad (Or.inr hd))
      fun k => hmorrey (phi (ns k)) x y
  obtain ⟨g, hg, hgA⟩ := hholder.extend_of_dense hα (mu.dense_of_ae hA)
  refine ⟨g, hg, ?_⟩
  filter_upwards [hA] with x hx using hgA hx

end TauCeti
