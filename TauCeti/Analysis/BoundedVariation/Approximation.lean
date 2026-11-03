/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.TotalVariation
import TauCeti.Analysis.BoundedVariation.Convolution
import TauCeti.Analysis.BoundedVariation.Multiplication
import TauCeti.Analysis.Calculus.BumpFunction.Convolution
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Convolution.Basic
import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# Smooth strict approximation

Every integrable real function on a finite-dimensional real inner product space admits
compactly supported smooth approximations converging in `L¹` and in total variation.
The variation may be infinite. For a BV function this is strict approximation, which is
weaker than convergence in the BV norm: jumps and singular derivatives are allowed.

Compact support makes the approximations suitable for choosing bounded regular superlevel
sets. Spatial cutoffs first control the error at infinity; mollification then provides
smoothness without losing compact support. The central formal inputs are
`TauCeti.totalVariationOn_top_mul_le`, the quantitative radial cutoffs in
`TauCeti.exists_forall_contDiff_cutoff_closedBall`, and
`ContDiffBump.totalVariationOn_normed_convolution_le`.

On an arbitrary open set `Ω`, a function `u` locally integrable on `Ω` is the limit of functions
smooth on `Ω` converging to it in `L¹(Ω)` whose variations on `Ω` converge to `|Du|(Ω)`, again
finite or infinite. Neither boundedness nor boundary regularity of `Ω` is needed. The approximation
is the locally finite sum `∑ k, ρ_k ⋆ (ζ k u)` over a nonnegative decomposition of unity `(ζ k)` of
`Ω` (`IsOpen.exists_contDiff_decomposition_cutoff`), with mollifiers `ρ_k` whose radii are chosen
piece by piece. Pairing it with a test vector field `φ`, the terms `ζ k div φ` combine into the
divergence of one test vector field of norm at most one, while the remaining terms `u Dζ k`, whose
sum vanishes, only contribute their small mollification errors. All the `ρ_k` are rescalings of
one kernel, so the averages over translates defining the different pieces can be taken jointly.

## Main results

* `MeasureTheory.Integrable.exists_contDiff_hasCompactSupport_strict_approximation`: compactly
  supported smooth strict approximation on the whole space.
* `MeasureTheory.LocallyIntegrableOn.exists_contDiffOn_strict_approximation`: strict
  approximation on an open set by functions smooth on it.
* `MeasureTheory.LocallyIntegrableOn.exists_contDiffOn_tendsto_setLIntegral_enorm_fderiv`: the same
  approximation, with `∫_Ω ‖∇w‖ → |Du|(Ω)`.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised
  edition, §5.2.2 (smooth approximation of BV functions).
* G. Anzellotti, M. Giaquinta, *Funzioni BV e tracce*, Rend. Sem. Mat. Univ. Padova 60 (1978),
  1–21.
* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, Theorem 3.9.
-/
public section

noncomputable section

open MeasureTheory Filter Metric Set TopologicalSpace ContinuousLinearMap
open scoped ENNReal NNReal Convolution Topology Gradient ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {u : E → ℝ}

namespace TauCeti

omit [μ.IsAddHaarMeasure] in
private theorem exists_cutoff_approximation (hu : Integrable u μ) :
    ∃ v : ℕ → E → ℝ, (∀ n, Integrable (v n) μ ∧ HasCompactSupport (v n)) ∧
      Tendsto (fun n => ∫⁻ x, ‖v n x - u x‖ₑ ∂μ) atTop (𝓝 0) ∧
      ∃ b : ℕ → ℝ≥0∞, Tendsto b atTop (𝓝 0) ∧
        ∀ n, totalVariationOn μ ⊤ (v n) ≤ totalVariationOn μ ⊤ u + b n := by
  -- Cut off on expanding balls with derivative bound tending to zero.
  obtain ⟨c, hc, hcut⟩ := exists_forall_contDiff_cutoff_closedBall (E := E)
  have hcut' (n : ℕ) := hcut (0 : E) (r := n + 1) (R := 2 * (n + 1))
    (by positivity) (by linarith [Nat.cast_nonneg (α := ℝ) n])
  choose χ hχ hχ01 hχone hχsupp hχgrad _ using hcut'
  have hχnorm (n : ℕ) (x : E) : ‖χ n x‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hχ01 n (mem_range_self x)).1]
    exact (hχ01 n (mem_range_self x)).2
  have hχc (n : ℕ) : HasCompactSupport (χ n) :=
    (isCompact_closedBall (0 : E) (2 * (n + 1))).of_isClosed_subset
      (isClosed_tsupport _) (hχsupp n)
  have hv (n : ℕ) : Integrable (χ n * u) μ :=
    hu.bdd_mul (hχ n).continuous.aestronglyMeasurable (.of_forall (hχnorm n))
  -- Dominated convergence controls the discarded L¹ mass.
  have hlim : Tendsto (fun n => ∫⁻ x, ‖χ n x * u x - u x‖ₑ ∂μ) atTop (𝓝 0) := by
    have hdom (n : ℕ) (x : E) : ‖χ n x * u x - u x‖ₑ ≤ ‖u x‖ₑ := by
      rw [← sub_one_mul, enorm_mul]
      have hle : ‖χ n x - 1‖ₑ ≤ 1 := by
        rw [← ofReal_norm, Real.norm_eq_abs]
        exact (ENNReal.ofReal_le_ofReal (by
          have h0 := (hχ01 n (mem_range_self x)).1
          have h1 := (hχ01 n (mem_range_self x)).2
          rw [abs_of_nonpos (by linarith)]
          linarith)).trans_eq ENNReal.ofReal_one
      simpa using mul_le_mul_left hle ‖u x‖ₑ
    have hpoint (x : E) : ∀ᶠ n : ℕ in atTop, χ n x = 1 := by
      filter_upwards [(tendsto_natCast_atTop_atTop.eventually_ge_atTop ‖x‖)] with n hn
      exact hχone n (by simpa using (hn.trans (by linarith : (n : ℝ) ≤ n + 1)))
    simpa only [Pi.mul_apply, Pi.sub_apply, lintegral_zero] using
      tendsto_lintegral_of_dominated_convergence' (f := fun _ => 0) (fun x => ‖u x‖ₑ)
        (fun n => ((hv n).sub hu).aestronglyMeasurable.enorm)
        (fun n => .of_forall (hdom n)) hu.hasFiniteIntegral.ne
        (.of_forall fun x => tendsto_const_nhds.congr' ((hpoint x).mono fun n hn => by
          simp only [Pi.sub_apply, Pi.mul_apply, hn, one_mul, sub_self, enorm_zero]))
  -- The product estimate bounds the additional variation by the L¹ mass times c / (n + 1).
  let b (n : ℕ) : ℝ≥0∞ := ENNReal.ofReal (c / (n + 1)) * ∫⁻ x, ‖u x‖ₑ ∂μ
  have hb : Tendsto b atTop (𝓝 0) := by
    have hreal : Tendsto (fun n : ℕ => c / (n + 1)) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using
        tendsto_const_nhds.mul tendsto_one_div_add_atTop_nhds_zero_nat (a := c)
    have h := ENNReal.Tendsto.mul_const
      (ENNReal.continuous_ofReal.tendsto 0 |>.comp hreal)
      (Or.inr hu.hasFiniteIntegral.ne)
    simpa [b, div_eq_mul_inv] using h
  refine ⟨fun n => χ n * u, fun n => ⟨hv n, (hχc n).mul_right⟩, hlim, b, hb, fun n => ?_⟩
  have hgrad (x : E) : ‖fderiv ℝ (χ n) x‖ ≤ c / (n + 1) := by
    have hr : 2 * ((n : ℝ) + 1) - (n + 1) = n + 1 := by ring
    simpa only [← toDual_gradient (𝕜 := ℝ), LinearIsometryEquiv.norm_map, hr] using hχgrad n x
  simpa only [b, ENNReal.ofReal_one, one_mul, Opens.coe_top, Measure.restrict_univ] using
    totalVariationOn_top_mul_le (μ := μ) (u := u) (c := 1) (Ω := ⊤) (hχ n)
      (fun x => by simpa only [Real.norm_eq_abs] using hχnorm n x)
      (subset_univ _) hgrad (hu.locallyIntegrable.locallyIntegrableOn ⊤)

end TauCeti

namespace MeasureTheory.Integrable

/-- Every integrable real function admits compactly supported smooth approximations converging
in `L¹` and in total variation on the whole space. For finite variation this is strict BV
approximation; the variation limit also holds when the original variation is infinite. -/
theorem exists_contDiff_hasCompactSupport_strict_approximation (hu : Integrable u μ) :
    ∃ w : ℕ → E → ℝ, (∀ n, ContDiff ℝ ∞ (w n) ∧ HasCompactSupport (w n)) ∧
      Tendsto (fun n => ∫⁻ x, ‖w n x - u x‖ₑ ∂μ) atTop (𝓝 0) ∧
      Tendsto (fun n => TauCeti.totalVariationOn μ ⊤ (w n)) atTop
        (𝓝 (TauCeti.totalVariationOn μ ⊤ u)) := by
  obtain ⟨v, hv, hvlim, b, hb, hvbound⟩ := TauCeti.exists_cutoff_approximation hu
  let φ : ℕ → ContDiffBump (0 : E) := fun k =>
    ⟨1 / (k + 2), 1 / (k + 1), by positivity, by gcongr; norm_num⟩
  have hφ : Tendsto (fun k => (φ k).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  -- Choose a mollification separately for each cutoff, with vanishing L¹ error.
  have happ (n : ℕ) : ∃ k, ∫⁻ x,
      ‖((φ k).normed μ ⋆[lsmul ℝ ℝ, μ] v n) x - v n x‖ₑ ∂μ < ENNReal.ofReal (1 / (n + 1)) :=
    ((TauCeti.tendsto_lintegral_enorm_normed_convolution_sub hφ (hv n).1).eventually
      (gt_mem_nhds (by positivity))).exists
  choose k hk using happ
  let w (n : ℕ) : E → ℝ := (φ (k n)).normed μ ⋆[lsmul ℝ ℝ, μ] v n
  have hw (n : ℕ) : ContDiff ℝ ∞ (w n) ∧ HasCompactSupport (w n) :=
    ⟨(φ (k n)).hasCompactSupport_normed.contDiff_convolution_left _
      (φ (k n)).contDiff_normed (hv n).1.locallyIntegrable,
      (φ (k n)).hasCompactSupport_normed.convolution (lsmul ℝ ℝ) (hv n).2⟩
  have hwi (n : ℕ) : Integrable (w n - v n) μ :=
    ((φ (k n)).integrable_normed.integrable_convolution (lsmul ℝ ℝ) (hv n).1).sub (hv n).1
  have hwv (n : ℕ) : TauCeti.totalVariationOn μ ⊤ (w n) ≤
      TauCeti.totalVariationOn μ ⊤ u + b n :=
    ((φ (k n)).totalVariationOn_normed_convolution_le
      ((hv n).1.locallyIntegrable.locallyIntegrableOn ⊤) (fun _ _ => subset_univ _)).trans
        (hvbound n)
  -- The two L¹ errors vanish; mollification does not increase the cutoff variation.
  have hwlim : Tendsto (fun n => ∫⁻ x, ‖w n x - u x‖ₑ ∂μ) atTop (𝓝 0) := by
    have hzero : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / (n + 1))) atTop (𝓝 0) := by
      simpa only [Function.comp_def, one_div, ENNReal.ofReal_zero] using
        ENNReal.continuous_ofReal.tendsto 0 |>.comp
        tendsto_one_div_add_atTop_nhds_zero_nat
    have hsum := hzero.add hvlim
    rw [add_zero] at hsum
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun _ => zero_le) fun n => ?_
    calc ∫⁻ x, ‖w n x - u x‖ₑ ∂μ
        ≤ ∫⁻ x, ‖w n x - v n x‖ₑ + ‖v n x - u x‖ₑ ∂μ :=
          lintegral_mono fun x => by
            simpa only [sub_add_sub_cancel] using
              (enorm_add_le (a := w n x - v n x) (b := v n x - u x))
      _ = (∫⁻ x, ‖w n x - v n x‖ₑ ∂μ) + ∫⁻ x, ‖v n x - u x‖ₑ ∂μ :=
          lintegral_add_left' (hwi n).aestronglyMeasurable.enorm _
      _ ≤ _ := add_le_add (hk n).le le_rfl
  -- Lower semicontinuity and the upper estimate give equality in the limit.
  refine ⟨w, hw, hwlim, TauCeti.tendsto_totalVariationOn_of_le_add
    (fun n => (hw n).1.continuous.locallyIntegrable.locallyIntegrableOn ⊤)
    (hu.locallyIntegrable.locallyIntegrableOn ⊤) (fun K _ _ =>
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hwlim
        (fun _ => zero_le) (fun n => setLIntegral_le_lintegral _ _)) hb hwv⟩

end MeasureTheory.Integrable

namespace TauCeti

open Function TestFunction
open scoped Distributions

variable {Ω : Opens E}

omit [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure] in
/-- A piece `ζ u` of a function locally integrable on `Ω`, cut off by a smooth `ζ` compactly
supported in `Ω`, is integrable. -/
private theorem integrable_cutoff_mul (hu : LocallyIntegrableOn u Ω μ) {ζ : E → ℝ}
    (hζ : ContDiff ℝ ∞ ζ ∧ HasCompactSupport ζ ∧ tsupport ζ ⊆ Ω) :
    Integrable (fun y => ζ y * u y) μ := by
  simpa only [smul_eq_mul, mul_comm (u _)] using
    hu.integrable_smul_right_of_hasCompactSupport hζ.1.continuous hζ.2.1 hζ.2.2

omit [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure] in
/-- The gradient term `u Dζ` of a function locally integrable on `Ω` and a smooth `ζ` compactly
supported in `Ω` is integrable. -/
private theorem integrable_smul_fderiv_cutoff (hu : LocallyIntegrableOn u Ω μ) {ζ : E → ℝ}
    (hζ : ContDiff ℝ ∞ ζ ∧ HasCompactSupport ζ ∧ tsupport ζ ⊆ Ω) :
    Integrable (fun y => u y • fderiv ℝ ζ y) μ :=
  hu.integrable_smul_right_of_hasCompactSupport (hζ.1.continuous_fderiv (by simp))
    (hζ.2.1.mono' (support_fderiv_subset ℝ)) ((tsupport_fderiv_subset ℝ).trans hζ.2.2)

variable (μ u) in
/-- The `k`-th piece `ζ k u` of `u`, mollified by the shrinking bump of radius `1 / (n k + 1)`. -/
private def mollifiedPiece (ζ : ℕ → E → ℝ) (n : ℕ → ℕ) (k : ℕ) : E → ℝ :=
  (ContDiffBump.shrinking (c := (0 : E)) one_pos (n k)).normed μ ⋆[lsmul ℝ ℝ, μ]
    fun z => ζ k z * u z

/-- The mollified pieces of a function locally integrable on `Ω` are smooth. -/
private theorem contDiff_mollifiedPiece (hu : LocallyIntegrableOn u Ω μ) {ζ : ℕ → E → ℝ}
    (hζ : ∀ k, ContDiff ℝ ∞ (ζ k) ∧ HasCompactSupport (ζ k) ∧ tsupport (ζ k) ⊆ Ω) (n : ℕ → ℕ)
    (k : ℕ) : ContDiff ℝ ∞ (mollifiedPiece μ u ζ n k) := by
  rw [mollifiedPiece]
  exact (ContDiffBump.shrinking one_pos (n k)).hasCompactSupport_normed.contDiff_convolution_left _
    (ContDiffBump.shrinking one_pos (n k)).contDiff_normed
    (integrable_cutoff_mul hu (hζ k)).locallyIntegrable

omit [μ.IsAddHaarMeasure] in
/-- **The pairing estimate behind approximation on open sets.** Let `ζ k` be nonnegative smooth
functions compactly supported in `Ω` whose partial sums are at most one, and suppose that the
derivatives of the first `M` of them sum to zero on the support of a test vector field `φ` with
`‖φ‖ ≤ 1`. Translating the pieces `ζ k u` by arbitrary vectors `τ k`, their total pairing with
`div φ` exceeds the variation `|Du|(Ω)` by at most the `L¹` translation increments of the
functions `u Dζ k`. The pieces combine into the single test vector field `∑ k, ζ k φ(· + τ k)`;
the increments measure how far the translated gradient terms are from cancelling. -/
private theorem sum_integral_mul_comp_sub_le [μ.IsAddRightInvariant]
    (hu : LocallyIntegrableOn u Ω μ) (hT : totalVariationOn μ Ω u ≠ ⊤) {ζ : ℕ → E → ℝ}
    (hζ : ∀ k, ContDiff ℝ ∞ (ζ k) ∧ HasCompactSupport (ζ k) ∧ tsupport (ζ k) ⊆ Ω)
    (hζ0 : ∀ k x, 0 ≤ ζ k x) (hζ1 : ∀ N x, ∑ k ∈ Finset.range N, ζ k x ≤ 1)
    (φ : 𝓓(Ω, E)) (hφ : ∀ x, ‖φ x‖ ≤ 1) {M : ℕ}
    (hM : ∀ x ∈ tsupport φ, ∑ k ∈ Finset.range M, fderiv ℝ (ζ k) x = 0) (τ : ℕ → E) :
    ∑ k ∈ Finset.range M, ∫ x, divergenceCLM φ x * (ζ k (x - τ k) * u (x - τ k)) ∂μ ≤
      (totalVariationOn μ Ω u).toReal + ∑ k ∈ Finset.range M,
        ∫ x, ‖u (x - τ k) • fderiv ℝ (ζ k) (x - τ k) - u x • fderiv ℝ (ζ k) x‖ ∂μ := by
  set ψ := divergenceCLM φ
  have hφτ (k : ℕ) : Continuous (fun y => φ (y + τ k)) :=
    φ.continuous.comp (continuous_id.add continuous_const)
  have hDζ (k : ℕ) : Continuous (fderiv ℝ (ζ k)) := (hζ k).1.continuous_fderiv (by simp)
  -- Continuous functions supported in `tsupport (ζ k)` are integrable against `u`.
  have hsupp (k : ℕ) {c : E → ℝ} (hc : Continuous c) (hcs : support c ⊆ tsupport (ζ k)) :
      Integrable (fun y => u y • c y) μ :=
    hu.integrable_smul_right_of_hasCompactSupport hc ((hζ k).2.1.mono' hcs)
      ((closure_minimal hcs (isClosed_tsupport _)).trans (hζ k).2.2)
  have hDζs (k : ℕ) {v : E → E} : support (fun y => fderiv ℝ (ζ k) y (v y)) ⊆ tsupport (ζ k) :=
    fun y hy => support_fderiv_subset ℝ fun h0 => hy (by simp [h0])
  have hA (k : ℕ) : Integrable (fun y => u y * (ζ k y * ψ (y + τ k))) μ := by
    simpa only [smul_eq_mul] using hsupp k (c := fun y => ζ k y * ψ (y + τ k))
      ((hζ k).1.continuous.mul (ψ.continuous.comp (continuous_id.add continuous_const)))
      fun y hy => subset_tsupport _ (left_ne_zero_of_mul hy)
  have hB (k : ℕ) : Integrable (fun y => u y * fderiv ℝ (ζ k) y (φ (y + τ k))) μ := by
    simpa only [smul_eq_mul] using hsupp k ((hDζ k).clm_apply (hφτ k)) (hDζs k)
  have hC (k : ℕ) : Integrable (fun x => (u x • fderiv ℝ (ζ k) x) (φ x)) μ := by
    simpa only [smul_apply] using
      hsupp k ((hDζ k).clm_apply φ.continuous) (hDζs k)
  have hg (k : ℕ) : Integrable (fun y => u y • fderiv ℝ (ζ k) y) μ :=
    integrable_smul_fderiv_cutoff hu (hζ k)
  -- Translating each piece back moves the translation onto `div φ` and `φ`.
  have htrans (k : ℕ) : ∫ x, ψ x * (ζ k (x - τ k) * u (x - τ k)) ∂μ =
      ∫ y, u y * (ζ k y * ψ (y + τ k)) ∂μ := by
    rw [← integral_sub_right_eq_self (μ := μ) (fun y => u y * (ζ k y * ψ (y + τ k))) (τ k)]
    exact integral_congr_ae (.of_forall fun x => by simp only [sub_add_cancel]; ring)
  have hBtrans (k : ℕ) : ∫ y, u y * fderiv ℝ (ζ k) y (φ (y + τ k)) ∂μ =
      ∫ x, (u (x - τ k) • fderiv ℝ (ζ k) (x - τ k)) (φ x) ∂μ := by
    simp only [smul_apply, smul_eq_mul]
    rw [← integral_sub_right_eq_self (μ := μ) (fun y => u y * fderiv ℝ (ζ k) y (φ (y + τ k)))
      (τ k)]
    simp only [sub_add_cancel]
  -- The single test vector field `Φ = ∑ k, ζ k φ(· + τ k)` on `Ω`, of norm at most one.
  obtain ⟨Φ, -, hΦ1, hdiv⟩ := exists_testFunction_sum_smul_comp_add (fun k _ => hζ k)
    (fun k _ => hζ0 k) (hζ1 M) φ hφ τ
  have hTV : ∫ y, divergenceCLM Φ y * u y ∂μ ≤ (totalVariationOn μ Ω u).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hT).mp (ofReal_integral_le_totalVariationOn Φ hΦ1)
  have hsplit : ∫ y, divergenceCLM Φ y * u y ∂μ =
      ∑ k ∈ Finset.range M, ∫ y, u y * (ζ k y * ψ (y + τ k)) ∂μ +
        ∑ k ∈ Finset.range M, ∫ y, u y * fderiv ℝ (ζ k) y (φ (y + τ k)) ∂μ := by
    have h : (fun y => divergenceCLM Φ y * u y) = fun y =>
        (∑ k ∈ Finset.range M, u y * (ζ k y * ψ (y + τ k))) +
          ∑ k ∈ Finset.range M, u y * fderiv ℝ (ζ k) y (φ (y + τ k)) := by
      funext y
      rw [hdiv, Finset.sum_mul, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [h, integral_add (integrable_finsetSum _ fun k _ => hA k)
      (integrable_finsetSum _ fun k _ => hB k), integral_finsetSum _ fun k _ => hA k,
      integral_finsetSum _ fun k _ => hB k]
  -- Untranslated, the gradient terms cancel on the support of `φ`.
  have hzero : ∑ k ∈ Finset.range M, ∫ x, (u x • fderiv ℝ (ζ k) x) (φ x) ∂μ = 0 := by
    rw [← integral_finsetSum _ fun k _ => hC k]
    refine (integral_congr_ae (.of_forall fun x => ?_)).trans (integral_zero _ _)
    by_cases hx : x ∈ tsupport φ
    · simp only [smul_apply, smul_eq_mul, ← Finset.mul_sum,
        ← sum_apply, hM x hx, zero_apply, mul_zero]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  have hdiff (k : ℕ) : -(∫ x, (u (x - τ k) • fderiv ℝ (ζ k) (x - τ k)) (φ x) ∂μ -
      ∫ x, (u x • fderiv ℝ (ζ k) x) (φ x) ∂μ) ≤
        ∫ x, ‖u (x - τ k) • fderiv ℝ (ζ k) (x - τ k) - u x • fderiv ℝ (ζ k) x‖ ∂μ := by
    have hC' : Integrable (fun x => (u (x - τ k) • fderiv ℝ (ζ k) (x - τ k)) (φ x)) μ :=
      ((hB k).comp_sub_right (τ k)).congr (.of_forall fun x => by
        simp only [sub_add_cancel, smul_apply, smul_eq_mul])
    rw [← integral_sub hC' (hC k)]
    refine (neg_le_abs _).trans ?_
    rw [← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le (((hg k).comp_sub_right (τ k)).sub (hg k)).norm
      (.of_forall fun x => ?_)
    rw [← sub_apply]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_of_le_one_right (norm_nonneg _) (hφ x))
  have hgrad : -∑ k ∈ Finset.range M, ∫ y, u y * fderiv ℝ (ζ k) y (φ (y + τ k)) ∂μ ≤
      ∑ k ∈ Finset.range M,
        ∫ x, ‖u (x - τ k) • fderiv ℝ (ζ k) (x - τ k) - u x • fderiv ℝ (ζ k) x‖ ∂μ := by
    rw [Finset.sum_congr rfl fun k _ => hBtrans k, ← sub_zero (∑ k ∈ Finset.range M, _), ← hzero,
      ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun k _ => hdiff k
  rw [Finset.sum_congr rfl fun k _ => htrans k]
  linarith

/-- **The variation bound for the mollified pieces.** Suppose that the derivatives of the first
`M` pieces `ζ k` of a nonnegative decomposition of unity of `Ω` sum to zero on the support of a
test vector field `φ` with `‖φ‖ ≤ 1`, and that translating the gradient term `u Dζ k` by at most
`1 / (n k + 1)` changes it by at most `ε k` in `L¹`. Then pairing `div φ` with the first `M`
pieces `ζ k u` mollified at radii `1 / (n k + 1)` gives at most `|Du|(Ω) + ∑ k < M, ε k`. All the
mollifiers are rescalings of one kernel, so at each point of that kernel's support the translated
pieces combine into one test vector field. -/
private theorem sum_integral_mul_shrinking_convolution_le (hu : LocallyIntegrableOn u Ω μ)
    (hT : totalVariationOn μ Ω u ≠ ⊤) {ζ : ℕ → E → ℝ}
    (hζ : ∀ k, ContDiff ℝ ∞ (ζ k) ∧ HasCompactSupport (ζ k) ∧ tsupport (ζ k) ⊆ Ω)
    (hζ0 : ∀ k x, 0 ≤ ζ k x) (hζ1 : ∀ N x, ∑ k ∈ Finset.range N, ζ k x ≤ 1)
    (φ : 𝓓(Ω, E)) (hφ : ∀ x, ‖φ x‖ ≤ 1) {M : ℕ}
    (hM : ∀ x ∈ tsupport φ, ∑ k ∈ Finset.range M, fderiv ℝ (ζ k) x = 0) {n : ℕ → ℕ}
    {ε : ℕ → ℝ} (hn : ∀ k (τ : E), ‖τ‖ ≤ ((n k : ℝ) + 1)⁻¹ →
      ∫ x, ‖u (x - τ) • fderiv ℝ (ζ k) (x - τ) - u x • fderiv ℝ (ζ k) x‖ ∂μ ≤ ε k) :
    ∑ k ∈ Finset.range M, ∫ x, divergenceCLM φ x * mollifiedPiece μ u ζ n k x ∂μ ≤
      (totalVariationOn μ Ω u).toReal + ∑ k ∈ Finset.range M, ε k := by
  set ψ := divergenceCLM φ
  set T := (totalVariationOn μ Ω u).toReal
  set δ := ∑ k ∈ Finset.range M, ε k
  let ρn : ℕ → ContDiffBump (0 : E) := fun n => .shrinking one_pos n
  have hv (k : ℕ) : Integrable (fun z => ζ k z * u z) μ := integrable_cutoff_mul hu (hζ k)
  -- Each mollified piece is an average of translates, all with the same rescaled kernel `ρ`.
  let ρ : E → ℝ := (ρn 0).normed μ
  let J : ℕ → E → ℝ := fun k t => ∫ x, ψ x * (ζ k (x - t) * u (x - t)) ∂μ
  have hJ (k : ℕ) : Continuous (J k) := by
    have h : J k = ψ ⋆[lsmul ℝ ℝ, μ] fun z => ζ k (-z) * u (-z) := by
      funext t
      simp only [J, convolution_lsmul, smul_eq_mul, neg_sub]
    rw [h]
    exact ψ.hasCompactSupport.continuous_convolution_left _ ψ.continuous
      (hv k).comp_neg.locallyIntegrable
  have hterm (k : ℕ) : ∫ x, ψ x * mollifiedPiece μ u ζ n k x ∂μ =
      ∫ s, ρ s * J k (((n k : ℝ) + 1)⁻¹ • s) ∂μ := by
    rw [mollifiedPiece, integral_mul_convolution_eq_integral_mul_integral_comp_sub ψ.continuous
      ψ.hasCompactSupport (ρn (n k)).integrable_normed (ρn (n k)).hasCompactSupport_normed
      ((hv k).locallyIntegrable.locallyIntegrableOn univ) fun _ _ _ _ => mem_univ _]
    exact ContDiffBump.integral_shrinking_normed_mul one_pos (n k) (J k)
  have hint (k : ℕ) : Integrable (fun s => ρ s * J k (((n k : ℝ) + 1)⁻¹ • s)) μ :=
    ((ρn 0).continuous_normed.mul
      ((hJ k).comp (continuous_const_smul _))).integrable_of_hasCompactSupport
        (ρn 0).hasCompactSupport_normed.mul_right
  -- For each point of the kernel's support the translates combine into one test field.
  have hbound (s : E) : ρ s * ∑ k ∈ Finset.range M, J k (((n k : ℝ) + 1)⁻¹ • s) ≤
      ρ s * (T + δ) := by
    rcases eq_or_ne (ρ s) 0 with hs | hs
    · simp [hs]
    refine mul_le_mul_of_nonneg_left ?_ ((ρn 0).nonneg_normed s)
    have hs1 : ‖s‖ < 1 := by
      have hmem : s ∈ support ρ := hs
      rw [ContDiffBump.support_normed_eq, mem_ball_zero_iff] at hmem
      simpa [ρn, ContDiffBump.rOut_shrinking] using hmem
    refine (sum_integral_mul_comp_sub_le hu hT hζ hζ0 hζ1 φ hφ hM
      fun k => ((n k : ℝ) + 1)⁻¹ • s).trans (add_le_add_right ?_ _)
    exact Finset.sum_le_sum fun k _ => hn k _ (by
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      exact mul_le_of_le_one_right (by positivity) hs1.le)
  rw [Finset.sum_congr rfl fun k _ => hterm k,
    ← integral_finsetSum (f := fun k s => ρ s * J k (((n k : ℝ) + 1)⁻¹ • s)) _
      fun k _ => hint k]
  calc ∫ s, ∑ k ∈ Finset.range M, ρ s * J k (((n k : ℝ) + 1)⁻¹ • s) ∂μ
      ≤ ∫ s, ρ s * (T + δ) ∂μ :=
        integral_mono (integrable_finsetSum _ fun k _ => hint k)
          ((ρn 0).integrable_normed.mul_const _) fun s => by
            rw [← Finset.mul_sum]
            exact hbound s
    _ = T + δ := by rw [integral_mul_const, (ρn 0).integral_normed, one_mul]

/-- A radius `1 / (n + 1)`, with `n` at least a given `k`, for which mollifying an integrable `v`
costs at most `ε` in `L¹` and translating an integrable `g` by at most the radius changes it by at
most `ε` in `L¹`. -/
private theorem exists_shrinking_radius {F : Type*} [NormedAddCommGroup F] (k : ℕ) {v : E → ℝ}
    (hv : Integrable v μ) {g : E → F} (hg : Integrable g μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ n, k ≤ n ∧
      ∫⁻ x, ‖((ContDiffBump.shrinking (c := (0 : E)) one_pos n).normed μ ⋆[lsmul ℝ ℝ, μ] v) x -
        v x‖ₑ ∂μ ≤ ENNReal.ofReal ε ∧
      ∀ τ : E, ‖τ‖ ≤ ((n : ℝ) + 1)⁻¹ → ∫ x, ‖g (x - τ) - g x‖ ∂μ ≤ ε := by
  have hL1 := tendsto_lintegral_enorm_normed_convolution_sub (mu := μ)
    (ContDiffBump.tendsto_rOut_shrinking (c := (0 : E)) one_pos) hv
  have htr := hg.tendsto_integral_norm_translate_sub (c := id) (b := (0 : E)) tendsto_id
  simp only [id, sub_zero] at htr
  obtain ⟨r, hr, hr'⟩ := Metric.eventually_nhds_iff.mp (htr.eventually (ge_mem_nhds hε))
  have hsmall : ∀ᶠ n : ℕ in atTop, ((n : ℝ) + 1)⁻¹ < r := by
    simpa only [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds hr)
  obtain ⟨n, hkn, hnv, hnr⟩ := ((eventually_ge_atTop k).and
    ((hL1.eventually (ge_mem_nhds (ENNReal.ofReal_pos.2 hε))).and hsmall)).exists
  exact ⟨n, hkn, hnv, fun τ hτ => hr' (by rw [dist_zero_right]; exact hτ.trans_lt hnr)⟩

/-- Mollifying the pieces `ζ k u` of a locally finite decomposition of unity of `Ω` at radii
`1 / (n k + 1) ≤ 1 / (k + 1)` keeps their sum locally finite: near each point of `Ω` only finitely
many of the mollified pieces are nonzero, while the `ζ k` sum to one. -/
private theorem exists_eventually_shrinking_convolution_eq_zero {ζ χ : ℕ → E → ℝ}
    (hχζ : ∀ k, EqOn (χ k) 1 (tsupport (ζ k)))
    (hfin : ∀ x ∈ (Ω : Set E), ∃ m, ∀ᶠ y in 𝓝 x, (∀ k, m ≤ k → χ k y = 0) ∧
      ∀ N, m ≤ N → ∑ j ∈ Finset.range N, ζ j y = 1)
    {n : ℕ → ℕ} (hkn : ∀ k, k ≤ n k) {x : E} (hx : x ∈ Ω) :
    ∃ m, ∀ᶠ y in 𝓝 x, (∀ k, m ≤ k → mollifiedPiece μ u ζ n k y = 0) ∧
      ∀ N, m ≤ N → ∑ j ∈ Finset.range N, ζ j y = 1 := by
  obtain ⟨m₀, hm₀⟩ := hfin x hx
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hm₀
  obtain ⟨K, hK⟩ := exists_nat_one_div_lt (half_pos hr)
  refine ⟨max m₀ K, ?_⟩
  filter_upwards [Metric.ball_mem_nhds x (half_pos hr)] with y hy
  refine ⟨fun k hk => ?_, fun N hN =>
    (hball y (ball_subset_ball (by linarith) hy)).2 N (le_of_max_le_left hN)⟩
  by_contra hne
  rw [mollifiedPiece] at hne
  obtain ⟨a, ha, b, hb, rfl⟩ := support_convolution_subset (lsmul ℝ ℝ) hne
  rw [ContDiffBump.support_normed_eq, mem_ball_zero_iff, ContDiffBump.rOut_shrinking] at ha
  have hbζ : b ∈ tsupport (ζ k) := subset_tsupport _ fun h => hb (by simp [h])
  have hra : ‖a‖ < r / 2 := ha.trans_le <| ((Nat.one_div_le_one_div
    ((le_of_max_le_right hk).trans (hkn k))).trans_lt hK).le
  have hb' : b ∈ ball x r := by
    rw [mem_ball] at hy ⊢
    calc dist b x ≤ dist b (a + b) + dist (a + b) x := dist_triangle _ _ _
      _ < r / 2 + r / 2 := by
        gcongr
        simpa [dist_eq_norm] using hra
      _ = r := add_halves r
  have h1 := hχζ k hbζ
  rw [(hball b hb').1 k (le_of_max_le_left hk)] at h1
  exact zero_ne_one h1

/-- **The variation of the glued approximation.** Let `ζ k` be nonnegative smooth functions
compactly supported in `Ω` whose partial sums are at most one, and mollify the pieces `ζ k u` at
radii `1 / (n k + 1)`. Suppose that near each point of `Ω` only finitely many mollified pieces are
nonzero while the `ζ k` sum to one, and that translating the gradient term `u Dζ k` by at most
`1 / (n k + 1)` changes it by at most `ε k` in `L¹`, where the `ε k ≥ 0` sum to `δ`. Then the sum
of the mollified pieces has variation on `Ω` at most `|Du|(Ω) + δ`. -/
private theorem totalVariationOn_tsum_shrinking_convolution_le
    (hu : LocallyIntegrableOn u Ω μ) {ζ : ℕ → E → ℝ}
    (hζ : ∀ k, ContDiff ℝ ∞ (ζ k) ∧ HasCompactSupport (ζ k) ∧ tsupport (ζ k) ⊆ Ω)
    (hζ0 : ∀ k x, 0 ≤ ζ k x) (hζ1 : ∀ N x, ∑ k ∈ Finset.range N, ζ k x ≤ 1) {n : ℕ → ℕ}
    (hloc : ∀ x ∈ Ω, ∃ m, ∀ᶠ y in 𝓝 x, (∀ k, m ≤ k → mollifiedPiece μ u ζ n k y = 0) ∧
      ∀ N, m ≤ N → ∑ j ∈ Finset.range N, ζ j y = 1)
    {ε : ℕ → ℝ} {δ : ℝ} (hε : ∀ k, 0 ≤ ε k) (hεδ : HasSum ε δ)
    (hng : ∀ k (τ : E), ‖τ‖ ≤ ((n k : ℝ) + 1)⁻¹ →
      ∫ x, ‖u (x - τ) • fderiv ℝ (ζ k) (x - τ) - u x • fderiv ℝ (ζ k) x‖ ∂μ ≤ ε k) :
    totalVariationOn μ Ω (fun x => ∑' k, mollifiedPiece μ u ζ n k x) ≤
      totalVariationOn μ Ω u + ENNReal.ofReal δ := by
  set f : ℕ → E → ℝ := mollifiedPiece μ u ζ n with hf_def
  have hf (k : ℕ) : ContDiff ℝ ∞ (f k) := contDiff_mollifiedPiece hu hζ n k
  set w : E → ℝ := fun x => ∑' k, f k x
  by_cases hT : totalVariationOn μ Ω u = ⊤
  · simp [hT]
  refine totalVariationOn_le_iff.mpr fun φ hφ => ?_
  set ψ := divergenceCLM φ
  -- A single index `M` works on the whole support of `φ`.
  let P : ℕ → Set E := fun m => {y | ∀ᶠ z in 𝓝 y,
    (∀ k, m ≤ k → f k z = 0) ∧ ∀ N, m ≤ N → ∑ j ∈ Finset.range N, ζ j z = 1}
  have hPmono : Monotone P := fun m m' hmm' y hy => hy.mono fun z hz =>
    ⟨fun k hk => hz.1 k (hmm'.trans hk), fun N hN => hz.2 N (hmm'.trans hN)⟩
  obtain ⟨M, hM⟩ := φ.hasCompactSupport.isCompact.elim_directed_cover P
    (fun m => isOpen_setOfPred_eventually_nhds) (fun y hy => by
      obtain ⟨m, hm⟩ := hloc y (φ.tsupport_subset hy)
      exact mem_iUnion.2 ⟨m, hm⟩) hPmono.directed_le
  have hDζ (y : E) (hy : y ∈ tsupport φ) : ∑ k ∈ Finset.range M, fderiv ℝ (ζ k) y = 0 := by
    have h1 : (fun z => ∑ k ∈ Finset.range M, ζ k z) =ᶠ[𝓝 y] fun _ => 1 :=
      (hM hy).mono fun z hz => hz.2 M le_rfl
    rw [← fderiv_fun_sum fun k _ => ((hζ k).1.differentiable (by simp)) y, h1.fderiv_eq,
      fderiv_const_apply]
  -- The pairing with `w` is a finite sum of pairings with the mollified pieces.
  have hpair : ∫ x, ψ x * w x ∂μ = ∑ k ∈ Finset.range M, ∫ x, ψ x * f k x ∂μ := by
    rw [← integral_finsetSum (f := fun k x => ψ x * f k x) _ fun k _ =>
      (ψ.continuous.mul (hf k).continuous).integrable_of_hasCompactSupport
        ψ.hasCompactSupport.mul_right]
    refine integral_congr_ae (.of_forall fun x => ?_)
    by_cases hx : x ∈ tsupport φ
    · simp only [w, ← Finset.mul_sum]
      rw [tsum_eq_sum (s := Finset.range M) fun k hk =>
        (hM hx).self_of_nhds.1 k (by simpa using hk)]
    · have hψx : ψ x = 0 := by
        simp [ψ, divergenceCLM_apply, fderiv_of_notMem_tsupport ℝ hx]
      simp [hψx]
  have hεM : ∑ k ∈ Finset.range M, ε k ≤ δ :=
    (hεδ.summable.sum_le_tsum _ fun k _ => hε k).trans_eq hεδ.tsum_eq
  have hle : ∫ x, ψ x * w x ∂μ ≤ (totalVariationOn μ Ω u).toReal + δ := by
    rw [hpair, hf_def]
    exact (sum_integral_mul_shrinking_convolution_le hu hT hζ hζ0 hζ1 φ hφ hDζ hng).trans
      (add_le_add_right hεM _)
  calc ENNReal.ofReal (∫ x, ψ x * w x ∂μ)
      ≤ ENNReal.ofReal ((totalVariationOn μ Ω u).toReal + δ) := ENNReal.ofReal_le_ofReal hle
    _ = totalVariationOn μ Ω u + ENNReal.ofReal δ := by
        rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (hεδ.nonneg hε), ENNReal.ofReal_toReal hT]

/-- A function locally integrable on an open set `Ω` is, for every `δ > 0`, within `δ` in
`L¹(Ω)` of a function smooth on `Ω` whose variation on `Ω` exceeds that of `u` by at most `δ`.
The approximation is `∑ k, ρ_k ⋆ (ζ k u)` for a nonnegative decomposition of unity `(ζ k)` of `Ω`
and mollifiers `ρ_k`, which are rescalings of one kernel with radii chosen piece by piece. -/
private theorem exists_contDiffOn_lintegral_le_totalVariationOn_le
    (hu : LocallyIntegrableOn u Ω μ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ w : E → ℝ, ContDiffOn ℝ ∞ w Ω ∧ ∫⁻ x in Ω, ‖w x - u x‖ₑ ∂μ ≤ ENNReal.ofReal δ ∧
      totalVariationOn μ Ω w ≤ totalVariationOn μ Ω u + ENNReal.ofReal δ := by
  obtain ⟨ζ, χ, hζ, hζ0, hζ1, -, hχζ, hfin⟩ := Ω.isOpen.exists_contDiff_decomposition_cutoff
  -- The pieces `ζ k u` and the gradient terms `u Dζ k` are integrable.
  have hv (k : ℕ) : Integrable (fun y => ζ k y * u y) μ := integrable_cutoff_mul hu (hζ k)
  have hg (k : ℕ) : Integrable (fun y => u y • fderiv ℝ (ζ k) y) μ :=
    integrable_smul_fderiv_cutoff hu (hζ k)
  have hε (k : ℕ) : 0 < δ / 2 / 2 ^ k := by positivity
  -- For each piece choose a mollification radius `1 / (n k + 1) ≤ 1 / (k + 1)` controlling both
  -- the `L¹` error of the piece and the translation increments of its gradient term.
  have hchoice (k : ℕ) := exists_shrinking_radius (μ := μ) k (hv k) (hg k) (hε k)
  choose n hkn hnv hng using hchoice
  have hf (k : ℕ) : ContDiff ℝ ∞ (mollifiedPiece μ u ζ n k) := contDiff_mollifiedPiece hu hζ n k
  -- Near each point of `Ω` only finitely many mollified pieces are nonzero, and the `ζ k` sum
  -- to one.
  have hloc (x : E) (hx : x ∈ Ω) : ∃ m, ∀ᶠ y in 𝓝 x,
      (∀ k, m ≤ k → mollifiedPiece μ u ζ n k y = 0) ∧
        ∀ N, m ≤ N → ∑ j ∈ Finset.range N, ζ j y = 1 :=
    exists_eventually_shrinking_convolution_eq_zero hχζ hfin hkn hx
  refine ⟨fun x => ∑' k, mollifiedPiece μ u ζ n k x, fun x hx => ?_, ?_,
    totalVariationOn_tsum_shrinking_convolution_le hu hζ hζ0 hζ1 hloc (fun k => (hε k).le)
      (hasSum_geometric_two' δ) hng⟩
  · obtain ⟨m, hm⟩ := hloc x hx
    refine (contDiffAt_tsum_of_eventually_eq_zero (Finset.range m)
      (fun k _ => (hf k).contDiffAt) (hm.mono fun y hy k hk => ?_)).contDiffWithinAt
    exact hy.1 k (by simpa using hk)
  -- The `L¹` error is at most the sum of the errors of the pieces.
  have hpt (x : E) (hx : x ∈ (Ω : Set E)) : ‖∑' k, mollifiedPiece μ u ζ n k x - u x‖ₑ ≤
      ∑' k, ‖mollifiedPiece μ u ζ n k x - ζ k x * u x‖ₑ := by
    obtain ⟨m, hm⟩ := hloc x hx
    have hwx : ∑' k, mollifiedPiece μ u ζ n k x =
        ∑ k ∈ Finset.range m, mollifiedPiece μ u ζ n k x :=
      tsum_eq_sum fun k hk => hm.self_of_nhds.1 k (by simpa using hk)
    have hux : ∑ k ∈ Finset.range m, ζ k x * u x = u x := by
      simp only [← Finset.sum_mul, hm.self_of_nhds.2 m le_rfl, one_mul]
    have hsum : ∑' k, mollifiedPiece μ u ζ n k x - u x =
        ∑ k ∈ Finset.range m, (mollifiedPiece μ u ζ n k x - ζ k x * u x) := by
      rw [hwx, Finset.sum_sub_distrib, hux]
    rw [hsum]
    exact (enorm_sum_le _ _).trans (sum_le_tsum _)
  calc ∫⁻ x in Ω, ‖∑' k, mollifiedPiece μ u ζ n k x - u x‖ₑ ∂μ
      ≤ ∫⁻ x in Ω, ∑' k, ‖mollifiedPiece μ u ζ n k x - ζ k x * u x‖ₑ ∂μ :=
        setLIntegral_mono' Ω.isOpen.measurableSet hpt
    _ ≤ ∫⁻ x, ∑' k, ‖mollifiedPiece μ u ζ n k x - ζ k x * u x‖ₑ ∂μ :=
        setLIntegral_le_lintegral _ _
    _ = ∑' k, ∫⁻ x, ‖mollifiedPiece μ u ζ n k x - ζ k x * u x‖ₑ ∂μ :=
        lintegral_tsum fun k => ((hf k).continuous.aestronglyMeasurable.sub
          (hv k).aestronglyMeasurable).enorm
    _ ≤ ∑' k, ENNReal.ofReal (δ / 2 / 2 ^ k) :=
        tsum_le_tsum fun k => by simpa only [mollifiedPiece] using hnv k
    _ = ENNReal.ofReal δ := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => (hε k).le) (summable_geometric_two' δ),
          tsum_geometric_two']

end TauCeti

namespace MeasureTheory.LocallyIntegrableOn

variable {Ω : Opens E}

/-- **Strict approximation on an open set.** A function `u` locally integrable on an arbitrary
open set `Ω` is the limit of functions `w n` smooth on `Ω` with `∫_Ω |w n - u| → 0` and
`|D(w n)|(Ω) → |Du|(Ω)`. For `u ∈ BV(Ω)` this is strict approximation; the variation limit also
holds when `|Du|(Ω)` is infinite. No integrability of `u` on `Ω`, boundedness of `Ω` or regularity
of its boundary is assumed, and the approximations need not be smooth up to the boundary. -/
theorem exists_contDiffOn_strict_approximation (hu : LocallyIntegrableOn u Ω μ) :
    ∃ w : ℕ → E → ℝ, (∀ n, ContDiffOn ℝ ∞ (w n) Ω) ∧
      Tendsto (fun n => ∫⁻ x in Ω, ‖w n x - u x‖ₑ ∂μ) atTop (𝓝 0) ∧
      Tendsto (fun n => TauCeti.totalVariationOn μ Ω (w n)) atTop
        (𝓝 (TauCeti.totalVariationOn μ Ω u)) := by
  choose w hw hwL hwV using fun n : ℕ =>
    TauCeti.exists_contDiffOn_lintegral_le_totalVariationOn_le hu (δ := 1 / (n + 1))
      (by positivity)
  have hzero : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / (n + 1))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
  have hL : Tendsto (fun n => ∫⁻ x in Ω, ‖w n x - u x‖ₑ ∂μ) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hzero (fun _ => zero_le) hwL
  refine ⟨w, hw, hL, TauCeti.tendsto_totalVariationOn_of_le_add
    (fun n => (hw n).continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet) hu
    (fun K _ hKΩ => tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hL
      (fun _ => zero_le) fun _ => lintegral_mono_set hKΩ) hzero hwV⟩

/-- **Strict approximation on an open set, with gradients.** A function `u` locally integrable on
an arbitrary open set `Ω` is the limit of functions `w n` smooth on `Ω` with
`∫_Ω |w n - u| → 0` and `∫_Ω ‖∇(w n)‖ → |Du|(Ω)`, finite or infinite. -/
theorem exists_contDiffOn_tendsto_setLIntegral_enorm_fderiv (hu : LocallyIntegrableOn u Ω μ) :
    ∃ w : ℕ → E → ℝ, (∀ n, ContDiffOn ℝ ∞ (w n) Ω) ∧
      Tendsto (fun n => ∫⁻ x in Ω, ‖w n x - u x‖ₑ ∂μ) atTop (𝓝 0) ∧
      Tendsto (fun n => ∫⁻ x in Ω, ‖fderiv ℝ (w n) x‖ₑ ∂μ) atTop
        (𝓝 (TauCeti.totalVariationOn μ Ω u)) := by
  obtain ⟨w, hw, hL, hV⟩ := hu.exists_contDiffOn_strict_approximation
  refine ⟨w, hw, hL, hV.congr fun n => ?_⟩
  refine LocallyLipschitzOn.totalVariationOn_eq_setLIntegral_enorm_fderiv fun x hx => ?_
  obtain ⟨K, t, ht, hK⟩ :=
    (((hw n).contDiffAt (Ω.isOpen.mem_nhds hx)).of_le (by simp)).exists_lipschitzOnWith
  exact ⟨K, t, mem_nhdsWithin_of_mem_nhds ht, hK⟩

end MeasureTheory.LocallyIntegrableOn
