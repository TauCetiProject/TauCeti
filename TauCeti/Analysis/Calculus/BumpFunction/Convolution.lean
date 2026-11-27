/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Topology.MetricSpace.Lipschitz
public import TauCeti.Analysis.Calculus.ContDiff.Convolution

import Mathlib.Analysis.Convex.Integral
import TauCeti.Algebra.Order.Field.Basic
import TauCeti.Analysis.Calculus.BumpFunction.Normed
import TauCeti.Analysis.Calculus.BumpFunction.Rescale
import TauCeti.Analysis.Convolution.Basic
import TauCeti.Analysis.Convolution.Holder
import TauCeti.MeasureTheory.Integral.Bochner.Basic

/-!
# Uniform approximation by normalized bumps

Convolution with normalized smooth bumps whose radii tend to zero converges uniformly to
any uniformly continuous Banach-valued function, and uniformly on a set `s` to a function that is
uniformly continuous on a neighbourhood of `s`. For uniformly continuous functions, this
upgrades the pointwise convergence of Mathlib's
`ContDiffBump.convolution_tendsto_right_of_continuous` to uniform convergence, and allows
simultaneous approximation of the derivatives of a compactly supported smooth function.
Mollifying a locally integrable function by a normalized bump gives a smooth function
(`ContDiffBump.contDiff_normed_convolution`).
Normalized-bump convolution also preserves an almost-everywhere bound on a function
(`ContDiffBump.norm_normed_convolution_le`), a uniform `L²`-product bound on a pair of functions
(`ContDiffBump.norm_normed_convolution_sq_add_norm_normed_convolution_sq_le`), and its Lipschitz
constant, since it averages the differences of translates
(`ContDiffBump.dist_normed_convolution_le_of_dist_sub_le`).
For `K`-Lipschitz data, the pointwise approximation error is at most `K * ρ.rOut`
(`LipschitzWith.dist_normed_convolution_le`).
The convolution at a point only reads the function on the ball of radius `ρ.rOut` around it
(`ContDiffBump.normed_convolution_eq_of_eqOn`), so it commutes with every available derivative
of a `C^N` function, with no support or growth condition
(`ContDiffBump.iteratedFDeriv_normed_convolution`).

Integrals against the mollifications of a uniformly continuous function converge, along any filter
of bump indices with radii tending to zero, to the integral against the function
(`ContDiffBump.tendsto_integral_normed_convolution_smul`).

Along an arbitrary filter of bump indices, convolution with normalized bumps also converges
uniformly on a neighbourhood filter of a point of continuity of the function.

The file also bounds the topological support of `ρ.normed μ ⋆ g` by the Minkowski sum
`closedBall 0 ρ.rOut + tsupport g`, and provides the standard shrinking sequence of bumps
`ContDiffBump.shrinking`, of radii `R / (n + 1)` and `R / (2 * (n + 1))`. These bumps are all
rescalings of the first one (`ContDiffBump.shrinking_apply_eq`), so integrals against their
normalized forms reduce to one kernel (`ContDiffBump.integral_shrinking_normed_mul`).
Integrating a function `H` on a product `X × G` against these bumps in the second variable
tends to the integral of `H (·, 0)` when `H` is continuous near `X × {0}` and vanishes for the
first variable outside a compact set (`ContDiffBump.tendsto_integral_shrinking_normed_smul`).
Mollifying a continuous function `h` with `‖h‖ ≤ M` along these bumps approximates it in `L¹` of
any finite measure by smooth functions with `‖ψ‖ ≤ M`, supported in a given closed thickening of
the support of `h` (`Continuous.exists_contDiff_norm_le_lintegral_sub_le`).

## References

* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public section

open ContinuousLinearMap MeasureTheory Filter Metric
open scoped Convolution Topology Pointwise NNReal ENNReal ContDiff

namespace ContDiffBump

section Shrinking

variable {X : Type*} {c : X} {R : ℝ}

/-- The bumps of outer radius `R / (n + 1)` and inner radius half of that. Their radii shrink to
zero while the outer radius stays twice the inner one, as Lebesgue differentiation along
normalized bump convolutions requires. -/
noncomputable def shrinking (hR : 0 < R) (n : ℕ) : ContDiffBump c where
  rIn := R / (2 * (n + 1))
  rOut := R / (n + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := div_lt_div_of_pos_left hR (by positivity) (by linarith)

/-- The inner radius of `ContDiffBump.shrinking`. -/
@[simp]
theorem rIn_shrinking (hR : 0 < R) (n : ℕ) :
    (shrinking hR n : ContDiffBump c).rIn = R / (2 * (n + 1)) :=
  (rfl)

/-- The outer radius of `ContDiffBump.shrinking`. -/
@[simp]
theorem rOut_shrinking (hR : 0 < R) (n : ℕ) :
    (shrinking hR n : ContDiffBump c).rOut = R / (n + 1) :=
  (rfl)

/-- The outer radius of `ContDiffBump.shrinking` is at most `R`. -/
theorem rOut_shrinking_le (hR : 0 < R) (n : ℕ) :
    (shrinking hR n : ContDiffBump c).rOut ≤ R := by
  rw [rOut_shrinking]
  exact div_le_self hR.le (by simp)

/-- The outer radius of `ContDiffBump.shrinking` is twice its inner radius. -/
theorem rOut_shrinking_eq_two_mul_rIn (hR : 0 < R) (n : ℕ) :
    (shrinking hR n : ContDiffBump c).rOut = 2 * (shrinking hR n : ContDiffBump c).rIn := by
  simp only [rOut_shrinking, rIn_shrinking]
  field_simp

/-- The radii of `ContDiffBump.shrinking` tend to zero. -/
theorem tendsto_rOut_shrinking (hR : 0 < R) :
    Tendsto (fun n : ℕ => (shrinking hR n : ContDiffBump c).rOut) atTop (𝓝 0) := by
  simp only [rOut_shrinking]
  exact tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)

/-- On a relatively compact open subdomain, a shrinking sequence of normalized bump kernels
has every translated support inside the ambient open domain. -/
theorem exists_seq_sub_tsupport_subset {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [μ.IsAddHaarMeasure] {W Ω : TopologicalSpace.Opens E}
    (hWc : IsCompact (closure (W : Set E))) (hWΩ : closure (W : Set E) ⊆ Ω) :
    ∃ φ : ℕ → ContDiffBump (0 : E),
      Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) ∧
      ∀ n x, x ∈ (W : Set E) → ∀ y ∈ tsupport ((φ n).normed μ), x - y ∈ Ω := by
  obtain ⟨δ, hδ, hδΩ⟩ := hWc.exists_cthickening_subset_open Ω.isOpen hWΩ
  refine ⟨shrinking hδ, tendsto_rOut_shrinking hδ, ?_⟩
  intro n x hx y hy
  rw [(shrinking hδ n).tsupport_normed_eq, mem_closedBall, dist_zero_right] at hy
  refine hδΩ (mem_cthickening_of_dist_le _ x δ _ (subset_closure hx) ?_)
  rw [dist_eq_norm, sub_sub_cancel_left, norm_neg]
  exact hy.trans (rOut_shrinking_le hδ n)

/-- `ContDiffBump.shrinking hR n` is `ContDiffBump.shrinking hR 0` rescaled by the factor `n + 1`,
so all the bumps of the sequence are rescalings of one kernel. -/
theorem shrinking_apply_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [HasContDiffBump E] (hR : 0 < R) (n : ℕ) (x : E) :
    (shrinking hR n : ContDiffBump (0 : E)) x =
      (shrinking hR 0 : ContDiffBump (0 : E)) (((n : ℝ) + 1) • x) := by
  rw [apply_eq_apply_smul_of_rOut_div_rIn_eq _ (shrinking hR 0)
    (by simp only [rOut_shrinking, rIn_shrinking]; field_simp)]
  congr 2
  simp only [rIn_shrinking]
  field_simp
  norm_num

end Shrinking

variable {G F : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [FiniteDimensional ℝ G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G}
  [NormedAddCommGroup F] [NormedSpace ℝ F] {g : G → F}

/-- The support of a normalized-bump convolution lies in the closed radius-neighborhood
of the support of the other factor, expressed as a Minkowski sum. -/
theorem tsupport_normed_convolution_subset [IsLocallyFiniteMeasure μ] [μ.IsOpenPosMeasure]
    (ρ : ContDiffBump (0 : G)) :
    tsupport (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] g) ⊆ closedBall 0 ρ.rOut + tsupport g := by
  apply closure_minimal
  · exact (support_convolution_subset _).trans
      (Set.add_subset_add (ρ.support_normed_eq.subset.trans ball_subset_closedBall) subset_closure)
  · exact (isClosed_tsupport g).add_left_of_isCompact (isCompact_closedBall _ _)

/-- Mollifying a locally integrable function by a normalized bump gives a smooth function. -/
theorem contDiff_normed_convolution [μ.IsAddHaarMeasure] (ρ : ContDiffBump (0 : G))
    (hg : LocallyIntegrable g μ) {n : ℕ∞} : ContDiff ℝ n (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] g) :=
  ρ.hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ) ρ.contDiff_normed hg

variable [μ.IsAddHaarMeasure] [CompleteSpace F]

/-- Integrating against the normalized bump `ContDiffBump.shrinking hR n` is integrating against
the normalized bump `ContDiffBump.shrinking hR 0` after rescaling the variable by `(n + 1)⁻¹`. -/
theorem integral_shrinking_normed_mul {R : ℝ} (hR : 0 < R) (n : ℕ) (f : G → ℝ) :
    ∫ t, (shrinking (c := (0 : G)) hR n).normed μ t * f t ∂μ =
      ∫ s, (shrinking (c := (0 : G)) hR 0).normed μ s * f (((n : ℝ) + 1)⁻¹ • s) ∂μ := by
  set S : ℝ := (n : ℝ) + 1
  have hS : 0 < S := by positivity
  set d := Module.finrank ℝ G
  have hc : (shrinking (c := (0 : G)) hR 0).rIn / (shrinking (c := (0 : G)) hR n).rIn = S := by
    simp only [rIn_shrinking, S]
    field_simp
    norm_num
  set g : G → ℝ := fun s => S ^ d * ((shrinking (c := (0 : G)) hR 0).normed μ s * f (S⁻¹ • s))
  have hg (t : G) : (shrinking (c := (0 : G)) hR n).normed μ t * f t = g (S • t) := by
    rw [normed_eq_mul_normed_smul_of_rOut_div_rIn_eq _ (shrinking hR 0)
      (by simp only [rOut_shrinking, rIn_shrinking]; field_simp), hc]
    simp only [g, inv_smul_smul₀ hS.ne']
    ring
  calc ∫ t, (shrinking (c := (0 : G)) hR n).normed μ t * f t ∂μ = ∫ t, g (S • t) ∂μ :=
        integral_congr_ae (.of_forall hg)
    _ = (S ^ d)⁻¹ • ∫ s, g s ∂μ := Measure.integral_comp_smul_of_nonneg μ g S (hR := hS.le)
    _ = _ := by
        simp only [g, smul_eq_mul, integral_const_mul]
        field_simp

/-- **Shrinking bumps in the second factor of a product.** Let `H : X × G → F` be continuous on
`X × ball 0 δ` and vanish for `x` outside a compact set. For the normalized bumps `ρ_n` of
`ContDiffBump.shrinking (δ / 2)`, `∫ ρ_n (y) • H (x, y) d(x, y) → ∫ H (x, 0) dx`. This is the
convergence `ρ_n ⋆ g → g` at `0` (`ContDiffBump.convolution_tendsto_right`) of the function
`g y = ∫ H (x, -y) dx`, which is continuous near `0`. -/
theorem tendsto_integral_shrinking_normed_smul {X : Type*} [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [OpensMeasurableSpace X] {ν : Measure X} [IsFiniteMeasureOnCompacts ν]
    [SFinite ν] {H : X × G → F} {k : Set X} (hk : IsCompact k)
    (hHk : ∀ x y, x ∉ k → H (x, y) = 0) {δ : ℝ} (hδ : 0 < δ)
    (hH : ContinuousOn H (Set.univ ×ˢ ball (0 : G) δ)) :
    Tendsto (fun n ↦ ∫ q, (shrinking (c := (0 : G)) (half_pos hδ) n).normed μ q.2 • H q ∂ν.prod μ)
      atTop (𝓝 (∫ x, H (x, 0) ∂ν)) := by
  set ρ : ℕ → ContDiffBump (0 : G) := shrinking (half_pos hδ)
  have hball : closedBall (0 : G) (δ / 2) ⊆ ball 0 δ := closedBall_subset_ball (half_lt_self hδ)
  -- `g y = ∫ H (x, -y) dx` is continuous on `closedBall 0 (δ / 2)`.
  set g : G → F := fun y ↦ ∫ x, H (x, -y) ∂ν
  have hg : ContinuousOn g (closedBall 0 (δ / 2)) :=
    continuousOn_integral_of_compact_support (f := fun y x ↦ H (x, -y)) hk
      (hH.comp (continuous_snd.prodMk continuous_fst.neg).continuousOn fun q hq ↦
        ⟨Set.mem_univ _, hball (by simpa using hq.1)⟩) fun y x _ hx ↦ hHk x _ hx
  set g₀ := (closedBall (0 : G) (δ / 2)).indicator g
  have hG0 : ContinuousAt g₀ 0 := (hg.continuousAt (closedBall_mem_nhds _ (half_pos hδ))).congr
    (eventuallyEq_of_mem (closedBall_mem_nhds _ (half_pos hδ)) fun y hy ↦
      (Set.indicator_of_mem hy g).symm)
  have hconv := convolution_tendsto_right (μ := μ) (φ := ρ) (g := fun _ ↦ g₀)
    (k := fun _ ↦ 0) (tendsto_rOut_shrinking _) (Eventually.of_forall fun _ ↦
      (aestronglyMeasurable_indicator_iff measurableSet_closedBall).2
        (hg.aestronglyMeasurable measurableSet_closedBall)) (hG0.tendsto.comp tendsto_snd)
    tendsto_const_nhds
  rw [show g₀ 0 = ∫ x, H (x, 0) ∂ν by
    simp only [g₀, Set.indicator_of_mem (mem_closedBall_self (half_pos hδ).le), g, neg_zero]]
    at hconv
  refine hconv.congr fun n ↦ ?_
  -- By Fubini, `∫ ρ_n (y) • H (x, y)` is the convolution `(ρ_n ⋆ g₀) (0) = ∫ ρ_n (y) • g₀ (-y) dy`.
  have hsupp (y : G) (hy : (ρ n).normed μ y ≠ 0) : -y ∈ closedBall (0 : G) (δ / 2) := by
    have hy' : y ∈ ball (0 : G) (ρ n).rOut := by
      rw [← (ρ n).support_normed_eq (μ := μ)]
      exact hy
    rw [mem_ball_zero_iff, rOut_shrinking] at hy'
    rw [mem_closedBall_zero_iff, norm_neg]
    exact hy'.le.trans (div_le_self (half_pos hδ).le (by linarith [n.cast_nonneg (α := ℝ)]))
  have hint : Integrable (fun q : X × G ↦ (ρ n).normed μ q.2 • H q) (ν.prod μ) := by
    refine ((((ρ n).continuous_normed.comp continuous_snd).continuousOn.smul
      (hH.mono (Set.prod_mono (Set.subset_univ _) hball))).integrableOn_compact
      (hk.prod (isCompact_closedBall _ _))).integrable_of_forall_notMem_eq_zero fun q hq ↦ ?_
    by_contra hne
    have hq' : (ρ n).normed μ q.2 ≠ 0 ∧ H q ≠ 0 := by simpa [not_or] using hne
    exact hq ⟨by_contra fun hx ↦ hq'.2 (hHk _ _ hx), by simpa using hsupp _ hq'.1⟩
  rw [convolution_def, integral_prod_symm _ hint]
  refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
  simp only [zero_sub, ContinuousLinearMap.lsmul_apply, integral_smul]
  by_cases hy : (ρ n).normed μ y = 0
  · simp [hy]
  · simp [g₀, g, Set.indicator_of_mem (hsupp y hy)]

/-- Normalized bumps of shrinking radius approximate a function uniformly on a set `s` when the
function is uniformly continuous on a `δ`-neighbourhood of `s`. Only the values on that
neighbourhood matter, so the function need not be continuous elsewhere. -/
theorem tendstoUniformlyOn_normed_convolution {ι : Type*} {l : Filter ι}
    {ρ : ι → ContDiffBump (0 : G)} (hρ : Tendsto (fun i => (ρ i).rOut) l (𝓝 0)) {s : Set G}
    {δ : ℝ} (hδ : 0 < δ) (hg : UniformContinuousOn g (thickening δ s))
    (hmg : AEStronglyMeasurable g μ) :
    TendstoUniformlyOn (fun i => (ρ i).normed μ ⋆[lsmul ℝ ℝ, μ] g) g l s := by
  refine Metric.tendstoUniformlyOn_iff.2 fun ε hε => ?_
  obtain ⟨η, hη, hgη⟩ := Metric.uniformContinuousOn_iff.1 hg (ε / 2) (by positivity)
  filter_upwards [hρ.eventually (gt_mem_nhds (lt_min hη hδ))] with i hi x hx
  rw [dist_comm]
  refine ((ρ i).dist_normed_convolution_le (μ := μ) hmg fun y hy => ?_).trans_lt
    (half_lt_self hε)
  have hyx : dist y x < min η δ := (mem_ball.1 hy).trans hi
  exact (hgη y (mem_thickening_iff.2 ⟨x, hx, hyx.trans_le (min_le_right _ _)⟩) x
    (self_subset_thickening hδ s hx) (hyx.trans_le (min_le_left _ _))).le

/-- Normalized bumps of shrinking radius approximate a uniformly continuous function
uniformly on the whole space. -/
theorem tendstoUniformly_normed_convolution {ι : Type*} {l : Filter ι}
    {ρ : ι → ContDiffBump (0 : G)} (hρ : Tendsto (fun i => (ρ i).rOut) l (𝓝 0))
    (hg : UniformContinuous g) :
    TendstoUniformly (fun i => (ρ i).normed μ ⋆[lsmul ℝ ℝ, μ] g) g l :=
  tendstoUniformlyOn_univ.1 <| tendstoUniformlyOn_normed_convolution hρ one_pos
    hg.uniformContinuousOn hg.continuous.aestronglyMeasurable

/-- As normalized bumps shrink to `0`, integrals against the mollifications of a uniformly
continuous function `g` converge to the integral against `g`: `∫ (ρᵢ ⋆ g) w → ∫ g w` whenever `w`
and `g w` are integrable. -/
theorem tendsto_integral_normed_convolution_smul {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] [SMul F H] [IsBoundedSMul F H] (hg : UniformContinuous g) {ι : Type*}
    {l : Filter ι} {ρ : ι → ContDiffBump (0 : G)}
    (hρ : Tendsto (fun i => (ρ i).rOut) l (𝓝 0)) {w : G → H} (hw : Integrable w μ)
    (hgw : Integrable (fun x => g x • w x) μ) :
    Tendsto (fun i => ∫ x, ((ρ i).normed μ ⋆[lsmul ℝ ℝ, μ] g) x • w x ∂μ) l
      (𝓝 (∫ x, g x • w x ∂μ)) :=
  (tendstoUniformly_normed_convolution (μ := μ) hρ hg).tendsto_integral_smul_of_integrable
    (Eventually.of_forall fun i =>
      ((ρ i).contDiff_normed_convolution hg.continuous.locallyIntegrable
        (n := ⊤)).continuous.aestronglyMeasurable.smul hw.1)
    hw hgw

/-- Normalized bumps of radius tending to zero along a filter approximate a function that is
continuous at `x` uniformly on a neighbourhood filter of `x`. This upgrades Mathlib's joint
convergence `ContDiffBump.convolution_tendsto_right` to the form needed for limit theorems of
derivatives such as `hasFDerivAt_of_tendstoUniformlyOnFilter`. -/
theorem tendstoUniformlyOnFilter_normed_convolution {ι : Type*} {l : Filter ι} {x : G}
    {ρ : ι → ContDiffBump (0 : G)} (hρ : Tendsto (fun i => (ρ i).rOut) l (𝓝 0))
    (hgm : AEStronglyMeasurable g μ) (hgx : ContinuousAt g x) :
    TendstoUniformlyOnFilter (fun i => (ρ i).normed μ ⋆[lsmul ℝ ℝ, μ] g) g l (𝓝 x) := by
  have hconv : Tendsto (fun p : ι × G => ((ρ p.1).normed μ ⋆[lsmul ℝ ℝ, μ] g) p.2)
      (l ×ˢ 𝓝 x) (𝓝 (g x)) :=
    ContDiffBump.convolution_tendsto_right (hρ.comp tendsto_fst)
      (Eventually.of_forall fun _ => hgm) (hgx.tendsto.comp tendsto_snd) tendsto_snd
  have hdist : Tendsto (fun p : ι × G =>
      dist (((ρ p.1).normed μ ⋆[lsmul ℝ ℝ, μ] g) p.2) (g p.2)) (l ×ˢ 𝓝 x) (𝓝 0) := by
    simpa only [dist_self, Function.comp_apply] using hconv.dist (hgx.tendsto.comp tendsto_snd)
  rw [Metric.tendstoUniformlyOnFilter_iff]
  intro ε hε
  simpa only [dist_comm] using (tendsto_order.1 hdist).2 ε hε

/-- Mollifying a locally integrable function with values in a closed convex set `s` by a
normalized bump keeps its values in `s`: the mollification at `x` is the mean of `g (x - ·)` for the
probability measure with density `φ.normed μ`. -/
theorem normed_convolution_mem_of_convex (φ : ContDiffBump (0 : G)) {s : Set F}
    (hs : Convex ℝ s) (hsc : IsClosed s) (hg : LocallyIntegrable g μ) (hgs : ∀ x, g x ∈ s)
    (x : G) : (φ.normed μ ⋆[lsmul ℝ ℝ, μ] g) x ∈ s := by
  have hexists := (φ.hasCompactSupport_normed (μ := μ)).convolutionExists_left
    (lsmul ℝ ℝ) φ.continuous_normed hg x
  have heq : (φ.normed μ ⋆[lsmul ℝ ℝ, μ] g) x = ∫ t, g (x - t) ∂φ.normedMeasure μ := by
    rw [convolution_def, φ.integral_normedMeasure]
    simp only [lsmul_apply]
  rw [heq]
  refine hs.integral_mem hsc (ae_of_all _ fun t => hgs _) ?_
  simpa only [φ.integrable_normedMeasure_iff, ConvolutionExistsAt, lsmul_apply] using hexists

/-- Mollifying a locally integrable function with values in `[a, b]` by a normalized bump keeps
its values in `[a, b]`. -/
theorem normed_convolution_mem_Icc (φ : ContDiffBump (0 : G)) {w : G → ℝ} {a b : ℝ}
    (hw : LocallyIntegrable w μ) (hwab : ∀ x, w x ∈ Set.Icc a b) (x : G) :
    (φ.normed μ ⋆[lsmul ℝ ℝ, μ] w) x ∈ Set.Icc a b :=
  φ.normed_convolution_mem_of_convex (convex_Icc a b) isClosed_Icc hw hwab x

open Set in
/-- Mollifying a function that is continuous on a ball by bumps with radii tending to `0`
converges uniformly on the half-radius ball, along any filter of parameters. -/
theorem tendstoUniformlyOn_convolution_indicator_ball {ι : Type*} {l : Filter ι} {x : G}
    {r : ℝ} (hr : 0 < r) {V : G → F}
    (hVc : ContinuousOn V (ball x r))
    {phi : ι → ContDiffBump (0 : G)} (hphi : Tendsto (fun n => (phi n).rOut) l (𝓝 0)) :
    TendstoUniformlyOn (fun n => (ball x r).indicator V ⋆[
      (ContinuousLinearMap.lsmul ℝ ℝ).flip, μ] (phi n).normed μ)
      ((ball x r).indicator V) l (ball x (r / 2)) := by
  let Fn := fun n => (ball x r).indicator V ⋆[
    (ContinuousLinearMap.lsmul ℝ ℝ).flip, μ] (phi n).normed μ
  -- Continuity on the ball makes the truncation measurable.
  have hVm : AEStronglyMeasurable ((ball x r).indicator V) μ :=
    (aestronglyMeasurable_indicator_iff measurableSet_ball).2
      (hVc.aestronglyMeasurable measurableSet_ball)
  -- The mollifications converge locally uniformly throughout the larger ball.
  have hlocal : TendstoLocallyUniformlyOn Fn ((ball x r).indicator V) l (ball x r) := by
    rw [isOpen_ball.tendstoLocallyUniformlyOn_iff_forall_tendsto]
    intro y hy
    have hcont : ContinuousAt ((ball x r).indicator V) y :=
      (hVc.congr fun z hz => indicator_of_mem hz V).continuousAt (isOpen_ball.mem_nhds hy)
    have hconv : Tendsto (fun p : ι × G => Fn p.1 p.2) (l ×ˢ 𝓝 y)
        (𝓝 (((ball x r).indicator V) y)) := by
      simp only [Fn, convolution_flip]
      exact ContDiffBump.convolution_tendsto_right (hphi.comp tendsto_fst)
        (Eventually.of_forall fun _ => hVm) (hcont.tendsto.comp tendsto_snd) tendsto_snd
    apply tendsto_uniformity_iff_dist_tendsto_zero.2
    simpa only [dist_self, Function.comp_apply] using
      (hcont.tendsto.comp tendsto_snd).dist hconv
  have hsub : closedBall x (r / 2) ⊆ ball x r := closedBall_subset_ball (half_lt_self hr)
  exact ((tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
    (isCompact_closedBall x (r / 2))).1 (hlocal.mono hsub)).mono ball_subset_closedBall

end ContDiffBump

/-- Every available Fréchet derivative of compactly supported finite-regularity data commutes
with normalized-bump convolution. -/
theorem HasCompactSupport.iteratedFDeriv_normed_convolution
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : Measure E} [μ.IsAddHaarMeasure] {f : E → F} {N : ℕ∞} {k : ℕ}
    (hfc : HasCompactSupport f) (hf : ContDiff ℝ N f) (ρ : ContDiffBump (0 : E))
    (hk : k ≤ N) :
    iteratedFDeriv ℝ k (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] f) =
      ρ.normed μ ⋆[lsmul ℝ ℝ, μ] iteratedFDeriv ℝ k f := by
  have hL : (compContinuousMultilinearMapL ℝ (fun _ : Fin k ↦ E) F F).comp
      (lsmul ℝ ℝ) = lsmul ℝ ℝ := by
    ext a m
    simp
  rw [← hL]
  exact hfc.iteratedFDeriv_convolution_right (lsmul ℝ ℝ)
    ρ.continuous_normed.locallyIntegrable hf hk

/-- The normalized-bump convolution of `g` at `x` only depends on the values of `g` on the ball
of radius `ρ.rOut` around `x`. -/
theorem ContDiffBump.normed_convolution_eq_of_eqOn {G F : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [HasContDiffBump G] [MeasurableSpace G] {μ : Measure G}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (ρ : ContDiffBump (0 : G)) {g₁ g₂ : G → F} {x : G}
    (h : Set.EqOn g₁ g₂ (ball x ρ.rOut)) :
    (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] g₁) x = (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] g₂) x := by
  simp only [convolution_def]
  congr 1 with t
  by_cases ht : ρ.normed μ t = 0
  · simp [ht]
  · have hρt : ρ t ≠ 0 := fun h0 ↦ ht (by simp [ContDiffBump.normed_def, h0])
    have htr : t ∈ ball (0 : G) ρ.rOut := ρ.support_eq ▸ Function.mem_support.2 hρt
    rw [h (by simpa [dist_eq_norm] using htr)]

/-- Every available Fréchet derivative of a `C^N` function commutes with normalized-bump
convolution: `Dᵏ (ρ ⋆ f) = ρ ⋆ Dᵏ f` for `k ≤ N`. Unlike
`HasCompactSupport.iteratedFDeriv_normed_convolution`, no support or growth condition on `f` is
needed, since near each point the convolution only reads `f` on a bounded set. -/
theorem ContDiffBump.iteratedFDeriv_normed_convolution
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : Measure E} [μ.IsAddHaarMeasure] {f : E → F} {N : ℕ∞} {k : ℕ}
    (hf : ContDiff ℝ N f) (ρ : ContDiffBump (0 : E)) (hk : k ≤ N) :
    iteratedFDeriv ℝ k (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] f) =
      ρ.normed μ ⋆[lsmul ℝ ℝ, μ] iteratedFDeriv ℝ k f := by
  funext x₀
  -- Near `x₀` the convolution only reads `f` on `ball x₀ (ρ.rOut + 1)`, where `f` agrees with
  -- the compactly supported cutoff `f₁ = χ f`.
  let χ : ContDiffBump x₀ := ⟨ρ.rOut + 1, ρ.rOut + 2, by linarith [ρ.rOut_pos], by linarith⟩
  set f₁ : E → F := fun x ↦ χ x • f x
  have hf₁ : ContDiff ℝ N f₁ := χ.contDiff.smul hf
  have hc₁ : HasCompactSupport f₁ := χ.hasCompactSupport.smul_right
  have heq : Set.EqOn f₁ f (ball x₀ (ρ.rOut + 1)) := fun y hy ↦ by
    simp [f₁, χ.one_of_mem_closedBall (ball_subset_closedBall hy)]
  have hsub (x : E) (hx : x ∈ ball x₀ 1) : ball x ρ.rOut ⊆ ball x₀ (ρ.rOut + 1) :=
    (ball_subset_ball' (by rw [mem_ball] at hx; linarith))
  have hnear : ρ.normed μ ⋆[lsmul ℝ ℝ, μ] f₁ =ᶠ[𝓝 x₀] ρ.normed μ ⋆[lsmul ℝ ℝ, μ] f :=
    eventually_of_mem (ball_mem_nhds x₀ one_pos) fun x hx ↦
      ρ.normed_convolution_eq_of_eqOn ((heq.mono (hsub x hx)))
  have hD : Set.EqOn (iteratedFDeriv ℝ k f₁) (iteratedFDeriv ℝ k f) (ball x₀ (ρ.rOut + 1)) :=
    fun y hy ↦ ((eventuallyEq_of_mem (isOpen_ball.mem_nhds hy) heq).iteratedFDeriv ℝ k).eq_of_nhds
  rw [← (hnear.iteratedFDeriv ℝ k).eq_of_nhds, hc₁.iteratedFDeriv_normed_convolution hf₁ ρ hk]
  exact ρ.normed_convolution_eq_of_eqOn (hD.mono (hsub x₀ (mem_ball_self one_pos)))

/-- Convolution with a nonnegative normalized bump averages the differences of translates: if
`dist (g (x - t)) (g (y - t)) ≤ B` for every `t` in the support `ball 0 ρ.rOut` of the bump, then
the convolutions at `x` and `y` are within `B` of each other. -/
theorem ContDiffBump.dist_normed_convolution_le_of_dist_sub_le {G F : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [MeasurableSpace G]
    [BorelSpace G] {μ : Measure G} [μ.IsAddHaarMeasure] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : G → F} (hg : Continuous g) (ρ : ContDiffBump (0 : G)) {x y : G} {B : ℝ}
    (hB : ∀ t ∈ Metric.ball (0 : G) ρ.rOut, dist (g (x - t)) (g (y - t)) ≤ B) :
    dist ((ρ.normed μ ⋆[lsmul ℝ ℝ, μ] g) x) ((ρ.normed μ ⋆[lsmul ℝ ℝ, μ] g) y) ≤ B := by
  have hi : ConvolutionExists (ρ.normed μ) g (lsmul ℝ ℝ) μ :=
    ρ.hasCompactSupport_normed.convolutionExists_left_of_continuous_right
      (lsmul ℝ ℝ) ρ.integrable_normed.locallyIntegrable hg
  rw [dist_eq_norm, convolution_def, convolution_def, ← integral_sub (hi x).integrable
    (hi y).integrable]
  calc
    ‖∫ t, lsmul ℝ ℝ (ρ.normed μ t) (g (x - t)) -
        lsmul ℝ ℝ (ρ.normed μ t) (g (y - t)) ∂μ‖
      ≤ ∫ t, ρ.normed μ t * B ∂μ := by
        apply norm_integral_le_of_norm_le (ρ.integrable_normed.mul_const _)
        filter_upwards with t
        simp only [lsmul_apply, ← smul_sub, norm_smul,
          Real.norm_of_nonneg (ρ.nonneg_normed t)]
        -- Off the support of the bump both sides vanish.
        by_cases ht : t ∈ Metric.ball (0 : G) ρ.rOut
        · exact mul_le_mul_of_nonneg_left (by simpa only [dist_eq_norm] using hB t ht)
            (ρ.nonneg_normed t)
        · have h0 : ρ.normed μ t = 0 := Function.notMem_support.1 fun h ↦
            ht (ρ.support_normed_eq (μ := μ) ▸ h)
          simp [h0]
    _ = B := by rw [integral_mul_const, ρ.integral_normed, one_mul]

/-- Convolution with a nonnegative normalized bump preserves an almost-everywhere bound on the
norm. -/
theorem ContDiffBump.norm_normed_convolution_le {G F : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [MeasurableSpace G] [BorelSpace G]
    {μ : Measure G} [μ.IsAddHaarMeasure] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : G → F} (ρ : ContDiffBump (0 : G)) {M : ℝ} (hM : ∀ᵐ x ∂μ, ‖g x‖ ≤ M) (x : G) :
    ‖(ρ.normed μ ⋆[lsmul ℝ ℝ, μ] g) x‖ ≤ M := by
  simpa only [convolution_def, lsmul_apply, Real.norm_of_nonneg (ρ.nonneg_normed _),
    ρ.integral_normed, one_mul] using
    TauCeti.norm_integral_kernel_smul_sub_le (μ := μ) ρ.integrable_normed
      ((μ.measurePreserving_sub_left x).quasiMeasurePreserving.ae hM)

/-- Convolution with a nonnegative normalized bump preserves an almost-everywhere `L²`-product bound
`‖f₁ y‖² + ‖f₂ y‖² ≤ M`. -/
theorem ContDiffBump.norm_normed_convolution_sq_add_norm_normed_convolution_sq_le
    {G F₁ F₂ : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsAddHaarMeasure]
    [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
    {f₁ : G → F₁} {f₂ : G → F₂} (ρ : ContDiffBump (0 : G)) {M : ℝ}
    (hM : ∀ᵐ y ∂μ, ‖f₁ y‖ ^ 2 + ‖f₂ y‖ ^ 2 ≤ M) (x : G) :
    ‖(ρ.normed μ ⋆[lsmul ℝ ℝ, μ] f₁) x‖ ^ 2 + ‖(ρ.normed μ ⋆[lsmul ℝ ℝ, μ] f₂) x‖ ^ 2 ≤ M := by
  obtain ⟨y₀, hy₀⟩ := hM.exists
  have hM0 : 0 ≤ M := (add_nonneg (sq_nonneg _) (sq_nonneg _)).trans hy₀
  set A := ‖(ρ.normed μ ⋆[lsmul ℝ ℝ, μ] f₁) x‖
  set B := ‖(ρ.normed μ ⋆[lsmul ℝ ℝ, μ] f₂) x‖
  have hA0 : 0 ≤ A := norm_nonneg _
  have hB0 : 0 ≤ B := norm_nonneg _
  have hf₁ : ∀ᵐ y ∂μ, ‖f₁ y‖ ≤ √M :=
    hM.mono fun y hy => Real.le_sqrt_of_sq_le (by linarith [hy, sq_nonneg ‖f₂ y‖])
  have hf₂ : ∀ᵐ y ∂μ, ‖f₂ y‖ ≤ √M :=
    hM.mono fun y hy => Real.le_sqrt_of_sq_le (by linarith [hy, sq_nonneg ‖f₁ y‖])
  by_cases h1 : Integrable (fun t => ρ.normed μ t • f₁ (x - t)) μ
  · by_cases h2 : Integrable (fun t => ρ.normed μ t • f₂ (x - t)) μ
    · have h1n : Integrable (fun t => ρ.normed μ t * ‖f₁ (x - t)‖) μ := by
        simpa only [norm_smul, Real.norm_of_nonneg (ρ.nonneg_normed _)] using h1.norm
      have h2n : Integrable (fun t => ρ.normed μ t * ‖f₂ (x - t)‖) μ := by
        simpa only [norm_smul, Real.norm_of_nonneg (ρ.nonneg_normed _)] using h2.norm
      have hA_le : A ≤ ∫ t, ρ.normed μ t * ‖f₁ (x - t)‖ ∂μ := by
        simpa only [A, convolution_def, lsmul_apply, norm_smul,
          Real.norm_of_nonneg (ρ.nonneg_normed _)] using
          norm_integral_le_integral_norm (fun t => ρ.normed μ t • f₁ (x - t))
      have hB_le : B ≤ ∫ t, ρ.normed μ t * ‖f₂ (x - t)‖ ∂μ := by
        simpa only [B, convolution_def, lsmul_apply, norm_smul,
          Real.norm_of_nonneg (ρ.nonneg_normed _)] using
          norm_integral_le_integral_norm (fun t => ρ.normed μ t • f₂ (x - t))
      rw [← Real.sq_sqrt hM0,
        TauCeti.sq_add_sq_le_sq_iff_forall_mul_add_mul_le hA0 hB0 (Real.sqrt_nonneg M)]
      intro c s hc0 hs0 hcs
      calc c * A + s * B
          ≤ c * (∫ t, ρ.normed μ t * ‖f₁ (x - t)‖ ∂μ) +
              s * (∫ t, ρ.normed μ t * ‖f₂ (x - t)‖ ∂μ) :=
            add_le_add (mul_le_mul_of_nonneg_left hA_le hc0)
              (mul_le_mul_of_nonneg_left hB_le hs0)
        _ = ∫ t, ρ.normed μ t * (c * ‖f₁ (x - t)‖ + s * ‖f₂ (x - t)‖) ∂μ := by
            rw [← integral_const_mul, ← integral_const_mul,
              ← integral_add (h1n.const_mul c) (h2n.const_mul s)]
            exact integral_congr_ae (.of_forall fun t => by ring)
        _ ≤ ∫ t, ρ.normed μ t * √M ∂μ := by
            have hMx : ∀ᵐ t ∂μ, ‖f₁ (x - t)‖ ^ 2 + ‖f₂ (x - t)‖ ^ 2 ≤ M :=
              (μ.measurePreserving_sub_left x).quasiMeasurePreserving.ae hM
            refine integral_mono_ae (((h1n.const_mul c).add (h2n.const_mul s)).congr
              (.of_forall fun t => by simp only [Pi.add_apply]; ring))
              (ρ.integrable_normed.mul_const √M) (hMx.mono fun t ht =>
                mul_le_mul_of_nonneg_left
                  ((TauCeti.sq_add_sq_le_sq_iff_forall_mul_add_mul_le (norm_nonneg _)
                    (norm_nonneg _) (Real.sqrt_nonneg M)).1
                      (ht.trans_eq (Real.sq_sqrt hM0).symm) c s hc0 hs0 hcs)
                  (ρ.nonneg_normed t))
        _ = √M := by rw [integral_mul_const, ρ.integral_normed, one_mul]
    · have hB : B = 0 := by
        simp only [B, convolution_def, lsmul_apply, integral_undef h2, norm_zero]
      rw [hB, zero_pow two_ne_zero, add_zero]
      exact (pow_le_pow_left₀ hA0 (ρ.norm_normed_convolution_le hf₁ x) 2).trans_eq
        (Real.sq_sqrt hM0)
  · have hA : A = 0 := by
      simp only [A, convolution_def, lsmul_apply, integral_undef h1, norm_zero]
    rw [hA, zero_pow two_ne_zero, zero_add]
    exact (pow_le_pow_left₀ hB0 (ρ.norm_normed_convolution_le hf₂ x) 2).trans_eq
      (Real.sq_sqrt hM0)

/-- Convolution with a nonnegative normalized bump preserves the Lipschitz constant,
including for Banach-valued functions. -/
theorem LipschitzWith.normed_convolution {G F : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [MeasurableSpace G] [BorelSpace G]
    {μ : Measure G} [μ.IsAddHaarMeasure] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : G → F} {K : ℝ≥0} (hg : LipschitzWith K g)
    (ρ : ContDiffBump (0 : G)) :
    LipschitzWith K (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] g) :=
  LipschitzWith.of_dist_le_mul fun x y ↦ ρ.dist_normed_convolution_le_of_dist_sub_le hg.continuous
    fun t _ ↦ by simpa only [dist_sub_right] using hg.dist_le_mul (x - t) (y - t)

/-- A normalized bump of outer radius `r` changes a Lipschitz function by at most `K * r`. -/
theorem LipschitzWith.dist_normed_convolution_le {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {f : E → F} {K : ℝ≥0} (hf : LipschitzWith K f)
    (φ : ContDiffBump (0 : E)) (x : E) :
    dist ((φ.normed μ ⋆[lsmul ℝ ℝ, μ] f) x) (f x) ≤ K * φ.rOut :=
  φ.dist_normed_convolution_le hf.continuous.aestronglyMeasurable fun y hy ↦
    (hf.dist_le_mul y x).trans
      (mul_le_mul_of_nonneg_left (mem_ball.1 hy).le K.coe_nonneg)

/-- **Smooth bounded approximation in `L¹`.** In `L¹` of a finite measure `ν`, a continuous
function `h` with `‖h x‖ ≤ M` is approximated by smooth functions with `‖ψ x‖ ≤ M`, supported in
any closed thickening of the support of `h`: its mollifications with the normalized bumps
`ContDiffBump.shrinking` converge to it everywhere, hence in `L¹(ν)` by dominated convergence. -/
theorem Continuous.exists_contDiff_norm_le_lintegral_sub_le {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {ν : Measure E}
    [IsFiniteMeasure ν] {h : E → F} (hhc : Continuous h) {M : ℝ} (hhM : ∀ x, ‖h x‖ ≤ M)
    {δ : ℝ} (hδ : 0 < δ) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ ψ : E → F, ContDiff ℝ ∞ ψ ∧ (∀ x, ‖ψ x‖ ≤ M) ∧ tsupport ψ ⊆ cthickening δ (tsupport h) ∧
      ∫⁻ x, ‖ψ x - h x‖ₑ ∂ν ≤ ε := by
  let φ : ℕ → ContDiffBump (0 : E) := ContDiffBump.shrinking hδ
  set ψ : ℕ → E → F := fun n => (φ n).normed Measure.addHaar ⋆[lsmul ℝ ℝ, Measure.addHaar] h
  have hψd (n : ℕ) : ContDiff ℝ ∞ (ψ n) :=
    (φ n).contDiff_normed_convolution hhc.locallyIntegrable
  have hψs (n : ℕ) : tsupport (ψ n) ⊆ cthickening δ (tsupport h) := by
    refine (φ n).tsupport_normed_convolution_subset.trans ?_
    rintro _ ⟨a, ha, b, hb, rfl⟩
    refine mem_cthickening_of_dist_le _ b _ _ hb ?_
    rw [dist_eq_norm, add_sub_cancel_right, ← dist_zero_right]
    exact (mem_closedBall.1 ha).trans (ContDiffBump.rOut_shrinking_le hδ n)
  have hψM (n : ℕ) (x : E) : ‖ψ n x‖ ≤ M := (φ n).norm_normed_convolution_le (.of_forall hhM) x
  have he (v : F) (hv : ‖v‖ ≤ M) : ‖v‖ₑ ≤ ENNReal.ofReal M := by
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal hv
  have hlim : Tendsto (fun n => ∫⁻ x, ‖ψ n x - h x‖ₑ ∂ν) atTop (𝓝 0) := by
    have := tendsto_lintegral_of_dominated_convergence (μ := ν)
      (fun _ => ENNReal.ofReal M + ENNReal.ofReal M) (f := fun _ => 0)
      (fun n => ((hψd n).continuous.sub hhc).eNorm.measurable)
      (fun n => ae_of_all _ fun x =>
        eNorm_sub_le.trans (add_le_add (he _ (hψM n x)) (he _ (hhM x))))
      (by rw [lintegral_const]; exact ENNReal.mul_ne_top (by simp) (measure_ne_top _ _))
      (ae_of_all _ fun x => by
        simpa using ((ContDiffBump.convolution_tendsto_right_of_continuous
          (ContDiffBump.tendsto_rOut_shrinking hδ) hhc x).sub_const (h x)).eNorm)
    simpa using this
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds (pos_iff_ne_zero.2 hε))).exists
  exact ⟨ψ n, hψd n, hψM n, hψs n, hn.le⟩
