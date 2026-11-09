/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import TauCeti.MeasureTheory.Integral.PiSystem

/-!
# Inner products of square-integrable functions

The pointwise inner product of two square-integrable functions with values in an inner product
space is integrable. Mathlib states this for elements of `L²` (`MeasureTheory.L2.integrable_inner`);
this file gives the form for functions satisfying `MemLp f 2 μ`, which is how second-moment
hypotheses on random vectors are usually stated, together with the special case of a quadratic
form `⟪B (f x), f x⟫` of a matrix `B` on a Euclidean-valued function.
For counting measure, singleton-supported vectors separate L² functions and determine
continuous linear maps out of L². On a compact space with a finite measure, the L² pairing of an
L² function with a continuous function is an integral
(`MeasureTheory.L2.inner_toLp_continuousMap`), extending Mathlib's `ContinuousMap.inner_toLp`.
Indicators of any countably spanning generating π-system of finite-measure sets have
dense real linear span in L².

The space `L²(μ)` is infinite-dimensional as soon as `μ` carries infinitely many pairwise disjoint
sets of positive finite measure (`MeasureTheory.L2.not_finiteDimensional_of_pairwise_disjoint`),
since their indicators are nonzero and pairwise orthogonal. In particular `L²` of an open-positive,
locally finite measure restricted to a nonempty open subset of a nontrivial real normed space is
infinite-dimensional (`MeasureTheory.L2.not_finiteDimensional_restrict_of_isOpen`), which applies
to Lebesgue measure on a nonempty open subset of `ℝⁿ`, `n ≥ 1`.
-/

public section

open Function
open scoped ComplexConjugate ENNReal InnerProductSpace

namespace MeasureTheory

variable {α 𝕜 E : Type*} [MeasurableSpace α] {μ : Measure α} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The pointwise inner product of two square-integrable functions is integrable. -/
theorem MemLp.integrable_inner {f g : α → E} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun x ↦ ⟪f x, g x⟫_𝕜) μ :=
  (L2.integrable_inner (𝕜 := 𝕜) (hf.toLp f) (hg.toLp g)).congr <| by
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
    rw [hfx, hgx]

/-- The quadratic form of a matrix on a square-integrable Euclidean-valued function is
integrable. -/
theorem MemLp.integrable_inner_toEuclideanLin {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : α → EuclideanSpace 𝕜 ι} (hf : MemLp f 2 μ) (B : Matrix ι ι 𝕜) :
    Integrable (fun x ↦ ⟪B.toEuclideanLin (f x), f x⟫_𝕜) μ :=
  (hf.continuousLinearMap_comp (LinearMap.toContinuousLinearMap B.toEuclideanLin)).integrable_inner
    hf

/-- A counting-measure L² function orthogonal to every singleton-supported vector is zero.
No countability of the underlying measurable space is needed. -/
theorem Lp.eq_zero_of_inner_indicatorConstLp_singleton [MeasurableSingletonClass α]
    (f : Lp E 2 (Measure.count : Measure α))
    (h : ∀ (i : α) (v : E),
      ⟪indicatorConstLp 2 (measurableSet_singleton i) (by simp) v, f⟫_𝕜 = 0) : f = 0 := by
  have hf (i : α) : f i = 0 := by
    refine ext_inner_left 𝕜 fun v => ?_
    have hi := h i v
    rw [L2.inner_indicatorConstLp_eq_setIntegral_inner, integral_singleton] at hi
    simpa only [count_real_singleton, one_smul, inner_zero_right] using hi
  have hf' : f =ᵐ[Measure.count] fun _ => 0 := Filter.Eventually.of_forall hf
  exact Lp.ext (hf'.trans (Lp.coeFn_zero E 2 Measure.count).symm)

/-- On a compact space with a finite measure, the L² inner product of an L² function `f` with a
continuous function `g` is the integral of their pointwise inner product. -/
theorem L2.inner_toLp_continuousMap [TopologicalSpace α] [BorelSpace α] [CompactSpace α]
    [IsFiniteMeasure μ] (f : Lp 𝕜 2 μ) (g : C(α, 𝕜)) :
    ⟪f, ContinuousMap.toLp 2 μ 𝕜 g⟫_𝕜 = ∫ x, g x * conj (f x) ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := 𝕜) μ g] with x hx
  rw [hx, RCLike.inner_apply]

/-- **`L²` is infinite-dimensional** when the measure carries a sequence of pairwise disjoint
measurable sets of positive finite measure: their indicators are nonzero and pairwise
orthogonal, hence linearly independent. -/
theorem L2.not_finiteDimensional_of_pairwise_disjoint {A : ℕ → Set α}
    (hA : ∀ k, MeasurableSet (A k)) (hpos : ∀ k, μ (A k) ≠ 0) (hfin : ∀ k, μ (A k) ≠ ∞)
    (hdisj : Pairwise (Disjoint on A)) : ¬ FiniteDimensional 𝕜 (Lp 𝕜 2 μ) := by
  intro _
  refine Module.Finite.not_linearIndependent_of_infinite
    (fun k ↦ indicatorConstLp 2 (hA k) (hfin k) (1 : 𝕜))
    (linearIndependent_of_ne_zero_of_inner_eq_zero (𝕜 := 𝕜) (fun k hk ↦ ?_) fun j k hjk ↦ ?_)
  · have h := L2.inner_indicatorConstLp_one_indicatorConstLp_one (𝕜 := 𝕜) (hA k) (hA k) (hfin k)
      (hfin k)
    rw [hk, inner_zero_left, Set.inter_self, eq_comm, RCLike.ofReal_eq_zero,
      measureReal_eq_zero_iff (hfin k)] at h
    exact hpos k h
  · refine (L2.inner_indicatorConstLp_one_indicatorConstLp_one (hA j) (hA k) (hfin j)
      (hfin k)).trans ?_
    rw [(hdisj hjk).inter_eq, measureReal_empty, RCLike.ofReal_zero]

/-- **`L²` of a nonempty open set is infinite-dimensional.** For an open-positive, locally finite
measure on a nontrivial real normed space, `L²` of its restriction to a nonempty open set `U` is
not finite-dimensional. The witnesses are indicators of disjoint concentric annuli in a small
ball inside `U`. -/
theorem L2.not_finiteDimensional_restrict_of_isOpen {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [Nontrivial E] [MeasurableSpace E] [OpensMeasurableSpace E]
    (μ : Measure E) [μ.IsOpenPosMeasure] [IsLocallyFiniteMeasure μ] {U : Set E} (hU : IsOpen U)
    (hne : U.Nonempty) : ¬ FiniteDimensional 𝕜 (Lp 𝕜 2 (μ.restrict U)) := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨V, hxV, hV⟩ := μ.finiteAt_nhds x
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem (hU.mem_nhds hx) hxV)
  -- The annuli `ball x (r / (k + 1)) \ closedBall x (r / (k + 2))` are open, nonempty, disjoint.
  set A : ℕ → Set E := fun k ↦ Metric.ball x (r / (k + 1)) \ Metric.closedBall x (r / (k + 2))
  have hAU (k : ℕ) : A k ⊆ U ∩ V := fun y hy ↦ hrU (Metric.ball_subset_ball
    (div_le_self hr.le (by linarith [k.cast_nonneg (α := ℝ)])) hy.1)
  have hAopen (k : ℕ) : IsOpen (A k) := Metric.isOpen_ball.sdiff Metric.isClosed_closedBall
  have hAne (k : ℕ) : (A k).Nonempty := by
    have hk : (0 : ℝ) < k + 1 := by positivity
    obtain ⟨v, hv⟩ := exists_norm_eq E (by positivity : 0 ≤ (r / (k + 1) + r / (k + 2)) / 2)
    refine ⟨x + v, ?_, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, hv]
      linarith [div_lt_div_of_pos_left hr hk (by linarith : (k : ℝ) + 1 < k + 2)]
    · rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, hv, not_le]
      linarith [div_lt_div_of_pos_left hr hk (by linarith : (k : ℝ) + 1 < k + 2)]
  refine L2.not_finiteDimensional_of_pairwise_disjoint (fun k ↦ (hAopen k).measurableSet)
    (fun k ↦ ?_) (fun k ↦ ?_) ?_
  · rw [Measure.restrict_apply (hAopen k).measurableSet,
      Set.inter_eq_left.2 fun y hy ↦ (hAU k hy).1]
    exact ((hAopen k).measure_pos μ (hAne k)).ne'
  · rw [Measure.restrict_apply (hAopen k).measurableSet]
    exact ((measure_mono (Set.inter_subset_left.trans fun y hy ↦ (hAU k hy).2)).trans_lt hV).ne
  · intro j k hjk
    wlog hlt : j < k generalizing j k
    · exact (this hjk.symm ((Nat.lt_or_gt_of_ne hjk).resolve_left hlt)).symm
    refine Set.disjoint_left.2 fun y hyj hyk ↦ hyj.2 (Metric.ball_subset_closedBall ?_)
    refine Metric.ball_subset_ball ?_ hyk.1
    have hjk' : (j : ℝ) + 2 ≤ k + 1 := by
      exact_mod_cast Nat.add_le_add_right (Nat.succ_le_of_lt hlt) 1
    exact div_le_div_of_nonneg_left hr.le (by positivity) hjk'

end MeasureTheory

namespace ContinuousLinearMap

open MeasureTheory

/-- A continuous linear map out of counting-measure L² that vanishes on all
singleton-supported vectors is zero. No countability of the index space is needed. -/
theorem eq_zero_of_apply_indicatorConstLp_singleton
    {α 𝕜 E F : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (T : Lp E 2 (Measure.count : Measure α) →L[𝕜] F)
    (h : ∀ (i : α) (v : E),
      T (indicatorConstLp 2 (measurableSet_singleton i) (by simp) v) = 0) : T = 0 := by
  have ht : T.adjoint = 0 := by
    apply ContinuousLinearMap.ext
    intro η
    rw [zero_apply]
    refine Lp.eq_zero_of_inner_indicatorConstLp_singleton (𝕜 := 𝕜) _ fun i v => ?_
    rw [adjoint_inner_right, h, inner_zero_left]
  calc
    T = T.adjoint.adjoint := (adjoint_adjoint T).symm
    _ = 0 := by rw [ht, map_zero]

end ContinuousLinearMap

namespace TauCeti

open MeasureTheory
open scoped ENNReal

/-- Indicators of a countably spanning generating π-system of finite-measure sets have
dense real linear span in L². -/
theorem topologicalClosure_span_indicatorConstLp_eq_top_of_isPiSystem
    {X : Type*} {m : MeasurableSpace X} {μ : Measure X}
    {S : Set (Set X)} (hgen : m = MeasurableSpace.generateFrom S)
    (hpi : IsPiSystem S) (hcover : IsCountablySpanning S) (hfin : ∀ s ∈ S, μ s ≠ ∞) :
    (Submodule.span ℝ {g : Lp ℝ 2 μ | ∃ (s : Set X) (hs : s ∈ S),
      g = indicatorConstLp 2 (hgen ▸ MeasurableSpace.measurableSet_generateFrom hs)
        (hfin s hs) 1}).topologicalClosure = ⊤ := by
  rw [← Submodule.orthogonal_eq_bot_iff, Submodule.orthogonal_closure]
  apply bot_unique
  intro f hf
  apply Lp.ext
  have hfi : ∀ s ∈ S, IntegrableOn f s μ := fun s hs =>
    integrableOn_Lp_of_measure_ne_top f (by norm_num) (hfin s hs)
  refine (ae_eq_zero_of_setIntegral_eq_zero_of_isPiSystem hgen hpi hcover hfi ?_).trans
    (Lp.coeFn_zero ℝ 2 μ).symm
  intro s hs
  rw [← L2.inner_indicatorConstLp_one
    (hgen ▸ MeasurableSpace.measurableSet_generateFrom hs) (hfin s hs) f]
  exact (Submodule.mem_orthogonal _ f).mp hf _
    (Submodule.subset_span ⟨s, hs, rfl⟩)

end TauCeti
