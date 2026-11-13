/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import TauCeti.MeasureTheory.Integral.PiSystem
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import TauCeti.Algebra.Order.Ring.PosPartSq

/-!
# Inner products of square-integrable functions

The pointwise inner product of two square-integrable functions with values in an inner product
space is integrable. Mathlib states this for elements of `L²` (`MeasureTheory.L2.integrable_inner`);
this file gives the form for functions satisfying `MemLp f 2 μ`, which is how second-moment
hypotheses on random vectors are usually stated, together with the special case of a quadratic
form `⟪B (f x), f x⟫` of a matrix `B` on a Euclidean-valued function. Likewise the weighted
squared norm `V² ‖g‖²` of a square-integrable `g` against an essentially bounded weight `V` is
integrable (`MeasureTheory.MemLp.integrable_sq_mul_norm_sq`).
For counting measure, singleton-supported vectors separate L² functions and determine
continuous linear maps out of L². On a compact space with a finite measure, the L² pairing of an
L² function with a continuous function is an integral
(`MeasureTheory.L2.inner_toLp_continuousMap`), extending Mathlib's `ContinuousMap.inner_toLp`.
More generally, the L² pairing of an L² function with the class of any square-integrable
function is the integral of their pointwise inner product (`MeasureTheory.L2.inner_toLp`).
The second moment of a finite sum of pairwise orthogonal functions with values in a real inner
product space is the sum of their second moments
(`TauCeti.integral_norm_sum_sq_of_pairwise_integral_inner_eq_zero`), with a scalar specialization
`TauCeti.integral_sq_sum_of_pairwise_integral_mul_eq_zero`.
The integral of `⟪f x, c⟫` is `⟪∫ f, c⟫` (`integral_inner_left`), the counterpart of Mathlib's
`integral_inner` with the integrand in the left slot, and the integral of the Hilbert space
adjoints `(f x)†` of an operator-valued function is `(∫ f)†`
(`ContinuousLinearMap.integral_adjoint`).
Indicators of any countably spanning generating π-system of finite-measure sets have
dense real linear span in L².

The space `L²(μ)` is infinite-dimensional as soon as `μ` carries infinitely many pairwise disjoint
sets of positive finite measure (`MeasureTheory.L2.not_finiteDimensional_of_pairwise_disjoint`),
since their indicators are nonzero and pairwise orthogonal. In particular `L²` of an open-positive,
locally finite measure restricted to a nonempty open subset of a nontrivial real normed space is
infinite-dimensional (`MeasureTheory.L2.not_finiteDimensional_restrict_of_isOpen`), which applies
to Lebesgue measure on a nonempty open subset of `ℝⁿ`, `n ≥ 1`.

For a complex inner product space `F` regarded as a real one (`InnerProductSpace.complexToReal`),
the real inner product on `L²(α, F)` is the real part of the complex one
(`MeasureTheory.L2.real_inner_eq_re_inner`). For a family of inner product spaces `G i`, evaluating
coordinate `i` of an `L²(α, ℓ²(G))` function is adjoint to placing an `L²(α, G i)` function in
coordinate `i` (`MeasureTheory.L2.inner_evalCLM_compLpL`).

On real `L²`, the squared norm of the positive part, `g ↦ ‖g⁺‖²`, is Fréchet differentiable with
derivative `k ↦ 2 ⟪f⁺, k⟫` at `f` (`MeasureTheory.Lp.hasFDerivAt_norm_posPart_sq`). Truncation
arguments for evolution equations use it to differentiate `‖u(t)⁺‖²` in time.
-/

public section

open Function MeasureTheory
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

/-- The weighted squared norm `V² ‖g‖²` of a square-integrable function `g` against an
essentially bounded measurable weight `V` is integrable. -/
theorem MemLp.integrable_sq_mul_norm_sq {F : Type*} [NormedAddCommGroup F] {g : α → F}
    (hg : MemLp g 2 μ) {V : α → ℝ} (hV : AEStronglyMeasurable V μ) {C : ℝ}
    (hVC : ∀ᵐ x ∂μ, V x ^ 2 ≤ C) :
    Integrable (fun x ↦ V x ^ 2 * ‖g x‖ ^ 2) μ :=
  hg.norm.integrable_sq.bdd_mul (hV.pow 2)
    (hVC.mono fun _ hx ↦ (Real.norm_of_nonneg (sq_nonneg _)).trans_le hx)

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

/-- For a complex inner product space `F` with its induced real structure, the real inner product
on `L²(α, F)` is the real part of the complex one. -/
theorem L2.real_inner_eq_re_inner {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (f g : Lp F 2 μ) :
    letI : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
    inner ℝ f g = Complex.re (inner ℂ f g) := by
  let : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  rw [L2.inner_def, L2.inner_def]
  exact integral_re (L2.integrable_inner (𝕜 := ℂ) f g)

/-- Evaluating coordinate `i` of an `L²(α, ℓ²(G))` function is adjoint to placing an
`L²(α, G i)` function in coordinate `i`. -/
theorem L2.inner_evalCLM_compLpL {ι : Type*} [DecidableEq ι] {G : ι → Type*}
    [∀ i, NormedAddCommGroup (G i)] [∀ i, InnerProductSpace 𝕜 (G i)] (i : ι)
    (g : Lp (lp G 2) 2 μ) (u : Lp (G i) 2 μ) :
    ⟪(lp.evalCLM 𝕜 G 2 i).compLpL 2 μ g, u⟫_𝕜 =
      ⟪g, (lp.singleContinuousLinearMap 𝕜 G 2 i).compLpL 2 μ u⟫_𝕜 := by
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(lp.evalCLM 𝕜 G 2 i).coeFn_compLpL g,
    (lp.singleContinuousLinearMap 𝕜 G 2 i).coeFn_compLpL u] with x h₁ h₂
  rw [h₁, h₂, lp.singleContinuousLinearMap_apply, lp.inner_single_right]
  rfl

/-- The L² inner product of an L² function `f` with the class of a square-integrable function
`g` is the integral of their pointwise inner product. -/
theorem L2.inner_toLp (f : Lp E 2 μ) {g : α → E} (hg : MemLp g 2 μ) :
    ⟪f, hg.toLp g⟫_𝕜 = ∫ x, ⟪f x, g x⟫_𝕜 ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hg.coeFn_toLp] with x hx
  rw [hx]

open Filter in
/-- **The squared `L²` norm of the positive part is differentiable**: on real `L²`, the map
`g ↦ ‖g⁺‖²` has derivative `k ↦ 2 ⟪f⁺, k⟫` at `f`. -/
theorem Lp.hasFDerivAt_norm_posPart_sq (f : Lp ℝ 2 μ) :
    HasFDerivAt (fun g : Lp ℝ 2 μ ↦ ‖Lp.posPart g‖ ^ 2)
      ((2 : ℝ) • innerSL ℝ (Lp.posPart f)) f := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  refine Asymptotics.IsBigO.trans_isLittleO ?_ (Asymptotics.isLittleO_norm_pow_id one_lt_two)
  refine Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun h ↦ ?_)
  -- The remainder is the integral of the pointwise remainder `φ` of `x ↦ (x⁺)²`, which lies
  -- between `0` and `h²` since `x ↦ (x⁺)²` is convex with `2`-Lipschitz derivative `2 x⁺`.
  set φ : α → ℝ := fun x ↦ max (f x + h x) 0 ^ 2 - max (f x) 0 ^ 2 - 2 * max (f x) 0 * h x
  have i₁ := L2.integrable_inner (𝕜 := ℝ) (Lp.posPart (f + h)) (Lp.posPart (f + h))
  have i₂ := L2.integrable_inner (𝕜 := ℝ) (Lp.posPart f) (Lp.posPart f)
  have i₃ := (L2.integrable_inner (𝕜 := ℝ) (Lp.posPart f) h).const_mul 2
  have i₁₂ : Integrable (fun x ↦ ⟪Lp.posPart (f + h) x, Lp.posPart (f + h) x⟫_ℝ -
      ⟪Lp.posPart f x, Lp.posPart f x⟫_ℝ) μ := i₁.sub i₂
  have hφeq : (fun x ↦ ⟪Lp.posPart (f + h) x, Lp.posPart (f + h) x⟫_ℝ -
      ⟪Lp.posPart f x, Lp.posPart f x⟫_ℝ - 2 * ⟪Lp.posPart f x, h x⟫_ℝ) =ᵐ[μ] φ := by
    filter_upwards [Lp.coeFn_posPart (f + h), Lp.coeFn_posPart f, Lp.coeFn_add f h]
      with x h₁ h₂ h₃
    simp only [φ, h₁, h₂, h₃, Pi.add_apply, RCLike.inner_apply, conj_trivial]
    ring
  have hrem : ‖Lp.posPart (f + h)‖ ^ 2 - ‖Lp.posPart f‖ ^ 2 -
      ((2 : ℝ) • innerSL ℝ (Lp.posPart f)) h = ∫ x, φ x ∂μ := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, smul_apply,
      innerSL_apply_apply, smul_eq_mul, L2.inner_def, L2.inner_def, L2.inner_def,
      ← integral_const_mul, ← integral_sub i₁ i₂, ← integral_sub i₁₂ i₃]
    exact integral_congr_ae hφeq
  -- Pointwise `0 ≤ φ ≤ h²`, so `0 ≤ ∫ φ ≤ ‖h‖²`.
  have hφ : ∀ᵐ x ∂μ, 0 ≤ φ x ∧ φ x ≤ h x * h x := Eventually.of_forall fun x ↦ by
    simpa only [φ, ← sq] using TauCeti.max_add_sq_sub_bounds (f x) (h x)
  have hh : ‖h‖ ^ 2 = ∫ x, h x * h x ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [RCLike.inner_apply, conj_trivial]
  rw [hrem, one_mul, norm_pow, norm_norm, Real.norm_of_nonneg
    (integral_nonneg_of_ae (hφ.mono fun x hx ↦ hx.1)), hh]
  exact integral_mono_ae ((i₁₂.sub i₃).congr hφeq)
    (by simpa only [RCLike.inner_apply, conj_trivial] using L2.integrable_inner (𝕜 := ℝ) h h)
    (hφ.mono fun x hx ↦ hx.2)

end MeasureTheory

namespace TauCeti

open MeasureTheory Finset

/-- The second moment of a finite sum of pairwise orthogonal random vectors is the sum
of their second moments. Only integrability of the pairwise inner products is required. -/
theorem integral_norm_sum_sq_of_pairwise_integral_inner_eq_zero
    {Ω ι E : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {X : ι → Ω → E} {s : Finset ι}
    (hint : ∀ i ∈ s, ∀ j ∈ s, Integrable (fun ω ↦ ⟪X i ω, X j ω⟫_ℝ) μ)
    (horth : Set.Pairwise ↑s fun i j ↦ (∫ ω, ⟪X i ω, X j ω⟫_ℝ ∂μ) = 0) :
    (∫ ω, ‖∑ i ∈ s, X i ω‖ ^ 2 ∂μ) = ∑ i ∈ s, ∫ ω, ‖X i ω‖ ^ 2 ∂μ := by
  simp_rw [← real_inner_self_eq_norm_sq, sum_inner, inner_sum]
  rw [integral_finsetSum _ fun i hi ↦ integrable_finsetSum _ fun j hj ↦ hint i hi j hj]
  refine sum_congr rfl fun i hi ↦ ?_
  rw [integral_finsetSum _ fun j hj ↦ hint i hi j hj]
  exact sum_eq_single_of_mem i hi fun j hj hji ↦ horth hi hj hji.symm

/-- The second moment of a finite sum of square-integrable real functions with vanishing
pairwise product integrals is the sum of their second moments. No independence or centering
assumption is required. -/
theorem integral_sq_sum_of_pairwise_integral_mul_eq_zero
    {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : ι → Ω → ℝ} {s : Finset ι}
    (hX : ∀ i ∈ s, MemLp (X i) 2 μ)
    (horth : Set.Pairwise ↑s fun i j ↦ (∫ ω, X i ω * X j ω ∂μ) = 0) :
    (∫ ω, (∑ i ∈ s, X i ω) ^ 2 ∂μ) = ∑ i ∈ s, ∫ ω, X i ω ^ 2 ∂μ := by
  simpa only [Real.norm_eq_abs, sq_abs] using
    integral_norm_sum_sq_of_pairwise_integral_inner_eq_zero
      (fun i hi j hj ↦ (hX i hi).integrable_inner (hX j hj))
      (by simpa only [Real.inner_apply] using horth)

end TauCeti

section IntegralInner

variable {α 𝕜 E : Type*} [MeasurableSpace α] {μ : Measure α} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] [NormedSpace ℝ E]

/-- Integration commutes with the inner product against a fixed vector in the right slot:
`∫ ⟪f x, c⟫ = ⟪∫ f, c⟫`. This is `integral_inner` with the integrand in the left slot. -/
theorem integral_inner_left {f : α → E} (hf : Integrable f μ) (c : E) :
    ∫ x, ⟪f x, c⟫_𝕜 ∂μ = ⟪∫ x, f x ∂μ, c⟫_𝕜 := by
  simpa only [innerSLFlip_apply_apply] using
    (innerSLFlip 𝕜 c).integral_comp_commSL RCLike.conj_smul hf

/-- The Hilbert space adjoint commutes with the integral of an operator-valued function:
`∫ (f x)† = (∫ f)†`, the counterpart of Mathlib's `integral_conj`. No integrability is needed,
since the adjoint is a real-linear isometric equivalence. -/
theorem ContinuousLinearMap.integral_adjoint {V W : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [CompleteSpace W] (f : α → V →L[ℂ] W) :
    ∫ x, ContinuousLinearMap.adjoint (f x) ∂μ = ContinuousLinearMap.adjoint (∫ x, f x ∂μ) :=
  (IsometryEquiv.toRealLinearIsometryEquivOfMapZero
    (ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := V) (F := W)).toIsometryEquiv
    (by simp)).toContinuousLinearEquiv.integral_comp_comm f

end IntegralInner

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
  obtain ⟨v, hv, hcover⟩ := hcover
  refine (ae_eq_zero_of_setIntegral_eq_zero_of_isPiSystem hgen hpi v hv hcover
    (fun n ↦ hfi _ (hv n)) ?_).trans (Lp.coeFn_zero ℝ 2 μ).symm
  intro s hs
  rw [← L2.inner_indicatorConstLp_one
    (hgen ▸ MeasurableSpace.measurableSet_generateFrom hs) (hfin s hs) f]
  exact (Submodule.mem_orthogonal _ f).mp hf _
    (Submodule.subset_span ⟨s, hs, rfl⟩)

/-- Initial-interval indicators have dense real linear span in `L²` for a Borel measure
finite on initial intervals of a second-countable linearly ordered space. -/
theorem topologicalClosure_span_indicatorConstLp_Iic_eq_top
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [SecondCountableTopology α]
    [LinearOrder α] [OrderTopology α] [BorelSpace α] {μ : Measure α}
    (hμ : ∀ a, μ (Set.Iic a) ≠ ∞) :
    (Submodule.span ℝ (Set.range fun a : α ↦
      indicatorConstLp (μ := μ) 2 measurableSet_Iic (hμ a) (1 : ℝ))).topologicalClosure = ⊤ := by
  classical
  cases isEmpty_or_nonempty α
  · apply top_unique
    intro f _
    have hf : f = 0 := Lp.ext (Filter.Eventually.of_forall (fun a ↦ isEmptyElim a))
    rw [hf]
    exact Submodule.zero_mem _
  have hgen : ‹MeasurableSpace α› =
      MeasurableSpace.generateFrom (Set.range Set.Iic) :=
    (BorelSpace.measurable_eq (α := α)).trans (borel_eq_generateFrom_Iic α)
  have hcover : IsCountablySpanning (Set.range (Set.Iic : α → Set α)) := by
    obtain ⟨u, hu⟩ := Filter.exists_seq_tendsto (Filter.atTop : Filter α)
    refine ⟨fun n ↦ Set.Iic (u n), fun n ↦ Set.mem_range_self _, ?_⟩
    ext a
    simp only [Set.mem_iUnion, Set.mem_Iic, Set.mem_univ, iff_true]
    exact (hu.eventually (Filter.eventually_ge_atTop a)).exists
  have hfin : ∀ s ∈ Set.range Set.Iic, μ s ≠ ∞ := by
    rintro _ ⟨a, rfl⟩
    exact hμ a
  have hdense := topologicalClosure_span_indicatorConstLp_eq_top_of_isPiSystem
    hgen isPiSystem_Iic hcover hfin
  have hset : {g : Lp ℝ 2 μ | ∃ (s : Set α) (hs : s ∈ Set.range Set.Iic),
      g = indicatorConstLp 2 (hgen ▸ MeasurableSpace.measurableSet_generateFrom hs)
        (hfin s hs) 1} = Set.range (fun a : α ↦
        indicatorConstLp (μ := μ) 2 measurableSet_Iic (hμ a) (1 : ℝ)) := by
    ext g
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact Set.mem_range_self a
    · rintro ⟨a, rfl⟩
      exact ⟨Set.Iic a, Set.mem_range_self a, rfl⟩
  rwa [hset] at hdense

end TauCeti
