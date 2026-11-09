/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.InnerProductSpace.Adjoint

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
-/

public section

open scoped ComplexConjugate InnerProductSpace

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
