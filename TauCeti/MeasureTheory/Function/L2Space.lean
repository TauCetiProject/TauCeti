/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Inner products of square-integrable functions

The pointwise inner product of two square-integrable functions with values in an inner product
space is integrable. Mathlib states this for elements of `L²` (`MeasureTheory.L2.integrable_inner`);
this file gives the form for functions satisfying `MemLp f 2 μ`, which is how second-moment
hypotheses on random vectors are usually stated, together with the special case of a quadratic
form `⟪B (f x), f x⟫` of a matrix `B` on a Euclidean-valued function.
For counting measure, singleton-supported vectors separate L² functions.

For a complex inner product space `F` regarded as a real one (`InnerProductSpace.complexToReal`),
the real inner product on `L²(α, F)` is the real part of the complex one
(`MeasureTheory.L2.real_inner_eq_re_inner`). For a family of inner product spaces `G i`, evaluating
coordinate `i` of an `L²(α, ℓ²(G))` function is adjoint to placing an `L²(α, G i)` function in
coordinate `i` (`MeasureTheory.L2.inner_evalCLM_compLpL`).
-/

public section

open scoped InnerProductSpace

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

end MeasureTheory
