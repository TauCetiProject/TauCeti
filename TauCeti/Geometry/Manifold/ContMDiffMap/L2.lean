/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
public import TauCeti.Geometry.Manifold.Algebra.ComplexSmoothFunctions
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Smooth functions are dense in `L²` of a compact manifold

Let `M` be a compact Hausdorff manifold modelled on a finite-dimensional real space and `μ` a
finite Borel measure on `M`. A smooth function on `M` is continuous, hence square-integrable, so
it has a class in `L²(M, μ)` (`ContMDiffMap.toL2`). This file proves that these classes are dense
(`ContMDiffMap.denseRange_toL2`): a function in `L²(M, μ)` orthogonal to every smooth function
has zero integral against every smooth function, and therefore vanishes almost everywhere by the
fundamental lemma of the calculus of variations on manifolds
(`ae_eq_zero_of_integral_contMDiff_smul_eq_zero`).

No regularity of `μ` is assumed: the argument only uses that `μ` is finite, so that continuous
functions are square-integrable.
-/

public section

noncomputable section

open MeasureTheory
open scoped ContDiff Manifold InnerProductSpace

namespace ContMDiffMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

variable (μ : Measure M) [IsFiniteMeasure μ]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] in
/-- The class in `L²(M, μ)` of a complex-valued smooth function on a compact manifold, as a
complex-linear map. -/
def toL2 : C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ] Lp ℂ 2 μ :=
  (ContinuousMap.toLp 2 μ ℂ).toLinearMap ∘ₗ
    { toFun u := (u : C(M, ℂ))
      map_add' _ _ := rfl
      map_smul' c u := ContinuousMap.ext fun x ↦ complex_smul_apply c u x }

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] in
@[simp]
theorem toL2_apply (u : C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    toL2 μ u = ContinuousMap.toLp 2 μ ℂ (u : C(M, ℂ)) :=
  (rfl)

/-- **Smooth functions are dense in `L²`.** On a compact Hausdorff manifold modelled on a
finite-dimensional real space, the classes in `L²(M, μ)` of the complex-valued smooth functions
are dense, for every finite Borel measure `μ`. -/
theorem denseRange_toL2 : DenseRange (toL2 (I := I) μ) := by
  -- A function orthogonal to the smooth functions vanishes almost everywhere.
  have hK : (LinearMap.range (toL2 (I := I) μ))ᗮ = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 fun f hf ↦ Lp.eq_zero_iff_ae_eq_zero.2 ?_
    refine ae_eq_zero_of_integral_contMDiff_smul_eq_zero I
      ((Lp.memLp f).integrable one_le_two).locallyIntegrable fun g hg _ ↦ ?_
    let g' : C^∞⟮I, M; ℝ⟯ := ⟨g, hg⟩
    have h := Submodule.inner_right_of_mem_orthogonal
      (LinearMap.mem_range_self (toL2 μ) (ofReal g')) hf
    rw [toL2_apply, L2.inner_def] at h
    rw [← h]
    refine integral_congr_ae ?_
    filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ (ofReal g' : C(M, ℂ))] with x hx
    rw [hx, ContinuousMap.coe_ofClass, ofReal_apply, RCLike.inner_apply, Complex.conj_ofReal,
      Complex.real_smul]
    exact mul_comm _ _
  have hd := Submodule.dense_iff_topologicalClosure_eq_top.2
    (Submodule.topologicalClosure_eq_top_iff.2 hK)
  rwa [LinearMap.coe_range] at hd

end ContMDiffMap
