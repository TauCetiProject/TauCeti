/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import TauCeti.Geometry.Manifold.Algebra.ComplexSmoothFunctions
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Smooth functions on a compact manifold in `Lᵖ`

A complex-valued smooth function on a compact manifold `M` is continuous, so it defines an element
of `Lᵖ(M, μ)` for every finite measure `μ` (`ContMDiffMap.toLp`). Its norm is the `Lᵖ` norm of the
function (`ContMDiffMap.norm_toLp`), and for `p = 2` the inner product of two such classes is the
integral of the pointwise inner product (`ContMDiffMap.inner_toLp`). On a finite-dimensional
Hausdorff manifold, smooth functions are dense in `L²(M, μ)` (`ContMDiffMap.denseRange_toLp`): a
function orthogonal to all of them integrates to zero against every real smooth function, so it
vanishes almost everywhere.

## Main definitions

* `ContMDiffMap.toLp`: a complex-valued smooth function on a compact manifold as an element of
  `Lᵖ(μ)`.

## Main results

* `ContMDiffMap.denseRange_toLp`: smooth functions are dense in `L²(M, μ)`.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal ContDiff Manifold

namespace ContMDiffMap

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [CompactSpace M] [MeasurableSpace M] [BorelSpace M] (p : ℝ≥0∞) [Fact (1 ≤ p)]
  (μ : Measure M) [IsFiniteMeasure μ]

/-- A complex-valued smooth function on a compact manifold, as an element of `Lᵖ(μ)` for a finite
measure `μ`. -/
def toLp : C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ] Lp ℂ p μ :=
  (ContinuousMap.toLp p μ ℂ).toLinearMap ∘ₗ
    { toFun u := ⟨u, u.contMDiff.continuous⟩
      map_add' _ _ := rfl
      map_smul' c u := by
        ext x
        simp }

variable {I p μ}

theorem toLp_apply (u : C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    toLp I p μ u = ContinuousMap.toLp p μ ℂ ⟨u, u.contMDiff.continuous⟩ :=
  (rfl)

/-- The class of a smooth function in `Lᵖ` is represented by the function itself. -/
theorem coeFn_toLp (u : C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) : toLp I p μ u =ᵐ[μ] u := by
  rw [toLp_apply]
  exact ContinuousMap.coeFn_toLp (p := p) (𝕜 := ℂ) μ _

/-- The norm of the class of a smooth function in `Lᵖ` is its `Lᵖ` norm. -/
theorem norm_toLp (u : C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    ‖toLp I p μ u‖ = (eLpNorm u p μ).toReal := by
  rw [Lp.norm_def, eLpNorm_congr_ae (coeFn_toLp u)]

/-- The `L²` inner product of two smooth functions is the integral of their pointwise inner
product. -/
theorem inner_toLp (u v : C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    inner ℂ (toLp I 2 μ u) (toLp I 2 μ v) = ∫ x, inner ℂ (u x) (v x) ∂μ := by
  rw [toLp_apply, toLp_apply, ContinuousMap.inner_toLp]
  simp [RCLike.inner_apply]

/-- **Smooth functions are dense in `L²`.** A function in `L²(μ)` orthogonal to every smooth
function has zero integral against every real smooth function, so it vanishes almost
everywhere. -/
theorem denseRange_toLp [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] :
    DenseRange (toLp I 2 μ) := by
  have hK : (LinearMap.range (toLp I 2 μ))ᗮ = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 fun f hf ↦ Lp.eq_zero_iff_ae_eq_zero.2 ?_
    refine ae_eq_zero_of_integral_contMDiff_smul_eq_zero I
      ((Lp.memLp f).locallyIntegrable one_le_two) fun g hg _ ↦ ?_
    obtain ⟨φ, rfl⟩ : ∃ φ : C^∞⟮I, M; ℝ⟯, ⇑φ = g := ⟨⟨g, hg⟩, rfl⟩
    have h := Submodule.inner_right_of_mem_orthogonal
      (LinearMap.mem_range_self _ (ContMDiffMap.ofReal φ)) hf
    rw [L2.inner_def] at h
    rw [← h]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_toLp (p := 2) (μ := μ) (ContMDiffMap.ofReal φ)] with x hx
    rw [hx, ContMDiffMap.ofReal_apply]
    simp [Complex.real_smul, mul_comm]
  have hd := Submodule.dense_iff_topologicalClosure_eq_top.2
    (Submodule.topologicalClosure_eq_top_iff.2 hK)
  rwa [LinearMap.coe_range] at hd

end ContMDiffMap
