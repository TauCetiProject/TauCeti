/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
public import TauCeti.Geometry.Manifold.Algebra.ComplexSmoothFunctions
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import TauCeti.MeasureTheory.Function.L2Space

/-!
# Smooth functions are dense in `L²` of a compact manifold

Let `M` be a compact Hausdorff manifold modelled on a finite-dimensional real space and `μ` a
finite Borel measure on `M`. A smooth function on `M` with values in `𝕜 = ℝ` or `ℂ` is continuous,
hence square-integrable, so it has a class in `L²(M, μ)`; for `𝕜 = ℂ` this is the complex-linear
map `ContMDiffMap.toL2`. This file proves that these classes are dense
(`ContMDiffMap.denseRange_toLp`, and `ContMDiffMap.denseRange_toL2` for `ℂ`): they form a
`𝕜`-subspace, and a function in `L²(M, μ)` orthogonal to it has zero integral against every
real-valued smooth function, and therefore vanishes almost everywhere by the fundamental lemma of
the calculus of variations on manifolds (`ae_eq_zero_of_integral_contMDiff_smul_eq_zero`).

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
finite-dimensional real space, the classes in `L²(M, μ)` of the `𝕜`-valued smooth functions are
dense, for every finite Borel measure `μ` and `𝕜 = ℝ` or `ℂ`. -/
theorem denseRange_toLp (𝕜 : Type*) [RCLike 𝕜] :
    DenseRange fun u : C^∞⟮I, M; 𝓘(ℝ, 𝕜), 𝕜⟯ ↦ ContinuousMap.toLp 2 μ 𝕜 (u : C(M, 𝕜)) := by
  -- The classes of smooth functions form a `𝕜`-subspace of `L²`.
  let S : Submodule 𝕜 (Lp 𝕜 2 μ) :=
    { carrier := Set.range fun u : C^∞⟮I, M; 𝓘(ℝ, 𝕜), 𝕜⟯ ↦ ContinuousMap.toLp 2 μ 𝕜 (u : C(M, 𝕜))
      add_mem' := by
        rintro _ _ ⟨u, rfl⟩ ⟨v, rfl⟩
        refine ⟨u + v, ?_⟩
        rw [← map_add]
        exact congrArg (ContinuousMap.toLp 2 μ 𝕜) <| ContinuousMap.ext fun x ↦ by
          rw [ContinuousMap.coe_ofClass, ContMDiffMap.coe_add, ContinuousMap.add_apply,
            ContinuousMap.coe_ofClass, ContinuousMap.coe_ofClass, Pi.add_apply]
      zero_mem' := ⟨0, map_zero (ContinuousMap.toLp 2 μ 𝕜)⟩
      smul_mem' := by
        rintro c _ ⟨u, rfl⟩
        let w : C^∞⟮I, M; 𝓘(ℝ, 𝕜), 𝕜⟯ :=
          ⟨fun x ↦ c * u x, (ContinuousLinearMap.mul ℝ 𝕜 c).contMDiff.comp u.contMDiff⟩
        have hw (x : M) : w x = c * u x := rfl
        refine ⟨w, ?_⟩
        rw [← map_smul]
        exact congrArg (ContinuousMap.toLp 2 μ 𝕜) <| ContinuousMap.ext fun x ↦ by
          rw [ContinuousMap.coe_ofClass, hw, ContinuousMap.smul_apply, ContinuousMap.coe_ofClass,
            smul_eq_mul] }
  -- A function orthogonal to the smooth functions vanishes almost everywhere.
  have hK : Sᗮ = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 fun f hf ↦ Lp.eq_zero_iff_ae_eq_zero.2 ?_
    refine ae_eq_zero_of_integral_contMDiff_smul_eq_zero I
      ((Lp.memLp f).locallyIntegrable one_le_two) fun g hg _ ↦ ?_
    let g' : C^∞⟮I, M; 𝓘(ℝ, 𝕜), 𝕜⟯ :=
      ⟨fun x ↦ (g x : 𝕜), (RCLike.ofRealCLM (K := 𝕜)).contMDiff.comp hg⟩
    have h := Submodule.inner_left_of_mem_orthogonal (K := S) ⟨g', rfl⟩ hf
    rw [L2.inner_toLp_continuousMap] at h
    have hg' (x : M) : (g' : C(M, 𝕜)) x = g x := rfl
    have h' := congrArg (starRingEnd 𝕜) h
    rw [← integral_conj, map_zero] at h'
    simpa [hg', RCLike.real_smul_eq_coe_mul] using h'
  exact Submodule.dense_iff_topologicalClosure_eq_top.2
    (Submodule.topologicalClosure_eq_top_iff.2 hK)

/-- **Smooth functions are dense in `L²`.** On a compact Hausdorff manifold modelled on a
finite-dimensional real space, the classes in `L²(M, μ)` of the complex-valued smooth functions
are dense, for every finite Borel measure `μ`. -/
theorem denseRange_toL2 : DenseRange (toL2 (I := I) μ) :=
  denseRange_toLp μ ℂ

end ContMDiffMap
