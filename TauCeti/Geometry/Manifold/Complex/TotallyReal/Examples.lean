/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.TotallyReal.Basic
public import TauCeti.Geometry.Symplectic.Complex.Line
public import TauCeti.LinearAlgebra.TotallyReal.Complex
public import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Model examples of totally real embeddings

The real locus in complex coordinate space and the unit circle give totally real embeddings.
Complex tangent planes fail the maximal-total-reality test, and a real line in complex dimension
two fails the half-dimension condition. The statements use the native constant smooth structure
for multiplication by `I`, interpreted pointwise, and allow every embedding regularity.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, Appendix B.
-/

public noncomputable section

open Manifold Module Complex
open scoped Manifold ContDiff

namespace TauCeti

/-- The real locus in complex coordinate space is a totally real embedding for every
regularity, including finite orders. -/
theorem isTotallyRealEmbedding_realLocus {ι : Type*} [Fintype ι] (n : ℕ∞ω) :
    IsTotallyRealEmbedding 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℂ) n
      (AlmostComplexStructure.ofComplexModule (ι → ℂ)).constSmooth.almostComplexStructureAt
      (ContinuousLinearMap.piMap fun _ : ι ↦ Complex.ofRealCLM) := by
  let L : (ι → ℝ) →L[ℝ] (ι → ℂ) := ContinuousLinearMap.piMap fun _ ↦ Complex.ofRealCLM
  have hinj : Function.Injective L := by
    intro x y h
    funext i
    apply Complex.ofReal_injective
    simpa [L] using congrFun h i
  rw [ContinuousLinearMap.isTotallyRealEmbedding_iff]
  refine ⟨by simp [Module.finrank_pi_fintype, Nat.mul_comm], ?_⟩
  have hJ : (AlmostComplexStructure.ofComplexModule (ι → ℂ)).toLinearMap =
      (LinearMap.lsmul ℂ (ι → ℂ) I).restrictScalars ℝ := by
    ext v i
    simp [AlmostComplexStructure.ofComplexModule_apply]
  rw [hJ]
  have hr : LinearMap.range L.toLinearMap =
      LinearMap.range (LinearMap.pi fun i ↦
        (LinearMap.proj i : (ι → ℝ) →ₗ[ℝ] ℝ).smulRight (1 : ℂ)) := by
    congr 1
    ext x i
    simp [L]
  have ht : IsTotallyReal ((LinearMap.lsmul ℂ (ι → ℂ) I).restrictScalars ℝ)
      (LinearMap.range L.toLinearMap) := by
    rw [hr]
    exact isTotallyReal_range_pi_smulRight
  have hJi := (AlmostComplexStructure.ofComplexModule (ι → ℂ)).injective
  rw [hJ] at hJi
  apply ht.isMaximalTotallyReal (hJi.comp (LinearMap.range L.toLinearMap).subtype_injective)
  rw [LinearMap.finrank_range_of_inj hinj]
  simp [Module.finrank_pi_fintype, Nat.mul_comm]

attribute [local instance] finrank_real_complex_fact'

/-- The unit circle is a totally real embedding, with arbitrary finite or analytic regularity. -/
theorem isTotallyRealEmbedding_circle (n : ℕ∞ω) :
    IsTotallyRealEmbedding (𝓡 1) 𝓘(ℝ, ℂ) n
      (AlmostComplexStructure.ofComplexModule ℂ).constSmooth.almostComplexStructureAt
      (fun z : Circle ↦ (z : ℂ)) := by
  -- Mathlib defines `Circle`, its topology and its charts using the unit sphere. Present
  -- that definitionally identical formulation to use the native sphere differential API.
  change IsTotallyRealEmbedding (𝓡 1) 𝓘(ℝ, ℂ) n
    (AlmostComplexStructure.ofComplexModule ℂ).constSmooth.almostComplexStructureAt
    (fun z : Metric.sphere (0 : ℂ) 1 ↦ (z : ℂ))
  have hmap : IsMaximalTotallyRealMap (𝓡 1) 𝓘(ℝ, ℂ)
      (AlmostComplexStructure.ofComplexModule ℂ).constSmooth.almostComplexStructureAt
      (fun z : Metric.sphere (0 : ℂ) 1 ↦ (z : ℂ)) := by
    rw [isMaximalTotallyRealMap_iff]
    intro x
    have hi : Function.Injective
        (mfderiv (𝓡 1) 𝓘(ℝ, ℂ) (fun z : Metric.sphere (0 : ℂ) 1 ↦ (z : ℂ)) x) := by
      intro v w h
      apply injective_mvfderiv_subtypeVal_sphere x
      rw [mvfderiv_apply_eq_mfderiv_apply, mvfderiv_apply_eq_mfderiv_apply]
      exact h
    have hd : finrank ℝ
        (LinearMap.range (mfderiv (𝓡 1) 𝓘(ℝ, ℂ)
          (fun z : Metric.sphere (0 : ℂ) 1 ↦ (z : ℂ)) x).toLinearMap) = 1 := by
      rw [LinearMap.finrank_range_of_inj hi, finrank_tangentSpace]
      simp
    rw [AlmostComplexStructure.constSmooth_almostComplexStructureAt]
    exact (isLagrangian_stdComplexSymplecticForm_of_finrank_eq_one hd).isMaximalTotallyReal_of_tames
      stdComplexSymplecticForm_tames
  have he : IsTotallyRealEmbedding (𝓡 1) 𝓘(ℝ, ℂ) ω
      (AlmostComplexStructure.ofComplexModule ℂ).constSmooth.almostComplexStructureAt
      (fun z : Metric.sphere (0 : ℂ) 1 ↦ (z : ℂ)) :=
    isTotallyRealEmbedding_of_contMDiff (by simp) contMDiff_coe_sphere
      Topology.IsEmbedding.subtypeVal (by simp) hmap
  exact he.of_le le_top

/-- A real line in complex dimension two fails the required half-dimensionality. -/
theorem not_isTotallyRealEmbedding_realLine (n : ℕ∞ω) :
    ¬ IsTotallyRealEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ × ℂ) n
      (AlmostComplexStructure.ofComplexModule (ℂ × ℂ)).constSmooth.almostComplexStructureAt
      (fun r : ℝ ↦ ((r : ℂ), 0)) := by
  intro h
  have hd := h.two_mul_finrank
  norm_num [Module.finrank_prod] at hd

/-- A complex line in complex dimension two has complex tangencies, despite having the
correct real dimension. -/
theorem not_isTotallyRealEmbedding_complexLine (n : ℕ∞ω) :
    ¬ IsTotallyRealEmbedding 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ × ℂ) n
      (AlmostComplexStructure.ofComplexModule (ℂ × ℂ)).constSmooth.almostComplexStructureAt
      ((ContinuousLinearMap.inl ℂ ℂ ℂ).restrictScalars ℝ) := by
  intro h
  have ht := (ContinuousLinearMap.isTotallyRealEmbedding_iff _ _).1 h |>.2 |>.isTotallyReal
  rw [isTotallyReal_iff, Submodule.disjoint_def] at ht
  have hz : (1, 0) = (0 : ℂ × ℂ) := ht (1, 0) ⟨1, rfl⟩
    ⟨(-I, 0), ⟨-I, rfl⟩, by
      ext <;> simp [AlmostComplexStructure.ofComplexModule_apply]⟩
  exact one_ne_zero (congrArg Prod.fst hz)

end TauCeti
