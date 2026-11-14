/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.TotallyReal.Basic
public import TauCeti.Geometry.Symplectic.Complex.CoordinateSpace
public import TauCeti.LinearAlgebra.TotallyReal.Complex
public import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Model examples of totally real embeddings

The real locus in complex coordinate space and the unit circle give totally real embeddings.
Complex tangent planes fail the maximal-total-reality test, and a real line in complex dimension
two fails the half-dimension condition. The statements use the native constant smooth structure
for multiplication by `I`, interpreted pointwise, and allow every embedding regularity.

The real locus is also Lagrangian for the standard symplectic form `ω₀ = Σ_j ds_j ∧ dt_j`, and the
Lagrangian comparison recovers its total reality both for `I`, which `ω₀` tames, and for `-I`,
which `-ω₀` tames. The conclusion does not depend on the sign of the complex structure, in
agreement with `isTotallyRealEmbedding_neg_iff`.

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
  have hinj : Function.Injective L := Function.Injective.piMap fun _ ↦ Complex.ofReal_injective
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

section Lagrangian

variable {ι : Type*} [Fintype ι]

/-- The real locus in complex coordinate space is a Lagrangian embedding for every nonzero
multiple `c Σ_j ds_j ∧ dt_j` of the standard symplectic form. -/
theorem isLagrangianEmbedding_realLocus_rescale (c : ℝ) (hc : c ≠ 0) :
    (SymplecticForm.isNondegenerate_constSmooth
        ((stdComplexPiSymplecticForm ι).rescale c hc)).IsLagrangianEmbedding
      𝓘(ℝ, ι → ℝ) (ContinuousLinearMap.piMap fun _ : ι ↦ Complex.ofRealCLM) :=
  (SmoothTwoForm.IsNondegenerate.isLagrangianEmbedding_iff_of_isSmoothEmbedding
    (isTotallyRealEmbedding_realLocus ∞).isSmoothEmbedding).2
    ((SymplecticForm.isLagrangianMap_continuousLinearMap_iff _ _).2
      ((SymplecticForm.isLagrangian_rescale_iff _ _).2
        isLagrangian_stdComplexPiSymplecticForm_range_ofReal))

/-- The real locus in complex coordinate space is a Lagrangian embedding for the standard
symplectic form `Σ_j ds_j ∧ dt_j`: the case `c = 1` of `isLagrangianEmbedding_realLocus_rescale`. -/
theorem isLagrangianEmbedding_realLocus :
    (SymplecticForm.isNondegenerate_constSmooth
        (stdComplexPiSymplecticForm ι)).IsLagrangianEmbedding
      𝓘(ℝ, ι → ℝ) (ContinuousLinearMap.piMap fun _ : ι ↦ Complex.ofRealCLM) := by
  simpa using isLagrangianEmbedding_realLocus_rescale (ι := ι) 1 one_ne_zero

/-! The Lagrangian comparison recovers the smooth case of `isTotallyRealEmbedding_realLocus`:
the real locus, Lagrangian for `Σ_j ds_j ∧ dt_j`, is totally real for multiplication by `I`,
which that form tames, and, Lagrangian for `-Σ_j ds_j ∧ dt_j`, is totally real for
multiplication by `-I`, which the reversed form tames. -/

example :
    IsTotallyRealEmbedding 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℂ) ∞
      (AlmostComplexStructure.ofComplexModule (ι → ℂ)).constSmooth.almostComplexStructureAt
      (ContinuousLinearMap.piMap fun _ : ι ↦ Complex.ofRealCLM) :=
  isLagrangianEmbedding_realLocus.isTotallyRealEmbedding
    (SymplecticForm.tames_constSmooth_iff.2 stdComplexPiSymplecticForm_tames)

example :
    IsTotallyRealEmbedding 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℂ) ∞
      (-AlmostComplexStructure.ofComplexModule (ι → ℂ)).constSmooth.almostComplexStructureAt
      (ContinuousLinearMap.piMap fun _ : ι ↦ Complex.ofRealCLM) :=
  (isLagrangianEmbedding_realLocus_rescale (-1) neg_one_lt_zero.ne).isTotallyRealEmbedding
    (SymplecticForm.tames_constSmooth_iff.2
      (stdComplexPiSymplecticForm_tames.rescale_neg_of_neg neg_one_lt_zero))

end Lagrangian

end TauCeti
