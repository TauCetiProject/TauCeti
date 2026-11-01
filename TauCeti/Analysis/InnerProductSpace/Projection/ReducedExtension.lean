/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5, GPT-6
-/
module

public import TauCeti.Analysis.InnerProductSpace.Projection.Block
public import TauCeti.Analysis.InnerProductSpace.InvariantSubspace
public import TauCeti.Analysis.InnerProductSpace.PointSpectrum

/-!
# Symmetry and spectral bounds for reduced extensions

`ContinuousLinearMap.reducedExtension` is defined in `Projection.Block`, together with its
block actions, quadratic-form splitting and global bounds from local quadratic-form bounds.
This module proves symmetry of the extension for invariant symmetric blocks, without a
completeness assumption, and obtains the global form bounds from finite-dimensional
restricted point-spectrum containment. For an invariant block, every real eigenvalue of the
extension is either the scalar `κ` or an eigenvalue of the original operator carried by the
block, so the extension can move the spectrum off the block wherever it is convenient.

## Provenance

The spectral consequences are adapted from the maintained
[AIQ-Kitware DKPS formalization](https://github.com/AIQ-Kitware/aiq-dkps-formalization)
(Kitware, Inc.; Apache-2.0), `ForTauCeti/Analysis/InnerProductSpace/ReducedExtension.lean`.
The common block splitting and bounds reuse `Projection.Block` rather than duplicating them.
-/

public section

open scoped InnerProductSpace

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The reduced extension of a symmetric operator along an invariant subspace is symmetric,
without any completeness hypothesis on the ambient inner product space. -/
theorem isSymmetric_reducedExtension (T : E →L[𝕜] E)
    {W : Submodule 𝕜 E} [W.HasOrthogonalProjection]
    (hT : (T : E →ₗ[𝕜] E).IsSymmetric) (hW : ∀ x ∈ W, T x ∈ W) (κ : ℝ) :
    (T.reducedExtension W κ : E →ₗ[𝕜] E).IsSymmetric := by
  have hcomm : Commute (W.starProjection : E →ₗ[𝕜] E) (T : E →ₗ[𝕜] E) :=
    (W.isReducing_iff_commute_starProjection (T : E →ₗ[𝕜] E)).mp
      ((hT.isReducing_iff_mem_invtSubmodule W).mpr hW)
  have hblock : ((T : E →ₗ[𝕜] E) * (W.starProjection : E →ₗ[𝕜] E)).IsSymmetric :=
    hT.mul_of_commute W.starProjection_isSymmetric hcomm.symm
  have hscalar : ((κ : 𝕜) • (Wᗮ.starProjection : E →ₗ[𝕜] E)).IsSymmetric :=
    LinearMap.IsSymmetric.smul (RCLike.conj_ofReal κ) Wᗮ.starProjection_isSymmetric
  rw [T.reducedExtension_def W κ]
  simpa only [ContinuousLinearMap.toLinearMap_add,
    ContinuousLinearMap.toLinearMap_smul, ContinuousLinearMap.toLinearMap_comp,
    ← Module.End.mul_eq_comp] using hblock.add hscalar

/-- Restricted point-spectrum containment in `(-∞, c]` gives an upper bound
for a reduced extension with scalar `κ ≤ c`. -/
theorem re_inner_reducedExtension_self_le_of_pointSpectrumIn (T : E →L[𝕜] E)
    {W : Submodule 𝕜 E} [W.HasOrthogonalProjection] [FiniteDimensional 𝕜 W]
    (hT : (T : E →ₗ[𝕜] E).IsSymmetric) (hW : ∀ x ∈ W, T x ∈ W)
    {c κ : ℝ} (hκ : κ ≤ c)
    (hspec : Module.End.PointSpectrumIn (T : E →ₗ[𝕜] E) W (Set.Iic c)) (x : E) :
    RCLike.re ⟪T.reducedExtension W κ x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2 :=
  T.re_inner_reducedExtension_self_le W hW
    (r := c) (κ := κ) hκ
    (fun _ hy => hT.re_inner_apply_self_le_of_pointSpectrumIn hW hspec hy) x

/-- Restricted point-spectrum containment in `[c, ∞)` gives a lower bound
for a reduced extension with scalar `κ ≥ c`. -/
theorem le_re_inner_reducedExtension_self_of_pointSpectrumIn (T : E →L[𝕜] E)
    {W : Submodule 𝕜 E} [W.HasOrthogonalProjection] [FiniteDimensional 𝕜 W]
    (hT : (T : E →ₗ[𝕜] E).IsSymmetric) (hW : ∀ x ∈ W, T x ∈ W)
    {c κ : ℝ} (hκ : c ≤ κ)
    (hspec : Module.End.PointSpectrumIn (T : E →ₗ[𝕜] E) W (Set.Ici c)) (x : E) :
    c * ‖x‖ ^ 2 ≤ RCLike.re ⟪T.reducedExtension W κ x, x⟫_𝕜 :=
  T.le_re_inner_reducedExtension_self W hW
    (r := c) (κ := κ) hκ
    (fun _ hy => hT.le_re_inner_apply_self_of_pointSpectrumIn hW hspec hy) x

/-- Along an invariant subspace `W`, every real eigenvalue of the reduced extension
`A P_W + κ P_{Wᗮ}` is either `κ` or an eigenvalue of `A` with an eigenvector in `W`. -/
theorem restrictedPointSpectrum_reducedExtension_subset (A : E →L[𝕜] E)
    {W : Submodule 𝕜 E} [W.HasOrthogonalProjection] (hW : ∀ x ∈ W, A x ∈ W) (κ : ℝ) :
    Module.End.restrictedPointSpectrum (A.reducedExtension W κ : E →ₗ[𝕜] E) ⊤ ⊆
      insert κ (Module.End.restrictedPointSpectrum (A : E →ₗ[𝕜] E) W) := by
  intro μ hμ
  obtain ⟨x, -, hx0, hx⟩ := Module.End.mem_restrictedPointSpectrum_iff.mp hμ
  rw [coe_coe] at hx
  by_cases hx' : Wᗮ.starProjection x = 0
  · -- The eigenvector lies in `W`, where the extension agrees with `A`.
    have hxW : x ∈ W := by
      simpa [Submodule.orthogonal_orthogonal] using Wᗮ.starProjection_apply_eq_zero_iff.mp hx'
    refine Or.inr (Module.End.mem_restrictedPointSpectrum hxW hx0 ?_)
    rwa [coe_coe, ← A.reducedExtension_apply_of_mem W κ hxW]
  · -- The `Wᗮ` component of the eigenvector equation reads `κ x'' = μ x''`.
    have h := congrArg Wᗮ.starProjection hx
    rw [reducedExtension_apply, map_add, map_smul, map_smul,
      W.starProjection_orthogonal_apply_eq_zero (hW _ (W.starProjection_apply_mem x)), zero_add,
      Wᗮ.starProjection_eq_self_iff.mpr (Wᗮ.starProjection_apply_mem x)] at h
    exact Or.inl (by exact_mod_cast (smul_left_injective 𝕜 hx' h).symm)

end ContinuousLinearMap
