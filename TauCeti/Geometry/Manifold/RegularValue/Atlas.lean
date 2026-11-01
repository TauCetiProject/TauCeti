/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.RegularValue.ManifoldLevel
import TauCeti.Geometry.Manifold.Immersion.Diffeomorph

/-!
# Independence of regular-fibre atlases

The regular-fibre atlas is constructed by choosing a target chart containing the regular value.
`TauCeti.RegularFiber.exists_chartDiffeomorph` identifies the atlases from any two such charts by
the identity on the actual fibre. Thus its smooth structure does not depend on target coordinates.

For a vector-space target, `TauCeti.exists_regularFiberLevelDiffeomorph` identifies the preferred
manifold-valued regular-fibre atlas with the regular-level atlas. Both comparisons preserve the
ambient point and its subspace topology, including for empty fibres. The two charted-space
arguments are explicit in the statements to keep both atlases on the same subtype, without a
type copy or a competing global instance.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2013,
  Corollary 5.14 and Proposition 5.38 (regular level sets and their tangent spaces).
-/

public section

open Module
open scoped ContDiff Manifold

namespace TauCeti

variable {E H M F G N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {m : ℕ∞ω} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I m M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace G]
  {J : ModelWithCorners ℝ F G} [TopologicalSpace N] [ChartedSpace G N]
  {f : M → N} {c : N}

namespace RegularFiber

/-- The identity of a regular fibre is a `C^m` diffeomorphism between the atlases constructed
using any two target charts containing the value. Neither separation nor nonemptiness is needed.
The two charted-space arguments are explicit because the underlying subtype is the same. -/
theorem exists_chartDiffeomorph (hm : 1 ≤ m) (hf : ContMDiff I J m f)
    (φ ψ : PartialDiffeomorph J 𝓘(ℝ, F) N F m) (hφ : c ∈ φ.source) (hψ : c ∈ ψ.source)
    (hreg : IsRegularValue I J f c) :
    ∃ e : @Diffeomorph ℝ _ _ _ _ _ _ _ _ _ _ _
      𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ F) → ℝ)
      𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ F) → ℝ)
      {x : M // f x = c} _ (chartedSpaceOfChart hm hf φ hφ hreg)
      {x : M // f x = c} _ (chartedSpaceOfChart hm hf ψ hψ hreg) m,
      ∀ x, e x = x := by
  obtain ⟨hi, -⟩ := isSmoothEmbedding_of_chart hm hf φ hφ hreg
  obtain ⟨hj, -⟩ := isSmoothEmbedding_of_chart hm hf ψ hψ hreg
  refine ⟨Homeomorph.diffeomorphOfImmersions
    (cM := chartedSpaceOfChart hm hf φ hφ hreg)
    (cN := chartedSpaceOfChart hm hf ψ hψ hreg)
    (Homeomorph.refl _) hi hj rfl, ?_⟩
  intro x
  exact Homeomorph.diffeomorphOfImmersions_apply
    (cM := chartedSpaceOfChart hm hf φ hφ hreg)
    (cN := chartedSpaceOfChart hm hf ψ hψ hreg) _ hi hj rfl x

end RegularFiber

/-- For a vector-space target, the preferred regular-fibre atlas and the regular-level atlas
are `C^m` diffeomorphic by the identity. The atlases are passed explicitly to retain both smooth
structures on the same subtype without installing a competing global instance. -/
theorem exists_regularFiberLevelDiffeomorph (hm : 1 ≤ m)
    {f : M → F} {c : F} (hf : ContMDiff I 𝓘(ℝ, F) m f)
    (hreg : IsRegularValue I 𝓘(ℝ, F) f c) :
    ∃ e : @Diffeomorph ℝ _ _ _ _ _ _ _ _ _ _ _
      𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ F) → ℝ)
      𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ F) → ℝ)
      {x : M // f x = c} _
        (regularFiberChartedSpace hm hf BoundarylessManifold.isInteriorPoint hreg)
      {x : M // f x = c} _
        (regularLevelChartedSpace (fun x _ ↦ (hf x).of_le hm) hreg rfl) m,
      ∀ x, e x = x := by
  obtain ⟨hi, -⟩ :=
    isSmoothEmbedding_coe_regularFiber hm hf BoundarylessManifold.isInteriorPoint hreg
  obtain ⟨hj, -⟩ := isSmoothEmbedding_coe_regularLevel hm (fun x _ ↦ hf x) hreg rfl
  refine ⟨Homeomorph.diffeomorphOfImmersions
    (cM := regularFiberChartedSpace hm hf BoundarylessManifold.isInteriorPoint hreg)
    (cN := regularLevelChartedSpace (fun x _ ↦ (hf x).of_le hm) hreg rfl)
    (Homeomorph.refl _) hi hj rfl, ?_⟩
  intro x
  exact Homeomorph.diffeomorphOfImmersions_apply
    (cM := regularFiberChartedSpace hm hf BoundarylessManifold.isInteriorPoint hreg)
    (cN := regularLevelChartedSpace (fun x _ ↦ (hf x).of_le hm) hreg rfl) _ hi hj rfl x

end TauCeti
