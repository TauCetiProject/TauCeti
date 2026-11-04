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
`TauCeti.RegularFiber.exists_diffeomorph_apply_eq_self` identifies the atlases from any two such
charts by the identity on the actual fibre. Thus its smooth structure does not depend on target
coordinates.

For a vector-space target,
`TauCeti.exists_diffeomorph_regularFiber_regularLevel_apply_eq_self` identifies the preferred
manifold-valued regular-fibre atlas with the regular-level atlas. Both comparisons preserve the
ambient point and its subspace topology, including for empty fibres. The two charted-space
arguments are explicit in the statements to keep both atlases on the same subtype, without a
type copy or a competing global instance.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2013,
  Theorem 5.31 (uniqueness of the smooth structure on an embedded submanifold), with
  Corollary 5.14 (regular level sets) as background.
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
theorem exists_diffeomorph_apply_eq_self (hm : 1 ≤ m) (hf : ContMDiff I J m f)
    (φ ψ : PartialDiffeomorph J 𝓘(ℝ, F) N F m) (hφ : c ∈ φ.source) (hψ : c ∈ ψ.source)
    (hreg : IsRegularValue I J f c) :
    ∃ e : @Diffeomorph ℝ _ _ _ _ _ _ _ _ _ _ _
      𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ F) → ℝ)
      𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ F) → ℝ)
      {x : M // f x = c} _ (chartedSpaceOfChart hm hf φ hφ hreg)
      {x : M // f x = c} _ (chartedSpaceOfChart hm hf ψ hψ hreg) m,
      ∀ x, e x = x := by
  obtain ⟨hi, -⟩ := isSmoothEmbedding_coe_of_chart hm hf φ hφ hreg
  obtain ⟨hj, -⟩ := isSmoothEmbedding_coe_of_chart hm hf ψ hψ hreg
  exact ChartedSpace.exists_diffeomorph_apply_eq_self
    (chartedSpaceOfChart hm hf φ hφ hreg) (chartedSpaceOfChart hm hf ψ hψ hreg) hi hj

end RegularFiber

/-- For a vector-space target, the preferred regular-fibre atlas and the regular-level atlas
are `C^m` diffeomorphic by the identity. The atlases are passed explicitly to retain both smooth
structures on the same subtype without installing a competing global instance. -/
theorem exists_diffeomorph_regularFiber_regularLevel_apply_eq_self (hm : 1 ≤ m)
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
  exact ChartedSpace.exists_diffeomorph_apply_eq_self
    (regularFiberChartedSpace hm hf BoundarylessManifold.isInteriorPoint hreg)
    (regularLevelChartedSpace (fun x _ ↦ (hf x).of_le hm) hreg rfl) hi hj

end TauCeti
