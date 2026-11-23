/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import TauCeti.Geometry.Manifold.ContMDiff.Defs
public import TauCeti.Geometry.Manifold.Orientation.Preserving

import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Manifold.Orientation.Pullback

/-!
# Orientation-preserving charts

Every interior point of an oriented positive-dimensional real manifold has an
orientation-preserving `C^n` chart into any oriented real normed space of the same dimension,
for `n ≠ 0`. Its source can lie inside any prescribed open neighborhood
(see `exists_partialDiffeomorph_isOrientationPreservingAt_of_isInteriorPoint` in the namespace
`TauCeti.Manifold.Orientation`).
On a boundaryless manifold this applies at every point
(`TauCeti.Manifold.Orientation.exists_partialDiffeomorph_isOrientationPreservingAt`).

For surfaces, specialize the target to `ℂ` with the model orientation induced by
`Complex.orientation`. These real-smooth ℂ-valued coordinates transfer orientation-sensitive
planar notions, such as signed turning and the boundary orientation with the domain on the left,
to the surface. The inverse parametrization preserves orientation by
`TauCeti.Manifold.Orientation.IsOrientationPreservingAt.partialDiffeomorph_symm`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 15.
-/

public section

open Set Filter
open scoped Manifold ContDiff Topology

namespace TauCeti.Manifold.Orientation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {n : ℕ∞ω} [NeZero n] [IsManifold I n M] [IsManifold I 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [Nontrivial F] {ι : Type*} [Fintype ι]

/-- An oriented chart at an interior point, preserving the given orientations at that point. -/
private theorem exists_partialDiffeomorph_isOrientationPreservingAt_self
    (o : Manifold.Orientation I M ι) (oF : Manifold.Orientation 𝓘(ℝ, F) F ι)
    (x₀ : M) (hx₀I : I.IsInteriorPoint x₀) :
    ∃ χ : PartialDiffeomorph I 𝓘(ℝ, F) M F n, x₀ ∈ χ.source ∧
      IsOrientationPreservingAt o oF χ x₀ := by
  classical
  let χ₀ := extChartPartialDiffeomorph I n x₀
  have hx₀χ₀ : x₀ ∈ χ₀.source :=
    (mem_extChartPartialDiffeomorph_source I n x₀).mpr hx₀I
  let χ₁ := χ₀.trans
    (ContinuousLinearEquiv.ofFinrankEq (o.card_eq.symm.trans oF.card_eq)).toPartialDiffeomorph
  have hx₀χ₁ : x₀ ∈ χ₁.source := by
    simpa only [χ₁, PartialDiffeomorph.trans_toPartialDiffeomorph_source] using hx₀χ₀
  rcases (χ₁.isLocalDiffeomorphAt I 𝓘(ℝ, F) n hx₀χ₁)
    |>.isOrientationPreservingAt_or_isOrientationReversingAt (NeZero.ne n) o oF with hp | hr
  · exact ⟨χ₁, hx₀χ₁, hp⟩
  · -- Negating one basis vector supplies a continuous linear map of determinant -1.
    let b := Module.finBasis ℝ F
    let i : Fin (Module.finrank ℝ F) := ⟨0, Module.finrank_pos⟩
    let L : F ≃L[ℝ] F :=
      (b.equiv (b.unitsSMul (Function.update 1 i (-1))) (Equiv.refl _)).toContinuousLinearEquiv
    have hL : LinearMap.det (L : F →ₗ[ℝ] F) < 0 := by
      simp [L, Module.Basis.det_basis, Module.Basis.det_unitsSMul_self,
        Function.update_apply, apply_ite, Finset.prod_ite_eq']
    refine ⟨χ₁.trans L.toPartialDiffeomorph,
      by simpa only [PartialDiffeomorph.trans_toPartialDiffeomorph_source] using hx₀χ₁, ?_⟩
    rw [PartialDiffeomorph.coe_trans, ContinuousLinearEquiv.coe_toPartialDiffeomorph]
    exact (isOrientationReversingAt_of_det_neg oF L hL (χ₁ x₀)).comp hr

/-- An interior point of an oriented manifold has a `C^n` chart into any oriented
positive-dimensional real normed space of the same dimension, for `n ≠ 0`, preserving
orientations throughout its source and contained in the prescribed open neighborhood. -/
theorem exists_partialDiffeomorph_isOrientationPreservingAt_of_isInteriorPoint
    (o : Manifold.Orientation I M ι) (oF : Manifold.Orientation 𝓘(ℝ, F) F ι)
    {x₀ : M} (hx₀I : I.IsInteriorPoint x₀) {V : Set M} (hV : IsOpen V) (hx₀ : x₀ ∈ V) :
    ∃ φ : PartialDiffeomorph I 𝓘(ℝ, F) M F n, x₀ ∈ φ.source ∧ φ.source ⊆ V ∧
      ∀ x ∈ φ.source, IsOrientationPreservingAt o oF φ x := by
  obtain ⟨χ, hx₀χ, hχp⟩ :=
    exists_partialDiffeomorph_isOrientationPreservingAt_self (n := n) o oF x₀ hx₀I
  have hev := eventually_isOrientationPreservingAt
    ((χ.contMDiffOn.contMDiffAt (χ.open_source.mem_nhds hx₀χ)).of_le
      (ENat.one_le_iff_ne_zero_withTop.mpr (NeZero.ne n))) hχp
  obtain ⟨O, hON, hO, hx₀O⟩ := mem_nhds_iff.mp hev
  refine ⟨χ.restrOpen (O ∩ V) (hO.inter hV), ?_, ?_, ?_⟩ <;>
    rw [PartialDiffeomorph.restrOpen_source]
  · exact ⟨hx₀χ, hx₀O, hx₀⟩
  · exact fun x hx ↦ hx.2.2
  · intro x hx
    rw [PartialDiffeomorph.coe_restrOpen]
    exact hON hx.2.1

/-- Every point of an oriented boundaryless manifold has a `C^n` chart into an oriented
positive-dimensional real normed space of the same dimension, for `n ≠ 0`, preserving
orientations throughout its source and contained in the prescribed open neighborhood. -/
theorem exists_partialDiffeomorph_isOrientationPreservingAt [BoundarylessManifold I M]
    (o : Manifold.Orientation I M ι) (oF : Manifold.Orientation 𝓘(ℝ, F) F ι)
    {x₀ : M} {V : Set M} (hV : IsOpen V) (hx₀ : x₀ ∈ V) :
    ∃ φ : PartialDiffeomorph I 𝓘(ℝ, F) M F n, x₀ ∈ φ.source ∧ φ.source ⊆ V ∧
      ∀ x ∈ φ.source, IsOrientationPreservingAt o oF φ x :=
  o.exists_partialDiffeomorph_isOrientationPreservingAt_of_isInteriorPoint oF
    BoundarylessManifold.isInteriorPoint hV hx₀

end TauCeti.Manifold.Orientation
