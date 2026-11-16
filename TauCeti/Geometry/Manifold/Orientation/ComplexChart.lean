/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.Complex.Orientation
public import TauCeti.Geometry.Manifold.Orientation.Preserving

import Mathlib.LinearAlgebra.Complex.Determinant
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Manifold.Orientation.Pullback

/-!
# Positive complex charts on an oriented surface

Every point `x₀` of an oriented smooth surface `M` without boundary lies in the source of a
complex chart `φ : PartialDiffeomorph I 𝓘(ℝ, ℂ) M ℂ ∞` which preserves orientation, for the
standard orientation `Complex.orientation` of the plane, at every point of its source, and whose
source lies in any prescribed open neighborhood of `x₀`
(`TauCeti.Manifold.exists_partialDiffeomorph_isOrientationPreservingAt`).

The extended chart at `x₀`, followed by a linear identification of the model space with `ℂ`, is
either orientation preserving or orientation reversing at `x₀`; in the second case it is followed
by complex conjugation. Orientation preservation then holds near `x₀`, and the chart is restricted
to such a neighborhood inside the prescribed one.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 15.
-/

public section

open Set Filter
open scoped Manifold ContDiff Topology

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
private theorem mem_trans_toPartialDiffeomorph_source {F G : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (Φ : PartialDiffeomorph I 𝓘(ℝ, F) M F ∞) (A : F ≃L[ℝ] G) {x : M} (hx : x ∈ Φ.source) :
    x ∈ (Φ.trans (A.toPartialDiffeomorph (n := ∞))).source := by
  change x ∈ Φ.source ∩ Φ ⁻¹' (A.toPartialDiffeomorph (n := ∞)).toPartialEquiv.source
  rw [ContinuousLinearEquiv.toPartialDiffeomorph_toPartialEquiv]
  exact ⟨hx, trivial⟩

/-- A complex chart at a point of an oriented surface without boundary that preserves
orientation at that point. -/
private theorem exists_partialDiffeomorph_isOrientationPreservingAt_self [I.Boundaryless]
    (o : Manifold.Orientation I M (Fin 2)) (x₀ : M) :
    ∃ χ : PartialDiffeomorph I 𝓘(ℝ, ℂ) M ℂ ∞, x₀ ∈ χ.source ∧
      Manifold.Orientation.IsOrientationPreservingAt o
        (Manifold.Orientation.model (I := 𝓘(ℝ, ℂ)) Complex.orientation (by simp)) χ x₀ := by
  have hdim : Module.finrank ℝ E = Module.finrank ℝ ℂ := by
    rw [← o.card_eq, Complex.finrank_real_complex, Fintype.card_fin]
  let χ₀ := extChartPartialDiffeomorph I ∞ x₀
  have hx₀χ₀ : x₀ ∈ χ₀.source :=
    (mem_extChartPartialDiffeomorph_source I ∞ x₀).mpr BoundarylessManifold.isInteriorPoint
  let χ₁ := χ₀.trans (ContinuousLinearEquiv.ofFinrankEq hdim).toPartialDiffeomorph
  have hx₀χ₁ : x₀ ∈ χ₁.source := mem_trans_toPartialDiffeomorph_source χ₀ _ hx₀χ₀
  rcases (χ₁.isLocalDiffeomorphAt I 𝓘(ℝ, ℂ) ∞ hx₀χ₁)
    |>.isOrientationPreservingAt_or_isOrientationReversingAt (by simp) o
      (Manifold.Orientation.model (I := 𝓘(ℝ, ℂ)) Complex.orientation (by simp)) with hp | hr
  · exact ⟨χ₁, hx₀χ₁, hp⟩
  · have hC : LinearMap.det (Complex.conjCLE : ℂ →ₗ[ℝ] ℂ) < 0 := by
      change LinearMap.det Complex.conjAe.toLinearEquiv.toLinearMap < 0
      rw [Complex.det_conjAe]
      norm_num
    refine ⟨χ₁.trans Complex.conjCLE.toPartialDiffeomorph,
      mem_trans_toPartialDiffeomorph_source χ₁ _ hx₀χ₁, ?_⟩
    rw [PartialDiffeomorph.coe_trans, ContinuousLinearEquiv.toPartialDiffeomorph_toPartialEquiv]
    exact (Manifold.Orientation.isOrientationReversingAt_of_det_neg _ _ hC (χ₁ x₀)).comp hr

/-- **Positive complex charts.** Every point `x₀` of an oriented surface without boundary lies in
the source of a complex chart, with source inside a prescribed open neighborhood `V` of `x₀`, that
preserves orientation at every point of its source. -/
theorem exists_partialDiffeomorph_isOrientationPreservingAt [I.Boundaryless]
    (o : Manifold.Orientation I M (Fin 2)) {x₀ : M} {V : Set M} (hV : IsOpen V)
    (hx₀ : x₀ ∈ V) :
    ∃ φ : PartialDiffeomorph I 𝓘(ℝ, ℂ) M ℂ ∞, x₀ ∈ φ.source ∧ φ.source ⊆ V ∧
      ∀ x ∈ φ.source, Manifold.Orientation.IsOrientationPreservingAt o
        (Manifold.Orientation.model (I := 𝓘(ℝ, ℂ)) Complex.orientation (by simp)) φ x := by
  obtain ⟨χ, hx₀χ, hχp⟩ := exists_partialDiffeomorph_isOrientationPreservingAt_self o x₀
  have hev := Manifold.Orientation.eventually_isOrientationPreservingAt
    ((χ.contMDiffOn.contMDiffAt (χ.open_source.mem_nhds hx₀χ)).of_le (by simp)) hχp
  obtain ⟨O, hON, hO, hx₀O⟩ := mem_nhds_iff.mp hev
  refine ⟨χ.restrOpen (O ∩ V) (hO.inter hV), ?_, ?_, ?_⟩ <;>
    rw [PartialDiffeomorph.restrOpen_source]
  · exact ⟨hx₀χ, hx₀O, hx₀⟩
  · exact fun x hx ↦ hx.2.2
  · intro x hx
    rw [PartialDiffeomorph.coe_restrOpen]
    exact hON hx.2.1

end TauCeti.Manifold
