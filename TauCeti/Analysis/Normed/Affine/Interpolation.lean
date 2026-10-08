/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Affine interpolation on independent points

Arbitrary values on an affinely independent set in a finite-dimensional real normed space
extend to a continuous affine map. In particular, an inverse prescribed on the vertices of
an affine simplex extends to an affine inverse on its convex hull. This allows inverse
simplicial maps to be checked one simplex at a time.

The construction extends the independent set to an affine basis and uses Mathlib's
continuous barycentric coordinates. See Rourke--Sanderson, *Introduction to Piecewise-Linear
Topology*, Chapter 1, for affine maps of simplices.
-/

public section

open Set

namespace AffineIndependent

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] {s : Set E}

/-- Values on an affinely independent set extend to a continuous affine map of the ambient
space. The set need not span the ambient space, and may be empty. -/
theorem exists_continuousAffineMap_eqOn (hs : AffineIndependent ℝ ((↑) : s → E))
    (f : E → F) : ∃ A : E →ᴬ[ℝ] F, EqOn A f s := by
  classical
  obtain ⟨t, hst, ht, hspan⟩ := exists_subset_affineIndependent_affineSpan_eq_top hs
  let b : AffineBasis t ℝ E := ⟨Subtype.val, ht, by simpa using hspan⟩
  have : Finite t := b.finite
  let : Fintype t := Fintype.ofFinite t
  let c (i : t) : E →ᴬ[ℝ] ℝ := ⟨b.coord i, continuous_barycentric_coord b i⟩
  let A : E →ᴬ[ℝ] F := ∑ i : t,
    ((ContinuousLinearMap.id ℝ ℝ).smulRight (f i)).toContinuousAffineMap.comp (c i)
  refine ⟨A, fun x hx => ?_⟩
  have hcoord (i : t) : b.coord i x = if i = ⟨x, hst hx⟩ then 1 else 0 :=
    b.coord_apply i ⟨x, hst hx⟩
  let ev : (E →ᴬ[ℝ] F) →+ F :=
    ⟨⟨fun A => A x, rfl⟩, fun _ _ => rfl⟩
  have hev := map_sum ev
    (fun i : t =>
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (f i)).toContinuousAffineMap.comp (c i))
    Finset.univ
  calc
    A x = ∑ i : t,
        (((ContinuousLinearMap.id ℝ ℝ).smulRight (f i)).toContinuousAffineMap.comp (c i)) x :=
      hev
    _ = f x := by
      simp [c, ContinuousAffineMap.comp_apply,
        ContinuousLinearMap.coe_toContinuousAffineMap, hcoord]

end AffineIndependent

namespace ContinuousAffineMap

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {s : Set E} {g : F → E}

/-- If the images of a set under an affine map are affinely independent, prescribed inverse
values on those images extend to an affine left inverse on the entire convex hull. -/
theorem exists_leftInverseOn_convexHull (A : E →ᴬ[ℝ] F)
    (hA : AffineIndependent ℝ ((↑) : (A '' s) → F))
    (hg : ∀ x ∈ s, g (A x) = x) :
    ∃ B : F →ᴬ[ℝ] E, ∀ x ∈ convexHull ℝ s, B (A x) = x := by
  obtain ⟨B, hB⟩ := hA.exists_continuousAffineMap_eqOn g
  have heq : EqOn (B.comp A).toAffineMap (AffineMap.id ℝ E) s := by
    intro x hx
    exact (hB ⟨x, hx, rfl⟩).trans (hg x hx)
  exact ⟨B, fun x hx => AffineMap.eqOn_affineSpan heq
    (convexHull_subset_affineSpan s hx)⟩

end ContinuousAffineMap
