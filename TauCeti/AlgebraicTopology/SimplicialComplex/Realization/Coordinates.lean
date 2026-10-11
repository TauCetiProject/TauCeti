/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Basic

/-!
# Coordinates of polyhedra with unused vertices

The standard polyhedron of a precomplex consists of nonnegative barycentric coordinates
summing to one whose support is a face. Unlike an abstract complex on a fixed vertex type,
a precomplex can leave vertices unused. This characterization therefore applies to geometric
moves which add or remove vertices, including stellar subdivision and elementary collapse.

The construction reuses Mathlib's `Geometry.SimplicialComplex.onFinsupp` and the standard
simplex coordinate API in `Realization.Basic`.
-/

public section

open Set

attribute [local instance] Classical.decEq

namespace Finsupp

variable {ι : Type*}

/-- The finite-coordinate linear equivalence carries the standard coordinate simplex to the
finitely supported coordinate simplex. -/
theorem mem_convexHull_single_equivFunOnFinite [Finite ι]
    {τ : Finset ι} {x : ι → ℝ}
    (hx : x ∈ convexHull ℝ ((Pi.single · (1 : ℝ)) '' (τ : Set ι))) :
    equivFunOnFinite.symm x ∈
      convexHull ℝ ((Finsupp.single · (1 : ℝ)) '' (τ : Set ι)) := by
  classical
  have him := (linearEquivFunOnFinite ℝ ℝ ι).symm.toLinearMap.image_convexHull
      ((Pi.single · (1 : ℝ)) '' (τ : Set ι))
  have hxf' : (linearEquivFunOnFinite ℝ ℝ ι).symm x ∈
      (linearEquivFunOnFinite ℝ ℝ ι).symm '' convexHull ℝ
      ((Pi.single · (1 : ℝ)) '' (τ : Set ι)) := ⟨x, hx, rfl⟩
  have hxf₀ := him ▸ hxf'
  have himage : (linearEquivFunOnFinite ℝ ℝ ι).symm ''
      ((Pi.single · (1 : ℝ)) '' (τ : Set ι)) =
      (Finsupp.single · (1 : ℝ)) '' (τ : Set ι) := by
    ext z
    constructor
    · rintro ⟨y, ⟨i, hi, rfl⟩, rfl⟩
      have hi_single : (linearEquivFunOnFinite ℝ ℝ ι).symm (Pi.single i 1) =
          Finsupp.single i 1 :=
        linearEquivFunOnFinite_symm_single ℝ ℝ ι i 1
      exact ⟨i, hi, hi_single.symm⟩
    · rintro ⟨i, hi, rfl⟩
      have hi_single : (linearEquivFunOnFinite ℝ ℝ ι).symm (Pi.single i 1) =
          Finsupp.single i 1 :=
        linearEquivFunOnFinite_symm_single ℝ ℝ ι i 1
      exact ⟨Pi.single (i : ι) 1, ⟨i, hi, rfl⟩, hi_single⟩
  have hxf₁ : (linearEquivFunOnFinite ℝ ℝ ι).symm x ∈ convexHull ℝ
      ((Finsupp.single · (1 : ℝ)) '' (τ : Set ι)) := by
    convert hxf₀ using 1
    exact congrArg (convexHull ℝ) himage.symm
  exact hxf₁

end Finsupp

namespace Geometry.SimplicialComplex

variable {ι : Type*} [DecidableEq ι]

/-- A point of the standard polyhedron has nonnegative coordinates summing to one and
support a face, including for precomplexes with unused vertices. -/
@[simp]
theorem mem_space_onFinsupp_iff {K : PreAbstractSimplicialComplex ι} {x : ι →₀ ℝ} :
    x ∈ (onFinsupp (𝕜 := ℝ) K).space ↔
      (∀ i, 0 ≤ x i) ∧ x.sum (fun _ r => r) = 1 ∧ x.support ∈ K := by
  classical
  have hfaces : ∀ τ, τ ∈ (onFinsupp (𝕜 := ℝ) K).faces ↔
      ∃ σ ∈ K, σ.image (fun i => Finsupp.single i (1 : ℝ)) = τ := by
    intro τ
    simp only [onFinsupp, ofAffineIndependent, PreAbstractSimplicialComplex.map, mem_image]
    aesop
  rw [mem_space_iff]
  constructor
  · rintro ⟨τ, hτ, hx⟩
    obtain ⟨σ, hσ, rfl⟩ := (hfaces τ).mp hτ
    rw [Finset.coe_image, AbstractSimplicialComplex.mem_standardSimplex_iff] at hx
    refine ⟨hx.1, hx.2.1, K.isRelLowerSet_faces.mem_of_le hσ hx.2.2 ?_⟩
    apply Finsupp.support_nonempty_iff.mpr
    intro hzero
    simp [hzero] at hx
  · rintro ⟨hnonneg, hsum, hsupp⟩
    refine ⟨x.support.image (fun i => Finsupp.single i (1 : ℝ)),
      (hfaces _).mpr ⟨x.support, hsupp, rfl⟩, ?_⟩
    rw [Finset.coe_image, AbstractSimplicialComplex.mem_standardSimplex_iff]
    exact ⟨hnonneg, hsum, Finset.Subset.rfl⟩

end Geometry.SimplicialComplex
