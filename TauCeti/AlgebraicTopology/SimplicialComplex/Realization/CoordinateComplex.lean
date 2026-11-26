/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Finite
public import TauCeti.Analysis.Convex.SimplicialComplex.Map

/-!
# The coordinate complex of a finite abstract complex

For a finite vertex type, the standard geometric complex can be read in the normed space of
all real coordinate vectors rather than finitely supported vectors. Its space is precisely the
coordinate image of the weak realization. This permits applying geometric subdivision and PL
inverse theorems directly to barycentric coordinate formulas.

The construction is the image of `AbstractSimplicialComplex.standardGeometricComplex` under
`Finsupp.linearEquivFunOnFinite`.
-/

public noncomputable section

open Set

namespace AbstractSimplicialComplex

variable {ι : Type*} [Finite ι] (K : AbstractSimplicialComplex ι)

/-- The geometric complex of barycentric coordinate vectors of a complex on a finite vertex
type, in the real vector space `ι → ℝ`. -/
def coordinateComplex : Geometry.SimplicialComplex ℝ (ι → ℝ) :=
  (standardGeometricComplex K).map (Finsupp.linearEquivFunOnFinite ℝ ℝ ι)
    (Finsupp.linearEquivFunOnFinite ℝ ℝ ι).injective.injOn
    (fun _ _ => ⟨(Finsupp.linearEquivFunOnFinite ℝ ℝ ι).toLinearMap.toAffineMap,
      fun _ _ => rfl⟩)

/-- The coordinate faces are exactly the coordinate images of the abstract faces. -/
@[simp]
theorem mem_coordinateComplex_faces_iff [DecidableEq ι] [DecidableEq (ι → ℝ)]
    (τ : Finset (ι → ℝ)) :
    τ ∈ K.coordinateComplex.faces ↔
      ∃ σ ∈ K.faces, σ.image (fun v => Pi.single v (1 : ℝ)) = τ := by
  classical
  rw [coordinateComplex, Geometry.SimplicialComplex.faces_map]
  constructor
  · rintro ⟨_, hτ, rfl⟩
    obtain ⟨σ, hσ, rfl⟩ := (mem_standardGeometricComplex_faces_iff K _).mp hτ
    exact ⟨σ, hσ, by simp [Finset.image_image, Function.comp_def]⟩
  · rintro ⟨σ, hσ, rfl⟩
    refine ⟨σ.image (fun v => Finsupp.single v (1 : ℝ)),
      (mem_standardGeometricComplex_faces_iff K _).mpr ⟨σ, hσ, by ext; simp⟩, ?_⟩
    simp [Finset.image_image, Function.comp_def]

/-- The coordinate complex occupies exactly the barycentric coordinate image of the weak
realization. -/
@[simp]
theorem space_coordinateComplex : K.coordinateComplex.space =
    range fun x : Realization K => (x.val : ι → ℝ) := by
  rw [coordinateComplex, Geometry.SimplicialComplex.space_map]
  exact Set.image_eq_range _ _

/-- The coordinate complex has finitely many faces. -/
theorem finite_faces_coordinateComplex : K.coordinateComplex.faces.Finite := by
  classical
  let := Fintype.ofFinite ι
  rw [coordinateComplex, Geometry.SimplicialComplex.finite_faces_map_iff]
  refine ((Set.toFinite K.faces).image (fun σ : Finset ι =>
    σ.image fun v => Finsupp.single v (1 : ℝ))).subset ?_
  intro τ hτ
  exact (mem_standardGeometricComplex_faces_iff K τ).mp hτ

end AbstractSimplicialComplex
