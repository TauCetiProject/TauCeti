/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.Stiefel.Homogeneous
public import TauCeti.Geometry.Manifold.Instances.Stiefel.LinearIsometry
public import TauCeti.Geometry.Manifold.Instances.Stiefel.OrientedGrassmannian.Basic
public import TauCeti.Topology.Grassmannian.Oriented
import TauCeti.Algebra.GroupAction.OrbitRelQuotient
import TauCeti.Topology.Homeomorph.Quotient

/-!
# Isometric coordinates for the oriented Grassmannian

An isometric choice of coordinates identifies the intrinsic Stiefel quotient with the finite
oriented Grassmannian and transports its orientation-forgetting double cover.
-/

public section

noncomputable section

open Matrix

namespace TauCeti.orientedGrassmannian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {r : ℕ+} {N : ℕ}

private def coordinateFrameHomeomorph (e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N)) :
    stiefel E r ≃ₜ finiteOrthonormalFrame ℝ r N :=
  (e.stiefelHomeomorph r).trans (stiefel.finiteOrthonormalFrameHomeomorph r N)

private theorem coordinateFrameHomeomorph_smul (e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N))
    (A : specialOrthogonalGroup (Fin r) ℝ) (v : stiefel E r) :
    coordinateFrameHomeomorph e (A • v) = A • coordinateFrameHomeomorph e v := by
  simp [coordinateFrameHomeomorph]

/-- An isometric choice of coordinates identifies the Stiefel quotient with the orientation
double cover of the finite coordinate Grassmannian. -/
def finiteOrientedGrassmannianHomeomorph (e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N)) :
    orientedGrassmannian E r ≃ₜ finiteOrientedGrassmannian r N :=
  let h := coordinateFrameHomeomorph (r := r) e
  let f : stiefel E r →[specialOrthogonalGroup (Fin r) ℝ] finiteOrthonormalFrame ℝ r N :=
    ⟨h, coordinateFrameHomeomorph_smul e⟩
  (Homeomorph.Quotient.congr h fun v w ↦ by
    -- The equivariant map has the same underlying function as the frame homeomorphism.
    change _ ↔ MulAction.orbitRel (specialOrthogonalGroup (Fin r) ℝ) _ (f v) (f w)
    rw [← Quotient.eq, ← Quotient.eq, ← MulActionHom.orbitRelQuotientMap_mk f v,
      ← MulActionHom.orbitRelQuotientMap_mk f w,
      (f.orbitRelQuotientMap_injective h.injective Function.surjective_id).eq_iff]).trans
    (finiteOrientedGrassmannian.specialOrthogonalOrbitHomeomorph r N)

/-- In isometric coordinates the image of a frame is its oriented coordinate span. -/
@[simp]
theorem finiteOrientedGrassmannianHomeomorph_ofFrame (e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N))
    (v : stiefel E r) :
    finiteOrientedGrassmannianHomeomorph e (ofFrame v) =
      finiteOrientedGrassmannian.orientedFrameSpan
        (stiefel.finiteOrthonormalFrameHomeomorph r N
          (e.stiefelHomeomorph r v)).toFullRankFrame := by
  rw [congrFun ofFrame_eq_quotientMk v]
  simp [finiteOrientedGrassmannianHomeomorph, coordinateFrameHomeomorph]

/-- In any choice of isometric coordinates, forgetting orientation is a covering map. -/
theorem isCoveringMap_forget_comp_finiteOrientedGrassmannianHomeomorph
    (e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N)) :
    IsCoveringMap ((finiteOrientedGrassmannian.forget :
      finiteOrientedGrassmannian r N → finiteGrassmannian ℝ r N) ∘
        finiteOrientedGrassmannianHomeomorph e) :=
  finiteOrientedGrassmannian.isCoveringMap_forget.comp_homeomorph
    (finiteOrientedGrassmannianHomeomorph e)

/-- The orientation-forgetting covering has exactly two points over every plane. -/
theorem encard_preimage_forget_comp_finiteOrientedGrassmannianHomeomorph_singleton
    (e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N)) (P : finiteGrassmannian ℝ r N) :
    (((finiteOrientedGrassmannian.forget :
      finiteOrientedGrassmannian r N → finiteGrassmannian ℝ r N) ∘
        finiteOrientedGrassmannianHomeomorph e) ⁻¹' {P}).encard = 2 := by
  let h := finiteOrientedGrassmannianHomeomorph (r := r) e
  rw [Set.preimage_comp, Set.encard_preimage_of_injective_subset_range h.injective
    (by rw [h.surjective.range_eq]; exact Set.subset_univ _)]
  exact finiteOrientedGrassmannian.encard_preimage_forget_singleton P

end TauCeti.orientedGrassmannian
