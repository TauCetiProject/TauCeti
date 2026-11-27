/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.Stiefel.Homogeneous
public import TauCeti.Geometry.Manifold.Instances.Stiefel.LinearIsometry
public import TauCeti.Geometry.Manifold.Instances.Stiefel.OrientedSpan
public import TauCeti.Topology.Grassmannian.Oriented
import TauCeti.Topology.Homeomorph.Quotient

/-!
# The oriented Grassmannian as a Stiefel quotient

The oriented Grassmannian of positive rank is the space of orthonormal frames modulo rotations.
The orbits are exactly the fibres of the map taking a frame to its oriented span. Isometric
coordinates identify the quotient with `TauCeti.finiteOrientedGrassmannian`, in which forgetting
orientation is a two-sheeted covering.

## References

* A. Hatcher, *Vector Bundles and K-Theory*, §1.2, for the Stiefel description of the
  oriented Grassmannian.
-/

public section

noncomputable section

open Matrix Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {N : ℕ}

/-- The oriented Grassmannian of positive rank as the space of orthonormal frames modulo
positive orthogonal changes of basis. -/
abbrev orientedGrassmannian (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (r : ℕ+) :=
  MulAction.orbitRel.Quotient (specialOrthogonalGroup (Fin r) ℝ) (stiefel E r)

namespace orientedGrassmannian

variable {r : ℕ+}

/-- Send a frame to the oriented plane it spans. -/
def ofFrame (v : stiefel E r) : orientedGrassmannian E r :=
  Quotient.mk _ v

/-- The frame projection is the orbit quotient projection. -/
theorem ofFrame_eq_quotientMk :
    (ofFrame : stiefel E r → orientedGrassmannian E r) =
      Quotient.mk (MulAction.orbitRel (specialOrthogonalGroup (Fin r) ℝ) (stiefel E r)) :=
  (rfl)

/-- Two frames determine the same oriented plane exactly when a rotation carries one to the
other. -/
theorem ofFrame_eq_iff {v w : stiefel E r} :
    ofFrame v = ofFrame w ↔ w ∈ MulAction.orbit (specialOrthogonalGroup (Fin r) ℝ) v :=
  Quotient.eq''.trans (MulAction.orbitRel_apply.trans MulAction.mem_orbit_symm)

/-- A rotation of a frame gives the same oriented plane. -/
@[simp]
theorem ofFrame_smul (A : specialOrthogonalGroup (Fin r) ℝ) (v : stiefel E r) :
    ofFrame (A • v) = ofFrame v :=
  (ofFrame_eq_iff.2 ⟨A, rfl⟩).symm

/-- The projection from frames is an open quotient map for the rotation action. -/
theorem isOpenQuotientMap_ofFrame :
    IsOpenQuotientMap (ofFrame : stiefel E r → orientedGrassmannian E r) :=
  MulAction.isOpenQuotientMap_quotientMk

theorem surjective_ofFrame :
    Function.Surjective (ofFrame : stiefel E r → orientedGrassmannian E r) :=
  isOpenQuotientMap_ofFrame.surjective

@[fun_prop]
theorem continuous_ofFrame : Continuous (ofFrame : stiefel E r → orientedGrassmannian E r) :=
  isOpenQuotientMap_ofFrame.continuous

/-- The Stiefel quotient identifies intrinsically with the rank-`r` subspaces equipped with
an orientation. -/
def orientedSubspaceEquiv : orientedGrassmannian E r ≃ OrientedSubspace E r := by
  let f : orientedGrassmannian E r → OrientedSubspace E r :=
    Quotient.lift stiefel.orientedSpan fun v w h ↦
      stiefel.orientedSpan_eq_iff.2 (MulAction.mem_orbit_symm.1 (MulAction.orbitRel_apply.1 h))
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro p q
    induction p using Quotient.inductionOn with
    | _ v =>
      induction q using Quotient.inductionOn with
      | _ w => exact fun h ↦ ofFrame_eq_iff.2 (stiefel.orientedSpan_eq_iff.1 h)
  · intro p
    have : NeZero (r : ℕ) := ⟨r.ne_zero⟩
    obtain ⟨v, hv⟩ := stiefel.surjective_orientedSpan p
    exact ⟨ofFrame v, hv⟩

/-- The oriented subspace represented by a frame is its span with the frame's orientation. -/
@[simp]
theorem orientedSubspaceEquiv_ofFrame (v : stiefel E r) :
    orientedSubspaceEquiv (ofFrame v) = stiefel.orientedSpan v :=
  (rfl)

/-- An oriented span corresponds to the quotient class of its frame. -/
@[simp]
theorem orientedSubspaceEquiv_symm_orientedSpan (v : stiefel E r) :
    orientedSubspaceEquiv.symm (stiefel.orientedSpan v) = ofFrame v :=
  orientedSubspaceEquiv.symm_apply_eq.2 (orientedSubspaceEquiv_ofFrame v).symm

private def coordinateFrameHomeomorph (e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N)) :
    stiefel E r ≃ₜ finiteOrthonormalFrame ℝ r N :=
  (e.stiefelHomeomorph r).trans (stiefel.finiteOrthonormalFrameHomeomorph r N)

private theorem coordinateFrameHomeomorph_smul (e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N))
    (A : specialOrthogonalGroup (Fin r) ℝ) (v : stiefel E r) :
    coordinateFrameHomeomorph e (A • v) = A • coordinateFrameHomeomorph e v := by
  simp [coordinateFrameHomeomorph]

private theorem coordinateFrameHomeomorph_mem_orbit (e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N))
    {v w : stiefel E r} :
    coordinateFrameHomeomorph e w ∈ MulAction.orbit (specialOrthogonalGroup (Fin r) ℝ)
      (coordinateFrameHomeomorph e v) ↔
        w ∈ MulAction.orbit (specialOrthogonalGroup (Fin r) ℝ) v := by
  constructor
  · rintro ⟨A, hA⟩
    exact ⟨A, (coordinateFrameHomeomorph e).injective
      ((coordinateFrameHomeomorph_smul e A v).trans hA)⟩
  · rintro ⟨A, rfl⟩
    exact ⟨A, (coordinateFrameHomeomorph_smul e A v).symm⟩

/-- An isometric choice of coordinates identifies the Stiefel quotient with the orientation
double cover of the finite coordinate Grassmannian. -/
def finiteOrientedGrassmannianHomeomorph (e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N)) :
    orientedGrassmannian E r ≃ₜ finiteOrientedGrassmannian r N :=
  (Homeomorph.Quotient.congr (coordinateFrameHomeomorph e) fun _ _ ↦
    MulAction.orbitRel_apply.trans <| (coordinateFrameHomeomorph_mem_orbit e).symm.trans
      MulAction.orbitRel_apply.symm).trans
    (finiteOrientedGrassmannian.specialOrthogonalOrbitHomeomorph r N)

/-- In isometric coordinates the image of a frame is its oriented coordinate span. -/
@[simp]
theorem finiteOrientedGrassmannianHomeomorph_ofFrame (e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N))
    (v : stiefel E r) :
    finiteOrientedGrassmannianHomeomorph e (ofFrame v) =
      finiteOrientedGrassmannian.orientedFrameSpan
        (stiefel.finiteOrthonormalFrameHomeomorph r N
          (e.stiefelHomeomorph r v)).toFullRankFrame := by
  simp [finiteOrientedGrassmannianHomeomorph, ofFrame, coordinateFrameHomeomorph]

/-- In any choice of isometric coordinates, forgetting orientation is a covering map. -/
theorem isCoveringMap_forget_comp_finiteOrientedGrassmannianHomeomorph
    (e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N)) :
    IsCoveringMap ((finiteOrientedGrassmannian.forget :
      finiteOrientedGrassmannian r N → finiteGrassmannian ℝ r N) ∘
        finiteOrientedGrassmannianHomeomorph e) :=
  (VectorBundleOrientationCover.isCoveringMap_proj (by simp)).comp_homeomorph
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
  exact VectorBundleOrientationCover.encard_preimage_proj_singleton (by simp) P

end orientedGrassmannian

end TauCeti
