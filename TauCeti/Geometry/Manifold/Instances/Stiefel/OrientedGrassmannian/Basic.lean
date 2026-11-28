/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.Stiefel.OrientedSpan
import Mathlib.Order.Setoid.Basic

/-!
# The oriented Grassmannian as a Stiefel quotient

The oriented Grassmannian of positive rank is the space of orthonormal frames modulo rotations.
The orbits are exactly the fibres of the map taking a frame to its oriented span.

## References

* A. Hatcher, *Vector Bundles and K-Theory*, §1.2, for the Stiefel description of the
  oriented Grassmannian.
-/

public section

noncomputable section

open Matrix Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

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
def orientedSubspaceEquiv : orientedGrassmannian E r ≃ OrientedSubspace ℝ E r :=
  have : NeZero (r : ℕ) := ⟨r.ne_zero⟩
  (Quotient.congrRight fun _ _ ↦
    MulAction.orbitRel_apply.trans <| MulAction.mem_orbit_symm.trans
      stiefel.orientedSpan_eq_iff.symm).trans
    (Setoid.quotientKerEquivOfSurjective stiefel.orientedSpan stiefel.surjective_orientedSpan)

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

end orientedGrassmannian

end TauCeti
