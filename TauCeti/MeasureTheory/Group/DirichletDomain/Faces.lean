/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Group.DirichletDomain.Basic
import Mathlib.Topology.LocallyFinite

/-!
# Faces and identifications of a Dirichlet domain

The equality face indexed by `g` consists of points in the Dirichlet domain of `p` at equal
distance from `p` and `g • p`. For an isometric group action this is exactly the intersection
with the `g`-translate of the domain. The transformation `g⁻¹` carries this face onto the face
indexed by `g⁻¹`, describing all orbit identifications between points of the domain.

For a properly discontinuous action on a proper space the equality faces form a locally finite
family. Every boundary point belongs to a face indexed by an element not fixing the centre.
These results supply the identifications used to pair sides of a hyperbolic Dirichlet polygon.
An equality face may be empty or have lower dimension than a side; no assertion of polygonal
structure or global finite-sidedness is made here. Elements fixing the centre have the whole
domain as their equality face, and are excluded from the boundary-covering statement.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, Graduate Texts in Mathematics 91,
  Springer, 1983, §9.4.
* Svetlana Katok, *Fuchsian Groups*, Chicago Lectures in Mathematics, University of Chicago
  Press, 1992, §3.2.
-/

public section

open Set Metric
open scoped Pointwise Topology

namespace TauCeti

variable {G X : Type*} [PseudoMetricSpace X]

section SMul

variable [SMul G X]

/-- The equality face of the Dirichlet domain of `p` indexed by `g`. It can be empty or of
lower dimension than a side. If `g` fixes `p`, it is the whole Dirichlet domain. -/
def dirichletFace (p : X) (g : G) : Set X :=
  dirichletDomain G p ∩ {x | dist x p = dist x (g • p)}

/-- The defining equality-face intersection, available without unfolding the definition. -/
theorem dirichletFace_def (p : X) (g : G) :
    dirichletFace p g = dirichletDomain G p ∩ {x | dist x p = dist x (g • p)} :=
  (rfl)

/-- Membership in an equality face. -/
@[simp]
theorem mem_dirichletFace {p x : X} {g : G} :
    x ∈ dirichletFace p g ↔ x ∈ dirichletDomain G p ∧ dist x p = dist x (g • p) :=
  Iff.rfl

/-- An equality face is contained in the Dirichlet domain. -/
theorem dirichletFace_subset (p : X) (g : G) :
    dirichletFace p g ⊆ dirichletDomain G p :=
  fun _ hx ↦ (mem_dirichletFace.mp hx).1

/-- Equality faces are closed. -/
theorem isClosed_dirichletFace (p : X) (g : G) : IsClosed (dirichletFace p g) :=
  (isClosed_dirichletDomain G p).inter
    (isClosed_eq (continuous_id.dist continuous_const) (continuous_id.dist continuous_const))

/-- An element fixing the centre gives the whole Dirichlet domain as its equality face. -/
@[simp]
theorem dirichletFace_eq_dirichletDomain_of_smul_eq {p : X} {g : G} (hg : g • p = p) :
    dirichletFace p g = dirichletDomain G p := by
  ext x
  simp [hg]

variable [ProperSpace X] [ProperlyDiscontinuousSMul G X]

/-- Only finitely many equality faces meet a bounded set. This counts acting elements,
including the finitely many elements fixing the centre. -/
theorem finite_setOf_dirichletFace_inter_nonempty (p : X) {K : Set X}
    (hK : Bornology.IsBounded K) :
    {g : G | (dirichletFace p g ∩ K).Nonempty}.Finite := by
  refine (finite_dirichletCompetitors (G := G) p hK).subset ?_
  rintro g ⟨x, hx, hxK⟩
  exact mem_dirichletCompetitors.mpr ⟨x, hxK, (mem_dirichletFace.mp hx).2.ge⟩

/-- The equality faces of a Dirichlet domain are locally finite. -/
theorem locallyFinite_dirichletFace (p : X) : LocallyFinite (dirichletFace (G := G) p) :=
  fun x ↦ ⟨closedBall x 1, closedBall_mem_nhds x zero_lt_one,
    finite_setOf_dirichletFace_inter_nonempty p isBounded_closedBall⟩

/-- Every boundary point of the Dirichlet domain belongs to an equality face indexed by an
element moving the centre. This does not assert that every equality face is a boundary face
in an arbitrary metric space. -/
theorem frontier_dirichletDomain_subset_iUnion_dirichletFace (p : X) :
    frontier (dirichletDomain G p) ⊆ ⋃ g : {g : G // g • p ≠ p}, dirichletFace p g.1 := by
  intro x hx
  have hxD : x ∈ dirichletDomain G p :=
    (isClosed_dirichletDomain G p).closure_subset (frontier_subset_closure hx)
  have hnot : ¬ ∀ g : G, g • p ≠ p → dist x p < dist x (g • p) :=
    fun h ↦ hx.2 (mem_interior_dirichletDomain_of_forall_dist_lt h)
  push Not at hnot
  obtain ⟨g, hgp, hg⟩ := hnot
  exact mem_iUnion.mpr ⟨⟨g, hgp⟩,
    mem_dirichletFace.mpr ⟨hxD, le_antisymm (mem_dirichletDomain.mp hxD g) hg⟩⟩

end SMul

section Group

variable [Group G] [MulAction G X] [IsIsometricSMul G X]

/-- An equality face is exactly the overlap with the corresponding translate of the Dirichlet
domain. Thus every overlap, including lower-dimensional ones, has its prescribed pairing. -/
theorem dirichletFace_eq_inter_smul (p : X) (g : G) :
    dirichletFace p g = dirichletDomain G p ∩ g • dirichletDomain G p := by
  rw [smul_dirichletDomain]
  ext x
  simp only [mem_dirichletFace, mem_inter_iff]
  exact and_congr_right fun hx ↦ (mem_dirichletDomain_smul_iff hx g).symm

/-- The side-identification transformation `g⁻¹` pairs the equality face indexed by `g` with
that indexed by `g⁻¹`. In particular inversion preserves the indices of nonempty faces. -/
@[simp]
theorem inv_smul_dirichletFace (p : X) (g : G) :
    g⁻¹ • dirichletFace p g = dirichletFace p g⁻¹ := by
  simp only [dirichletFace_eq_inter_smul, smul_set_inter, smul_smul, inv_mul_cancel,
    one_smul]
  exact inter_comm _ _

/-- Two points of the Dirichlet domain related by `g⁻¹` are related along the face indexed by
`g`; conversely every point of that face has its `g⁻¹`-translate in the domain. -/
theorem inv_smul_mem_dirichletDomain_iff {p x : X} (hx : x ∈ dirichletDomain G p) (g : G) :
    g⁻¹ • x ∈ dirichletDomain G p ↔ x ∈ dirichletFace p g := by
  rw [dirichletFace_eq_inter_smul, mem_inter_iff, mem_smul_set_iff_inv_smul_mem]
  exact (and_iff_right hx).symm

end Group

end TauCeti
