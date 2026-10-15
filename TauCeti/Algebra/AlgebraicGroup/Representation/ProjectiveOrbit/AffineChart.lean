/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Basic
public import TauCeti.Algebra.AlgebraicGroup.Solvable.LieKolchin
import Mathlib.RingTheory.HopfAlgebra.GroupLike

/-!
# Affine charts containing solvable projective orbits

Every projective orbit of a reduced connected solvable affine group over an algebraically
closed field lies in a single standard affine chart of projective space. This assertion
concerns the entire scheme-point image, including its nonclosed points.

Lie--Kolchin supplies a triangular basis with group-like diagonal entries. The last nonzero
coordinate of the vector, normalized to take value one, pulls back to a group-like matrix
coefficient. That coefficient is a unit of the coordinate Hopf algebra, so the corresponding
projective chart pulls back to the whole group scheme.

This is the affine-chart step in the Borel fixed-point argument: a closed projective orbit
contained in this chart can be studied as a closed subscheme of an affine scheme. Containment
in a chart alone does not assert that an arbitrary orbit is affine or closed.
-/

public section

open AlgebraicGeometry

namespace TauCeti.Comodule

universe u

section Solvable

variable {k H M : Type u} [Field k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H] [IsReduced H] [ConnectedSpace (PrimeSpectrum H)]
  [Group.IsSolvable (WithConv (H →ₐ[k] k))]
  [AddCommGroup M] [Module k M] [Comodule k H M] [Module.Finite k M]

/-- Every projective orbit of a reduced connected solvable affine group over an
algebraically closed field is contained in one standard affine chart. The containment
includes all scheme points, not just rational points. -/
theorem exists_isAffineOpen_range_projectiveOrbitMap_subset_of_isSolvable
    (m : M) (hm : Module.IsUnimodular k m) :
    ∃ φ : Module.Dual k M,
      IsAffineOpen (Proj.basicOpen
        (TauCeti.SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k M))
        (SymmetricAlgebra.ι k (Module.Dual k M) φ)) ∧
      Set.range (projectiveOrbitMap (H := H) m hm) ⊆
        (Proj.basicOpen
          (TauCeti.SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k M))
          (SymmetricAlgebra.ι k (Module.Dual k M) φ) : Set _) := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    obtain ⟨ψ, hψ⟩ := Module.isUnimodular_iff.mp hm
    simp at hψ
  obtain ⟨φ, hφ⟩ := exists_isGroupLikeElem_matrixCoefficient_of_isSolvable
    (k := k) (H := H) hm0
  refine ⟨φ, Proj.isAffineOpen_basicOpen _ _
    (TauCeti.SymmetricAlgebra.ι_mem_homogeneousSubmodule k (Module.Dual k M) φ)
    (by decide : 0 < 1), ?_⟩
  rintro _ ⟨x, rfl⟩
  have htop : projectiveOrbitMap (H := H) m hm ⁻¹ᵁ
      Proj.basicOpen _ (SymmetricAlgebra.ι k (Module.Dual k M) φ) = ⊤ := by
    rw [projectiveOrbitMap_preimage_basicOpen_ι]
    exact Scheme.basicOpen_of_isUnit _ (hφ.isUnit.map (Scheme.ΓSpecIso (.of H)).inv.hom)
  exact htop.ge (Set.mem_univ x)

end Solvable

end TauCeti.Comodule
