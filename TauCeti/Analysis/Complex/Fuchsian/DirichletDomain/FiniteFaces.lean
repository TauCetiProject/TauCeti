/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.DirichletDomain.Finite
public import TauCeti.Analysis.Complex.UpperHalfPlane.DirichletDomain.FiniteFaces

/-!
# Finite face covers of Fuchsian Dirichlet domains

A Fuchsian Dirichlet domain with a bounded truncation outside finitely many cusp horodiscs has
a boundary covered by finitely many equality faces. Each nonempty selected face is an extended
geodesic segment, allowing finite segments, rays with an ideal endpoint, and complete geodesics
between ideal points.

This is the boundary-data step in constructing a finite-sided cuspidal Dirichlet polygon. It does
not order the faces cyclically or discard empty and singleton faces; those operations require the
incidence theory of the selected geodesics.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, §9.4.
* Svetlana Katok, *Fuchsian Groups*, §§3.2 and 4.2.
-/

public section

open Metric Set UpperHalfPlane TauCeti
open TauCeti.UpperHalfPlane
open scoped MatrixGroups OnePoint

namespace Subgroup

variable (Γ : Subgroup PSL(2, ℝ)) {ι : Type*} [Finite ι] [DiscreteTopology Γ]

/-- A bounded cusp truncation supplies finitely many geodesic faces which cover the entire
boundary of the Dirichlet domain. Every nonempty selected face is presented uniformly by its two
finite or ideal endpoints. Empty and singleton faces are retained, since the finite constraint
family need not be irredundant. -/
theorem exists_finset_dirichletFace_cover_of_isBounded_truncation
    (p : ℍ) (D : ι → Γ.CuspDatum) {A : ι → ℝ} (hA : ∀ i, 0 < A i)
    (hb : Bornology.IsBounded (sdiff (dirichletDomain Γ p) (⋃ i, (D i).horodisc (A i)))) :
    ∃ s : Finset Γ, (∀ g ∈ s, p ≠ g • p) ∧
      frontier (dirichletDomain Γ p) = ⋃ g ∈ s, dirichletFace p g ∧
      ∀ g ∈ s, (dirichletFace p g).Nonempty →
        ∃ a b : ℍ ⊕ OnePoint ℝ, dirichletFace p g = extGeodesicSegment a b := by
  obtain ⟨s, hmove, hD⟩ :=
    Γ.exists_finset_dirichletDomain_eq_iInter_closure_leftHalfPlane_of_isBounded_truncation
      p D hA hb
  refine ⟨s, hmove,
    frontier_dirichletDomain_eq_biUnion_dirichletFace_of_eq_iInter hmove hD, ?_⟩
  intro g hg hne
  exact exists_dirichletFace_eq_extGeodesicSegment (hmove g hg).symm hne

end Subgroup
