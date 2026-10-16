/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Group.DirichletDomain.Basic
import TauCeti.Topology.Compactness.LocallyCompact

/-!
# Compact Dirichlet domains

For an isometric group action on a proper metric space with compact orbit space, every
Dirichlet domain is compact. A compact set of orbit representatives bounds the distance from
a point of the domain to its centre. No proper discontinuity or freeness is needed.

In the hyperbolic plane, this supplies the boundedness used to reduce the defining bisectors
to a finite family when the orbit quotient is compact.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, §9.4.
* Svetlana Katok, *Fuchsian Groups*, §3.2.

Compact representatives are supplied by `IsOpenMap.exists_isCompact_subset_image`.
-/

public section

open Metric MulAction Set

namespace TauCeti

variable {G X : Type*} [Group G] [PseudoMetricSpace X] [ProperSpace X]
  [MulAction G X] [IsIsometricSMul G X]

/-- If the orbit space of an isometric action on a proper metric space is compact, every
Dirichlet domain is compact. The action need not be properly discontinuous. -/
theorem isCompact_dirichletDomain_of_compactSpace
    [CompactSpace (orbitRel.Quotient G X)] (p : X) : IsCompact (dirichletDomain G p) := by
  obtain ⟨K, hK, hcover⟩ := isOpenMap_quotient_mk'_mul.exists_isCompact_subset_image
    (Quotient.mk''_surjective : Function.Surjective (Quotient.mk'' : X → orbitRel.Quotient G X))
    isCompact_univ
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall p
  refine (isCompact_closedBall p r).of_isClosed_subset (isClosed_dirichletDomain G p) ?_
  intro x hx
  obtain ⟨y, hyK, hy⟩ := hcover (mem_univ (Quotient.mk'' x))
  obtain ⟨g, hg⟩ := mem_orbit_iff.mp (orbitRel_apply.mp (Quotient.exact hy))
  have hxg := mem_dirichletDomain.mp hx g⁻¹
  have hdist : dist x (g⁻¹ • p) = dist y p := by
    rw [← dist_smul g, smul_inv_smul, hg]
  exact hxg.trans (hdist ▸ hr hyK)

end TauCeti
