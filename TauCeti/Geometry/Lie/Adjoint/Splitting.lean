/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Basic
public import TauCeti.RepresentationTheory.Subrepresentation
import TauCeti.Order.ModularLattice

/-!
# Invariant splittings of a Lie algebra along a compact subgroup

Let `H` be a compact subgroup of a Lie group `G`, acting on the Lie algebra
`𝔤 = GroupLieAlgebra I G` by the adjoint action, and let `𝔥 ≤ 𝔨` be `Ad(H)`-invariant subspaces of
`𝔤`. The adjoint representation of `H` is semisimple
(`TauCeti.Lie.isSemisimpleRepresentation_adjointRepresentation_comp_subtype`, by averaging over
`H`), so its subrepresentations form a complemented modular lattice. Taking a relative complement
of `𝔥` in `𝔨` and a complement of `𝔨`, as for any flag in such a lattice
(`TauCeti.exists_sup_eq_and_isCompl_of_le`), gives `Ad(H)`-invariant subspaces `𝔪` and `𝔮` with

`𝔤 = 𝔥 ⊕ 𝔪 ⊕ 𝔮`,  `𝔥 ⊕ 𝔪 = 𝔨`,

so that `𝔪` complements `𝔥` in `𝔨` and `𝔮` complements `𝔨` in `𝔤`
(`TauCeti.Lie.exists_sup_eq_and_isCompl_of_isCompact`). Neither `G` nor `H` need be connected,
and no `Ad(G)`-invariant inner product is assumed or produced; for noncompact `G` there need not be
one.

A complement determines the inclusion of the dual of each summand into `𝔤*`: a linear form on a
summand is extended by zero on the complementary sum, that is, composed with the projection along
it. For invariant summands this inclusion intertwines the dual of the adjoint action of `H` on the
summand with the coadjoint action of `H` on `𝔤*`: this is
`Subrepresentation.isIntertwiningMap_dualMap_projectionOnto`, since the coadjoint representation
of `H` is the dual of its adjoint representation (`TauCeti.Lie.coadjointRepresentation_def` and
`Representation.dual_comp`). Applied to the splitting above, it includes `𝔥*` and `𝔪*`
equivariantly into `𝔤*`.

This is the linear algebra of the local model of a Hamiltonian action near an orbit with compact
stabilizer `H` (the Marle–Guillemin–Sternberg normal form), where `𝔨` is the Lie algebra of the
coadjoint stabilizer of the moment map value, which contains `𝔥`.

## Main results

* `TauCeti.Lie.exists_sup_eq_and_isCompl_of_isCompact`: `Ad(H)`-invariant complements
  `𝔤 = 𝔥 ⊕ 𝔪 ⊕ 𝔮` adapted to a flag `𝔥 ≤ 𝔨` of invariant subspaces.

## References

* C.-M. Marle, *Modèle d'action hamiltonienne d'un groupe de Lie sur une variété symplectique*,
  Rend. Sem. Mat. Univ. Politec. Torino 43 (1985), 227–251.
* V. Guillemin and S. Sternberg, *A normal form for the moment map*, in *Differential Geometric
  Methods in Mathematical Physics*, Math. Phys. Stud. 6, Reidel (1984), 161–175.
* J.-P. Ortega and T. S. Ratiu, *Momentum Maps and Hamiltonian Reduction*, Progress in
  Mathematics 222, Birkhäuser (2004), Section 7.2.
-/

public section

namespace TauCeti.Lie

open scoped ContDiff Manifold

section Splitting

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H' G] [Group G] [LieGroup I ∞ G]

/-- **Invariant splittings of the Lie algebra along a compact subgroup.** Let `H` be a compact
subgroup of a Lie group `G` and `𝔥 ≤ 𝔨` subspaces of `𝔤` invariant under `Ad(H)`. There are
`Ad(H)`-invariant subspaces `𝔪` and `𝔮` with `𝔥 ⊕ 𝔪 = 𝔨` and `𝔨 ⊕ 𝔮 = 𝔤`, so that
`𝔤 = 𝔥 ⊕ 𝔪 ⊕ 𝔮` and each summand is complementary to the sum of the other two. -/
theorem exists_sup_eq_and_isCompl_of_isCompact {H : Subgroup G} (hH : IsCompact (H : Set G))
    {𝔥 𝔨 : Subrepresentation ((adjointRepresentation ℝ I G).comp H.subtype)} (h𝔥𝔨 : 𝔥 ≤ 𝔨) :
    ∃ 𝔪 𝔮 : Subrepresentation ((adjointRepresentation ℝ I G).comp H.subtype),
      𝔥 ⊔ 𝔪 = 𝔨 ∧ IsCompl 𝔨 𝔮 ∧ IsCompl 𝔥 (𝔪 ⊔ 𝔮) ∧ IsCompl 𝔪 (𝔥 ⊔ 𝔮) := by
  have := isSemisimpleRepresentation_adjointRepresentation_comp_subtype (I := I) hH
  exact exists_sup_eq_and_isCompl_of_le h𝔥𝔨

end Splitting

end TauCeti.Lie
