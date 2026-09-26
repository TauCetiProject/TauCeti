/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Generation
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Burnside
import TauCeti.Topology.Algebra.Group.OpenSubgroup.TopologicallyFinitelyGenerated

/-!
# Finite generation and the Frattini quotient

A profinite pro-`p` group is topologically finitely generated if and only if its Frattini
quotient is finite, equivalently if and only if its Frattini subgroup is open. This turns
topological finite generation into a finiteness condition on the maximal elementary abelian
quotient, as needed for the finite-dimensional form of the Burnside basis theorem.

The forward implication holds for any compact topologically finitely generated group:
there are only finitely many open normal subgroups of index `p`, so their intersection is
open. For the converse, lift the finite set of all elements of the quotient and apply the
topological Burnside theorem. In particular, the converse uses the pro-`p` hypothesis.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 2.8.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

/-- In a compact topologically finitely generated group, the intersection of the open normal
subgroups of any fixed index is open. In particular, its pro-`p` Frattini subgroup is open. -/
theorem IsTopologicallyFinitelyGenerated.isOpen_proPFrattini
    (hG : IsTopologicallyFinitelyGenerated G) (p : ℕ) :
    IsOpen (proPFrattini p G : Set G) := by
  have := hG.finite_openSubgroup_index_eq p
  have : Finite {U : OpenNormalSubgroup G // U.toSubgroup.index = p} :=
    Finite.of_injective
      (fun U ↦ (⟨U.1.toOpenSubgroup, U.2⟩ :
        {U : OpenSubgroup G // (U : Subgroup G).index = p})) (by
      intro U V h
      apply Subtype.ext
      apply OpenNormalSubgroup.toSubgroup_injective
      exact congrArg (fun U : {U : OpenSubgroup G // (U : Subgroup G).index = p} ↦
        U.1.toSubgroup) h)
  rw [proPFrattini_def, Subgroup.coe_iInf]
  exact isOpen_iInter_of_finite fun U ↦ U.1.isOpen

/-- The pro-`p` Frattini quotient of a compact topologically finitely generated group is finite.
Neither primality of `p` nor the pro-`p` condition on the group is needed in this direction. -/
theorem IsTopologicallyFinitelyGenerated.finite_quotient_proPFrattini
    (hG : IsTopologicallyFinitelyGenerated G) (p : ℕ) :
    Finite (G ⧸ proPFrattini p G) :=
  Subgroup.quotient_finite_of_isOpen _ (hG.isOpen_proPFrattini p)

variable {p : ℕ} [Fact p.Prime] [TotallyDisconnectedSpace G]

/-- **Finite generation detected by the Frattini quotient.** A profinite pro-`p` group is
topologically finitely generated exactly when its Frattini quotient is finite. -/
theorem IsProP.isTopologicallyFinitelyGenerated_iff_finite_quotient_proPFrattini
    (hG : IsProP p G) :
    IsTopologicallyFinitelyGenerated G ↔ Finite (G ⧸ proPFrattini p G) := by
  refine ⟨fun h ↦ h.finite_quotient_proPFrattini p, fun h ↦ ?_⟩
  let q := QuotientGroup.mk' (proPFrattini p G)
  obtain ⟨s, -, hs, hqs⟩ :=
    (Set.finite_univ (α := G ⧸ proPFrattini p G)).exists_subset_finite_image_eq
      (f := q) (s := Set.univ) (by
        rw [Set.image_univ, (QuotientGroup.mk'_surjective _).range_eq])
  apply hs.isTopologicallyFinitelyGenerated
  rw [topologicallyGenerates_iff_frattiniQuotient hG s, hqs, Subgroup.closure_univ]
  exact top_unique (Subgroup.le_topologicalClosure _)

/-- **The open Frattini criterion.** A profinite pro-`p` group is topologically finitely
generated exactly when its Frattini subgroup is open. -/
theorem IsProP.isTopologicallyFinitelyGenerated_iff_isOpen_proPFrattini
    (hG : IsProP p G) :
    IsTopologicallyFinitelyGenerated G ↔ IsOpen (proPFrattini p G : Set G) := by
  refine ⟨fun h ↦ h.isOpen_proPFrattini p, fun h ↦ ?_⟩
  exact hG.isTopologicallyFinitelyGenerated_iff_finite_quotient_proPFrattini.mpr
    (Subgroup.quotient_finite_of_isOpen _ h)

end TauCeti
