/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Borel.Basic
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.Positive.Generated.Solvable

/-!
# A Borel candidate inside the generated Geck group

The positive numbered root subgroups and weight torus generate a smooth, geometrically connected
closed subgroup with solvable geometric points over every field. This file proves that its
intrinsic Hopf ideal in the full generated Geck group is a Borel candidate. The quotient is
identified with the existing positive coordinate algebra, not with a new carrier.

Maximality among smooth connected solvable closed subgroups is not asserted here. Neither
generated group is identified with the specialization of the integral carrier or an independently
pinned group. The statements apply to every valid diagram; the Geck representation need not be
faithful on the simply connected form for these subgroup statements.

## References

* M. Geck, *On the construction of semisimple Lie algebras and Chevalley groups*,
  Proc. Amer. Math. Soc. **145** (2017), 3233--3247.
* J. S. Milne, *Algebraic Groups* (2017), Section 17.a.
* The quotient transport follows
  `TauCeti.Algebra.Lie.E6.Minuscule.Generated.Positive.BorelCandidate`.
-/

public section

namespace TauCeti.DynkinType

universe v

/-- The positive subgroup is a Borel candidate inside the full generated Geck group over every
field: it is smooth, geometrically connected, and has solvable geometric points. -/
theorem isBorelCandidate_geckPositiveGeneratedCarrierDefiningIdeal
    (t : DynkinType) (ht : t.Valid) (k : Type v) [Field k] :
    HopfIdeal.IsBorelCandidate k
      (FiniteTypeCommHopfAlgCat.of k (t.geckGeneratedCoordinateHopfAlgebra ht k))
      (t.geckPositiveGeneratedCarrierDefiningIdeal ht k) := by
  let e := t.geckPositiveGeneratedCarrierQuotientIso ht k
  exact HopfIdeal.IsBorelCandidate.mk
    ((smoothCommHopfAlgProperty k).prop_of_iso e.symm
      (t.smoothCommHopfAlgProperty_geckPositiveGeneratedCoordinateHopfAlgebra ht k))
    ((geometricallyConnectedCommHopfAlgProperty k).prop_of_iso e.symm
      (t.geometricallyConnectedCommHopfAlgProperty_geckPositiveGeneratedCoordinateHopfAlgebra ht k))
    ((geometricallySolvablePointsCommHopfAlgProperty k).prop_of_iso e.symm
      (t.geometricallySolvablePointsCommHopfAlgProperty_geckPositiveGeneratedCoordinateHopfAlgebra
        ht k))

end TauCeti.DynkinType
