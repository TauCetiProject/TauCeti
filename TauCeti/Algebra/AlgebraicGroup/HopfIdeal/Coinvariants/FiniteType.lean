/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.FiniteType

/-!
# Finite generation of normal coinvariants

For a normal closed subgroup of a geometrically reduced finite-type affine group over a field,
the invariant functions form a finite-type Hopf algebra. The corresponding affine quotient
projection is faithfully flat. The subgroup may be nonreduced, and the field need not be perfect.

These statements concern the actual coinvariant algebra, rather than a chosen finite-type
subalgebra of it. Identifying the kernel of this projection with the original normal subgroup
is a separate assertion, required to identify the quotient with the fppf quotient by that subgroup.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §16.3.
* J. S. Milne, *Algebraic Groups* (2017), §5.c.
-/

public section

namespace TauCeti

universe u

noncomputable section

variable {k : Type u} [Field k] {H : _root_.CommHopfAlgCat.{u} k}
  [Algebra.FiniteType k H] [Algebra.IsGeometricallyReduced k H]
  {I : HopfIdeal k H}

namespace HopfIdeal.IsNormal

/-- The coinvariants of a normal closed subgroup of a geometrically reduced finite-type affine
group over a field are finitely generated as an algebra. The subgroup need not be smooth. -/
theorem finiteType_coinvariants (hI : I.IsNormal) : Algebra.FiniteType k I.coinvariants :=
  _root_.CommHopfAlgCat.finiteType_of_injective (CommHopfAlgCat.coinvariantsι hI)
    (CommHopfAlgCat.hopfSubalgebraι_injective hI.isHopfSubalgebra_coinvariants)

end HopfIdeal.IsNormal

namespace CommHopfAlgCat

/-- The affine quotient projection defined by normal coinvariants is faithfully flat when the
ambient finite-type affine group is geometrically reduced, over any field. -/
theorem faithfullyFlat_coinvariantsι (hI : I.IsNormal) :
    (coinvariantsι hI).hom.toAlgHom.toRingHom.FaithfullyFlat := by
  let : Algebra.FiniteType k (coinvariants hI) := hI.finiteType_coinvariants
  have hinj := hopfSubalgebraι_injective hI.isHopfSubalgebra_coinvariants
  let : Algebra.IsGeometricallyReduced k (coinvariants hI) :=
    Algebra.IsGeometricallyReduced.of_injective (coinvariantsι hI).hom.toAlgHom hinj
  exact (faithfullyFlat_iff_injective_of_isGeometricallyReduced (coinvariantsι hI)).mpr hinj

end CommHopfAlgCat

end

end TauCeti
