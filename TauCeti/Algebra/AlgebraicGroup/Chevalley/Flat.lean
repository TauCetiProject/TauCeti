/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Datum
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Flat
public import TauCeti.AlgebraicGeometry.Fibers.SchematicDensity

/-!
# Flatness and generic fibres of Chevalley data

The group scheme of a Chevalley datum has torsion-free coordinate algebra over `ℤ`, and hence
is flat over `ℤ`. Its generic fibre is schematically dense: the ideal sheaf cutting out the
integral group in `GLₙ` is already the kernel of the map from its rational generic fibre.
Thus the integral group is the schematic closure of that fibre in the given representation.

These statements retain the datum's actual coordinate weights, which parametrize the torus
with character lattice equal to the lattice spanned by the representation's weights. They
apply to every Chevalley datum, not just to representations with full weight lattice.
Flatness and generic-fibre density do not assert smoothness, or that the integral generated
subgroup commutes with specialization to a field of positive characteristic.

The torsion-freeness input is
`TauCeti.UniversalEnvelopingAlgebra.isTorsionFree_kostantToralCoordinateHopfAlgebra`;
no second construction of the integral group is used.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
* The Stacks Project, [Tag 0AUW](https://stacks.math.columbia.edu/tag/0AUW), for flatness
  of torsion-free modules over Dedekind domains.
-/

public section

open AlgebraicGeometry CategoryTheory

namespace TauCeti.DynkinType.ChevalleyDatum

noncomputable section

-- Use the scalar module of the coordinate algebra in the flatness criterion.
attribute [local instance high] Algebra.toModule

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

/-- The structural morphism of the integral group scheme of a Chevalley datum is flat. -/
instance flat_groupScheme : Flat D.groupScheme.X.hom := by
  rw [D.groupScheme_eq_hopfSpec]
  exact (moduleFlat_iff_flat_hopfSpec ℤ D.coordinateHopfAlgebra).mp inferInstance

/-- The rational generic fibre is schematically dense in the integral group scheme. -/
instance isSchemeTheoreticallyDominant_genericFiberι :
    IsSchemeTheoreticallyDominant (genericFiberι ℤ ℚ D.groupScheme.X.hom) :=
  TauCeti.isSchemeTheoreticallyDominant_genericFiberι ℤ ℚ (Int.cast_injective) _

/-- The integral defining ideal sheaf in `GLₙ` is recovered from the rational generic fibre.
Equivalently, the integral group is the schematic closure of its generic fibre in `GLₙ`. -/
theorem ker_genericFiberι_comp_groupSchemeι :
    (genericFiberι ℤ ℚ D.groupScheme.X.hom ≫ D.groupSchemeι.hom.hom.left).ker =
      D.groupSchemeι.hom.hom.left.ker :=
  Scheme.Hom.ker_comp_of_isSchemeTheoreticallyDominant _ _

end

end TauCeti.DynkinType.ChevalleyDatum
