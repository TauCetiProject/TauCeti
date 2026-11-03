/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.TorsionClass
public import TauCeti.RingTheory.NovikovSeries.NonZeroDivisors

/-!
# The sign/monomial quotient for Novikov torsion

The monomials of a Novikov ring give units in every algebra over that ring.
`NovikovSeries.TorsionClass R N Q` quotients all of `Q` by their signed action.
Taking `Q` to be a total quotient ring gives the target for dynamical torsion,
including its nonacyclic field components. No domain or acyclicity assumption
is needed to form this quotient.

The inclusion from the group ring induces an injective map on torsion classes
of total quotient rings. Thus passing to the Novikov completion introduces no
new sign/monomial identifications of cellular torsions.

## References

* M. Hutchings, *Reidemeister torsion in generalized Morse theory*, Forum Math. 14 (2002),
  Section 2.
-/

public section

noncomputable section

namespace TauCeti.NovikovSeries

variable (R : Type*) {H : Type*} [CommRing R] [AddCommGroup H] (N : H →+ ℝ)
  (Q : Type*) [CommRing Q] [Algebra (NovikovSeries R H N) Q]

/-- The target of torsion modulo signs and deck monomials, including scalars that are not units.
For Novikov torsion, `Q` is a total quotient ring of `NovikovSeries R H N`. -/
abbrev TorsionClass := TauCeti.TorsionClass
  (AddMonoidAlgebra.deckUnitsHom R
    ((algebraMap (NovikovSeries R H N) Q).comp ofAddMonoidAlgebra))

variable {R N Q}

/-- A map from the group ring's total quotient to the Novikov total quotient respects the
specified deck units. -/
theorem map_deckUnitsHom (Q₀ : Type*) [CommRing Q₀]
    [Algebra (AddMonoidAlgebra R H) Q₀] [IsFractionRing (AddMonoidAlgebra R H) Q₀]
    [IsFractionRing (NovikovSeries R H N) Q] [NoZeroDivisors R] [AddGroup.FG H]
    (h : Multiplicative H) :
    Units.map (IsLocalization.map Q
      (ofAddMonoidAlgebra : AddMonoidAlgebra R H →+* NovikovSeries R H N)
      nonZeroDivisors_le_comap_ofAddMonoidAlgebra : Q₀ →+* Q)
      (AddMonoidAlgebra.deckUnitsHom R (algebraMap (AddMonoidAlgebra R H) Q₀) h) =
    AddMonoidAlgebra.deckUnitsHom R
      ((algebraMap (NovikovSeries R H N) Q).comp ofAddMonoidAlgebra) h := by
  apply Units.ext
  simp [IsLocalization.map_eq]

/-- The total-quotient map from the group ring to the Novikov ring descends to the sign/monomial
quotients of the whole rings, not merely of their units. -/
def torsionClassOfAddMonoidAlgebra (Q₀ : Type*) [CommRing Q₀]
    [Algebra (AddMonoidAlgebra R H) Q₀] [IsFractionRing (AddMonoidAlgebra R H) Q₀]
    [IsFractionRing (NovikovSeries R H N) Q] [NoZeroDivisors R] [AddGroup.FG H] :
    TauCeti.TorsionClass
      (AddMonoidAlgebra.deckUnitsHom R (algebraMap (AddMonoidAlgebra R H) Q₀)) →*₀
      TorsionClass R N Q :=
  TauCeti.TorsionClass.map
    (IsLocalization.map Q
      (ofAddMonoidAlgebra : AddMonoidAlgebra R H →+* NovikovSeries R H N)
      nonZeroDivisors_le_comap_ofAddMonoidAlgebra : Q₀ →+* Q)
    (map_deckUnitsHom Q₀)

/-- On representatives the torsion-class map is the actual map of total quotient rings. -/
@[simp]
theorem torsionClassOfAddMonoidAlgebra_mk (Q₀ : Type*) [CommRing Q₀]
    [Algebra (AddMonoidAlgebra R H) Q₀] [IsFractionRing (AddMonoidAlgebra R H) Q₀]
    [IsFractionRing (NovikovSeries R H N) Q] [NoZeroDivisors R] [AddGroup.FG H] (a : Q₀) :
    torsionClassOfAddMonoidAlgebra (N := N) (Q := Q) Q₀
      (TauCeti.TorsionClass.mk _ a) =
    TauCeti.TorsionClass.mk
      (AddMonoidAlgebra.deckUnitsHom R
        ((algebraMap (NovikovSeries R H N) Q).comp ofAddMonoidAlgebra))
      ((IsLocalization.map Q
        (ofAddMonoidAlgebra : AddMonoidAlgebra R H →+* NovikovSeries R H N)
        nonZeroDivisors_le_comap_ofAddMonoidAlgebra : Q₀ →+* Q) a) := by
  rw [torsionClassOfAddMonoidAlgebra, TauCeti.TorsionClass.map_mk]

/-- No extra signed monomial identifications arise on passing from the group-ring total
quotient to the Novikov total quotient. -/
theorem torsionClassOfAddMonoidAlgebra_injective (Q₀ : Type*) [CommRing Q₀]
    [Algebra (AddMonoidAlgebra R H) Q₀] [IsFractionRing (AddMonoidAlgebra R H) Q₀]
    [IsFractionRing (NovikovSeries R H N) Q] [NoZeroDivisors R] [AddGroup.FG H] :
    Function.Injective (torsionClassOfAddMonoidAlgebra (R := R) (N := N) (Q := Q) Q₀) :=
  TauCeti.TorsionClass.map_injective _ _ (map_ofAddMonoidAlgebra_injective Q₀ Q)

end TauCeti.NovikovSeries
