/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Root.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.RootSubgroup.Basic
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.BaseChange

/-!
# Base change of special-linear root subgroups

The elementary root maps `xᵢⱼ : 𝔾ₐ → SLₙ` are compatible with arbitrary base
extension. The canonical identifications of the scalar-extended coordinate Hopf
algebras with those constructed over the new ring preserve the normalized root maps.
Thus extending an integral elementary root subgroup gives the chosen elementary root
subgroup over the new base, including in positive characteristic and over rings with
nilpotents.

The compatibility follows from the general-linear root-map calculation and
`coordinateMap_comp_rootSubgroupCoordinateMap`, using the surjective determinant-one
quotient. No new presentation of the root maps is introduced.

## References

* B. Conrad, *Reductive Group Schemes* (2014), §5.1.
* J. S. Milne, *Algebraic Groups* (2017), §21, Example 21.2.
-/

public section

open CategoryTheory

namespace TauCeti.SpecialLinear

universe u v

variable (R : Type u) (K : Type max u v) [CommRing R] [CommRing K] [Algebra R K]
variable {n : ℕ} {i j : Fin n}

/-- The normalized special-linear root map commutes with scalar extension under
the canonical coordinate-algebra identifications. In particular, this identifies
the base change of each integral root subgroup with the root subgroup over `K`. -/
-- Supply the ring arguments explicitly when rewriting: the extension ring
-- lives in a `max` universe, which prevents reliable global simp matching.
@[reassoc]
theorem baseChangeMap_rootSubgroupCoordinateMap_comp_baseChangeIso_hom (hij : i ≠ j) :
    CommHopfAlgCat.baseChangeMap (K := K) (rootSubgroupCoordinateMap (R := R) hij) ≫
        (AdditiveGroup.coordinateHopfAlgebraBaseChangeIso R K).hom =
      (coordinateHopfAlgebraBaseChangeIso R K n).hom ≫
        rootSubgroupCoordinateMap (R := K) hij := by
  let q := CommHopfAlgCat.baseChangeMap (K := K) (coordinateMap R n)
  let : Epi q := ConcreteCategory.epi_of_surjective q
    (CommHopfAlgCat.baseChangeMap_surjective (coordinateMap R n)
      (CommHopfAlgCat.mkQuotient_surjective _ _))
  apply (cancel_epi q).mp
  dsimp only [q]
  rw [← Category.assoc, ← (CommHopfAlgCat.baseChangeFunctor (k := R) (K := K)).map_comp,
    coordinateMap_comp_rootSubgroupCoordinateMap]
  rw [← Category.assoc
    (CommHopfAlgCat.baseChangeMap (K := K) (coordinateMap R n))]
  rw [baseChangeMap_coordinateMap_comp_coordinateHopfAlgebraBaseChangeIso_hom]
  rw [Category.assoc, coordinateMap_comp_rootSubgroupCoordinateMap]
  exact GeneralLinear.baseChangeMap_rootSubgroupCoordinateMap_comp_baseChangeIso_hom R K hij

end TauCeti.SpecialLinear
