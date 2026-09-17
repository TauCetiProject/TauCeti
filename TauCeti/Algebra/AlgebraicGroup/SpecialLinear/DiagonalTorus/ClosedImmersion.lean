/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.DiagonalTorus.Basic
public import TauCeti.Algebra.AlgebraicGroup.Torus.Basic

/-!
# The diagonal torus as a closed subgroup of the special linear group

Over every commutative ring, the diagonal torus of `SL_{r+1}` is cut out by the Hopf ideal of
functions whose restriction to the torus vanishes, the kernel of the surjective coordinate
morphism `TauCeti.SpecialLinear.diagonalTorusCoordinateMap`. The quotient by this ideal is the
Laurent coordinate Hopf algebra of the rank-`r` split torus, and the ideal is compatible with
scalar extension. These constructions make the diagonal torus available as a closed subgroup
when studying maximal tori.

## Main declarations

* `TauCeti.SpecialLinear.diagonalTorusDefiningIdeal`: the Hopf ideal cutting out the diagonal
  torus in `SL_{r+1}`.
* `TauCeti.SpecialLinear.diagonalTorusCoordinateIso`: its coordinate quotient is the Laurent
  coordinate Hopf algebra of the rank-`r` split torus.
* `TauCeti.SpecialLinear.splitTorusCommHopfAlgProperty_quotient_diagonalTorusDefiningIdeal`: that
  quotient is a split torus.
* `TauCeti.SpecialLinear.map_baseChangeHopfIdeal_diagonalTorusDefiningIdeal`: the defining ideal
  is compatible with scalar extension.
* `TauCeti.SpecialLinear.torusCommHopfAlgProperty_quotient_diagonalTorusDefiningIdeal`: over a
  field, the quotient is a torus.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 12 and 17.
* The construction follows the diagonal tori of
  `TauCeti.Algebra.AlgebraicGroup.GeneralLinear.DiagonalTorus.Maximal` and
  `TauCeti.Algebra.AlgebraicGroup.Symplectic.DiagonalTorus.ClosedImmersion`.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.SpecialLinear

universe u

noncomputable section

variable (r : ℕ)

section CommRing

variable (R : Type u) [CommRing R]

/-- The Hopf ideal defining the diagonal torus inside the coordinate Hopf algebra of `SL_{r+1}`:
the kernel of restriction to the torus. -/
noncomputable def diagonalTorusDefiningIdeal : HopfIdeal R (coordinateHopfAlgebra R (r + 1)) :=
  HopfIdeal.kerOfSurjective (diagonalTorusCoordinateMap r R).hom
    (diagonalTorusCoordinateMap_surjective r R)

/-- A function belongs to the diagonal-torus ideal precisely when its restriction vanishes. -/
@[simp]
theorem mem_diagonalTorusDefiningIdeal (x : coordinateHopfAlgebra R (r + 1)) :
    x ∈ diagonalTorusDefiningIdeal r R ↔ (diagonalTorusCoordinateMap r R).hom x = 0 := by
  rw [diagonalTorusDefiningIdeal, HopfIdeal.mem_kerOfSurjective]

/-- The quotient by the diagonal-torus ideal is the Laurent coordinate Hopf algebra of the
rank-`r` split torus. -/
noncomputable def diagonalTorusCoordinateIso :
    FiniteTypeCommHopfAlgCat.quotient ⟨coordinateHopfAlgebra R (r + 1),
        (finiteTypeCommHopfAlgProperty_iff _).2 inferInstance⟩
        (diagonalTorusDefiningIdeal r R) ≅
      DiagonalizableGroup.coordinateRing R (SplitTorus.characterGroup (ULift.{u} (Fin r))) :=
  ObjectProperty.isoMk _ <|
    CommHopfAlgCat.quotientKerOfSurjectiveIso (diagonalTorusCoordinateMap r R)
      (diagonalTorusCoordinateMap_surjective r R)

/-- The quotient isomorphism identifies the quotient morphism with restriction to the torus. -/
@[simp]
theorem mkQuotient_comp_diagonalTorusCoordinateIso_hom :
    FiniteTypeCommHopfAlgCat.mkQuotient ⟨coordinateHopfAlgebra R (r + 1),
        (finiteTypeCommHopfAlgProperty_iff _).2 inferInstance⟩
          (diagonalTorusDefiningIdeal r R) ≫
        (diagonalTorusCoordinateIso r R).hom =
      ObjectProperty.homMk (diagonalTorusCoordinateMap r R) :=
  ObjectProperty.hom_ext _ (CommHopfAlgCat.mkQuotient_comp_quotientKerOfSurjectiveIso_hom _ _)

/-- The coordinate quotient defining the diagonal torus of `SL_{r+1}` is a split torus. -/
theorem splitTorusCommHopfAlgProperty_quotient_diagonalTorusDefiningIdeal :
    splitTorusCommHopfAlgProperty R
      (FiniteTypeCommHopfAlgCat.quotient ⟨coordinateHopfAlgebra R (r + 1),
        (finiteTypeCommHopfAlgProperty_iff _).2 inferInstance⟩
        (diagonalTorusDefiningIdeal r R)) := by
  rw [splitTorusCommHopfAlgProperty_iff]
  exact ⟨r, ⟨(diagonalTorusCoordinateIso r R).symm⟩⟩

grind_pattern splitTorusCommHopfAlgProperty_quotient_diagonalTorusDefiningIdeal =>
  diagonalTorusDefiningIdeal r R

/-- The base-change isomorphism of special-linear coordinate Hopf algebras carries the
base-changed diagonal-torus ideal onto the diagonal-torus ideal over the extended base. -/
@[simp]
theorem map_baseChangeHopfIdeal_diagonalTorusDefiningIdeal
    (K : Type u) [CommRing K] [Algebra R K] :
    (CommHopfAlgCat.baseChangeHopfIdeal (K := K) (diagonalTorusDefiningIdeal r R)).map
        (coordinateHopfAlgebraBaseChangeIso R K (r + 1)).hom.hom =
      diagonalTorusDefiningIdeal r K :=
  CommHopfAlgCat.map_baseChangeHopfIdeal_kerOfSurjective
    (coordinateHopfAlgebraBaseChangeIso R K (r + 1))
    (DiagonalizableGroup.baseChangeCoordinateHopfAlgebraIso R K
      (SplitTorus.characterGroup (ULift.{u} (Fin r))))
    (diagonalTorusCoordinateMap_surjective r R) (diagonalTorusCoordinateMap_surjective r K)
    (diagonalTorusCoordinateMap_baseChange r R K)

end CommRing

variable (k : Type u) [Field k]

/-- Over a field, the coordinate quotient defining the diagonal torus of `SL_{r+1}` is a torus. -/
theorem torusCommHopfAlgProperty_quotient_diagonalTorusDefiningIdeal :
    torusCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient ⟨coordinateHopfAlgebra k (r + 1),
        (finiteTypeCommHopfAlgProperty_iff _).2 inferInstance⟩
        (diagonalTorusDefiningIdeal r k)) :=
  (splitTorusCommHopfAlgProperty_quotient_diagonalTorusDefiningIdeal r k).torus k _

grind_pattern torusCommHopfAlgProperty_quotient_diagonalTorusDefiningIdeal =>
  diagonalTorusDefiningIdeal r k

end

end TauCeti.SpecialLinear
