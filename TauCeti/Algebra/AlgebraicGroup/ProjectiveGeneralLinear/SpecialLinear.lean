/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Semisimple.Center.Isogeny
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.CentralIsogeny
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Semisimple
public import TauCeti.Algebra.AlgebraicGroup.ProjectiveGeneralLinear.Center
import TauCeti.AlgebraicGeometry.GroupScheme.CentralIsogeny.Isomorphism

/-!
# The represented center quotient of the special linear group

Over every field, `PGLₙ` is canonically the represented quotient of `SLₙ` by its full
scheme-theoretic center. The comparison commutes with the conjugation homomorphism
`SLₙ → PGLₙ`, and is therefore a comparison of quotient maps, rather than just an
abstract isomorphism of groups. This includes characteristics dividing `n`, where the
center can be nonreduced.

The construction applies `centerQuotientIsoOfIsCentralIsogeny` to the central isogeny
proved in `SpecialLinear.CentralIsogeny` and the centerless target from
`ProjectiveGeneralLinear.Center`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §21, the adjoint quotient of `SLₙ`.
-/

public section

open CategoryTheory

namespace TauCeti.ProjectiveGeneralLinear

universe u

variable (n : ℕ) (k : Type u) [Field k]

/-- The projective general linear coordinate algebra is canonically the coordinate algebra
of the represented center quotient of `SLₙ`. -/
noncomputable def specialLinearCenterQuotientIso :
    coordinateHopfAlgebra n k ≅
      (SpecialLinear.semisimpleCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra
        k n).reductive.centerQuotient.obj := by
  let hSL := SpecialLinear.semisimpleCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra k n
  let e := eqToIso (SpecialLinear.finiteTypeCoordinateHopfAlgebra_obj k n).symm
  exact hSL.centerQuotientIsoOfIsCentralIsogeny
    (SpecialLinear.conjugationMap n k ≫ e.hom)
    (by
      rw [CommHopfAlgCat.isCentralIsogeny_iff_isCentralIsogeny_hopfSpec_map]
      simpa only [op_comp, Functor.map_comp] using
        ((GroupScheme.centralIsogenies k).cancel_left_of_respectsIso
          ((AlgebraicGeometry.hopfSpec (CommRingCat.of k)).map e.hom.op)
          ((AlgebraicGeometry.hopfSpec (CommRingCat.of k)).map
            (SpecialLinear.conjugationMap n k).op)).mpr
          ((CommHopfAlgCat.isCentralIsogeny_iff_isCentralIsogeny_hopfSpec_map _).mp
            (SpecialLinear.isCentralIsogeny_conjugationMap n k)))
    (centerDefiningIdeal_eq_augmentation n k)

/-- The comparison with the center quotient recovers the standard conjugation homomorphism
`SLₙ → PGLₙ`. -/
@[reassoc (attr := simp)]
theorem specialLinearCenterQuotientIso_hom_comp :
    (specialLinearCenterQuotientIso n k).hom ≫
        (SpecialLinear.semisimpleCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra
          k n).reductive.centerQuotientι ≫
        eqToHom (SpecialLinear.finiteTypeCoordinateHopfAlgebra_obj k n) =
      SpecialLinear.conjugationMap n k := by
  simp [specialLinearCenterQuotientIso]

/-- The inverse comparison also intertwines the standard quotient projections. -/
@[reassoc (attr := simp)]
theorem specialLinearCenterQuotientIso_inv_comp :
    (specialLinearCenterQuotientIso n k).inv ≫ SpecialLinear.conjugationMap n k =
      (SpecialLinear.semisimpleCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra
        k n).reductive.centerQuotientι ≫
        eqToHom (SpecialLinear.finiteTypeCoordinateHopfAlgebra_obj k n) :=
  (specialLinearCenterQuotientIso n k).inv_comp_eq.mpr
    (specialLinearCenterQuotientIso_hom_comp n k).symm

end TauCeti.ProjectiveGeneralLinear
