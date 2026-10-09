/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.ProjectiveGeneralLinear.SmoothConnected
public import TauCeti.Algebra.AlgebraicGroup.Reductive.Basic
public import TauCeti.Algebra.AlgebraicGroup.Semisimple.Basic
import TauCeti.Algebra.AlgebraicGroup.Semisimple.Isogeny
import TauCeti.Algebra.AlgebraicGroup.Semisimple.Reductive
import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.CentralIsogeny
import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Semisimple
import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Smooth

/-!
# The projective general linear group is semisimple

The group `PGLₙ = Aut(Mₙ)` is semisimple, hence reductive, over every field, in every rank and
in every characteristic. It is the target of the central isogeny `SLₙ → PGLₙ`
(`TauCeti.SpecialLinear.isCentralIsogeny_conjugationMap`), the group `SLₙ` is semisimple, and
the target of a central isogeny from a semisimple group is semisimple
(`TauCeti.semisimpleCommHopfAlgProperty.of_isCentralIsogeny`).

## Main declarations

* `TauCeti.ProjectiveGeneralLinear.semisimpleCommHopfAlgProperty_coordinateHopfAlgebra`: `PGLₙ` is
  semisimple.
* `TauCeti.ProjectiveGeneralLinear.reductiveCommHopfAlgProperty_coordinateHopfAlgebra`: `PGLₙ` is
  reductive.

## References

* J. S. Milne, *Algebraic Groups* (2017), Examples 5.49 and 21.4.
-/

public section

open CategoryTheory

namespace TauCeti.ProjectiveGeneralLinear

universe u

variable (n : ℕ) (k : Type u) [Field k]

/-- **The projective general linear group is semisimple** over every field and in every rank,
with no restriction on the characteristic. -/
theorem semisimpleCommHopfAlgProperty_coordinateHopfAlgebra :
    semisimpleCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.of k (coordinateHopfAlgebra n k)) := by
  have hSL := (semisimpleCommHopfAlgProperty k).prop_of_iso
    (ObjectProperty.isoMk _ (eqToIso (SpecialLinear.finiteTypeCoordinateHopfAlgebra_obj k n)) :
      SpecialLinear.finiteTypeCoordinateHopfAlgebra k n ≅
        FiniteTypeCommHopfAlgCat.of k (SpecialLinear.coordinateHopfAlgebra k n))
    (SpecialLinear.semisimpleCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra k n)
  exact hSL.of_isCentralIsogeny (SpecialLinear.conjugationMap n k)
    (SpecialLinear.isCentralIsogeny_conjugationMap n k)

/-- **The projective general linear group is reductive** over every field and in every rank. -/
theorem reductiveCommHopfAlgProperty_coordinateHopfAlgebra :
    reductiveCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.of k (coordinateHopfAlgebra n k)) :=
  (semisimpleCommHopfAlgProperty_coordinateHopfAlgebra n k).reductive

end TauCeti.ProjectiveGeneralLinear
