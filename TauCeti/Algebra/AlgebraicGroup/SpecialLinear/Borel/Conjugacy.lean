/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Borel.Conjugation
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Borel.Geometry
import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.UpperTriangular.Borel

/-!
# Conjugacy of Borel subgroups of `SL₂`

Over an algebraically closed field, every reduced connected solvable closed subgroup of `SL₂` is
contained in a conjugate of the standard upper-triangular subgroup; this is the rank-two case of
`TauCeti.SpecialLinear.UpperTriangular.exists_conjugate_definingHopfIdeal_le`. Consequently, every
Borel subgroup of `SL₂` is conjugate to the standard one, and any two Borel subgroups are
conjugate. This reduces questions about arbitrary Borel subgroups of `SL₂` to the standard
subgroup.

## Main results

* `TauCeti.SpecialLinear.Borel.isBorelOverAlgClosed_iff_exists_eq_conjugate`: classification of
  Borel subgroups of `SL₂` by conjugacy.
* `TauCeti.SpecialLinear.Borel.exists_conjugate_eq_of_isBorelOverAlgClosed`: geometric conjugacy
  of any two Borel subgroups of `SL₂`.

## References

* J. S. Milne, *Algebraic Groups* (2017), Section 17.a.
* T. A. Springer, *Linear Algebraic Groups*, Sections 6.2--6.3.

The corresponding `GLₙ` development is in
`TauCeti.Algebra.AlgebraicGroup.GeneralLinear.UpperTriangular.Borel`, and the containment in a
conjugate of the standard subgroup is proved for `SLₙ` in
`TauCeti.Algebra.AlgebraicGroup.SpecialLinear.UpperTriangular.Borel`.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.SpecialLinear.Borel

universe u

noncomputable section

variable {k : Type u} [Field k] [IsAlgClosed k]

private theorem exists_conjugate_definingHopfIdeal_le_of_isBorelOverAlgClosed
    (I : HopfIdeal k (SpecialLinear.coordinateHopfAlgebra k 2))
    (hI : HopfIdeal.IsBorelOverAlgClosed k
      (FiniteTypeCommHopfAlgCat.of k (SpecialLinear.coordinateHopfAlgebra k 2)) I) :
    ∃ g : WithConv (SpecialLinear.coordinateHopfAlgebra k 2 →ₐ[k] k),
      (definingHopfIdeal k).conjugate g ≤ I := by
  have hcandidate := ((HopfIdeal.isBorelOverAlgClosed_iff _ _ _).mp hI).2.1
  let _ : IsReduced (CommHopfAlgCat.quotient
      (SpecialLinear.coordinateHopfAlgebra k 2) I) :=
    ((smoothCommHopfAlgProperty_iff_geometricallyReduced k _).mp
      hcandidate.smooth).isReduced
  rw [definingHopfIdeal_eq_upperTriangular_definingHopfIdeal]
  exact SpecialLinear.UpperTriangular.exists_conjugate_definingHopfIdeal_le I
    hcandidate.geometricallyConnected hcandidate.geometricallySolvable

/-- Over an algebraically closed field, the Borel subgroups of `SL₂` are precisely the
conjugates of its standard upper-triangular Borel. -/
theorem isBorelOverAlgClosed_iff_exists_eq_conjugate
    (I : HopfIdeal k (SpecialLinear.coordinateHopfAlgebra k 2)) :
    HopfIdeal.IsBorelOverAlgClosed k
        (FiniteTypeCommHopfAlgCat.of k (SpecialLinear.coordinateHopfAlgebra k 2)) I ↔
      ∃ g : WithConv (SpecialLinear.coordinateHopfAlgebra k 2 →ₐ[k] k),
        I = (definingHopfIdeal k).conjugate g :=
  HopfIdeal.isBorelOverAlgClosed_iff_exists_eq_conjugate _
    (isBorelCandidate_definingHopfIdeal k)
    exists_conjugate_definingHopfIdeal_le_of_isBorelOverAlgClosed I

/-- Any two Borel subgroups of `SL₂` over an algebraically closed field are conjugate by an
`SL₂`-point. -/
theorem exists_conjugate_eq_of_isBorelOverAlgClosed
    {I J : HopfIdeal k (SpecialLinear.coordinateHopfAlgebra k 2)}
    (hI : HopfIdeal.IsBorelOverAlgClosed k
      (FiniteTypeCommHopfAlgCat.of k (SpecialLinear.coordinateHopfAlgebra k 2)) I)
    (hJ : HopfIdeal.IsBorelOverAlgClosed k
      (FiniteTypeCommHopfAlgCat.of k (SpecialLinear.coordinateHopfAlgebra k 2)) J) :
    ∃ g : WithConv (SpecialLinear.coordinateHopfAlgebra k 2 →ₐ[k] k),
      I.conjugate g = J :=
  HopfIdeal.exists_conjugate_eq_of_isBorelOverAlgClosed _
    (isBorelCandidate_definingHopfIdeal k)
    exists_conjugate_definingHopfIdeal_le_of_isBorelOverAlgClosed hI hJ

end

end TauCeti.SpecialLinear.Borel
