/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Datum

/-!
# The coordinate algebra and universal matrix of a Chevalley datum

The integral coordinate Hopf algebra is the quotient defining the datum's toral closure.
Its universal matrix evaluates to the matrix of a point under the existing
`GeneralLinear.IntegralPointsPresentation.mulEquiv`. In particular, polynomial conditions on
matrix entries can be imposed directly on the coordinate algebra, without replacing the
scheme by its field-valued points.

The construction uses the quotient presentation of the Kostant toral closure and the
matrix-point equivalence in
`TauCeti.Algebra.AlgebraicGroup.GeneralLinear.HopfIdealPoints.Presentation`.
-/

public section

open AlgebraicGeometry CategoryTheory WithConv

namespace TauCeti.DynkinType.ChevalleyDatum

noncomputable section

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

/-- The integral coordinate Hopf algebra of the group scheme of a Chevalley datum. -/
abbrev coordinateHopfAlgebra : _root_.CommHopfAlgCat ℤ :=
  CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ D.dim)
    (UniversalEnvelopingAlgebra.kostantToralDefiningIdeal (t.lieBasis ht).rootGenerator
      (t.lieBasis ht).h D.representation D.lattice D.representation_mem_lattice
      D.isNilpotent_representation_rootGenerator D.basis D.coordinateWeight)

/-- The underlying group scheme is the spectrum of its integral coordinate algebra. -/
theorem groupScheme_X_left :
    D.groupScheme.X.left = Spec (CommRingCat.of D.coordinateHopfAlgebra) :=
  hopfSpec_obj_X_left _ _

/-- The universal matrix of the datum, obtained from the universal general-linear matrix
by the defining quotient map. -/
def coordinateMatrix : Matrix (Fin D.dim) (Fin D.dim) D.coordinateHopfAlgebra :=
  (GeneralLinear.genericMatrix ℤ D.dim).map
    (Ideal.Quotient.mkₐ ℤ _)

/-- Evaluation of the universal matrix gives the matrix of the corresponding point. -/
@[simp]
theorem map_coordinateMatrix {A : Type*} [CommRing A]
    (f : D.coordinateHopfAlgebra →ₐ[ℤ] A) :
    D.coordinateMatrix.map f =
      (((D.pointsPresentation A).mulEquiv (A := CommAlgCat.of ℤ A) (toConv f)).val :
        Matrix (Fin D.dim) (Fin D.dim) A) := by
  rw [GeneralLinear.IntegralPointsPresentation.coe_mulEquiv_apply]
  ext i j
  simp only [coordinateMatrix, Matrix.map_apply, GeneralLinear.pointsMulEquiv_apply,
    GeneralLinear.pointToGeneralLinear_apply, GeneralLinear.genericMatrix_apply]
  exact (CommHopfAlgCat.quotientPointsHom_apply_apply _ _ (CommAlgCat.of ℤ A)
    (toConv f) _).symm

end

end TauCeti.DynkinType.ChevalleyDatum
