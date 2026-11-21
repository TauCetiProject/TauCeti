/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Datum
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.MultiplicativeMatrix

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
The Hopf-operation formulas use `TauCeti.Algebra.AlgebraicGroup.GeneralLinear.MultiplicativeMatrix`.
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

/-- The scheme underlying the group scheme is the spectrum of its integral coordinate algebra. -/
theorem groupScheme_X_left :
    D.groupScheme.X.left = Spec (CommRingCat.of D.coordinateHopfAlgebra) :=
  hopfSpec_obj_X_left _ _

/-- The universal matrix of the datum, obtained from the universal general-linear matrix
by the defining quotient map. -/
def coordinateMatrix : Matrix (Fin D.dim) (Fin D.dim) D.coordinateHopfAlgebra :=
  (GeneralLinear.genericMatrix ℤ D.dim).map
    (Ideal.Quotient.mkₐ ℤ _)

/-- The universal matrix is the image of the general-linear generic matrix in the quotient. -/
theorem coordinateMatrix_def :
    D.coordinateMatrix = (GeneralLinear.genericMatrix ℤ D.dim).map (Ideal.Quotient.mkₐ ℤ _) :=
  (rfl)

/-- The universal Chevalley matrix has invertible determinant. -/
theorem isUnit_det_coordinateMatrix : IsUnit D.coordinateMatrix.det := by
  rw [coordinateMatrix_def, ← AlgHom.mapMatrix_apply, ← AlgHom.map_det]
  exact (GeneralLinear.isUnit_det_genericMatrix ℤ D.dim).map (Ideal.Quotient.mkₐ ℤ _)

/-- Algebra maps out of the Chevalley coordinate algebra agree if their matrices agree. -/
theorem coordinateHopfAlgebra_algHom_ext {S : Type*} [Semiring S] [Algebra ℤ S]
    {f g : D.coordinateHopfAlgebra →ₐ[ℤ] S}
    (h : D.coordinateMatrix.map f = D.coordinateMatrix.map g) : f = g := by
  apply Ideal.Quotient.algHom_ext ℤ
  apply GeneralLinear.coordinateHopfAlgebra_algHom_ext
  intro i j
  simpa only [coordinateMatrix_def, Matrix.map_apply, GeneralLinear.genericMatrix_apply,
    AlgHom.comp_apply] using congrFun (congrFun h i) j

/-- The counit sends the universal Chevalley matrix to the identity. -/
@[simp↓]
theorem map_counit_coordinateMatrix :
    D.coordinateMatrix.map (Bialgebra.counitAlgHom ℤ D.coordinateHopfAlgebra) = 1 := by
  rw [coordinateMatrix_def, Matrix.map_map, ← Bialgebra.Quotient.mkBialgHom_toAlgHom]
  exact GeneralLinear.map_counit_map_genericMatrix _

/-- Comultiplication on the universal Chevalley matrix is matrix multiplication of its two
copies in the tensor square. -/
@[simp↓]
theorem map_comul_coordinateMatrix :
    D.coordinateMatrix.map (Bialgebra.comulAlgHom ℤ D.coordinateHopfAlgebra) =
      D.coordinateMatrix.map (Algebra.TensorProduct.includeLeft (R := ℤ) (S := ℤ)) *
        D.coordinateMatrix.map (Algebra.TensorProduct.includeRight (R := ℤ)) := by
  rw [coordinateMatrix_def, Matrix.map_map, ← Bialgebra.Quotient.mkBialgHom_toAlgHom]
  exact GeneralLinear.map_comul_map_genericMatrix _

/-- The antipode sends the universal Chevalley matrix to its inverse. -/
@[simp↓]
theorem map_antipode_coordinateMatrix :
    D.coordinateMatrix.map (HopfAlgebra.antipodeAlgHom (R := ℤ) (A := D.coordinateHopfAlgebra)) =
      D.coordinateMatrix⁻¹ := by
  rw [coordinateMatrix_def, ← GeneralLinear.map_inv_genericMatrix,
    ← GeneralLinear.map_antipode_genericMatrix, ← Bialgebra.Quotient.mkBialgHom_toAlgHom]
  ext i j
  simp only [Matrix.map_apply, HopfAlgebra.antipodeAlgHom_apply, BialgHom.coe_toAlgHom,
    BialgHomClass.map_antipode]

/-- Evaluation of the universal matrix gives the matrix of the corresponding point. -/
theorem map_coordinateMatrix {A : Type*} [CommRing A] [Algebra ℤ A]
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
