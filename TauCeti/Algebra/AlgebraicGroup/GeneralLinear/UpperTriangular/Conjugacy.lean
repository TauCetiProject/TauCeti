/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.StandardComodule
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.UpperTriangular.SmoothConnected
import TauCeti.Algebra.AlgebraicGroup.Solvable.LieKolchin
import TauCeti.Algebra.AlgebraicGroup.Solvable.UpperTriangular
public import TauCeti.Algebra.AlgebraicGroup.Borel.Conjugation
import TauCeti.Algebra.AlgebraicGroup.Borel.Existence
import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.ChangeBasis

/-!
# Triangularization of connected solvable closed subgroups of `GLₙ`

Over an algebraically closed field, a reduced connected solvable closed subgroup of `GLₙ`
is contained in a rational conjugate of the upper-triangular subgroup scheme. Applying
Lie–Kolchin to the restricted standard comodule triangularizes the generic matrix, so
the result is containment of closed subgroup schemes over every value algebra.

For Borel subgroups, maximality upgrades this containment to equality.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §17.6 and §21.

The generic-point argument follows the diagonalization construction in
`TauCeti.Algebra.AlgebraicGroup.GeneralLinear.DiagonalTorus.Conjugacy`.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.GeneralLinear

universe u

noncomputable section

variable {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}

attribute [local instance] standardComodule

/-- A matrix-valued point given by a bialgebra morphism from `O(GLₙ)` into a reduced,
connected, solvable Hopf algebra of finite type is triangularized by a rational matrix. -/
theorem exists_mul_map_eq_map_mul_upperTriangular
    {Q : Type u} [CommRing Q] [HopfAlgebra k Q] [Algebra.FiniteType k Q]
    [IsReduced Q]
    (hconn : geometricallyConnectedCommHopfAlgProperty k (_root_.CommHopfAlgCat.of k Q))
    (hsolv : geometricallySolvablePointsCommHopfAlgProperty k (_root_.CommHopfAlgCat.of k Q))
    (π : coordinateHopfAlgebra k n →ₐc[k] Q) :
    ∃ (P : GL (Fin n) k) (U : upperTriangularGroup (Fin n) Q),
      pointsMulEquiv n (toConv π.toAlgHom) *
          Matrix.GeneralLinearGroup.map (algebraMap k Q) P =
        Matrix.GeneralLinearGroup.map (algebraMap k Q) P * U := by
  let _ : Comodule k Q (Fin n → k) := Comodule.Corestrict π.toCoalgHom
  obtain ⟨m, b, hb, -⟩ :=
    Comodule.exists_basis_coefficientMatrix_isUpperTriangular_of_geometricallySolvable
      (k := k) (H := Q) (M := Fin n → k) hconn hsolv
  have hm : m = n := by
    simpa using (Module.finrank_eq_card_basis b).symm
  subst m
  let _ := (Pi.basisFun k (Fin n)).invertibleToMatrix b
  let U := Matrix.GeneralLinearGroup.mk'' (Comodule.coefficientMatrix (C := Q) b)
    (Comodule.isUnit_det_coefficientMatrix b)
  refine ⟨unitOfInvertible ((Pi.basisFun k (Fin n)).toMatrix b),
    ⟨U, UpperTriangularGroup.mem_iff.mpr hb⟩, ?_⟩
  have h := Module.Basis.coefficientMatrix_mul_toMatrix (C := Q) (Pi.basisFun k (Fin n)) b
  rw [Comodule.coefficientMatrix_corestrict, coefficientMatrix_basisFun] at h
  ext i j
  simpa only [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.map_apply,
    val_unitOfInvertible, Matrix.GeneralLinearGroup.val_mk'', U,
    pointsMulEquiv_apply, pointToGeneralLinear_apply, genericMatrix_apply,
    Matrix.mul_apply, Matrix.map_apply, BialgHom.toCoalgHom_apply,
    BialgHom.coe_toAlgHom, ofConv_toConv] using congrFun (congrFun h i) j

/-- A smooth connected solvable closed subgroup of `GLₙ` over an algebraically closed field
is contained in a rational conjugate of the upper-triangular subgroup scheme. -/
theorem exists_conjugate_upperTriangularDefiningHopfIdeal_le
    (I : HopfIdeal k (coordinateHopfAlgebra k n))
    (hI : HopfIdeal.IsBorelCandidate k
      (FiniteTypeCommHopfAlgCat.of k (coordinateHopfAlgebra k n)) I) :
    ∃ g : WithConv (coordinateHopfAlgebra k n →ₐ[k] k),
      (UpperTriangular.definingHopfIdeal k n).conjugate g ≤ I := by
  let Q := CommHopfAlgCat.quotient (coordinateHopfAlgebra k n) I
  let π : coordinateHopfAlgebra k n →ₐc[k] Q := (CommHopfAlgCat.mkQuotient _ I).hom
  let _ : IsReduced Q :=
    ((smoothCommHopfAlgProperty_iff_geometricallyReduced k _).mp hI.smooth).isReduced
  obtain ⟨P, U, hmat⟩ := exists_mul_map_eq_map_mul_upperTriangular
    hI.geometricallyConnected hI.geometricallySolvable π
  let g : WithConv (coordinateHopfAlgebra k n →ₐ[k] k) :=
    (pointsMulEquiv (R := k) (A := k) n).symm P⁻¹
  let f := π.toAlgHom.comp (HopfAlgebra.pointConjugationAlgHom g)
  have hkey : pointsMulEquiv n (toConv f) = U := by
    rw [HopfAlgebra.comp_pointConjugationAlgHom, map_mul, map_mul, map_inv,
      pointsMulEquiv_mapValue, MulEquiv.apply_symm_apply, map_inv, inv_inv,
      mul_assoc, inv_mul_eq_iff_eq_mul]
    exact hmat
  have hker := UpperTriangular.definingHopfIdeal_toIdeal_le_ker_of_isUpperTriangular
    k n f (by
      rw [← pointsMulEquiv_apply, hkey]
      exact UpperTriangularGroup.isUpperTriangular U)
  have hle : UpperTriangular.definingHopfIdeal k n ≤ I.conjugate g := by
    intro x hx
    rw [HopfIdeal.mem_conjugate, ← HopfIdeal.mem_toIdeal,
      ← CommHopfAlgCat.mkQuotient_eq_zero_iff]
    exact hker hx
  exact ⟨g⁻¹, by simpa using HopfIdeal.conjugate_mono g⁻¹ hle⟩

/-- Every Borel subgroup of `GLₙ` over an algebraically closed field is a rational conjugate
of the upper-triangular subgroup scheme. -/
theorem exists_eq_conjugate_upperTriangularDefiningHopfIdeal_of_isBorelOverAlgClosed
    {I : HopfIdeal k (coordinateHopfAlgebra k n)}
    (hI : HopfIdeal.IsBorelOverAlgClosed k
      (FiniteTypeCommHopfAlgCat.of k (coordinateHopfAlgebra k n)) I) :
    ∃ g : WithConv (coordinateHopfAlgebra k n →ₐ[k] k),
      I = (UpperTriangular.definingHopfIdeal k n).conjugate g := by
  have hmin := ((HopfIdeal.isBorelOverAlgClosed_iff k
    (FiniteTypeCommHopfAlgCat.of k (coordinateHopfAlgebra k n)) I).mp hI).2
  obtain ⟨g, hg⟩ := exists_conjugate_upperTriangularDefiningHopfIdeal_le I hmin.prop
  have hB : HopfIdeal.IsBorelCandidate k
      (FiniteTypeCommHopfAlgCat.of k (coordinateHopfAlgebra k n))
      (UpperTriangular.definingHopfIdeal k n) :=
    .mk (UpperTriangular.smoothCommHopfAlgProperty_coordinateHopfAlgebra n k)
      (UpperTriangular.geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra n k)
      (UpperTriangular.geometricallySolvablePointsCommHopfAlgProperty_coordinateHopfAlgebra k n)
  exact ⟨g, le_antisymm (hmin.le_of_le (hB.conjugate g) hg) hg⟩

/-- The upper-triangular subgroup scheme of `GLₙ` is a Borel subgroup over an algebraically
closed field, in every rank (including rank zero). -/
theorem UpperTriangular.isBorelOverAlgClosed_definingHopfIdeal :
    HopfIdeal.IsBorelOverAlgClosed k
      (FiniteTypeCommHopfAlgCat.of k (GeneralLinear.coordinateHopfAlgebra k n))
      (definingHopfIdeal k n) := by
  obtain ⟨I, hI⟩ := HopfIdeal.exists_minimal_isBorelCandidate
    (FiniteTypeCommHopfAlgCat.of k (GeneralLinear.coordinateHopfAlgebra k n))
  have hIB : HopfIdeal.IsBorelOverAlgClosed k
      (FiniteTypeCommHopfAlgCat.of k (GeneralLinear.coordinateHopfAlgebra k n)) I :=
    (HopfIdeal.isBorelOverAlgClosed_iff k _ I).mpr ⟨inferInstance, hI⟩
  obtain ⟨g, hg⟩ :=
    exists_eq_conjugate_upperTriangularDefiningHopfIdeal_of_isBorelOverAlgClosed hIB
  simpa only [hg, HopfIdeal.conjugate_inv_conjugate] using hIB.conjugate g⁻¹

/-- Over an algebraically closed field the Borel subgroups of `GLₙ` are exactly the rational
conjugates of the upper-triangular subgroup scheme. -/
theorem isBorelOverAlgClosed_iff_exists_eq_conjugate_upperTriangularDefiningHopfIdeal
    (I : HopfIdeal k (coordinateHopfAlgebra k n)) :
    HopfIdeal.IsBorelOverAlgClosed k
        (FiniteTypeCommHopfAlgCat.of k (coordinateHopfAlgebra k n)) I ↔
      ∃ g : WithConv (coordinateHopfAlgebra k n →ₐ[k] k),
        I = (UpperTriangular.definingHopfIdeal k n).conjugate g := by
  constructor
  · exact exists_eq_conjugate_upperTriangularDefiningHopfIdeal_of_isBorelOverAlgClosed
  · rintro ⟨g, rfl⟩
    exact UpperTriangular.isBorelOverAlgClosed_definingHopfIdeal.conjugate g

/-- Any two Borel subgroups of `GLₙ` over an algebraically closed field are conjugate by a
rational point. The equality is scheme-theoretic, expressed through defining Hopf ideals. -/
theorem exists_conjugate_eq_of_isBorelOverAlgClosed
    {I J : HopfIdeal k (coordinateHopfAlgebra k n)}
    (hI : HopfIdeal.IsBorelOverAlgClosed k
      (FiniteTypeCommHopfAlgCat.of k (coordinateHopfAlgebra k n)) I)
    (hJ : HopfIdeal.IsBorelOverAlgClosed k
      (FiniteTypeCommHopfAlgCat.of k (coordinateHopfAlgebra k n)) J) :
    ∃ g : WithConv (coordinateHopfAlgebra k n →ₐ[k] k), I.conjugate g = J := by
  obtain ⟨g, rfl⟩ :=
    exists_eq_conjugate_upperTriangularDefiningHopfIdeal_of_isBorelOverAlgClosed hI
  obtain ⟨h, rfl⟩ :=
    exists_eq_conjugate_upperTriangularDefiningHopfIdeal_of_isBorelOverAlgClosed hJ
  exact ⟨h * g⁻¹, by simp [HopfIdeal.conjugate_mul]⟩

end

end TauCeti.GeneralLinear
