/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Symplectic.Pinning.Antidiagonal

/-!
# Points of the torus and Borel subgroup of the antidiagonal symplectic pinning

The pinning `TauCeti.Symplectic.antidiagPinning` of the subgroup scheme preserving the antidiagonal
alternating form `Q = TauCeti.JAntidiag m R` is the standard pinning of `Sp₂ₘ` transported along
conjugation by the signed permutation `P = TauCeti.antidiagCongr m R`, with `P Q Pᵀ = JFin m R`.
On algebra-valued points, the transport sends a matrix `M` preserving `JFin` to `P⁻¹ M P`. This
file computes the points of the transported torus and Borel subgroup as matrices:

* the torus point of `t = (t₁, …, t_m)` is `diag(t₁, …, t_m, t_m⁻¹, …, t₁⁻¹)`, the diagonal torus
  `diag(t₁, …, t_m, t₁⁻¹, …, t_m⁻¹)` of the `JFin` model with its entries in flag order
  (`TauCeti.Symplectic.antidiagPinning_torus_points`);
* a point of the group preserving `Q` lies in the Borel subgroup exactly when its matrix is upper
  triangular (`TauCeti.Symplectic.mem_quotientPointsSubgroup_antidiagPinning_borel_iff`).

So over every connected nontrivial ring this is the pinning with the diagonal torus and the upper
triangular Borel subgroup, the convention for `J_{Sp₂ₘ}` of ReductiveGroups §9B.5.

## References

* B. Conrad, *Reductive Group Schemes* (2014), §5.1, for transporting pinnings.
-/

public section

open CategoryTheory Matrix

namespace TauCeti

open GLSymplecticFin.IsotropicFlag

variable {m : ℕ}

/-- The signs of the antidiagonal congruence are preserved by ring homomorphisms. -/
theorem map_antidiagSign {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (i : Fin (m + m)) : f (antidiagSign m R i) = antidiagSign m S i := by
  refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) i
  · simp
  · simp

/-- The signed permutation `antidiagCongr` is preserved by ring homomorphisms. -/
theorem map_antidiagCongr {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    GeneralLinearGroup.map f (antidiagCongr m R) = antidiagCongr m S := by
  apply Units.ext
  ext i j
  rw [GeneralLinearGroup.map_apply, coe_antidiagCongr, coe_antidiagCongr,
    antidiagCongrMatrix_apply, antidiagCongrMatrix_apply, apply_ite f, map_antidiagSign,
    map_zero]

namespace Symplectic

universe u v

variable (R : Type u) [CommRing R] [Nontrivial R] [ConnectedSpace (PrimeSpectrum R)] (m)

/-- **The torus of the antidiagonal pinning on points.** The point of the transported torus given
by `t = (t₁, …, t_m)` has matrix `diag(t₁, …, t_m, t_m⁻¹, …, t₁⁻¹)`: the symplectic diagonal
coordinates `(t₁, …, t_m, t₁⁻¹, …, t_m⁻¹)` read in the flag order. -/
theorem antidiagPinning_torus_points (A : CommAlgCat.{v} R)
    (t : HopfAlgebra.points (R := R)
      (H := MonoidAlgebra R (Multiplicative (ULift.{u} (Fin m) →₀ ℤ))) A) :
    ((GeneralLinear.pointsMulEquiv (m + m)
        ((CommHopfAlgCat.Hom.mapPointsFunctor
          (ConstantForm.coordinateMap R (m + m) (JAntidiag m R))).app A
          ((CommHopfAlgCat.Hom.mapPointsFunctor (antidiagPinning R m).torus.coordinateMap).app
            A t)) : GL (Fin (m + m)) A) : Matrix (Fin (m + m)) (Fin (m + m)) A) =
      diagonal fun k ↦ (GLSymplecticFin.diagonalCoordinates
        (GeneralLinear.diagonalTorusCoordinates (SplitTorus.pointsMulEquiv t)) (flagOrder m k) :
          A) := by
  rw [constantFormPinning_torus, SplitMaximalTorus.comapOfIso_coordinateMap,
    CommHopfAlgCat.Hom.mapPointsFunctor_comp_app_apply]
  refine (congrArg (fun g : GL (Fin (m + m)) A ↦ (g : Matrix (Fin (m + m)) (Fin (m + m)) A))
    (ConstantForm.pointsMulEquiv_mapPointsFunctor_coordinateHopfAlgebraCongr _
      antidiagCongr_mul_JAntidiag_mul_transpose A _)).trans ?_
  have ht := mapPointsFunctor_diagonalTorusCoordinateMap_app A t
  have hcoe := pointsMulEquiv_coe R m (A := A) (diagonalTorusPoints t)
  rw [CommHopfAlgCat.quotientPointsHom_apply, ← coordinateMap_def,
    ← CommHopfAlgCat.Hom.mapPointsFunctor_app_apply] at hcoe
  rw [splitMaximalTorus_coordinateMap, ht]
  erw [hcoe]
  rw [pointsMulEquiv_diagonalTorusPoints, GLSymplecticFin.coe_diagonal, map_inv, inv_inv,
    map_antidiagCongr, Units.val_mul, Units.val_mul, diagGL_coe]
  exact antidiagCongr_inv_mul_diagonal_mul _

/-- **The Borel subgroup of the antidiagonal pinning on points.** A point of the subgroup scheme
preserving the antidiagonal form lies in the transported Borel subgroup exactly when its matrix
is upper triangular. -/
theorem mem_quotientPointsSubgroup_antidiagPinning_borel_iff (A : CommAlgCat.{v} R)
    (f : HopfAlgebra.points (R := R)
      (H := ConstantForm.coordinateHopfAlgebra R (m + m) (JAntidiag m R)) A) :
    f ∈ CommHopfAlgCat.quotientPointsSubgroup
        (ConstantForm.coordinateHopfAlgebra R (m + m) (JAntidiag m R)) (antidiagPinning R m).borel
        A ↔
      ((GeneralLinear.pointsMulEquiv (m + m)
        ((CommHopfAlgCat.Hom.mapPointsFunctor
          (ConstantForm.coordinateMap R (m + m) (JAntidiag m R))).app A f) :
          GL (Fin (m + m)) A) : Matrix (Fin (m + m)) (Fin (m + m)) A).BlockTriangular id := by
  set e := ConstantForm.coordinateHopfAlgebraCongr (antidiagCongr m R)
    (antidiagCongr_mul_JAntidiag_mul_transpose (m := m) (R := R))
  obtain ⟨g, rfl⟩ : ∃ g : WithConv (coordinateHopfAlgebra R m →ₐ[R] A),
      (CommHopfAlgCat.Hom.mapPointsFunctor e.hom).app A g = f := by
    refine ⟨(CommHopfAlgCat.Hom.mapPointsFunctor e.inv).app A f, ?_⟩
    rw [← CommHopfAlgCat.Hom.mapPointsFunctor_comp_app_apply, e.hom_inv_id]
    simp
    rfl
  have hcoe := pointsMulEquiv_coe R m (A := A) g
  rw [CommHopfAlgCat.quotientPointsHom_apply, ← coordinateMap_def,
    ← CommHopfAlgCat.Hom.mapPointsFunctor_app_apply] at hcoe
  have hM := ConstantForm.pointsMulEquiv_mapPointsFunctor_coordinateHopfAlgebraCongr
    (antidiagCongr m R) antidiagCongr_mul_JAntidiag_mul_transpose A g
  rw [hM, constantFormPinning_borel]
  erw [hcoe]
  refine (BialgHom.mapDomain_mem_quotientPointsSubgroup_comapOfSurjective_iff e.hom.hom _ _ A
    g).trans ?_
  erw [IsotropicFlag.mem_definingPointsSubgroup_iff]
  rw [mem_matrixSubgroup_iff_flagOrder, map_inv, inv_inv, map_antidiagCongr, Units.val_mul,
    Units.val_mul, blockTriangular_antidiagCongr_inv_mul_mul_iff]
  constructor
  · intro h a b hab
    exact h _ _ (by rwa [flagOrder_flagOrder, flagOrder_flagOrder])
  · intro h i j hij
    simpa only [submatrix_apply, flagOrder_flagOrder] using @h (flagOrder m i) (flagOrder m j) hij

end Symplectic

end TauCeti
