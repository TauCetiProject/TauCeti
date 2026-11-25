/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Symplectic.Pinning.Antidiagonal.Basic

/-!
# Points of the torus and Borel subgroup of the antidiagonal symplectic pinning

The pinning `TauCeti.Symplectic.antidiagPinning` of the subgroup scheme preserving the antidiagonal
alternating form `Q = TauCeti.JAntidiag m R` is the standard pinning of `Sp₂ₘ` transported along
conjugation by the signed permutation `P = TauCeti.antidiagCongr m R`, with `P Q Pᵀ = JFin m R`.
On algebra-valued points, the transport sends a matrix `M` preserving `JFin` to `P⁻¹ M P`
(`TauCeti.Symplectic.constantFormPinning_torus_points`,
`TauCeti.Symplectic.mem_quotientPointsSubgroup_constantFormPinning_borel_iff`). This file computes
the points of the transported torus and Borel subgroup as matrices:

* the torus point of `t = (t₁, …, t_m)` is `diag(t₁, …, t_m, t_m⁻¹, …, t₁⁻¹)`, the diagonal torus
  `diag(t₁, …, t_m, t₁⁻¹, …, t_m⁻¹)` of the `JFin` model with its entries in flag order
  (`TauCeti.Symplectic.antidiagPinning_torus_points`);
* a point of the group preserving `Q` lies in the Borel subgroup exactly when its matrix is upper
  triangular (`TauCeti.Symplectic.mem_quotientPointsSubgroup_antidiagPinning_borel_iff`).

So over every connected nontrivial ring this is the pinning with the diagonal torus and the upper
triangular Borel subgroup, the convention for the symplectic group of the antidiagonal form used
by Cai, Friedberg and Kaplan.

## References

* B. Conrad, *Reductive Group Schemes* (2014), §5.1, for transporting pinnings.
* Y. Cai, S. Friedberg, E. Kaplan, *Doubling constructions: local and global theory, with an
  application to global functoriality for non-generic cuspidal representations*, Ann. of Math.
  §1, for `Sp₂ₘ` defined by the antidiagonal form with its diagonal torus and upper triangular
  Borel subgroup.
-/

public section

open CategoryTheory Matrix

namespace TauCeti.Symplectic

open GLSymplecticFin.IsotropicFlag

universe u v

variable (R : Type u) [CommRing R] [Nontrivial R] [ConnectedSpace (PrimeSpectrum R)] (m : ℕ)

/-- **The torus of the antidiagonal pinning on points.** The point of the transported torus given
by `t = (t₁, …, t_m)` has matrix `diag(t₁, …, t_m, t_m⁻¹, …, t₁⁻¹)`: the symplectic diagonal
coordinates `(t₁, …, t_m, t₁⁻¹, …, t_m⁻¹)` read in the flag order. -/
theorem antidiagPinning_torus_points (A : Type v) [CommRing A] [Algebra R A]
    (t : HopfAlgebra.points (R := R)
      (H := MonoidAlgebra R (Multiplicative (ULift.{u} (Fin m) →₀ ℤ))) (CommAlgCat.of R A)) :
    ((GeneralLinear.pointsMulEquiv (m + m)
        ((CommHopfAlgCat.Hom.mapPointsFunctor
          (ConstantForm.coordinateMap R (m + m) (JAntidiag m R))).app (CommAlgCat.of R A)
          ((CommHopfAlgCat.Hom.mapPointsFunctor (antidiagPinning R m).torus.coordinateMap).app
            (CommAlgCat.of R A) t)) : GL (Fin (m + m)) A) :
        Matrix (Fin (m + m)) (Fin (m + m)) A) =
      diagonal fun k ↦ (GLSymplecticFin.diagonalCoordinates
        (GeneralLinear.diagonalTorusCoordinates (SplitTorus.pointsMulEquiv t)) (flagOrder m k) :
          A) := by
  rw [constantFormPinning_torus_points, map_antidiagCongr]
  exact antidiagCongr_inv_mul_diagonal_mul _

/-- **The Borel subgroup of the antidiagonal pinning on points.** A point of the subgroup scheme
preserving the antidiagonal form lies in the transported Borel subgroup exactly when its matrix
is upper triangular. -/
theorem mem_quotientPointsSubgroup_antidiagPinning_borel_iff (A : Type v) [CommRing A]
    [Algebra R A]
    (f : HopfAlgebra.points (R := R)
      (H := ConstantForm.coordinateHopfAlgebra R (m + m) (JAntidiag m R)) (CommAlgCat.of R A)) :
    f ∈ CommHopfAlgCat.quotientPointsSubgroup
        (ConstantForm.coordinateHopfAlgebra R (m + m) (JAntidiag m R)) (antidiagPinning R m).borel
        (CommAlgCat.of R A) ↔
      ((GeneralLinear.pointsMulEquiv (m + m)
        ((CommHopfAlgCat.Hom.mapPointsFunctor
          (ConstantForm.coordinateMap R (m + m) (JAntidiag m R))).app (CommAlgCat.of R A) f) :
          GL (Fin (m + m)) A) : Matrix (Fin (m + m)) (Fin (m + m)) A).BlockTriangular id := by
  rw [mem_quotientPointsSubgroup_constantFormPinning_borel_iff, map_antidiagCongr]
  suffices ∀ M : Matrix (Fin (m + m)) (Fin (m + m)) A,
      (∀ i j, flagOrder m j < flagOrder m i →
        ((antidiagCongr m A : Matrix (Fin (m + m)) (Fin (m + m)) A) * M *
          (((antidiagCongr m A)⁻¹ : GL (Fin (m + m)) A) :
            Matrix (Fin (m + m)) (Fin (m + m)) A)) i j = 0) ↔ M.BlockTriangular id from this _
  intro M
  have h := blockTriangular_antidiagCongr_inv_mul_mul_iff
    ((antidiagCongr m A : Matrix (Fin (m + m)) (Fin (m + m)) A) * M *
      (((antidiagCongr m A)⁻¹ : GL (Fin (m + m)) A) : Matrix (Fin (m + m)) (Fin (m + m)) A))
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one,
    Units.inv_mul_cancel_left] at h
  rw [h]
  constructor
  · intro h a b hab
    exact h _ _ (by rwa [flagOrder_flagOrder, flagOrder_flagOrder])
  · intro h i j hij
    simpa only [submatrix_apply, flagOrder_flagOrder] using @h (flagOrder m i) (flagOrder m j) hij

end TauCeti.Symplectic
