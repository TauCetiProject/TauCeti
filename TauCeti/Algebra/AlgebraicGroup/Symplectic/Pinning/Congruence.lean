/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.ConstantForm.Congruence.Basic
public import TauCeti.Algebra.AlgebraicGroup.Pinning.Isomorphism
public import TauCeti.Algebra.AlgebraicGroup.Symplectic.Pinning.Basic

/-!
# The symplectic group of another Gram matrix

The carrier of `Sp₂ₘ` is the constant-form subgroup scheme of `TauCeti.JFin m R`. Another
alternating Gram matrix `C` that is congruent to it, `P C Pᵀ = JFin m R` for an invertible
matrix `P`, gives the same group: conjugation by `P` is an isomorphism from
`ConstantForm.groupScheme R (m + m) C` onto `Sp₂ₘ` (`TauCeti.ConstantForm.groupSchemeCongr`).
Since `Sp₂ₘ` and its coordinate Hopf algebra are abbreviations for the constant-form ones, that
isomorphism and its coordinate version `TauCeti.ConstantForm.coordinateHopfAlgebraCongr` apply
directly with `C' = JFin m R`; so does the smoothness transfer
`TauCeti.ConstantForm.smooth_of_congr`, with the smoothness of `Sp₂ₘ`. This file records the
pinning transported along them from the standard pinning of `Sp₂ₘ` by
`TauCeti.Pinning.comapOfIso`.

## Main declarations

* `TauCeti.Symplectic.constantFormPinning`: the standard pinning of `Sp₂ₘ` transported to the
  subgroup scheme preserving `C`.
* `TauCeti.Symplectic.constantFormPinning_torus_points`: on points, the transported torus point
  of `t = (t₁, …, t_m)` has matrix `P⁻¹ diag(t₁, …, t_m, t₁⁻¹, …, t_m⁻¹) P`.
* `TauCeti.Symplectic.mem_quotientPointsSubgroup_constantFormPinning_borel_iff`: a point with
  matrix `M` lies in the transported Borel subgroup exactly when `P M P⁻¹` preserves the isotropic
  flag, that is, vanishes below the diagonal in the flag order.

## References

* J. S. Milne, *Algebraic Groups* (2017), 2.10.
* B. Conrad, *Reductive Group Schemes* (2014), §5.1, for transporting pinnings.
-/

public section

open CategoryTheory Matrix

namespace TauCeti.Symplectic

universe u v

variable {R : Type u} [CommRing R] {m : ℕ} {C : Matrix (Fin (m + m)) (Fin (m + m)) R}

/-- **The transported pinning.** For a Gram matrix `C` with `P C Pᵀ = JFin m R`, the standard
pinning of `Sp₂ₘ` pulled back along `TauCeti.ConstantForm.coordinateHopfAlgebraCongr`: its torus
and Borel subgroup are the conjugates by `P⁻¹` of the diagonal torus and the isotropic-flag
Borel subgroup of `Sp₂ₘ`. The smoothness instance it needs holds by
`TauCeti.ConstantForm.smooth_of_congr`. -/
noncomputable def constantFormPinning [Nontrivial R] [ConnectedSpace (PrimeSpectrum R)]
    [Algebra.Smooth R (ConstantForm.coordinateHopfAlgebra R (m + m) C)] (P : GL (Fin (m + m)) R)
    (hP : (P : Matrix (Fin (m + m)) (Fin (m + m)) R) * C *
      (P : Matrix (Fin (m + m)) (Fin (m + m)) R)ᵀ = JFin m R) :
    Pinning R (ConstantForm.coordinateHopfAlgebra R (m + m) C) m :=
  (standardPinning R m).comapOfIso (ConstantForm.coordinateHopfAlgebraCongr P hP)

/-- The torus of the transported pinning is the pullback of the diagonal torus of `Sp₂ₘ`. -/
@[simp]
theorem constantFormPinning_torus [Nontrivial R] [ConnectedSpace (PrimeSpectrum R)]
    [Algebra.Smooth R (ConstantForm.coordinateHopfAlgebra R (m + m) C)] (P : GL (Fin (m + m)) R)
    (hP : (P : Matrix (Fin (m + m)) (Fin (m + m)) R) * C *
      (P : Matrix (Fin (m + m)) (Fin (m + m)) R)ᵀ = JFin m R) :
    (constantFormPinning P hP).torus =
      (splitMaximalTorus R m).comapOfIso (ConstantForm.coordinateHopfAlgebraCongr P hP) := by
  rw [constantFormPinning, Pinning.comapOfIso_torus, standardPinning_torus]

/-- The Borel subgroup of the transported pinning is the pullback of the isotropic-flag Borel
subgroup of `Sp₂ₘ`. -/
@[simp]
theorem constantFormPinning_borel [Nontrivial R] [ConnectedSpace (PrimeSpectrum R)]
    [Algebra.Smooth R (ConstantForm.coordinateHopfAlgebra R (m + m) C)] (P : GL (Fin (m + m)) R)
    (hP : (P : Matrix (Fin (m + m)) (Fin (m + m)) R) * C *
      (P : Matrix (Fin (m + m)) (Fin (m + m)) R)ᵀ = JFin m R) :
    (constantFormPinning P hP).borel =
      (IsotropicFlag.definingHopfIdeal R m).comapOfSurjective
        (ConstantForm.coordinateHopfAlgebraCongr P hP).hom.hom
        (ConcreteCategory.bijective_of_isIso
          (ConstantForm.coordinateHopfAlgebraCongr P hP).hom).2 := by
  rw [constantFormPinning, Pinning.comapOfIso_borel, standardPinning_borel]

/-- **The torus of the transported pinning on points.** The point of the transported torus given
by `t = (t₁, …, t_m)` has matrix `P⁻¹ diag(t₁, …, t_m, t₁⁻¹, …, t_m⁻¹) P`, the conjugate by `P⁻¹`
of the diagonal torus point of `Sp₂ₘ`, with `P` read in `A`. -/
theorem constantFormPinning_torus_points [Nontrivial R] [ConnectedSpace (PrimeSpectrum R)]
    [Algebra.Smooth R (ConstantForm.coordinateHopfAlgebra R (m + m) C)] (P : GL (Fin (m + m)) R)
    (hP : (P : Matrix (Fin (m + m)) (Fin (m + m)) R) * C *
      (P : Matrix (Fin (m + m)) (Fin (m + m)) R)ᵀ = JFin m R)
    (A : Type v) [CommRing A] [Algebra R A]
    (t : HopfAlgebra.points (R := R)
      (H := MonoidAlgebra R (Multiplicative (ULift.{u} (Fin m) →₀ ℤ))) (CommAlgCat.of R A)) :
    ((GeneralLinear.pointsMulEquiv (m + m)
        ((CommHopfAlgCat.Hom.mapPointsFunctor (ConstantForm.coordinateMap R (m + m) C)).app
          (CommAlgCat.of R A)
          ((CommHopfAlgCat.Hom.mapPointsFunctor (constantFormPinning P hP).torus.coordinateMap).app
            (CommAlgCat.of R A) t)) : GL (Fin (m + m)) A) : Matrix (Fin (m + m)) (Fin (m + m)) A) =
      (((GeneralLinearGroup.map (algebraMap R A) P)⁻¹ : GL (Fin (m + m)) A) :
          Matrix (Fin (m + m)) (Fin (m + m)) A) *
        diagonal (fun k ↦ (GLSymplecticFin.diagonalCoordinates
          (GeneralLinear.diagonalTorusCoordinates (SplitTorus.pointsMulEquiv t)) k : A)) *
        (GeneralLinearGroup.map (algebraMap R A) P : Matrix (Fin (m + m)) (Fin (m + m)) A) := by
  rw [constantFormPinning_torus, SplitMaximalTorus.comapOfIso_coordinateMap,
    CommHopfAlgCat.Hom.mapPointsFunctor_comp_app_apply]
  refine (congrArg (fun g : GL (Fin (m + m)) A ↦ (g : Matrix (Fin (m + m)) (Fin (m + m)) A))
    (ConstantForm.pointsMulEquiv_mapPointsFunctor_coordinateHopfAlgebraCongr P hP
      (CommAlgCat.of R A) _)).trans ?_
  rw [splitMaximalTorus_coordinateMap, mapPointsFunctor_diagonalTorusCoordinateMap_app,
    ConstantForm.mapPointsFunctor_coordinateMap_app, pointsMulEquiv_coe,
    pointsMulEquiv_diagonalTorusPoints]
  simp only [GLSymplecticFin.coe_diagonal, map_inv, inv_inv, Units.val_mul, diagGL_coe]

/-- **The Borel subgroup of the transported pinning on points.** A point of the subgroup scheme
preserving `C` with matrix `M` lies in the transported Borel subgroup exactly when `P M P⁻¹`, with
`P` read in `A`, preserves the isotropic flag: its entries vanish below the diagonal in the flag
order. -/
theorem mem_quotientPointsSubgroup_constantFormPinning_borel_iff [Nontrivial R]
    [ConnectedSpace (PrimeSpectrum R)]
    [Algebra.Smooth R (ConstantForm.coordinateHopfAlgebra R (m + m) C)] (P : GL (Fin (m + m)) R)
    (hP : (P : Matrix (Fin (m + m)) (Fin (m + m)) R) * C *
      (P : Matrix (Fin (m + m)) (Fin (m + m)) R)ᵀ = JFin m R)
    (A : Type v) [CommRing A] [Algebra R A]
    (f : HopfAlgebra.points (R := R)
      (H := ConstantForm.coordinateHopfAlgebra R (m + m) C) (CommAlgCat.of R A)) :
    f ∈ CommHopfAlgCat.quotientPointsSubgroup
        (ConstantForm.coordinateHopfAlgebra R (m + m) C) (constantFormPinning P hP).borel
        (CommAlgCat.of R A) ↔
      ∀ i j, GLSymplecticFin.IsotropicFlag.flagOrder m j <
          GLSymplecticFin.IsotropicFlag.flagOrder m i →
        ((GeneralLinearGroup.map (algebraMap R A) P : Matrix (Fin (m + m)) (Fin (m + m)) A) *
          (GeneralLinear.pointsMulEquiv (m + m)
            ((CommHopfAlgCat.Hom.mapPointsFunctor (ConstantForm.coordinateMap R (m + m) C)).app
              (CommAlgCat.of R A) f) : Matrix (Fin (m + m)) (Fin (m + m)) A) *
          (((GeneralLinearGroup.map (algebraMap R A) P)⁻¹ : GL (Fin (m + m)) A) :
            Matrix (Fin (m + m)) (Fin (m + m)) A)) i j = 0 := by
  set e := ConstantForm.coordinateHopfAlgebraCongr P hP
  rw [constantFormPinning_borel]
  -- Every point of the subgroup scheme preserving `C` comes from a point of `Sp₂ₘ` along `e`.
  obtain ⟨g, rfl⟩ : ∃ g : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R m)
      (CommAlgCat.of R A),
      (CommHopfAlgCat.Hom.mapPointsFunctor e.hom).app (CommAlgCat.of R A) g = f :=
    (CommHopfAlgCat.mapPointsFunctor_app_bijective_of_isIso e.hom (CommAlgCat.of R A)).2 f
  refine (BialgHom.mapDomain_mem_quotientPointsSubgroup_comapOfSurjective_iff e.hom.hom _ _ _
    g).trans ?_
  rw [IsotropicFlag.mem_definingPointsSubgroup_iff,
    GLSymplecticFin.IsotropicFlag.mem_matrixSubgroup_iff_flagOrder,
    ConstantForm.pointsMulEquiv_mapPointsFunctor_coordinateHopfAlgebraCongr,
    ConstantForm.mapPointsFunctor_coordinateMap_app, pointsMulEquiv_coe]
  simp only [map_inv, inv_inv, Units.val_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one,
    Units.mul_inv_cancel_left]

end TauCeti.Symplectic
