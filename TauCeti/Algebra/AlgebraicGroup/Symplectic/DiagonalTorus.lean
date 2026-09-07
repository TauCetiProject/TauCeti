/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.DiagonalTorus.Basic
public import TauCeti.Algebra.AlgebraicGroup.Symplectic.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.Symplectic.RootSubgroup
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Diagonal

/-!
# The diagonal torus of the symplectic group scheme

This file promotes the diagonal symplectic matrices

```text
diag(t₀, …, tₘ₋₁, t₀⁻¹, …, tₘ₋₁⁻¹)
```

to a morphism from the rank-`m` split torus to `Sp₂ₘ` over an arbitrary commutative base
ring. The construction is made simultaneously in the functor-of-points, coordinate-Hopf-algebra,
and affine-group-scheme models. On algebra-valued points it is injective, natural in the value
algebra, and conjugates each symplectic root subgroup through its standard root character.

This is the torus and pinning-equation part of the standard type-`C` pinning. It does not yet claim
that the morphism is a closed immersion or that its image is maximal; those statements require the
coordinate-surjectivity and root-datum work that remain in Layer 9.

## Main definitions

* `TauCeti.Symplectic.diagonalTorusPoints`: the diagonal-torus homomorphism on algebra-valued
  points.
* `TauCeti.Symplectic.diagonalTorusCoordinateMap`: the corresponding coordinate Hopf-algebra map.
* `TauCeti.Symplectic.diagonalTorus`: the group-scheme morphism from the split torus to `Sp₂ₘ`.

## Main results

* `TauCeti.Symplectic.pointsMulEquiv_diagonalTorusPoints`: the point map is the standard diagonal
  symplectic matrix.
* `TauCeti.Symplectic.diagonalTorusPoints_injective` and
  `TauCeti.Symplectic.mapValue_diagonalTorusPoints`: injectivity and naturality.
* `TauCeti.Symplectic.diagonalTorusPoints_mul_rootSubgroupPoints_mul_inv`: the pinning equation on
  every root subgroup.
* `TauCeti.Symplectic.coordinateMap_comp_diagonalTorusCoordinateMap_X_castAdd`,
  `TauCeti.Symplectic.coordinateMap_comp_diagonalTorusCoordinateMap_X_addNat`, and
  `TauCeti.Symplectic.coordinateMap_comp_diagonalTorusCoordinateMap_X_of_ne`: the coordinate-map
  formulas on ambient generic matrix entries.
* `TauCeti.Symplectic.diagonalTorusCoordinateMap_baseChange`: compatibility with scalar extension.
* `TauCeti.Symplectic.schemePointsMulEquiv_diagonalTorus` and
  `TauCeti.Symplectic.schemePointsMulEquiv_diagonalTorus_mul_rootSubgroup_mul_inv`: the
  scheme-valued action and pinning equation.

## References

* J. S. Milne, *Algebraic Groups* (2017), §23 and §24.6.
* J. E. Humphreys, *Linear Algebraic Groups* (1975), §26.3.
* The points-map, natural-transformation, coordinate-morphism, and relative-spectrum
  constructions follow the formal template in
  `TauCeti.Algebra.AlgebraicGroup.GeneralLinear.DiagonalTorus.Basic`.

This advances the pinnings and root-subgroup-map targets of Layer 9 in
`TauCetiRoadmap/ReductiveGroups/README.md`. The resulting type-`C` pinning is consumed by milestone
L0, "pinned ambient groups", of `TauCetiRoadmap/CFSGStatement/README.md` for the `Cₙ(q)` family.
-/

public section

open AlgebraicGeometry CategoryTheory WithConv
open scoped CategoryTheory.MonObj

namespace TauCeti.Symplectic

universe u v w

variable {R : Type u} [CommRing R] {m : ℕ}

section Points

variable {A : Type w} [CommRing A] [Algebra R A]

/-- **The diagonal torus of `Sp₂ₘ` on algebra-valued points.** Under the split-torus and
symplectic points equivalences it is the standard diagonal matrix with paired inverse entries. -/
noncomputable def diagonalTorusPoints :
    WithConv (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin m) →₀ ℤ)) →ₐ[R] A) →*
      WithConv (coordinateHopfAlgebra R m →ₐ[R] A) :=
  (pointsMulEquiv (R := R) (A := A) m).symm.toMonoidHom.comp
    (GLSymplecticFin.diagonal.comp
      ((GeneralLinear.diagonalTorusCoordinates (N := m) (A := A)).comp
        (SplitTorus.pointsMulEquiv (R := R) (A := A)).toMonoidHom))

/-- Reading a diagonal-torus point as a symplectic matrix gives the standard diagonal matrix. -/
theorem pointsMulEquiv_diagonalTorusPoints
    (t : WithConv (MonoidAlgebra R
      (Multiplicative (ULift.{u} (Fin m) →₀ ℤ)) →ₐ[R] A)) :
    pointsMulEquiv (R := R) (A := A) m (diagonalTorusPoints t) =
      GLSymplecticFin.diagonal
        (GeneralLinear.diagonalTorusCoordinates (SplitTorus.pointsMulEquiv t)) := by
  simp [diagonalTorusPoints]

/-- The diagonal-torus homomorphism into symplectic points is injective. -/
theorem diagonalTorusPoints_injective :
    Function.Injective (diagonalTorusPoints (R := R) (m := m) (A := A)) := by
  intro s t h
  apply (SplitTorus.pointsMulEquiv (R := R) (A := A)).injective
  have hc :
      GeneralLinear.diagonalTorusCoordinates (SplitTorus.pointsMulEquiv s) =
        GeneralLinear.diagonalTorusCoordinates (SplitTorus.pointsMulEquiv t) := by
    apply GLSymplecticFin.diagonal_injective
    rw [← pointsMulEquiv_diagonalTorusPoints, ← pointsMulEquiv_diagonalTorusPoints, h]
  funext i
  simpa only [GeneralLinear.diagonalTorusCoordinates_apply, ULift.up_down] using
    congrFun hc i.down

variable {B : Type v} [CommRing B] [Algebra R B]

/-- The symplectic diagonal-torus map is natural in the value algebra. -/
theorem mapValue_diagonalTorusPoints (f : A →ₐ[R] B)
    (t : WithConv (MonoidAlgebra R
      (Multiplicative (ULift.{u} (Fin m) →₀ ℤ)) →ₐ[R] A)) :
    AlgHom.mapValue (H := coordinateHopfAlgebra R m) f (diagonalTorusPoints t) =
      diagonalTorusPoints
        (AlgHom.mapValue
          (H := MonoidAlgebra R (Multiplicative (ULift.{u} (Fin m) →₀ ℤ))) f t) := by
  apply (pointsMulEquiv (R := R) (A := B) m).injective
  rw [pointsMulEquiv_mapValue, pointsMulEquiv_diagonalTorusPoints,
    pointsMulEquiv_diagonalTorusPoints, GLSymplecticFin.map_diagonal]
  congr 1
  funext i
  rw [GeneralLinear.diagonalTorusCoordinates_apply,
    GeneralLinear.diagonalTorusCoordinates_apply]
  change Units.map f.toRingHom (SplitTorus.pointsMulEquiv t (ULift.up i)) =
    SplitTorus.pointsMulEquiv (AlgHom.mapValue f t) (ULift.up i)
  exact (SplitTorus.pointsMulEquiv_mapValue f t (ULift.up i)).symm

/-- **The symplectic pinning equation on algebra-valued points.** Conjugation by a diagonal-torus
point scales the parameter of every standard root subgroup by its root character. -/
theorem diagonalTorusPoints_mul_rootSubgroupPoints_mul_inv
    (root : GLSymplecticFin.RootSubgroupIndex m)
    (t : WithConv (MonoidAlgebra R
      (Multiplicative (ULift.{u} (Fin m) →₀ ℤ)) →ₐ[R] A))
    (c : WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A)) :
    diagonalTorusPoints t * rootSubgroupPoints root c * (diagonalTorusPoints t)⁻¹ =
      rootSubgroupPoints root
        ((AdditiveGroup.gaPointsMulEquiv (R := R) (A := A)).symm <|
          Multiplicative.ofAdd
            (((root.character
                (GeneralLinear.diagonalTorusCoordinates (SplitTorus.pointsMulEquiv t)) : Aˣ) : A) *
              Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv c))) := by
  apply (pointsMulEquiv (R := R) (A := A) m).injective
  rw [map_mul, map_mul, map_inv, pointsMulEquiv_diagonalTorusPoints,
    pointsMulEquiv_rootSubgroupPoints, pointsMulEquiv_rootSubgroupPoints,
    MulEquiv.apply_symm_apply]
  exact GLSymplecticFin.diagonal_mul_rootSubgroup_mul_inv root
    (GeneralLinear.diagonalTorusCoordinates (SplitTorus.pointsMulEquiv t))
    (AdditiveGroup.gaPointsMulEquiv c)

end Points

section Functor

/-- The natural transformation of group-valued points defined by the symplectic diagonal torus. -/
noncomputable def diagonalTorusPointsMap :
    HopfAlgebra.pointsFunctor
        (R := R)
        (H := MonoidAlgebra R (Multiplicative (ULift.{u} (Fin m) →₀ ℤ))) ⟶
      HopfAlgebra.pointsFunctor (R := R) (H := coordinateHopfAlgebra R m) where
  app A := GrpCat.ofHom (diagonalTorusPoints (A := A))
  naturality _ _ f := by
    ext t
    exact (mapValue_diagonalTorusPoints f.hom t).symm

/-- The component of the natural diagonal-torus map is `diagonalTorusPoints`. -/
@[simp]
theorem diagonalTorusPointsMap_app (A : CommAlgCat.{w} R) :
    (diagonalTorusPointsMap (R := R) (m := m)).app A =
      GrpCat.ofHom diagonalTorusPoints :=
  (rfl)

end Functor

section Scheme

/-- The coordinate morphism of the symplectic diagonal torus, recovered from its natural action
on points. Its direction is opposite to the represented group-scheme morphism. -/
noncomputable def diagonalTorusCoordinateMap :
    coordinateHopfAlgebra R m ⟶
      _root_.CommHopfAlgCat.of R
        (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin m) →₀ ℤ))) :=
  CommHopfAlgCat.homOfPointsMap
    (diagonalTorusPointsMap.{u, u} (R := R) (m := m))

/-- Precomposition by the coordinate morphism is the natural point map already constructed. -/
theorem mapPointsFunctor_diagonalTorusCoordinateMap :
    (CommHopfAlgCat.mapPointsFunctor.{u, u, u}
      (diagonalTorusCoordinateMap (R := R) (m := m)) :
      HopfAlgebra.pointsFunctor
          (R := R)
          (H := MonoidAlgebra R (Multiplicative (ULift.{u} (Fin m) →₀ ℤ))) ⟶
        HopfAlgebra.pointsFunctor (R := R) (H := coordinateHopfAlgebra R m)) =
      (diagonalTorusPointsMap.{u, u} (R := R) (m := m) :
        HopfAlgebra.pointsFunctor
            (R := R)
            (H := MonoidAlgebra R (Multiplicative (ULift.{u} (Fin m) →₀ ℤ))) ⟶
          HopfAlgebra.pointsFunctor (R := R) (H := coordinateHopfAlgebra R m)) :=
  CommHopfAlgCat.mapPointsFunctor_homOfPointsMap _

/-- On every value algebra, the coordinate morphism induces `diagonalTorusPoints`. -/
@[simp]
theorem mapPointsFunctor_diagonalTorusCoordinateMap_app
    (A : CommAlgCat.{w} R)
    (t : HopfAlgebra.points
      (R := R)
      (H := MonoidAlgebra R (Multiplicative (ULift.{u} (Fin m) →₀ ℤ))) A) :
    (CommHopfAlgCat.mapPointsFunctor
      (diagonalTorusCoordinateMap (R := R) (m := m))).app A t =
      diagonalTorusPoints t := by
  let K := MonoidAlgebra R (Multiplicative (ULift.{u} (Fin m) →₀ ℤ))
  let p : WithConv (K →ₐ[R] K) := toConv (AlgHom.id R K)
  have hp :
      (CommHopfAlgCat.mapPointsFunctor
        (diagonalTorusCoordinateMap (R := R) (m := m))).app (CommAlgCat.of R K) p =
        diagonalTorusPoints p := by
    rw [mapPointsFunctor_diagonalTorusCoordinateMap, diagonalTorusPointsMap_app]
    exact GrpCat.ofHom_apply diagonalTorusPoints p
  have htp : AlgHom.mapValue (H := K) t.ofConv p = t := by
    simp only [AlgHom.mapValue_apply, p, AlgHom.comp_id, WithConv.toConv_ofConv]
  have hnat :
      AlgHom.mapValue (H := coordinateHopfAlgebra R m) t.ofConv
          ((CommHopfAlgCat.mapPointsFunctor
            (diagonalTorusCoordinateMap (R := R) (m := m))).app (CommAlgCat.of R K) p) =
        (CommHopfAlgCat.mapPointsFunctor
          (diagonalTorusCoordinateMap (R := R) (m := m))).app A
            (AlgHom.mapValue (H := K) t.ofConv p) := by
    exact DFunLike.congr_fun
      (AlgHom.mapValue_mapDomain
        (diagonalTorusCoordinateMap (R := R) (m := m)).hom t.ofConv) p
  rw [← htp, ← hnat, hp, mapValue_diagonalTorusPoints]

private abbrev diagonalTorusCoordinateRing :=
  MonoidAlgebra R (Multiplicative (ULift.{u} (Fin m) →₀ ℤ))

private noncomputable def diagonalTorusGenericMatrix :
    Matrix (Fin (m + m)) (Fin (m + m)) (diagonalTorusCoordinateRing (R := R) (m := m)) :=
  ((GLSymplecticFin.diagonal
      (GeneralLinear.diagonalTorusCoordinates
        (SplitTorus.pointsMulEquiv
          (toConv (AlgHom.id R (diagonalTorusCoordinateRing (R := R) (m := m)))))) :
      GLSymplecticFin m (diagonalTorusCoordinateRing (R := R) (m := m))) :
    GL (Fin (m + m)) (diagonalTorusCoordinateRing (R := R) (m := m)))

private theorem diagonalTorusCoordinateMap_ambient_X_eq_entry (i j : Fin (m + m)) :
    (diagonalTorusCoordinateMap (R := R) (m := m)).hom
        ((coordinateMap R m).hom
          (GeneralLinear.coordinateHopfAlgebraAlgEquiv R (m + m)
            (GeneralLinear.coordinateRingMap R (m + m) (MvPolynomial.X (i, j))))) =
      diagonalTorusGenericMatrix (R := R) (m := m) i j := by
  let K := MonoidAlgebra R (Multiplicative (ULift.{u} (Fin m) →₀ ℤ))
  let p : WithConv (K →ₐ[R] K) := toConv (AlgHom.id R K)
  have hpoints := mapPointsFunctor_diagonalTorusCoordinateMap_app
    (R := R) (m := m) (CommAlgCat.of R K) p
  have heval := congrArg
    (fun q : WithConv (coordinateHopfAlgebra R m →ₐ[R] K) ↦ q.ofConv
      ((coordinateMap R m).hom
        (GeneralLinear.coordinateHopfAlgebraAlgEquiv R (m + m)
          (GeneralLinear.coordinateRingMap R (m + m) (MvPolynomial.X (i, j)))))) hpoints
  rw [CommHopfAlgCat.mapPointsFunctor_app_apply_apply] at heval
  rw [coordinateMap_def, CommHopfAlgCat.mkQuotient_apply] at heval
  have hcoe := pointsMulEquiv_coe (R := R) (A := K) m (diagonalTorusPoints p)
  have hentry := congrArg (fun g : GL (Fin (m + m)) K ↦ g i j) hcoe
  rw [GeneralLinear.pointsMulEquiv_apply, GeneralLinear.pointToGeneralLinear_apply] at hentry
  rw [CommHopfAlgCat.quotientPointsHom_apply_apply] at hentry
  have hdiag := congrArg
    (fun g : GLSymplecticFin m K ↦ ((g : GL (Fin (m + m)) K) :
      Matrix (Fin (m + m)) (Fin (m + m)) K) i j)
    (pointsMulEquiv_diagonalTorusPoints p)
  rw [coordinateMap_def, CommHopfAlgCat.mkQuotient_apply]
  simpa only [diagonalTorusGenericMatrix, diagonalTorusCoordinateRing, AlgHom.id_apply, p, K]
    using
    heval.trans (hentry.trans hdiag)

/-- The first-block diagonal generic entry restricts to its corresponding torus character. -/
@[simp]
theorem coordinateMap_comp_diagonalTorusCoordinateMap_X_castAdd (i : Fin m) :
    (diagonalTorusCoordinateMap (R := R) (m := m)).hom
        ((coordinateMap R m).hom
          (GeneralLinear.coordinateHopfAlgebraAlgEquiv R (m + m)
            (GeneralLinear.coordinateRingMap R (m + m)
              (MvPolynomial.X (Fin.castAdd m i, Fin.castAdd m i))))) =
      MonoidAlgebra.single
        (Multiplicative.ofAdd (Finsupp.single (ULift.up i) 1)) 1 := by
  rw [diagonalTorusCoordinateMap_ambient_X_eq_entry]
  simp [diagonalTorusGenericMatrix, GeneralLinear.diagonalTorusCoordinates_apply]

/-- The second-block diagonal generic entry restricts to the inverse torus character. -/
@[simp]
theorem coordinateMap_comp_diagonalTorusCoordinateMap_X_addNat (i : Fin m) :
    (diagonalTorusCoordinateMap (R := R) (m := m)).hom
        ((coordinateMap R m).hom
          (GeneralLinear.coordinateHopfAlgebraAlgEquiv R (m + m)
            (GeneralLinear.coordinateRingMap R (m + m)
              (MvPolynomial.X (i.addNat m, i.addNat m))))) =
      MonoidAlgebra.single
        (Multiplicative.ofAdd (Finsupp.single (ULift.up i) (-1))) 1 := by
  rw [diagonalTorusCoordinateMap_ambient_X_eq_entry]
  rw [diagonalTorusGenericMatrix, GLSymplecticFin.coe_diagonal, diagGL_apply]
  simp only [↓reduceIte]
  rw [GLSymplecticFin.diagonalCoordinates_addNat,
    GeneralLinear.diagonalTorusCoordinates_apply]
  rw [SplitTorus.pointsMulEquiv_eq_freeAbelianCharEquiv, freeAbelianCharEquiv_apply,
    DiagonalizableGroup.pointsMulEquiv_apply,
    DiagonalizableGroup.charOfPoint_apply_inv_coe]
  simp only [AlgHom.id_apply, Int.reduceNeg, Finsupp.single_neg, ofAdd_neg]

/-- Every off-diagonal ambient generic matrix entry restricts to zero on the diagonal torus. -/
@[simp]
theorem coordinateMap_comp_diagonalTorusCoordinateMap_X_of_ne
    (i j : Fin (m + m)) (hij : i ≠ j) :
    (diagonalTorusCoordinateMap (R := R) (m := m)).hom
        ((coordinateMap R m).hom
          (GeneralLinear.coordinateHopfAlgebraAlgEquiv R (m + m)
            (GeneralLinear.coordinateRingMap R (m + m) (MvPolynomial.X (i, j))))) = 0 := by
  rw [diagonalTorusCoordinateMap_ambient_X_eq_entry]
  simp [diagonalTorusGenericMatrix, GLSymplecticFin.coe_diagonal, diagGL_apply, hij]

/-- **The symplectic diagonal-torus coordinate morphism commutes with base change.** -/
theorem diagonalTorusCoordinateMap_baseChange
    (R K : Type u) [CommRing R] [CommRing K] [Algebra R K] :
    (coordinateHopfAlgebraBaseChangeIso R K m).inv ≫
        CommHopfAlgCat.baseChangeMap (diagonalTorusCoordinateMap (R := R) (m := m)) ≫
        (DiagonalizableGroup.baseChangeCoordinateHopfAlgebraIso R K
          (SplitTorus.characterGroup (ULift.{u} (Fin m)))).hom =
      diagonalTorusCoordinateMap (R := K) (m := m) := by
  let eSp := coordinateHopfAlgebraBaseChangeIso R K m
  let eGL := GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K (m + m)
  let eT := DiagonalizableGroup.baseChangeCoordinateHopfAlgebraIso R K
    (SplitTorus.characterGroup (ULift.{u} (Fin m)))
  have hpre :
      coordinateMap K m ≫ eSp.inv =
        eGL.inv ≫ CommHopfAlgCat.baseChangeMap (coordinateMap R m) := by
    apply (cancel_mono eSp.hom).mp
    simp only [Category.assoc]
    rw [baseChangeMap_coordinateMap_comp_coordinateHopfAlgebraBaseChangeIso_hom]
    simp
  apply CommHopfAlgCat.mkQuotient_hom_ext
  rw [← coordinateMap_def K m]
  change coordinateMap K m ≫
      (eSp.inv ≫ CommHopfAlgCat.baseChangeMap
        (diagonalTorusCoordinateMap (R := R) (m := m)) ≫ eT.hom) =
    coordinateMap K m ≫ diagonalTorusCoordinateMap (R := K) (m := m)
  rw [← Category.assoc, hpre, Category.assoc]
  rw [← Category.assoc (CommHopfAlgCat.baseChangeMap (coordinateMap R m))
    (CommHopfAlgCat.baseChangeMap (diagonalTorusCoordinateMap (R := R) (m := m))) eT.hom]
  rw [← (CommHopfAlgCat.baseChangeFunctor (K := K)).map_comp]
  apply _root_.CommHopfAlgCat.hom_ext
  apply GeneralLinear.coordinateHopfAlgebra_bialgHom_ext K (m + m)
  intro i j
  rw [GeneralLinear.coordinateHopfAlgebraBaseChangeMap_X]
  obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective i
  · obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective j
    all_goals simp only [_root_.CommHopfAlgCat.hom_comp, BialgHom.coe_comp,
      Function.comp_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
      Fin.natAdd_eq_addNat]
    · by_cases hij : i = j
      · subst j
        rw [coordinateMap_comp_diagonalTorusCoordinateMap_X_castAdd,
          coordinateMap_comp_diagonalTorusCoordinateMap_X_castAdd,
          DiagonalizableGroup.baseChangeCoordinateHopfAlgebraIso_hom_apply]
        simp
      · have hne : Fin.castAdd m i ≠ Fin.castAdd m j := by
          exact fun h ↦ hij (Fin.castAdd_injective m m h)
        rw [coordinateMap_comp_diagonalTorusCoordinateMap_X_of_ne _ _ hne,
          coordinateMap_comp_diagonalTorusCoordinateMap_X_of_ne _ _ hne,
          DiagonalizableGroup.baseChangeCoordinateHopfAlgebraIso_hom_apply]
        simp
    · have hne : Fin.castAdd m i ≠ j.addNat m := by
        simpa only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
          Fin.natAdd_eq_addNat] using GLSymplecticFin.finSumFinEquiv_inl_ne_inr i j
      rw [coordinateMap_comp_diagonalTorusCoordinateMap_X_of_ne _ _ hne,
        coordinateMap_comp_diagonalTorusCoordinateMap_X_of_ne _ _ hne,
        DiagonalizableGroup.baseChangeCoordinateHopfAlgebraIso_hom_apply]
      simp
  · obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective j
    all_goals simp only [_root_.CommHopfAlgCat.hom_comp, BialgHom.coe_comp,
      Function.comp_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
      Fin.natAdd_eq_addNat]
    · have hne : i.addNat m ≠ Fin.castAdd m j := by
        simpa only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
          Fin.natAdd_eq_addNat] using GLSymplecticFin.finSumFinEquiv_inr_ne_inl i j
      rw [coordinateMap_comp_diagonalTorusCoordinateMap_X_of_ne _ _ hne,
        coordinateMap_comp_diagonalTorusCoordinateMap_X_of_ne _ _ hne,
        DiagonalizableGroup.baseChangeCoordinateHopfAlgebraIso_hom_apply]
      simp
    · by_cases hij : i = j
      · subst j
        rw [coordinateMap_comp_diagonalTorusCoordinateMap_X_addNat,
          coordinateMap_comp_diagonalTorusCoordinateMap_X_addNat,
          DiagonalizableGroup.baseChangeCoordinateHopfAlgebraIso_hom_apply]
        simp
      · have hne : i.addNat m ≠ j.addNat m := by
          exact fun h ↦ hij ((Fin.addNat_inj m).mp h)
        rw [coordinateMap_comp_diagonalTorusCoordinateMap_X_of_ne _ _ hne,
          coordinateMap_comp_diagonalTorusCoordinateMap_X_of_ne _ _ hne,
          DiagonalizableGroup.baseChangeCoordinateHopfAlgebraIso_hom_apply]
        simp

/-- **The diagonal torus of `Sp₂ₘ` as a group-scheme morphism** from the rank-`m` split
torus. -/
noncomputable def diagonalTorus :
    SplitTorus.groupScheme R (ULift.{u} (Fin m)) ⟶ groupScheme R m :=
  eqToHom
      (DiagonalizableGroup.groupScheme_def R
        (SplitTorus.characterGroup (ULift.{u} (Fin m)))) ≫
    (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
      (diagonalTorusCoordinateMap (R := R) (m := m)).op ≫
    eqToHom (groupScheme_def R m).symm

/-- The diagonal torus is relative spectrum applied contravariantly to its coordinate morphism,
transported across the named presentations of the split torus and symplectic group. -/
theorem diagonalTorus_def :
    diagonalTorus (R := R) (m := m) =
      eqToHom
          (DiagonalizableGroup.groupScheme_def R
            (SplitTorus.characterGroup (ULift.{u} (Fin m)))) ≫
        (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
          (diagonalTorusCoordinateMap (R := R) (m := m)).op ≫
        eqToHom (groupScheme_def R m).symm :=
  (rfl)

section SchemePoints

variable (A : Type u) [CommRing A] [Algebra R A]

private lemma groupSchemePointMulEquiv_comp_diagonalTorus
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (SplitTorus.groupScheme R (ULift.{u} (Fin m))).X) :
    p ≫ (diagonalTorus (R := R) (m := m)).hom.hom =
      groupSchemePointMulEquiv m A
        (diagonalTorusPoints
          (DiagonalizableGroup.groupSchemePointsMulEquiv (R := R) (A := A)
            (SplitTorus.characterGroup (ULift.{u} (Fin m))) p)) := by
  let q := DiagonalizableGroup.groupSchemePointsMulEquiv (R := R) (A := A)
    (SplitTorus.characterGroup (ULift.{u} (Fin m))) p
  have hmap : AlgebraicGeometry.Spec.mapMulEquiv
      ((CommHopfAlgCat.mapPointsFunctor
        (diagonalTorusCoordinateMap (R := R) (m := m))).app (CommAlgCat.of R A) q) =
      AlgebraicGeometry.Spec.mapMulEquiv q ≫
        ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
          (diagonalTorusCoordinateMap (R := R) (m := m)).op).hom.hom :=
    CommHopfAlgCat.mapMulEquiv_mapDomain (CommAlgCat.of R A)
      (diagonalTorusCoordinateMap (R := R) (m := m)).hom q
  rw [mapPointsFunctor_diagonalTorusCoordinateMap_app] at hmap
  apply Over.OverMorphism.ext
  rw [groupSchemePointMulEquiv_apply_left, Over.comp_left]
  unfold diagonalTorus
  rw [show ((eqToHom (DiagonalizableGroup.groupScheme_def R
        (SplitTorus.characterGroup (ULift.{u} (Fin m)))) ≫
        (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
          (diagonalTorusCoordinateMap (R := R) (m := m)).op ≫
        eqToHom (groupScheme_def R m).symm)).hom.hom.left =
      (eqToHom (DiagonalizableGroup.groupScheme_def R
        (SplitTorus.characterGroup (ULift.{u} (Fin m))))).hom.hom.left ≫
        ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
          (diagonalTorusCoordinateMap (R := R) (m := m)).op).hom.hom.left ≫
        (eqToHom (groupScheme_def R m).symm).hom.hom.left from rfl]
  rw [DiagonalizableGroup.eqToHom_hom_hom_left, DiagonalizableGroup.eqToHom_hom_hom_left]
  change p.left ≫ eqToHom (DiagonalizableGroup.groupScheme_X_left R
      (SplitTorus.characterGroup (ULift.{u} (Fin m)))) ≫
      ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
        (diagonalTorusCoordinateMap (R := R) (m := m)).op).hom.hom.left ≫
      eqToHom (groupScheme_X_left R m).symm =
    (AlgebraicGeometry.Spec.mapMulEquiv (diagonalTorusPoints q)).left ≫
      eqToHom (groupScheme_X_left R m).symm
  rw [← Category.assoc p.left,
    DiagonalizableGroup.groupSchemePointsMulEquiv_apply_left_comp]
  change Spec.map (CommRingCat.ofHom q.ofConv.toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (diagonalTorusCoordinateMap (R := R) (m := m)).hom.toAlgHom.toRingHom) ≫
      eqToHom (groupScheme_X_left R m).symm =
    Spec.map (CommRingCat.ofHom (diagonalTorusPoints q).ofConv.toRingHom) ≫
      eqToHom (groupScheme_X_left R m).symm
  have hmapLeft :
      (AlgebraicGeometry.Spec.mapMulEquiv (diagonalTorusPoints q)).left =
        (AlgebraicGeometry.Spec.mapMulEquiv q).left ≫
          ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
            (diagonalTorusCoordinateMap (R := R) (m := m)).op).hom.hom.left :=
    congrArg Over.Hom.left hmap
  change Spec.map (CommRingCat.ofHom (diagonalTorusPoints q).ofConv.toRingHom) =
    Spec.map (CommRingCat.ofHom q.ofConv.toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (diagonalTorusCoordinateMap (R := R) (m := m)).hom.toAlgHom.toRingHom) at hmapLeft
  rw [← Category.assoc, ← hmapLeft]

/-- **The symplectic diagonal torus on scheme-valued points** is the standard paired diagonal
matrix. -/
-- Not `@[simp]`: the reducible symplectic `groupScheme` target prevents this statement from being
-- in simp normal form.
theorem schemePointsMulEquiv_diagonalTorus
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (SplitTorus.groupScheme R (ULift.{u} (Fin m))).X) :
    schemePointsMulEquiv m A (p ≫ (diagonalTorus (R := R) (m := m)).hom.hom) =
      GLSymplecticFin.diagonal
        (GeneralLinear.diagonalTorusCoordinates
          (SplitTorus.schemePointsMulEquiv (R := R) (A := A) p)) := by
  let q := DiagonalizableGroup.groupSchemePointsMulEquiv (R := R) (A := A)
    (SplitTorus.characterGroup (ULift.{u} (Fin m))) p
  have hSp : schemePointsMulEquiv m A
      (groupSchemePointMulEquiv m A (diagonalTorusPoints q)) =
      pointsMulEquiv (R := R) (A := A) m (diagonalTorusPoints q) := by
    rw [schemePointsMulEquiv_groupSchemePointMulEquiv]
  have hTorus : SplitTorus.schemePointsMulEquiv (R := R) (A := A) p =
      SplitTorus.pointsMulEquiv q := by
    ext i
    exact (SplitTorus.schemePointsMulEquiv_apply_coe p i).trans
      (SplitTorus.pointsMulEquiv_apply_coe q i).symm
  rw [groupSchemePointMulEquiv_comp_diagonalTorus, hSp, hTorus,
    pointsMulEquiv_diagonalTorusPoints]

/-- **The symplectic pinning equation on scheme-valued points.** Conjugating a root-subgroup
point by a diagonal-torus point scales its additive parameter by the corresponding root
character. -/
theorem schemePointsMulEquiv_diagonalTorus_mul_rootSubgroup_mul_inv
    (root : GLSymplecticFin.RootSubgroupIndex m)
    (t : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (SplitTorus.groupScheme R (ULift.{u} (Fin m))).X)
    (c : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (AdditiveGroup.groupScheme R).X) :
    schemePointsMulEquiv m A (t ≫ (diagonalTorus (R := R) (m := m)).hom.hom) *
        schemePointsMulEquiv m A (c ≫ (rootSubgroup root).hom.hom) *
          (schemePointsMulEquiv m A
            (t ≫ (diagonalTorus (R := R) (m := m)).hom.hom))⁻¹ =
      schemePointsMulEquiv m A
        (AdditiveGroup.groupSchemePointMulEquiv A
          ((AdditiveGroup.gaPointsMulEquiv (R := R) (A := A)).symm <|
            Multiplicative.ofAdd
              (((root.character
                  (GeneralLinear.diagonalTorusCoordinates
                    (SplitTorus.schemePointsMulEquiv (R := R) (A := A) t)) : Aˣ) : A) *
                Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A c))) ≫
          (rootSubgroup root).hom.hom) := by
  rw [schemePointsMulEquiv_diagonalTorus, schemePointsMulEquiv_rootSubgroup,
    schemePointsMulEquiv_rootSubgroup,
    AdditiveGroup.schemePointsMulEquiv_groupSchemePointMulEquiv,
    MulEquiv.apply_symm_apply]
  exact GLSymplecticFin.diagonal_mul_rootSubgroup_mul_inv root
    (GeneralLinear.diagonalTorusCoordinates
      (SplitTorus.schemePointsMulEquiv (R := R) (A := A) t))
    (AdditiveGroup.schemePointsMulEquiv A c)

end SchemePoints

end Scheme

end TauCeti.Symplectic
