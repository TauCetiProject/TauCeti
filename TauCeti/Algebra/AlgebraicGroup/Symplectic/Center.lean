/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Center.Basic
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.Yoneda
public import TauCeti.Algebra.AlgebraicGroup.RootsOfUnity.Basic
public import TauCeti.Algebra.AlgebraicGroup.Symplectic.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Center

/-!
# The scheme-theoretic center of the symplectic group

In positive rank the center of `Sp₂ₘ` is `μ₂`. A square root of one acts by its scalar
matrix. The matrix-center calculation holds over every commutative value algebra, so
universal centrality identifies the full represented center, including its nonreduced
structure in characteristic two. Over a field we obtain an isomorphism of coordinate
Hopf algebras with the group algebra of `Multiplicative (ZMod 2)`.

This identifies the central subgroup used in forming the adjoint symplectic group.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapter 21, the classical semisimple groups.

The functor-of-points construction follows
`TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Center.Basic`, using the symplectic
matrix-center calculation and `RootsOfUnityGroup.pointsMulEquiv`. No division by two
or passage to reduced points occurs.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.Symplectic

universe u v w

noncomputable section

variable (m : ℕ)

/-- Send a `μ₂`-point to its scalar symplectic point. -/
def rootsOfUnityScalarPoints {R : Type u} [CommRing R]
    {A : Type v} [CommRing A] [Algebra R A] :
    WithConv (MonoidAlgebra R (Multiplicative (ZMod 2)) →ₐ[R] A) →*
      WithConv (coordinateHopfAlgebra R m →ₐ[R] A) :=
  (pointsMulEquiv R m (A := A)).symm.toMonoidHom.comp <|
    (GLSymplecticFin.rootsOfUnityScalar m).comp (RootsOfUnityGroup.pointsMulEquiv 2).toMonoidHom

/-- Scalar points correspond to scalar matrices under the symplectic points equivalence. -/
-- Apply before simplification reduces the bundled point types.
@[simp↓]
theorem pointsMulEquiv_rootsOfUnityScalarPoints {R : Type u} [CommRing R]
    {A : Type v} [CommRing A] [Algebra R A]
    (f : WithConv (MonoidAlgebra R (Multiplicative (ZMod 2)) →ₐ[R] A)) :
    pointsMulEquiv R m (A := A) (rootsOfUnityScalarPoints m f) =
      GLSymplecticFin.rootsOfUnityScalar m (RootsOfUnityGroup.pointsMulEquiv 2 f) := by
  simp [rootsOfUnityScalarPoints]

/-- Scalar symplectic points commute with change of value algebra. -/
theorem mapValue_rootsOfUnityScalarPoints {R : Type u} [CommRing R]
    {A : Type v} {B : Type w} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (φ : A →ₐ[R] B)
    (f : WithConv (MonoidAlgebra R (Multiplicative (ZMod 2)) →ₐ[R] A)) :
    AlgHom.mapValue φ (rootsOfUnityScalarPoints m f) =
      rootsOfUnityScalarPoints m (AlgHom.mapValue φ f) := by
  apply (pointsMulEquiv R m (A := B)).injective
  rw [pointsMulEquiv_mapValue, pointsMulEquiv_rootsOfUnityScalarPoints,
    pointsMulEquiv_rootsOfUnityScalarPoints]
  apply Subtype.ext
  apply Units.ext
  simp [GLSymplecticFin.coe_map, Matrix.GeneralLinearGroup.val_map_apply]

/-- Scalar square roots of one are universally central symplectic points. -/
theorem isCentralPoint_rootsOfUnityScalarPoints {R : Type u} [CommRing R]
    {A : Type v} [CommRing A] [Algebra R A]
    (f : WithConv (MonoidAlgebra R (Multiplicative (ZMod 2)) →ₐ[R] A)) :
    HopfAlgebra.IsCentralPoint (rootsOfUnityScalarPoints m f) := by
  rw [HopfAlgebra.isCentralPoint_def]
  intro B _ _ φ h
  apply (pointsMulEquiv R m (A := B)).injective
  rw [map_mul, map_mul, mapValue_rootsOfUnityScalarPoints,
    pointsMulEquiv_rootsOfUnityScalarPoints]
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, GLSymplecticFin.coe_rootsOfUnityScalar]
  exact (Matrix.scalar_commute _ (fun r ↦ Commute.all _ r) _).eq

variable {m}

/-- In positive rank distinct square roots of one give distinct scalar symplectic points. -/
theorem rootsOfUnityScalarPoints_injective (hm : m ≠ 0) {R : Type u} [CommRing R]
    {A : Type v} [CommRing A] [Algebra R A] :
    Function.Injective (rootsOfUnityScalarPoints (R := R) m (A := A)) := by
  intro f h he
  apply (RootsOfUnityGroup.pointsMulEquiv (R := R) (A := A) 2).injective
  apply Subtype.ext
  apply Units.ext
  have : Nonempty (Fin (m + m)) := ⟨⟨0, by omega⟩⟩
  have he' := congrArg (pointsMulEquiv R m (A := A)) he
  rw [pointsMulEquiv_rootsOfUnityScalarPoints, pointsMulEquiv_rootsOfUnityScalarPoints] at he'
  have hmat := congrArg (fun x : GLSymplecticFin m A ↦
    (x.val : Matrix (Fin (m + m)) (Fin (m + m)) A)) he'
  rw [GLSymplecticFin.coe_rootsOfUnityScalar, GLSymplecticFin.coe_rootsOfUnityScalar] at hmat
  exact Matrix.scalar_inj.mp hmat

/-- In positive rank every central symplectic point is a unique scalar square root of one.
The statement uses universal centrality, so it detects the scheme-theoretic center. -/
theorem isCentralPoint_iff_existsUnique_rootsOfUnityScalarPoints
    (hm : m ≠ 0) {R : Type u} [CommRing R]
    {A : Type v} [CommRing A] [Algebra R A]
    (g : WithConv (coordinateHopfAlgebra R m →ₐ[R] A)) :
    HopfAlgebra.IsCentralPoint g ↔ ∃! f, rootsOfUnityScalarPoints m f = g := by
  constructor
  · intro hg
    have hcenter := MulEquivClass.apply_mem_center (pointsMulEquiv R m (A := A))
      (HopfAlgebra.center_le_center (HopfAlgebra.mem_center.mpr hg))
    obtain ⟨c, hc, hc2⟩ := (GLSymplecticFin.mem_center_iff hm _).mp hcenter
    let ζ : rootsOfUnity 2 A :=
      ⟨Units.mkOfMulEqOne c c (by simpa [sq] using hc2),
        (mem_rootsOfUnity' 2 _).mpr hc2⟩
    have hf : rootsOfUnityScalarPoints m
        ((RootsOfUnityGroup.pointsMulEquiv (R := R) (A := A) 2).symm ζ) = g := by
      apply (pointsMulEquiv R m (A := A)).injective
      rw [pointsMulEquiv_rootsOfUnityScalarPoints, MulEquiv.apply_symm_apply]
      apply Subtype.ext
      apply Units.ext
      rw [GLSymplecticFin.coe_rootsOfUnityScalar]
      exact hc.symm
    exact ⟨_, hf, fun f hh ↦ rootsOfUnityScalarPoints_injective hm (hh.trans hf.symm)⟩
  · rintro ⟨f, rfl, -⟩
    exact isCentralPoint_rootsOfUnityScalarPoints m f

section RepresentedCenter

variable {k : Type u} [Field k]

private def scalarCenterHom (A : CommAlgCat.{u} k) :
    HopfAlgebra.points (R := k) (H := MonoidAlgebra k (Multiplicative (ZMod 2))) A →*
      CommHopfAlgCat.centerPointsSubgroup (coordinateHopfAlgebra k m) A :=
  (rootsOfUnityScalarPoints m).codRestrict _ fun f ↦
    (CommHopfAlgCat.mem_centerPointsSubgroup_iff _ _ _).mpr
      (isCentralPoint_rootsOfUnityScalarPoints m f)

private theorem scalarCenterHom_bijective (hm : m ≠ 0) (A : CommAlgCat.{u} k) :
    Function.Bijective (scalarCenterHom (m := m) A) := by
  constructor
  · intro f h he
    exact rootsOfUnityScalarPoints_injective hm (congrArg Subtype.val he)
  · intro g
    obtain ⟨f, hf, -⟩ := (isCentralPoint_iff_existsUnique_rootsOfUnityScalarPoints hm g.val).mp
      ((CommHopfAlgCat.mem_centerPointsSubgroup_iff _ _ _).mp g.property)
    exact ⟨f, Subtype.ext hf⟩

/-- Scalar square roots of one identify the `μ₂` point functor with the represented
center of the positive-rank symplectic group. -/
def rootsOfUnityScalarCenterNatIso (hm : m ≠ 0) :
    HopfAlgebra.pointsFunctor (R := k) (H := MonoidAlgebra k (Multiplicative (ZMod 2))) ≅
      CommHopfAlgCat.quotientPointsSubgroupFunctor (coordinateHopfAlgebra k m)
        (CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k m)) :=
  NatIso.ofComponents
    (fun A ↦ (MulEquiv.ofBijective (scalarCenterHom A)
      (scalarCenterHom_bijective hm A)).toGrpIso) (by
    intro A B φ
    ext f
    apply Subtype.ext
    -- These concrete categorical components are the codomain restrictions of the scalar map.
    change rootsOfUnityScalarPoints m (AlgHom.mapValue φ.hom f) =
      AlgHom.mapValue φ.hom (rootsOfUnityScalarPoints m f)
    exact (mapValue_rootsOfUnityScalarPoints m φ.hom f).symm)

/-- The natural center comparison sends a `μ₂`-point to its scalar symplectic point. -/
-- As for the symplectic points comparison, simplify before reducing the bundled types.
@[simp↓]
theorem rootsOfUnityScalarCenterNatIso_hom_app_apply (hm : m ≠ 0) (A : CommAlgCat.{u} k)
    (f : HopfAlgebra.points (R := k) (H := MonoidAlgebra k (Multiplicative (ZMod 2))) A) :
    (ConcreteCategory.hom
      (X := (HopfAlgebra.pointsFunctor (R := k)
        (H := MonoidAlgebra k (Multiplicative (ZMod 2)))).obj A)
      (Y := GrpCat.of (CommHopfAlgCat.centerPointsSubgroup (coordinateHopfAlgebra k m) A))
      ((rootsOfUnityScalarCenterNatIso hm).hom.app A) f).1 =
        rootsOfUnityScalarPoints m f := (rfl)

/-- The full center of `Sp₂ₘ` in positive rank is `μ₂`, as an isomorphism of coordinate
Hopf algebras. This includes characteristic two and nonreduced value algebras. -/
def centerCoordinateIsoGroupAlgebra (hm : m ≠ 0) :
    CommHopfAlgCat.quotient (coordinateHopfAlgebra k m)
        (CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k m)) ≅
      _root_.CommHopfAlgCat.of k (MonoidAlgebra k (Multiplicative (ZMod 2))) :=
  Iso.unop <| (Functor.FullyFaithful.ofFullyFaithful
    (CommHopfAlgCat.pointsFunctor (R := k))).preimageIso
      (rootsOfUnityScalarCenterNatIso hm ≪≫
        (CommHopfAlgCat.quotientPointsSubgroupNatIso (coordinateHopfAlgebra k m)
          (CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k m))).symm)

/-- The coordinate isomorphism represents the scalar-matrix comparison on points. -/
theorem pointsFunctor_mapIso_centerCoordinateIsoGroupAlgebra (hm : m ≠ 0) :
    (CommHopfAlgCat.pointsFunctor (R := k)).mapIso (centerCoordinateIsoGroupAlgebra hm).op =
      rootsOfUnityScalarCenterNatIso hm ≪≫
        (CommHopfAlgCat.quotientPointsSubgroupNatIso (coordinateHopfAlgebra k m)
          (CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k m))).symm := by
  apply Iso.ext
  exact (Functor.FullyFaithful.ofFullyFaithful
    (CommHopfAlgCat.pointsFunctor (R := k))).map_preimage _

end RepresentedCenter

end

end TauCeti.Symplectic
