/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Hopf.KernelPoints
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.DiagonalTorus.Basic
public import TauCeti.Algebra.AlgebraicGroup.Torus.Maximal
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Separation
import TauCeti.Algebra.AlgebraicGroup.Torus.SmoothConnected
import TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.FieldPoints
import TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.MaximalTorus

/-!
# Maximality of the diagonal torus in the special linear group

Over any field, the diagonal torus of `SL_{r+1}` is a maximal torus. Over an algebraically closed
field it is moreover maximal among reduced commutative closed subgroup schemes: a competing
subgroup need not be a torus, or even connected.

The defining Hopf ideal is the kernel of the surjective restriction morphism
`TauCeti.SpecialLinear.diagonalTorusCoordinateMap`, and its quotient is the coordinate Hopf algebra
of the rank-`r` split torus, whose points are exactly the points with diagonal matrix. Maximality
is proved on algebraically closed points. A reduced commutative closed subgroup containing the
diagonal torus has commutative point group containing all determinant-one diagonal matrices.
Transported into the standard type `A_r` carrier, the maximality of its weight torus among
commutative subgroups shows that every point of the subgroup is diagonal, and therefore already a
point of the torus. Reduced
finite-type point separation turns this equality of point groups into an equality of defining
Hopf ideals, and maximality over an arbitrary field descends from an algebraic closure.

## Main declarations

* `TauCeti.SpecialLinear.diagonalTorusDefiningIdeal`: the Hopf ideal cutting out the diagonal
  torus in `SL_{r+1}`.
* `TauCeti.SpecialLinear.diagonalTorusCoordinateIso`: its coordinate quotient is the Laurent
  coordinate Hopf algebra of the rank-`r` split torus.
* `TauCeti.SpecialLinear.splitTorusCommHopfAlgProperty_quotient_diagonalTorusDefiningIdeal`: that
  quotient is a split torus.
* `TauCeti.SpecialLinear.map_baseChangeHopfIdeal_diagonalTorusDefiningIdeal`: the defining ideal
  is compatible with scalar extension.
* `TauCeti.SpecialLinear.quotientPointsSubgroup_diagonalTorusDefiningIdeal`: its points are the
  range of the diagonal-torus point morphism.
* `TauCeti.SpecialLinear.mem_quotientPointsSubgroup_diagonalTorusDefiningIdeal_iff`: a point lies
  in the diagonal torus exactly when its matrix is diagonal.
* `TauCeti.SpecialLinear.eq_diagonalTorusDefiningIdeal_of_le_of_isCocomm`: over an algebraically
  closed field, no larger reduced commutative closed subgroup contains the diagonal torus.
* `TauCeti.SpecialLinear.isMaximalTorus_diagonalTorusDefiningIdeal`: **the diagonal torus of
  `SL_{r+1}` is a maximal torus**, over every field.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 17 and 21.
* J. E. Humphreys, *Linear Algebraic Groups* (1975), §§15.3 and 26.3.
* The Hopf-ideal organization and the point-subgroup comparison follow
  `TauCeti.Algebra.AlgebraicGroup.GeneralLinear.DiagonalTorus.Maximal` and
  `TauCeti.Algebra.AlgebraicGroup.Symplectic.DiagonalTorus.Maximal`, sharing with them the kernel
  quotient constructions `TauCeti.CommHopfAlgCat.quotientKerOfSurjectiveIso`,
  `TauCeti.CommHopfAlgCat.map_baseChangeHopfIdeal_kerOfSurjective` and
  `TauCeti.HopfIdeal.quotientPointsSubgroup_kerOfSurjective_eq_range_mapPointsFunctor`; the
  point-level maximality is
  `TauCeti.SlStd.eq_range_weightTorusPoints_of_le_of_isMulCommutative`, and the diagonal-point
  criterion follows `TauCeti.SlStd.range_weightTorusPoints_eq_diagonalPoints`.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.SpecialLinear

universe u

noncomputable section

variable (r : ℕ)

section CommRing

variable (R : Type u) [CommRing R]

/-- The Hopf ideal defining the diagonal torus inside the coordinate Hopf algebra of `SL_{r+1}`:
the kernel of restriction to the torus. -/
noncomputable def diagonalTorusDefiningIdeal : HopfIdeal R (coordinateHopfAlgebra R (r + 1)) :=
  HopfIdeal.kerOfSurjective (diagonalTorusCoordinateMap r R).hom
    (diagonalTorusCoordinateMap_surjective r R)

/-- A function belongs to the diagonal-torus ideal precisely when its restriction vanishes. -/
@[simp]
theorem mem_diagonalTorusDefiningIdeal (x : coordinateHopfAlgebra R (r + 1)) :
    x ∈ diagonalTorusDefiningIdeal r R ↔ (diagonalTorusCoordinateMap r R).hom x = 0 := by
  rw [diagonalTorusDefiningIdeal, HopfIdeal.mem_kerOfSurjective]

/-- The quotient by the diagonal-torus ideal is the Laurent coordinate Hopf algebra of the
rank-`r` split torus. -/
noncomputable def diagonalTorusCoordinateIso :
    FiniteTypeCommHopfAlgCat.quotient ⟨coordinateHopfAlgebra R (r + 1),
        (finiteTypeCommHopfAlgProperty_iff _).2 inferInstance⟩
        (diagonalTorusDefiningIdeal r R) ≅
      DiagonalizableGroup.coordinateRing R (SplitTorus.characterGroup (ULift.{u} (Fin r))) :=
  ObjectProperty.isoMk _ <|
    CommHopfAlgCat.quotientKerOfSurjectiveIso (diagonalTorusCoordinateMap r R)
      (diagonalTorusCoordinateMap_surjective r R)

/-- The quotient isomorphism identifies the quotient morphism with restriction to the torus. -/
@[simp]
theorem mkQuotient_comp_diagonalTorusCoordinateIso_hom :
    FiniteTypeCommHopfAlgCat.mkQuotient ⟨coordinateHopfAlgebra R (r + 1),
        (finiteTypeCommHopfAlgProperty_iff _).2 inferInstance⟩
          (diagonalTorusDefiningIdeal r R) ≫
        (diagonalTorusCoordinateIso r R).hom =
      ObjectProperty.homMk (diagonalTorusCoordinateMap r R) :=
  ObjectProperty.hom_ext _ (CommHopfAlgCat.mkQuotient_comp_quotientKerOfSurjectiveIso_hom _ _)

/-- The coordinate quotient defining the diagonal torus of `SL_{r+1}` is a split torus. -/
theorem splitTorusCommHopfAlgProperty_quotient_diagonalTorusDefiningIdeal :
    splitTorusCommHopfAlgProperty R
      (FiniteTypeCommHopfAlgCat.quotient ⟨coordinateHopfAlgebra R (r + 1),
        (finiteTypeCommHopfAlgProperty_iff _).2 inferInstance⟩
        (diagonalTorusDefiningIdeal r R)) := by
  rw [splitTorusCommHopfAlgProperty_iff]
  exact ⟨r, ⟨(diagonalTorusCoordinateIso r R).symm⟩⟩

grind_pattern splitTorusCommHopfAlgProperty_quotient_diagonalTorusDefiningIdeal =>
  diagonalTorusDefiningIdeal r R

/-- The base-change isomorphism of special-linear coordinate Hopf algebras carries the
base-changed diagonal-torus ideal onto the diagonal-torus ideal over the extended base. -/
@[simp]
theorem map_baseChangeHopfIdeal_diagonalTorusDefiningIdeal
    (K : Type u) [CommRing K] [Algebra R K] :
    (CommHopfAlgCat.baseChangeHopfIdeal (K := K) (diagonalTorusDefiningIdeal r R)).map
        (coordinateHopfAlgebraBaseChangeIso R K (r + 1)).hom.hom =
      diagonalTorusDefiningIdeal r K :=
  CommHopfAlgCat.map_baseChangeHopfIdeal_kerOfSurjective
    (coordinateHopfAlgebraBaseChangeIso R K (r + 1))
    (DiagonalizableGroup.baseChangeCoordinateHopfAlgebraIso R K
      (SplitTorus.characterGroup (ULift.{u} (Fin r))))
    (diagonalTorusCoordinateMap_surjective r R) (diagonalTorusCoordinateMap_surjective r K)
    (diagonalTorusCoordinateMap_baseChange r R K)

/-- The points cut out by `diagonalTorusDefiningIdeal` are exactly the diagonal-torus points. -/
@[simp]
theorem quotientPointsSubgroup_diagonalTorusDefiningIdeal (A : CommAlgCat.{u} R) :
    CommHopfAlgCat.quotientPointsSubgroup (coordinateHopfAlgebra R (r + 1))
        (diagonalTorusDefiningIdeal r R) A =
      ((CommHopfAlgCat.mapPointsFunctor (diagonalTorusCoordinateMap r R)).app A).hom.range :=
  HopfIdeal.quotientPointsSubgroup_kerOfSurjective_eq_range_mapPointsFunctor _ _ A

/-- **Membership in the diagonal torus of `SL_{r+1}` on points.** A point lies in the torus
exactly when its matrix is diagonal. -/
theorem mem_quotientPointsSubgroup_diagonalTorusDefiningIdeal_iff (A : Type u) [CommRing A]
    [Algebra R A]
    (g : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R (r + 1)) (CommAlgCat.of R A)) :
    g ∈ CommHopfAlgCat.quotientPointsSubgroup (coordinateHopfAlgebra R (r + 1))
        (diagonalTorusDefiningIdeal r R) (CommAlgCat.of R A) ↔
      (Matrix.SpecialLinearGroup.toGL (pointsMulEquiv (R := R) (A := A) (r + 1) g) :
        Matrix (Fin (r + 1)) (Fin (r + 1)) A).IsDiag := by
  rw [quotientPointsSubgroup_diagonalTorusDefiningIdeal]
  constructor
  · rintro ⟨p, rfl⟩
    exact mem_diagonalTorus_iff.mp (mem_diagonalTorus_iff_exists_diagGL.mpr
      ⟨_, (toGL_pointsMulEquiv_mapPointsFunctor_diagonalTorusCoordinateMap r R A p).symm⟩)
  · intro hg
    obtain ⟨t, ht⟩ := mem_diagonalTorus_iff_exists_diagGL.mp (mem_diagonalTorus_iff.mpr hg)
    have hprod : ∏ i, t i = 1 := by
      have hdet := congrArg Matrix.GeneralLinearGroup.det ht
      rw [det_diagGL] at hdet
      rw [hdet]
      ext
      simp
    refine ⟨(SplitTorus.pointsMulEquiv (R := R) (A := A)).symm
      fun i : ULift.{u} (Fin r) ↦ Fin.partialProd t i.down.succ.castSucc, ?_⟩
    apply (pointsMulEquiv (R := R) (A := A) (r + 1)).injective
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [toGL_pointsMulEquiv_mapPointsFunctor_diagonalTorusCoordinateMap, MulEquiv.apply_symm_apply,
      ← ht]
    refine congrArg diagGL (funext fun l ↦ ?_)
    rw [torusCharacter_diagonalTorusWeight]
    exact SlStd.torusCharacter_partialProd r t hprod l

end CommRing

variable (k : Type u) [Field k]

/-- Over a field, the coordinate quotient defining the diagonal torus of `SL_{r+1}` is a torus. -/
theorem torusCommHopfAlgProperty_quotient_diagonalTorusDefiningIdeal :
    torusCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient ⟨coordinateHopfAlgebra k (r + 1),
        (finiteTypeCommHopfAlgProperty_iff _).2 inferInstance⟩
        (diagonalTorusDefiningIdeal r k)) :=
  (splitTorusCommHopfAlgProperty_quotient_diagonalTorusDefiningIdeal r k).torus k _

grind_pattern torusCommHopfAlgProperty_quotient_diagonalTorusDefiningIdeal =>
  diagonalTorusDefiningIdeal r k

private theorem isReduced_quotient_diagonalTorusDefiningIdeal :
    IsReduced (CommHopfAlgCat.quotient (coordinateHopfAlgebra k (r + 1))
      (diagonalTorusDefiningIdeal r k)) := by
  let e := HopfIdeal.kerLiftBialgEquiv (diagonalTorusCoordinateMap r k).hom
    (diagonalTorusCoordinateMap_surjective r k)
  exact isReduced_of_injective e.toAlgEquiv.toRingEquiv.toRingHom e.injective

variable [IsAlgClosed k]

/-- **The diagonal torus of `SL_{r+1}` is maximal among reduced commutative closed subgroup
schemes over an algebraically closed field.**

If `I` cuts out a reduced commutative closed subgroup containing the diagonal torus, then `I` is
the diagonal-torus defining ideal. Containment is written contravariantly as
`I ≤ diagonalTorusDefiningIdeal r k`; commutativity is the cocommutativity of the quotient
coordinate Hopf algebra. -/
theorem eq_diagonalTorusDefiningIdeal_of_le_of_isCocomm
    (I : HopfIdeal k (coordinateHopfAlgebra k (r + 1)))
    [IsReduced (CommHopfAlgCat.quotient (coordinateHopfAlgebra k (r + 1)) I)]
    [Coalgebra.IsCocomm k (CommHopfAlgCat.quotient (coordinateHopfAlgebra k (r + 1)) I)]
    (hI : I ≤ diagonalTorusDefiningIdeal r k) :
    I = diagonalTorusDefiningIdeal r k := by
  let H := coordinateHopfAlgebra k (r + 1)
  let D := diagonalTorusDefiningIdeal r k
  let A := CommAlgCat.of k k
  let GI := CommHopfAlgCat.quotientPointsSubgroup H I A
  let GD := CommHopfAlgCat.quotientPointsSubgroup H D A
  let e := pointsMulEquiv (R := k) (A := k) (r + 1)
  -- Transport the point group of `I` into the standard carrier points of type `A_r`.
  let φ : HopfAlgebra.points (R := k) (H := H) A →* SlStd.points r k :=
    (Matrix.SpecialLinearGroup.toGL.comp e.toMonoidHom).codRestrict _
      fun g ↦ SlStd.toGL_mem_points r (e g)
  have hmem (g : HopfAlgebra.points (R := k) (H := H) A) :
      g ∈ GD ↔ φ g ∈ SlStd.diagonalPoints r k := by
    rw [SlStd.mem_diagonalPoints_iff]
    exact mem_quotientPointsSubgroup_diagonalTorusDefiningIdeal_iff r k k g
  let P : Subgroup (SlStd.points r k) := GI.map φ
  let _ : IsMulCommutative GI :=
    CommHopfAlgCat.instIsMulCommutativeQuotientPointsSubgroup H I A
  let _ : IsMulCommutative P := Subgroup.map_isMulCommutative GI φ
  have hDG : GD ≤ GI := CommHopfAlgCat.quotientPointsSubgroup_le_of_le H hI A
  have hle : (SlStd.weightTorusPoints r k).range ≤ P := by
    rw [SlStd.range_weightTorusPoints_eq_diagonalPoints]
    intro x hx
    obtain ⟨y, hy⟩ :
        x.1 ∈ (Matrix.SpecialLinearGroup.toGL (n := Fin (r + 1)) (R := k)).range :=
      SlStd.points_eq_range_toGL (K := k) r ▸ x.2
    have hφy : φ (e.symm y) = x := Subtype.ext (by simp [φ, hy])
    exact ⟨e.symm y, hDG ((hmem _).mpr (hφy ▸ hx)), hφy⟩
  have hP := SlStd.eq_range_weightTorusPoints_of_le_of_isMulCommutative r k P hle
  rw [SlStd.range_weightTorusPoints_eq_diagonalPoints] at hP
  have hpoints : GI = GD :=
    le_antisymm (fun g hg ↦ (hmem g).mpr (hP ▸ Subgroup.mem_map_of_mem φ hg)) hDG
  let _ : IsReduced (CommHopfAlgCat.quotient H D) :=
    isReduced_quotient_diagonalTorusDefiningIdeal r k
  exact HopfIdeal.eq_of_quotientPointsSubgroup_eq hpoints

/-- The diagonal torus of `SL_{r+1}` is a maximal torus over an algebraically closed field. -/
private theorem isMaximalTorus_diagonalTorusDefiningIdeal_of_isAlgClosed :
    HopfIdeal.IsMaximalTorus k (coordinateHopfAlgebra k (r + 1))
      (diagonalTorusDefiningIdeal r k) := by
  rw [HopfIdeal.isMaximalTorus_iff]
  refine ⟨torusCommHopfAlgProperty_quotient_diagonalTorusDefiningIdeal r k, ?_⟩
  intro I hI hID
  let _ : IsReduced (CommHopfAlgCat.quotient (coordinateHopfAlgebra k (r + 1)) I) :=
    hI.geometricallyReduced.isReduced
  let _ : Coalgebra.IsCocomm k (CommHopfAlgCat.quotient (coordinateHopfAlgebra k (r + 1)) I) :=
    hI.isCocomm k _
  exact (eq_diagonalTorusDefiningIdeal_of_le_of_isCocomm r k I hID).ge

omit [IsAlgClosed k] in
/-- **The diagonal torus of `SL_{r+1}` is a maximal torus over every field.** -/
@[grind =>]
theorem isMaximalTorus_diagonalTorusDefiningIdeal :
    HopfIdeal.IsMaximalTorus k (coordinateHopfAlgebra k (r + 1))
      (diagonalTorusDefiningIdeal r k) :=
  -- Maximality is checked after base change to an algebraic closure, where the stronger
  -- pointwise maximality theorem applies, and descended along the faithfully flat extension.
  HopfIdeal.isMaximalTorus_of_baseChange (diagonalTorusDefiningIdeal r k)
    (diagonalTorusDefiningIdeal r (AlgebraicClosure k))
    (coordinateHopfAlgebraBaseChangeIso k (AlgebraicClosure k) (r + 1))
    (torusCommHopfAlgProperty_quotient_diagonalTorusDefiningIdeal r k)
    (map_baseChangeHopfIdeal_diagonalTorusDefiningIdeal r k (AlgebraicClosure k))
    (isMaximalTorus_diagonalTorusDefiningIdeal_of_isAlgClosed r (AlgebraicClosure k))

end

end TauCeti.SpecialLinear
