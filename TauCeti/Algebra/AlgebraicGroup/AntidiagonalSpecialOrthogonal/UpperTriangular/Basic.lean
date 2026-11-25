/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.AntidiagonalSpecialOrthogonal.DiagonalTorus
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.UpperTriangular.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperTriangular.Solvable

/-!
# The upper triangular subgroup of `SO_l^J`

Let `J_l` be the antidiagonal matrix and `SO_l^J = {g ∈ SL_l : g J_l gᵀ = J_l}`
(`TauCeti.AntidiagonalSpecialOrthogonal`). In the basis `e₁, …, e_l`, the subspaces
`⟨e₁, …, e_k⟩` for `k ≤ l / 2` are isotropic for the form of `J_l`, and the stabilizer of the
standard complete flag is the subgroup of upper triangular matrices. This file constructs it as a
closed subgroup scheme over every commutative ring `R`: the defining Hopf ideal is the join of the
defining Hopf ideal of `SO_l^J` and the upper triangular Hopf ideal of `GL_l`
(`TauCeti.GeneralLinear.UpperTriangular.definingHopfIdeal`), so that on points it cuts out the
upper triangular matrices of `SO_l^J`. This closed subgroup scheme is defined over every
commutative ring; it is the upper triangular subgroup of the split special orthogonal group only
where `TauCeti.Algebra.AlgebraicGroup.AntidiagonalSpecialOrthogonal.Basic` identifies `SO_l^J` with
it, away from characteristic two.

The diagonal torus `diag(t₁, …, tₙ, (1), tₙ⁻¹, …, t₁⁻¹)` of `SO_l^J`
(`TauCeti.AntidiagonalSpecialOrthogonal.diagonalTorus`) factors through the upper triangular
subgroup, as a closed subgroup scheme. Root subgroups are in
`TauCeti.Algebra.AlgebraicGroup.AntidiagonalSpecialOrthogonal.RootSubgroup`. No smoothness,
connectedness or Borel maximality is claimed here.

## Main declarations

* `TauCeti.AntidiagonalSpecialOrthogonal.UpperTriangular.definingHopfIdeal`: the join of the
  defining Hopf ideals of `SO_l^J` and of the upper triangular subgroup of `GL_l`.
* `TauCeti.AntidiagonalSpecialOrthogonal.UpperTriangular.groupScheme` and
  `TauCeti.AntidiagonalSpecialOrthogonal.UpperTriangular.inclusion`: the closed subgroup scheme
  and its closed immersion into `SO_l^J`.
* `TauCeti.AntidiagonalSpecialOrthogonal.UpperTriangular.pointsMulEquiv`: its points over an
  `R`-algebra `A` are the upper triangular matrices of `SO_l^J(A)`, naturally in `A`.
* `TauCeti.AntidiagonalSpecialOrthogonal.UpperTriangular.isSolvable_points`: these point groups
  are solvable.
* `TauCeti.AntidiagonalSpecialOrthogonal.UpperTriangular.diagonalTorus`: the diagonal torus as a
  closed subgroup scheme of the upper triangular subgroup, recovering the diagonal torus of
  `SO_l^J` (`diagonalTorus_comp_inclusion`, and `pointsMulEquiv_diagonalTorusCoordinateMap` on
  points).

## References

* J. E. Humphreys, *Linear Algebraic Groups* (1975), §26.3, for the diagonal torus and the upper
  triangular Borel subgroup of the orthogonal groups in the antidiagonal model.

The construction follows `TauCeti.Algebra.AlgebraicGroup.AntidiagonalSpecialOrthogonal.Basic`,
which forms `SO_l^J` itself as a join of Hopf ideals. The diagonal-torus factorization follows
`TauCeti.Algebra.AlgebraicGroup.Symplectic.IsotropicFlag.DiagonalTorus`.
-/

public section

open AlgebraicGeometry CategoryTheory WithConv

namespace TauCeti.AntidiagonalSpecialOrthogonal.UpperTriangular

universe u v w

/-! ### The point groups -/

section PointsSubgroup

variable (l : ℕ) (A : Type w) [CommRing A]

/-- **The points of the upper triangular subgroup of `SO_l^J` over `A`**: the upper triangular
matrices of determinant one preserving `J_l`. -/
def pointsSubgroup : Subgroup (GL (Fin l) A) :=
  AntidiagonalSpecialOrthogonal.pointsSubgroup l A ⊓ upperTriangularGroup (Fin l) A

variable {l A}

/-- Membership in the upper triangular points of `SO_l^J`. -/
@[simp]
theorem mem_pointsSubgroup_iff (g : GL (Fin l) A) :
    g ∈ pointsSubgroup l A ↔
      g ∈ AntidiagonalSpecialOrthogonal.pointsSubgroup l A ∧
        (g : Matrix (Fin l) (Fin l) A).IsUpperTriangular := by
  rw [pointsSubgroup, Subgroup.mem_inf, UpperTriangularGroup.mem_iff]

/-- The upper triangular points of `SO_l^J` form a solvable group. -/
instance isSolvable_pointsSubgroup : Group.IsSolvable (pointsSubgroup l A) :=
  Group.isSolvable_of_isSolvable_injective
    (f := Subgroup.inclusion (inf_le_right :
      pointsSubgroup l A ≤ upperTriangularGroup (Fin l) A))
    (Subgroup.inclusion_injective _)

variable {B : Type v} [CommRing B]

/-- Entrywise mapping along a ring homomorphism preserves the upper triangular points of
`SO_l^J`. -/
theorem map_mem_pointsSubgroup (f : A →+* B) {g : GL (Fin l) A} (hg : g ∈ pointsSubgroup l A) :
    Matrix.GeneralLinearGroup.map f g ∈ pointsSubgroup l B := by
  obtain ⟨hSO, hUT⟩ := Subgroup.mem_inf.mp hg
  exact ⟨AntidiagonalSpecialOrthogonal.map_mem_pointsSubgroup f hSO,
    UpperTriangularGroup.mem_iff.mpr ((UpperTriangularGroup.mem_iff.mp hUT).map f)⟩

/-- The homomorphism of upper triangular point groups of `SO_l^J` induced by a ring
homomorphism. -/
def pointsSubgroupMap (f : A →+* B) : pointsSubgroup l A →* pointsSubgroup l B :=
  ((Matrix.GeneralLinearGroup.map f).comp (pointsSubgroup l A).subtype).codRestrict _
    fun g => map_mem_pointsSubgroup f g.property

/-- The induced map on upper triangular points is entrywise mapping of matrices. -/
@[simp]
theorem coe_pointsSubgroupMap (f : A →+* B) (g : pointsSubgroup l A) :
    (pointsSubgroupMap f g : GL (Fin l) B) = Matrix.GeneralLinearGroup.map f (g : GL (Fin l) A) :=
  (rfl)

end PointsSubgroup

/-! ### The defining Hopf ideal and the group scheme -/

variable (R : Type u) [CommRing R] (l : ℕ)

/-- **The defining Hopf ideal of the upper triangular subgroup of `SO_l^J`**: the join of the
defining Hopf ideal of `SO_l^J` and the upper triangular Hopf ideal of `GL_l`. -/
noncomputable def definingHopfIdeal :
    HopfIdeal R (GeneralLinear.coordinateHopfAlgebra R l) :=
  AntidiagonalSpecialOrthogonal.definingHopfIdeal R l ⊔
    GeneralLinear.UpperTriangular.definingHopfIdeal R l

/-- The defining Hopf ideal is the join of the `SO_l^J` and upper triangular Hopf ideals. -/
theorem definingHopfIdeal_def :
    definingHopfIdeal R l =
      AntidiagonalSpecialOrthogonal.definingHopfIdeal R l ⊔
        GeneralLinear.UpperTriangular.definingHopfIdeal R l :=
  (rfl)

/-- The defining Hopf ideal of `SO_l^J` is contained in that of its upper triangular subgroup. -/
theorem le_definingHopfIdeal :
    AntidiagonalSpecialOrthogonal.definingHopfIdeal R l ≤ definingHopfIdeal R l :=
  le_sup_left

/-- The coordinate Hopf algebra of the upper triangular subgroup of `SO_l^J`. -/
noncomputable abbrev coordinateHopfAlgebra : _root_.CommHopfAlgCat.{u} R :=
  CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra R l) (definingHopfIdeal R l)

/-- Restriction of functions from `SO_l^J` to its upper triangular subgroup. -/
noncomputable def coordinateMap :
    AntidiagonalSpecialOrthogonal.coordinateHopfAlgebra R l ⟶ coordinateHopfAlgebra R l :=
  CommHopfAlgCat.quotientMapOfLe (GeneralLinear.coordinateHopfAlgebra R l)
    (le_definingHopfIdeal R l)

/-- Restriction from `SO_l^J` to its upper triangular subgroup is the quotient-to-quotient
morphism of the inclusion of Hopf ideals. -/
theorem coordinateMap_def :
    coordinateMap R l =
      CommHopfAlgCat.quotientMapOfLe (GeneralLinear.coordinateHopfAlgebra R l)
        (le_definingHopfIdeal R l) :=
  (rfl)

/-- Restricting from `GL_l` to `SO_l^J` and then to the upper triangular subgroup is the quotient
map of the defining Hopf ideal. -/
@[simp]
theorem coordinateMap_comp_coordinateMap :
    AntidiagonalSpecialOrthogonal.coordinateMap R l ≫ coordinateMap R l =
      CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra R l)
        (definingHopfIdeal R l) := by
  rw [AntidiagonalSpecialOrthogonal.coordinateMap_def, coordinateMap_def]
  exact CommHopfAlgCat.mkQuotient_comp_quotientMapOfLe _ _

/-- **The upper triangular subgroup of `SO_l^J`**, a closed subgroup scheme of `GL_l` and of
`SO_l^J`. -/
noncomputable abbrev groupScheme :=
  CommHopfAlgCat.quotientSpec (GeneralLinear.coordinateHopfAlgebra R l) (definingHopfIdeal R l)

/-- The closed-subgroup inclusion of the upper triangular subgroup into `SO_l^J`. -/
noncomputable def inclusion : groupScheme R l ⟶ AntidiagonalSpecialOrthogonal.groupScheme R l :=
  CommHopfAlgCat.quotientSpecMapOfLe (GeneralLinear.coordinateHopfAlgebra R l)
    (le_definingHopfIdeal R l)

/-- The inclusion into `SO_l^J` is the closed immersion of the inclusion of Hopf ideals. -/
theorem inclusion_def :
    inclusion R l =
      CommHopfAlgCat.quotientSpecMapOfLe (GeneralLinear.coordinateHopfAlgebra R l)
        (le_definingHopfIdeal R l) :=
  (rfl)

/-- The upper triangular subgroup is a closed subgroup scheme of `SO_l^J`. -/
instance isClosedImmersion_inclusion : IsClosedImmersion (inclusion R l).hom.hom.left := by
  rw [inclusion_def]
  infer_instance

/-- Including the upper triangular subgroup into `SO_l^J` and then into `GL_l` is its inclusion
into `GL_l` as the closed subgroup cut out by its defining Hopf ideal. -/
@[simp]
theorem inclusion_comp_inclusion :
    inclusion R l ≫ AntidiagonalSpecialOrthogonal.inclusion R l =
      GeneralLinear.hopfIdealInclusion R l (definingHopfIdeal R l) := by
  rw [inclusion_def, AntidiagonalSpecialOrthogonal.inclusion_def,
    GeneralLinear.hopfIdealInclusion_def, GeneralLinear.hopfIdealInclusion_def,
    ← Category.assoc, CommHopfAlgCat.quotientSpecMapOfLe_comp_quotientSpecι]

/-! ### Algebra-valued points -/

section Points

variable {A : Type w} [CommRing A] [Algebra R A]

/-- The matrix subgroup of `GL_l(A)` cut out by the defining Hopf ideal is the group of upper
triangular points of `SO_l^J`. -/
theorem hopfIdealPointsSubgroup_definingHopfIdeal :
    GeneralLinear.hopfIdealPointsSubgroup l (definingHopfIdeal R l) A = pointsSubgroup l A := by
  rw [definingHopfIdeal, GeneralLinear.hopfIdealPointsSubgroup_sup,
    AntidiagonalSpecialOrthogonal.hopfIdealPointsSubgroup_definingHopfIdeal,
    GeneralLinear.UpperTriangular.hopfIdealPointsSubgroup_eq, pointsSubgroup]

/-- **The points of the upper triangular subgroup of `SO_l^J`**: the group of algebra-valued
points of its coordinate Hopf algebra is the group of upper triangular matrices of `SO_l^J(A)`. -/
noncomputable def pointsMulEquiv :
    HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R l) (CommAlgCat.of R A) ≃*
      pointsSubgroup l A :=
  (GeneralLinear.hopfIdealPointsSubgroupMulEquiv l (definingHopfIdeal R l)
    (CommAlgCat.of R A)).trans
    (MulEquiv.subgroupCongr (hopfIdealPointsSubgroup_definingHopfIdeal R l))

/-- Under the point equivalences, the quotient-point inclusion into `GL_l` is the inclusion of
the upper triangular points of `SO_l^J`. -/
theorem pointsMulEquiv_coe
    (f : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R l) (CommAlgCat.of R A)) :
    GeneralLinear.pointsMulEquiv l
        (CommHopfAlgCat.quotientPointsHom
          (GeneralLinear.coordinateHopfAlgebra R l) (definingHopfIdeal R l)
          (CommAlgCat.of R A) f) =
      (pointsMulEquiv R l (A := A) f : GL (Fin l) A) := by
  rw [pointsMulEquiv, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
    GeneralLinear.coe_hopfIdealPointsSubgroupMulEquiv_apply]

/-- The ambient point attached to an upper triangular point of `SO_l^J` is the general-linear
point of its matrix. -/
@[simp↓]
theorem quotientPointsHom_pointsMulEquiv_symm (g : pointsSubgroup l A) :
    CommHopfAlgCat.quotientPointsHom
        (GeneralLinear.coordinateHopfAlgebra R l) (definingHopfIdeal R l)
        (CommAlgCat.of R A) ((pointsMulEquiv R l (A := A)).symm g) =
      (GeneralLinear.pointsMulEquiv (R := R) (A := A) l).symm (g : GL (Fin l) A) := by
  apply (GeneralLinear.pointsMulEquiv (R := R) (A := A) l).injective
  rw [pointsMulEquiv_coe, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

variable {B : Type v} [CommRing B] [Algebra R B]

/-- **The points of the upper triangular subgroup are natural in the value algebra**:
postcomposition of Hopf points agrees with entrywise mapping of matrices. -/
theorem pointsMulEquiv_mapValue (phi : A →ₐ[R] B)
    (f : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R l) (CommAlgCat.of R A)) :
    pointsMulEquiv R l (A := B) (AlgHom.mapValue (H := coordinateHopfAlgebra R l) phi f) =
      pointsSubgroupMap (phi : A →+* B) (pointsMulEquiv R l (A := A) f) := by
  apply Subtype.ext
  rw [coe_pointsSubgroupMap, ← pointsMulEquiv_coe, ← pointsMulEquiv_coe,
    ← CommHopfAlgCat.mapValue_quotientPointsHom, GeneralLinear.pointsMulEquiv_mapValue]

/-- Every algebra-valued point group of the upper triangular subgroup of `SO_l^J` is solvable. -/
theorem isSolvable_points :
    Group.IsSolvable
      (HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R l) (CommAlgCat.of R A)) :=
  Group.isSolvable_of_isSolvable_injective
    (f := (pointsMulEquiv R l (A := A)).toMonoidHom) (pointsMulEquiv R l (A := A)).injective

end Points

/-! ### The diagonal torus -/

/-- The general-linear weight torus of the diagonal torus of `SO_l^J` kills the defining Hopf ideal
of the upper triangular subgroup: its matrix is diagonal and lies in `SO_l^J`. -/
theorem definingHopfIdeal_toIdeal_le_ker_weightTorusCoordinateMap :
    (definingHopfIdeal R l).toIdeal ≤
      RingHom.ker (GeneralLinear.weightTorusCoordinateMap (R := R)
        (diagonalTorusWeight.{u} l)).hom.toAlgHom.toRingHom := by
  rw [definingHopfIdeal, HopfIdeal.sup_toIdeal, sup_le_iff]
  constructor
  · exact CommHopfAlgCat.toIdeal_le_ker_of_mkQuotient_comp (by
      rw [← AntidiagonalSpecialOrthogonal.coordinateMap_def]
      exact AntidiagonalSpecialOrthogonal.coordinateMap_comp_diagonalTorusCoordinateMap R l)
  · refine GeneralLinear.UpperTriangular.definingHopfIdeal_toIdeal_le_ker R l _ fun i j hji => ?_
    have h := congrFun (congrFun (GeneralLinear.map_genericMatrix_weightTorusCoordinateMap
      (R := R) (diagonalTorusWeight.{u} l)) i) j
    rw [Matrix.map_apply, GeneralLinear.genericMatrix_apply,
      Matrix.diagonal_apply_ne _ (ne_of_gt hji)] at h
    exact h

/-- **The coordinate morphism of the diagonal torus of the upper triangular subgroup of
`SO_l^J`.** Its direction is opposite to the represented group-scheme morphism. -/
noncomputable def diagonalTorusCoordinateMap :
    coordinateHopfAlgebra R l ⟶
      (DiagonalizableGroup.coordinateRing R
        (SplitTorus.characterGroup (ULift.{u} (Fin (l / 2))))).obj :=
  CommHopfAlgCat.liftQuotient (definingHopfIdeal R l)
    (GeneralLinear.weightTorusCoordinateMap (diagonalTorusWeight l))
    (definingHopfIdeal_toIdeal_le_ker_weightTorusCoordinateMap R l)

/-- Restricting from `SO_l^J` to its upper triangular subgroup and then to the diagonal torus is
restriction to the diagonal torus of `SO_l^J`. -/
@[reassoc (attr := simp)]
theorem coordinateMap_comp_diagonalTorusCoordinateMap :
    coordinateMap R l ≫ diagonalTorusCoordinateMap R l =
      AntidiagonalSpecialOrthogonal.diagonalTorusCoordinateMap R l := by
  rw [coordinateMap_def]
  exact CommHopfAlgCat.quotientMapOfLe_comp_liftQuotient_eq _ _ _ _ _
    (by rw [← AntidiagonalSpecialOrthogonal.coordinateMap_def,
      AntidiagonalSpecialOrthogonal.coordinateMap_comp_diagonalTorusCoordinateMap])

/-- The coordinate morphism of the diagonal torus of the upper triangular subgroup is
surjective over every commutative base ring. -/
theorem diagonalTorusCoordinateMap_surjective :
    Function.Surjective (diagonalTorusCoordinateMap R l).hom :=
  CommHopfAlgCat.liftQuotient_surjective_of_surjective _ _ _
    (GeneralLinear.weightTorusCoordinateMap_surjective _ span_range_diagonalTorusWeight_eq_top)

/-- **The diagonal torus of the upper triangular subgroup of `SO_l^J`**, as a group-scheme
morphism from the rank-`l / 2` split torus. -/
noncomputable def diagonalTorus :
    SplitTorus.groupScheme R (ULift.{u} (Fin (l / 2))) ⟶ groupScheme R l :=
  eqToHom
      (DiagonalizableGroup.groupScheme_def R
        (SplitTorus.characterGroup (ULift.{u} (Fin (l / 2))))) ≫
    (hopfSpec (CommRingCat.of R)).map (diagonalTorusCoordinateMap R l).op

/-- The diagonal torus of the upper triangular subgroup is relative spectrum applied to its
coordinate morphism. -/
theorem diagonalTorus_def :
    diagonalTorus R l =
      eqToHom
          (DiagonalizableGroup.groupScheme_def R
            (SplitTorus.characterGroup (ULift.{u} (Fin (l / 2))))) ≫
        (hopfSpec (CommRingCat.of R)).map (diagonalTorusCoordinateMap R l).op :=
  (rfl)

/-- **The diagonal torus of `SO_l^J` factors through its upper triangular subgroup.** -/
@[reassoc (attr := simp)]
theorem diagonalTorus_comp_inclusion :
    diagonalTorus R l ≫ inclusion R l = AntidiagonalSpecialOrthogonal.diagonalTorus R l := by
  rw [diagonalTorus_def, inclusion_def, CommHopfAlgCat.quotientSpecMapOfLe_def,
    AntidiagonalSpecialOrthogonal.diagonalTorus_def, Category.assoc, ← Functor.map_comp,
    ← op_comp, ← coordinateMap_def, coordinateMap_comp_diagonalTorusCoordinateMap]
  simp only [eqToHom_refl, Category.comp_id]

/-- The diagonal torus is a closed subgroup scheme of the upper triangular subgroup of
`SO_l^J`. -/
instance isClosedImmersion_diagonalTorus :
    IsClosedImmersion (diagonalTorus R l).hom.hom.left := by
  rw [diagonalTorus]
  exact (CommHopfAlgCat.isClosedImmersion_eqToHom_comp_hopfSpec_map_iff
    (DiagonalizableGroup.groupScheme_def R
      (SplitTorus.characterGroup (ULift.{u} (Fin (l / 2))))) _).mpr
    (diagonalTorusCoordinateMap_surjective R l)

/-- **The diagonal torus of the upper triangular subgroup on points**: the factored torus map
gives the same diagonal matrix as the diagonal torus of `SO_l^J`. -/
@[simp]
theorem pointsMulEquiv_diagonalTorusCoordinateMap {A : Type w} [CommRing A] [Algebra R A]
    (f : WithConv
      (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin (l / 2)) →₀ ℤ)) →ₐ[R] A)) :
    (pointsMulEquiv R l (A := A)
        (toConv (f.ofConv.comp (diagonalTorusCoordinateMap R l).hom)) : GL (Fin l) A) =
      AntidiagonalSpecialOrthogonal.pointsMulEquiv R l (A := A)
        (AntidiagonalSpecialOrthogonal.diagonalTorusPoints R l A f) := by
  have hquot := CommHopfAlgCat.mapPointsFunctor_eq_quotientPointsHom_of_mkQuotient_comp
    (definingHopfIdeal R l) (diagonalTorusCoordinateMap R l)
    (GeneralLinear.weightTorusCoordinateMap (diagonalTorusWeight l))
    (CommHopfAlgCat.mkQuotient_comp_liftQuotient _ _ _) (CommAlgCat.of R A) f
  rw [CommHopfAlgCat.Hom.mapPointsFunctor_app_apply (diagonalTorusCoordinateMap R l)
    (CommAlgCat.of R A) f] at hquot
  rw [← pointsMulEquiv_coe, ← hquot,
    AntidiagonalSpecialOrthogonal.pointsMulEquiv_diagonalTorusPoints]
  exact GeneralLinear.pointsMulEquiv_mapPointsFunctor_weightTorusCoordinateMap _
    (CommAlgCat.of R A) f

end TauCeti.AntidiagonalSpecialOrthogonal.UpperTriangular
