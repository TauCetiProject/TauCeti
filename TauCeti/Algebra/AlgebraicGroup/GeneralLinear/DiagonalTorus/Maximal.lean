/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.DiagonalTorus.ClosedImmersion
public import TauCeti.Algebra.AlgebraicGroup.Hopf.KernelPoints
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Separation
public import TauCeti.Algebra.AlgebraicGroup.Torus.Maximal
import TauCeti.Algebra.AlgebraicGroup.Torus.SmoothConnected
import TauCeti.Algebra.GroupWithZero.Units.Basic

/-!
# Maximality of the diagonal torus in the general linear group

Over any field, the diagonal torus of `GL_n` is a maximal torus. Over an algebraically closed
field, it is moreover maximal among reduced commutative closed subgroup schemes. The defining
ideal and its quotient presentation work over every commutative ring and commute with arbitrary
base change. In Hopf coordinates, the defining ideal is the kernel of the surjective
restriction morphism from
`O(GL_n)` to the Laurent coordinate ring of the split torus.

The proof compares algebraically closed points. A reduced commutative closed subgroup containing
the diagonal torus gives a commutative matrix subgroup containing all invertible diagonal
matrices. The point-level centralizer calculation says that this subgroup is exactly the diagonal
torus. Reduced finite-type point separation then upgrades equality of point subgroups to equality
of their defining Hopf ideals.

This statement is stronger than maximality among tori: every torus is reduced and commutative,
whereas the competing subgroup below need not itself be a torus or connected.

## Main declarations

* `TauCeti.GeneralLinear.diagonalTorusDefiningIdeal`: the Hopf ideal cutting out the diagonal
  torus in `GL_n`.
* `TauCeti.GeneralLinear.diagonalTorusCoordinateIso`: its coordinate quotient is the standard
  Laurent Hopf algebra.
* `TauCeti.GeneralLinear.splitTorusCommHopfAlgProperty_quotient_diagonalTorusDefiningIdeal`:
  its quotient coordinate Hopf algebra is a split torus.
* `TauCeti.GeneralLinear.quotientPointsSubgroup_diagonalTorusDefiningIdeal`: its points are the
  range of the diagonal-torus point morphism.
* `TauCeti.GeneralLinear.mem_quotientPointsSubgroup_diagonalTorusDefiningIdeal_iff`: over every
  value algebra, its points are the diagonal invertible matrices.
* `TauCeti.GeneralLinear.eq_diagonalTorusDefiningIdeal_of_le_of_isCocomm`: no larger reduced
  commutative closed subgroup contains the diagonal torus.
* `TauCeti.GeneralLinear.isMaximalTorus_diagonalTorusDefiningIdeal`: the diagonal torus is a
  maximal torus in the Hopf-ideal API.

## References

* J. S. Milne, *Algebraic Groups* (2017), Example 12.6 and Section 21.1.
* J. E. Humphreys, *Linear Algebraic Groups* (1975), Sections 15.3 and 16.1.

This completes the standard `GL_n` maximal-torus example required by Layer 7, "Borel subgroups,
maximal tori", of the ReductiveGroups roadmap. Together with the existing adjoint root spaces and
normalizer quotient, it validates the torus used by the packaged `GL_n` root datum and Weyl group.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.GeneralLinear

universe u w

noncomputable section

section Ring

variable (k : Type u) [CommRing k] (n : ℕ)

/-- The Hopf ideal defining the diagonal torus inside the coordinate Hopf algebra of `GL_n`.

It is the ordinary kernel of the surjective restriction morphism to the split-torus coordinate
ring, packaged as a Hopf ideal. This construction works over every commutative base ring. -/
noncomputable def diagonalTorusDefiningIdeal :
    HopfIdeal k (coordinateHopfAlgebra k n) :=
  HopfIdeal.kerOfSurjective (diagonalTorusCoordinateMap (R := k) (N := n)).hom
    (diagonalTorusCoordinateMap_surjective k n)

/-- The diagonal-torus defining ideal is the Hopf kernel of restriction to diagonal
coordinates. -/
theorem diagonalTorusDefiningIdeal_eq_ker :
    diagonalTorusDefiningIdeal k n =
      HopfIdeal.kerOfSurjective (diagonalTorusCoordinateMap (R := k) (N := n)).hom
        (diagonalTorusCoordinateMap_surjective k n) := (rfl)

/-- A function belongs to the diagonal-torus ideal precisely when its restriction vanishes. -/
@[simp]
theorem mem_diagonalTorusDefiningIdeal (x : coordinateHopfAlgebra k n) :
    x ∈ diagonalTorusDefiningIdeal k n ↔
      (diagonalTorusCoordinateMap (R := k) (N := n)).hom x = 0 := by
  rw [diagonalTorusDefiningIdeal, HopfIdeal.mem_kerOfSurjective]

/-- The quotient by the diagonal-torus defining ideal is its Laurent coordinate Hopf algebra. -/
noncomputable def diagonalTorusCoordinateIso :
    FiniteTypeCommHopfAlgCat.quotient
        ⟨coordinateHopfAlgebra k n,
          (finiteTypeCommHopfAlgProperty_iff _).2 inferInstance⟩
        (diagonalTorusDefiningIdeal k n) ≅
      DiagonalizableGroup.coordinateRing k
        (SplitTorus.characterGroup (ULift.{u} (Fin n))) :=
  ObjectProperty.isoMk _ <|
    CommHopfAlgCat.Hom.quotientKerOfSurjectiveIso (diagonalTorusCoordinateMap (R := k) (N := n))
      (diagonalTorusCoordinateMap_surjective k n)

/-- The diagonal-torus quotient isomorphism identifies the quotient morphism with the canonical
restriction to diagonal coordinates. -/
@[simp]
theorem mkQuotient_comp_diagonalTorusCoordinateIso_hom :
    FiniteTypeCommHopfAlgCat.mkQuotient
          ⟨coordinateHopfAlgebra k n,
            (finiteTypeCommHopfAlgProperty_iff _).2 inferInstance⟩
          (diagonalTorusDefiningIdeal k n) ≫
        (diagonalTorusCoordinateIso k n).hom =
      ObjectProperty.homMk (diagonalTorusCoordinateMap (R := k) (N := n)) :=
  ObjectProperty.hom_ext _ (CommHopfAlgCat.Hom.mkQuotient_comp_quotientKerOfSurjectiveIso_hom _ _)

/-- The base-change isomorphism of `GL_n` coordinate Hopf algebras carries the base-changed
diagonal-torus ideal onto the diagonal-torus ideal over the extended base. -/
@[simp]
theorem map_baseChangeHopfIdeal_diagonalTorusDefiningIdeal
    (K : Type u) [CommRing K] [Algebra k K] :
    (CommHopfAlgCat.baseChangeHopfIdeal (K := K) (diagonalTorusDefiningIdeal k n)).map
        (coordinateHopfAlgebraBaseChangeIso k K n).hom.hom =
      diagonalTorusDefiningIdeal K n :=
  CommHopfAlgCat.map_baseChangeHopfIdeal_kerOfSurjective
    (coordinateHopfAlgebraBaseChangeIso k K n)
    (DiagonalizableGroup.baseChangeCoordinateHopfAlgebraIso k K
      (SplitTorus.characterGroup (ULift.{u} (Fin n))))
    (diagonalTorusCoordinateMap_surjective k n) (diagonalTorusCoordinateMap_surjective K n)
    (diagonalTorusCoordinateMap_baseChange (N := n) k K)

/-- The quotient coordinate Hopf algebra of the diagonal torus is a split torus of rank `n`. -/
theorem splitTorusCommHopfAlgProperty_quotient_diagonalTorusDefiningIdeal :
    splitTorusCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient
        ⟨coordinateHopfAlgebra k n,
          (finiteTypeCommHopfAlgProperty_iff _).2 inferInstance⟩
        (diagonalTorusDefiningIdeal k n)) := by
  rw [splitTorusCommHopfAlgProperty_iff]
  exact ⟨n, ⟨(diagonalTorusCoordinateIso k n).symm⟩⟩

grind_pattern splitTorusCommHopfAlgProperty_quotient_diagonalTorusDefiningIdeal =>
  diagonalTorusDefiningIdeal k n

/-- The points cut out by `diagonalTorusDefiningIdeal` are exactly the diagonal-torus points. -/
theorem quotientPointsSubgroup_diagonalTorusDefiningIdeal (A : CommAlgCat.{u} k) :
    CommHopfAlgCat.quotientPointsSubgroup (coordinateHopfAlgebra k n)
        (diagonalTorusDefiningIdeal k n) A =
      ((CommHopfAlgCat.Hom.mapPointsFunctor
        (diagonalTorusCoordinateMap (R := k) (N := n))).app A).hom.range :=
  HopfIdeal.quotientPointsSubgroup_kerOfSurjective_eq_range_mapPointsFunctor _ _ A

/-- **The points of the diagonal torus are the diagonal matrices.** Over every value algebra, a
point of `GL_n` kills `diagonalTorusDefiningIdeal` exactly when its matrix is diagonal. -/
@[simp↓]
theorem mem_quotientPointsSubgroup_diagonalTorusDefiningIdeal_iff
    (A : Type w) [CommRing A] [Algebra k A]
    (g : HopfAlgebra.points (R := k) (H := coordinateHopfAlgebra k n) (CommAlgCat.of k A)) :
    g ∈ CommHopfAlgCat.quotientPointsSubgroup (coordinateHopfAlgebra k n)
        (diagonalTorusDefiningIdeal k n) (CommAlgCat.of k A) ↔
      ((pointsMulEquiv n g : Matrix.GeneralLinearGroup (Fin n) A) :
        Matrix (Fin n) (Fin n) A).IsDiag := by
  rw [diagonalTorusDefiningIdeal_eq_ker,
    HopfIdeal.quotientPointsSubgroup_kerOfSurjective_eq_range_mapPointsFunctor]
  constructor
  · rintro ⟨t, rfl⟩
    rw [mapPointsFunctor_diagonalTorusCoordinateMap_app (CommAlgCat.of k A) t]
    exact TauCeti.mem_diagonalTorus_iff.mp (TauCeti.mem_diagonalTorus_iff_exists_diagGL.mpr
      ⟨_, (pointsMulEquiv_diagonalTorusPoints t).symm⟩)
  · intro hg
    obtain ⟨s, hs⟩ := TauCeti.mem_diagonalTorus_iff_exists_diagGL.mp
      (TauCeti.mem_diagonalTorus_iff.mpr hg)
    refine ⟨(SplitTorus.pointsMulEquiv (R := k) (A := A)).symm fun i ↦ s i.down,
      (mapPointsFunctor_diagonalTorusCoordinateMap_app (CommAlgCat.of k A) _).trans ?_⟩
    apply (pointsMulEquiv (R := k) (A := A) n).injective
    rw [pointsMulEquiv_diagonalTorusPoints, ← hs]
    congr 1
    funext i
    rw [diagonalTorusCoordinates_apply, MulEquiv.apply_symm_apply]

end Ring

variable (k : Type u) [Field k] (n : ℕ)

/-- The quotient coordinate Hopf algebra of the diagonal torus is a torus. -/
theorem torusCommHopfAlgProperty_quotient_diagonalTorusDefiningIdeal :
    torusCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient
        ⟨coordinateHopfAlgebra k n,
          (finiteTypeCommHopfAlgProperty_iff _).2 inferInstance⟩
        (diagonalTorusDefiningIdeal k n)) :=
  (splitTorusCommHopfAlgProperty_quotient_diagonalTorusDefiningIdeal k n).torus k _

grind_pattern torusCommHopfAlgProperty_quotient_diagonalTorusDefiningIdeal =>
  diagonalTorusDefiningIdeal k n

variable [IsAlgClosed k]

omit [IsAlgClosed k] in
/-- Every diagonal matrix is the image of a `k`-point cut out by `diagonalTorusDefiningIdeal`. -/
private theorem diagonalTorus_le_map_quotientPointsSubgroup :
    TauCeti.diagonalTorus k n ≤
      (CommHopfAlgCat.quotientPointsSubgroup (coordinateHopfAlgebra k n)
        (diagonalTorusDefiningIdeal k n) (CommAlgCat.of k k)).map
          (pointsMulEquiv (R := k) (A := k) n).toMonoidHom := by
  intro m hm
  refine ⟨(pointsMulEquiv (R := k) (A := k) n).symm m, ?_, MulEquiv.apply_symm_apply _ m⟩
  refine (mem_quotientPointsSubgroup_diagonalTorusDefiningIdeal_iff k n k _).mpr ?_
  rw [MulEquiv.apply_symm_apply]
  exact TauCeti.mem_diagonalTorus_iff.mp hm

/-- **The diagonal torus of `GL_n` is maximal among reduced commutative closed subgroup
schemes over an algebraically closed field.**

If `I` cuts out a reduced commutative closed subgroup containing the diagonal torus, then `I` is
the diagonal-torus defining ideal. Containment is written contravariantly as
`I ≤ diagonalTorusDefiningIdeal k n`; commutativity is the cocommutativity of the quotient
coordinate Hopf algebra. -/
theorem eq_diagonalTorusDefiningIdeal_of_le_of_isCocomm
    (I : HopfIdeal k (coordinateHopfAlgebra k n))
    [IsReduced (CommHopfAlgCat.quotient (coordinateHopfAlgebra k n) I)]
    [Coalgebra.IsCocomm k (CommHopfAlgCat.quotient (coordinateHopfAlgebra k n) I)]
    (hI : I ≤ diagonalTorusDefiningIdeal k n) :
    I = diagonalTorusDefiningIdeal k n := by
  let H := coordinateHopfAlgebra k n
  let D := diagonalTorusDefiningIdeal k n
  let A := CommAlgCat.of k k
  let GI := CommHopfAlgCat.quotientPointsSubgroup H I A
  let GD := CommHopfAlgCat.quotientPointsSubgroup H D A
  let e := pointsMulEquiv (R := k) (A := k) n
  let P : Subgroup (GL (Fin n) k) := GI.map e.toMonoidHom
  let _ : IsMulCommutative GI :=
    CommHopfAlgCat.instIsMulCommutativeQuotientPointsSubgroup
      (coordinateHopfAlgebra k n) I (CommAlgCat.of k k)
  let _ : IsMulCommutative P := Subgroup.map_isMulCommutative GI e.toMonoidHom
  have hDG : GD ≤ GI :=
    CommHopfAlgCat.quotientPointsSubgroup_le_of_le H hI A
  have hle := diagonalTorus_le_map_quotientPointsSubgroup k n
  have hP : P = TauCeti.diagonalTorus k n :=
    eq_diagonalTorus_of_le_of_isMulCommutative P (hle.trans (Subgroup.map_mono hDG))
  have hpoints : GI = GD := by
    refine le_antisymm (fun g hg ↦ ?_) hDG
    obtain ⟨g', hg', he⟩ := hle (hP ▸ ⟨g, hg, rfl⟩ : e g ∈ TauCeti.diagonalTorus k n)
    rwa [e.injective he] at hg'
  let _ : IsReduced (CommHopfAlgCat.quotient H D) :=
    HopfIdeal.isReduced_quotient_kerOfSurjective _ (diagonalTorusCoordinateMap_surjective k n)
  exact HopfIdeal.eq_of_quotientPointsSubgroup_eq hpoints

/-- **The diagonal torus of `GL_n` is a maximal torus.** This packages the stronger result that
no reduced commutative closed subgroup properly containing it exists into the general
Hopf-ideal maximal-torus predicate. -/
private theorem isMaximalTorus_diagonalTorusDefiningIdeal_of_isAlgClosed :
    HopfIdeal.IsMaximalTorus k (coordinateHopfAlgebra k n)
      (diagonalTorusDefiningIdeal k n) := by
  rw [HopfIdeal.isMaximalTorus_iff]
  refine ⟨torusCommHopfAlgProperty_quotient_diagonalTorusDefiningIdeal k n, ?_⟩
  intro I hI hID
  let _ : IsReduced
      (CommHopfAlgCat.quotient (coordinateHopfAlgebra k n) I) :=
    hI.geometricallyReduced.isReduced
  let _ : Coalgebra.IsCocomm k
      (CommHopfAlgCat.quotient (coordinateHopfAlgebra k n) I) :=
    hI.isCocomm k _
  have hEq := eq_diagonalTorusDefiningIdeal_of_le_of_isCocomm k n I hID
  subst I
  exact le_rfl

omit [IsAlgClosed k] in
/-- **The diagonal torus of `GL_n` is a maximal torus over every field.** Maximality is checked
after base change to an algebraic closure, where the stronger pointwise maximality theorem
applies, and then descended using faithful flatness. -/
@[grind =>]
theorem isMaximalTorus_diagonalTorusDefiningIdeal :
    HopfIdeal.IsMaximalTorus k (coordinateHopfAlgebra k n)
      (diagonalTorusDefiningIdeal k n) :=
  HopfIdeal.isMaximalTorus_of_baseChange (diagonalTorusDefiningIdeal k n)
    (diagonalTorusDefiningIdeal (AlgebraicClosure k) n)
    (coordinateHopfAlgebraBaseChangeIso k (AlgebraicClosure k) n)
    (torusCommHopfAlgProperty_quotient_diagonalTorusDefiningIdeal k n)
    (map_baseChangeHopfIdeal_diagonalTorusDefiningIdeal k n (AlgebraicClosure k))
    (isMaximalTorus_diagonalTorusDefiningIdeal_of_isAlgClosed (AlgebraicClosure k) n)

end

end TauCeti.GeneralLinear
