/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.DiagonalTorus.ClosedImmersion
public import TauCeti.Algebra.AlgebraicGroup.Hopf.KernelPoints
public import TauCeti.Algebra.AlgebraicGroup.Torus.Maximal.Points
import TauCeti.Algebra.GroupWithZero.Units.Basic

/-!
# Maximality of the diagonal torus in the general linear group

Over any field, the diagonal torus of `GL_n` is maximal among reduced commutative closed
subgroup schemes, and hence is a maximal torus. The defining ideal and its quotient presentation
work over every commutative ring and commute with arbitrary base change. In Hopf coordinates,
the defining ideal is the kernel of the surjective restriction morphism from `O(GL_n)` to the
Laurent coordinate ring of the split torus.

The proof compares points over an algebraic closure of the base field. A reduced commutative
closed subgroup containing the diagonal torus gives a commutative matrix subgroup containing all
invertible diagonal matrices. The point-level centralizer calculation says that this subgroup is
exactly the diagonal torus. Reduced finite-type point separation then upgrades equality of point
subgroups to equality of their defining Hopf ideals.

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
* `TauCeti.GeneralLinear.centralizer_quotientPointsSubgroup_diagonalTorusDefiningIdeal`: its
  points over an algebraically closed extension are self-centralizing.
* `TauCeti.GeneralLinear.eq_diagonalTorusDefiningIdeal_of_le_of_isCocomm`: no larger reduced
  commutative closed subgroup contains the diagonal torus.
* `TauCeti.GeneralLinear.isMaximalTorus_diagonalTorusDefiningIdeal`: the diagonal torus is a
  maximal torus in the Hopf-ideal API.

This supplies the standard `GL_n` maximal-torus example for Layer 7, "Borel subgroups, maximal
tori", of the ReductiveGroups roadmap.
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

/-- The points of the diagonal closed subgroup over an algebraically closed extension are
self-centralizing in the ambient point group of `GL_n`. -/
theorem centralizer_quotientPointsSubgroup_diagonalTorusDefiningIdeal
    (K : Type w) [Field K] [Algebra k K] [IsAlgClosed K] :
    Subgroup.centralizer
        (CommHopfAlgCat.quotientPointsSubgroup (coordinateHopfAlgebra k n)
          (diagonalTorusDefiningIdeal k n) (CommAlgCat.of k K) : Set _) =
      CommHopfAlgCat.quotientPointsSubgroup (coordinateHopfAlgebra k n)
        (diagonalTorusDefiningIdeal k n) (CommAlgCat.of k K) := by
  let e := pointsMulEquiv (R := k) (A := K) n
  ext g
  rw [mem_quotientPointsSubgroup_diagonalTorusDefiningIdeal_iff,
    ← TauCeti.mem_diagonalTorus_iff, ← TauCeti.centralizer_diagonalTorus]
  simp only [Subgroup.mem_centralizer_iff]
  constructor
  · intro hg m hm
    have hd := (mem_quotientPointsSubgroup_diagonalTorusDefiningIdeal_iff
      k n K (e.symm m)).mpr (by
        simpa only [e, MulEquiv.apply_symm_apply] using TauCeti.mem_diagonalTorus_iff.mp hm)
    have h := congrArg e (hg (e.symm m) hd)
    simpa only [map_mul, MulEquiv.apply_symm_apply] using h
  · intro hg d hd
    apply e.injective
    exact (map_mul e d g).trans <|
      (hg (e d) (TauCeti.mem_diagonalTorus_iff.mpr
        ((mem_quotientPointsSubgroup_diagonalTorusDefiningIdeal_iff k n K d).mp hd))).trans
          (map_mul e g d).symm

/-- **The diagonal torus of `GL_n` is maximal among reduced commutative closed subgroup
schemes over every field.**

If `I` cuts out a reduced commutative closed subgroup containing the diagonal torus, then `I` is
the diagonal-torus defining ideal. Containment is written contravariantly as
`I ≤ diagonalTorusDefiningIdeal k n`; commutativity is the cocommutativity of the quotient
coordinate Hopf algebra. Reducedness over `k` suffices: point separation uses maps into an
algebraic closure, without requiring geometric reducedness. -/
theorem eq_diagonalTorusDefiningIdeal_of_le_of_isCocomm
    (I : HopfIdeal k (coordinateHopfAlgebra k n))
    [IsReduced (CommHopfAlgCat.quotient (coordinateHopfAlgebra k n) I)]
    [Coalgebra.IsCocomm k (CommHopfAlgCat.quotient (coordinateHopfAlgebra k n) I)]
    (hI : I ≤ diagonalTorusDefiningIdeal k n) :
    I = diagonalTorusDefiningIdeal k n :=
  HopfIdeal.eq_of_le_of_centralizer_quotientPointsSubgroup hI
    (centralizer_quotientPointsSubgroup_diagonalTorusDefiningIdeal k n (AlgebraicClosure k))

/-- **The diagonal torus of `GL_n` is a maximal torus over every field.** Its points over an
algebraic closure are self-centralizing, so the geometric-point criterion applies. -/
@[grind =>]
theorem isMaximalTorus_diagonalTorusDefiningIdeal :
    HopfIdeal.IsMaximalTorus k (coordinateHopfAlgebra k n)
      (diagonalTorusDefiningIdeal k n) :=
  HopfIdeal.isMaximalTorus_of_centralizer_quotientPointsSubgroup
    (torusCommHopfAlgProperty_quotient_diagonalTorusDefiningIdeal k n)
    (centralizer_quotientPointsSubgroup_diagonalTorusDefiningIdeal k n (AlgebraicClosure k))

end

end TauCeti.GeneralLinear
