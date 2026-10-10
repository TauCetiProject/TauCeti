/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.DiagonalTorus.ClosedImmersion
public import TauCeti.Algebra.AlgebraicGroup.Hopf.KernelPoints
public import TauCeti.Algebra.AlgebraicGroup.Torus.Maximal.Points

/-!
# Maximality of the diagonal torus in the general linear group

Over any field, the diagonal torus of `GL_n` is a maximal torus. Over an algebraically closed
field, it is moreover maximal among reduced commutative closed subgroup schemes. In Hopf
coordinates, its defining ideal is the kernel of the surjective restriction morphism from
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
* `TauCeti.GeneralLinear.centralizer_quotientPointsSubgroup_diagonalTorusDefiningIdeal`:
  its geometric points are self-centralizing in the ambient point group.
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

universe u

noncomputable section

variable (k : Type u) [Field k] (n : ℕ)

/-- The Hopf ideal defining the diagonal torus inside the coordinate Hopf algebra of `GL_n`.

It is the ordinary kernel of the surjective restriction morphism to the split-torus coordinate
ring, packaged as a Hopf ideal. -/
noncomputable def diagonalTorusDefiningIdeal :
    HopfIdeal k (coordinateHopfAlgebra k n) :=
  HopfIdeal.kerOfSurjective (diagonalTorusCoordinateMap (R := k) (N := n)).hom
    (diagonalTorusCoordinateMap_surjective k n)

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
    CommHopfAlgCat.quotientKerOfSurjectiveIso (diagonalTorusCoordinateMap (R := k) (N := n))
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
  ObjectProperty.hom_ext _ (CommHopfAlgCat.mkQuotient_comp_quotientKerOfSurjectiveIso_hom _ _)

/-- The base-change isomorphism of `GL_n` coordinate Hopf algebras carries the base-changed
diagonal-torus ideal onto the diagonal-torus ideal over the extended base. -/
@[simp]
theorem map_baseChangeHopfIdeal_diagonalTorusDefiningIdeal
    (K : Type u) [Field K] [Algebra k K] :
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

/-- The points cut out by `diagonalTorusDefiningIdeal` are exactly the diagonal-torus points. -/
theorem quotientPointsSubgroup_diagonalTorusDefiningIdeal (A : CommAlgCat.{u} k) :
    CommHopfAlgCat.quotientPointsSubgroup (coordinateHopfAlgebra k n)
        (diagonalTorusDefiningIdeal k n) A =
      ((CommHopfAlgCat.mapPointsFunctor
        (diagonalTorusCoordinateMap (R := k) (N := n))).app A).hom.range :=
  HopfIdeal.quotientPointsSubgroup_kerOfSurjective_eq_range_mapPointsFunctor _ _ A

variable [IsAlgClosed k]

private instance instNontrivialUnitsOfInfiniteField {F : Type*} [Field F] [Infinite F] :
    Nontrivial Fˣ := by
  let U := {x : F // x ∈ ({0} : Set F)ᶜ}
  let _ : Infinite U := (Set.toFinite ({0} : Set F)).infinite_compl.to_subtype
  obtain ⟨x, y, hxy⟩ := exists_pair_ne U
  refine ⟨Units.mk0 x (by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using x.property),
    Units.mk0 y (by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using y.property), ?_⟩
  intro h
  apply hxy
  apply Subtype.ext
  exact congrArg Units.val h

omit [IsAlgClosed k] in
private theorem pointsMulEquiv_diagonalTorusPoints_symm (t : Fin n → kˣ) :
    pointsMulEquiv (R := k) (A := k) n
        (diagonalTorusPoints
          ((SplitTorus.pointsMulEquiv (R := k) (A := k)).symm
            (fun i : ULift.{u} (Fin n) ↦ t i.down))) =
      diagGL t := by
  rw [pointsMulEquiv_diagonalTorusPoints]
  congr 1
  funext i
  rw [diagonalTorusCoordinates_apply]
  exact congrFun
    ((SplitTorus.pointsMulEquiv (R := k) (A := k)).apply_symm_apply
      (fun j : ULift.{u} (Fin n) ↦ t j.down)) (ULift.up i)

omit [IsAlgClosed k] in
/-- The canonical point equivalence identifies the diagonal closed subgroup with the subgroup
of invertible diagonal matrices. -/
theorem pointsMulEquiv_mem_diagonalTorus_iff
    (g : HopfAlgebra.points (R := k) (H := coordinateHopfAlgebra k n) (CommAlgCat.of k k)) :
    pointsMulEquiv (R := k) (A := k) n g ∈ TauCeti.diagonalTorus k n ↔
      g ∈ CommHopfAlgCat.quotientPointsSubgroup (coordinateHopfAlgebra k n)
        (diagonalTorusDefiningIdeal k n) (CommAlgCat.of k k) := by
  rw [quotientPointsSubgroup_diagonalTorusDefiningIdeal]
  constructor
  · intro hg
    obtain ⟨t, ht⟩ := mem_diagonalTorus_iff_exists_diagGL.mp hg
    refine ⟨(SplitTorus.pointsMulEquiv (R := k) (A := k)).symm
      (fun i : ULift.{u} (Fin n) ↦ t i.down), ?_⟩
    apply (pointsMulEquiv (R := k) (A := k) n).injective
    rw [mapPointsFunctor_diagonalTorusCoordinateMap_app,
      pointsMulEquiv_diagonalTorusPoints_symm]
    exact ht
  · rintro ⟨q, hq⟩
    have hq' : diagonalTorusPoints (A := k) q = g :=
      (mapPointsFunctor_diagonalTorusCoordinateMap_app (CommAlgCat.of k k) q).symm.trans hq
    refine mem_diagonalTorus_iff_exists_diagGL.mpr
      ⟨diagonalTorusCoordinates (SplitTorus.pointsMulEquiv (R := k) (A := k) q), ?_⟩
    exact (pointsMulEquiv_diagonalTorusPoints (R := k) (A := k) (N := n) q).symm.trans
      (congrArg (pointsMulEquiv (R := k) (A := k) n) hq')

/-- The geometric points of the diagonal closed subgroup are self-centralizing in the ambient
point group of `GL_n`. -/
theorem centralizer_quotientPointsSubgroup_diagonalTorusDefiningIdeal :
    Subgroup.centralizer
        (CommHopfAlgCat.quotientPointsSubgroup (coordinateHopfAlgebra k n)
          (diagonalTorusDefiningIdeal k n) (CommAlgCat.of k k) : Set _) =
      CommHopfAlgCat.quotientPointsSubgroup (coordinateHopfAlgebra k n)
        (diagonalTorusDefiningIdeal k n) (CommAlgCat.of k k) := by
  let e := pointsMulEquiv (R := k) (A := k) n
  ext g
  rw [← pointsMulEquiv_mem_diagonalTorus_iff, ← TauCeti.centralizer_diagonalTorus]
  constructor
  · intro hg m hm
    change m ∈ TauCeti.diagonalTorus k n at hm
    have hd := (pointsMulEquiv_mem_diagonalTorus_iff k n (e.symm m)).mp (by
      simpa only [e, MulEquiv.apply_symm_apply] using hm)
    have h := congrArg e (hg (e.symm m) hd)
    simpa only [map_mul, MulEquiv.apply_symm_apply] using h
  · intro hg d hd
    apply e.injective
    exact (map_mul e d g).trans <|
      (hg (e d) ((pointsMulEquiv_mem_diagonalTorus_iff k n d).mpr hd)).trans
        (map_mul e g d).symm

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
    I = diagonalTorusDefiningIdeal k n :=
  HopfIdeal.eq_of_le_of_centralizer_quotientPointsSubgroup hI
    (centralizer_quotientPointsSubgroup_diagonalTorusDefiningIdeal k n)

/-- **The diagonal torus of `GL_n` is a maximal torus.** This packages the stronger result that
no reduced commutative closed subgroup properly containing it exists into the general
Hopf-ideal maximal-torus predicate. -/
private theorem isMaximalTorus_diagonalTorusDefiningIdeal_of_isAlgClosed :
    HopfIdeal.IsMaximalTorus k (coordinateHopfAlgebra k n)
      (diagonalTorusDefiningIdeal k n) :=
  HopfIdeal.isMaximalTorus_of_centralizer_quotientPointsSubgroup
    (torusCommHopfAlgProperty_quotient_diagonalTorusDefiningIdeal k n)
    (centralizer_quotientPointsSubgroup_diagonalTorusDefiningIdeal k n)

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
