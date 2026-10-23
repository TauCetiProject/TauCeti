/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.UpperTriangular.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Image.Basic
public import TauCeti.Algebra.AlgebraicGroup.ProjectiveGeneralLinear.DiagonalTorus.Basic
public import TauCeti.Algebra.AlgebraicGroup.ProjectiveGeneralLinear.RootSubgroup.Basic

/-!
# The upper-triangular closed subgroup of `PGLₙ`

Over a field, take the closed image of the upper-triangular subgroup of `GLₙ` under
conjugation on the matrix algebra. Its coordinate algebra is the quotient of `O(PGLₙ)`
by the kernel of restriction to the general-linear upper-triangular group. The positive
root maps and the normalized diagonal torus factor through this quotient. These are
scheme-theoretic factorizations, valid on all value algebras, including nonreduced ones.

This constructs the closed subgroup used for the standard Borel of the adjoint group;
Borel maximality is a separate assertion. The construction uses
`ProjectiveGeneralLinear.conjugationMap` and the quotient-by-kernel factorization
`CommHopfAlgCat.image`.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 17 and 21.
* A. Borel, *Linear Algebraic Groups*, second edition, Section 11.
-/

public section

open CategoryTheory

namespace TauCeti.ProjectiveGeneralLinear.UpperTriangular

universe u w

noncomputable section

section Restriction

variable (k : Type u) [CommRing k] (n : ℕ)

/-- Restriction from the projective group to the general-linear upper-triangular group. -/
def restriction : ProjectiveGeneralLinear.coordinateHopfAlgebra n k ⟶
    GeneralLinear.UpperTriangular.coordinateHopfAlgebra k n :=
  conjugationMap n k ≫ GeneralLinear.UpperTriangular.coordinateMap k n

/-- Restriction is conjugation followed, contravariantly, by upper-triangular restriction. -/
theorem restriction_def : restriction k n =
    conjugationMap n k ≫ GeneralLinear.UpperTriangular.coordinateMap k n := (rfl)

/-- Restriction sends a projective coordinate to the upper-triangular quotient class
of its conjugation coordinate. -/
theorem restriction_apply (x : ProjectiveGeneralLinear.coordinateHopfAlgebra n k) :
    (restriction k n).hom x = Ideal.Quotient.mkₐ k
      (GeneralLinear.UpperTriangular.definingHopfIdeal k n).toIdeal
      ((ProjectiveGeneralLinear.conjugationMap n k).hom x) := by
  rw [restriction_def, _root_.CommHopfAlgCat.hom_comp, BialgHom.comp_apply]
  exact GeneralLinear.UpperTriangular.coordinateMap_apply k n _

variable {A : Type w} [CommRing A] [Algebra k A]

/-- Restriction on points is conjugation after the upper-triangular quotient-point inclusion. -/
theorem mapPointsFunctor_restriction
    (f : HopfAlgebra.points (R := k)
      (H := GeneralLinear.UpperTriangular.coordinateHopfAlgebra k n) (CommAlgCat.of k A)) :
    (CommHopfAlgCat.Hom.mapPointsFunctor (restriction k n)).app (CommAlgCat.of k A) f =
      WithConv.toConv ((CommHopfAlgCat.quotientPointsHom
        (GeneralLinear.coordinateHopfAlgebra k n)
        (GeneralLinear.UpperTriangular.definingHopfIdeal k n) (CommAlgCat.of k A) f).ofConv.comp
          ((ProjectiveGeneralLinear.conjugationMap n k).hom :
            ProjectiveGeneralLinear.coordinateHopfAlgebra n k →ₐ[k]
              GeneralLinear.coordinateHopfAlgebra k n)) := by
  apply WithConv.ofConv_injective
  ext x
  rw [CommHopfAlgCat.Hom.mapPointsFunctor_app_apply_apply, restriction_apply,
    WithConv.ofConv_toConv, AlgHom.comp_apply, CommHopfAlgCat.quotientPointsHom_apply_apply,
    BialgHom.coe_toAlgHom]

/-- Restriction on points sends an upper-triangular matrix to its inner automorphism. -/
@[simp]
theorem pointsMulEquiv_restriction
    (f : HopfAlgebra.points (R := k)
      (H := GeneralLinear.UpperTriangular.coordinateHopfAlgebra k n) (CommAlgCat.of k A)) :
    ProjectiveGeneralLinear.pointsMulEquiv n k (CommAlgCat.of k A)
        ((CommHopfAlgCat.Hom.mapPointsFunctor (restriction k n)).app (CommAlgCat.of k A) f) =
      Matrix.GeneralLinearGroup.innerAut
        (GeneralLinear.UpperTriangular.pointsMulEquiv (R := k) (n := n) (A := A) f :
          Matrix.GeneralLinearGroup (Fin n) A) := by
  rw [mapPointsFunctor_restriction, ProjectiveGeneralLinear.pointsMulEquiv_conjugationMap,
    GeneralLinear.pointsMulEquiv_apply, GeneralLinear.UpperTriangular.pointsMulEquiv_coe]

end Restriction

variable (k : Type u) [Field k] (n : ℕ)

/-- The defining Hopf ideal of the closed image of the upper-triangular general-linear group. -/
abbrev definingHopfIdeal : HopfIdeal k (ProjectiveGeneralLinear.coordinateHopfAlgebra n k) :=
  HopfIdeal.ker (restriction k n).hom

/-- A projective coordinate vanishes on the closed image exactly when its conjugation
coordinate vanishes on the general-linear upper-triangular group. -/
@[simp↓]
theorem mem_definingHopfIdeal (x : ProjectiveGeneralLinear.coordinateHopfAlgebra n k) :
    x ∈ definingHopfIdeal k n ↔
      (conjugationMap n k).hom x ∈ GeneralLinear.UpperTriangular.definingHopfIdeal k n := by
  rw [HopfIdeal.mem_ker, restriction_apply]
  exact Ideal.Quotient.eq_zero_iff_mem

/-- The coordinate Hopf algebra of the projective upper-triangular closed subgroup. -/
abbrev coordinateHopfAlgebra : _root_.CommHopfAlgCat.{u} k :=
  CommHopfAlgCat.quotient (ProjectiveGeneralLinear.coordinateHopfAlgebra n k)
    (definingHopfIdeal k n)

/-- The closed-subgroup inclusion, in coordinates. -/
abbrev coordinateMap : ProjectiveGeneralLinear.coordinateHopfAlgebra n k ⟶
    coordinateHopfAlgebra k n :=
  CommHopfAlgCat.mkQuotient _ (definingHopfIdeal k n)

/-- The coordinate morphism `O(PBₙ) → O(Bₙ)` of the quotient map from the general-linear
upper-triangular group onto its projective image. -/
abbrev conjugationMap : coordinateHopfAlgebra k n ⟶
    GeneralLinear.UpperTriangular.coordinateHopfAlgebra k n :=
  CommHopfAlgCat.imageι (restriction k n)

/-- The upper-triangular conjugation map recovers ambient conjugation after inclusion. -/
@[reassoc]
theorem coordinateMap_comp_conjugationMap :
    coordinateMap k n ≫ conjugationMap k n = restriction k n :=
  CommHopfAlgCat.mkImage_comp_imageι _

variable {n} {i j : Fin n}

/-- The positive elementary root map, factored through the projective upper-triangular group. -/
def rootSubgroupCoordinateMap (hij : i < j) :
    coordinateHopfAlgebra k n ⟶ AdditiveGroup.coordinateHopfAlgebra k :=
  CommHopfAlgCat.liftQuotient (definingHopfIdeal k n)
    (ProjectiveGeneralLinear.rootSubgroupCoordinateMap hij.ne) (by
      intro x hx
      have hkill := CommHopfAlgCat.toIdeal_le_ker_of_mkQuotient_comp
        (I := GeneralLinear.UpperTriangular.definingHopfIdeal k n)
        (g := GeneralLinear.UpperTriangular.rootSubgroupCoordinateMap k hij)
        (f := GeneralLinear.rootSubgroupCoordinateMap hij.ne)
        (by rw [← GeneralLinear.UpperTriangular.coordinateMap_def,
          GeneralLinear.UpperTriangular.coordinateMap_comp_rootSubgroupCoordinateMap])
      simp only [RingHom.mem_ker, AlgHom.toRingHom_eq_coe,
        ProjectiveGeneralLinear.rootSubgroupCoordinateMap_def, _root_.CommHopfAlgCat.hom_comp]
      exact RingHom.mem_ker.mp (hkill ((mem_definingHopfIdeal k n x).mp hx)))

/-- Inclusion after a factored positive root map gives the ambient elementary root map. -/
@[reassoc (attr := simp)]
theorem coordinateMap_comp_rootSubgroupCoordinateMap (hij : i < j) :
    coordinateMap k n ≫ rootSubgroupCoordinateMap k hij =
      ProjectiveGeneralLinear.rootSubgroupCoordinateMap hij.ne :=
  CommHopfAlgCat.mkQuotient_comp_liftQuotient _ _ _

/-- Conjugation carries each positive general-linear root map to its projective root map. -/
@[reassoc]
theorem conjugationMap_comp_rootSubgroupCoordinateMap (hij : i < j) :
    conjugationMap k n ≫ GeneralLinear.UpperTriangular.rootSubgroupCoordinateMap k hij =
      rootSubgroupCoordinateMap k hij := by
  apply CommHopfAlgCat.mkQuotient_hom_ext (H :=
    ProjectiveGeneralLinear.coordinateHopfAlgebra n k) (I := definingHopfIdeal k n)
  -- Quotient extensionality produces mkQuotient; name it coordinateMap so the factorization
  -- lemmas match without unfolding the maps being compared.
  change coordinateMap k n ≫ _ = coordinateMap k n ≫ _
  rw [coordinateMap_comp_conjugationMap_assoc, restriction_def, Category.assoc,
    GeneralLinear.UpperTriangular.coordinateMap_comp_rootSubgroupCoordinateMap,
    coordinateMap_comp_rootSubgroupCoordinateMap,
    ProjectiveGeneralLinear.rootSubgroupCoordinateMap_def]

/-- The defining ideal is killed by the normalized diagonal torus of `PGL_{r+1}`. -/
theorem definingHopfIdeal_le_ker_diagonalTorusCoordinateMap (r : ℕ) :
    (definingHopfIdeal k (r + 1)).toIdeal ≤
      RingHom.ker (ProjectiveGeneralLinear.diagonalTorusCoordinateMap r k).hom.toAlgHom := by
  intro x hx
  exact ProjectiveGeneralLinear.comap_upperTriangularIdeal_le_ker_diagonalTorusCoordinateMap
    r k ((mem_definingHopfIdeal k (r + 1) x).mp hx)

/-- The coordinate morphism `O(PB_{r+1}) → O(T)` of the inclusion of the normalized
diagonal torus into the projective upper-triangular group. -/
def diagonalTorusCoordinateMap (r : ℕ) :
    coordinateHopfAlgebra k (r + 1) ⟶
      (DiagonalizableGroup.coordinateRing k
        (SplitTorus.characterGroup (ULift.{u} (Fin r)))).obj :=
  CommHopfAlgCat.liftQuotient (definingHopfIdeal k (r + 1))
    (ProjectiveGeneralLinear.diagonalTorusCoordinateMap r k)
    (definingHopfIdeal_le_ker_diagonalTorusCoordinateMap k r)

/-- Inclusion after the factored diagonal torus gives the ambient normalized diagonal torus. -/
@[reassoc (attr := simp)]
theorem coordinateMap_comp_diagonalTorusCoordinateMap (r : ℕ) :
    coordinateMap k (r + 1) ≫ diagonalTorusCoordinateMap k r =
      ProjectiveGeneralLinear.diagonalTorusCoordinateMap r k :=
  CommHopfAlgCat.mkQuotient_comp_liftQuotient _ _ _

end

end TauCeti.ProjectiveGeneralLinear.UpperTriangular
