/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.ProjectiveGeneralLinear.UpperTriangular.Basic
public import TauCeti.Algebra.AlgebraicGroup.Borel.Basic
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.UpperTriangular.SmoothConnected
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Image.FaithfullyFlat
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Image.Smooth
import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.FaithfullyFlatPoints
import TauCeti.Algebra.AlgebraicGroup.Solvable.Reduced
import TauCeti.Algebra.AlgebraicGroup.Solvable.UpperTriangular

/-!
# Geometry and geometric points of the projective upper-triangular subgroup

The closed image of the general-linear upper-triangular group in `PGLₙ` is smooth,
geometrically connected, and geometrically solvable over every field. Its geometric
points are exactly conjugations by upper-triangular invertible matrices. In particular,
this is a Borel candidate with the expected points, in every characteristic and rank.
The point characterization is stated over algebraically closed value fields: over a
general value algebra the image of a group-scheme morphism need not be its pointwise image.

The proofs descend the three geometric properties along `CommHopfAlgCat.imageι`,
and use `CommHopfAlgCat.faithfullyFlat_imageι` to lift geometric points.

## References

* J. S. Milne, *Algebraic Groups* (2017), Sections 5.a and 17.a.
* A. Borel, *Linear Algebraic Groups*, second edition, Section 11.
-/

public section

open CategoryTheory

namespace TauCeti.ProjectiveGeneralLinear.UpperTriangular

universe u w

noncomputable section

variable (k : Type u) [Field k] (n : ℕ)

/-- The projective upper-triangular subgroup is smooth over every field. -/
instance instSmoothCoordinateHopfAlgebra : Algebra.Smooth k (coordinateHopfAlgebra k n) :=
  (smoothCommHopfAlgProperty_iff _).mp
    (smoothCommHopfAlgProperty.image (restriction k n)
      (GeneralLinear.UpperTriangular.smoothCommHopfAlgProperty_coordinateHopfAlgebra n k))

/-- The projective upper-triangular subgroup is geometrically connected. -/
theorem geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra :
    geometricallyConnectedCommHopfAlgProperty k (coordinateHopfAlgebra k n) :=
  geometricallyConnectedCommHopfAlgProperty.image (restriction k n)
    (GeneralLinear.UpperTriangular.geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra
      n k)

/-- The projective upper-triangular subgroup has solvable geometric point group. -/
theorem geometricallySolvablePointsCommHopfAlgProperty_coordinateHopfAlgebra :
    geometricallySolvablePointsCommHopfAlgProperty k (coordinateHopfAlgebra k n) :=
  geometricallySolvablePointsCommHopfAlgProperty.of_injective_of_smooth
    (conjugationMap k n) (CommHopfAlgCat.imageι_injective (restriction k n))
    ((smoothCommHopfAlgProperty_iff _).mp
      (GeneralLinear.UpperTriangular.smoothCommHopfAlgProperty_coordinateHopfAlgebra n k)) <|
  GeneralLinear.UpperTriangular.geometricallySolvablePointsCommHopfAlgProperty_coordinateHopfAlgebra
    k n

/-- The projective upper-triangular closed subgroup is a Borel candidate:
it is smooth, geometrically connected, and geometrically solvable. -/
theorem isBorelCandidate_definingHopfIdeal :
    HopfIdeal.IsBorelCandidate k
      (FiniteTypeCommHopfAlgCat.of k (ProjectiveGeneralLinear.coordinateHopfAlgebra n k))
      (definingHopfIdeal k n) :=
  .mk ((smoothCommHopfAlgProperty_iff _).mpr inferInstance)
    (geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra k n)
    (geometricallySolvablePointsCommHopfAlgProperty_coordinateHopfAlgebra k n)

/-- Conjugation from the general-linear upper-triangular group onto its projective
closed image is faithfully flat. -/
theorem faithfullyFlat_conjugationMap :
    (conjugationMap k n).hom.toAlgHom.toRingHom.FaithfullyFlat := by
  let _ : Algebra.Smooth k (GeneralLinear.UpperTriangular.coordinateHopfAlgebra k n) :=
    (smoothCommHopfAlgProperty_iff _).mp
      (GeneralLinear.UpperTriangular.smoothCommHopfAlgProperty_coordinateHopfAlgebra n k)
  let _ := isGeometricallyReduced_of_smooth k
    (GeneralLinear.UpperTriangular.coordinateHopfAlgebra k n)
  exact CommHopfAlgCat.faithfullyFlat_imageι (restriction k n)

/-- Over an algebraically closed value field, the points cut out by the projective
upper-triangular ideal are exactly inner automorphisms by upper-triangular matrices. -/
@[simp↓ high]
theorem mem_definingPointsSubgroup_iff (L : Type w) [Field L] [Algebra k L] [IsAlgClosed L]
    (q : HopfAlgebra.points (R := k)
      (H := ProjectiveGeneralLinear.coordinateHopfAlgebra n k) (CommAlgCat.of k L)) :
    q ∈ CommHopfAlgCat.quotientPointsSubgroup
        (ProjectiveGeneralLinear.coordinateHopfAlgebra n k) (definingHopfIdeal k n)
        (CommAlgCat.of k L) ↔
      ∃ g : upperTriangularGroup (Fin n) L,
        Matrix.GeneralLinearGroup.innerAut (g : Matrix.GeneralLinearGroup (Fin n) L) =
          ProjectiveGeneralLinear.pointsMulEquiv n k (CommAlgCat.of k L) q := by
  have hmap := CommHopfAlgCat.mapPointsFunctor_eq_quotientPointsHom_of_mkQuotient_comp
    (definingHopfIdeal k n) (conjugationMap k n) (restriction k n)
    (coordinateMap_comp_conjugationMap k n) (CommAlgCat.of k L)
  constructor
  · intro hq
    obtain ⟨p, hp⟩ := hq
    obtain ⟨f, hf⟩ := CommHopfAlgCat.mapPointsFunctor_app_surjective_of_faithfullyFlat L
      (conjugationMap k n) (CommHopfAlgCat.imageι_finiteType (restriction k n))
      (faithfullyFlat_conjugationMap k n) p
    refine ⟨GeneralLinear.UpperTriangular.pointsMulEquiv (R := k) (n := n) (A := L) f, ?_⟩
    have hq' := (hmap f).trans (congrArg
      (CommHopfAlgCat.quotientPointsHom _ (definingHopfIdeal k n) (CommAlgCat.of k L)) hf)
    rw [hp] at hq'
    exact (pointsMulEquiv_restriction k n f).symm.trans
      (congrArg (ProjectiveGeneralLinear.pointsMulEquiv n k (CommAlgCat.of k L)) hq')
  · rintro ⟨g, hg⟩
    let f := (GeneralLinear.UpperTriangular.pointsMulEquiv (R := k) (n := n) (A := L)).symm g
    have hf : (CommHopfAlgCat.Hom.mapPointsFunctor (restriction k n)).app
        (CommAlgCat.of k L) f = q := by
      apply (ProjectiveGeneralLinear.pointsMulEquiv n k (CommAlgCat.of k L)).injective
      rw [pointsMulEquiv_restriction, MulEquiv.apply_symm_apply]
      exact hg
    rw [← hf]
    exact ⟨_, (hmap f).symm⟩

end

end TauCeti.ProjectiveGeneralLinear.UpperTriangular
