/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Solvable.LieKolchin
public import TauCeti.Algebra.AlgebraicGroup.Derived.Character
public import TauCeti.Algebra.AlgebraicGroup.Derived.Connected
public import TauCeti.Algebra.AlgebraicGroup.Derived.Smooth
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Construction
import TauCeti.Algebra.AlgebraicGroup.Unipotent.ClosedSubgroup
import TauCeti.Algebra.AlgebraicGroup.Unipotent.Reduced
import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.PointAction
import Mathlib.RingTheory.Nilpotent.Lemmas

/-!
# The derived subgroup of a connected solvable group is unipotent

Over an algebraically closed field, the derived closed subgroup of a reduced connected
solvable affine group of finite type is smooth, connected, and unipotent. Consequently it lies
in the unipotent radical. No characteristic restriction is imposed.

Lie--Kolchin triangularizes every ambient representation. Its diagonal entries are characters,
which restrict to one on the derived subgroup; hence every derived point acts by an upper
unitriangular matrix. Reflection of unipotence along closed immersions then gives intrinsic
unipotence of the derived subgroup, rather than just unipotence in ambient representations.

## References

* A. Borel, *Linear Algebraic Groups*, §10.5.
* J. S. Milne, *Algebraic Groups* (2017), §§6d and 16.
-/

public section

open WithConv

namespace TauCeti

universe u

namespace CommHopfAlgCat

variable {k H : Type u} [Field k] [CommRing H] [HopfAlgebra k H]
  [IsAlgClosed k] [Algebra.FiniteType k H] [IsReduced H]
  [ConnectedSpace (PrimeSpectrum H)] [Group.IsSolvable (WithConv (H →ₐ[k] k))]

/-- Every rational point of the derived subgroup of a reduced connected solvable affine group
over an algebraically closed field is unipotent. -/
theorem isUnipotentPoint_derived_of_isSolvable
    (g : WithConv ((H ⧸ (derivedDefiningIdeal (R := k) H).toIdeal) →ₐ[k] k)) :
    HopfAlgebra.IsUnipotentPoint g := by
  apply (HopfAlgebra.isUnipotentPoint_mapDomain_iff_of_surjective
    (Bialgebra.Quotient.mkBialgHom (R := k) (derivedDefiningIdeal (R := k) H).toIdeal)
    Ideal.Quotient.mk_surjective g).mp
  rw [HopfAlgebra.isUnipotentPoint_iff_forall_isNilpotent_endOfPoint_sub_one]
  intro M
  obtain ⟨n, b, htri, hdiag⟩ :=
    Comodule.exists_basis_coefficientMatrix_isUpperTriangular_of_isSolvable
      (k := k) (H := H) (M := M)
  let f := g.ofConv.comp (Ideal.Quotient.mkₐ k (derivedDefiningIdeal (R := k) H).toIdeal)
  have hu : ((Comodule.coefficientMatrix (C := H) b).map f).IsUpperUnitriangular := by
    rw [Matrix.isUpperUnitriangular_def]
    refine ⟨htri.map f, fun i ↦ ?_⟩
    have hzero : f (Comodule.coefficientMatrix (C := H) b i i - 1) = 0 := by
      have hmem : Comodule.coefficientMatrix (C := H) b i i - 1 ∈
          (derivedDefiningIdeal (R := k) H).toIdeal :=
        HopfIdeal.mem_toIdeal.mpr (GroupLike.sub_one_mem_derivedDefiningIdeal
          (⟨Comodule.coefficientMatrix (C := H) b i i, hdiag i⟩ : GroupLike k H))
      have hq := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
      simp only [f, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, hq, map_zero]
    simpa only [map_sub, map_one, sub_eq_zero, Matrix.map_apply] using hzero
  rw [← LinearMap.isNilpotent_toMatrix_iff (b.baseChange k),
    _root_.map_sub (LinearMap.toMatrix (b.baseChange k) (b.baseChange k)),
    LinearMap.toMatrix_one, Comodule.toMatrix_endOfPoint]
  simpa only [AlgHom.mapDomain_apply, ofConv_toConv,
    Bialgebra.Quotient.mkBialgHom_toAlgHom] using hu.isNilpotent_sub_one

/-- The derived subgroup of a reduced connected solvable affine group over an algebraically
closed field is geometrically unipotent. -/
theorem geometricallyUnipotentPointsCommHopfAlgProperty_derived_of_isSolvable :
    geometricallyUnipotentPointsCommHopfAlgProperty k
      (quotient (_root_.CommHopfAlgCat.of k H) (derivedDefiningIdeal (R := k) H)) := by
  let A := _root_.CommHopfAlgCat.of k H
  let D := quotient A (derivedDefiningIdeal (R := k) H)
  let _ : IsReduced D := isReduced_quotient_derivedDefiningIdeal A
  apply (geometricallyUnipotentPointsCommHopfAlgProperty.iff_forall_isUnipotentPoint
    (A := D) k).mpr
  intro g
  exact isUnipotentPoint_derived_of_isSolvable g

/-- The derived subgroup of a reduced connected solvable affine group is a connected normal
smooth unipotent subgroup, so it is a candidate for its unipotent radical. -/
theorem isUnipotentRadicalCandidate_derived_of_isSolvable :
    HopfIdeal.IsUnipotentRadicalCandidate (FiniteTypeCommHopfAlgCat.of k H)
      (derivedDefiningIdeal (R := k) H) := by
  refine HopfIdeal.IsUnipotentRadicalCandidate.mk
    (isNormal_derivedDefiningIdeal (_root_.CommHopfAlgCat.of k H))
    (geometricallyConnectedCommHopfAlgProperty_derived H) ?_
  rw [smoothUnipotentCommHopfAlgProperty_iff]
  exact ⟨(smoothCommHopfAlgProperty_iff _).mp
      (smoothCommHopfAlgProperty_quotient_derivedDefiningIdeal (_root_.CommHopfAlgCat.of k H)),
    (geometricallyUnipotentPointsCommHopfAlgProperty_iff k _).mp
      (geometricallyUnipotentPointsCommHopfAlgProperty_derived_of_isSolvable (k := k) (H := H))⟩

/-- The unipotent radical of a reduced connected solvable affine group over an algebraically
closed field contains its derived subgroup. The inclusion reverses on defining Hopf ideals. -/
theorem unipotentRadicalDefiningIdeal_le_derivedDefiningIdeal_of_isSolvable :
    FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal (FiniteTypeCommHopfAlgCat.of k H) ≤
      derivedDefiningIdeal (R := k) H :=
  FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal_le _ _
    isUnipotentRadicalCandidate_derived_of_isSolvable

end CommHopfAlgCat

end TauCeti
