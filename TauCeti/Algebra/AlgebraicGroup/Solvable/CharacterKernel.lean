/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.CharacterKernel
public import TauCeti.Algebra.AlgebraicGroup.Solvable.LieKolchin
public import TauCeti.Algebra.AlgebraicGroup.Representation.UnipotentPoint.Character
import TauCeti.Algebra.AlgebraicGroup.Unipotent.ClosedSubgroup
import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.PointAction
import Mathlib.RingTheory.Nilpotent.Lemmas

/-!
# The character kernel of a connected solvable group is unipotent

Over an algebraically closed field, a point of a reduced connected solvable affine group of
finite type is unipotent precisely when every algebraic character evaluates to one. Thus the
common kernel of characters has geometrically unipotent points. No smoothness or reducedness
of that kernel is assumed.

Lie--Kolchin makes every representation upper triangular with characters on the diagonal;
trivial character values make its point action upper unitriangular. The triangular argument is
shared with `CommHopfAlgCat.isUnipotentPoint_derived_of_isSolvable`. The kernel identifies the
unipotent obstruction to detecting a connected solvable group by its characters.

## References

* A. Borel, *Linear Algebraic Groups*, §10.
* T. A. Springer, *Linear Algebraic Groups*, §6.3.
-/

public section

open WithConv

namespace TauCeti

universe u v w

section Point

variable {k : Type u} {H : Type v} [Field k] [CommRing H] [HopfAlgebra k H]
  [IsAlgClosed k] [Algebra.FiniteType k H] [IsReduced H]
  [ConnectedSpace (PrimeSpectrum H)] [Group.IsSolvable (WithConv (H →ₐ[k] k))]

namespace HopfAlgebra

/-- In a reduced connected solvable affine group over an algebraically closed field, a point
valued in any reduced commutative algebra is unipotent exactly when every algebraic character
has value one. -/
theorem isUnipotentPoint_iff_forall_apply_groupLike_eq_one
    {K : Type w} [CommRing K] [IsReduced K] [Algebra k K] (g : WithConv (H →ₐ[k] K)) :
    IsUnipotentPoint g ↔ ∀ x : GroupLike k H, g.ofConv x = 1 := by
  refine ⟨fun hg x ↦ hg.apply_groupLike_eq_one x, fun hg ↦ ?_⟩
  rw [isUnipotentPoint_iff_forall_isNilpotent_endOfPoint_sub_one]
  intro M
  obtain ⟨n, b, htri, hdiag⟩ :=
    Comodule.exists_basis_coefficientMatrix_isUpperTriangular_of_isSolvable
      (k := k) (H := H) (M := M)
  have hu : ((Comodule.coefficientMatrix (C := H) b).map g.ofConv).IsUpperUnitriangular := by
    rw [Matrix.isUpperUnitriangular_def]
    exact ⟨htri.map g.ofConv, fun i ↦ hg ⟨_, hdiag i⟩⟩
  rw [← LinearMap.isNilpotent_toMatrix_iff (b.baseChange K),
    _root_.map_sub (LinearMap.toMatrix (b.baseChange K) (b.baseChange K)),
    LinearMap.toMatrix_one, Comodule.toMatrix_endOfPoint]
  exact hu.isNilpotent_sub_one

end HopfAlgebra

end Point

namespace CommHopfAlgCat

variable {k H : Type u} [Field k] [CommRing H] [HopfAlgebra k H]
  [IsAlgClosed k] [Algebra.FiniteType k H] [IsReduced H]
  [ConnectedSpace (PrimeSpectrum H)] [Group.IsSolvable (WithConv (H →ₐ[k] k))]

/-- Every geometric point of the common kernel of characters of a reduced connected solvable
affine group is unipotent. The kernel may be nonreduced. -/
theorem geometricallyUnipotentPointsCommHopfAlgProperty_characterKernelIdeal :
    geometricallyUnipotentPointsCommHopfAlgProperty k
      (_root_.CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of k H)
        (_root_.CommHopfAlgCat.characterKernelIdeal (_root_.CommHopfAlgCat.of k H))) := by
  rw [geometricallyUnipotentPointsCommHopfAlgProperty_iff]
  intro g
  let A := _root_.CommHopfAlgCat.of k H
  let I := _root_.CommHopfAlgCat.characterKernelIdeal A
  let q := (_root_.CommHopfAlgCat.mkQuotient A I).hom
  apply (HopfAlgebra.isUnipotentPoint_mapDomain_iff_of_surjective q
    (_root_.CommHopfAlgCat.mkQuotient_surjective A I) g).mp
  rw [HopfAlgebra.isUnipotentPoint_iff_forall_apply_groupLike_eq_one]
  intro x
  have hx : q x = 1 := by
    have hzero := (_root_.CommHopfAlgCat.mkQuotient_eq_zero_iff A I ((x : H) - 1)).mpr
      (_root_.CommHopfAlgCat.sub_one_mem_characterKernelIdeal A x)
    simpa only [map_sub, map_one, sub_eq_zero] using hzero
  simp only [AlgHom.comp_apply, BialgHom.coe_toAlgHom, hx, map_one]

end CommHopfAlgCat

end TauCeti
