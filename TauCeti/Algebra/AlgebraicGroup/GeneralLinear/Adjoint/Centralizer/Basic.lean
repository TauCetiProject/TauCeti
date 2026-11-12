/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Submonoid.Units
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Adjoint.Comodule
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Basic
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Orbit

/-!
# Centralizers of matrices in the general linear group

Let `X` be an `n × n` matrix over a field `k`, viewed as an element `x` of the Lie algebra of
`GLₙ` through `TauCeti.GeneralLinear.cotangentDualMatrixEquiv`, so `X = cotangentDualMatrixEquiv x`.
Its centralizer `C_GL(X)` is the closed subgroup `TauCeti.centralizerHopfIdeal` of `GLₙ` fixing
`X` under the adjoint action. This file identifies it with the unit group of the matrix
centralizer algebra `Z(X) = {Y | X Y = Y X}`:

* over every commutative `k`-algebra `A`, including nonreduced ones, a point of `GLₙ` lies in
  `C_GL(X)` exactly when its matrix commutes with `X`, and the `A`-points of `C_GL(X)` form the
  unit group of the centralizer of `X` in `Matrix (Fin n) (Fin n) A`;
* in characteristic zero, `dim C_GL(X) = dim_k Z(X)`;
* over an algebraically closed field of characteristic zero, the adjoint orbit of `X` has
  dimension `n² - dim_k Z(X)`.

The dimension statements specialize the general centralizer and orbit dimension formulas to `GLₙ`,
through the identification of its Lie algebra with matrices and of `ker (ad X)` with `Z(X)`.
For a nilpotent `X`, the dimension of `Z(X)` is computed from the kernels of the powers of `X`,
that is from its Jordan type, by `Module.End.finrank_centralizer_eq_sum_sq_ker`.

## Main declarations

* `TauCeti.GeneralLinear.map_cotangentDualMatrixEquiv_ker_ad`: `ker (ad X)` is the matrix
  centralizer of `X`.
* `TauCeti.GeneralLinear.centralizerHopfIdeal_le_ker_iff_commute` and
  `TauCeti.GeneralLinear.mem_quotientPointsSubgroup_centralizerHopfIdeal_iff`: the points of
  `C_GL(X)` are the invertible matrices commuting with `X`.
* `TauCeti.GeneralLinear.centralizerPointsMulEquivUnits`: the `A`-points of `C_GL(X)` are the
  units of the centralizer of `X` in `Matrix (Fin n) (Fin n) A`.
* `TauCeti.GeneralLinear.ringKrullDim_quotient_centralizerHopfIdeal_eq_finrank_centralizer`:
  in characteristic zero, `dim C_GL(X) = dim_k Z(X)`.
* `TauCeti.GeneralLinear.topologicalKrullDim_range_projectiveOrbitMap_add_finrank_centralizer`:
  over an algebraically closed field of characteristic zero, `dim (GLₙ • X) + dim_k Z(X) = n²`.

## References

* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*, Van
  Nostrand Reinhold, 1993, §6.1, for centralizers and orbit dimensions of nilpotent matrices.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 10, for centralizers as stabilizers under the
  adjoint representation.
-/

public section

namespace TauCeti.GeneralLinear

universe u w

section Lie

variable {k : Type u} [CommRing k] {n : ℕ}

/-- The kernel of `ad x` in the Lie algebra of `GLₙ` is the centralizer of the matrix of `x`. -/
theorem map_cotangentDualMatrixEquiv_ker_ad
    (x : Module.Dual k (Bialgebra.CotangentSpace k (coordinateHopfAlgebra k n))) :
    (LinearMap.ker (LieAlgebra.ad k _ x)).map
        (cotangentDualMatrixEquiv (k := k) (n := n)).toLinearMap =
      Subalgebra.toSubmodule (Subalgebra.centralizer k {cotangentDualMatrixEquiv x}) := by
  ext Y
  obtain ⟨y, rfl⟩ := cotangentDualMatrixEquiv.surjective Y
  rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply, LinearMap.mem_ker,
    LieAlgebra.ad_apply, ← cotangentDualMatrixEquiv.injective.eq_iff, map_zero,
    cotangentDualMatrixEquiv_lie, sub_eq_zero, Subalgebra.mem_toSubmodule,
    Subalgebra.mem_centralizer_iff, Set.forall_mem_singleton, eq_comm]

end Lie

section Points

variable {k : Type u} [Field k] {n : ℕ} {A : Type w} [CommRing A] [Algebra k A]

/-- **The points of the centralizer of a matrix.** A point of `GLₙ` with values in any commutative
`k`-algebra lies in the centralizer of `x` exactly when its matrix commutes with the matrix of
`x`. The value algebra may be nonreduced. -/
theorem centralizerHopfIdeal_le_ker_iff_commute
    (x : Module.Dual k (Bialgebra.CotangentSpace k (coordinateHopfAlgebra k n)))
    (g : HopfAlgebra.points (H := coordinateHopfAlgebra k n) (CommAlgCat.of k A)) :
    (centralizerHopfIdeal (coordinateHopfAlgebra k n) x).toIdeal ≤ RingHom.ker g.ofConv ↔
      Commute (pointsMulEquiv n g : Matrix (Fin n) (Fin n) A)
        ((cotangentDualMatrixEquiv x).map (algebraMap k A)) := by
  let := Derivation.adjointComodule (R := k) (H := coordinateHopfAlgebra k n)
  rw [centralizerHopfIdeal_def, Comodule.stabilizerHopfIdeal_le_ker_iff,
    ← (Derivation.tangentScalarExtensionEquiv (R := k) (A := coordinateHopfAlgebra k n)
      (B := A)).injective.eq_iff,
    ← (tangentLinearEquivMatrix (R := k) (B := A) n).injective.eq_iff,
    tangentLinearEquivMatrix_apply, tangentLinearEquivMatrix_apply,
    tangentMatrix_adjointComodule_endOfPoint, tangentMatrix_tangentScalarExtensionEquiv_one_tmul,
    Units.mul_inv_eq_iff_eq_mul, commute_iff_eq]

/-- **The points of the centralizer of a matrix.** A point of `GLₙ` lies in the subgroup cut out
by the centralizer of `x` exactly when its matrix lies in the centralizer of the matrix of `x`. -/
@[simp]
theorem mem_quotientPointsSubgroup_centralizerHopfIdeal_iff
    (x : Module.Dual k (Bialgebra.CotangentSpace k (coordinateHopfAlgebra k n)))
    (g : HopfAlgebra.points (H := coordinateHopfAlgebra k n) (CommAlgCat.of k A)) :
    g ∈ CommHopfAlgCat.quotientPointsSubgroup (coordinateHopfAlgebra k n)
        (centralizerHopfIdeal (coordinateHopfAlgebra k n) x) (CommAlgCat.of k A) ↔
      (pointsMulEquiv n g : Matrix (Fin n) (Fin n) A) ∈
        Subalgebra.centralizer A {(cotangentDualMatrixEquiv x).map (algebraMap k A)} := by
  rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff, Subalgebra.mem_centralizer_iff,
    Set.forall_mem_singleton, ← commute_iff_eq, Commute.symm_iff,
    ← centralizerHopfIdeal_le_ker_iff_commute, IsConcreteLE.le_iff]
  simp only [HopfIdeal.mem_toIdeal, RingHom.mem_ker]

/-- Under `pointsMulEquiv`, the points of the centralizer of `x` are the invertible matrices
whose matrix and inverse lie in the centralizer of the matrix of `x`. -/
theorem map_quotientPointsSubgroup_centralizerHopfIdeal
    (x : Module.Dual k (Bialgebra.CotangentSpace k (coordinateHopfAlgebra k n))) :
    (CommHopfAlgCat.quotientPointsSubgroup (coordinateHopfAlgebra k n)
        (centralizerHopfIdeal (coordinateHopfAlgebra k n) x) (CommAlgCat.of k A)).map
        (pointsMulEquiv n).toMonoidHom =
      (Subalgebra.centralizer A
        {(cotangentDualMatrixEquiv x).map (algebraMap k A)}).toSubmonoid.units := by
  ext u
  rw [Subgroup.mem_map_equiv, Submonoid.mem_units_iff,
    mem_quotientPointsSubgroup_centralizerHopfIdeal_iff,
    MulEquiv.apply_symm_apply]
  refine ⟨fun h ↦ ⟨h, ?_⟩, And.left⟩
  rw [Subalgebra.mem_centralizer_iff, Set.forall_mem_singleton] at h
  exact (Subalgebra.mem_centralizer_iff A).mpr <| Set.forall_mem_singleton.mpr
    ((commute_iff_eq _ _).mpr h).units_inv_right.eq

/-- **The points of the centralizer of a matrix are the units of its centralizer algebra.** Over
every commutative `k`-algebra `A`, the `A`-points of the centralizer of `x` in `GLₙ` are
identified, through their matrices, with the unit group of the centralizer of the matrix of `x`
in `Matrix (Fin n) (Fin n) A`. -/
noncomputable def centralizerPointsMulEquivUnits
    (x : Module.Dual k (Bialgebra.CotangentSpace k (coordinateHopfAlgebra k n)))
    (A : Type w) [CommRing A] [Algebra k A] :
    CommHopfAlgCat.quotientPointsSubgroup (coordinateHopfAlgebra k n)
        (centralizerHopfIdeal (coordinateHopfAlgebra k n) x) (CommAlgCat.of k A) ≃*
      (Subalgebra.centralizer A {(cotangentDualMatrixEquiv x).map (algebraMap k A)})ˣ :=
  ((pointsMulEquiv n).subgroupMap _).trans <|
    (MulEquiv.subgroupCongr (map_quotientPointsSubgroup_centralizerHopfIdeal x)).trans
      (Submonoid.unitsEquivUnitsType _)

/-- The unit of the centralizer algebra attached to a point of the centralizer of `x` is the
matrix of that point. -/
@[simp]
theorem coe_coe_centralizerPointsMulEquivUnits_apply
    (x : Module.Dual k (Bialgebra.CotangentSpace k (coordinateHopfAlgebra k n)))
    (g : CommHopfAlgCat.quotientPointsSubgroup (coordinateHopfAlgebra k n)
        (centralizerHopfIdeal (coordinateHopfAlgebra k n) x) (CommAlgCat.of k A)) :
    ((centralizerPointsMulEquivUnits x A g : Subalgebra.centralizer A
        {(cotangentDualMatrixEquiv x).map (algebraMap k A)}) : Matrix (Fin n) (Fin n) A) =
      (pointsMulEquiv n g.1 : Matrix (Fin n) (Fin n) A) :=
  (rfl)

end Points

section Dimension

variable {k : Type u} [Field k] [CharZero k] {n : ℕ}

/-- **The dimension of the centralizer of a matrix.** Over a field of characteristic zero, the
centralizer of `x` in `GLₙ` has the dimension of the centralizer algebra of the matrix of `x`. -/
theorem ringKrullDim_quotient_centralizerHopfIdeal_eq_finrank_centralizer
    (x : Module.Dual k (Bialgebra.CotangentSpace k (coordinateHopfAlgebra k n))) :
    ringKrullDim (coordinateHopfAlgebra k n ⧸
        (centralizerHopfIdeal (coordinateHopfAlgebra k n) x).toIdeal) =
      Module.finrank k (Subalgebra.centralizer k {cotangentDualMatrixEquiv x}) := by
  rw [ringKrullDim_quotient_centralizerHopfIdeal, ← Subalgebra.finrank_toSubmodule,
    ← map_cotangentDualMatrixEquiv_ker_ad, LinearEquiv.finrank_map_eq]

attribute [local instance] Derivation.adjointComodule Comodule.prodTrivial

/-- **The dimension of the adjoint orbit of a matrix.** Over an algebraically closed field of
characteristic zero, the orbit of `x` under the adjoint action of `GLₙ` has dimension
`n² - dim Z(X)`, where `Z(X)` is the centralizer algebra of the matrix `X` of `x`. -/
theorem topologicalKrullDim_range_projectiveOrbitMap_add_finrank_centralizer [IsAlgClosed k]
    (x : Module.Dual k (Bialgebra.CotangentSpace k (coordinateHopfAlgebra k n))) :
    topologicalKrullDim (Set.range (Comodule.projectiveOrbitMap
        (H := coordinateHopfAlgebra k n)
        ((x, 1) : Module.Dual k (Bialgebra.CotangentSpace k (coordinateHopfAlgebra k n)) × k)
        (Module.isUnimodular_mk_one x))) +
      Module.finrank k (Subalgebra.centralizer k {cotangentDualMatrixEquiv x}) = n * n := by
  rw [topologicalKrullDim_range_projectiveOrbitMap_mk_one_eq_finrank_range_ad,
    ← Subalgebra.finrank_toSubmodule, ← map_cotangentDualMatrixEquiv_ker_ad,
    LinearEquiv.finrank_map_eq]
  norm_cast
  rw [LinearMap.finrank_range_add_finrank_ker, cotangentDualMatrixEquiv.finrank_eq,
    Module.finrank_matrix, Fintype.card_fin, Module.finrank_self, mul_one]

end Dimension

end TauCeti.GeneralLinear
