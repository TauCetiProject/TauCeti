/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Dynamic.TwoWeylCocharacter
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Root.Adjoint
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Root.Positive
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Root.Staircase

/-!
# The cocharacter `2ρ^∨` of the diagonal torus of the general linear group

For the diagonal torus of `GL_(n+1)` with the upper-triangular base of its diagonal root datum,
the sum of the positive coroots is the cocharacter with coordinates

```text
2ρ^∨ = (n, n - 2, …, -n),   that is   t ↦ diag(t ^ n, t ^ (n - 2), …, t ^ (-n)).
```

The roots of `GL_(n+1)` relative to its diagonal torus are exactly its nontrivial adjoint weights,
so the general description of the dynamic Lie algebras of `2ρ^∨` in
`TauCeti.Algebra.AlgebraicGroup.Dynamic.TwoWeylCocharacter` applies. The Lie algebra of the dynamic
unipotent subgroup `U(2ρ^∨)` is the sum of the positive root spaces, spanned by the matrix units
`E_ij` with `i < j`. The Lie algebra of the dynamic parabolic subgroup `P(2ρ^∨)` is that of the
upper-triangular Borel subgroup: the trivial weight space consists of the diagonal matrices, and
the positive root spaces lie in the Lie algebra of the Borel by the definition of positivity.

## Main declarations

* `TauCeti.GeneralLinear.cocharEquiv_twoWeylCocharacter_diagonalRootBase_apply`: the coordinates
  of `2ρ^∨` are `(n, n - 2, …, -n)`.
* `TauCeti.GeneralLinear.lieSubalgebra_unipotentDefiningHopfIdeal_twoWeylCocharacter`: the Lie
  algebra of `U(2ρ^∨)` is spanned by the matrix units `E_ij` with `i < j`.
* `TauCeti.GeneralLinear.lieSubalgebra_parabolicDefiningHopfIdeal_twoWeylCocharacter`: the Lie
  algebra of `P(2ρ^∨)` is the Lie algebra of the upper-triangular Borel subgroup.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate I.
* J. S. Milne, *Algebraic Groups* (2017), Chapters 13 and 21.
-/

public section

open RootPairing

namespace TauCeti.GeneralLinear

universe u

/-- **The coordinates of `2ρ^∨` for the diagonal torus of `GL_(n+1)` are `(n, n - 2, …, -n)`.**
The roots and coroots of the diagonal root datum have the same coordinates, so `2ρ^∨` has the
coordinates of `2ρ` (`TauCeti.GeneralLinear.twoWeylVector_diagonalRootBase_apply`). -/
theorem cocharEquiv_twoWeylCocharacter_diagonalRootBase_apply (n : ℕ)
    (a : ULift.{u} (Fin (n + 1))) :
    SplitTorus.cocharEquiv
        ((diagonalRootDatum.{u} (n + 1)).twoWeylCocharacter (diagonalRootBase n)) a =
      n - 2 * (a.down : ℕ) := by
  rw [RootPairing.cocharEquiv_twoWeylCocharacter_eq_sum _ (diagonalRootDatum_toLinearMap _),
    Finset.sum_apply,
    ← twoWeylVector_diagonalRootBase_apply, twoWeylVector_def, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [diagonalRootDatum_coroot, diagonalRootDatum_root, coe_diagonalRoot]

variable {k : Type u} [CommRing k] [Nontrivial k]

/-- **The Lie algebra of the dynamic unipotent subgroup of `2ρ^∨` in `GL_(n+1)` is spanned by the
matrix units `E_ij` with `i < j`**, the positive root vectors of the upper-triangular base. -/
theorem lieSubalgebra_unipotentDefiningHopfIdeal_twoWeylCocharacter (n : ℕ) :
    (((diagonalTorusCoordinateMap (R := k) (N := n + 1)).hom.cocharacter
        ((diagonalRootDatum.{u} (n + 1)).twoWeylCocharacter
          (diagonalRootBase n))).unipotentDefiningHopfIdeal.lieSubalgebra (B := k)).toSubmodule =
      (⨆ (p : DiagonalRootIndex.{u} (n + 1)) (_ : p.val.1.down < p.val.2.down),
        k ∙ matrixUnitTangent (k := k) p.val.1.down p.val.2.down).map
        (Derivation.cotangentLinearEquiv (R := k) (A := coordinateHopfAlgebra k (n + 1))
          (B := k)).toLinearMap := by
  rw [BialgHom.lieSubalgebra_unipotentDefiningHopfIdeal_cocharacter_twoWeylCocharacter_toSubmodule
    _ range_ofAdd_diagonalRootDatum_root_eq_nontrivialAdjointWeights.superset]
  refine congrArg _ (iSup_congr fun p ↦ iSup_congr_Prop ?_ fun _ ↦ ?_)
  · rw [mem_posRoots, diagonalRootBase_isPos_iff]
  · have hne : p.val.1.down ≠ p.val.2.down := fun h ↦ p.property (ULift.down_injective h)
    rw [diagonalRootDatum_root, ofAdd_diagonalRoot,
      adjointWeightSpace_matrixUnitWeight_eq_span_singleton hne]

/-- **The Lie algebra of the dynamic parabolic subgroup of `2ρ^∨` in `GL_(n+1)` is the Lie algebra
of the upper-triangular Borel subgroup**: both are the upper-triangular matrices. -/
theorem lieSubalgebra_parabolicDefiningHopfIdeal_twoWeylCocharacter (n : ℕ) :
    ((Cocharacter.parabolicDefiningHopfIdeal
        ((diagonalTorusCoordinateMap (R := k) (N := n + 1)).hom.cocharacter
          ((diagonalRootDatum.{u} (n + 1)).twoWeylCocharacter (diagonalRootBase n)))).lieSubalgebra
        (B := k)).toSubmodule =
      ((UpperTriangular.definingHopfIdeal k (n + 1)).lieSubalgebra (B := k)).toSubmodule := by
  rw [BialgHom.lieSubalgebra_parabolicDefiningHopfIdeal_cocharacter_twoWeylCocharacter_toSubmodule
    _ range_ofAdd_diagonalRootDatum_root_eq_nontrivialAdjointWeights.superset]
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    refine sup_le (fun x hx ↦ ?_) (iSup₂_le fun p hp x hx ↦ ?_)
    · -- The trivial weight space consists of diagonal matrices.
      rw [Submodule.mem_comap, LieSubalgebra.mem_toSubmodule, LinearEquiv.coe_coe,
        UpperTriangular.mem_lieSubalgebra_definingHopfIdeal_iff, ← cotangentDualMatrixEquiv_apply,
        TauCeti.mem_upperTriangular_iff]
      exact fun i j hji ↦
        cotangentDualMatrixEquiv_apply_eq_zero_of_mem_adjointWeightSpace_one hx hji.ne'
    · -- A positive root space lies in the Lie algebra of the Borel, by definition of positivity.
      have hpos :=
        (isPositiveRoot_diagonalRoot_iff (R := k) p).mpr ((mem_posRoots _ _ p).mp hp)
      rw [SplitMaximalTorus.isPositiveRoot_iff, splitMaximalTorus_coordinateMap] at hpos
      exact hpos.2 x hx
  · -- An upper-triangular matrix is a diagonal matrix plus a combination of the `E_ij`, `i < j`.
    intro y hy
    obtain ⟨x, rfl⟩ := (Derivation.cotangentLinearEquiv (R := k)
      (A := coordinateHopfAlgebra k (n + 1)) (B := k)).surjective y
    rw [LieSubalgebra.mem_toSubmodule, UpperTriangular.mem_lieSubalgebra_definingHopfIdeal_iff,
      ← cotangentDualMatrixEquiv_apply, TauCeti.mem_upperTriangular_iff] at hy
    have hx : x = ∑ i, ∑ j, cotangentDualMatrixEquiv x i j • matrixUnitTangent (k := k) i j := by
      apply (cotangentDualMatrixEquiv (k := k) (n := n + 1)).injective
      simp_rw [map_sum, map_smul, cotangentDualMatrixEquiv_matrixUnitTangent, Matrix.smul_single,
        smul_eq_mul, mul_one]
      exact Matrix.matrix_eq_sum_single _
    refine Submodule.mem_map_of_mem ?_
    rw [hx]
    refine Submodule.sum_mem _ fun i _ ↦ Submodule.sum_mem _ fun j _ ↦ ?_
    rcases lt_trichotomy i j with hij | rfl | hji
    · refine Submodule.smul_mem _ _ ?_
      let p : DiagonalRootIndex.{u} (n + 1) :=
        ⟨(ULift.up i, ULift.up j), fun h ↦ hij.ne (congrArg ULift.down h)⟩
      refine Submodule.mem_sup_right (Submodule.mem_iSup_of_mem p (Submodule.mem_iSup_of_mem
        ((mem_posRoots _ _ _).mpr ((diagonalRootBase_isPos_iff n p).mpr hij)) ?_))
      rw [diagonalRootDatum_root, ofAdd_diagonalRoot]
      exact matrixUnitTangent_mem_adjointWeightSpace i j
    · exact Submodule.smul_mem _ _
        (Submodule.mem_sup_left (matrixUnitTangent_mem_trivialAdjointWeightSpace i))
    · rw [hy i j hji, zero_smul]
      exact zero_mem _

end TauCeti.GeneralLinear
