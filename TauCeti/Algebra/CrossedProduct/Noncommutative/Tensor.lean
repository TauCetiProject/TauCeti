/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.CrossedProduct.Noncommutative.Free
public import TauCeti.LinearAlgebra.TensorProduct.Balanced.Basis
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Tensor coordinates for subgroup crossed products

Extension of scalars from a subgroup crossed product has one copy of the original
module for each left coset. The equivalence `subgroupTensorEquiv` uses the actual
subgroup algebra inclusion and the right basis `rightSubgroupBasis`. Its inverse
sends the coefficient at a coset to the tensor with the chosen representative.

At finite subgroup index, extension of scalars preserves ground-ring finite generation.
The natural-number rank is the index times the original natural-number rank,
with infinite ranks and indices represented by zero. The index group and the
coefficient algebra may be infinite and noncommutative, respectively.
These are the underlying vector-space coordinates for induction of crossed-product
modules; no comparison with induction of group representations is asserted here.

## References

* G. Karpilovsky, *Projective Representations of Finite Groups* (1985).
-/

public noncomputable section

namespace TauCeti.CrossedSystem.Algebra

open MulOpposite

variable {k D G : Type*} [CommRing k] [Ring D] [_root_.Algebra k D]
  [Group G] (c : CrossedSystem k D G) (H : Subgroup G)

attribute [local instance] rightSubgroupModule

variable (N : Type*) [AddCommGroup N] [Module k N]
  [Module (Algebra (c.comap H.subtype)) N]
  [IsScalarTower k (Algebra (c.comap H.subtype)) N]

/-- Extension of scalars from a subgroup crossed product, in left-coset coordinates.
The right subgroup action on the ambient algebra is `rightSubgroupModule`. -/
def subgroupTensorEquiv :
    BalancedTensorProduct k (Algebra (c.comap H.subtype)) (Algebra c) N ≃ₗ[k]
      (G ⧸ H →₀ N) :=
  (rightSubgroupBasis c H).balancedTensorProductEquiv

/-- Subgroup tensor coordinates are the balanced tensor coordinates of the
right-module basis indexed by left cosets. -/
theorem subgroupTensorEquiv_def :
    subgroupTensorEquiv c H N = (rightSubgroupBasis c H).balancedTensorProductEquiv := (rfl)

/-- A tensor's coordinate at a coset is its right subgroup coefficient acting on the vector. -/
@[simp]
theorem subgroupTensorEquiv_tmul_apply (x : Algebra c) (n : N) (q : G ⧸ H) :
    subgroupTensorEquiv c H N
        (BalancedTensorProduct.tmul k (Algebra (c.comap H.subtype)) x n) q =
      unop ((rightSubgroupBasis c H).repr x q) • n :=
  (rightSubgroupBasis c H).balancedTensorProductEquiv_tmul_apply x n q

/-- A chosen coset representative, followed by a subgroup coefficient, acts in one slot. -/
@[simp]
theorem subgroupTensorEquiv_basis_mul_tmul (q : G ⧸ H)
    (a : Algebra (c.comap H.subtype)) (n : N) :
    subgroupTensorEquiv c H N (BalancedTensorProduct.tmul k (Algebra (c.comap H.subtype))
      (basis c q.out * comapHom c H.subtype a) n) = Finsupp.single q (a • n) := by
  classical
  simp [subgroupTensorEquiv, Module.Basis.balancedTensorProductEquiv_tmul]

/-- The inverse inserts a tensor with the chosen coset representative. -/
@[simp]
theorem subgroupTensorEquiv_symm_single (q : G ⧸ H) (n : N) :
    (subgroupTensorEquiv c H N).symm (Finsupp.single q n) =
      BalancedTensorProduct.tmul k (Algebra (c.comap H.subtype)) (basis c q.out) n := by
  simp [subgroupTensorEquiv]

/-- A coefficient multiple of a basis tensor has one nonzero coset coordinate.
The coefficient is untwisted by the chosen representative's automorphism and factor. -/
@[simp]
theorem subgroupTensorEquiv_smul_basis_tmul (q : G ⧸ H) (h : H) (d : D) (n : N) :
    subgroupTensorEquiv c H N
        (BalancedTensorProduct.tmul k (Algebra (c.comap H.subtype))
          (d • basis c (q.out * h)) n) =
      Finsupp.single q
        (((c.action q.out).symm (d * ↑(c.factor q.out h)⁻¹) •
          basis (c.comap H.subtype) h) • n) := by
  classical
  ext r
  simp only [subgroupTensorEquiv_tmul_apply, rightSubgroupBasis_repr_smul_basis,
    Finsupp.single_apply]
  split_ifs with hr <;> simp [hr]

/-- At finite subgroup index, extension of scalars preserves ground-ring finite generation. -/
instance moduleFinite_subgroupTensor [H.FiniteIndex] [Module.Finite k N] :
    Module.Finite k
      (BalancedTensorProduct k (Algebra (c.comap H.subtype)) (Algebra c) N) :=
  Module.Finite.equiv (subgroupTensorEquiv c H N).symm

/-- The ground-ring natural-number rank is multiplied by the subgroup index.
Infinite ranks and indices are represented by zero. Over a field every module is free,
so at finite index and finite dimension this is the usual dimension formula. -/
theorem finrank_subgroupTensor [StrongRankCondition k] [Module.Free k N] :
    Module.finrank k
        (BalancedTensorProduct k (Algebra (c.comap H.subtype)) (Algebra c) N) =
      H.index * Module.finrank k N := by
  -- The rank formula permits the coset and module carriers to live in different universes.
  simpa only [Module.finrank, rank_finsupp, Cardinal.toNat_mul, Cardinal.toNat_lift,
    Cardinal.toNat_mk, Subgroup.index] using
    (subgroupTensorEquiv c H N).finrank_eq

end TauCeti.CrossedSystem.Algebra
