/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.CrossedProduct.Noncommutative.Tensor
public import TauCeti.LinearAlgebra.TensorProduct.Balanced.Actions

/-!
# Induced crossed-product actions in coset coordinates

For a crossed system `c` and an arbitrary subgroup `H` of its index group, extension
of scalars from the subgroup crossed product acts on `G ⧸ H →₀ N`. The algebra map
`subgroupInductionAction` transports left multiplication on the balanced tensor
through `subgroupTensorEquiv`.

The formula `subgroupInductionAction_smul_basis_single` computes the action on a
single coset. It retains both the inverse coefficient automorphism at the new
representative and the factor-set correction. These are the coordinates needed to
compare induction of semilinear multiplicity modules with induction of group
representations. No finite-index, centrality, or semisimplicity hypothesis is used.
The tensor-side scalar action is `BalancedTensorProduct.leftModule`; install it and
`rightSubgroupModule` locally when writing that action with scalar notation.

## References

* G. Karpilovsky, *Projective Representations of Finite Groups* (1985).
-/

public noncomputable section

namespace TauCeti.CrossedSystem.Algebra

variable {k D G : Type*} [CommRing k] [Ring D] [_root_.Algebra k D]
  [Group G] (c : CrossedSystem k D G) (H : Subgroup G)

attribute [local instance] rightSubgroupModule
attribute [local instance 100] BalancedTensorProduct.leftModule
  BalancedTensorProduct.leftIsScalarTower

variable (N : Type*) [AddCommGroup N] [Module k N]
  [Module (Algebra (c.comap H.subtype)) N]
  [IsScalarTower k (Algebra (c.comap H.subtype)) N]

/-- The ambient crossed-product action on the finite-support left-coset model of
extension of scalars from the subgroup crossed product. -/
def subgroupInductionAction : Algebra c →ₐ[k] Module.End k (G ⧸ H →₀ N) :=
  ((subgroupTensorEquiv c H N).conjAlgEquiv k).toAlgHom.comp
    (_root_.Algebra.lsmul k k
      (BalancedTensorProduct k (Algebra (c.comap H.subtype)) (Algebra c) N))

/-- The coset action is left multiplication on the first tensor factor, transported
through the tensor-coordinate equivalence. -/
theorem subgroupInductionAction_apply (a : Algebra c) (v : G ⧸ H →₀ N) :
    subgroupInductionAction c H N a v =
      subgroupTensorEquiv c H N (a • (subgroupTensorEquiv c H N).symm v) := (rfl)

/-- In tensor coordinates, an ambient algebra element multiplies the first factor. -/
@[simp]
theorem subgroupInductionAction_tmul (a x : Algebra c) (n : N) :
    subgroupInductionAction c H N a
        (subgroupTensorEquiv c H N
          (BalancedTensorProduct.tmul k (Algebra (c.comap H.subtype)) x n)) =
      subgroupTensorEquiv c H N
        (BalancedTensorProduct.tmul k (Algebra (c.comap H.subtype)) (a * x) n) := by
  rw [subgroupInductionAction_apply, LinearEquiv.symm_apply_apply,
    BalancedTensorProduct.smul_tmul_left]
  rfl

/-- The action on a single coset is obtained by multiplying its representative. -/
theorem subgroupInductionAction_single (a : Algebra c) (q : G ⧸ H) (n : N) :
    subgroupInductionAction c H N a (Finsupp.single q n) =
      subgroupTensorEquiv c H N
        (BalancedTensorProduct.tmul k (Algebra (c.comap H.subtype))
          (a * basis c q.out) n) := by
  rw [subgroupInductionAction_apply, subgroupTensorEquiv_symm_single,
    BalancedTensorProduct.smul_tmul_left]
  rfl

/-- The twisted coset formula for induction. If `g * q.out = r.out * h`,
then `d[g]` sends the `q` slot to the `r` slot with subgroup coefficient
`σ_r⁻¹(d a(g,q.out) a(r.out,h)⁻¹)[h]`. -/
theorem subgroupInductionAction_smul_basis_single
    (g : G) (d : D) (q r : G ⧸ H) (h : H) (hgh : g * q.out = r.out * h) (n : N) :
    subgroupInductionAction c H N (d • basis c g) (Finsupp.single q n) =
      Finsupp.single r
        (((c.action r.out).symm
          (d * c.factor g q.out * ↑(c.factor r.out h)⁻¹) •
            basis (c.comap H.subtype) h) • n) := by
  rw [subgroupInductionAction_single, ← one_smul D (basis c q.out),
    smul_basis_mul_smul_basis]
  simp only [map_one, mul_one, hgh, subgroupTensorEquiv_smul_basis_tmul]

/-- The action of a coefficient is twisted in each slot by the inverse automorphism
of that slot's representative; it is not generally the pointwise coefficient action. -/
@[simp]
theorem subgroupInductionAction_inc_single (d : D) (q : G ⧸ H) (n : N) :
    subgroupInductionAction c H N (inc c d) (Finsupp.single q n) =
      Finsupp.single q ((inc (c.comap H.subtype) ((c.action q.out).symm d)) • n) := by
  simpa only [inc_apply, Subgroup.coe_one, factor_one_left, factor_one_right, Units.val_one,
    inv_one, mul_one] using
    subgroupInductionAction_smul_basis_single c H N 1 d q q 1 (by simp) n

/-- A formula for every basis element and input coset, using the standard coset
factorization to choose the new slot and subgroup element. -/
@[simp]
theorem subgroupInductionAction_basis_single (g : G) (q : G ⧸ H) (n : N) :
    let p := H.groupEquivQuotientProdSubgroup (g * q.out)
    subgroupInductionAction c H N (basis c g) (Finsupp.single q n) =
      Finsupp.single p.1
        (((c.action p.1.out).symm
          (c.factor g q.out * ↑(c.factor p.1.out p.2)⁻¹) •
            basis (c.comap H.subtype) p.2) • n) := by
  have h := H.groupEquivQuotientProdSubgroup.symm_apply_apply (g * q.out)
  rw [Subgroup.groupEquivQuotientProdSubgroup_symm_apply] at h
  simpa only [one_smul, one_mul] using
    subgroupInductionAction_smul_basis_single c H N g 1 q _ _ h.symm n

variable {N} {N' : Type*} [AddCommGroup N'] [Module k N']
  [Module (Algebra (c.comap H.subtype)) N']
  [IsScalarTower k (Algebra (c.comap H.subtype)) N']

/-- Applying a subgroup-module homomorphism in every coset intertwines the induced
ambient algebra actions. Thus the coset model is natural in the inducing module. -/
theorem subgroupInductionAction_naturality
    (f : N →ₗ[Algebra (c.comap H.subtype)] N') (a : Algebra c) (v : G ⧸ H →₀ N) :
    Finsupp.mapRange.linearMap (f.restrictScalars k)
        (subgroupInductionAction c H N a v) =
      subgroupInductionAction c H N' a
        (Finsupp.mapRange.linearMap (f.restrictScalars k) v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]
  | single q n =>
    simp only [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single,
      subgroupInductionAction_single]
    ext r
    simp [subgroupTensorEquiv_tmul_apply]

end TauCeti.CrossedSystem.Algebra
