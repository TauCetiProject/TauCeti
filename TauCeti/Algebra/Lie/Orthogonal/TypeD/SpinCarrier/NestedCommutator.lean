/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.IntegralMatrix
public import TauCeti.LinearAlgebra.Matrix.UnipotentCommutator

/-!
# Adjacent-root nested commutators in the full type-D spin carrier

At adjacent Bourbaki nodes, the numbered root subgroups satisfy
`⁅⁅xᵢ(t), xⱼ(s)⁆, x₋ⱼ(r)⁆ = xᵢ(t * s * r)` and the corresponding negative-root identity.
These are identities in the full-weight spin carrier over every commutative ring, including
characteristic two. They supply adjacent-root calculus for the numbered root parametrizations;
no identification with an independently pinned group scheme is asserted.

The Serre relations are first transported to the integral spin-lattice matrices. The integral
matrix theorem for nested unipotent commutators then gives the group identities without dividing
by two in the value ring.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.

The group-identity argument follows
`TauCeti.Algebra.Lie.E7.Minuscule.ChevalleyRelations`; the integral spin-matrix transport uses
the invariant exterior lattice rather than a fixed minuscule matrix table.
-/

public section

namespace TauCeti.TypeDSpinCarrier

open TauCeti.UniversalEnvelopingAlgebra
open scoped commutatorElement

attribute [local instance 100] LieRing.ofAssociativeRing

universe u

variable (n : ℕ) (hn : 4 ≤ n)

local notation "CM" => CartanMatrix.D n
local notation "rootGen" => TauCeti.serreRootGenerator CM
local notation "cartanGen" => TauCeti.serreH ℚ CM

private noncomputable abbrev rootOperator (i : Fin n ⊕ Fin n) :=
  kostantRootOperator rootGen cartanGen (rep n hn) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n hn) i

private noncomputable abbrev rootRep :=
  (rep n hn).toLieHom.comp (_root_.UniversalEnvelopingAlgebra.ι ℚ)

private theorem toMatrix_rootOperator (i : Fin n ⊕ Fin n) :
    LinearMap.toMatrixAlgEquiv (latticeBasis n) (rootOperator n hn i) =
      rootIntMatrix n hn i :=
  -- The algebra equivalence is the bundled endomorphism form of the same basis matrix.
  (rootIntMatrix_eq_toMatrix n hn i).symm

private theorem lie_rootIntMatrix_eq_zero {i j : Fin n ⊕ Fin n}
    (h : ⁅rootGen i, rootGen j⁆ = 0) :
    ⁅rootIntMatrix n hn i, rootIntMatrix n hn j⁆ = 0 := by
  have hop : ⁅rootOperator n hn i, rootOperator n hn j⁆ = 0 := by
    refine LinearMap.ext fun m => Subtype.ext ?_
    have hr : ⁅rootRep n hn (rootGen i), rootRep n hn (rootGen j)⁆ = 0 := by
      rw [← LieHom.map_lie, h, map_zero]
    have hm := congrArg (fun f => f (m : ExteriorAlgebra ℚ (polarization n).W)) hr
    -- The lattice inclusion preserves subtraction and the restricted root operators.
    simpa only [Ring.lie_def, LinearMap.sub_apply, mul_apply_eq_comp,
      AddSubgroupClass.coe_sub, LinearMap.zero_apply, ZeroMemClass.coe_zero, rootOperator,
      coe_kostantRootOperator_apply, rootRep, LieHom.comp_apply, AlgHom.toLieHom_apply] using hm
  have hm := congrArg (LinearMap.toMatrixAlgEquiv (latticeBasis n)) hop
  simpa only [Ring.lie_def, map_sub, map_mul, map_zero, toMatrix_rootOperator] using hm

private theorem lie_lie_rootIntMatrix_eq_smul {i j k l : Fin n ⊕ Fin n} (c : ℤ)
    (h : ⁅⁅rootGen i, rootGen j⁆, rootGen k⁆ = c • rootGen l) :
    ⁅⁅rootIntMatrix n hn i, rootIntMatrix n hn j⁆, rootIntMatrix n hn k⁆ =
      c • rootIntMatrix n hn l := by
  have hop : ⁅⁅rootOperator n hn i, rootOperator n hn j⁆, rootOperator n hn k⁆ =
      c • rootOperator n hn l := by
    refine LinearMap.ext fun m => Subtype.ext ?_
    have hr : ⁅⁅rootRep n hn (rootGen i), rootRep n hn (rootGen j)⁆,
        rootRep n hn (rootGen k)⁆ = c • rootRep n hn (rootGen l) := by
      rw [← LieHom.map_lie, ← LieHom.map_lie, h, map_zsmul]
    have hm := congrArg (fun f => f (m : ExteriorAlgebra ℚ (polarization n).W)) hr
    -- Transport the rational bracket identity through the injective lattice inclusion.
    simpa only [Ring.lie_def, LinearMap.sub_apply, mul_apply_eq_comp,
      AddSubgroupClass.coe_sub, LinearMap.map_sub, LinearMap.smul_apply,
      AddSubgroupClass.coe_zsmul, rootOperator, coe_kostantRootOperator_apply,
      rootRep, LieHom.comp_apply, AlgHom.toLieHom_apply] using hm
  have hm := congrArg (LinearMap.toMatrixAlgEquiv (latticeBasis n)) hop
  simpa only [Ring.lie_def, map_sub, map_mul, map_zsmul, toMatrix_rootOperator] using hm

private theorem adjacent_ne {i j : Fin n} (hij : CM i j = -1) : i ≠ j := by
  rintro rfl
  rw [CartanMatrix.D_diag] at hij
  norm_num at hij

private theorem raising_lie_lie_eq_zero {i j : Fin n} (hij : CM i j = -1) :
    ⁅rootIntMatrix n hn (.inl i),
      ⁅rootIntMatrix n hn (.inl i), rootIntMatrix n hn (.inl j)⁆⁆ = 0 := by
  have h : ⁅rootGen (.inl i), ⁅rootGen (.inl i), rootGen (.inl j)⁆⁆ = 0 := by
    simpa [TauCeti.serreRootGenerator_inl, hij] using
      TauCeti.ad_pow_lie_serreE_serreE ℚ CM i j
  have hskew : ⁅⁅rootGen (.inl i), rootGen (.inl j)⁆, rootGen (.inl i)⁆ =
      (0 : ℤ) • rootGen (.inl i) := by
    rw [← lie_skew, h, neg_zero, zero_smul]
  have hM := lie_lie_rootIntMatrix_eq_smul n hn 0 hskew
  rw [zero_smul, ← lie_skew] at hM
  exact neg_eq_zero.mp hM

private theorem lowering_lie_lie_eq_zero {i j : Fin n} (hij : CM i j = -1) :
    ⁅rootIntMatrix n hn (.inr i),
      ⁅rootIntMatrix n hn (.inr i), rootIntMatrix n hn (.inr j)⁆⁆ = 0 := by
  have h : ⁅rootGen (.inr i), ⁅rootGen (.inr i), rootGen (.inr j)⁆⁆ = 0 := by
    simpa [TauCeti.serreRootGenerator_inr, hij] using
      TauCeti.ad_pow_lie_serreF_serreF ℚ CM i j
  have hskew : ⁅⁅rootGen (.inr i), rootGen (.inr j)⁆, rootGen (.inr i)⁆ =
      (0 : ℤ) • rootGen (.inr i) := by
    rw [← lie_skew, h, neg_zero, zero_smul]
  have hM := lie_lie_rootIntMatrix_eq_smul n hn 0 hskew
  rw [zero_smul, ← lie_skew] at hM
  exact neg_eq_zero.mp hM

/-- At adjacent nodes, a positive-root commutator followed by the matching negative-root
commutator recovers the first positive root, with parameter the product of the three inputs. -/
theorem commutatorElement_commutatorElement_rootSubgroupPoints_inl {i j : Fin n}
    (hij : CM i j = -1) (A : Type u) [CommRing A] (t s r : A) :
    ⁅⁅rootSubgroupPoints n hn (.inl i) A (Multiplicative.ofAdd t),
        rootSubgroupPoints n hn (.inl j) A (Multiplicative.ofAdd s)⁆,
      rootSubgroupPoints n hn (.inr j) A (Multiplicative.ofAdd r)⁆ =
        rootSubgroupPoints n hn (.inl i) A (Multiplicative.ofAdd (t * s * r)) := by
  have hji : CM j i = -1 := by rw [(CartanMatrix.D_isSymm n).apply, hij]
  have hne := adjacent_ne n hij
  have hAC : ⁅rootGen (.inl i), rootGen (.inr j)⁆ = 0 := by
    simpa only [TauCeti.serreRootGenerator_inl, TauCeti.serreRootGenerator_inr] using
      TauCeti.lie_serreE_serreF_of_ne ℚ CM hne
  have hABC : ⁅⁅rootGen (.inl i), rootGen (.inl j)⁆, rootGen (.inr j)⁆ =
      (1 : ℤ) • rootGen (.inl i) := by
    simp only [TauCeti.serreRootGenerator_inl, TauCeti.serreRootGenerator_inr]
    rw [lie_lie, TauCeti.lie_serreE_serreF_of_ne ℚ CM hne, lie_zero, sub_zero,
      (TauCeti.isSerreSystem_serre ℚ CM).lie_E_F_self, ← lie_skew,
      TauCeti.lie_serreH_serreE, hji, neg_one_zsmul, neg_neg, one_smul]
  have hM := lie_lie_rootIntMatrix_eq_smul n hn 1 hABC
  rw [one_smul] at hM
  apply (points n hn A).subtype_injective
  simp only [map_commutatorElement, Subgroup.subtype_apply]
  apply Units.ext
  rw [coe_rootSubgroupPoints_eq_one_add_smul, toAdd_ofAdd]
  exact Matrix.coe_commutatorElement_commutatorElement_eq_one_add_smul
    (rootIntMatrix n hn (.inl i)) (rootIntMatrix n hn (.inl j))
    (rootIntMatrix n hn (.inr j)) (rootIntMatrix_mul_self n hn _)
    (rootIntMatrix_mul_self n hn _) (rootIntMatrix_mul_self n hn _)
    (lie_rootIntMatrix_eq_zero n hn hAC) hM (raising_lie_lie_eq_zero n hn hij)
    (raising_lie_lie_eq_zero n hn hji) t s r _ _ _
    (coe_rootSubgroupPoints_eq_one_add_smul n hn _ A _)
    (coe_rootSubgroupPoints_eq_one_add_smul n hn _ A _)
    (coe_rootSubgroupPoints_eq_one_add_smul n hn _ A _)

/-- At adjacent nodes, a negative-root commutator followed by the matching positive-root
commutator recovers the first negative root, with parameter the product of the three inputs. -/
theorem commutatorElement_commutatorElement_rootSubgroupPoints_inr {i j : Fin n}
    (hij : CM i j = -1) (A : Type u) [CommRing A] (t s r : A) :
    ⁅⁅rootSubgroupPoints n hn (.inr i) A (Multiplicative.ofAdd t),
        rootSubgroupPoints n hn (.inr j) A (Multiplicative.ofAdd s)⁆,
      rootSubgroupPoints n hn (.inl j) A (Multiplicative.ofAdd r)⁆ =
        rootSubgroupPoints n hn (.inr i) A (Multiplicative.ofAdd (t * s * r)) := by
  have hji : CM j i = -1 := by rw [(CartanMatrix.D_isSymm n).apply, hij]
  have hne := adjacent_ne n hij
  have hAC : ⁅rootGen (.inr i), rootGen (.inl j)⁆ = 0 := by
    rw [← lie_skew, TauCeti.serreRootGenerator_inl, TauCeti.serreRootGenerator_inr,
      TauCeti.lie_serreE_serreF_of_ne ℚ CM hne.symm, neg_zero]
  have hABC : ⁅⁅rootGen (.inr i), rootGen (.inr j)⁆, rootGen (.inl j)⁆ =
      (1 : ℤ) • rootGen (.inr i) := by
    simp only [TauCeti.serreRootGenerator_inl, TauCeti.serreRootGenerator_inr]
    have hFE : ⁅TauCeti.serreF ℚ CM j, TauCeti.serreE ℚ CM j⁆ =
        -TauCeti.serreH ℚ CM j := by
      rw [← lie_skew, (TauCeti.isSerreSystem_serre ℚ CM).lie_E_F_self]
    have hFij : ⁅TauCeti.serreF ℚ CM i, TauCeti.serreE ℚ CM j⁆ = 0 := by
      simpa only [TauCeti.serreRootGenerator_inl, TauCeti.serreRootGenerator_inr] using hAC
    rw [lie_lie, hFij, lie_zero, sub_zero, hFE, lie_neg,
      ← lie_skew, TauCeti.lie_serreH_serreF, hji]
    simp only [neg_one_zsmul, neg_neg, one_smul]
  have hM := lie_lie_rootIntMatrix_eq_smul n hn 1 hABC
  rw [one_smul] at hM
  apply (points n hn A).subtype_injective
  simp only [map_commutatorElement, Subgroup.subtype_apply]
  apply Units.ext
  rw [coe_rootSubgroupPoints_eq_one_add_smul, toAdd_ofAdd]
  exact Matrix.coe_commutatorElement_commutatorElement_eq_one_add_smul
    (rootIntMatrix n hn (.inr i)) (rootIntMatrix n hn (.inr j))
    (rootIntMatrix n hn (.inl j)) (rootIntMatrix_mul_self n hn _)
    (rootIntMatrix_mul_self n hn _) (rootIntMatrix_mul_self n hn _)
    (lie_rootIntMatrix_eq_zero n hn hAC) hM (lowering_lie_lie_eq_zero n hn hij)
    (lowering_lie_lie_eq_zero n hn hji) t s r _ _ _
    (coe_rootSubgroupPoints_eq_one_add_smul n hn _ A _)
    (coe_rootSubgroupPoints_eq_one_add_smul n hn _ A _)
    (coe_rootSubgroupPoints_eq_one_add_smul n hn _ A _)

end TauCeti.TypeDSpinCarrier
