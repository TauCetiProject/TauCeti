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

open scoped commutatorElement

attribute [local instance 100] LieRing.ofAssociativeRing

universe u

variable (n : ℕ) (hn : 4 ≤ n)

local notation "CM" => CartanMatrix.D n
local notation "rootGen" => TauCeti.serreRootGenerator CM

private theorem raising_lie_lie_eq_zero {i j : Fin n} (hij : CM i j = -1) :
    ⁅rootIntMatrix n hn (.inl i),
      ⁅rootIntMatrix n hn (.inl i), rootIntMatrix n hn (.inl j)⁆⁆ = 0 := by
  apply lie_rootIntMatrix_lie_eq_zero
  simpa [TauCeti.serreRootGenerator_inl, hij] using
    TauCeti.ad_pow_lie_serreE_serreE ℚ CM i j

private theorem lowering_lie_lie_eq_zero {i j : Fin n} (hij : CM i j = -1) :
    ⁅rootIntMatrix n hn (.inr i),
      ⁅rootIntMatrix n hn (.inr i), rootIntMatrix n hn (.inr j)⁆⁆ = 0 := by
  apply lie_rootIntMatrix_lie_eq_zero
  simpa [TauCeti.serreRootGenerator_inr, hij] using
    TauCeti.ad_pow_lie_serreF_serreF ℚ CM i j

/-- At adjacent nodes, a positive-root commutator followed by the matching negative-root
commutator recovers the first positive root, with parameter the product of the three inputs. -/
theorem commutatorElement_commutatorElement_rootSubgroupPoints_inl {i j : Fin n}
    (hij : CM i j = -1) (A : Type u) [CommRing A] (t s r : A) :
    ⁅⁅rootSubgroupPoints n hn (.inl i) A (Multiplicative.ofAdd t),
        rootSubgroupPoints n hn (.inl j) A (Multiplicative.ofAdd s)⁆,
      rootSubgroupPoints n hn (.inr j) A (Multiplicative.ofAdd r)⁆ =
        rootSubgroupPoints n hn (.inl i) A (Multiplicative.ofAdd (t * s * r)) := by
  have hji : CM j i = -1 := by rw [(CartanMatrix.D_isSymm n).apply, hij]
  have hne : i ≠ j := ne_of_apply_ne (CM i) (by simp [hij])
  have hAC : ⁅rootGen (.inl i), rootGen (.inr j)⁆ = 0 := by
    simpa only [TauCeti.serreRootGenerator_inl, TauCeti.serreRootGenerator_inr] using
      TauCeti.lie_serreE_serreF_of_ne ℚ CM hne
  have hABC : ⁅⁅rootGen (.inl i), rootGen (.inl j)⁆, rootGen (.inr j)⁆ =
      (1 : ℤ) • rootGen (.inl i) := by
    simpa [TauCeti.serreRootGenerator_inl, TauCeti.serreRootGenerator_inr, hji] using
      (TauCeti.isSerreSystem_serre ℚ CM).lie_lie_E_E_F_of_ne hne
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
  have hne : i ≠ j := ne_of_apply_ne (CM i) (by simp [hij])
  have hAC : ⁅rootGen (.inr i), rootGen (.inl j)⁆ = 0 := by
    rw [← lie_skew, TauCeti.serreRootGenerator_inl, TauCeti.serreRootGenerator_inr,
      TauCeti.lie_serreE_serreF_of_ne ℚ CM hne.symm, neg_zero]
  have hABC : ⁅⁅rootGen (.inr i), rootGen (.inr j)⁆, rootGen (.inl j)⁆ =
      (1 : ℤ) • rootGen (.inr i) := by
    simpa [TauCeti.serreRootGenerator_inl, TauCeti.serreRootGenerator_inr, hji] using
      (TauCeti.isSerreSystem_serre ℚ CM).lie_lie_F_F_E_of_ne hne
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
