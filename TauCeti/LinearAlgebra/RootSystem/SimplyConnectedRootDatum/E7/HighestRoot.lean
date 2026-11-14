/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.CoefficientReflection
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E7.Datum

/-!
# Simple-root coefficients and the highest root of type `E₇`

Type `E₇` is simply laced, so the simple-root coefficients of a root of the pinned datum are the
simple-coroot coordinates of its coroot, which the datum stores in the table
`TauCeti.DynkinType.e7Coroot`. By `TauCeti.DynkinType.e7Coroot_le_apply_62` the root at index `62`
dominates every root coefficientwise. Hence it is the highest root, with the Bourbaki marks
`(2, 2, 3, 4, 3, 2, 1)` as coefficients and height `17`, and it lies above every root in the
positive root cone. The datum has `63` positive roots.

Over `ℤ` the datum is not irreducible in the sense of `RootPairing.IsIrreducible`, since for
instance the sublattice of even vectors is reflection-invariant, so the general highest-root
theorems for irreducible root pairings do not apply to it directly; the statements here are proved
from the table instead.

## Main results

* `TauCeti.DynkinType.rootCoefficients_e7SimplyConnectedBase`: the coefficients of a root are the
  coordinates of its coroot.
* `TauCeti.DynkinType.highestRoot_e7SimplyConnectedBase`: the highest root has index `62`.
* `TauCeti.DynkinType.rootCoefficients_highestRoot_e7SimplyConnectedBase`: its coefficients are
  `(2, 2, 3, 4, 3, 2, 1)`.
* `TauCeti.DynkinType.root_highestRoot_sub_mem_posRootCone_e7`: it lies above every root.
* `TauCeti.DynkinType.height_highestRoot_e7SimplyConnectedBase`: its height is `17`.
* `TauCeti.DynkinType.ncard_posRoots_e7SimplyConnectedBase`: there are `63` positive roots.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate VI.
-/

public section

namespace TauCeti.DynkinType

open _root_.Matrix

private lemma bijOn_e7SimpleIndex :
    Set.BijOn e7SimpleIndex Set.univ e7SimplyConnectedBase.support :=
  ⟨fun i _ ↦ mem_support_e7SimplyConnectedBase.mpr (by simp), e7SimpleIndex_injective.injOn,
    fun j hj ↦ ⟨⟨j, mem_support_e7SimplyConnectedBase.mp hj⟩, trivial, Fin.ext (by simp)⟩⟩

private lemma root_e7_eq_sum_coroot_smul (j : Fin 126) :
    e7SimplyConnectedRootDatum.root j =
      ∑ i, e7Coroot j i • e7SimplyConnectedRootDatum.root (e7SimpleIndex i) := by
  rw [e7SimplyConnectedRootDatum_root, e7Root_apply, vecMul_eq_sum]
  simp

/-- **The simple-root coefficients of an `E₇` root are the coordinates of its coroot**, in the
Bourbaki numbering of the simple roots. -/
@[simp]
theorem rootCoefficients_e7SimplyConnectedBase (j : Fin 126) (i : Fin 7) :
    e7SimplyConnectedBase.rootCoefficients j ⟨e7SimpleIndex i, by simp⟩ = e7Coroot j i :=
  e7SimplyConnectedBase.rootCoefficients_apply_of_bijOn bijOn_e7SimpleIndex
    (root_e7_eq_sum_coroot_smul j) i

private lemma rootCoefficients_le_e7 (j : Fin 126) :
    e7SimplyConnectedBase.rootCoefficients j ≤ e7SimplyConnectedBase.rootCoefficients 62 := by
  intro k
  obtain ⟨i, -, hi⟩ := bijOn_e7SimpleIndex.surjOn k.2
  obtain rfl : k = ⟨e7SimpleIndex i, by simp⟩ := Subtype.ext hi.symm
  simpa using e7Coroot_le_apply_62 j i

/-- **The highest root of the pinned `E₇` datum has index `62`**, the last positive root of the
table. -/
theorem highestRoot_e7SimplyConnectedBase : e7SimplyConnectedBase.highestRoot = 62 :=
  (e7SimplyConnectedBase.eq_highestRoot_of_forall_rootCoefficients_le rootCoefficients_le_e7).symm

/-- **The simple-root coefficients of the highest root of `E₇`** are the Bourbaki marks
`(2, 2, 3, 4, 3, 2, 1)`. -/
theorem rootCoefficients_highestRoot_e7SimplyConnectedBase (i : Fin 7) :
    e7SimplyConnectedBase.rootCoefficients e7SimplyConnectedBase.highestRoot
        ⟨e7SimpleIndex i, by simp⟩ = ![2, 2, 3, 4, 3, 2, 1] i := by
  rw [highestRoot_e7SimplyConnectedBase, rootCoefficients_e7SimplyConnectedBase, e7Coroot_apply_62]

/-- **Every root of `E₇` lies below the highest root** in the positive root cone. -/
theorem root_highestRoot_sub_mem_posRootCone_e7 (j : Fin 126) :
    e7SimplyConnectedRootDatum.root e7SimplyConnectedBase.highestRoot -
        e7SimplyConnectedRootDatum.root j ∈
      posRootCone e7SimplyConnectedRootDatum e7SimplyConnectedBase := by
  rw [RootPairing.Base.root_sub_root_mem_posRootCone_iff, highestRoot_e7SimplyConnectedBase]
  exact rootCoefficients_le_e7 j

/-- The height of the highest root of `E₇` is `17`. -/
@[simp]
theorem height_highestRoot_e7SimplyConnectedBase :
    e7SimplyConnectedBase.height e7SimplyConnectedBase.highestRoot = 17 := by
  rw [highestRoot_e7SimplyConnectedBase, e7SimplyConnectedBase.height_eq_sum_of_bijOn
    bijOn_e7SimpleIndex (root_e7_eq_sum_coroot_smul 62), e7Coroot_apply_62]
  decide

/-- The pinned `E₇` datum has `63` positive roots. -/
theorem ncard_posRoots_e7SimplyConnectedBase :
    (posRoots e7SimplyConnectedRootDatum e7SimplyConnectedBase).ncard = 63 := by
  have h := two_mul_ncard_posRoots e7SimplyConnectedRootDatum e7SimplyConnectedBase
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at h
  omega

end TauCeti.DynkinType

end
