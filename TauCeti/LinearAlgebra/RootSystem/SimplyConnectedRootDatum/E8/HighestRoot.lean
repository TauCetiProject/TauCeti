/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.CoefficientReflection
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E8.Datum
-- The finite certificate evaluates the existing coroot table.
import all TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E8.Basic

/-!
# Simple-root coefficients and the highest root of type `E₈`

Type `E₈` is simply laced, so the simple-root coefficients of a root of the pinned datum are the
simple-coroot coordinates of its coroot, which the datum stores in the table
`TauCeti.DynkinType.e8Coroot`. Reading the table, the root at index `119` dominates every root
coefficientwise. Hence it is the highest root, with the Bourbaki marks `(2, 3, 4, 6, 5, 4, 3, 2)`
as coefficients and height `29`, and it lies above every root in the positive root cone. The datum
has `120` positive roots.

Over `ℤ` the datum is not irreducible in the sense of `RootPairing.IsIrreducible`, since for
instance the sublattice of even vectors is reflection-invariant, so the general highest-root
theorems for irreducible root pairings do not apply to it directly; the statements here are proved
from the table instead.

## Main results

* `TauCeti.DynkinType.rootCoefficients_e8SimplyConnectedBase`: the coefficients of a root are the
  coordinates of its coroot.
* `TauCeti.DynkinType.highestRoot_e8SimplyConnectedBase`: the highest root has index `119`.
* `TauCeti.DynkinType.rootCoefficients_highestRoot_e8SimplyConnectedBase`: its coefficients are
  `(2, 3, 4, 6, 5, 4, 3, 2)`.
* `TauCeti.DynkinType.root_highestRoot_sub_mem_posRootCone_e8`: it lies above every root.
* `TauCeti.DynkinType.height_highestRoot_e8SimplyConnectedBase`: its height is `29`.
* `TauCeti.DynkinType.ncard_posRoots_e8SimplyConnectedBase`: there are `120` positive roots.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate VII.
-/

public section

namespace TauCeti.DynkinType

open _root_.Matrix

private lemma bijOn_e8SimpleIndex :
    Set.BijOn e8SimpleIndex Set.univ e8SimplyConnectedBase.support :=
  ⟨fun i _ ↦ mem_support_e8SimplyConnectedBase.mpr (by simp), e8SimpleIndex_injective.injOn,
    fun j hj ↦ ⟨⟨j, mem_support_e8SimplyConnectedBase.mp hj⟩, trivial, Fin.ext (by simp)⟩⟩

private lemma root_e8_eq_sum_coroot_smul (j : Fin 240) :
    e8SimplyConnectedRootDatum.root j =
      ∑ i, e8Coroot j i • e8SimplyConnectedRootDatum.root (e8SimpleIndex i) := by
  rw [e8SimplyConnectedRootDatum_root, e8Root_apply, vecMul_eq_sum]
  simp

/-- **The simple-root coefficients of an `E₈` root are the coordinates of its coroot**, in the
Bourbaki numbering of the simple roots. -/
@[simp]
theorem rootCoefficients_e8SimplyConnectedBase (j : Fin 240) (i : Fin 8) :
    e8SimplyConnectedBase.rootCoefficients j ⟨e8SimpleIndex i, by simp⟩ = e8Coroot j i :=
  e8SimplyConnectedBase.rootCoefficients_apply_of_bijOn bijOn_e8SimpleIndex
    (root_e8_eq_sum_coroot_smul j) i

/-- The root at index `119` has the largest coordinates in the `E₈` coroot table. -/
private lemma e8Coroot_le_apply_119 (j : Fin 240) (i : Fin 8) :
    e8Coroot j i ≤ e8Coroot 119 i := by
  revert j i
  decide +kernel

private lemma rootCoefficients_le_e8 (j : Fin 240) :
    e8SimplyConnectedBase.rootCoefficients j ≤ e8SimplyConnectedBase.rootCoefficients 119 := by
  intro k
  obtain ⟨i, -, hi⟩ := bijOn_e8SimpleIndex.surjOn k.2
  obtain rfl : k = ⟨e8SimpleIndex i, by simp⟩ := Subtype.ext hi.symm
  simpa using e8Coroot_le_apply_119 j i

/-- **The highest root of the pinned `E₈` datum has index `119`**, the last positive root of the
table. -/
theorem highestRoot_e8SimplyConnectedBase : e8SimplyConnectedBase.highestRoot = 119 :=
  (e8SimplyConnectedBase.eq_highestRoot_of_forall_rootCoefficients_le rootCoefficients_le_e8).symm

/-- **The simple-root coefficients of the highest root of `E₈`** are the Bourbaki marks
`(2, 3, 4, 6, 5, 4, 3, 2)`. -/
theorem rootCoefficients_highestRoot_e8SimplyConnectedBase (i : Fin 8) :
    e8SimplyConnectedBase.rootCoefficients e8SimplyConnectedBase.highestRoot
        ⟨e8SimpleIndex i, by simp⟩ = ![2, 3, 4, 6, 5, 4, 3, 2] i := by
  rw [highestRoot_e8SimplyConnectedBase, rootCoefficients_e8SimplyConnectedBase,
    e8Coroot_apply_last_positive]

/-- **Every root of `E₈` lies below the highest root** in the positive root cone. -/
theorem root_highestRoot_sub_mem_posRootCone_e8 (j : Fin 240) :
    e8SimplyConnectedRootDatum.root e8SimplyConnectedBase.highestRoot -
        e8SimplyConnectedRootDatum.root j ∈
      posRootCone e8SimplyConnectedRootDatum e8SimplyConnectedBase := by
  rw [RootPairing.Base.root_sub_root_mem_posRootCone_iff, highestRoot_e8SimplyConnectedBase]
  exact rootCoefficients_le_e8 j

/-- The height of the highest root of `E₈` is `29`. -/
@[simp]
theorem height_highestRoot_e8SimplyConnectedBase :
    e8SimplyConnectedBase.height e8SimplyConnectedBase.highestRoot = 29 := by
  rw [highestRoot_e8SimplyConnectedBase, e8SimplyConnectedBase.height_eq_sum_of_bijOn
    bijOn_e8SimpleIndex (root_e8_eq_sum_coroot_smul 119), e8Coroot_apply_last_positive]
  decide

/-- The pinned `E₈` datum has `120` positive roots. -/
theorem ncard_posRoots_e8SimplyConnectedBase :
    (posRoots e8SimplyConnectedRootDatum e8SimplyConnectedBase).ncard = 120 := by
  have h := two_mul_ncard_posRoots e8SimplyConnectedRootDatum e8SimplyConnectedBase
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at h
  omega

end TauCeti.DynkinType

end
