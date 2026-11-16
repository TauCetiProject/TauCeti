/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.CoefficientReflection
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E6.Basic
-- The finite certificates evaluate the existing private coroot table.
import all TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E6.Basic

/-!
# Simple-root coefficients and the highest root of type `E₆`

Type `E₆` is simply laced, so the simple-root coefficients of a root of the pinned datum are the
simple-coroot coordinates of its coroot, which the datum stores in the table
`TauCeti.DynkinType.e6Coroot`. By `TauCeti.DynkinType.e6Coroot_le_apply_35` the root at index
`35` dominates every root coefficientwise. Hence it is the highest root, with the Bourbaki marks
`(1, 2, 2, 3, 2, 1)` as coefficients and height `11`, and it lies above every root in the positive
root cone. The datum has `36` positive roots.

Over `ℤ` the datum is not irreducible in the sense of `RootPairing.IsIrreducible`, since for
instance the sublattice of even vectors is reflection-invariant, so the general highest-root
theorems for irreducible root pairings do not apply to it directly; the statements here are proved
from the table instead.

## Main results

* `TauCeti.DynkinType.e6Coroot_apply_35` and `TauCeti.DynkinType.e6Root_apply_35`: the entries of
  the tables at index `35`.
* `TauCeti.DynkinType.e6Coroot_le_apply_35`: the coroot at index `35` dominates every coroot.
* `TauCeti.DynkinType.rootCoefficients_e6SimplyConnectedBase`: the coefficients of a root are the
  coordinates of its coroot.
* `TauCeti.DynkinType.highestRoot_e6SimplyConnectedBase`: the highest root has index `35`.
* `TauCeti.DynkinType.rootCoefficients_highestRoot_e6SimplyConnectedBase`: its coefficients are
  `(1, 2, 2, 3, 2, 1)`.
* `TauCeti.DynkinType.root_highestRoot_sub_mem_posRootCone_e6`: it lies above every root.
* `TauCeti.DynkinType.height_highestRoot_e6SimplyConnectedBase`: its height is `11`.
* `TauCeti.DynkinType.ncard_posRoots_e6SimplyConnectedRootDatum`: there are `36` positive roots,
  for any base.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate V.
-/

public section

namespace TauCeti.DynkinType

open _root_.Matrix

private lemma bijOn_e6SimpleIndex :
    Set.BijOn e6SimpleIndex Set.univ e6SimplyConnectedBase.support :=
  ⟨fun i _ ↦ mem_e6SimplyConnectedBase_support.mpr (by simp), e6SimpleIndex_injective.injOn,
    fun j hj ↦ ⟨⟨j, mem_e6SimplyConnectedBase_support.mp hj⟩, trivial, Fin.ext (by simp)⟩⟩

private lemma root_e6_eq_sum_coroot_smul (j : Fin 72) :
    e6SimplyConnectedRootDatum.root j =
      ∑ i, e6Coroot j i • e6SimplyConnectedRootDatum.root (e6SimpleIndex i) := by
  rw [e6SimplyConnectedRootDatum_root, e6Root_eq_mulVec, ← vecMul_transpose,
    (CartanMatrix.E_isSymm 6).eq, vecMul_eq_sum]
  simp

/-- **The simple-root coefficients of an `E₆` root are the coordinates of its coroot**, in the
Bourbaki numbering of the simple roots. -/
@[simp]
theorem rootCoefficients_e6SimplyConnectedBase (j : Fin 72) (i : Fin 6) :
    e6SimplyConnectedBase.rootCoefficients j ⟨e6SimpleIndex i, by simp⟩ = e6Coroot j i :=
  e6SimplyConnectedBase.rootCoefficients_apply_of_injective e6SimpleIndex_injective
    (fun _ ↦ by simp) (root_e6_eq_sum_coroot_smul j) i

/-- The last positive entry of the `E₆` coroot table has the Bourbaki marks `(1, 2, 2, 3, 2, 1)`. -/
@[simp] theorem e6Coroot_apply_35 : e6Coroot 35 = ![1, 2, 2, 3, 2, 1] := by decide +kernel

/-- The last positive entry of the `E₆` root table has fundamental-weight coordinates
`(0, 1, 0, 0, 0, 0)`. -/
@[simp] theorem e6Root_apply_35 : e6Root 35 = ![0, 1, 0, 0, 0, 0] := by decide +kernel

/-- **The root at index `35` has the largest coordinates in the `E₆` coroot table.** -/
theorem e6Coroot_le_apply_35 (j : Fin 72) (i : Fin 6) : e6Coroot j i ≤ e6Coroot 35 i := by
  revert j i
  decide +kernel

private lemma rootCoefficients_le_e6 (j : Fin 72) :
    e6SimplyConnectedBase.rootCoefficients j ≤ e6SimplyConnectedBase.rootCoefficients 35 :=
  (e6SimplyConnectedBase.rootCoefficients_le_iff_of_surjOn (fun _ ↦ by simp)
    bijOn_e6SimpleIndex.surjOn).mpr fun i ↦ by simpa using e6Coroot_le_apply_35 j i

/-- **The highest root of the pinned `E₆` datum has index `35`**, the last positive root of the
table. -/
theorem highestRoot_e6SimplyConnectedBase : e6SimplyConnectedBase.highestRoot = 35 :=
  (e6SimplyConnectedBase.eq_highestRoot_of_forall_rootCoefficients_le rootCoefficients_le_e6).symm

/-- **The simple-root coefficients of the highest root of `E₆`** are the Bourbaki marks
`(1, 2, 2, 3, 2, 1)`. -/
@[simp high]
theorem rootCoefficients_highestRoot_e6SimplyConnectedBase (i : Fin 6) :
    e6SimplyConnectedBase.rootCoefficients e6SimplyConnectedBase.highestRoot
        ⟨e6SimpleIndex i, by simp⟩ = ![1, 2, 2, 3, 2, 1] i := by
  rw [highestRoot_e6SimplyConnectedBase, rootCoefficients_e6SimplyConnectedBase, e6Coroot_apply_35]

/-- **Every root of `E₆` lies below the highest root** in the positive root cone. -/
theorem root_highestRoot_sub_mem_posRootCone_e6 (j : Fin 72) :
    e6SimplyConnectedRootDatum.root e6SimplyConnectedBase.highestRoot -
        e6SimplyConnectedRootDatum.root j ∈
      posRootCone e6SimplyConnectedRootDatum e6SimplyConnectedBase := by
  rw [RootPairing.Base.root_sub_root_mem_posRootCone_iff, highestRoot_e6SimplyConnectedBase]
  exact rootCoefficients_le_e6 j

/-- The height of the highest root of `E₆` is `11`. -/
@[simp]
theorem height_highestRoot_e6SimplyConnectedBase :
    e6SimplyConnectedBase.height e6SimplyConnectedBase.highestRoot = 11 := by
  rw [e6SimplyConnectedBase.height_eq_sum_rootCoefficients_of_bijOn bijOn_e6SimpleIndex]
  simp only [rootCoefficients_highestRoot_e6SimplyConnectedBase]
  decide

/-- **The pinned `E₆` datum has `36` positive roots.** Exactly half of its `72` roots are positive,
for any base. -/
@[simp]
theorem ncard_posRoots_e6SimplyConnectedRootDatum (b : e6SimplyConnectedRootDatum.Base) :
    (posRoots e6SimplyConnectedRootDatum b).ncard = 36 := by
  rw [ncard_posRoots_eq_natCard_div_two]
  norm_num

end TauCeti.DynkinType

end
