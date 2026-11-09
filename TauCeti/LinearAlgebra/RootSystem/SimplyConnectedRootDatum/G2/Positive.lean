/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.G2.Basic

/-!
# The positive roots of the `G₂` root datum

For the pinned simply connected root datum of type `G₂`, with `α₁` the short and `α₂` the long
simple root, the positive roots are the first six entries `α₁`, `α₂`, `α₁ + α₂`, `2α₁ + α₂`,
`3α₁ + α₂` and `3α₁ + 2α₂` of its coordinate tables.

The heights of the coroots against the simple coroots are the coordinate sums in the table
`TauCeti.DynkinType.g2Coroot`, and a root is positive exactly when its coroot is, that is, when
this height is positive.

## Main results

* `TauCeti.DynkinType.height_flip_g2SimplyConnectedBase`: the heights of the coroots.
* `TauCeti.DynkinType.mem_posRoots_g2_iff`: the positive roots are the first six table entries.
* `TauCeti.DynkinType.posRootsFinset_g2`: the positive roots of the pinned `G₂` datum.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IX.
-/

public section

namespace TauCeti

open RootPairing

namespace DynkinType

/-- **The height of a coroot of the pinned `G₂` datum**, against the simple coroots, is the sum
of its coordinates. -/
@[simp] theorem height_flip_g2SimplyConnectedBase (k : Fin 12) :
    g2SimplyConnectedBase.flip.height k = g2Coroot k 0 + g2Coroot k 1 := by
  -- The coordinate sum takes the value `1` on both simple coroots, the standard basis vectors.
  have h := apply_root_eq_height_zsmul g2SimplyConnectedRootDatum.flip g2SimplyConnectedBase.flip
    (Pi.evalAddMonoidHom (fun _ : Fin 2 ↦ ℤ) 0 + Pi.evalAddMonoidHom (fun _ : Fin 2 ↦ ℤ) 1)
    (c := 1) ?_ k
  · simpa using h.symm
  · intro j hj
    rw [Base.flip_support, g2SimplyConnectedBase_support, Finset.mem_insert,
      Finset.mem_singleton] at hj
    rcases hj with rfl | rfl <;> simp [g2Coroot_apply]

/-- The positive roots of the pinned `G₂` datum are the first six entries of its coordinate
table. -/
theorem mem_posRoots_g2_iff (k : Fin 12) :
    k ∈ posRoots g2SimplyConnectedRootDatum g2SimplyConnectedBase ↔ (k : ℕ) < 6 := by
  rw [mem_posRoots, ← Base.isPos_flip_iff, Base.isPos_iff, height_flip_g2SimplyConnectedBase,
    g2Coroot_apply]
  decide +revert

/-- **The positive roots of the pinned `G₂` datum are `α₁`, `α₂`, `α₁ + α₂`, `2α₁ + α₂`,
`3α₁ + α₂` and `3α₁ + 2α₂`**, the first six entries of its coordinate table. -/
theorem posRootsFinset_g2 :
    posRootsFinset g2SimplyConnectedRootDatum g2SimplyConnectedBase = {0, 1, 2, 3, 4, 5} := by
  ext k
  rw [mem_posRootsFinset, mem_posRoots_g2_iff]
  decide +revert

end DynkinType

end TauCeti
