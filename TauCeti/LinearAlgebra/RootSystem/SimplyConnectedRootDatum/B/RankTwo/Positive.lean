/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Positive
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.B.RankTwo
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.NonSimplyLaced

/-!
# The positive roots of the rank-two type `B` root datum

For the pinned simply connected root datum of type `B₂`, with `α₀` the long and `α₁` the short
simple root, the positive roots are the first four entries `α₀`, `α₁`, `α₀ + α₁` and `α₀ + 2 α₁`
of its coordinate tables, the roots at the indices `b2Index 0` to `b2Index 3`.

The heights of the coroots against the simple coroots are the coordinate sums in the table
`TauCeti.DynkinType.b2Coroot`, and a root is positive exactly when its coroot is, that is, when
this height is positive.

## Main results

* `TauCeti.DynkinType.height_flip_b2Index`: the heights of the coroots.
* `TauCeti.DynkinType.b2Index_mem_posRoots_iff`: the positive roots are the first four table
  entries.
* `TauCeti.DynkinType.posRootsFinset_typeB_two`: the positive roots of the pinned `B₂` datum.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate II.
-/

public section

namespace TauCeti

open RootPairing

namespace DynkinType

/-- **The height of a coroot of the pinned `B₂` datum**, against the simple coroots, is the sum
of its coordinates. It is tagged `simp↓` so that it fires at `b2Index 0` and `b2Index 1` before
`TauCeti.DynkinType.b2Index_zero` and `TauCeti.DynkinType.b2Index_one` rewrite the index. -/
@[simp↓] theorem height_flip_b2Index (k : Fin 8) :
    (typeBSimplyConnectedBase 2).flip.height (b2Index k) = b2Coroot k 0 + b2Coroot k 1 := by
  -- The coordinate sum takes the value `1` on both simple coroots, the standard basis vectors.
  have h := apply_root_eq_height_zsmul (typeBSimplyConnectedRootDatum 2).flip
    (typeBSimplyConnectedBase 2).flip
    (Pi.evalAddMonoidHom (fun _ : Fin 2 ↦ ℤ) 0 + Pi.evalAddMonoidHom (fun _ : Fin 2 ↦ ℤ) 1)
    (c := 1) ?_ (b2Index k)
  · rw [flip_root, coroot_b2Index] at h
    simpa only [AddMonoidHom.add_apply, Pi.evalAddMonoidHom_apply, smul_eq_mul, mul_one] using
      h.symm
  · intro j hj
    rw [Base.flip_support, typeBSimplyConnectedBase_two_support, Finset.mem_insert,
      Finset.mem_singleton] at hj
    rcases hj with rfl | rfl <;> rw [flip_root, coroot_b2Index] <;> decide

/-- The positive roots of the pinned `B₂` datum are the first four entries of its coordinate
table. -/
theorem b2Index_mem_posRoots_iff (k : Fin 8) :
    b2Index k ∈ posRoots (typeBSimplyConnectedRootDatum 2) (typeBSimplyConnectedBase 2) ↔
      (k : ℕ) < 4 := by
  rw [mem_posRoots, ← Base.isPos_flip_iff, Base.isPos_iff, height_flip_b2Index]
  decide +revert

/-- **The positive roots of the pinned `B₂` datum are `α₀`, `α₁`, `α₀ + α₁` and
`α₀ + 2 α₁`.** -/
theorem posRootsFinset_typeB_two :
    posRootsFinset (typeBSimplyConnectedRootDatum 2) (typeBSimplyConnectedBase 2) =
      {b2Index 0, b2Index 1, b2Index 2, b2Index 3} := by
  ext i
  obtain ⟨k, rfl⟩ := b2Index_bijective.surjective i
  rw [mem_posRootsFinset, b2Index_mem_posRoots_iff]
  simp only [Finset.mem_insert, Finset.mem_singleton, b2Index_injective.eq_iff]
  decide +revert

end DynkinType

end TauCeti
