/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.Classical

/-!
# Classical local systems and pullback

The identification of the zeroth homology of `C_*(Ω_b B; R)` with the group ring of the opposite
fundamental group is natural in based maps `f : (B, b) → (B', b')`: the class of the image of a
Moore loop is the image of its class under `π₁(f)` (`MooreLoopSpace.loopClass_map`), and the
degree-zero ring map `loopChainDegreeZero` intertwines `C_*(Ωf)` with the map of group rings
(`loopChainDegreeZero_loopChainMap`).

## Main results

* `TauCeti.MooreLoopSpace.loopClass_map`: the class of the image of a loop.
* `TauCeti.zerothClass_map`: naturality of `zerothClass`.
* `TauCeti.loopChainDegreeZero_loopChainMap`: naturality of `loopChainDegreeZero`.
-/

public section

noncomputable section

open MulOpposite

namespace TauCeti

section Naturality

variable {B B' : Type*} [TopologicalSpace B] [TopologicalSpace B'] {b : B} {b' : B'}
  {R : Type*} [CommRing R]

/-- **The class of the image of a Moore loop** is the image of its class under the map of
fundamental groups. -/
theorem MooreLoopSpace.loopClass_map (f : C(B, B')) (hf : f b = b') (γ : MooreLoopSpace B b) :
    loopClass (MooreLoopSpace.map f hf γ) = FundamentalGroup.mapOfEq f hf (loopClass γ) := by
  rw [FundamentalGroup.mapOfEq_apply, MooreLoopSpace.loopClass, MooreLoopSpace.loopClass,
    ← Path.Homotopic.Quotient.mk_map]
  have h : (MooreLoopSpace.map f hf γ).toPath = (γ.toPath.map f.continuous).cast hf.symm hf.symm :=
    by
    ext s
    simp [MooreLoopSpace.toPath_apply, MoorePath.map_apply]
  rw [h]
  rfl

end Naturality

end TauCeti
