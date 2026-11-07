/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.EilenbergMacLane.Degree
public import TauCeti.Topology.Homotopy.HomotopyGroup.LoopSpace
public import TauCeti.Topology.PathSpace.Moore.Comparison.HomotopyGroup

/-!
# The loop space of a `K(G, n + 2)` space is a `K(G, n + 1)` space

For a based space `(X, x)` the loop-space shift identifies `πₖ(ΩX)` with `πₖ₊₁(X, x)` in every
positive degree `k`, and `ΩX` is path connected exactly when `π₁(X, x)` is trivial. Hence, for a
path-connected `X` and every `n`, the loop space `ΩX` is an Eilenberg--Mac Lane space of type
`K(G, n + 1)` exactly when `X` is one of type `K(G, n + 2)`
(`TauCeti.isEilenbergMacLaneSpace_loopSpace_iff`). The same holds for the Moore loop space
(`TauCeti.MooreLoopSpace.isEilenbergMacLaneSpace_iff`), the strictly associative model of the
loop space.

The loop space is based at the constant loop. Since `ΩX` is then path connected, the base point
plays no role (`TauCeti.IsEilenbergMacLaneSpace.of_basepoint`). This identifies the fibre of the
based path-space fibration `ΩK(G, n + 2) → P → K(G, n + 2)` as a `K(G, n + 1)` space.

## Main results

* `TauCeti.isEilenbergMacLaneSpace_loopSpace_iff`: for path-connected `X`, `Ω X x` is a
  `K(G, n + 1)` space if and only if `X` is a `K(G, n + 2)` space.
* `TauCeti.IsEilenbergMacLaneSpace.loopSpace`: the loop space of a `K(G, n + 2)` space is a
  `K(G, n + 1)` space.
* `TauCeti.MooreLoopSpace.isEilenbergMacLaneSpace_iff`,
  `TauCeti.IsEilenbergMacLaneSpace.mooreLoopSpace`: the same for Moore loops.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 4.2,
  Eilenberg--MacLane spaces, and Section 4.3, loop spaces of Eilenberg--MacLane spaces.
-/

public section

namespace TauCeti

open scoped Topology Topology.Homotopy

universe u v w

variable {G : Type u} [Group G] {n : ℕ} {X : Type v} [TopologicalSpace X] {x : X}

/-- A based space `(L, l)` whose path-connectedness is detected by `π₁(X, x)` and whose positive
homotopy groups are those of `(X, x)` shifted by one is a `K(G, n + 1)` space exactly when the
path-connected space `X` is a `K(G, n + 2)` space. This covers both loop-space models. -/
private theorem isEilenbergMacLaneSpace_iff_of_shift [PathConnectedSpace X]
    {L : Type w} [TopologicalSpace L] {l : L}
    (hL : PathConnectedSpace L ↔ Subsingleton (π_ 1 X x))
    (e : ∀ m : ℕ, π_ (m + 1) L l ≃* π_ (m + 2) X x) :
    IsEilenbergMacLaneSpace G (n + 1) L l ↔ IsEilenbergMacLaneSpace G (n + 2) X x := by
  refine ⟨fun h ↦ .mk inferInstance (fun k hk0 hk ↦ ?_)
      (h.nonempty_homotopyGroupMulEquiv.map (e n).symm.trans),
    fun h ↦ .mk (hL.2 (h.subsingleton_homotopyGroup (by omega))) (fun k hk0 hk ↦ ?_)
      (h.nonempty_homotopyGroupMulEquiv.map (e n).trans)⟩
  · -- `π₁(X)` vanishes because `L` is path connected, and the higher groups by the shift.
    obtain rfl | ⟨m, rfl⟩ : k = 1 ∨ ∃ m, k = m + 2 := by
      rcases k with _ | _ | m
      exacts [absurd rfl hk0, .inl rfl, .inr ⟨m, rfl⟩]
    · exact hL.1 h.pathConnectedSpace
    · exact (e m).toEquiv.subsingleton_congr.mp (h.subsingleton_homotopyGroup (by omega))
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    exact (e m).toEquiv.subsingleton_congr.mpr (h.subsingleton_homotopyGroup (by omega))

/-- **The loop space of a `K(G, n + 2)` space is a `K(G, n + 1)` space, and conversely.** For a
path-connected space `X`, the fixed-interval loop space `Ω X x`, based at the constant loop, is a
`K(G, n + 1)` space if and only if `X` is a `K(G, n + 2)` space. -/
theorem isEilenbergMacLaneSpace_loopSpace_iff [PathConnectedSpace X] :
    IsEilenbergMacLaneSpace G (n + 1) (Ω X x) (Path.refl x) ↔
      IsEilenbergMacLaneSpace G (n + 2) X x :=
  isEilenbergMacLaneSpace_iff_of_shift (pathConnectedSpace_loopSpace_iff_subsingleton_pi1 x)
    HomotopyGroup.pathLoopSpaceMulEquiv

/-- **The loop space of a `K(G, n + 2)` space is a `K(G, n + 1)` space.** -/
theorem IsEilenbergMacLaneSpace.loopSpace (h : IsEilenbergMacLaneSpace G (n + 2) X x) :
    IsEilenbergMacLaneSpace G (n + 1) (Ω X x) (Path.refl x) :=
  have := h.pathConnectedSpace
  isEilenbergMacLaneSpace_loopSpace_iff.2 h

/-- **The Moore loop space of a `K(G, n + 2)` space is a `K(G, n + 1)` space, and conversely.**
For a path-connected space `X`, the Moore loop space `MooreLoopSpace X x`, based at the constant
loop of length zero, is a `K(G, n + 1)` space if and only if `X` is a `K(G, n + 2)` space. -/
theorem MooreLoopSpace.isEilenbergMacLaneSpace_iff [PathConnectedSpace X] :
    IsEilenbergMacLaneSpace G (n + 1) (MooreLoopSpace X x) 1 ↔
      IsEilenbergMacLaneSpace G (n + 2) X x :=
  isEilenbergMacLaneSpace_iff_of_shift (pathConnectedSpace_iff_subsingleton_pi1 x)
    (homotopyGroupMulEquiv x)

/-- **The Moore loop space of a `K(G, n + 2)` space is a `K(G, n + 1)` space.** -/
theorem IsEilenbergMacLaneSpace.mooreLoopSpace (h : IsEilenbergMacLaneSpace G (n + 2) X x) :
    IsEilenbergMacLaneSpace G (n + 1) (MooreLoopSpace X x) 1 :=
  have := h.pathConnectedSpace
  MooreLoopSpace.isEilenbergMacLaneSpace_iff.2 h

end TauCeti
